#!/usr/bin/env python3
"""
aheui2pgm.py - compile an Aheui (아희) program straight to a pgmpiet image.

Usage:
    python aheui2pgm.py prog.aheui          (writes prog.pgm next to it)

Aheui semantics follow the specification / reference interpreter (rpaheui):
starting direction, wrapping, reflection, reversal when a storage runs short,
the ㅇ queue and the ㅎ channel. Numbers are plain values on the Piet stack
(no size limit in pgmpiet.py; exact up to 2^53 in the browser).

Layout (all codels are 1x1):
  * row 0     start-up code (creates the storage counters, pushes the first state)
  * row 2     dispatch row: finds the column of the current state
  * columns   one per state, hanging below the dispatch row
  * bottom    a white lane that walls turn back to the dispatch row

Stack layout while running (bottom -> top):
  storage segments ... | [channel's last push] | counters c(n-1) .. c(0) | state
"""
import argparse, os, sys

# ======================= Aheui front end (mirrors rpaheui) =======================
DOWN, RIGHT, UP, LEFT = 1, 2, -1, -2
MV_DET = {0: (RIGHT, 1), 2: (RIGHT, 2), 4: (LEFT, 1), 6: (LEFT, 2),
          8: (UP, 1), 12: (UP, 2), 13: (DOWN, 1), 17: (DOWN, 2)}
MV_HWALL, MV_WALL, MV_VWALL = 18, 19, 20
VAL_CONSTS = [0, 2, 4, 4, 2, 5, 5, 3, 5, 7, 9, 9, 7, 9, 9, 8, 4, 4, 6, 2, 4, 1, 3, 4, 3, 4, 4, 3]
QUEUE, PORT, DIGITS = 21, 27, 'digits'
BINOPS = {2: 'div', 3: 'add', 4: 'mul', 5: 'mod', 12: 'cmp', 16: 'sub'}
NOOP_INITIALS = {0, 1, 11, 13, 15}          # ㄱ ㄲ ㅇ ㅉ ㅋ


class Pane:
    def __init__(self, text):
        self.cells = {}
        r = c = maxc = 0
        for ch in text:
            if ch == '\n':
                r += 1; maxc = max(maxc, c); c = 0; continue
            self.cells[r, c] = ch if '가' <= ch <= '힣' else None
            c += 1
        self.max_row, self.max_col = r, max(maxc, c)

    def decode(self, pos):
        ch = self.cells.get(pos)
        if ch is None:
            return 11, -1, -1
        b = ord(ch) - 0xAC00
        return b // 588, (b // 28) % 21, b % 28

    def advance(self, pos, d, step):
        r, c = pos
        if d == DOWN:
            r += step
            if r > self.max_row:
                r = 0
                while (r, c) not in self.cells: r += 1
        elif d == RIGHT:
            c += step
            if c > self.max_col: c = 0
        elif d == UP:
            r -= step
            if r < 0:
                r = self.max_row
                while (r, c) not in self.cells: r -= 1
        else:
            c -= step
            if c < 0:
                c = self.max_col
                while (r, c) not in self.cells: c -= 1
        return r, c

    def normalize(self, pos, d, step):
        seen = 0
        while pos not in self.cells:
            pos = self.advance(pos, d, step)
            seen += 1
            if seen > 4 * (self.max_row + self.max_col + 4):
                return None                 # can never land on a cell
        return pos


def dir_from_mv(mv, d, step):
    if mv in MV_DET: return MV_DET[mv]
    if mv == MV_WALL: return -d, step
    if mv == MV_HWALL: return (-d, step) if d in (UP, DOWN) else (d, step)
    if mv == MV_VWALL: return (-d, step) if d in (LEFT, RIGHT) else (d, step)
    return d, step


class Node:
    """A reachable state that does runtime work."""
    def __init__(self, key, op, lane, req):
        self.key, self.op, self.lane, self.req = key, op, lane, req
        self.next = self.fail = self.zero = None


def trace(text):
    pane = Pane(text)
    if not pane.cells:
        return None, []
    nodes, order, memo = {}, [], {}
    HALT = 'HALT'

    def classify(raw):
        """raw state -> ('eps', next_raw) | ('halt',) | ('node', key)"""
        pos, d, s, st = raw
        pos = pane.normalize(pos, d, s)
        if pos is None:
            return ('spin',)
        op, mv, val = pane.decode(pos)
        nd, ns = dir_from_mv(mv, d, s)
        nxt = (pane.advance(pos, nd, ns), nd, ns, st)
        if op in NOOP_INITIALS:
            return ('eps', nxt)
        if op == 9:                                   # ㅅ select
            return ('eps', (nxt[0], nd, ns, val))
        if op == 18:
            return ('halt',)
        return ('node', (pos, nd, ns, st), op, val)

    def make_node(info):
        _, key, op, val = info
        if key in nodes: return key
        pos, nd, ns, st = key
        if op in BINOPS: n = Node(key, ('bin', BINOPS[op]), st, 2)
        elif op == 6: n = Node(key, ('popnum',) if val == 21 else ('popchar',) if val == 27 else ('pop',), st, 1)
        elif op == 7:
            n = Node(key, ('pushnum',) if val == 21 else ('pushchar',) if val == 27
                     else ('push', VAL_CONSTS[val]), st, 0)
        elif op == 8: n = Node(key, ('dup',), st, 1)
        elif op == 17: n = Node(key, ('swap',), st, 2)
        elif op == 10: n = Node(key, ('mov', val), st, 1)
        elif op == 14: n = Node(key, ('brz',), st, 1)
        else: raise AssertionError(op)
        n.raw_next = (pane.advance(pos, nd, ns), nd, ns, st)
        n.raw_back = (pane.advance(pos, -nd, ns), -nd, ns, st)
        nodes[key] = n; order.append(n)
        return key

    def resolve(raw):
        chain, seen = [], set()
        cur = raw
        while True:
            if cur in memo:
                res = memo[cur]; break
            if cur in seen:                           # cycle with no effect: spin forever
                key = ('spin', cur)
                if key not in nodes:
                    n = Node(key, None, None, 0); nodes[key] = n; order.append(n)
                    n.next = key
                res = key; break
            seen.add(cur); chain.append(cur)
            info = classify(cur)
            if info[0] == 'eps': cur = info[1]; continue
            if info[0] == 'halt': res = HALT; break
            if info[0] == 'spin':
                key = ('spin', cur); n = Node(key, None, None, 0); n.next = key
                nodes[key] = n; order.append(n); res = key; break
            res = make_node(info); break
        for c in chain: memo[c] = res
        return res

    start = resolve(((0, 0), DOWN, 1, 0))
    i = 0
    while i < len(order):
        n = order[i]; i += 1
        if n.op is None: continue
        n.next = resolve(n.raw_next)
        if n.req: n.fail = resolve(n.raw_back)
        if n.op == ('brz',): n.zero = resolve(n.raw_back)
    return start, order



# ================================ pgmpiet back end ================================
STEPS = [112, 131, 134, 148, 155, 162, 170, 177, 184, 191, 198, 205, 212, 219, 226,
         233, 240, 247]
BLACK, WHITE = 33, 255
CMD = {'push': 1, 'pop': 2, 'add': 3, 'sub': 4, 'mul': 5, 'div': 6, 'mod': 7, 'not': 8,
       'gt': 9, 'ptr': 10, 'sw': 11, 'dup': 12, 'roll': 13, 'innum': 14, 'inchr': 15,
       'outnum': 16, 'outchr': 17}


def next_step(s, cmd):
    c = CMD[cmd]
    return ((s // 3 + c // 3) % 6) * 3 + (s % 3 + c % 3) % 3


def lit(n):
    """Piet commands that push the integer n (every block is 1 codel, so push = 1)."""
    if n == 0:
        return ['push', 'not']
    if n < 0:
        return ['push', 'not'] + lit(-n) + ['sub']
    out = ['push']
    for b in bin(n)[3:]:
        out += ['dup', 'add']
        if b == '1':
            out += ['push', 'add']
    return out


def roll(depth, rolls):
    return lit(depth) + lit(rolls) + ['roll']


class Storage:
    """Code for the multi-storage layout. `extra` = values sitting above the
    counter block at that moment (the dispatch value is never there: every
    state column starts by popping it)."""

    def __init__(self, lanes):
        self.lanes = lanes                       # storage indices, in stack order
        self.L = len(lanes)
        self.port = PORT in lanes
        self.K = self.L + (1 if self.port else 0)

    def idx(self, lane):
        return self.lanes.index(lane)

    def cdepth(self, j, extra):                  # depth of counter j (1 = top)
        return extra + j + 1

    def pick(self, d):
        return roll(d, -1) + ['dup'] + roll(d + 1, 1)

    def bump(self, j, extra, delta):
        d = self.cdepth(j, extra)
        return roll(d, -1) + lit(abs(delta)) + ['add' if delta > 0 else 'sub'] + roll(d, 1)

    def depth_above(self, j, extra, const):
        """push const + (sizes of the segments stacked above segment j)"""
        code = lit(const)
        for i in range(j):
            code += self.pick(self.cdepth(i, extra + 1)) + ['add']
        return code

    def count(self, j, extra):                   # push a copy of counter j
        return self.pick(self.cdepth(j, extra))

    def pop(self, lane, extra):
        """move the top (stack) / front (queue) value of `lane` to the top"""
        j = self.idx(lane)
        if lane == QUEUE:
            code = self.depth_above(j, extra, extra + self.K) + \
                self.pick(self.cdepth(j, extra + 1)) + ['add']
        else:
            code = self.depth_above(j, extra, extra + self.K + 1)
        return code + lit(-1) + ['roll'] + self.bump(j, extra + 1, -1)

    def push(self, lane, extra, front=False):
        """move the value on top (one of `extra` values) into `lane`"""
        j = self.idx(lane)
        code = self.depth_above(j, extra, extra + self.K)
        if front:
            code += self.pick(self.cdepth(j, extra + 1)) + ['add']
        return code + lit(1) + ['roll'] + self.bump(j, extra - 1, 1)

    def set_last_push(self, extra):
        """channel (ㅎ) bookkeeping: remember a copy of the value on top"""
        lp = extra + 1 + self.L + 1
        return ['dup'] + roll(lp, -1) + ['pop'] + roll(extra + self.K, 1)

    def get_last_push(self, extra):
        return self.pick(extra + self.L + 1)

    def store(self, lane, extra, update_port=True):
        code = []
        if lane == PORT and update_port:
            code += self.set_last_push(extra)
        return code + self.push(lane, extra)


def select(then_state, else_state):
    """flag on top (0/1): push else_state if 0, then_state if 1"""
    if then_state == else_state:
        return ['pop'] + lit(then_state)
    return lit(then_state - else_state) + ['mul'] + lit(else_state) + ['add']


SENTINEL = -987654321


def build_states(start, nodes):
    """Turn traced Aheui nodes into Piet states: {id: (command list, special)}."""
    lanes = [0]
    for n in nodes:
        if n.op is None: continue
        for s in ([n.lane, n.op[1]] if n.op[0] == 'mov' else [n.lane]):
            if s not in lanes: lanes.append(s)
    S = Storage(lanes)

    states = []            # list of [commands, kind]; kind 'code' or 'halt'
    def new(kind='code'):
        states.append([None, kind]); return len(states) - 1
    HALT = new('halt')
    entry = {}             # node key -> first state id
    for n in nodes:
        entry[n.key] = new()
    def ent(key):
        return HALT if key == 'HALT' else entry[key]

    for n in nodes:
        sid = entry[n.key]
        if n.op is None:                                   # effect-free infinite loop
            states[sid][0] = lit(sid); continue
        if n.req:                                          # enough values? else reverse
            ex = new()
            states[sid][0] = S.count(S.idx(n.lane), 0) + lit(n.req - 1) + ['gt'] + \
                select(ex, ent(n.fail))
            sid = ex
        states[sid][0] = exec_code(n, S, sid, ent, new, states)
    return states, ent(start), S


def exec_code(n, S, sid, ent, new, states):
    k, ln = n.op[0], n.lane
    nxt = ent(n.next)
    if k == 'push':
        return lit(n.op[1]) + S.store(ln, 1) + lit(nxt)
    if k == 'pop':
        return S.pop(ln, 0) + ['pop'] + lit(nxt)
    if k == 'popnum':
        return S.pop(ln, 0) + ['outnum'] + lit(nxt)
    if k == 'dup':
        if ln == PORT:
            return S.get_last_push(0) + S.store(ln, 1) + lit(nxt)
        if ln == QUEUE:
            return S.pop(ln, 0) + ['dup'] + S.push(ln, 2, True) + S.push(ln, 1, True) + lit(nxt)
        return S.pop(ln, 0) + ['dup'] + S.push(ln, 2) + S.push(ln, 1) + lit(nxt)
    if k == 'swap':
        q = ln == QUEUE
        return S.pop(ln, 0) + S.pop(ln, 1) + roll(2, 1) + \
            S.push(ln, 2, q) + S.push(ln, 1, q) + lit(nxt)
    if k == 'mov':
        return S.pop(ln, 0) + S.store(n.op[1], 1) + lit(nxt)
    if k == 'brz':
        return S.pop(ln, 0) + ['not'] + select(ent(n.zero), nxt)
    if k == 'bin':
        op = n.op[1]
        code = S.pop(ln, 0) + S.pop(ln, 1)                 # [a, b]  (a was on top)
        if op == 'cmp':
            code += ['gt', 'not']                          # b >= a  ==  not (a > b)
        else:
            code += roll(2, 1)                             # [b, a]
            if op in ('div', 'mod'):                       # x / 0 -> 0 (undefined in Aheui)
                code += ['dup', 'not', 'dup'] + roll(4, 1) + ['add'] + \
                    [{'div': 'div', 'mod': 'mod'}[op]] + roll(2, 1) + ['not', 'mul']
            else:
                code += [{'add': 'add', 'sub': 'sub', 'mul': 'mul'}[op]]
        return code + S.store(ln, 1, update_port=False) + lit(nxt)
    if k == 'popchar':
        # value on top; choose how many UTF-8 bytes (0 = invalid -> U+FFFD)
        base = [new() for _ in range(5)]
        code = S.pop(ln, 0)                                # [v]
        def combine(test, op):                             # [v, r] -> [v, r op test(v)]
            return roll(2, 1) + ['dup'] + test + roll(3, -1) + [op]
        code += ['dup'] + lit(0) + ['gt']                  # [v, v>0]
        code += combine(lit(0x110000) + ['gt', 'not'], 'mul')   # [v, valid]
        code += roll(2, 1) + lit(1)                        # [valid, v, 1]
        for lim in (127, 2047, 65535):
            code += combine(lit(lim) + ['gt'], 'add')      # [valid, v, bytes]
        code += roll(3, -1) + ['mul']                      # [v, bytes*valid]
        code += lit(base[0]) + ['add']
        def byte(div, first_mark=None):
            c = ['dup'] + (lit(div) + ['div'] if div > 1 else [])
            if first_mark is None:
                c += lit(64) + ['mod'] + lit(128) + ['add']
            else:
                c += lit(first_mark) + ['add']
            return c + ['outchr']
        states[base[0]][0] = ['pop'] + lit(239) + ['outchr'] + lit(191) + ['outchr'] + \
            lit(189) + ['outchr'] + lit(nxt)
        states[base[1]][0] = ['outchr'] + lit(nxt)
        states[base[2]][0] = byte(64, 192) + byte(1) + ['pop'] + lit(nxt)
        states[base[3]][0] = byte(4096, 224) + byte(64) + byte(1) + ['pop'] + lit(nxt)
        states[base[4]][0] = byte(262144, 240) + byte(4096) + byte(64) + byte(1) + ['pop'] + lit(nxt)
        return code
    if k == 'pushnum':
        got, none = new(), new()
        states[got][0] = roll(2, 1) + ['pop'] + S.store(ln, 1) + lit(nxt)
        states[none][0] = ['pop'] + lit(0) + S.store(ln, 1) + lit(nxt)
        return lit(SENTINEL) + ['innum', 'dup'] + lit(SENTINEL) + ['sub', 'not'] + select(none, got)
    if k == 'pushchar':
        done = new()
        states[done][0] = S.store(ln, 1) + lit(nxt)
        eof = new()
        states[eof][0] = ['pop'] + lit(-1) + S.store(ln, 1) + lit(nxt)
        # continuation readers: cont[r] expects [cp] and r bytes still to read
        cont = {r: new() for r in (1, 2, 3)}
        bad = new()
        states[bad][0] = ['pop', 'pop'] + lit(-1) + S.store(ln, 1) + lit(nxt)
        for r in (1, 2, 3):
            after = done if r == 1 else cont[r - 1]
            got = new()
            states[got][0] = roll(2, 1) + ['pop'] + lit(128) + ['sub'] + roll(2, 1) + \
                lit(64) + ['mul', 'add'] + lit(after)
            states[cont[r]][0] = lit(SENTINEL) + ['inchr', 'dup'] + lit(SENTINEL) + \
                ['sub', 'not'] + select(bad, got)
        lead = new()
        # [b]: k = (b>127)+(b>191)+(b>223)+(b>239) -> ascii, invalid, 2, 3, 4-byte
        kinds = [new() for _ in range(5)]
        code = ['dup'] + lit(127) + ['gt']
        for lim in (191, 223, 239):
            code += roll(2, 1) + ['dup'] + lit(lim) + ['gt'] + roll(3, -1) + ['add']
        states[lead][0] = code + lit(kinds[0]) + ['add']
        states[kinds[0]][0] = lit(done)
        states[kinds[1]][0] = ['pop'] + lit(-1) + lit(done)
        states[kinds[2]][0] = lit(192) + ['sub'] + lit(cont[1])
        states[kinds[3]][0] = lit(224) + ['sub'] + lit(cont[2])
        states[kinds[4]][0] = lit(240) + ['sub'] + lit(cont[3])
        first = new()
        states[first][0] = roll(2, 1) + ['pop'] + lit(lead)
        return lit(SENTINEL) + ['inchr', 'dup'] + lit(SENTINEL) + ['sub', 'not'] + select(eof, first)
    raise AssertionError(k)


def layout(states, start_id, S):
    """Place everything on a grid; returns (width, height, rows of gray values)."""
    N = len(states)
    init = ['push', 'not'] * S.K + lit(start_id) + ['push', 'ptr']
    kx = len(init)                           # init corridor column
    M = 2                                    # dispatch row
    x0 = kx + 2                              # first dispatch codel (free entry)
    B = [x0 + 3 + 5 * i for i in range(N)]
    # a state column is ['pop' the dispatch value] + its commands
    cols = []
    for code, kind in states:
        cols.append(['pop'] + code if kind == 'code' else None)
    longest = max([len(c) for c in cols if c] + [3])
    Y = M + 1 + longest + 1                  # bottom lane
    Y = max(Y, M + 5)
    Wd = B[-1] + 3
    H = Y + 1
    g = [[BLACK] * Wd for _ in range(H)]

    def put(x, y, v):
        g[y][x] = v

    # start-up row
    c = 0
    put(0, 0, STEPS[c])
    for i, cmd in enumerate(init):
        c = next_step(c, cmd); put(i + 1, 0, STEPS[c])
    # the init chain ends at x = len(init); its corridor goes down from there
    kx = len(init)
    for y in range(1, Y + 1):
        put(kx, y, WHITE)
    # return column and lane
    for y in range(M, Y + 1):
        put(0, y, WHITE)
    for x in range(0, Wd):
        put(x, Y, WHITE)
    for x in range(0, x0):
        put(x, M, WHITE)
    # dispatch row
    c = 0
    put(x0, M, STEPS[c])
    x = x0
    for i in range(N):
        for cmd in ('dup', 'not', 'ptr', 'push', 'sub'):
            c = next_step(c, cmd); x += 1; put(x, M, STEPS[c])
            if cmd == 'ptr':
                bcol = c
                assert x == B[i]
        col = cols[i]
        if col is None:                      # halt: a trap the pointer can't leave
            q = next_step(bcol, 'pop')
            put(B[i], M + 1, STEPS[q])
            put(B[i], M + 2, WHITE)
            t = (q + 1) % 18
            for (tx, ty) in ((B[i], M + 3), (B[i] - 1, M + 3), (B[i] - 1, M + 2)):
                put(tx, ty, STEPS[t])
            continue
        cc = bcol
        for j, cmd in enumerate(col):
            cc = next_step(cc, cmd); put(B[i], M + 1 + j, STEPS[cc])
        for y in range(M + 1 + len(col), Y):
            put(B[i], y, WHITE)
    return Wd, H, g


def compile_aheui(text):
    if text.startswith('\ufeff'):
        text = text[1:]
    start, nodes = trace(text)
    if start is None or start == 'HALT':
        nodes, start = [], 'HALT'
    states, start_id, S = build_states(start, nodes)
    return layout(states, start_id, S)


def main():
    ap = argparse.ArgumentParser(description='Compile Aheui to a pgmpiet image: prog.aheui -> prog.pgm')
    ap.add_argument('src', help='Aheui source file')
    a = ap.parse_args()
    raw = open(a.src, 'rb').read().decode('utf-8')
    if raw.startswith('\ufeff'):
        print('note: removed UTF-8 byte-order mark')
    W, H, g = compile_aheui(raw.replace('\r\n', '\n'))
    out = os.path.splitext(a.src)[0] + '.pgm'
    with open(out, 'wb') as f:
        f.write(('P5\n# aheui2pgm\n%d %d\n255\n' % (W, H)).encode())
        for row in g:
            f.write(bytes(row))
    print('wrote %s (%d x %d)' % (out, W, H))


if __name__ == '__main__':
    main()
