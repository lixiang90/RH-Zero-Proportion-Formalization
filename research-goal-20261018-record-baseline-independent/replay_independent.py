"""Independent full original-floor finite replay of fixed s1R13 source.

No producer Python module is imported.  Only our previously frozen packing
decoder is reused.  Walk propagation uses a signed 9x9 graph matrix; numeric
leaf margins come from the printed source Nat.ble AST; root WZ uses exact
Fraction-based outward rounding.  No threshold change, search, Lean or network.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import ast
import gzip
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SRC = ROOT / "research-goal-20261018-record-source-audit/snapshot/Solution.lean"
PROD = ROOT / "research-goal-20261018-record-baseline-replay"
PROD_MANIFEST_SHA = "03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f"
SRC_SHA = "f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf"
OUT = HERE / "independent-replay.json"
FAIL = HERE / "independent-failure.json"
START = HERE / "independent-started.json"


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def canon(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def sub(a, b):
    return max(0, a - b)


def parse_app(text):
    """Parenthesized Lean application fragment, with complete token consumption."""
    tokens = ["("] + re.findall(r"\[[^\]]*\]|[()]|[^\s()]+", text) + [")"]
    at = 0
    def expr():
        nonlocal at
        item = tokens[at]
        at += 1
        if item != "(":
            return item
        values = []
        while tokens[at] != ")":
            values.append(expr())
        at += 1
        assert values
        return values[0] if len(values) == 1 else values
    value = expr()
    assert at == len(tokens)
    return value


def declaration(text, name, kind="def"):
    pattern = (r"(?m)^(?:(?:noncomputable|private) )?" + kind + " " + re.escape(name)
        + r"\b[\s\S]*?(?=^(?:(?:noncomputable|private) )?(?:def|theorem|lemma|abbrev|structure)|^end |^namespace |\Z)")
    found = re.findall(pattern, text)
    assert len(found) == 1, ("declaration", name, len(found))
    return found[0]


def load_source():
    sys.set_int_max_str_digits(20000)
    assert pin(SRC)["sha256"] == SRC_SHA
    own = ROOT / "research-goal-20261018-record-packing-independent/decode_packing.py"
    spec = importlib.util.spec_from_file_location("own_frozen_packing", own)
    packing = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(packing)
    raw = SRC.read_bytes()
    text = packing.mask_comments(raw.decode("utf-8"))
    cert = text.split("namespace AMW.Cert.PC9QB6M\n", 1)[1].split("end AMW.Cert.PC9QB6MData", 1)[0]
    nums, packed_count = {}, 0
    for name, body in re.findall(r"(?m)^(?:noncomputable )?def (\w+) : ℕ := ([^\n]+)$", cert):
        body = body.strip()
        m = re.fullmatch(r'zfNat64 (\d+) "([A-Za-z0-9+_]*)"', body)
        if m:
            value = packing.independent_decode(int(m[1]), m[2])
            packed_count += 1
        elif re.fullmatch(r"0x[0-9a-fA-F]+|\d+", body):
            value = int(body, 16 if body.startswith("0x") else 10)
        else:
            continue
        assert name not in nums
        nums[name] = value
    assert packed_count == 137
    def literal(name):
        m = re.search(r"(?m)^(?:noncomputable )?def " + name + r" :[^\n]*:= (\[[^\n]*\])$", cert)
        assert m, name
        return ast.literal_eval(m[1])
    BS, TS, PR, BND = [literal(name) for name in ["BS", "TS", "PR", "BND"]]
    CN, SIG, TOP = [nums[name] for name in ["cN", "SIG", "TOP"]]
    assert CN == 893616123055294719 and nums["SA"] == 10**20
    assert len(BS) == 8 and len(TS) == 34 and len(PR) == 28
    ALL = [(r, r + 1) for r in range(8)] + PR
    assert len(set(ALL)) == 36
    LOOK = {edge: j for j, edge in enumerate(ALL)}
    dispatch = {name: parse_app(body) for name, body in re.findall(
        r"(?m)^(?:noncomputable )?def ((?:BKD?|WL\d+)\w*) \(j : ℕ\) : ℕ := ([^\n]+)$", cert)}
    def dispatch_value(name, j):
        def ev(tree):
            if isinstance(tree, str):
                if tree == "j": return j
                if tree.isdecimal(): return int(tree)
                if tree in nums: return nums[tree]
                return ev(dispatch[tree])
            head, *args = tree
            if head == "dsel":
                return ev(args[2] if ev(args[0]) < ev(args[1]) else args[3])
            if head == "dpk":
                return ev(args[2]) if ev(args[0]) == ev(args[1]) else 0
            assert args == ["j"] and head in dispatch, tree
            return ev(dispatch[head])
        return ev(name)
    dispatch_checks = 0
    for prefix, limits in [("BK", range(513)), ("BKD", range(513))] + [
            (f"WL{r}", range(2 + max(int(k.split("_")[-1]) for k in nums if re.fullmatch(f"WL{r}_\\d+", k))))
            for r in range(48)]:
        for j in limits:
            assert dispatch_value(prefix, j) == nums.get(f"{prefix}_{j}", 0)
            dispatch_checks += 1
    pts, trees = {}, {}
    for name, body in re.findall(r"(?m)^(?:noncomputable )?def (PTT(?:_\d+)?) : PTrD := ([^\n]+)$", cert):
        def pt_node(tree):
            if isinstance(tree, str): return trees[tree]
            head, *args = tree
            if head == ".nd":
                return ("node", int(args[0]), pt_node(args[1]), pt_node(args[2]))
            assert head == ".lf" and len(args) == 2
            block = int(args[0]); entries = ast.literal_eval(args[1])
            assert all(0 <= off < 1024 for off, value in entries)
            for off, value in entries:
                key = 1024 * block + off
                assert key not in pts
                pts[key] = value
            return ("leaf", block, dict(entries))
        trees[name] = pt_node(parse_app(body))
    assert len(pts) == 2095 and "PTT" in trees
    def pt_raw(point):
        node = trees["PTT"]
        while node[0] == "node":
            node = node[2] if point // 1024 < node[1] else node[3]
        return node[2].get(point % 1024, 0) if point // 1024 == node[1] else 0
    assert all(pt_raw(point) == value for point, value in pts.items())
    @lru_cache(None)
    def point_value(point):
        word = pt_raw(point)
        if not word: return 0
        # Printed pwD: ordinary low96 bits plus absolute 24-bit interval ends.
        lo = sub(point, (word >> 96) & ((1 << 20) - 1))
        hi = point + (word >> 116)
        return (word & ((1 << 96) - 1)) + (lo << 96) + (hi << 120)
    cov_match = re.search(r"def COV[^\n]*:= ([\s\S]*?)\nnoncomputable def SMAX", cert)
    COV = ast.literal_eval(cov_match[1].strip().replace("true", "True").replace("false", "False"))
    BAD = [[(a, b) for a, b, good in row if not good] for row in COV]
    SMAX = ast.literal_eval(re.search(r"def SMAX[^\n]*:= (\[[^\]]*\])", cert)[1])
    roots = {}
    for r, wd, cuts, fuel, pos, indices, M, end in re.findall(
        r"theorem ready(\d+)_parent_cursor : U \(walkCutR TOP BK TOPD BKD PT REG WD(\d+) ready\d+_cuts(\d+) (\d+) (\d+)\) \(ofCl \(RC ([\d ]+)\) (\d+)\) = (\d+)", cert):
        assert r == wd and M == "0"
        roots[int(r)] = dict(indices=tuple(map(int, indices.split())), cuts=int(cuts), fuel=int(fuel), pos=int(pos), expected=int(end))
    assert set(roots) == set(range(48))
    assert sorted(r["indices"] for r in roots.values()) == sorted(itertools.product(*(range(len(row)) for row in BAD)))
    wd = re.findall(r"def WD(\d+) : ℕ → ℕ := rdw WL(\d+)", cert)
    assert sorted((int(a), int(b)) for a, b in wd) == [(j, j) for j in range(48)]
    states = {name: tuple(map(int, values.split(", "))) for name, values in re.findall(
        r"def (ready\d+_\d+_state) : St := ⟨([\d, ]+)⟩", cert)}
    assert len(states) == 70 and all(len(row) == 73 and row[-1] == 0 for row in states.values())
    cursors = []
    for name, r, j, wd_id, cuts, fuel, pos, state, end in re.findall(
        r"theorem (ready(\d+)_(\d+))_cursor : U \(walkCut TOP BK TOPD BKD PT REG WD(\d+) (ready\d+_cuts\d+) (\d+) (\d+)\) (ready\d+_\d+_state) = (\d+)", cert):
        assert r == wd_id and state == name + "_state"
        cursors.append(dict(name=name, root=int(r), index=int(j), cuts=cuts, fuel=int(fuel), pos=int(pos), state=state, expected=int(end)))
    assert len(cursors) == 70 and {c["state"] for c in cursors} == set(states)
    cuts = {f"ready{r}_cuts0": [] for r in range(48)}
    for name, pos, state, end, previous in re.findall(
        r"def (ready\d+_cuts\d+) : List[^\n]*:= \((\d+), (ready\d+_\d+_state), (\d+)\) :: (ready\d+_cuts\d+)", cert):
        cuts[name] = [(int(pos), state, int(end))] + cuts[previous]
    assert len(cuts) == 118
    st_names = re.search(r"structure St where\s*\(([^)]*) : ℕ\)", cert)[1].split()
    assert len(st_names) == 73 and st_names[-1] == "M"
    printed = declaration(cert, "mcheckP")
    begin = printed.index("(Nat.ble")
    balance = 0
    for end in range(begin, len(printed)):
        if printed[end] == "(": balance += 1
        elif printed[end] == ")":
            balance -= 1
            if not balance: break
    margin_tree = parse_app(printed[begin:end + 1])
    assert margin_tree[0] == "Nat.ble"
    STEP = int(re.search(r"let t := Nat.land \(Nat.shiftRight (\d+)", declaration(text, "dstep"))[1])
    BL8 = int(re.search(r"def BL8 : ℕ := (0x[0-9a-f]+)", text)[1], 16)
    rcM = int(re.search(r"def RC[^\n]*:= rootCl 8 28 (\d+) COV", cert)[1])
    return locals()


def source_poly(text, name, x, DZ):
    body = declaration(text, name).split(":=", 1)[1].strip()
    tree = parse_app(body)
    def ev(t):
        if isinstance(t, str):
            if t == "T": return x
            if t.isdecimal(): return int(t)
            raise AssertionError((name, t))
        head, *args = t
        values = [ev(a) for a in args]
        if head == "DZp": return DZ ** values[0]
        return {"Nat.add": lambda a, b: a + b, "Nat.mul": lambda a, b: a * b,
                "Nat.pow": pow}[head](*values)
    return ev(tree)


def root_wz(text, L, U):
    def scalar(name):
        values = re.findall(r"(?m)^noncomputable def " + name + r" : ℕ := (\d+)\s*$", text)
        assert values and len(set(values)) == 1, name
        return int(values[0])
    DZ, SC, PLN, PUN, E20, ERRD, E9, SW, G0, G1 = [scalar(n) for n in
        ["DZ", "SC", "PLN", "PUN", "E20", "ERRD", "E9", "SW", "GAM0", "GAM1"]]
    def floor(x): return x.numerator // x.denominator if isinstance(x, F) else x
    def ceil(x): return -((-x.numerator) // x.denominator) if isinstance(x, F) else x
    def plus(a, b): return (a[0] + b[0], a[1] + b[1])
    def neg(a): return (-a[1], -a[0])
    def minus(a, b): return plus(a, neg(b))
    def product(a, b):
        candidates = [F(x * y, DZ) for x in a for y in b]
        return (floor(min(candidates)), ceil(max(candidates)))
    def divide(a, n): return (floor(F(a[0], n)), ceil(F(a[1], n)))
    def parameter(name):
        m = re.search(r"def " + name + r" : IV := IV.ofN (\d+) (\d+)", text)
        return tuple(map(int, m.groups()))
    k = (2 * (L + U) + SC) // (2 * SC)
    right = k * SC <= 2 * L
    XL, XU = floor(F(L * DZ, SC)), ceil(F(U * DZ, SC))
    anchor = k * (DZ // 2)
    RL = sub(XL, anchor) if right else sub(anchor, XU)
    RU = sub(XU, anchor) if right else sub(anchor, XL)
    TL, TU = floor(F(PLN * RL, E20)), ceil(F(PUN * RU, E20))
    poly = lambda name, x: source_poly(text, name, x, DZ)
    CI = (floor(F(sub(poly("cosP", TU), poly("cosN", TU)), 3628800 * DZ**9)) - ERRD,
          ceil(F(sub(poly("cosP", TL), poly("cosN", TL)), 3628800 * DZ**9)) + ERRD)
    SI = (floor(F(sub(poly("sinP", TL), poly("sinN", TL)), 39916800 * DZ**10)) - ERRD,
          ceil(F(sub(poly("sinP", TU), poly("sinN", TU)), 39916800 * DZ**10)) + ERRD)
    if k % 4 == 0: CX, SX = CI, SI if right else neg(SI)
    elif k % 4 == 1: CX, SX = neg(SI) if right else SI, CI
    elif k % 4 == 2: CX, SX = neg(CI), neg(SI) if right else SI
    else: CX, SX = SI if right else neg(SI), neg(CI)
    BL, BU = floor(F(PLN * XL, E20)), ceil(F(PUN * XU, E20))
    PG = (floor(F(G0 * BL, DZ)), ceil(F(G1 * BU, DZ)))
    NI = minus(CX, product(PG, SX))
    E0, E1 = sub(floor(F(2 * BL**2, DZ)), DZ), sub(ceil(F(2 * BU**2, DZ)), DZ)
    assert L <= U and TU <= DZ and E0 > 0 and (k * SC <= 2 * L if right else 2 * U <= k * SC)
    ce = ast.literal_eval(re.search(r"def CE : List[^\n]*:=\s*(\[[\s\S]*?\])", text)[1].replace("true", "True").replace("false", "False"))
    fa = declaration(text, "FA")
    assert [(int(j), int(v), sign == "true") for j, v, sign in re.findall(r"\b(\d+) (\d+) (true|false)\)", fa)] == ce
    total = (0, 0)
    for j, coefficient, negative in ce:
        J = j * DZ
        if 2 * j == k:
            low, high = floor(F(DZ**2, 2 * (XU + J))), ceil(F(DZ**2, 2 * (XL + J)))
        elif 2 * j < k:
            low, high = floor(F(XU * DZ**2, XU**2 - J**2)), ceil(F(XL * DZ**2, XL**2 - J**2))
        else:
            low, high = floor(F(XL * DZ**2, J**2 - XL**2)), ceil(F(XU * DZ**2, J**2 - XU**2))
            negative = not negative
        term = (coefficient * low, coefficient * high)
        total = plus(total, neg(term) if negative else term)
    FA = divide(total, E9)
    B0 = (0, 0)
    if k % 2 == 0 and 2 <= k <= 24:
        S0 = (floor(F(poly("scP", TL) - poly("scN", TU), 39916800 * DZ**9)) - ERRD,
              ceil(F(poly("scP", TU) - poly("scN", TL), 39916800 * DZ**9)) + ERRD)
        cj = {int(j): (int(v), sign == "true") for j, v, sign in re.findall(
            r"\| (\d+) => \((\d+), (true|false)\)", declaration(text, "CJ"))}
        coefficient, negative = cj[k // 2]
        signed = (coefficient * S0[0], coefficient * S0[1])
        B0 = divide(neg(signed) if negative else signed, 2 * E9)
    lo, hi = neg(NI)
    quotient = (floor(F(lo * DZ, E1 if lo >= 0 else E0)),
                ceil(F(hi * DZ, E0 if hi >= 0 else E1)))
    K0 = plus(quotient, plus(product(parameter("SIGC"), product(SX, FA)), product(parameter("RHOC"), B0)))
    KA = max(0, K0[0], -K0[1])
    return (KA * KA * SW) // (DZ * DZ)


class Replay:
    def __init__(self, model):
        self.m = model
        self.count = Counter(); self.contract_count = Counter()
        self.trace = sha256(); self.rows = []; self.contracts = []; self.minmargin = None
        self.BB = 1 << 42
        self.mask32 = (1 << 32) - 1

    def flat(self, state):
        return tuple(itertools.chain.from_iterable(zip(*state))) + (0,)

    def hashstate(self, state):
        return sha256(canon(self.flat(state))).hexdigest()

    def root(self, index):
        L, U = zip(*(self.m["BAD"][r][j] for r, j in enumerate(index)))
        lows = list(L) + [sum(L[i:j]) for i, j in self.m["PR"]]
        highs = list(U) + [min(self.m["rcM"], sum(U[i:j])) for i, j in self.m["PR"]]
        assert all(sum(U[i:j]) <= self.m["rcM"] for i, j in self.m["PR"])
        return (lows, highs)

    def graph(self, state):
        D = [[0] * 9 for _ in range(9)]
        for index, (a, b) in enumerate(self.m["ALL"]):
            D[a][b], D[b][a] = state[1][index], -state[0][index]
        return D

    def split(self, state, a, b, cut, upper):
        if not upper: a, b, cut = b, a, -cut
        graph = self.graph(state)
        assert all(self.BB + graph[x][a] >= 0 and self.BB + cut + graph[b][x] >= 0 for x in range(9))
        low, high = [], []
        for i, (u, v) in enumerate(self.m["ALL"]):
            low.append(max(state[0][i], max(0, -(graph[v][a] + cut + graph[b][u]))))
            high.append(min(state[1][i], max(0, graph[u][a] + cut + graph[b][v])))
        return (low, high)

    @lru_cache(None)
    def table_entry(self, level, column):
        m = self.m
        if level >= 20: return 0
        if level >= 11:
            return (m["TOP"] >> (32 * ((1 << sub(19, level)) + column))) & self.mask32
        block_id = column >> sub(10, level)
        block = m["dispatch_value"]("BK", block_id)
        refined = level + sub(block & 31, level)
        height = sub(10, refined)
        index = sub(1 << height, 1) + sub(column >> sub(refined, level), block_id << height)
        return ((block >> 5) >> (32 * index)) & self.mask32

    @lru_cache(None)
    def lower_bound(self, low, high):
        if high <= low or high >= 524289: return 0
        width = sub(high, low) >> 5
        # Use the actual source BL8 nibble semantics, not Python bit_length.
        if width < 256: level = (self.m["BL8"] >> (4 * width)) & 15
        else: level = 8 + ((self.m["BL8"] >> (4 * (width >> 8))) & 15)
        boundary = (sub(high, 1) >> level) + 1
        at = low >> level
        values = []
        for _ in range(14):
            distance = sub(boundary, at)
            hop = (self.m["STEP"] >> (3 * (17 * (at & 15) + min(distance, 16)))) & 7
            node = at >> hop
            assert node < (1 << 40)
            values.append(self.table_entry(level + hop, node))
            at = (node + 1) << hop
            if boundary <= at: return min(values)
        return min(values + [0])

    def gpoint(self, low, high, code):
        if code == 33: return low
        size = 5 if (code >> 6) & 1 else 8
        unit = 1 << size
        lower = ((low + unit - 1) // unit) * unit
        upper = (high // unit) * unit
        selected = ((low + ((sub(high, low) * (code & 63)) >> 5)) // unit) * unit
        return lower if selected <= lower else upper if upper <= selected else selected

    def decode_term(self, word, at, low, high):
        kind = (word >> at) & 3
        mass = ((word >> (at + 9)) & 1023) if kind == 2 else ((word >> (at + 16)) & 1023) if kind == 3 else 0
        point = self.gpoint(low, high, (word >> (at + 2)) & 127) if kind else 0
        other = self.gpoint(low, high, (word >> (at + 9)) & 127) if kind == 3 else 0
        return (kind, mass, point, other), at + [2, 9, 19, 26][kind]

    @staticmethod
    def weights(kind, mass):
        return (1024, 0) if kind == 1 else (mass, 0) if kind == 2 else (sub(1024, mass), mass) if kind == 3 else (0, 0)

    def bounds(self, state, i, j):
        q = self.m["LOOK"][(i, j)]
        return max(state[0][q], sum(state[0][i:j])), min(state[1][q], sum(state[1][i:j]))

    def flow(self, state, word, at):
        P, S, positive, negative = [0] * 8, [0] * 8, 0, 0
        for _ in range(42):
            if not ((word >> at) & 1): return P, S, positive, negative, at + 1
            tag = (word >> (at + 1)) & 31
            offset = at + 6
            at = offset + 15
            # Source permits an invalid tag to terminate; all actual input tags
            # are additionally required valid, as in the producer's precheck.
            assert tag < 28
            self.count["valid_ydec_entries"] += 1
            scale = self.m["SIG"] * ((word >> (offset + 1)) & 16383)
            i, j = self.m["PR"][tag]; base = sum(state[0][i:j]); q = 8 + tag
            if (word >> offset) & 1:
                for r in range(i, j): S[r] += scale
                positive += scale * sub(state[1][q], base)
                negative += scale * sub(base, state[1][q])
            else:
                for r in range(i, j): P[r] += scale
                positive += scale * sub(base, state[0][q])
                negative += scale * sub(state[0][q], base)
        return P, S, positive, negative, at

    def numeric(self, state, word):
        assert all(l <= u for l, u in zip(state[0][:8], state[1][:8]))
        env = {"s." + name: value for name, value in zip(self.m["st_names"], self.flat(state))}
        env.update(cN=self.m["CN"], true=True, false=False, top=self.m["TOP"], bk="BK")
        point = self.m["point_value"]
        packed = lambda p: point(p) & ((1 << 96) - 1)
        env["f"] = packed
        at = 0
        for i, j, coefficient, slot in self.m["TS"]:
            low, high = self.bounds(state, i, j)
            assert low <= high
            decoded, at = self.decode_term(word, at, low, high)
            kind, mass, p, r = decoded
            assert mass <= 1024
            for stem, value in zip(["k", "m", "p", "r"], decoded): env[stem + str(i) + str(j)] = value
            self.count["term_decode_checks"] += 1
            for amount, sample in zip(self.weights(kind, mass), (p, r)):
                if not amount: continue
                assert sample in self.m["pts"]
                actual = point(sample)
                A, B = (actual >> 96) & ((1 << 24) - 1), actual >> 120
                assert 1 <= B and A <= low <= sample <= high <= B
                self.count["active_mokI_checks"] += 1
                self.count["active_tangent_mass"] += amount
        P, S, cp, cm, at = self.flow(state, word, at)
        env.update({"P" + str(r): P[r] for r in range(8)})
        env.update({"S" + str(r): S[r] for r in range(8)})
        env.update(Cp=cp, Cm=cm)
        def kernel_loss(function, sign, lower, kind, mass, p, r):
            total = 0
            for amount, sample in zip(self.weights(kind, mass), (p, r)):
                derivative = function(sample) >> 64
                signed = sub(derivative, 2000000000) if sign else sub(2000000000, derivative)
                total += amount * signed * sub(sample, lower)
            return total
        def slope(function, kind, mass, p, r):
            a, b = self.weights(kind, mass)
            return a * ((function(p) >> 32) & self.mask32) + b * ((function(r) >> 32) & self.mask32)
        def mixed(top, bk, function, lower, upper, kind, mass, p, r):
            a, b = self.weights(kind, mass)
            return sub(1024, a + b) * self.lower_bound(lower, upper) + a * (function(p) & self.mask32) + b * (function(r) & self.mask32)
        env.update({"Nat.add": lambda a, b: a + b, "Nat.mul": lambda a, b: a * b, "Nat.sub": sub,
            "Nat.ble": lambda a, b: (a, b), "nmax": max, "nmin": min, "uc": lambda a, b: max(b, a + 1),
            "tf": lambda function: function, "mcK": kernel_loss, "mslK": slope,
            "mvKF": mixed, "mwT": lambda k, q: sum(self.weights(k, q))})
        def ev(tree):
            if isinstance(tree, str): return int(tree) if tree.isdecimal() else env[tree]
            return ev(tree[0])(*(ev(arg) for arg in tree[1:]))
        lhs, rhs = ev(self.m["margin_tree"])
        assert rhs >= lhs
        self.count["numeric_leaves"] += 1
        self.count["direct_AST_comparisons"] += 1
        return at, rhs - lhs

    def run_root(self, r):
        self.nodes = {}; count_before = self.count.copy(); minimum = None; minpos = None
        rootrec = self.m["roots"][r]
        def walk(state, pos, fuel):
            nonlocal minimum, minpos
            assert fuel > 0 and pos not in self.nodes
            assert all(0 <= x < self.BB for x in state[0] + state[1])
            self.count["nodes"] += 1
            entry = dict(state=state, fuel=fuel)
            self.nodes[pos] = entry
            word = (self.m["dispatch_value"](f"WL{r}", pos // 32768) >> (pos % 32768)) & ((1 << 480) - 1)
            if word & 1:
                axis, mode = (word >> 1) & 63, (word >> 7) & 1
                assert axis < 36
                low, high = state[0][axis], state[1][axis]
                cut = (low + high) // 2
                if mode:
                    selected = [(abs(2 * z - low - high), ix, z) for ix, z in enumerate(self.m["BND"])
                                if low + 64 <= z and z + 64 <= high]
                    if selected: cut = min(selected)[2]
                assert cut < self.BB
                a, b = self.m["ALL"][axis]
                endleft, leftheight = walk(self.split(state, a, b, cut, True), pos + 8, fuel - 1)
                end, rightheight = walk(self.split(state, a, b, cut, False), endleft, fuel - 1)
                height = max(leftheight, rightheight) + 1
                entry.update(kind="branch", left=pos + 8, right=endleft, end=end, height=height)
                event = dict(root=r, pos=pos, kind="branch", axis=axis, mode=mode, cut=cut,
                             left=pos + 8, right=endleft, end=end, state_sha256=self.hashstate(state))
                self.count["branches"] += 1
                self.count["split_nat_sub_preconditions"] += 2
            else:
                self.count["terminal_leaves"] += 1
                margin = None
                if state[1][7] < state[0][0]:
                    kind, end = "reflection", pos + 1
                    self.count["reflection_leaves"] += 1
                elif (word >> 1) & 1:
                    P, S, cp, cm, used = self.flow(state, word >> 2, 0)
                    margin = cm - cp - sum(sub(p, s) * sub(u, l) for p, s, u, l in zip(P, S, state[1][:8], state[0][:8]))
                    assert margin > 0
                    kind, end = "farkas", pos + 2 + used
                    self.count["farkas_leaves"] += 1
                else:
                    used, margin = self.numeric(state, word >> 2)
                    kind, end = "numeric", pos + 2 + used
                    if minimum is None or margin < minimum: minimum, minpos = margin, pos
                height = 1
                entry.update(kind=kind, end=end, height=height, margin=margin)
                event = dict(root=r, pos=pos, kind=kind, end=end, margin=margin, state_sha256=self.hashstate(state))
            self.trace.update(canon(event)); self.count["trace_events"] += 1
            return end, height
        actual, height = walk(self.root(rootrec["indices"]), rootrec["pos"], rootrec["fuel"])
        assert actual == rootrec["expected"]
        covered = set()
        def cutwalk(state, pos, fuel, cutlist):
            assert fuel > 0
            node = self.nodes[pos]
            assert self.flat(node["state"]) == state
            self.contract_count["cutwalk_state_equalities"] += 1
            for at, name, end in cutlist:
                if at == pos:
                    assert self.m["states"][name] == state and node["end"] == end
                    self.contract_count["cut_hits"] += 1
                    return end
            if node["kind"] != "branch": return node["end"]
            middle = cutwalk(self.flat(self.nodes[node["left"]]["state"]), node["left"], fuel - 1, cutlist)
            assert middle == node["right"]
            return cutwalk(self.flat(self.nodes[middle]["state"]), middle, fuel - 1, cutlist)
        records = sorted((c for c in self.m["cursors"] if c["root"] == r), key=lambda row: row["index"])
        assert [c["index"] for c in records] == list(range(len(records)))
        for rec in records:
            cutlist = self.m["cuts"][rec["cuts"]]
            assert all(name in covered for _, name, _ in cutlist)
            state = self.m["states"][rec["state"]]
            actual = cutwalk(state, rec["pos"], rec["fuel"], cutlist)
            assert actual == rec["expected"] and actual != 0
            covered.add(rec["state"])
            self.contracts.append({**rec, "actual": actual, "state_sha256": sha256(canon(state)).hexdigest(), "passed": True})
        cutlist = self.m["cuts"][f'ready{r}_cuts{rootrec["cuts"]}']
        assert all(name in covered for _, name, _ in cutlist)
        assert cutwalk(self.flat(self.nodes[1]["state"]), 1, rootrec["fuel"], cutlist) == rootrec["expected"]
        self.contract_count["parent_cursor_checks"] += 1
        self.contract_count["nested_cursor_checks"] += len(records)
        self.rows.append(dict(root=r, end=rootrec["expected"], height=height,
            counts=dict(self.count - count_before), min_original_margin=minimum, min_margin_position=minpos))
        if minimum is not None and (self.minmargin is None or minimum < self.minmargin[0]):
            self.minmargin = (minimum, r, minpos)


def main():
    assert __debug__ and not any(p.exists() for p in [START, OUT, FAIL])
    begun = time.monotonic()
    assert pin(PROD / "files.json")["sha256"] == PROD_MANIFEST_SHA
    manifest = json.loads((PROD / "files.json").read_text(encoding="utf-8"))
    producer_rows = manifest.get("package_files", manifest.get("files", []))
    assert producer_rows
    for row in producer_rows:
        assert pin(ROOT / row["path"]) == row, ("producer_pin", row["path"])
    inputs = [Path(__file__), SRC, PROD / "files.json", PROD / "baseline-replay.json", PROD / "root-wz-replay.json",
        PROD / "stage-a-summary.json", ROOT / "research-goal-20261018-record-packing-independent/decode_packing.py"]
    before = [pin(p) for p in inputs]
    START.write_text(json.dumps({"scope": "One independent original-floor finite replay", "inputs": before}, indent=2) + "\n", encoding="utf-8")
    runner = None
    try:
        model = load_source()
        runner = Replay(model)
        for root in range(48):
            runner.run_root(root)
            if root % 8 == 7:
                print(json.dumps({"completed_roots": root + 1, "numeric_leaves": runner.count["numeric_leaves"], "seconds": time.monotonic() - begun}), flush=True)
        producer = json.loads((PROD / "baseline-replay.json").read_text(encoding="utf-8"))
        assert dict(runner.count) == producer["derived_counts"], ("count_mismatch", dict(runner.count), producer["derived_counts"])
        assert dict(runner.contract_count) == producer["ready_contract_counts"]
        assert runner.trace.hexdigest() == producer["trace"]["uncompressed_canonical_jsonl_sha256"]
        assert runner.contracts == producer["all70_ready_contracts"]
        assert runner.minmargin == (producer["minimum_original_integer_margin"], producer["minimum_root"], producer["minimum_position"])
        for left, right in zip(runner.rows, producer["per_root"]):
            for key, value in left.items(): assert value == right[key], ("root_row", left["root"], key)
        # Recalculate exactly the existing original root queries, not new anchors.
        wz_rows = []
        adjacency = {i: a for i, j, a, slot in model["TS"] if j == i + 1}
        SW = 10**13
        for gap, row in enumerate(model["COV"]):
            cursor = 16384
            for low, high, good in row:
                assert cursor == low <= high < 1048576
                cursor = high
                if good:
                    value = root_wz(model["text"], low, high)
                    lhs, rhs = model["CN"] * SW, adjacency[gap] * value
                    assert lhs <= rhs
                    wz_rows.append(dict(gap=gap, lo=low, hi=high, adjacent_coefficient=adjacency[gap], WZ=value,
                        left_cN_times_SW=lhs, right_a_times_WZ=rhs, margin=rhs-lhs, passed=True))
            assert cursor == model["SMAX"][gap]
            assert model["BS"][gap] * cursor >= model["CN"] * 32768
            assert adjacency[gap] >= model["CN"] * 4
        assert 8 * 1048576 <= model["rcM"]
        producer_wz = json.loads((PROD / "root-wz-replay.json").read_text(encoding="utf-8"))
        assert wz_rows == producer_wz["all_guard_rows"] and len(wz_rows) == 160
        after = [pin(p) for p in inputs]
        assert before == after
        result = dict(schema="independent-new-record-original-floor-finite-review-v1", passed=True,
            producer_manifest_sha256=PROD_MANIFEST_SHA, inputs_sha256_start=before, inputs_sha256_end=after,
            source_sha256=SRC_SHA, original_cN=model["CN"], threshold_changed=False,
            producer_Python_modules_imported=0, shared_helper="Own independently frozen positional packing decoder only",
            independent_algorithms="Signed 9x9 graph rank-one split; actual BL8 semantics; actual pwD absolute interval reconstruction; source printed Nat.ble AST; Fraction outward WZ",
            derived_counts=dict(runner.count), ready_contract_counts=dict(runner.contract_count),
            root_count=len(runner.rows), corrected_independent_WD_identity_count=48,
            all_producer_counts_and_root_rows_equal=True, all70_nested_contracts_equal=True,
            canonical_trace_sha256=runner.trace.hexdigest(), canonical_trace_equal_producer=True,
            minimum_original_integer_margin=runner.minmargin[0], minimum_root=runner.minmargin[1], minimum_position=runner.minmargin[2],
            original_root_true_WZ_guard_count=len(wz_rows), all160_WZ_values_and_margins_equal_producer=True,
            minimum_root_guard_margin=min(row["margin"] for row in wz_rows),
            source_dispatch_identity_checks=model["dispatch_checks"], point_tree_literal_entries=len(model["pts"]),
            per_root=runner.rows, all70_contracts=runner.contracts, all_original_WZ_guards=wz_rows,
            analytic_LB_PT_WZ_soundness_reproved=False, Lean_runs=0, solver_calls=0,
            new_threshold_classification=False, new_kernel_anchor_queries=0, exception_pairs_scanned=0,
            new_global_floor_proven=False, new_unconditional_zero_proportion_proven=False, website_submission_ready=False,
            scope="Independent original finite argument/guard replay with source analytic theorems retained; not Lean/nanoda/Comparator acceptance or new floor",
            seconds=time.monotonic()-begun)
        OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({"passed": True, "derived_counts": result["derived_counts"], "trace_sha256": result["canonical_trace_sha256"], "root_WZ": len(wz_rows), "seconds": result["seconds"]}), flush=True)
    except BaseException as exc:
        failure = dict(passed=False, error=repr(exc), traceback=traceback.format_exc(),
            completed_roots=len(runner.rows) if runner else 0,
            partial_counts=dict(runner.count) if runner else {}, seconds=time.monotonic()-begun)
        FAIL.write_text(json.dumps(failure, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
        print(json.dumps(failure), flush=True)
        raise


if __name__ == "__main__":
    main()
