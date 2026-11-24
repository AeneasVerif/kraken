#!/usr/bin/env python3
"""Deterministic 10-family adversarial tricky-UNSAT canary suite for C0 Kissat.

Every generated CNF is mathematically UNSAT and targets a concrete algorithmic
or capacity cliff across the Kissat C0 inprocessing and search passes:
  01_php_bva          - PHP(10..12) + 6-CNF/7-CNF product BVA matrices (sz > 5)
  02_deep_miter       - 16/32-bit adder miters (depth > 6), 5x5 mult, pure-3-CNF XOR/ITE
  03_sweep_algebraic  - Non-structural algebraic sweeping miters (cones 120..240 vars)
  04_pure3cnf_tseitin - Pure-3-CNF 3-regular Tseitin (n=40..60), Urquhart U3/U4, 3-XOR
  05_bve_vivify       - BVE-resistant balanced 3-SAT core + ternary-trigger vivifiable 8-clauses
  06_deep_chrono      - Multi-component decision depth >= 180 (> chrono_levels=100)
  07_high_fanout_bve  - Reverse-ordered gate-BVE chains with occ in [45..100]
  08_long_horizon     - Long-horizon search/reduction (ordering, pebbling, Mycielski, 3-SAT)
  09_big_backbone     - 500..600v BIG DAG with transitive shortcuts + backbones at v >= 100
  10_dead_var_compact - 5k..10k trivially eliminable dead vars wrapping an UNSAT core
"""

import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

import argparse
import json
import os
import random

from cnf_families import (
    encode_xor_lits,
    gen_graph_kcol,
    gen_pebbling_pyramid,
    gen_php,
    make_prism_edges,
    write_cnf,
)


class CircuitBuilder:
    def __init__(self, n_inputs):
        self.nvars = n_inputs
        self.clauses = []
        self.gates = []

    def fresh(self):
        self.nvars += 1
        return self.nvars

    def add_and(self, a, b):
        y = self.fresh()
        self.clauses.extend([[-y, a], [-y, b], [y, -a, -b]])
        self.gates.append(("AND", y, (a, b)))
        return y

    def add_or(self, a, b):
        y = self.fresh()
        self.clauses.extend([[y, -a], [y, -b], [-y, a, b]])
        self.gates.append(("OR", y, (a, b)))
        return y

    def add_xor(self, a, b):
        y = self.fresh()
        self.clauses.extend(encode_xor_lits([a, b, y], 0))
        self.gates.append(("XOR", y, (a, b)))
        return y

    def add_ite(self, c, t, e, consensus=False):
        y = self.fresh()
        self.clauses.extend([[-c, -t, y], [-c, t, -y], [c, -e, y], [c, e, -y]])
        if consensus:
            self.clauses.extend([[-t, -e, y], [t, e, -y]])
        self.gates.append(("ITE", y, (c, t, e)))
        return y

    def eval_lit(self, lit, env):
        v = env[abs(lit)]
        return v if lit > 0 else (not v)

    def eval_all(self, input_bits):
        env = [False] * (self.nvars + 1)
        for i, b in enumerate(input_bits, start=1):
            env[i] = b
        for kind, y, args in self.gates:
            if kind == "AND":
                env[y] = self.eval_lit(args[0], env) and self.eval_lit(args[1], env)
            elif kind == "OR":
                env[y] = self.eval_lit(args[0], env) or self.eval_lit(args[1], env)
            elif kind == "XOR":
                env[y] = self.eval_lit(args[0], env) != self.eval_lit(args[1], env)
            elif kind == "ITE":
                c = self.eval_lit(args[0], env)
                env[y] = self.eval_lit(args[1], env) if c else self.eval_lit(args[2], env)
        return env


def record(manifest, out_dir, fname, family, nvars, clauses, meta):
    path = os.path.join(out_dir, fname)
    stats = write_cnf(path, nvars, clauses, comment=f"canary {family}: {meta['desc']}")
    entry = {
        "file": fname,
        "family": family,
        "expected_status": 20,
        "stats": stats,
    }
    entry.update(meta)
    manifest.append(entry)


# ---------------------------------------------------------------------------
# Family 1: PHP(10..12) & Product BVA Matrices (sz > 5)
# ---------------------------------------------------------------------------
def gen_family_01(out_dir, manifest):
    fam = "01_php_bva"
    for p in (10, 11, 12):
        h = p - 1
        nv, cls = gen_php(p, h)
        record(
            manifest, out_dir, f"c01_php_{p}_{h}.cnf", fam, nv, cls,
            {
                "desc": f"Standard UNSAT PHP({p},{h}) targeting BVA/factoring",
                "cliff": "factor.c 3-hop heap, bva_cap, red > elim_bound",
                "expected_gap": "M3-bva-bound",
                "min_counters": {"bva": 10 if p == 10 else 20},
                "kissat_confl_mult": 3.0,
                "kissat_confl_add": 500,
            },
        )

    # Shuffled PHP(10,9)
    rng = random.Random(100109)
    nv, cls = gen_php(10, 9)
    perm = list(range(1, nv + 1))
    rng.shuffle(perm)
    pcls = []
    for cl in cls:
        ncl = [perm[abs(l) - 1] * (1 if l > 0 else -1) for l in cl]
        rng.shuffle(ncl)
        pcls.append(ncl)
    rng.shuffle(pcls)
    record(
        manifest, out_dir, "c01_php_10_9_shuf.cnf", fam, nv, pcls,
        {
            "desc": "Permuted UNSAT PHP(10,9) targeting order-independent BVA",
            "cliff": "factor.c heap ordering & bva_cap",
            "expected_gap": "M3-bva-bound",
            "min_counters": {"bva": 10},
            "kissat_confl_mult": 3.0,
            "kissat_confl_add": 500,
        },
    )

    # Large-clause (sz=6 and sz=7) product BVA matrices:
    # (/\_i /\_j (l_i \/ K_j)) /\ (~l_1 \/ ... \/ ~l_m), where {K_j} is all 2^k k-clauses
    # over k cube variables. Strictly UNSAT; BVA collapses m*2^k clauses -> m + 2^k.
    for tag, m_lits, k_cube in [("prod6_8x32", 8, 5), ("prod7_10x64", 10, 6)]:
        nv = m_lits + k_cube
        ls = list(range(1, m_lits + 1))
        vs = list(range(m_lits + 1, nv + 1))
        cube = [
            [-v if ((mask >> b) & 1) else v for b, v in enumerate(vs)]
            for mask in range(1 << k_cube)
        ]
        cls = [[-l for l in ls]]
        for l in ls:
            for kcl in cube:
                cls.append([l] + kcl)
        record(
            manifest, out_dir, f"c01_bva_{tag}.cnf", fam, nv, cls,
            {
                "desc": f"Size-{k_cube + 1} product BVA matrix ({m_lits}x{1 << k_cube}, all sz={k_cube + 1})",
                "cliff": "FullBvaHeap sz <= 5 cap & red > elim_bound gate",
                "expected_gap": "M3-bva-sz5",
                "min_counters": {"bva": 1},
                "kissat_confl_mult": 3.0,
                "kissat_confl_add": 500,
            },
        )


# ---------------------------------------------------------------------------
# Family 2: Deep & Binary-Free Circuit Miters
# ---------------------------------------------------------------------------
def gen_family_02(out_dir, manifest):
    fam = "02_deep_miter"

    # 2a. 16-bit and 32-bit ripple-carry adder commutativity miters (depth 32..64 > 6)
    for w in (16, 32):
        cb = CircuitBuilder(2 * w)
        a = list(range(1, w + 1))
        b = list(range(w + 1, 2 * w + 1))

        def build_adder(xs, ys, flip_or):
            c = None
            sums = []
            for i in range(w):
                axb = cb.add_xor(xs[i], ys[i])
                if c is None:
                    s = axb
                    cout = cb.add_and(xs[i], ys[i])
                else:
                    s = cb.add_xor(axb, c)
                    g1 = cb.add_and(xs[i], ys[i])
                    g2 = cb.add_and(axb, c)
                    cout = (-cb.add_and(-g1, -g2)) if flip_or else cb.add_or(g1, g2)
                sums.append(s)
                c = cout
            sums.append(c)
            return sums

        s1 = build_adder(a, b, flip_or=False)
        s2 = build_adder(b, a, flip_or=True)
        diffs = [cb.add_xor(x, y) for x, y in zip(s1, s2)]
        mout = diffs[0]
        for d in diffs[1:]:
            mout = cb.add_or(mout, d)
        cls = cb.clauses + [[mout]]
        record(
            manifest, out_dir, f"c02_miter_add{w}.cnf", fam, cb.nvars, cls,
            {
                "desc": f"{w}-bit ripple-carry adder commutativity miter (depth > {2 * w})",
                "cliff": "congruence 6-pass depth cap & ht_sz <= 4096",
                "expected_gap": "M3-cong-depth6",
                "min_counters": {"cong": 30},
                "kissat_confl_mult": 2.0,
                "kissat_confl_add": 50,
            },
        )

    # 2b. 5x5 multiplier commutativity miter (A*B == B*A via Braun array)
    for w in (5,):
        cb = CircuitBuilder(2 * w)
        a = list(range(1, w + 1))
        b = list(range(w + 1, 2 * w + 1))

        def build_mul(xs, ys, swap_and):
            # Accumulate w shifted partial-product rows with full/half adders
            acc = [None] * (2 * w)
            for i in range(w):
                row = [
                    cb.add_and(ys[j], xs[i]) if swap_and else cb.add_and(xs[i], ys[j])
                    for j in range(w)
                ]
                carry = None
                for j in range(w):
                    col = i + j
                    if acc[col] is None and carry is None:
                        acc[col] = row[j]
                    elif acc[col] is None:
                        s = cb.add_xor(row[j], carry)
                        carry = cb.add_and(row[j], carry)
                        acc[col] = s
                    elif carry is None:
                        s = cb.add_xor(acc[col], row[j])
                        carry = cb.add_and(acc[col], row[j])
                        acc[col] = s
                    else:
                        t = cb.add_xor(acc[col], row[j])
                        s = cb.add_xor(t, carry)
                        g1 = cb.add_and(acc[col], row[j])
                        g2 = cb.add_and(t, carry)
                        carry = (-cb.add_and(-g1, -g2)) if swap_and else cb.add_or(g1, g2)
                        acc[col] = s
                if carry is not None:
                    acc[i + w] = carry
            return acc

        p1 = build_mul(a, b, swap_and=False)
        p2 = build_mul(b, a, swap_and=True)
        diffs = [cb.add_xor(x, y) for x, y in zip(p1, p2)]
        mout = diffs[0]
        for d in diffs[1:]:
            mout = cb.add_or(mout, d)
        cls = cb.clauses + [[mout]]
        record(
            manifest, out_dir, f"c02_miter_mul{w}.cnf", fam, cb.nvars, cls,
            {
                "desc": f"{w}x{w} Braun multiplier commutativity miter",
                "cliff": "congruence depth > 6 & AND/OR DeMorgan folding",
                "expected_gap": "M3-cong-depth6",
                "min_counters": {"cong": 25},
                "kissat_confl_mult": 2.0,
                "kissat_confl_add": 50,
            },
        )

    # 2c. Pure-3-CNF XOR/ITE deep miter (num_binary == 0, every clause size 3, nvars >= 100)
    rng = random.Random(200301)
    n_in = 12
    n_gates = 48
    cb = CircuitBuilder(n_in)
    w1 = list(range(1, n_in + 1))
    w2 = list(range(1, n_in + 1))
    for g in range(n_gates):
        if g % 2 == 0:
            i1, i2 = rng.sample(range(len(w1)), 2)
            s1 = -1 if rng.getrandbits(1) else 1
            y1 = cb.add_xor(s1 * w1[i1], w1[i2])
            y2 = cb.add_xor(w2[i2], s1 * w2[i1])
        else:
            i1, i2, i3 = rng.sample(range(len(w1)), 3)
            y1 = cb.add_ite(w1[i1], w1[i2], w1[i3], consensus=False)
            y2 = cb.add_ite(-w2[i1], w2[i3], w2[i2], consensus=False)
        w1.append(y1)
        w2.append(y2)
    o1, o2 = w1[-1], w2[-1]
    # Pure-3-CNF encoding of o1 != o2 using two fresh aux vars u, v:
    u = cb.fresh()
    v = cb.fresh()
    cls = cb.clauses + [
        [o1, o2, u], [o1, o2, -u],
        [-o1, -o2, v], [-o1, -o2, -v],
    ]
    assert all(len(c) == 3 for c in cls), "pure-3-CNF miter violated"
    record(
        manifest, out_dir, "c02_miter_pure3_xor_ite.cnf", fam, cb.nvars, cls,
        {
            "desc": "Pure-3-CNF 48-gate XOR/ITE miter (0 binaries, nvars=110, depth > 12)",
            "cliff": "FullFastSched pure-3-CNF bypass + num_binary < 4 dense gate + depth > 6",
            "expected_gap": "M3-pure3-bypass",
            "min_counters": {"cong": 30},
            "kissat_confl_mult": 2.0,
            "kissat_confl_add": 50,
        },
    )


# ---------------------------------------------------------------------------
# Family 3: Non-Structural Algebraic Sweeping (cones 120..240 vars)
# ---------------------------------------------------------------------------
def gen_family_03(out_dir, manifest):
    fam = "03_sweep_algebraic"
    for tag, n_in, n_layers in [("cone140", 14, 24), ("cone230", 18, 40)]:
        rng = random.Random(300100 + n_layers)
        cb = CircuitBuilder(n_in)
        w1 = list(range(1, n_in + 1))
        w2 = list(range(1, n_in + 1))
        for layer in range(n_layers):
            i1, i2, i3 = rng.sample(range(len(w1)), 3)
            a1, b1, c1 = w1[i1], w1[i2], w1[i3]
            a2, b2, c2 = w2[i1], w2[i2], w2[i3]
            kind = layer % 4
            if kind == 0:
                # AND(a, b) == AND(OR(a, c), ITE(a, b, AND(a, -c)))
                y1 = cb.add_and(a1, b1)
                t_or = cb.add_or(a2, c2)
                t_an = cb.add_and(a2, -c2)
                t_it = cb.add_ite(a2, b2, t_an)
                y2 = cb.add_and(t_or, t_it)
            elif kind == 1:
                # XOR(a, b) == OR(AND(a, -b), AND(-a, b))
                y1 = cb.add_xor(a1, b1)
                p1 = cb.add_and(a2, -b2)
                p2 = cb.add_and(-a2, b2)
                y2 = cb.add_or(p1, p2)
            elif kind == 2:
                # ITE(c, a, b) == OR(AND(c, a), AND(-c, b))
                y1 = cb.add_ite(c1, a1, b1)
                p1 = cb.add_and(c2, a2)
                p2 = cb.add_and(-c2, b2)
                y2 = cb.add_or(p1, p2)
            else:
                # Absorption: OR(a, AND(b, c)) == AND(OR(a, b), OR(a, c))
                y1 = cb.add_or(a1, cb.add_and(b1, c1))
                y2 = cb.add_and(cb.add_or(a2, b2), cb.add_or(a2, c2))
            w1.append(y1)
            w2.append(y2)

        o1, o2 = w1[-1], w2[-1]
        # Empirical sanity check on 32 random inputs: o1 == o2 must hold identically!
        for t in range(32):
            inp = [bool((t >> (k % 5)) & 1) if t < 16 else bool(rng.getrandbits(1)) for k in range(n_in)]
            env = cb.eval_all(inp)
            assert cb.eval_lit(o1, env) == cb.eval_lit(o2, env), "algebraic miter bug!"

        cls = cb.clauses + [[o1, o2], [-o1, -o2]]
        record(
            manifest, out_dir, f"c03_sweep_{tag}.cnf", fam, cb.nvars, cls,
            {
                "desc": f"Non-structural algebraic sweeping miter ({cb.nvars} vars, {n_layers} layers)",
                "cliff": "sweep/kitten cone size (> 128), partition refinement, FL_SWEEP re-arm",
                "expected_gap": "M3-sweep-cone",
                "min_counters": {"sweep": 4},
                "kissat_confl_mult": 3.0,
                "kissat_confl_add": 200,
            },
        )


# ---------------------------------------------------------------------------
# Family 4: Pure-3-CNF Tseitin (n=40..60), Urquhart U3/U4, 3-XOR Systems
# ---------------------------------------------------------------------------
def gen_tseitin_3reg(nverts, edges, charges):
    inc = [[] for _ in range(nverts)]
    for eidx, (u, v) in enumerate(edges):
        var = eidx + 1
        inc[u].append(var)
        inc[v].append(var)
    clauses = []
    for v in range(nverts):
        assert len(inc[v]) == 3, f"vertex {v} degree {len(inc[v])} != 3"
        clauses.extend(encode_xor_lits(inc[v], charges[v] & 1))
    return len(edges), clauses


def gen_urquhart_pure3(m):
    """Urquhart parity formula U_m on m x m 4-regular torus, split into pure 3-CNF."""
    # Vertices (r, c) in Z_m x Z_m: degree 4 (horiz + vert torus edges)
    edges = []
    inc = [[] for _ in range(m * m)]
    for r in range(m):
        for c in range(m):
            u = r * m + c
            v_h = r * m + ((c + 1) % m)
            v_v = ((r + 1) % m) * m + c
            eh = len(edges) + 1
            edges.append((u, v_h))
            inc[u].append(eh)
            inc[v_h].append(eh)
            ev = len(edges) + 1
            edges.append((u, v_v))
            inc[u].append(ev)
            inc[v_v].append(ev)
    nxt = len(edges) + 1
    clauses = []
    # Odd total charge: vertex 0 has charge 1, all others 0 -> UNSAT
    for u in range(m * m):
        assert len(inc[u]) == 4
        e0, e1, e2, e3 = inc[u]
        t = nxt
        nxt += 1
        ch = 1 if u == 0 else 0
        clauses.extend(encode_xor_lits([e0, e1, t], 0))
        clauses.extend(encode_xor_lits([t, e2, e3], ch))
    return nxt - 1, clauses


def gen_family_04(out_dir, manifest):
    fam = "04_pure3cnf_tseitin"
    for nverts in (40, 50, 60):
        edges = make_prism_edges(nverts // 2)
        charges = [1] + [0] * (nverts - 1)
        nv, cls = gen_tseitin_3reg(nverts, edges, charges)
        assert all(len(c) == 3 for c in cls)
        record(
            manifest, out_dir, f"c04_tseitin_3reg_n{nverts}.cnf", fam, nv, cls,
            {
                "desc": f"Pure-3-CNF 3-regular prism Tseitin ({nverts} verts, {nv} vars, 0 binaries)",
                "cliff": "FullFastSched pure-3-CNF preproc bypass (cur_vars >= 48 && num_binary == 0)",
                "expected_gap": "M3-pure3-bypass",
                "min_counters_any": {"bve": 1, "cong": 1},
                "kissat_confl_mult": 4.0,
                "kissat_confl_add": 2000,
            },
        )

    for m in (3, 4):
        nv, cls = gen_urquhart_pure3(m)
        assert all(len(c) == 3 for c in cls)
        record(
            manifest, out_dir, f"c04_urquhart_u{m}.cnf", fam, nv, cls,
            {
                "desc": f"Pure-3-CNF Urquhart parity torus U_{m} ({nv} vars, 0 binaries)",
                "cliff": "Pure-3-CNF bypass + 3-XOR BVE / CDCL parity",
                "expected_gap": "M3-pure3-bypass",
                "min_counters_any": {"bve": 1, "cong": 1},
                "kissat_confl_mult": 4.0,
                "kissat_confl_add": 2000,
            },
        )

    # Sparse pure-3-CNF 3-XOR UNSAT system (n=60, 0 binaries)
    rng = random.Random(400060)
    n = 60
    sol = [False] + [bool(rng.getrandbits(1)) for _ in range(n)]
    cls = []
    # 10-row unsatisfiable GF(2) 3-XOR cycle over 15 vars:
    # Build chain of 8 linked triples summing to 0 with 1 flipped rhs
    pv = rng.sample(range(1, n + 1), 16)
    # (p0^p1^p2)=0, (p2^p3^p4)=0, (p4^p5^p6)=0, (p6^p7^p0)=0, (p1^p3^p5)=0?
    # Clean exact cancellation: sum of two cycles sharing edge pairs:
    # a0^b0^c0 = 0, a0^b0^c1 = 0  => c0 == c1
    # c1^d0^e0 = 0, d0^e0^c2 = 0  => c1 == c2
    # c2^f0^g0 = 0, f0^g0^c3 = 0  => c2 == c3
    # c3^h0^k0 = 0, h0^k0^c0 = 1  => c3 != c0 (contradiction!)
    c0, c1, c2, c3 = pv[0], pv[1], pv[2], pv[3]
    pairs = [(pv[4], pv[5]), (pv[6], pv[7]), (pv[8], pv[9]), (pv[10], pv[11])]
    cycle_rows = [
        ([c0, pairs[0][0], pairs[0][1]], 0),
        ([c1, pairs[0][0], pairs[0][1]], 0),
        ([c1, pairs[1][0], pairs[1][1]], 0),
        ([c2, pairs[1][0], pairs[1][1]], 0),
        ([c2, pairs[2][0], pairs[2][1]], 0),
        ([c3, pairs[2][0], pairs[2][1]], 0),
        ([c3, pairs[3][0], pairs[3][1]], 0),
        ([c0, pairs[3][0], pairs[3][1]], 1),
    ]
    for _ in range(n):
        vs = rng.sample(range(1, n + 1), 3)
        rhs = int(sol[vs[0]]) ^ int(sol[vs[1]]) ^ int(sol[vs[2]])
        cls.extend(encode_xor_lits(vs, rhs))
    for vs, rhs in cycle_rows:
        cls.extend(encode_xor_lits(vs, rhs))
    rng.shuffle(cls)
    assert all(len(c) == 3 for c in cls)
    record(
        manifest, out_dir, "c04_xor3_sys_n60.cnf", fam, n, cls,
        {
            "desc": "Pure-3-CNF 60-var sparse 3-XOR UNSAT system (0 binaries)",
            "cliff": "Pure-3-CNF preproc bypass + 3-XOR congruence/BVE",
            "expected_gap": "M3-pure3-bypass",
            "min_counters_any": {"bve": 1, "cong": 1},
            "kissat_confl_mult": 4.0,
            "kissat_confl_add": 2000,
        },
    )


# ---------------------------------------------------------------------------
# Family 5: BVE-Resistant Balanced-Core + Ternary-Trigger Vivification Canary
# ---------------------------------------------------------------------------
def _exact_balanced_3sat(rng, n_core, deg_each=7):
    """Build collision-free 3-CNF where every var 1..n_core has >= deg_each + and - occs."""
    assert n_core % 3 == 0
    signs = {}
    for v in range(1, n_core + 1):
        s = [1] * deg_each + [-1] * deg_each
        rng.shuffle(s)
        signs[v] = s
    clauses = []
    for p in range(2 * deg_each):
        perm = list(range(1, n_core + 1))
        rng.shuffle(perm)
        for i in range(0, n_core, 3):
            a, b, c = perm[i], perm[i + 1], perm[i + 2]
            clauses.append([signs[a][p] * a, signs[b][p] * b, signs[c][p] * c])
    return clauses


def _viv_trigger_gadget(rng, base_var, k_vars, n_trigs, n_bloat):
    """Build BVE-resistant ternary vivification triggers + bloated 8-clauses.

    Each trigger triple T_i = (l1, l2, l3) satisfies a fixed witness W on >= 1 literal,
    with clauses (l1 v l2 v l3 v tvar) and (l1 v l2 v l3 v -tvar). Every bloated 8-clause
    T_i + 5 random distinct gadget literals is NOT self-subsumable by any single clause,
    and every gadget/bridge variable resists preprocessing BVE via high occ / fanout.
    """
    tvar = base_var
    gvars = [base_var + 1 + i for i in range(k_vars)]
    witness = {v: rng.choice([-1, 1]) for v in gvars}
    triples = []
    seen = set()
    trigs = []
    while len(triples) < n_trigs:
        u, v, w = rng.sample(gvars, 3)
        lits = [rng.choice([-1, 1]) * u, rng.choice([-1, 1]) * v, rng.choice([-1, 1]) * w]
        if not any((l > 0 and witness[abs(l)] == 1) or (l < 0 and witness[abs(l)] == -1) for l in lits):
            idx = rng.randrange(3)
            lits[idx] = -lits[idx]
        key = tuple(sorted(lits))
        if key not in seen:
            seen.add(key)
            triples.append(lits)
            trigs.append(lits + [tvar])
            trigs.append(lits + [-tvar])
    bloated = []
    for idx in range(n_bloat):
        t = triples[idx % len(triples)]
        tv = {abs(x) for x in t}
        rs = rng.sample([x for x in gvars if x not in tv], 5)
        bloated.append(t + [r * rng.choice([-1, 1]) for r in rs])
    return base_var + k_vars, trigs, bloated


def gen_family_05(out_dir, manifest):
    fam = "05_bve_vivify"
    configs = [
        ("c05_bve_vivify_2600.cnf", 1, 132, 30, 450, 1100),
        ("c05_bve_vivify_3200.cnf", 3, 150, 30, 500, 1500),
    ]
    for fname, seed, n_core, k_vars, n_trigs, n_bloat in configs:
        core_rng = random.Random(seed)
        gadget_rng = random.Random(seed + 500)
        core = _exact_balanced_3sat(core_rng, n_core, deg_each=7)
        nvars, trigs, bloated = _viv_trigger_gadget(gadget_rng, n_core + 1, k_vars, n_trigs, n_bloat)
        clauses = trigs + bloated[: n_bloat // 2] + core + bloated[n_bloat // 2 :]
        record(
            manifest, out_dir, fname, fam, nvars, clauses,
            {
                "desc": (
                    f"BVE-resistant balanced 3-SAT core ({n_core}v) + {n_trigs} viv trigger pairs "
                    f"+ {n_bloat} bloated 8-clauses"
                ),
                "cliff": "Preproc BVE resistance (deg=7 core + high-occ viv triggers) exercising full_vivify",
                "expected_gap": "M3-bve-resistant-vivify",
                "min_counters": {"viv": 200, "conflicts": 1000, "probings": 1},
                "kissat_confl_mult": 2.0,
                "kissat_confl_add": 100,
            },
        )


# ---------------------------------------------------------------------------
# Family 6: Deep Multi-Component Chronological BT Trap (depth >= 180 > 100)
# ---------------------------------------------------------------------------
def gen_family_06(out_dir, manifest):
    fam = "06_deep_chrono"
    for depth in (180, 240):
        rng = random.Random(600000 + depth)
        # 3 independent satisfiable components of depth//3 vars each (total depth >= 180).
        # Every clause over 1..depth has >= 2 positive literals so initial phase +1 climbs
        # smoothly to decision level >= depth (> chrono_levels = 100) with 0 unit props!
        clauses = []
        comp_sz = depth // 3
        for c in range(3):
            base = c * comp_sz + 1
            comp = list(range(base, base + comp_sz))
            for _ in range(comp_sz * 3):
                vs = rng.sample(comp, 3)
                # Two positive, one negative -> satisfied under all-true without unit prop
                clauses.append([vs[0], vs[1], -vs[2]])

        # Place an unconditional UNSAT core (PHP(5,4) = 20 vars) AFTER the spine vars
        core_nv, core_cls = gen_php(5, 4, v_off=depth)
        nvars = depth + core_nv

        # Add satisfiable bridge clauses linking low-level & high-level spine vars with core vars
        # (always satisfied when spine vars are True, forcing deep chrono backtracking interactions)
        for k in range(40):
            v_lo = 1 + (k % 20)
            v_hi = depth - (k % 30)
            cv = depth + 1 + (k % core_nv)
            clauses.append([v_lo, -v_hi, cv])
            clauses.append([v_lo, -v_hi, -cv])
        clauses.extend(core_cls)

        record(
            manifest, out_dir, f"c06_deep_chrono_{depth}.cnf", fam, nvars, clauses,
            {
                "desc": f"3-component depth-{depth} (> 100) spine + PHP(5,4) UNSAT core",
                "cliff": "chrono_levels=100 lits[1] watch-swap on partial backtrack",
                "expected_gap": "M3-chrono-swap",
                "min_counters": {"conflicts": 10},
                "kissat_confl_mult": 2.5,
                "kissat_confl_add": 500,
            },
        )


# ---------------------------------------------------------------------------
# Family 7: High-Fanout & Reverse-Ordered Gate-BVE Chains (occ 45..100)
# ---------------------------------------------------------------------------
def gen_family_07(out_dir, manifest):
    fam = "07_high_fanout_bve"
    for fanout in (48, 88):
        rng = random.Random(700000 + fanout)
        # Build a base UNSAT core (PHP(5,4), 20 vars) mapped through a 6-layer gate stack,
        # numbered OUTPUT-TO-INPUT (lowest var IDs = deepest gates with high fanout,
        # highest var IDs = leaf unconstrained consumer gates d_k <-> AND(g, p_k)).
        # Eliminating d_k peels fanout off g, reducing occ(g) from ~fanout+4 down to ~5 —
        # punishing linear single-pass 0..cv-1 BVE without neighbor FL_ELIM_C re-marking
        # AND testing occ > 64!
        core_nv, core_cls = gen_php(5, 4)
        # Allocate 20 gate vars (vars 1..20) + 20 base vars (vars 21..40) + 20 selector vars (41..60)
        # Each gate var g_i (1..20) is defined as g_i <-> ITE(s_i, b_i, b_i) == b_i,
        # or g_i <-> XOR(b_i, c_zero) where c_zero is forced false via 2 binary clauses!
        # Even better: 10 chain layers of AND/ITE definitions around PHP(5,4) core vars!
        # Let vars 1..core_nv be the root PHP vars; for each v in 1..core_nv, attach `fanout`
        # unconstrained consumer AND-gates d_{v,k} <-> AND(v, p_{v,k}) (strictly equisatisfiable!).
        # Numbering: core/gate vars 1..20 FIRST, then dummy inputs, then consumer outputs LAST!
        n_gates = core_nv
        # Extra 2 layers of gate definitions above the first 12 core vars:
        # mid_i (1..12) <-> AND(inA_i, inB_i), root_i (13..24) <-> ITE(sel_i, mid_i, ...)
        # Keep it 100% equisatisfiable with PHP(5,4):
        # vars 1..20 = PHP vars (high fanout!), vars 21..60 = 40 extra gate vars defined on 1..20
        # vars 61..60+20 = aux inputs p_k, vars 81.. = consumer output gates d_{v,k} <-> AND(v, p_k)
        clauses = list(core_cls)
        aux_in = list(range(core_nv + 1, core_nv + 21))
        nxt = core_nv + 21
        # Add 20 intermediate semantic ITE gates y_i <-> ITE(aux_in[i], i+1, i+1) (numbered BEFORE consumers!)
        inter_gates = []
        for i in range(core_nv):
            y = nxt
            nxt += 1
            s = aux_in[i]
            v = i + 1
            # y <-> ITE(s, v, -aux_in[(i+1)%20]) is unconstrained output wire -> equisatisfiable!
            e = aux_in[(i + 1) % 20]
            clauses.extend([[-s, -v, y], [-s, v, -y], [s, -e, y], [s, e, -y]])
            inter_gates.append(y)

        # Attach high-fanout unconstrained consumer gates to each inter_gate (numbered AFTER inter_gates!)
        # Each inter_gate gets `fanout` consumer AND-gates -> occ(inter_gate) = fanout + 4!
        # In linear 0..cv-1 order, inter_gate is visited BEFORE consumers -> occ > 64 skipped and NEVER re-armed!
        n_consumers = 0
        for idx, g in enumerate(inter_gates):
            for k in range(fanout):
                d = nxt
                nxt += 1
                p = aux_in[(idx + k) % len(aux_in)]
                if k % 2 == 0:
                    clauses.extend([[-d, g], [-d, p], [d, -g, -p]])
                else:
                    clauses.extend([[d, -g], [d, -p], [-d, g, p]])
                n_consumers += 1
        nvars = nxt - 1
        record(
            manifest, out_dir, f"c07_bve_rev_occ{fanout}.cnf", fam, nvars, clauses,
            {
                "desc": f"Reverse-ordered gate-BVE with occ={fanout + 4} ({n_consumers} consumer + {len(inter_gates)} root gates)",
                "cliff": "BVE linear scan without neighbor FL_ELIM_C re-marking & occ > 64 cap",
                "expected_gap": "M3-bve-heap",
                "min_counters": {"bve": n_consumers + 15},
                "kissat_confl_mult": 2.0,
                "kissat_confl_add": 100,
            },
        )


# ---------------------------------------------------------------------------
# Family 8: Long-Horizon Search, Promotion & Clause Reduction (20k..200k confls)
# ---------------------------------------------------------------------------
def gen_ordering_principle(n):
    """Linear Ordering Principle LOP(n) / GT_n: irreflexive, transitive, no min -> UNSAT."""
    # Variable x(i, j) for 0 <= i < j < n means i < j (x(j, i) is -x(i, j))
    idx = {}
    nxt = 1
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = nxt
            nxt += 1

    def lt(i, j):
        assert i != j
        return idx[(i, j)] if i < j else -idx[(j, i)]

    clauses = []
    # Transitivity: (i < j) /\ (j < k) => (i < k)
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            for k in range(n):
                if k == i or k == j:
                    continue
                clauses.append([-lt(i, j), -lt(j, k), lt(i, k)])
    # No minimal element: for every j, there exists i != j with i < j
    for j in range(n):
        clauses.append([lt(i, j) for i in range(n) if i != j])
    return nxt - 1, clauses


def gen_mycielski_edges(k):
    """Construct Mycielski graph M_k (chromatic number = k). M_2 = K_2."""
    n = 2
    edges = [(0, 1)]
    for _ in range(2, k):
        old_n = n
        new_edges = list(edges)
        w = 2 * old_n
        for u, v in edges:
            new_edges.append((u, old_n + v))
            new_edges.append((v, old_n + u))
        for i in range(old_n):
            new_edges.append((old_n + i, w))
        n = 2 * old_n + 1
        edges = new_edges
    return n, edges


def gen_schur_unsat(k_colors, n_nums):
    """Schur(k, n): k-coloring of {1..n} with no monochromatic x+y=z (UNSAT for k=3, n>=14)."""
    def var(x, c):
        return (x - 1) * k_colors + c + 1

    clauses = []
    for x in range(1, n_nums + 1):
        clauses.append([var(x, c) for c in range(k_colors)])
        for c1 in range(k_colors):
            for c2 in range(c1 + 1, k_colors):
                clauses.append([-var(x, c1), -var(x, c2)])
    for x in range(1, n_nums + 1):
        for y in range(x, n_nums + 1):
            z = x + y
            if z <= n_nums:
                for c in range(k_colors):
                    clauses.append([-var(x, c), -var(y, c), -var(z, c)])
    return n_nums * k_colors, clauses


def gen_vdw_3color_3ap(n_nums):
    """van der Waerden W(3,3,3) = 27: 3-coloring {1..n} avoiding monochromatic 3-AP (UNSAT for n>=27)."""
    def var(x, c):
        return (x - 1) * 3 + c + 1

    clauses = []
    for x in range(1, n_nums + 1):
        clauses.append([var(x, 0), var(x, 1), var(x, 2)])
        clauses.append([-var(x, 0), -var(x, 1)])
        clauses.append([-var(x, 0), -var(x, 2)])
        clauses.append([-var(x, 1), -var(x, 2)])
    for a in range(1, n_nums + 1):
        for d in range(1, (n_nums - a) // 2 + 1):
            b, c = a + d, a + 2 * d
            for col in range(3):
                clauses.append([-var(a, col), -var(b, col), -var(c, col)])
    return n_nums * 3, clauses


def gen_family_08(out_dir, manifest):
    fam = "08_long_horizon"
    for n in (8, 9):
        nv, cls = gen_ordering_principle(n)
        record(
            manifest, out_dir, f"c08_ordering_{n}.cnf", fam, nv, cls,
            {
                "desc": f"Linear Ordering Principle LOP({n}) ({nv} vars, {len(cls)} clauses)",
                "cliff": "promote.c, reduce.c, EMA/restarts, VSIDS rescale",
                "expected_gap": "M3-promote-ema",
                "min_counters": {"conflicts": 500},
                "kissat_confl_mult": 3.0,
                "kissat_confl_add": 2000,
            },
        )

    nv, cls = gen_pebbling_pyramid(8)
    record(
        manifest, out_dir, "c08_pebbling_h8.cnf", fam, nv, cls,
        {
            "desc": f"2-pebbling pyramid height 8 ({nv} vars, {len(cls)} clauses)",
            "cliff": "CDCL clause learning, minimize/shrink, reductions",
            "expected_gap": "M3-promote-ema",
            "min_counters": {"conflicts": 100},
            "kissat_confl_mult": 3.0,
            "kissat_confl_add": 1000,
        },
    )

    # Mycielski M_5 (23 verts, chromatic number 5) -> 4-coloring UNSAT (hard search stress!)
    nv_g, edges = gen_mycielski_edges(5)
    nv, cls = gen_graph_kcol(nv_g, edges, 4)
    record(
        manifest, out_dir, "c08_mycielski5_4col.cnf", fam, nv, cls,
        {
            "desc": f"Mycielski M_5 4-coloring UNSAT ({nv} vars, {len(cls)} clauses)",
            "cliff": "Long-horizon promote.c, restarts, reductions, mode switching",
            "expected_gap": "M3-promote-ema",
            "min_counters": {"restarts": 20, "reductions": 2},
            "kissat_confl_mult": 3.0,
            "kissat_confl_add": 2000,
        },
    )

    # Schur(3, 14) UNSAT (S(3) = 13)
    nv, cls = gen_schur_unsat(3, 14)
    record(
        manifest, out_dir, "c08_schur_3_14.cnf", fam, nv, cls,
        {
            "desc": "Schur(3,14) UNSAT (S(3)=13, 42 vars)",
            "cliff": "CDCL restarts, phase saving, minimize/shrink",
            "expected_gap": "M3-promote-ema",
            "min_counters": {"conflicts": 100},
            "kissat_confl_mult": 3.0,
            "kissat_confl_add": 1000,
        },
    )

    # van der Waerden W(3,3,3) = 27 UNSAT (81 vars, 615 clauses -> deep long-horizon CDCL)
    nv, cls = gen_vdw_3color_3ap(27)
    record(
        manifest, out_dir, "c08_vdw_3_3_3_27.cnf", fam, nv, cls,
        {
            "desc": f"van der Waerden W(3,3,3)=27 UNSAT ({nv} vars, {len(cls)} clauses)",
            "cliff": "Long-horizon promote.c, restarts/EMA, VSIDS rescale, reduce.c",
            "expected_gap": "M3-promote-ema",
            "min_counters": {"reductions": 5, "restarts": 50, "switched": 2},
            "kissat_confl_mult": 3.0,
            "kissat_confl_add": 2000,
        },
    )


# ---------------------------------------------------------------------------
# Family 9: Large-BIG (500..600v) Backbone & Transitive-Closure Hybrids
# ---------------------------------------------------------------------------
def gen_family_09(out_dir, manifest):
    fam = "09_big_backbone"
    for n_tot in (500, 600):
        rng = random.Random(900000 + n_tot)
        clauses = []
        # Vars 1..99: satisfiable decoy block (occupying v < 64 so probe_run 0..63 misses backbones!)
        dec_model = [False] + [bool(rng.getrandbits(1)) for _ in range(99)]
        for _ in range(180):
            vs = rng.sample(range(1, 100), 3)
            ti = rng.randrange(3)
            cl = [v if (i == ti and dec_model[v]) or (i != ti and rng.getrandbits(1)) else -v
                  for i, v in enumerate(vs)]
            if not any((l > 0 and dec_model[l]) or (l < 0 and not dec_model[-l]) for l in cl):
                cl[0] = vs[0] if dec_model[vs[0]] else -vs[0]
            clauses.append(cl)

        # Vars 100..259: 160-var binary implication DAG with dense transitive shortcuts
        dag_vars = list(range(100, 260))
        dag_lits = [v if rng.getrandbits(1) else -v for v in dag_vars]
        for i in range(len(dag_lits) - 1):
            clauses.append([-dag_lits[i], dag_lits[i + 1]])
        edges = set()
        target_shortcuts = 2400 if n_tot == 500 else 3000
        while len(edges) < target_shortcuts:
            i = rng.randrange(len(dag_lits) - 1)
            j = rng.randrange(i + 1, len(dag_lits))
            if j > i + 1 and (i, j) not in edges:
                edges.add((i, j))
                clauses.append([-dag_lits[i], dag_lits[j]])

        # Vars 260..n_tot: ternary failed-literal backbone diamonds strictly past var 64!
        # [bl, u], [bl, v], [-u, -v, w], [-u, -v, -w]: NO binary path ~bl -> bl (so Tarjan SCC
        # cannot prove bl), yet probing ~bl propagates u & v -> w & ~w -> conflict -> bl = True!
        n_bb = (n_tot - 260) // 4
        bb_lits = []
        nxt = 260
        for _ in range(n_bb):
            b, u, v, w = nxt, nxt + 1, nxt + 2, nxt + 3
            nxt += 4
            sign = 1 if rng.getrandbits(1) else -1
            bl = b * sign
            clauses.extend([[bl, u], [bl, v], [-u, -v, w], [-u, -v, -w]])
            bb_lits.append(bl)

        # Hide an UNSAT 3-cube over dag_lits[0..2] guarded by negated backbone literals
        # (since all bb_lits are forced True, every guard -bl is False -> pure UNSAT 3-cube!)
        c_vars = [dag_vars[0], dag_vars[1], dag_vars[2]]
        for mask in range(8):
            cl = [-v if ((mask >> bit) & 1) else v for bit, v in enumerate(c_vars)]
            guards = [-bb_lits[(mask * 3 + g) % len(bb_lits)] for g in range(3)]
            clauses.append(guards + cl)
        # Also force dag_lits[0] true and dag_lits[-1] false guarded by backbone literals!
        clauses.append([-bb_lits[0], -bb_lits[1], dag_lits[0]])
        clauses.append([-bb_lits[2], -bb_lits[3], -dag_lits[-1]])

        nvars = max(n_tot, nxt - 1)
        record(
            manifest, out_dir, f"c09_big_backbone_{n_tot}.cnf", fam, nvars, clauses,
            {
                "desc": f"{nvars}-var BIG DAG ({target_shortcuts} shortcuts) + {n_bb} backbones at v >= 260",
                "cliff": "backbone.c missing + probe_run fixed 0..63 cursor + transitive budget",
                "expected_gap": "M3-backbone-probe64",
                "min_counters": {"trans": 200},
                "kissat_confl_mult": 2.0,
                "kissat_confl_add": 100,
            },
        )


# ---------------------------------------------------------------------------
# Family 10: Dead-Variable Compaction & Memory-Pressure Stress (5k..10k dead)
# ---------------------------------------------------------------------------
def gen_family_10(out_dir, manifest):
    fam = "10_dead_var_compact"
    for n_dead, core_p in [(5000, 6), (10000, 7)]:
        rng = random.Random(1000000 + n_dead)
        clauses = []
        # 1..n_dead: trivially eliminable scaffolding (95%+ dead after unit/SCC/BVE preproc!)
        # Mix: 40% unit-forced vars + subsumed clauses, 40% binary equiv pairs, 20% unconstrained AND gates
        n_unit = int(n_dead * 0.4)
        n_eq = int(n_dead * 0.4) // 2 * 2
        n_gate = n_dead - n_unit - n_eq

        for v in range(1, n_unit + 1):
            s = 1 if (v % 2 == 0) else -1
            clauses.append([s * v])
            if v > 1:
                clauses.append([s * v, (v - 1), -((v % n_unit) + 1)])

        base_eq = n_unit + 1
        for k in range(0, n_eq, 2):
            a = base_eq + k
            b = base_eq + k + 1
            clauses.append([-a, b])
            clauses.append([a, -b])

        base_g = base_eq + n_eq
        for k in range(n_gate):
            y = base_g + k
            a = base_eq + ((2 * k) % n_eq)
            b = base_eq + ((2 * k + 2) % n_eq)
            clauses.extend([[-y, a], [-y, b], [y, -a, -b]])

        # Place UNSAT core PHP(core_p, core_p-1) at the very end (vars n_dead+1 ..)
        core_nv, core_cls = gen_php(core_p, core_p - 1, v_off=n_dead)
        clauses.extend(core_cls)
        nvars = n_dead + core_nv

        record(
            manifest, out_dir, f"c10_dead_compact_{n_dead // 1000}k.cnf", fam, nvars, clauses,
            {
                "desc": f"{n_dead} dead scaffolding vars (>95% dead) + PHP({core_p},{core_p - 1}) core",
                "cliff": "compact.c missing (dead vars scanned forever) & workspace sizing",
                "expected_gap": "M3-compact",
                "min_counters": {"oom": 0},
                "kissat_confl_mult": 3.0,
                "kissat_confl_add": 500,
            },
        )


def gen_family_11(out_dir, manifest):
    """Family 11: 6 fast (<500ms) C3b/C1 regression canaries (chrono/compact/BVA/cong/viv/wcap)."""
    fam = "11_c11_regressions"
    # 1. c11_chrono_cnt2_2wl: dual gated PHP(6,5) cores + staggered 5-lit decision triggers.
    rng = random.Random(1101)
    nv1 = 96
    sel = 1
    cl1 = []
    _, php_a = gen_php(6, 5, v_off=1)  # vars 2..31
    _, php_b = gen_php(6, 5, v_off=31)  # vars 32..61
    for cl in php_a:
        cl1.append([sel] + cl)
    for cl in php_b:
        cl1.append([-sel] + cl)
    for v in range(62, 94):
        cl1.append([v, v + 1, v + 2, -sel if (v & 1) else sel, -(v - 30)])
        cl1.append([-v, rng.randint(2, 31), rng.randint(32, 61), v + 1])
    record(
        manifest, out_dir, "c11_chrono_cnt2_2wl.cnf", fam, nv1, cl1,
        {"desc": "chrono/2WL staggered decision backtracking", "cliff": "chrono cnt>=2 2WL"},
    )

    # 2. c11_compact_multisat: PHP(5,4) core + 1180 unit/pure/equiv variables that compact down.
    nv2 = 1200
    _, cl2_php = gen_php(5, 4)
    cl2 = list(cl2_php)
    for v in range(21, 421):
        cl2.append([v if (v & 1) else -v])
    for v in range(421, 821, 2):
        cl2.extend([[-v, v + 1], [v, -(v + 1)]])
        cl2.append([v, 1, 2, v - 400 if ((v - 400) & 1) else -(v - 400)])
    for v in range(821, 1199):
        cl2.append([v, v + 1, 421, 21])
    cl2.append([1199, 1200, 21, 421])
    record(
        manifest, out_dir, "c11_compact_multisat.cnf", fam, nv2, cl2,
        {"desc": "compact multi-sat variable shrinkage after units/BVE", "cliff": "compact"},
    )

    # 3. c11_bva_pure_kcnf_5k: ~5100-var factorable biclique + pure k-CNF + PHP(6,5) core.
    nv3 = 5100
    _, cl3_php = gen_php(6, 5)
    cl3 = list(cl3_php)
    for blk in range(31, 5088, 12):
        a_set = [blk, blk + 1, blk + 2, blk + 3]
        b_set = [blk + 4, blk + 5, blk + 6, blk + 7]
        tail = [blk + 8, blk + 9, blk + 10, blk + 11]
        for a in a_set:
            for b in b_set:
                cl3.append([a, b] + tail)
    record(
        manifest, out_dir, "c11_bva_pure_kcnf_5k.cnf", fam, nv3, cl3,
        {"desc": "5k-var pure/BVA biclique k-CNF scaling", "cliff": "bva pure 5k"},
    )

    # 4. c11_sparse_bin_cong_sweep: congruent AND/XOR/ITE miter + sparse binary chain.
    cb = CircuitBuilder(18)
    a_nodes = list(range(1, 19))
    b_nodes = list(range(1, 19))
    for k in range(18):
        pa, qa, ra = a_nodes[k], a_nodes[k + 5], a_nodes[k + 9]
        ga = cb.add_and(pa, qa)
        gx = cb.add_xor(ga, ra)
        a_nodes.append(cb.add_ite(pa, gx, qa))
        pb, qb, rb = b_nodes[k], b_nodes[k + 5], b_nodes[k + 9]
        dor = cb.add_or(-pb, -qb)
        gb = -dor
        gxb = cb.add_ite(gb, -rb, rb)
        b_nodes.append(cb.add_ite(pb, gxb, qb))
    chain = [cb.fresh() for _ in range(48)]
    for i in range(47):
        cb.clauses.append([-chain[i], chain[i + 1]])
    cb.clauses.append([-chain[-1], a_nodes[-1]])
    cb.clauses.append([chain[0]])
    cb.clauses.append([-b_nodes[-1]])
    record(
        manifest, out_dir, "c11_sparse_bin_cong_sweep.cnf", fam, cb.nvars, cb.clauses,
        {"desc": "sparse binary watch + congruence/kitten sweep miter", "cliff": "cong sweep"},
    )

    # 5. c11_viv_prefix_2wl: equisatisfiable vivification-padded PHP(5,4) clauses.
    nv5, cl5_base = gen_php(5, 4)
    cl5 = []
    for cl in cl5_base:
        if len(cl) >= 3:
            pads = [nv5 + 1, nv5 + 2, nv5 + 3, nv5 + 4]
            nv5 += 4
            cl5.append(cl + pads)
            for p in pads:
                cl5.append([-p, cl[0]])
        else:
            cl5.append(cl)
    record(
        manifest, out_dir, "c11_viv_prefix_2wl.cnf", fam, nv5, cl5,
        {"desc": "vivification prefix strengthening + 2WL update", "cliff": "vivify 2wl"},
    )

    # 6. c11_tight_wcap_subst: Tarjan SCC binary equiv rings wrapping PHP(5,4) (820 vars).
    _, cl6 = gen_php(5, 4)
    nxt_v = 21
    ring_len = 40
    for base in range(1, 21):
        ring = [base] + list(range(nxt_v, nxt_v + ring_len))
        nxt_v += ring_len
        n_r = len(ring)
        for i, u in enumerate(ring):
            v = ring[(i + 1) % n_r]
            lu = u if (i % 2 == 0) else -u
            lv = v if (((i + 1) % n_r) % 2 == 0) else -v
            cl6.append([-lu, lv])
        for hop in (2, 7, 15):
            for i in range(0, n_r, 3):
                u = ring[i]
                v = ring[(i + hop) % n_r]
                lu = u if (i % 2 == 0) else -u
                lv = v if (((i + hop) % n_r) % 2 == 0) else -v
                cl6.append([-lu, lv])
    nv6 = nxt_v - 1
    record(
        manifest, out_dir, "c11_tight_wcap_subst.cnf", fam, nv6, cl6,
        {"desc": "Tarjan SCC subst + dense binary watch_stk pressure", "cliff": "wcap subst"},
    )


def main():
    ap = argparse.ArgumentParser(description="Generate 10-family (+ optional c11) UNSAT canaries.")
    ap.add_argument("out_dir", help="Output directory for generated .cnf files + manifest.json")
    ap.add_argument("--summary", action="store_true", help="Print per-family summary table")
    ap.add_argument("--include-c11", action="store_true", help="Also emit 6 c11_* canaries")
    ap.add_argument("--c11-only", action="store_true", help="Emit only the 6 c11_* canaries")
    args = ap.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)
    manifest = []
    if not args.c11_only:
        gen_family_01(args.out_dir, manifest)
        gen_family_02(args.out_dir, manifest)
        gen_family_03(args.out_dir, manifest)
        gen_family_04(args.out_dir, manifest)
        gen_family_05(args.out_dir, manifest)
        gen_family_06(args.out_dir, manifest)
        gen_family_07(args.out_dir, manifest)
        gen_family_08(args.out_dir, manifest)
        gen_family_09(args.out_dir, manifest)
        gen_family_10(args.out_dir, manifest)
    if args.include_c11 or args.c11_only:
        gen_family_11(args.out_dir, manifest)

    manifest_path = os.path.join(args.out_dir, "manifest.json")
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump({"schema_version": 1, "canaries": manifest}, f, indent=2)

    if args.summary:
        fam_counts = {}
        for e in manifest:
            fam_counts[e["family"]] = fam_counts.get(e["family"], 0) + 1
        print(f"Generated {len(manifest)} tricky-UNSAT canaries across {len(fam_counts)} families in {args.out_dir}:")
        for fam, cnt in fam_counts.items():
            sub = [e for e in manifest if e["family"] == fam]
            v_lo = min(e["stats"]["vars"] for e in sub)
            v_hi = max(e["stats"]["vars"] for e in sub)
            c_lo = min(e["stats"]["clauses"] for e in sub)
            c_hi = max(e["stats"]["clauses"] for e in sub)
            print(f"  {fam:<22} n={cnt:2d}  vars=[{v_lo}..{v_hi}]  clauses=[{c_lo}..{c_hi}]")


if __name__ == "__main__":
    main()
