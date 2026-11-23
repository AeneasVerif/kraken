#!/usr/bin/env python3
"""Deterministic 300+ CNF inprocessing & search-heuristic stress suite for Kissat 4.0.4."""

import sys

sys.dont_write_bytecode = True

import argparse
import os
import random


def verify_model(nvars, clauses, model):
    assert len(model) >= nvars + 1
    for cl in clauses:
        ok = False
        for lit in cl:
            v = abs(lit)
            assert 1 <= v <= nvars
            if (lit > 0 and model[v]) or (lit < 0 and not model[v]):
                ok = True
                break
        if not ok:
            raise AssertionError(f"Model failed clause {cl}")


def write_cnf(path, nvars, clauses, comment=None, model=None):
    assert nvars >= 1, f"invalid nvars={nvars} for {path}"
    for cl in clauses:
        assert len(cl) >= 1, f"empty clause in {path}"
        for lit in cl:
            assert lit != 0 and 1 <= abs(lit) <= nvars, f"bad lit {lit} in {path}"
    if model is not None:
        verify_model(nvars, clauses, model)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        if comment:
            f.write(f"c {comment}\n")
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")


def lit_sign(var, val):
    return var if val else -var


def make_sat_clause_from_model(vars_list, model, rng):
    """Build a k-clause over vars_list guaranteed satisfied by model."""
    k = len(vars_list)
    true_idx = rng.randrange(k)
    cl = []
    for idx, v in enumerate(vars_list):
        if idx == true_idx:
            cl.append(lit_sign(v, model[v]))
        else:
            cl.append(v if rng.getrandbits(1) else -v)
    return cl


# ---------------------------------------------------------------------------
# 1. Pigeonhole Principle (PHP) — 24 CNFs (12 UNSAT, 12 SAT)
# ---------------------------------------------------------------------------
def gen_php(pigeons, holes):
    nvars = pigeons * holes
    clauses = []
    for i in range(pigeons):
        clauses.append([i * holes + j + 1 for j in range(holes)])
    for j in range(holes):
        for i1 in range(pigeons):
            for i2 in range(i1 + 1, pigeons):
                clauses.append([-(i1 * holes + j + 1), -(i2 * holes + j + 1)])
    return nvars, clauses


def gen_php_family(out, counts):
    # 6 standard UNSAT + 6 standard SAT
    for p in (3, 4, 5, 6, 7, 8):
        nv, cls = gen_php(p, p - 1)
        write_cnf(os.path.join(out, f"php_unsat_{p}_{p - 1}.cnf"), nv, cls)
        counts["php"] += 1

        nv, cls = gen_php(p, p)
        sol = [False] * (nv + 1)
        for i in range(p):
            sol[i * p + i + 1] = True
        write_cnf(os.path.join(out, f"php_sat_{p}_{p}.cnf"), nv, cls, model=sol)
        counts["php"] += 1

    # 6 permuted/shaken UNSAT PHP
    for p, h in [(4, 3), (5, 4), (6, 5)]:
        for s in (1, 2):
            rng = random.Random(10100 + p * 10 + s)
            nv, cls = gen_php(p, h)
            perm = list(range(1, nv + 1))
            rng.shuffle(perm)
            pcls = []
            for cl in cls:
                ncl = [perm[abs(l) - 1] * (1 if l > 0 else -1) for l in cl]
                rng.shuffle(ncl)
                pcls.append(ncl)
            rng.shuffle(pcls)
            write_cnf(os.path.join(out, f"php_unsat_perm_{p}_{h}_s{s}.cnf"), nv, pcls)
            counts["php"] += 1

    # 6 pinned-domain SAT PHP (diagonal matching x_{i,i}=1 always allowed)
    for p in (4, 5, 6):
        for s in (1, 2):
            rng = random.Random(10200 + p * 10 + s)
            nv, cls = gen_php(p, p)
            sol = [False] * (nv + 1)
            for i in range(p):
                sol[i * p + i + 1] = True
            # Forbid some off-diagonal assignments safely
            for i in range(p):
                for j in range(p):
                    if i != j and rng.random() < 0.35:
                        cls.append([-(i * p + j + 1)])
            write_cnf(os.path.join(out, f"php_sat_pinned_{p}_{p}_s{s}.cnf"), nv, cls, model=sol)
            counts["php"] += 1


# ---------------------------------------------------------------------------
# 2. Tseitin Parity on Graphs — 32 CNFs (16 UNSAT, 16 SAT)
# ---------------------------------------------------------------------------
def gen_tseitin(nverts, edges, charges):
    inc = [[] for _ in range(nverts)]
    for eidx, (u, v) in enumerate(edges):
        var = eidx + 1
        inc[u].append(var)
        inc[v].append(var)
    clauses = []
    for v in range(nverts):
        vs = inc[v]
        d = len(vs)
        target = charges[v] & 1
        for mask in range(1 << d):
            if (mask.bit_count() & 1) != target:
                clauses.append([-var if ((mask >> bit) & 1) else var for bit, var in enumerate(vs)])
    return len(edges), clauses


def solve_tseitin_model(nverts, edges, charges, seed):
    assert sum(charges) % 2 == 0
    rng = random.Random(seed)
    adj = [[] for _ in range(nverts)]
    for eidx, (u, v) in enumerate(edges):
        adj[u].append((v, eidx))
        adj[v].append((u, eidx))
    visited = [False] * nverts
    parent = [None] * nverts
    order = []
    stack = [0]
    visited[0] = True
    while stack:
        u = stack.pop()
        order.append(u)
        for w, eidx in adj[u]:
            if not visited[w]:
                visited[w] = True
                parent[w] = (u, eidx)
                stack.append(w)
    assert all(visited), "graph must be connected"
    tree_eids = {p[1] for p in parent[1:] if p is not None}
    val = [False] * (len(edges) + 1)
    for eidx in range(len(edges)):
        if eidx not in tree_eids:
            val[eidx + 1] = bool(rng.getrandbits(1))
    for u in reversed(order[1:]):
        cur = 0
        for _, eidx in adj[u]:
            if eidx not in tree_eids or (parent[u][1] != eidx):
                if val[eidx + 1]:
                    cur ^= 1
        pe = parent[u][1]
        val[pe + 1] = (cur ^ (charges[u] & 1)) == 1
    return val


def make_circulant_edges(n):
    edges = []
    seen = set()
    for i in range(n):
        for j in ((i + 1) % n, (i + n // 2) % n):
            a, b = (i, j) if i < j else (j, i)
            if a != b and (a, b) not in seen:
                seen.add((a, b))
                edges.append((a, b))
    return edges


def make_grid_edges(rows, cols):
    edges = []
    for r in range(rows):
        for c in range(cols):
            u = r * cols + c
            if r + 1 < rows:
                edges.append((u, (r + 1) * cols + c))
            if c + 1 < cols:
                edges.append((u, r * cols + (c + 1)))
    return edges


def make_prism_edges(n):
    edges = []
    for i in range(n):
        edges.append((i, (i + 1) % n))
        edges.append((n + i, n + (i + 1) % n))
        edges.append((i, n + i))
    return edges


def make_cube3_edges():
    edges = []
    for u in range(8):
        for b in range(3):
            v = u ^ (1 << b)
            if u < v:
                edges.append((u, v))
    return edges


def make_petersen_edges():
    edges = []
    for i in range(5):
        edges.append((i, (i + 1) % 5))
        edges.append((i, 5 + i))
        edges.append((5 + i, 5 + (i + 2) % 5))
    return edges


def gen_tseitin_family(out, counts):
    graphs = []
    for n in (6, 8, 10, 12, 14, 16):
        graphs.append((f"circ{n}", n, make_circulant_edges(n)))
    for r, c in ((2, 4), (3, 3), (3, 4), (3, 5), (4, 4)):
        graphs.append((f"grid{r}x{c}", r * c, make_grid_edges(r, c)))
    graphs.append(("k4", 4, [(i, j) for i in range(4) for j in range(i + 1, 4)]))
    graphs.append(("k33", 6, [(i, 3 + j) for i in range(3) for j in range(3)]))
    graphs.append(("cube3", 8, make_cube3_edges()))
    graphs.append(("prism5", 10, make_prism_edges(5)))
    graphs.append(("petersen", 10, make_petersen_edges()))

    for idx, (name, nv_g, edges) in enumerate(graphs):
        ch_u = [1] + [0] * (nv_g - 1)
        ch_s = [1, 1] + [0] * (nv_g - 2)
        nv, cls_u = gen_tseitin(nv_g, edges, ch_u)
        write_cnf(os.path.join(out, f"tseitin_unsat_{name}.cnf"), nv, cls_u)
        counts["tseitin"] += 1

        nv, cls_s = gen_tseitin(nv_g, edges, ch_s)
        sol = solve_tseitin_model(nv_g, edges, ch_s, 20000 + idx)
        write_cnf(os.path.join(out, f"tseitin_sat_{name}.cnf"), nv, cls_s, model=sol)
        counts["tseitin"] += 1


# ---------------------------------------------------------------------------
# 3. XOR Chains & GF(2) Linear Systems — 36 CNFs (18 UNSAT, 18 SAT)
# ---------------------------------------------------------------------------
def encode_xor_lits(lits, rhs):
    """Emit clauses enforcing XOR(lits) == rhs (lits are signed nonzero ints)."""
    k = len(lits)
    clauses = []
    for mask in range(1 << k):
        # Under assignment x_i = (mask>>i)&1 where lits[i] > 0 means x_i, < 0 means ~x_i:
        # Let val(lits[i]) = ((mask >> i) & 1) directly, so cl forbids val(lits[i]) == ((mask>>i)&1)
        if (mask.bit_count() & 1) != (rhs & 1):
            cl = [-(l) if ((mask >> bit) & 1) else l for bit, l in enumerate(lits)]
            clauses.append(cl)
    return clauses


def lit_val(lit, model):
    v = model[abs(lit)]
    return v if lit > 0 else (not v)


def gen_xor_family(out, counts):
    # 12 UNSAT + 12 SAT dual XOR chains (Tseitin XOR equivalence vs contradiction)
    for n in (6, 8, 10, 12, 16, 20):
        for pol in (0, 1):
            rng = random.Random(30100 + n * 10 + pol)
            clauses = []
            nxt = n + 1
            xs = [i if (pol == 0 or i % 2 == 1) else -i for i in range(1, n + 1)]
            # Chain 1: left-to-right
            cur1 = xs[0]
            for j in range(1, n):
                out1 = nxt
                nxt += 1
                clauses.extend(encode_xor_lits([cur1, xs[j], out1], 0))
                cur1 = out1
            # Chain 2: reversed / shuffled grouping
            order = list(xs)
            rng.shuffle(order)
            cur2 = order[0]
            for j in range(1, n):
                out2 = nxt
                nxt += 1
                clauses.extend(encode_xor_lits([cur2, order[j], out2], 0))
                cur2 = out2
            nvars = nxt - 1

            # UNSAT: cur1 XOR cur2 == 1
            cls_u = clauses + [[-cur1, -cur2], [cur1, cur2]]
            write_cnf(os.path.join(out, f"xor_unsat_chain_n{n}_p{pol}.cnf"), nvars, cls_u)
            counts["xor"] += 1

            # SAT: cur1 == cur2 + planted random 3-SAT constraints on primary vars
            sol = [False] * (nvars + 1)
            for i in range(1, n + 1):
                sol[i] = bool(rng.getrandbits(1))
            cls_s = []
            nxt_s = n + 1
            c1 = xs[0]
            v1 = lit_val(c1, sol)
            for j in range(1, n):
                out1 = nxt_s
                nxt_s += 1
                sol[out1] = v1 ^ lit_val(xs[j], sol)
                cls_s.extend(encode_xor_lits([c1, xs[j], out1], 0))
                c1 = out1
                v1 = sol[out1]
            c2 = order[0]
            v2 = lit_val(c2, sol)
            for j in range(1, n):
                out2 = nxt_s
                nxt_s += 1
                sol[out2] = v2 ^ lit_val(order[j], sol)
                cls_s.extend(encode_xor_lits([c2, order[j], out2], 0))
                c2 = out2
                v2 = sol[out2]
            cls_s.extend([[-c1, c2], [c1, -c2]])
            for _ in range(n):
                vs = rng.sample(range(1, n + 1), 3)
                cls_s.append(make_sat_clause_from_model(vs, sol, rng))
            write_cnf(
                os.path.join(out, f"xor_sat_chain_n{n}_p{pol}.cnf"),
                nvars,
                cls_s,
                model=sol,
            )
            counts["xor"] += 1

    # 6 UNSAT + 6 SAT sparse 3-XOR linear systems
    for n in (8, 10, 12, 14, 16, 18):
        rng = random.Random(30200 + n)
        sol = [False] + [bool(rng.getrandbits(1)) for _ in range(n)]
        # Build UNSAT parity cycle over triples sharing pairs of variables:
        # Take m = n//2 disjoint pairs P_0..P_{m-1} and singletons or cycle of 4 equations cancelling all vars:
        # Specifically: pick 4 subsets A,B,C,D of size >=1 and build 4 XOR rows whose XOR sum is 0:
        # e.g. (x1^x2^x3), (x1^x2^x4), (x3^x5^x6), (x4^x5^x6) -> sum is 0 mod 2!
        u_cls = []
        # Create two 3-var XOR chains summing to 0 on x1..x6 with flipped last rhs
        p1, p2, p3, p4, p5, p6 = rng.sample(range(1, n + 1), 6)
        rows = [
            ([p1, p2, p3], 0),
            ([p1, p2, p4], 0),
            ([p3, p5, p6], 0),
            ([p4, p5, p6], 1),
        ]
        # Add extra consistent 3-XOR noise rows over all n vars
        for _ in range(n):
            vs = rng.sample(range(1, n + 1), 3)
            rhs = int(sol[vs[0]]) ^ int(sol[vs[1]]) ^ int(sol[vs[2]])
            u_cls.extend(encode_xor_lits(vs, rhs))
        for vs, rhs in rows:
            u_cls.extend(encode_xor_lits(vs, rhs))
        write_cnf(os.path.join(out, f"xor_unsat_sys_n{n}.cnf"), n, u_cls)
        counts["xor"] += 1

        s_cls = []
        for _ in range(n + 2):
            vs = rng.sample(range(1, n + 1), 3)
            rhs = int(sol[vs[0]]) ^ int(sol[vs[1]]) ^ int(sol[vs[2]])
            s_cls.extend(encode_xor_lits(vs, rhs))
        for _ in range(n):
            vs = rng.sample(range(1, n + 1), 3)
            s_cls.append(make_sat_clause_from_model(vs, sol, rng))
        write_cnf(os.path.join(out, f"xor_sat_sys_n{n}.cnf"), n, s_cls, model=sol)
        counts["xor"] += 1


# ---------------------------------------------------------------------------
# 4. AND / ITE / XOR Circuit Miters — 40 CNFs (20 UNSAT, 20 SAT)
#    (Gate congruence + SAT sweeping + Gate-BVE)
# ---------------------------------------------------------------------------
class CircuitBuilder:
    def __init__(self, n_inputs):
        self.nvars = n_inputs
        self.clauses = []
        self.gates = []  # (kind, out, args, value_fn)

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


def gen_miter_family(out, counts):
    # 4a. Random AND/OR/XOR/ITE DAG congruence + DeMorgan/commuted miters (8 UNSAT, 8 SAT)
    for idx in range(8):
        rng = random.Random(40100 + idx)
        n_in = 4 + (idx % 4)
        n_gates = 10 + idx * 2
        cb = CircuitBuilder(n_in)
        wires1 = list(range(1, n_in + 1))
        wires2 = list(range(1, n_in + 1))
        # Build C1 and isomorphic C2 with commuted/DeMorgan/ITE-swapped gates
        bug_at = n_gates // 2
        for g in range(n_gates):
            op = rng.choice(("AND", "OR", "XOR", "ITE"))
            if op == "AND":
                i1, i2 = rng.sample(range(len(wires1)), 2)
                s1 = -1 if rng.getrandbits(1) else 1
                s2 = -1 if rng.getrandbits(1) else 1
                a1, b1 = s1 * wires1[i1], s2 * wires1[i2]
                a2, b2 = s1 * wires2[i1], s2 * wires2[i2]
                y1 = cb.add_and(a1, b1)
                # Commute + DeMorgan half the time
                if g % 2 == 0:
                    y2 = cb.add_and(b2, a2)
                else:
                    y2 = -cb.add_or(-a2, -b2)
            elif op == "OR":
                i1, i2 = rng.sample(range(len(wires1)), 2)
                a1, b1 = wires1[i1], wires1[i2]
                a2, b2 = wires2[i1], wires2[i2]
                y1 = cb.add_or(a1, b1)
                y2 = -cb.add_and(-b2, -a2)
            elif op == "XOR":
                i1, i2 = rng.sample(range(len(wires1)), 2)
                s1 = -1 if rng.getrandbits(1) else 1
                a1, b1 = s1 * wires1[i1], wires1[i2]
                a2, b2 = s1 * wires2[i1], wires2[i2]
                y1 = cb.add_xor(a1, b1)
                y2 = cb.add_xor(b2, a2) if g % 2 == 0 else -cb.add_xor(-a2, b2)
            else:
                i1, i2, i3 = rng.sample(range(len(wires1)), 3)
                c1, t1, e1 = wires1[i1], wires1[i2], wires1[i3]
                c2, t2, e2 = wires2[i1], wires2[i2], wires2[i3]
                y1 = cb.add_ite(c1, t1, e1, consensus=(g % 3 == 0))
                y2 = cb.add_ite(-c2, e2, t2, consensus=(g % 3 == 1))
            wires1.append(y1)
            wires2.append(y2)

        o1, o2 = wires1[-1], wires2[-1]
        # UNSAT miter: o1 != o2
        cls_u = cb.clauses + [[o1, o2], [-o1, -o2]]
        write_cnf(os.path.join(out, f"miter_unsat_dag_{idx}.cnf"), cb.nvars, cls_u)
        counts["miter"] += 1

        # SAT miter: inject bug or constrain o1 == o2 with reachable input
        inp = [bool(rng.getrandbits(1)) for _ in range(n_in)]
        env = cb.eval_all(inp)
        # Also test bug-injected miter on half of them when distinguishable input exists
        cls_s = list(cb.clauses) + [[-o1, o2], [o1, -o2]]
        # Constrain output to match env[abs(o1)] and fix half the inputs to make non-trivial
        cls_s.append([o1 if cb.eval_lit(o1, env) else -o1])
        for k in range(1, n_in, 2):
            cls_s.append([k if env[k] else -k])
        write_cnf(os.path.join(out, f"miter_sat_dag_{idx}.cnf"), cb.nvars, cls_s, model=env)
        counts["miter"] += 1

    # 4b. Ripple-carry adder commutativity miters (4 UNSAT, 4 SAT)
    for w in (3, 4, 5, 6):
        cb = CircuitBuilder(2 * w)
        a = list(range(1, w + 1))
        b = list(range(w + 1, 2 * w + 1))

        def build_adder(xs, ys, flip_or=False):
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
        miter_out = diffs[0]
        for d in diffs[1:]:
            miter_out = cb.add_or(miter_out, d)
        cls_u = cb.clauses + [[miter_out]]
        write_cnf(os.path.join(out, f"miter_unsat_add{w}.cnf"), cb.nvars, cls_u)
        counts["miter"] += 1

        # SAT: find A+B == target sum for fixed target bits from a concrete sample
        rng = random.Random(40200 + w)
        inp = [bool(rng.getrandbits(1)) for _ in range(2 * w)]
        env = cb.eval_all(inp)
        cls_s = list(cb.clauses)
        for bit_out in s1:
            cls_s.append([bit_out if cb.eval_lit(bit_out, env) else -bit_out])
        write_cnf(os.path.join(out, f"miter_sat_add{w}.cnf"), cb.nvars, cls_s, model=env)
        counts["miter"] += 1

    # 4c. ITE Shannon-tree commutation & Gate-BVE cones (4 UNSAT, 4 SAT)
    for idx in range(4):
        rng = random.Random(40300 + idx)
        n_in = 6 + idx
        cb = CircuitBuilder(n_in)
        # Build nested Shannon ITE trees: ITE(s, ITE(t, a, b), ITE(t, c, d)) vs ITE(t, ITE(s, a, c), ITE(s, b, d))
        s, t = 1, 2
        leaves = [3 + (k % (n_in - 2)) for k in range(4)]
        # Make leaves nontrivial functions of inputs
        lits = []
        for k, lv in enumerate(leaves):
            other = 3 + ((k + 1) % (n_in - 2))
            lits.append(cb.add_and(lv, other) if k % 2 == 0 else cb.add_xor(lv, other))
        a, b, c, d = lits
        lhs = cb.add_ite(s, cb.add_ite(t, a, b, True), cb.add_ite(t, c, d, True), True)
        rhs = cb.add_ite(t, cb.add_ite(s, a, c, False), cb.add_ite(s, b, d, False), False)
        for extra in range(idx + 2):
            v = 1 + (extra % n_in)
            lhs = cb.add_xor(lhs, v)
            rhs = cb.add_xor(v, rhs)
        cls_u = cb.clauses + [[lhs, rhs], [-lhs, -rhs]]
        write_cnf(os.path.join(out, f"miter_unsat_ite_{idx}.cnf"), cb.nvars, cls_u)
        counts["miter"] += 1

        inp = [bool(rng.getrandbits(1)) for _ in range(n_in)]
        env = cb.eval_all(inp)
        cls_s = list(cb.clauses) + [[-lhs, rhs], [lhs, -rhs], [lhs if cb.eval_lit(lhs, env) else -lhs]]
        write_cnf(os.path.join(out, f"miter_sat_ite_{idx}.cnf"), cb.nvars, cls_s, model=env)
        counts["miter"] += 1

    # 4d. Non-structural SAT-sweeping algebraic identities (4 UNSAT, 4 SAT)
    for idx in range(4):
        rng = random.Random(40400 + idx)
        n_in = 5 + idx
        cb = CircuitBuilder(n_in)
        w1 = 1
        w2 = 1
        for k in range(n_in - 1):
            b = k + 2
            c = ((k + 1) % (n_in - 1)) + 2
            # Identity 1: AND(a, ITE(a, b, c)) == AND(a, b)
            t1 = cb.add_and(w1, cb.add_ite(w1, b, c))
            t2 = cb.add_and(w2, b)
            # Identity 2: XOR(a, XOR(a, c)) == c (masked with t1/t2)
            x1 = cb.add_xor(c, cb.add_xor(c, t1))
            x2 = t2
            # Identity 3: AND(x1, OR(-x1, b)) == AND(x1, b)
            w1 = cb.add_and(x1, cb.add_or(-x1, b))
            w2 = cb.add_and(x2, b)
        cls_u = cb.clauses + [[w1, w2], [-w1, -w2]]
        write_cnf(os.path.join(out, f"miter_unsat_sweep_{idx}.cnf"), cb.nvars, cls_u)
        counts["miter"] += 1

        # SAT: break identity cleanly by XORing w2 with an input and check satisfiability
        inp = [bool(rng.getrandbits(1)) for _ in range(n_in)]
        # Pick an input with inp[n_in-1] == True so w1 != (w2 ^ inp_last)
        inp[-1] = True
        w2_bug = cb.add_xor(w2, n_in)
        env = cb.eval_all(inp)
        cls_s = list(cb.clauses) + [[w1, w2_bug], [-w1, -w2_bug]]
        write_cnf(os.path.join(out, f"miter_sat_sweep_{idx}.cnf"), cb.nvars, cls_s, model=env)
        counts["miter"] += 1


# ---------------------------------------------------------------------------
# 5. Redundant Binary Implication DAGs & SCC Cycles — 36 CNFs (18 UNSAT, 18 SAT)
#    (transitive.c + substitute.c)
# ---------------------------------------------------------------------------
def gen_big_family(out, counts):
    # 5a. Transitive reduction DAGs (6 UNSAT, 6 SAT)
    for n in (12, 16, 20, 25, 30, 40):
        rng = random.Random(50100 + n)
        # Signed literals over 1..n in fixed topological order
        signs = [1 if rng.getrandbits(1) else -1 for _ in range(n)]
        seq = [(i + 1) * signs[i] for i in range(n)]
        clauses = []
        # Backbone chain: seq[i] -> seq[i+1]
        for i in range(n - 1):
            clauses.append([-seq[i], seq[i + 1]])
        # Dense transitive shortcuts: seq[i] -> seq[j] for i < j
        edges = set()
        while len(edges) < 4 * n:
            i = rng.randrange(n - 1)
            j = rng.randrange(i + 1, n)
            if (i, j) not in edges:
                edges.add((i, j))
                clauses.append([-seq[i], seq[j]])
        # UNSAT: force seq[0] true and seq[-1] false
        cls_u = clauses + [[seq[0]], [-seq[-1]]]
        write_cnf(os.path.join(out, f"big_unsat_trans_n{n}.cnf"), n, cls_u)
        counts["big"] += 1

        # SAT: pick a split k; seq[0..k-1] = False, seq[k..n-1] = True satisfies all seq[i]->seq[j].
        k = n // 3
        sol = [False] * (n + 1)
        for idx, l in enumerate(seq):
            want = idx >= k
            sol[abs(l)] = want if l > 0 else (not want)
        cls_s = list(clauses)
        for _ in range(2 * n):
            vs = rng.sample(range(1, n + 1), 3)
            cls_s.append(make_sat_clause_from_model(vs, sol, rng))
        write_cnf(os.path.join(out, f"big_sat_trans_n{n}.cnf"), n, cls_s, model=sol)
        counts["big"] += 1

    # 5b. Contradictory SCC cycles x -> ... -> -x -> ... -> x (6 UNSAT)
    for k in (3, 4, 5, 6, 8, 10):
        rng = random.Random(50200 + k)
        n = k * 3 + 4
        # Cycle including +1 and -1 plus extra decoy SCCs
        mid_pos = [rng.choice([1, -1]) * v for v in range(2, k + 2)]
        mid_neg = [rng.choice([1, -1]) * v for v in range(k + 2, 2 * k + 2)]
        cyc = [1] + mid_pos + [-1] + mid_neg
        clauses = []
        for i in range(len(cyc)):
            a = cyc[i]
            b = cyc[(i + 1) % len(cyc)]
            clauses.append([-a, b])
        # Decoy SCC on remaining vars + random 3-clauses
        rem = list(range(2 * k + 2, n + 1))
        for i in range(len(rem)):
            clauses.append([-rem[i], rem[(i + 1) % len(rem)]])
        for _ in range(2 * n):
            vs = rng.sample(range(1, n + 1), 3)
            clauses.append([v if rng.getrandbits(1) else -v for v in vs])
        write_cnf(os.path.join(out, f"big_unsat_scc_contra_k{k}.cnf"), n, clauses)
        counts["big"] += 1

    # 5c. Valid SCC cycles + UNSAT kernel across mixed representatives (6 UNSAT)
    #     & Valid SCC cycles + satisfiable 3-SAT core (12 SAT)
    for idx, k in enumerate((4, 5, 6, 8, 10, 12)):
        rng = random.Random(50300 + k)
        m = 4  # members per SCC
        n = k * m
        sccs = []
        clauses = []
        for c in range(k):
            cyc = [(c * m + j + 1) * (1 if rng.getrandbits(1) else -1) for j in range(m)]
            sccs.append(cyc)
            for j in range(m):
                clauses.append([-cyc[j], cyc[(j + 1) % m]])
            # Shortcut inside SCC
            clauses.append([-cyc[0], cyc[2]])

        # UNSAT: hide all-8 3-var UNSAT cube across SCCs 0, 1, 2 (choosing random member per clause!)
        cls_u = list(clauses)
        for mask in range(8):
            cl = []
            for bit in range(3):
                lit = rng.choice(sccs[bit])
                cl.append(-lit if ((mask >> bit) & 1) else lit)
            cls_u.append(cl)
        # Plus hide 2-SAT cycle over SCCs 3.. if k>=4
        for _ in range(2 * n):
            vs = rng.sample(range(1, n + 1), 3)
            cls_u.append([v if rng.getrandbits(1) else -v for v in vs])
        write_cnf(os.path.join(out, f"big_unsat_scc_core_k{k}.cnf"), n, cls_u)
        counts["big"] += 1

        # SAT: 2 seeds each -> 12 SAT
        for s in (1, 2):
            rng_s = random.Random(50400 + k * 10 + s)
            sol = [False] * (n + 1)
            for cyc in sccs:
                val = bool(rng_s.getrandbits(1))
                for lit in cyc:
                    sol[abs(lit)] = val if lit > 0 else (not val)
            cls_s = list(clauses)
            for _ in range(3 * n):
                vs = rng_s.sample(range(1, n + 1), 3)
                cls_s.append(make_sat_clause_from_model(vs, sol, rng_s))
            write_cnf(os.path.join(out, f"big_sat_scc_k{k}_s{s}.cnf"), n, cls_s, model=sol)
            counts["big"] += 1


# ---------------------------------------------------------------------------
# 6. Subsumption / SSR / Vivification Formulas — 36 CNFs (18 UNSAT, 18 SAT)
#    (forward.c + strengthen.c + vivify.c)
# ---------------------------------------------------------------------------
def gen_subsume_viv_family(out, counts):
    # 6a. Subsumption + Cascading SSR (9 UNSAT, 9 SAT)
    for idx in range(9):
        rng = random.Random(60100 + idx)
        n_core = 4 + (idx % 3)
        n_aux = 6 + idx
        nvars = n_core + n_aux

        # UNSAT: PHP(3,2) or all-3-cube split via SSR + bloated subsumed clauses
        if idx % 2 == 0:
            # All 2^3 cubes on vars 1..3
            core = [
                [-v if ((m >> b) & 1) else v for b, v in enumerate((1, 2, 3))]
                for m in range(8)
            ]
        else:
            _, core = gen_php(3, 2)
            nvars = max(nvars, 6 + n_aux)
        cls_u = []
        aux_vars = list(range(n_core + 1, nvars + 1))
        for cl in core:
            # Split cl into SSR pair [p] + cl and [-p] + cl (exact equisatisfiable!)
            p = rng.choice(aux_vars)
            cls_u.append([p] + cl)
            cls_u.append([-p] + cl)
            # Also add subsumed supersets
            for _ in range(3):
                extras = rng.sample(aux_vars, min(3, len(aux_vars)))
                ext_lits = [u if rng.getrandbits(1) else -u for u in extras if u != p]
                cls_u.append(cl + ext_lits)
        rng.shuffle(cls_u)
        write_cnf(os.path.join(out, f"subsume_unsat_ssr_{idx}.cnf"), nvars, cls_u)
        counts["subsume_viv"] += 1

        # SAT: planted 3-SAT base + subsumed supersets + SSR pairs
        sol = [False] + [bool(rng.getrandbits(1)) for _ in range(nvars)]
        base = [make_sat_clause_from_model(rng.sample(range(1, n_core + 4), 3), sol, rng)
                for _ in range(12 + idx * 2)]
        cls_s = list(base)
        for cl in base:
            p = rng.choice(aux_vars)
            cls_s.append([p] + cl)
            cls_s.append([-p] + cl)
            extras = [u if rng.getrandbits(1) else -u for u in rng.sample(aux_vars, 3)]
            cls_s.append(cl + extras)
        rng.shuffle(cls_s)
        write_cnf(os.path.join(out, f"subsume_sat_ssr_{idx}.cnf"), nvars, cls_s, model=sol)
        counts["subsume_viv"] += 1

    # 6b. Vivification Stress (9 UNSAT, 9 SAT)
    for idx in range(9):
        rng = random.Random(60200 + idx)
        n_chain = 6 + idx
        nvars = n_chain + 8
        # Implication chain: 1 -> 2 -> ... -> n_chain
        impls = [[-(i), i + 1] for i in range(1, n_chain)]
        # Add cross binary implications
        for i in range(1, n_chain - 1):
            impls.append([-i, i + 2])

        # UNSAT: bloated clauses that vivify down to contradicting units [1] and [-n_chain]
        cls_u = list(impls)
        # Bloated [1, extra...] where binary hints force extra false when -1 assumed:
        # Take aux vars A = n_chain+1 .. nvars; if -1 -> a1 -> a2, then [1, -a1, -a2] vivifies!
        aux = list(range(n_chain + 1, nvars + 1))
        for j in range(len(aux) - 1):
            cls_u.append([1, aux[j]])
            cls_u.append([-aux[j], aux[j + 1]])
            cls_u.append([-n_chain, aux[j]])
        for _ in range(6):
            sub = rng.sample(aux, 4)
            cls_u.append([1] + [-u for u in sub])
            cls_u.append([-n_chain] + [-u for u in sub])
        # Force [1] via [1, aux[0]] and [1, -aux[0]] and [-n_chain, aux[0]], [-n_chain, -aux[0]]
        cls_u.extend([[1, aux[0]], [1, -aux[0]], [-n_chain, aux[0]], [-n_chain, -aux[0]]])
        write_cnf(os.path.join(out, f"viv_unsat_{idx}.cnf"), nvars, cls_u)
        counts["subsume_viv"] += 1

        # SAT: implication chain true (set all vars >= mid True, rest False) + bloated vivifiable clauses
        sol = [False] * (nvars + 1)
        mid = n_chain // 2
        for v in range(mid, n_chain + 1):
            sol[v] = True
        for v in aux:
            sol[v] = bool(rng.getrandbits(1))
        cls_s = list(impls)
        # Add binary implications consistent with sol
        for _ in range(6):
            u, v = rng.sample(aux, 2)
            lu = lit_sign(u, not sol[u])
            lv = lit_sign(v, sol[v])
            cls_s.append([lu, lv])
        # Bloated clauses sharing implication prefixes satisfied by sol
        for _ in range(16 + idx * 2):
            c_vars = rng.sample(range(1, nvars + 1), 6)
            cls_s.append(make_sat_clause_from_model(c_vars, sol, rng))
        write_cnf(os.path.join(out, f"viv_sat_{idx}.cnf"), nvars, cls_s, model=sol)
        counts["subsume_viv"] += 1


# ---------------------------------------------------------------------------
# 7. Factorable BVA Matrices — 36 CNFs (18 UNSAT, 18 SAT)
#    (factor.c Bounded Variable Addition + extend stack model reconstruction)
# ---------------------------------------------------------------------------
def gen_bva_family(out, counts):
    configs = [
        (3, 3, 1), (4, 4, 1), (5, 5, 1), (4, 6, 1), (6, 6, 1), (5, 7, 1),
        (3, 4, 2), (4, 4, 2), (4, 5, 2), (5, 5, 2), (5, 6, 2), (6, 6, 2),
        (3, 3, 3), (4, 4, 3), (4, 5, 3), (5, 5, 3), (3, 6, 2), (6, 7, 1),
    ]
    for idx, (m, n, kblocks) in enumerate(configs):
        rng = random.Random(70100 + idx)
        # Allocate disjoint sets A_0..A_{k-1} (size m) and B (size n)
        # Plus optional shared ternary context lit (disabled for half, forced via 2-clause for half)
        nxt = 1
        blocks = []
        for _ in range(kblocks):
            a_set = [nxt + i for i in range(m)]
            nxt += m
            blocks.append(a_set)
        b_set = [nxt + j for j in range(n)]
        nxt += n
        use_ctx = (idx % 3 == 2)
        ctx_v = nxt if use_ctx else None
        if use_ctx:
            nxt += 1
        nvars = nxt - 1

        # UNSAT chained BVA matrix:
        # A_0 x (~A_1), A_1 x (~A_2), ..., A_{k-1} x B, plus [~a_{0,*}] and [~b_*]
        cls_u = []
        ctx_tail = [-ctx_v] if use_ctx else []
        if use_ctx:
            # Force ctx_v = True via 2 binary clauses over fresh var? Use existing vars: [-ctx_v] would allow ctx=F;
            # To keep pure non-unit: [ctx_v, b_set[0]]? Actually [ctx_v, aux] & [ctx_v, -aux] forces ctx_v=T!
            nvars += 1
            aux_c = nvars
            cls_u.extend([[ctx_v, aux_c], [ctx_v, -aux_c]])
        for r in range(kblocks):
            left = blocks[r]
            right = [-v for v in blocks[r + 1]] if r + 1 < kblocks else b_set
            for la in left:
                for rb in right:
                    cls_u.append([la, rb] + ctx_tail)
        cls_u.append([-v for v in blocks[0]])
        cls_u.append([-v for v in b_set])
        write_cnf(os.path.join(out, f"bva_unsat_b{kblocks}_{m}x{n}_{idx}.cnf"), nvars, cls_u)
        counts["bva"] += 1

        # SAT BVA matrices: kblocks independent (A_r x B_r) blocks with planted signs
        nxt_s = 1
        cls_s = []
        sol = [False]
        s_blocks = []
        for r in range(kblocks):
            la = []
            for _ in range(m):
                sgn = 1 if rng.getrandbits(1) else -1
                la.append(sgn * nxt_s)
                sol.append(bool(rng.getrandbits(1)))
                nxt_s += 1
            lb = []
            for _ in range(n):
                sgn = 1 if rng.getrandbits(1) else -1
                lb.append(sgn * nxt_s)
                sol.append(bool(rng.getrandbits(1)))
                nxt_s += 1
            # Force either all literals in la true under sol, or all literals in lb true under sol
            if r % 2 == 0:
                for lit in la:
                    sol[abs(lit)] = (lit > 0)
            else:
                for lit in lb:
                    sol[abs(lit)] = (lit > 0)
            s_blocks.append((la, lb))
        nv_s = nxt_s - 1
        for la, lb in s_blocks:
            for a in la:
                for b in lb:
                    cls_s.append([a, b])
        # Add extra 3-SAT constraints satisfied by sol across all blocks so it's non-trivial
        for _ in range(2 * nv_s):
            vs = rng.sample(range(1, nv_s + 1), min(3, nv_s))
            cls_s.append(make_sat_clause_from_model(vs, sol, rng))
        write_cnf(
            os.path.join(out, f"bva_sat_b{kblocks}_{m}x{n}_{idx}.cnf"),
            nv_s,
            cls_s,
            model=sol,
        )
        counts["bva"] += 1


# ---------------------------------------------------------------------------
# 8. Chronological-Backtrack & WalkSAT / VMTF Stress — 36 CNFs (18 UNSAT, 18 SAT)
# ---------------------------------------------------------------------------
def gen_graph_kcol(nverts, edges, k):
    # var(v, c) = v * k + c + 1
    nvars = nverts * k
    clauses = []
    for v in range(nverts):
        clauses.append([v * k + c + 1 for c in range(k)])
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                clauses.append([-(v * k + c1 + 1), -(v * k + c2 + 1)])
    for u, v in edges:
        for c in range(k):
            clauses.append([-(u * k + c + 1), -(v * k + c + 1)])
    return nvars, clauses


def gen_nqueens(n):
    nvars = n * n
    clauses = []
    def var(r, c):
        return r * n + c + 1
    for r in range(n):
        clauses.append([var(r, c) for c in range(n)])
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-var(r, c1), -var(r, c2)])
    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append([-var(r1, c), -var(r2, c)])
    for r1 in range(n):
        for c1 in range(n):
            for r2 in range(r1 + 1, n):
                d = r2 - r1
                if c1 + d < n:
                    clauses.append([-var(r1, c1), -var(r2, c1 + d)])
                if c1 - d >= 0:
                    clauses.append([-var(r1, c1), -var(r2, c1 - d)])
    return nvars, clauses


def solve_nqueens_backtrack(n):
    cols = set()
    d1 = set()
    d2 = set()
    pos = [-1] * n
    def dfs(r):
        if r == n:
            return True
        for c in range(n):
            if c not in cols and (r - c) not in d1 and (r + c) not in d2:
                cols.add(c); d1.add(r - c); d2.add(r + c); pos[r] = c
                if dfs(r + 1):
                    return True
                cols.remove(c); d1.remove(r - c); d2.remove(r + c)
        return False
    assert dfs(0)
    sol = [False] * (n * n + 1)
    for r, c in enumerate(pos):
        sol[r * n + c + 1] = True
    return sol


def moser_spindle_edges():
    # 7 vertices, 11 edges, chromatic number 4
    return [
        (0, 1), (0, 2), (1, 2), (1, 3), (2, 3),
        (0, 4), (0, 5), (4, 5), (4, 6), (5, 6),
        (3, 6),
    ]


def mycielski_m4_edges():
    # 11 vertices, 20 edges, triangle-free, chromatic number 4
    edges = [(i, (i + 1) % 5) for i in range(5)]  # C5: 0..4
    for i in range(5):
        u_shadow = 5 + i
        edges.append((u_shadow, (i + 1) % 5))
        edges.append((u_shadow, (i + 4) % 5))
        edges.append((10, u_shadow))
    return edges


def gen_search_stress_family(out, counts):
    # 8a. Interleaved multi-component chronological-backtrack stress (6 UNSAT, 6 SAT)
    for idx in range(6):
        rng = random.Random(80100 + idx)
        # Component A (UNSAT PHP(4,3) or ordering(4)) interleaved with Component B (SAT 3-SAT + chain)
        if idx % 2 == 0:
            nv_a, cls_a = gen_php(4, 3)
        else:
            nv_a, cls_a = gen_graph_kcol(4, [(i, j) for i in range(4) for j in range(i + 1, 4)], 3)
        nv_b = 18 + idx * 4
        nvars = nv_a + nv_b
        # Interleave variables of A and B deterministically
        perm = list(range(1, nvars + 1))
        rng.shuffle(perm)
        map_a = perm[:nv_a]
        map_b = perm[nv_a:]
        clauses_a = [[(1 if l > 0 else -1) * map_a[abs(l) - 1] for l in cl] for cl in cls_a]
        # Build deep implication chain + 3-SAT in B
        sol_b = [bool(rng.getrandbits(1)) for _ in range(nv_b)]
        clauses_b = []
        for i in range(nv_b - 1):
            la = map_b[i] if not sol_b[i] else -map_b[i]
            lb = map_b[i + 1] if sol_b[i + 1] else -map_b[i + 1]
            clauses_b.append([la, lb])
        for _ in range(int(3.8 * nv_b)):
            idxs = rng.sample(range(nv_b), 3)
            ti = rng.randrange(3)
            cl = []
            for j, bi in enumerate(idxs):
                if j == ti:
                    cl.append(map_b[bi] if sol_b[bi] else -map_b[bi])
                else:
                    cl.append(map_b[bi] if rng.getrandbits(1) else -map_b[bi])
            clauses_b.append(cl)
        cls_u = clauses_a + clauses_b
        rng.shuffle(cls_u)
        write_cnf(os.path.join(out, f"search_unsat_chrono_{idx}.cnf"), nvars, cls_u)
        counts["search_stress"] += 1

        # SAT chrono: replace UNSAT Comp A with SAT Comp A (e.g. PHP(4,4) or bipartite 2-col)
        nv_a_s, cls_a_s = gen_php(4, 4)
        nvars_s = nv_a_s + nv_b
        perm_s = list(range(1, nvars_s + 1))
        rng.shuffle(perm_s)
        ma = perm_s[:nv_a_s]
        mb = perm_s[nv_a_s:]
        sol_s = [False] * (nvars_s + 1)
        for i in range(4):
            sol_s[ma[i * 4 + i]] = True
        for bi in range(nv_b):
            sol_s[mb[bi]] = sol_b[bi]
        clauses_as = [[(1 if l > 0 else -1) * ma[abs(l) - 1] for l in cl] for cl in cls_a_s]
        clauses_bs = []
        for i in range(nv_b - 1):
            la = mb[i] if not sol_b[i] else -mb[i]
            lb = mb[i + 1] if sol_b[i + 1] else -mb[i + 1]
            clauses_bs.append([la, lb])
        # Add bridge clauses satisfied by sol_s to couple A and B
        for _ in range(int(4.0 * nv_b)):
            vs = rng.sample(range(1, nvars_s + 1), 3)
            clauses_bs.append(make_sat_clause_from_model(vs, sol_s, rng))
        cls_s = clauses_as + clauses_bs
        rng.shuffle(cls_s)
        write_cnf(os.path.join(out, f"search_sat_chrono_{idx}.cnf"), nvars_s, cls_s, model=sol_s)
        counts["search_stress"] += 1

    # 8b. Graph k-coloring UNSAT (12 UNSAT)
    col_unsat = [
        ("k4_3col", 4, [(i, j) for i in range(4) for j in range(i + 1, 4)], 3),
        ("k5_3col", 5, [(i, j) for i in range(5) for j in range(i + 1, 5)], 3),
        ("k5_4col", 5, [(i, j) for i in range(5) for j in range(i + 1, 5)], 4),
        ("k6_4col", 6, [(i, j) for i in range(6) for j in range(i + 1, 6)], 4),
        ("moser_3col", 7, moser_spindle_edges(), 3),
        ("mycielski_m4_3col", 11, mycielski_m4_edges(), 3),
        ("wheel5_3col", 6, [(5, i) for i in range(5)] + [(i, (i + 1) % 5) for i in range(5)], 3),
        ("wheel7_3col", 8, [(7, i) for i in range(7)] + [(i, (i + 1) % 7) for i in range(7)], 3),
        ("k4_pad1", 4, [(i, j) for i in range(4) for j in range(i + 1, 4)], 3),
        ("moser_pad", 7, moser_spindle_edges(), 3),
        ("mycielski_pad", 11, mycielski_m4_edges(), 3),
        ("k5_4col_pad", 5, [(i, j) for i in range(5) for j in range(i + 1, 5)], 4),
    ]
    for idx, (nm, nv_g, edges, k) in enumerate(col_unsat):
        nv, cls = gen_graph_kcol(nv_g, edges, k)
        if nm.endswith("pad") or nm.endswith("pad1"):
            rng = random.Random(80200 + idx)
            # Add noisy decoy 3-SAT clauses on extra vars to exercise VMTF/WalkSAT/reduce
            extra = 12
            nv_tot = nv + extra
            for _ in range(extra * 3):
                vs = rng.sample(range(nv + 1, nv_tot + 1), 3)
                cls.append([v if rng.getrandbits(1) else -v for v in vs])
            nv = nv_tot
        write_cnf(os.path.join(out, f"search_unsat_{nm}.cnf"), nv, cls)
        counts["search_stress"] += 1

    # 8c. N-Queens SAT + Planted WalkSAT / Rephase Deceptive 3-SAT (12 SAT)
    for n in (4, 5, 6, 7, 8, 9):
        nv, cls = gen_nqueens(n)
        sol = solve_nqueens_backtrack(n)
        write_cnf(os.path.join(out, f"search_sat_nqueens_{n}.cnf"), nv, cls, model=sol)
        counts["search_stress"] += 1

    for idx in range(6):
        rng = random.Random(80300 + idx)
        n = 30 + idx * 10
        # Planted deceptive 3-SAT: bias negative literals in non-planted positions so naive all-false fails
        sol = [False] + [bool(rng.getrandbits(1)) for _ in range(n)]
        m = int(4.2 * n)
        cls = []
        for _ in range(m):
            vs = rng.sample(range(1, n + 1), 3)
            # At least 1 literal matches sol; bias other 2 to opposite of sol -> hard local minima!
            ti = rng.randrange(3)
            cl = []
            for j, v in enumerate(vs):
                if j == ti:
                    cl.append(lit_sign(v, sol[v]))
                else:
                    cl.append(lit_sign(v, not sol[v]) if rng.random() < 0.7 else lit_sign(v, sol[v]))
            cls.append(cl)
        write_cnf(os.path.join(out, f"search_sat_walk_n{n}.cnf"), n, cls, model=sol)
        counts["search_stress"] += 1


# ---------------------------------------------------------------------------
# 9. Random 3-SAT Phase Transition — 40 CNFs (mixed SAT/UNSAT)
# ---------------------------------------------------------------------------
def gen_rand3sat(n, m, seed):
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        clauses.append([v if rng.getrandbits(1) else -v for v in vs])
    return n, clauses


def gen_rand3sat_family(out, counts):
    specs = [
        (18, 77), (24, 102), (32, 136), (42, 179),
        (54, 230), (68, 290), (84, 358), (100, 426),
    ]
    for n, m in specs:
        for s in (1, 2, 3, 4, 5):
            # Vary ratio slightly for seeds 4 & 5 to sample both sides of threshold
            m_use = m if s <= 3 else (int(3.9 * n) if s == 4 else int(4.6 * n))
            nv, cls = gen_rand3sat(n, m_use, 90000 + n * 100 + s)
            write_cnf(os.path.join(out, f"r3sat_n{n}_m{m_use}_s{s}.cnf"), nv, cls)
            counts["rand3sat"] += 1


def main():
    ap = argparse.ArgumentParser(description="Generate 300+ Kissat inprocessing & search CNFs.")
    ap.add_argument("out_dir")
    ap.add_argument("--summary", action="store_true", help="Print per-family CNF counts.")
    args = ap.parse_args()
    out = args.out_dir
    os.makedirs(out, exist_ok=True)

    counts = {
        "php": 0,
        "tseitin": 0,
        "xor": 0,
        "miter": 0,
        "big": 0,
        "subsume_viv": 0,
        "bva": 0,
        "search_stress": 0,
        "rand3sat": 0,
    }
    gen_php_family(out, counts)
    gen_tseitin_family(out, counts)
    gen_xor_family(out, counts)
    gen_miter_family(out, counts)
    gen_big_family(out, counts)
    gen_subsume_viv_family(out, counts)
    gen_bva_family(out, counts)
    gen_search_stress_family(out, counts)
    gen_rand3sat_family(out, counts)

    total = sum(counts.values())
    assert total >= 300, f"Expected >= 300 CNFs, got {total}"
    if args.summary:
        for k, v in counts.items():
            print(f"{k:<14}: {v}")
        print(f"TOTAL         : {total}")


if __name__ == "__main__":
    main()
