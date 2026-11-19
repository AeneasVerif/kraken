#!/usr/bin/env python3
"""Deterministic multi-family DIMACS CNF benchmark generator for LeanQbe Kissat."""

import argparse
import os
import random


def write_cnf(path, nvars, clauses):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")


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


def gen_tseitin(nverts, edges, charges):
    # Variable i+1 corresponds to edge i (0 <= i < len(edges)).
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
            parity = bin(mask).count("1") & 1
            if parity != target:
                # Forbid this edge assignment: negate literals that are 1 in mask.
                cl = []
                for bit, var in enumerate(vs):
                    cl.append(-var if ((mask >> bit) & 1) else var)
                clauses.append(cl)
    return len(edges), clauses


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


def gen_ordering(n):
    # gt(i, j) for i != j, encoded 1-based.
    idx = {}
    nxt = 1
    for i in range(n):
        for j in range(n):
            if i != j:
                idx[(i, j)] = nxt
                nxt += 1
    nvars = nxt - 1
    clauses = []
    for i in range(n):
        for j in range(i + 1, n):
            clauses.append([-idx[(i, j)], -idx[(j, i)]])
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            for k in range(n):
                if k == i or k == j:
                    continue
                clauses.append([-idx[(i, j)], -idx[(j, k)], idx[(i, k)]])
    for i in range(n):
        clauses.append([idx[(j, i)] for j in range(n) if j != i])
    return nvars, clauses


def gen_pebbling_pyramid(height):
    # 2-pebbling CNF on pyramid DAG of height `height`.
    # Level 0 is the single sink; level `height - 1` has `height` sources.
    nodes = {}
    nxt = 1
    for r in range(height):
        for c in range(r + 1):
            nodes[(r, c)] = (nxt, nxt + 1)
            nxt += 2
    nvars = nxt - 1
    clauses = []
    # Sources at bottom row r = height - 1: x_{u,0} v x_{u,1}
    for c in range(height):
        v0, v1 = nodes[(height - 1, c)]
        clauses.append([v0, v1])
    # Internal nodes r < height - 1: preds are (r+1, c) and (r+1, c+1)
    for r in range(height - 1):
        for c in range(r + 1):
            u0, u1 = nodes[(r, c)]
            a0, a1 = nodes[(r + 1, c)]
            b0, b1 = nodes[(r + 1, c + 1)]
            for ax in (a0, a1):
                for bx in (b0, b1):
                    clauses.append([-ax, -bx, u0, u1])
    # Sink (0, 0) forbidden
    s0, s1 = nodes[(0, 0)]
    clauses.append([-s0])
    clauses.append([-s1])
    return nvars, clauses


def gen_rand3sat(n, m, seed):
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        cl = [v if rng.getrandbits(1) else -v for v in vs]
        clauses.append(cl)
    return n, clauses


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out_dir")
    args = ap.parse_args()
    out = args.out_dir
    os.makedirs(out, exist_ok=True)

    # 1. Pigeonhole PHP(4,3) .. PHP(7,6)
    for p, h in [(4, 3), (5, 4), (6, 5), (7, 6)]:
        nv, cls = gen_php(p, h)
        write_cnf(os.path.join(out, f"php_{p}_{h}.cnf"), nv, cls)

    # 2. Tseitin parity formulas (UNSAT odd charge + SAT even charge)
    k4_edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    write_cnf(os.path.join(out, "tseitin_k4_unsat.cnf"),
              *gen_tseitin(4, k4_edges, [1, 0, 0, 0]))
    write_cnf(os.path.join(out, "tseitin_k4_sat.cnf"),
              *gen_tseitin(4, k4_edges, [1, 1, 0, 0]))

    k33_edges = [(i, 3 + j) for i in range(3) for j in range(3)]
    write_cnf(os.path.join(out, "tseitin_k33_unsat.cnf"),
              *gen_tseitin(6, k33_edges, [1, 0, 0, 0, 0, 0]))
    write_cnf(os.path.join(out, "tseitin_k33_sat.cnf"),
              *gen_tseitin(6, k33_edges, [1, 0, 0, 1, 0, 0]))

    for n in (6, 8, 10, 12, 14):
        edges = make_circulant_edges(n)
        write_cnf(os.path.join(out, f"tseitin_circ{n}_unsat.cnf"),
                  *gen_tseitin(n, edges, [1] + [0] * (n - 1)))
        write_cnf(os.path.join(out, f"tseitin_circ{n}_sat.cnf"),
                  *gen_tseitin(n, edges, [1, 1] + [0] * (n - 2)))

    g_edges = make_grid_edges(3, 4)
    write_cnf(os.path.join(out, "tseitin_grid3x4_unsat.cnf"),
              *gen_tseitin(12, g_edges, [1] + [0] * 11))
    write_cnf(os.path.join(out, "tseitin_grid3x4_sat.cnf"),
              *gen_tseitin(12, g_edges, [1, 1] + [0] * 10))

    # 3. Ordering & pebbling UNSAT
    for n in (4, 5, 6, 7):
        nv, cls = gen_ordering(n)
        write_cnf(os.path.join(out, f"ordering_{n}.cnf"), nv, cls)

    for h in (4, 5, 6):
        nv, cls = gen_pebbling_pyramid(h)
        write_cnf(os.path.join(out, f"pebbling_h{h}.cnf"), nv, cls)

    # 4. Random 3-SAT near m/n ~ 4.26 threshold
    for n, m in [(25, 107), (40, 170), (55, 234), (75, 320), (100, 426)]:
        seeds = [1, 2, 3, 4] if n <= 75 else [1, 2]
        for s in seeds:
            nv, cls = gen_rand3sat(n, m, 202600 + n * 100 + s)
            write_cnf(os.path.join(out, f"r3sat_n{n}_s{s}.cnf"), nv, cls)


if __name__ == "__main__":
    main()
