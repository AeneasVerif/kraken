#!/usr/bin/env python3
"""Deterministic multi-family DIMACS CNF benchmark generator for LeanQbe Kissat."""

import argparse
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cnf_families import (
    gen_pebbling_pyramid,
    gen_php,
    gen_rand3sat,
    gen_tseitin,
    make_circulant_edges,
    make_grid_edges,
    write_cnf,
)


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
