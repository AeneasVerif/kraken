#!/usr/bin/env python3
"""Shared CNF formula and graph edge generators for Kissat benchmarks."""

from __future__ import annotations

import os
import random
from typing import Any


def verify_model(nvars: int, clauses: list[list[int]], model: list[bool]) -> None:
    """Verify that `model` satisfies all clauses."""
    assert len(model) >= nvars + 1, f"model length {len(model)} < nvars+1={nvars+1}"
    for cl in clauses:
        ok = False
        for lit in cl:
            v = abs(lit)
            assert 1 <= v <= nvars, f"bad lit {lit} (nvars={nvars})"
            if (lit > 0 and model[v]) or (lit < 0 and not model[v]):
                ok = True
                break
        if not ok:
            raise AssertionError(f"Model failed clause {cl}")


def write_cnf(
    path: str,
    nvars: int,
    clauses: list[list[int]],
    comment: str | None = None,
    model: list[bool] | None = None,
) -> dict[str, Any]:
    """Write DIMACS CNF file, optionally verifying a model or adding header comments."""
    assert nvars >= 1, f"invalid nvars={nvars} for {path}"
    assert len(clauses) >= 1, f"no clauses for {path}"
    n_bin = 0
    max_sz = 0
    min_sz = 1 << 30
    for cl in clauses:
        sz = len(cl)
        assert sz >= 1, f"empty clause in {path}"
        if sz == 2:
            n_bin += 1
        if sz > max_sz:
            max_sz = sz
        if sz < min_sz:
            min_sz = sz
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
    return {
        "vars": nvars,
        "clauses": len(clauses),
        "binaries": n_bin,
        "min_cl": min_sz,
        "max_cl": max_sz,
    }


def encode_xor_lits(lits: list[int], rhs: int) -> list[list[int]]:
    """Encode XOR constraint sum(lits) = rhs (mod 2) into 2^(k-1) clauses."""
    k = len(lits)
    clauses: list[list[int]] = []
    for mask in range(1 << k):
        if (mask.bit_count() & 1) != (rhs & 1):
            clauses.append([-l if ((mask >> b) & 1) else l for b, l in enumerate(lits)])
    return clauses


def gen_php(pigeons: int, holes: int, v_off: int = 0) -> tuple[int, list[list[int]]]:
    """Generate Pigeonhole Principle (PHP) CNF with `pigeons` and `holes`."""
    clauses: list[list[int]] = []
    for i in range(pigeons):
        clauses.append([v_off + i * holes + j + 1 for j in range(holes)])
    for j in range(holes):
        for i1 in range(pigeons):
            for i2 in range(i1 + 1, pigeons):
                clauses.append([-(v_off + i1 * holes + j + 1), -(v_off + i2 * holes + j + 1)])
    return pigeons * holes, clauses


def make_circulant_edges(n: int) -> list[tuple[int, int]]:
    """Generate 4-regular circulant graph C(n; 1, n//2) edges."""
    edges: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for i in range(n):
        for j in ((i + 1) % n, (i + n // 2) % n):
            a, b = (i, j) if i < j else (j, i)
            if a != b and (a, b) not in seen:
                seen.add((a, b))
                edges.append((a, b))
    return edges


def make_grid_edges(rows: int, cols: int) -> list[tuple[int, int]]:
    """Generate grid graph edges of size rows x cols."""
    edges: list[tuple[int, int]] = []
    for r in range(rows):
        for c in range(cols):
            u = r * cols + c
            if r + 1 < rows:
                edges.append((u, (r + 1) * cols + c))
            if c + 1 < cols:
                edges.append((u, r * cols + (c + 1)))
    return edges


def make_prism_edges(n: int) -> list[tuple[int, int]]:
    """Generate 3-regular prism graph Y_n edges (two n-cycles with rungs)."""
    edges: list[tuple[int, int]] = []
    for i in range(n):
        edges.append((i, (i + 1) % n))
        edges.append((n + i, n + (i + 1) % n))
        edges.append((i, n + i))
    return edges


def gen_tseitin(
    nverts: int, edges: list[tuple[int, int]], charges: list[int]
) -> tuple[int, list[list[int]]]:
    """Generate Tseitin parity formula on arbitrary graph."""
    inc: list[list[int]] = [[] for _ in range(nverts)]
    for eidx, (u, v) in enumerate(edges):
        var = eidx + 1
        inc[u].append(var)
        inc[v].append(var)
    clauses: list[list[int]] = []
    for v in range(nverts):
        vs = inc[v]
        d = len(vs)
        target = charges[v] & 1
        for mask in range(1 << d):
            if (mask.bit_count() & 1) != target:
                clauses.append([-var if ((mask >> bit) & 1) else var for bit, var in enumerate(vs)])
    return len(edges), clauses


def gen_pebbling_pyramid(height: int) -> tuple[int, list[list[int]]]:
    """2-pebbling contradiction on a pyramid DAG of height `height` (UNSAT)."""
    nodes: dict[tuple[int, int], tuple[int, int]] = {}
    nxt = 1
    for r in range(height):
        for c in range(r + 1):
            nodes[(r, c)] = (nxt, nxt + 1)
            nxt += 2
    clauses: list[list[int]] = []
    # Sources at bottom row r = height - 1: p0 \/ p1
    for c in range(height):
        v0, v1 = nodes[(height - 1, c)]
        clauses.append([v0, v1])
    # Propagation: (left pebbled) /\ (right pebbled) => parent pebbled
    for r in range(height - 1):
        for c in range(r + 1):
            pa, pb = nodes[(r, c)]
            la, lb = nodes[(r + 1, c)]
            ra, rb = nodes[(r + 1, c + 1)]
            for ax in (la, lb):
                for bx in (ra, rb):
                    clauses.append([-ax, -bx, pa, pb])
    # Sink / root (0, 0) forbidden: ~p0 /\ ~p1
    s0, s1 = nodes[(0, 0)]
    clauses.append([-s0])
    clauses.append([-s1])
    return nxt - 1, clauses


def gen_graph_kcol(
    nverts: int, edges: list[tuple[int, int]], k: int
) -> tuple[int, list[list[int]]]:
    """Encode k-coloring of graph (UNSAT when chromatic number > k)."""
    nvars = nverts * k
    clauses: list[list[int]] = []
    for v in range(nverts):
        clauses.append([v * k + c + 1 for c in range(k)])
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                clauses.append([-(v * k + c1 + 1), -(v * k + c2 + 1)])
    for u, v in edges:
        for c in range(k):
            clauses.append([-(u * k + c + 1), -(v * k + c + 1)])
    return nvars, clauses


def gen_rand3sat(n: int, m: int, seed: int) -> tuple[int, list[list[int]]]:
    """Generate uniform random 3-SAT formula with n variables, m clauses."""
    rng = random.Random(seed)
    clauses: list[list[int]] = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        clauses.append([v if rng.getrandbits(1) else -v for v in vs])
    return n, clauses
