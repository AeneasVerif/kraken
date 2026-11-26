/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Search Boolean Constraint Propagation & Trail Flush (`Src/PropSearch.lean`)

Mirrors upstream `kissat/src/propsearch.c, proplit.h, trail.c` (`7` live functions, DAG level `L2`):
- `full_prop_lit_ovf_hot` (R4: `kissat_propagate_watch_overflow`)
- `full_prop_flush_slow_fid` (R4: `kissat_flush_delayed_slow`)
- `full_prop_flush_del_fid` (R4: `kissat_flush_delayed_watches`)
- `full_propagate_ignore_hot` (R4: `kissat_propagate_ignore_hot`)
- `full_propagate_ignore` (R4: `kissat_propagate_ignore`)
- `full_propagate` (R4: `kissat_search_propagate`)
- `full_flush_trail` (R4: `kissat_flush_trail`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.PropSearch

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! propSearch "
#include \"kissat_internal.h\"

extern bool full_watch_push(FullHdr *h, u32 lit, u32 w0, u32 w1, u32 cnt);
extern void full_backtrack(FullHdr *h, u64 target_lvl);

bool full_prop_lit_ovf_hot(FullHdr *h, u32 rw, u32 w0, u32 cref) {
  return full_watch_push(h, rw, w0, cref, 2u);
}

bool full_prop_flush_slow_fid(FullHdr *h, u64 j, u64 di) {
  u32 *del = (u32 *)h->delayed;
  if (!full_watch_push(h, del[j], del[j + 1ULL], del[j + 2ULL], 2u)) { return false; }
  j = j + 3ULL;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  while (j < di) {
    u32 rw = del[j];
    u32 ow = del[j + 1ULL];
    u32 cr = del[j + 2ULL];
    u64 wlen = h->wlen;
    u64 wu = h->wusable;
    u64 rw64 = (u64)rw << 1;
    u64 roff = (u64)wvec[rw64];
    u64 rsz = (u64)wvec[rw64 + 1ULL];
    if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
        wstk[roff + rsz] == 0xFFFFFFFFu &&
        wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
      wstk[roff + rsz] = ow;
      wstk[roff + rsz + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      if (wu >= 2ULL) { h->wusable = wu - 2ULL; }
    } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      h->wlen = wlen + 2ULL;
    } else if (rsz == 0ULL && wlen > 0ULL && wlen + 2ULL <= wcap) {
      wvec[rw64] = (u32)wlen;
      wvec[rw64 + 1ULL] = 2u;
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      h->wlen = wlen + 2ULL;
    } else {
      if (!full_watch_push(h, rw, ow, cr, 2u)) { return false; }
      wstk = (u32 *)h->watch_stk;
    }
    j = j + 3ULL;
  }
  return true;
}

bool full_prop_flush_del_fid(FullHdr *h, u64 di) {
  u32 *del = (u32 *)h->delayed;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u64 wcap = h->wcap;
  u64 wlen = h->wlen;
  u64 wu = h->wusable;
  u64 j = 0ULL;
  while (j < di) {
    u32 rw = del[j];
    u32 ow = del[j + 1ULL];
    u32 cr = del[j + 2ULL];
    u64 rw64 = (u64)rw << 1;
    u64 roff = (u64)wvec[rw64];
    u64 rsz = (u64)wvec[rw64 + 1ULL];
    if (rsz > 0ULL && roff + rsz + 2ULL <= wlen &&
        wstk[roff + rsz] == 0xFFFFFFFFu &&
        wstk[roff + rsz + 1ULL] == 0xFFFFFFFFu) {
      wstk[roff + rsz] = ow;
      wstk[roff + rsz + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      if (wu >= 2ULL) { wu = wu - 2ULL; }
    } else if (rsz > 0ULL && roff + rsz == wlen && wlen + 2ULL <= wcap) {
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wvec[rw64 + 1ULL] = (u32)(rsz + 2ULL);
      wlen = wlen + 2ULL;
    } else if (rsz == 0ULL && wlen > 0ULL && wlen + 2ULL <= wcap) {
      wvec[rw64] = (u32)wlen;
      wvec[rw64 + 1ULL] = 2u;
      wstk[wlen] = ow;
      wstk[wlen + 1ULL] = cr;
      wlen = wlen + 2ULL;
    } else {
      h->wlen = wlen;
      h->wusable = wu;
      return full_prop_flush_slow_fid(h, j, di);
    }
    j = j + 3ULL;
  }
  h->wlen = wlen;
  h->wusable = wu;
  return true;
}

u64 full_propagate_ignore_hot(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u32 *del = (u32 *)h->delayed;
  u64 dlim = h->delayed_cap * 3ULL;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  u64 fuel = h->fuel;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    if (fuel == 0ULL) {
      h->fuel = 0ULL;
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec[nl64];
    u64 sz = (u64)wvec[nl64 + 1ULL];
    if (sz == 0ULL) {
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u32 nl_lvl = lvl[not_lit >> 1];
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 di = 0ULL;
    u64 brk = 0ULL;
    bool ovf = true;
    while (ovf) {
      ovf = false;
      u32 ovf_rw = 0u;
      u32 ovf_other = 0u;
      u32 ovf_cref = 0u;
      u64 ovf_ri = 0ULL;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          p = p + 1ULL;
          u32 blk = w0 & PW_LIT_MASK;
          i8 bv = vals[blk];
          wstk[q] = w0;
          q = q + 1ULL;
          if (bv > (i8)0) { continue; }
          if (bv < (i8)0) {
            brk = 1ULL;
            h->confl_type = 1ULL;
            h->confl_lit0 = (u64)not_lit;
            h->confl_lit1 = (u64)blk;
            break;
          }
          ticks = ticks + 1ULL;
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = nl_lvl;
          if (nl_lvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            rsns[bv64] = PW_BIN_FLAG | not_lit;
          }
          tpos[bv64] = (u32)tend;
          trl[tend] = blk;
          tend = tend + 1ULL;
          continue;
        }
        if ((u64)w0 < nlits && vals[w0] > (i8)0) {
          u32 cref0 = wstk[p + 1ULL];
          p = p + 2ULL;
          wstk[q] = w0;
          wstk[q + 1ULL] = cref0;
          q = q + 2ULL;
          continue;
        }
        u32 cref = wstk[p + 1ULL];
        p = p + 2ULL;
        ticks = ticks + 1ULL;
        u32 chdr = ar[cref];
        if ((chdr & PH_GARB) != 0u) { continue; }
        u64 cbase = (u64)cref + 3ULL;
        u32 l0 = ar[cbase];
        u32 l1 = ar[cbase + 1ULL];
        if (l0 != not_lit && l1 != not_lit) { continue; }
        u32 other = l0 ^ l1 ^ not_lit;
        if (l0 == not_lit) {
          ar[cbase] = other;
          ar[cbase + 1ULL] = not_lit;
        }
        i8 ov = vals[other];
        if (ov > (i8)0) {
          wstk[q] = other;
          wstk[q + 1ULL] = cref;
          q = q + 2ULL;
          continue;
        }
        u64 csz = (u64)ar[(u64)cref + 2ULL];
        u64 srch = (u64)ar[(u64)cref + 1ULL];
        if (srch < 2ULL || srch >= csz) { srch = 2ULL; }
        u64 ri = srch;
        u32 repl = 0u;
        bool found = false;
        while (ri < csz) {
          u32 cand = ar[cbase + ri];
          if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
          ri = ri + 1ULL;
        }
        if (!found) {
          ri = 2ULL;
          while (ri < srch) {
            u32 cand = ar[cbase + ri];
            if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
            ri = ri + 1ULL;
          }
        }
        if (found) {
          ticks = ticks + 1ULL;
          ar[(u64)cref + 1ULL] = (u32)ri;
          if (repl == not_lit) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[q] = other;
            wstk[q + 1ULL] = cref;
            q = q + 2ULL;
          } else if (di < dlim) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            del[di] = repl;
            del[di + 1ULL] = other;
            del[di + 2ULL] = cref;
            di = di + 3ULL;
          } else {
            ovf_rw = repl;
            ovf_other = other;
            ovf_cref = cref;
            ovf_ri = ri;
            ovf = true;
            break;
          }
          continue;
        }
        wstk[q] = other;
        wstk[q + 1ULL] = cref;
        q = q + 2ULL;
        if ((u64)cref == ignore_ref) { continue; }
        if (ov < (i8)0) {
          brk = 1ULL;
          h->confl_type = 2ULL;
          h->confl_ref = (u64)cref;
          break;
        }
        ticks = ticks + 1ULL;
        u32 alvl = nl_lvl;
        if (nl_lvl < clvl32) {
          u32 mx = 0u;
          u64 bi = 0ULL;
          while (bi < csz) {
            u32 clit = ar[cbase + bi];
            if (clit != other) {
              u32 lv = lvl[clit >> 1];
              if (lv > mx) { mx = lv; }
            }
            bi = bi + 1ULL;
          }
          alvl = mx;
        }
        u64 ov64 = (u64)(other >> 1);
        vals[other] = (i8)1;
        vals[other ^ 1u] = (i8)(-1);
        if ((fl[ov64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
        if (rec_ph) {
          if ((other & 1u) != 0u) { ph[ov64] = (i8)(-1); }
          else { ph[ov64] = (i8)1; }
        }
        lvl[ov64] = alvl;
        if (alvl == 0u) {
          rsns[ov64] = 0xFFFFFFFFu;
          fl[ov64] = fl[ov64] & (~FL_ACTIVE);
          unfl = unfl + 1ULL;
        } else {
          rsns[ov64] = cref;
        }
        tpos[ov64] = (u32)tend;
        trl[tend] = other;
        tend = tend + 1ULL;
      }
      if (ovf) {
        bool fok = true;
        if (di > 0ULL) {
          fok = full_prop_flush_del_fid(h, di);
          di = 0ULL;
        }
        bool pushed = false;
        if (fok) {
          pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        }
        u64 noff = (u64)wvec[nl64];
        if (noff != off) {
          q = noff + (q - off);
          p = noff + (p - off);
          end = noff + (end - off);
          off = noff;
        }
        if (!pushed) {
          wstk[q] = ovf_other;
          wstk[q + 1ULL] = ovf_cref;
          q = q + 2ULL;
          brk = 2ULL;
          break;
        }
        u64 obase = (u64)ovf_cref + 3ULL;
        ar[obase] = ovf_other;
        ar[obase + 1ULL] = ovf_rw;
        ar[obase + ovf_ri] = not_lit;
      }
    }
    while (p < end) {
      wstk[q] = wstk[p];
      q = q + 1ULL;
      p = p + 1ULL;
    }
    wvec[nl64 + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (di > 0ULL) {
      if (!full_prop_flush_del_fid(h, di)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->fuel = fuel;
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->fuel = fuel;
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  h->search_ticks = h->search_ticks + ticks;
  return 0ULL;
}

u64 full_propagate_ignore(FullHdr *h, u64 ignore_ref) {
  u64 prop = h->propagated;
  u64 tend = h->trail_end;
  if (prop >= tend) { return 0ULL; }
  if (h->oom != 0ULL) { return 2ULL; }
  i8 *vals = (i8 *)h->values;
  u32 *wvec = (u32 *)h->watch_vec;
  u32 *wstk = (u32 *)h->watch_stk;
  u32 *ar = (u32 *)h->arena;
  u32 *lvl = (u32 *)h->level;
  u32 *rsns = (u32 *)h->reason;
  u32 *trl = (u32 *)h->trail;
  u32 *tpos = (u32 *)h->trail_pos;
  u32 *fl = (u32 *)h->flags;
  i8 *ph = (i8 *)h->phases;
  u32 *del = (u32 *)h->delayed;
  u64 dlim = h->delayed_cap * 3ULL;
  u64 nlits = h->cur_vars << 1;
  u64 clvl = h->cur_level;
  u32 clvl32 = (u32)clvl;
  bool rec_ph = (h->probing == 0ULL);
  u64 fuel = h->fuel;
  u64 unass = h->unassigned;
  u64 unfl = h->unflushed;
  u64 ticks = 0ULL;
  while (prop < tend) {
    if (fuel == 0ULL) {
      h->fuel = 0ULL;
      h->propagated = prop;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return 2ULL;
    }
    fuel = fuel - 1ULL;
    u32 lit = trl[prop];
    u32 not_lit = lit ^ 1u;
    u64 nl64 = (u64)not_lit << 1;
    u64 off = (u64)wvec[nl64];
    u64 sz = (u64)wvec[nl64 + 1ULL];
    if (sz == 0ULL) {
      prop = prop + 1ULL;
      continue;
    }
    ticks = ticks + 1ULL + ((sz + 31ULL) >> 5ULL);
    u32 nl_lvl = lvl[not_lit >> 1];
    u64 p = off;
    u64 q = off;
    u64 end = off + sz;
    u64 di = 0ULL;
    u64 brk = 0ULL;
    bool ovf = true;
    while (ovf) {
      ovf = false;
      u32 ovf_rw = 0u;
      u32 ovf_other = 0u;
      u32 ovf_cref = 0u;
      u64 ovf_ri = 0ULL;
      while (p < end) {
        u32 w0 = wstk[p];
        if ((w0 & PW_BIN_FLAG) != 0u) {
          p = p + 1ULL;
          u32 blk = w0 & PW_LIT_MASK;
          i8 bv = vals[blk];
          wstk[q] = w0;
          q = q + 1ULL;
          if (bv > (i8)0) { continue; }
          if (bv < (i8)0) {
            brk = 1ULL;
            h->confl_type = 1ULL;
            h->confl_lit0 = (u64)not_lit;
            h->confl_lit1 = (u64)blk;
            break;
          }
          ticks = ticks + 1ULL;
          u64 bv64 = (u64)(blk >> 1);
          vals[blk] = (i8)1;
          vals[blk ^ 1u] = (i8)(-1);
          if ((fl[bv64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
          if (rec_ph) {
            if ((blk & 1u) != 0u) { ph[bv64] = (i8)(-1); }
            else { ph[bv64] = (i8)1; }
          }
          lvl[bv64] = nl_lvl;
          if (nl_lvl == 0u) {
            rsns[bv64] = 0xFFFFFFFFu;
            fl[bv64] = fl[bv64] & (~FL_ACTIVE);
            unfl = unfl + 1ULL;
          } else {
            rsns[bv64] = PW_BIN_FLAG | not_lit;
          }
          tpos[bv64] = (u32)tend;
          trl[tend] = blk;
          tend = tend + 1ULL;
          continue;
        }
        if ((u64)w0 < nlits && vals[w0] > (i8)0) {
          u32 cref0 = wstk[p + 1ULL];
          p = p + 2ULL;
          wstk[q] = w0;
          wstk[q + 1ULL] = cref0;
          q = q + 2ULL;
          continue;
        }
        u32 cref = wstk[p + 1ULL];
        p = p + 2ULL;
        ticks = ticks + 1ULL;
        u32 chdr = ar[cref];
        if ((chdr & PH_GARB) != 0u) { continue; }
        u64 cbase = (u64)cref + 3ULL;
        u32 l0 = ar[cbase];
        u32 l1 = ar[cbase + 1ULL];
        if (l0 != not_lit && l1 != not_lit) { continue; }
        u32 other = l0 ^ l1 ^ not_lit;
        if (l0 == not_lit) {
          ar[cbase] = other;
          ar[cbase + 1ULL] = not_lit;
        }
        i8 ov = vals[other];
        if (ov > (i8)0) {
          wstk[q] = other;
          wstk[q + 1ULL] = cref;
          q = q + 2ULL;
          continue;
        }
        u64 csz = (u64)ar[(u64)cref + 2ULL];
        u64 srch = (u64)ar[(u64)cref + 1ULL];
        if (srch < 2ULL || srch >= csz) { srch = 2ULL; }
        u64 ri = srch;
        u32 repl = 0u;
        bool found = false;
        while (ri < csz) {
          u32 cand = ar[cbase + ri];
          if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
          ri = ri + 1ULL;
        }
        if (!found) {
          ri = 2ULL;
          while (ri < srch) {
            u32 cand = ar[cbase + ri];
            if (vals[cand] >= (i8)0) { repl = cand; found = true; break; }
            ri = ri + 1ULL;
          }
        }
        if (found) {
          ticks = ticks + 1ULL;
          ar[(u64)cref + 1ULL] = (u32)ri;
          if (repl == not_lit) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            wstk[q] = other;
            wstk[q + 1ULL] = cref;
            q = q + 2ULL;
          } else if (di < dlim) {
            ar[cbase] = other;
            ar[cbase + 1ULL] = repl;
            ar[cbase + ri] = not_lit;
            del[di] = repl;
            del[di + 1ULL] = other;
            del[di + 2ULL] = cref;
            di = di + 3ULL;
          } else {
            ovf_rw = repl;
            ovf_other = other;
            ovf_cref = cref;
            ovf_ri = ri;
            ovf = true;
            break;
          }
          continue;
        }
        wstk[q] = other;
        wstk[q + 1ULL] = cref;
        q = q + 2ULL;
        if ((u64)cref == ignore_ref) { continue; }
        if (ov < (i8)0) {
          brk = 1ULL;
          h->confl_type = 2ULL;
          h->confl_ref = (u64)cref;
          break;
        }
        ticks = ticks + 1ULL;
        u32 alvl = nl_lvl;
        if (nl_lvl < clvl32) {
          u32 mx = 0u;
          u64 bi = 0ULL;
          while (bi < csz) {
            u32 clit = ar[cbase + bi];
            if (clit != other) {
              u32 lv = lvl[clit >> 1];
              if (lv > mx) { mx = lv; }
            }
            bi = bi + 1ULL;
          }
          alvl = mx;
        }
        u64 ov64 = (u64)(other >> 1);
        vals[other] = (i8)1;
        vals[other ^ 1u] = (i8)(-1);
        if ((fl[ov64] & FL_ACTIVE) != 0u && unass > 0ULL) { unass = unass - 1ULL; }
        if (rec_ph) {
          if ((other & 1u) != 0u) { ph[ov64] = (i8)(-1); }
          else { ph[ov64] = (i8)1; }
        }
        lvl[ov64] = alvl;
        if (alvl == 0u) {
          rsns[ov64] = 0xFFFFFFFFu;
          fl[ov64] = fl[ov64] & (~FL_ACTIVE);
          unfl = unfl + 1ULL;
        } else {
          rsns[ov64] = cref;
        }
        tpos[ov64] = (u32)tend;
        trl[tend] = other;
        tend = tend + 1ULL;
      }
      if (ovf) {
        bool fok = true;
        if (di > 0ULL) {
          fok = full_prop_flush_del_fid(h, di);
          di = 0ULL;
        }
        bool pushed = false;
        if (fok) {
          pushed = full_prop_lit_ovf_hot(h, ovf_rw, ovf_other, ovf_cref);
        }
        u64 noff = (u64)wvec[nl64];
        if (noff != off) {
          q = noff + (q - off);
          p = noff + (p - off);
          end = noff + (end - off);
          off = noff;
        }
        if (!pushed) {
          wstk[q] = ovf_other;
          wstk[q + 1ULL] = ovf_cref;
          q = q + 2ULL;
          brk = 2ULL;
          break;
        }
        u64 obase = (u64)ovf_cref + 3ULL;
        ar[obase] = ovf_other;
        ar[obase + 1ULL] = ovf_rw;
        ar[obase + ovf_ri] = not_lit;
      }
    }
    while (p < end) {
      wstk[q] = wstk[p];
      q = q + 1ULL;
      p = p + 1ULL;
    }
    wvec[nl64 + 1ULL] = (u32)(q - off);
    if (q < end) {
      h->wusable = h->wusable + (end - q);
      u64 k = q;
      while (k < end) {
        wstk[k] = 0xFFFFFFFFu;
        k = k + 1ULL;
      }
    }
    if (di > 0ULL) {
      if (!full_prop_flush_del_fid(h, di)) { brk = 2ULL; }
    }
    if (brk != 0ULL) {
      if (brk == 2ULL) { h->oom = 1ULL; }
      h->fuel = fuel;
      h->propagated = prop + 1ULL;
      h->trail_end = tend;
      h->unassigned = unass;
      h->unflushed = unfl;
      h->search_ticks = h->search_ticks + ticks;
      return brk;
    }
    prop = prop + 1ULL;
  }
  h->fuel = fuel;
  h->propagated = prop;
  h->trail_end = tend;
  h->unassigned = unass;
  h->unflushed = unfl;
  h->search_ticks = h->search_ticks + ticks;
  return 0ULL;
}

u64 full_propagate(FullHdr *h) {
  return full_propagate_ignore_hot(h, 0xFFFFFFFFULL);
}

u64 full_flush_trail(FullHdr *h) {
  if (h->inconsistent != 0ULL) { return 20ULL; }
  if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }
  if (h->oom != 0ULL) { return 0ULL; }
  if (h->propagated < h->trail_end) {
    u64 pr = full_propagate(h);
    if (pr == 1ULL) { h->inconsistent = 1ULL; return 20ULL; }
    if (pr != 0ULL || h->oom != 0ULL) { return 0ULL; }
  }
  h->unflushed = 0ULL;
  h->confl_ref = 0xFFFFFFFFULL;
  h->confl_type = 0ULL;
  return 1ULL;
}
"

/-- Ordered live functions of `Src/PropSearch.lean` (`7` fns). -/
def fns : List Fn := propSearch_fns

end

public section

theorem full_prop_lit_ovf_hot_wf : Func.Wf full_prop_lit_ovf_hot_body := by kissat_wf_reify
theorem full_prop_flush_slow_fid_wf : Func.Wf full_prop_flush_slow_fid_body := by kissat_wf_reify
theorem full_prop_flush_del_fid_wf : Func.Wf full_prop_flush_del_fid_body := by kissat_wf_reify
theorem full_propagate_ignore_hot_wf : Func.Wf full_propagate_ignore_hot_body := by kissat_wf_reify
theorem full_propagate_ignore_wf : Func.Wf full_propagate_ignore_body := by kissat_wf_reify
theorem full_propagate_wf : Func.Wf full_propagate_body := by kissat_wf_reify
theorem full_flush_trail_wf : Func.Wf full_flush_trail_body := by kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, propSearch_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact full_prop_lit_ovf_hot_wf
  · exact full_prop_flush_slow_fid_wf
  · exact full_prop_flush_del_fid_wf
  · exact full_propagate_ignore_hot_wf
  · exact full_propagate_ignore_wf
  · exact full_propagate_wf
  · exact full_flush_trail_wf

end

end LeanQbe.T.Examples.Kissat.Src.PropSearch
