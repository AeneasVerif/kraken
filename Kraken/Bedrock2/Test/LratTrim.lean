module

public import Kraken.Bedrock2.CPrinter
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.CPrinter

@[expose] public section

namespace Kraken.Bedrock2.Test

def br_is_original_clause := bedrock2:(fn br_is_original_clause(first_proof_id, id) -> (res) {
  abs_id = id .< 0 ? -id : id;
  res = (abs_id == 0) | (first_proof_id == 0) | (abs_id .< first_proof_id)
})

def br_mark_used := bedrock2:(fn br_mark_used(st, id, used_where) -> (res) {
  used_begin = load8(st);
  w = used_begin + (id << 2);
  used_before = (load4(w) << 32) .>> 32;
  if (used_before .< used_where) == 0 {
    res = 1
  } else {
    store4(w, used_where);
    if used_before {
      res = 1
    } else {
      first_proof_id = (load8(st + 72) << 32) .>> 32;
      is_orig = br_is_original_clause(first_proof_id, id);
      if is_orig {
        store8(st + 112, load8(st + 112) + 1)
      } else {
        store8(st + 120, load8(st + 120) + 1)
      };
      res = 0
    }
  }
})

/-- Inline `mark_used` operating on register-resident locals `used_begin`, `first_proof_id`,
`stat_trimmed_cnf`, `stat_trimmed_prf`, setting `was_used` and `is_orig`. -/
def inline_mark_used (id used_where : Expr) : Cmd := bedrock2_cmd:(
  w = used_begin + (%❰id❱ << 2);
  used_before = (load4(w) << 32) .>> 32;
  if (used_before .< %❰used_where❱) == 0 {
    was_used = 1
  } else {
    store4(w, %❰used_where❱);
    if used_before {
      was_used = 1
    } else {
      is_orig = (first_proof_id == 0) | (%❰id❱ .< first_proof_id);
      if is_orig {
        stat_trimmed_cnf = stat_trimmed_cnf + 1
      } else {
        stat_trimmed_prf = stat_trimmed_prf + 1
      };
      was_used = 0
    }
  }
)

def br_trim_proof := bedrock2:(fn br_trim_proof(st) {
  trimming = load8(st + 88);
  if trimming {
    empty_clause = (load8(st + 64) << 32) .>> 32;
    if empty_clause {
      used_begin = load8(st);
      antecedents_begin = load8(st + 8);
      work_begin = load8(st + 56);
      work_end = work_begin;
      first_proof_id = (load8(st + 72) << 32) .>> 32;
      stat_trimmed_cnf = load8(st + 112);
      stat_trimmed_prf = load8(st + 120);
      %❰inline_mark_used bedrock2_expr:(empty_clause) bedrock2_expr:(empty_clause)❱;
      if (first_proof_id == 0) | (empty_clause .< first_proof_id) {
        skip
      } else {
        store4(work_end, empty_clause);
        work_end = work_end + 4
      };
      while (work_end == work_begin) == 0 {
        work_end = work_end - 4;
        id = (load4(work_end) << 32) .>> 32;
        p = load8(antecedents_begin + (id << 3));
        raw = (load4(p) << 32) .>> 32;
        other = raw .< 0 ? -raw : raw;
        while other {
          %❰inline_mark_used bedrock2_expr:(other) bedrock2_expr:(id)❱;
          if was_used == 0 {
            if is_orig == 0 {
              store4(work_end, other);
              work_end = work_end + 4
            }
          };
          p = p + 4;
          raw = (load4(p) << 32) .>> 32;
          other = raw .< 0 ? -raw : raw
        }
      };
      store8(st + 112, stat_trimmed_cnf);
      store8(st + 120, stat_trimmed_prf)
    }
  }
})

def br_assign_literal := bedrock2:(fn br_assign_literal(st, lit) {
  idx = lit .< 0 ? -lit : lit;
  val = (lit .>> 63) | 1;
  values_begin = load8(st + 24);
  store1(values_begin + idx, val);
  trail_end = load8(st + 48);
  store4(trail_end, lit);
  store8(st + 48, trail_end + 4);
  store8(st + 152, load8(st + 152) + 1)
})

def br_unassign_literal := bedrock2:(fn br_unassign_literal(st, lit) {
  idx = lit .< 0 ? -lit : lit;
  values_begin = load8(st + 24);
  store1(values_begin + idx, 0)
})

def br_backtrack := bedrock2:(fn br_backtrack(st) {
  values_begin = load8(st + 24);
  trail_begin = load8(st + 40);
  trail_end = load8(st + 48);
  t = trail_begin;
  while (t == trail_end) == 0 {
    lit = (load4(t) << 32) .>> 32;
    idx = lit .< 0 ? -lit : lit;
    store1(values_begin + idx, 0);
    t = t + 4
  };
  store8(st + 48, trail_begin)
})

def br_assigned_literal := bedrock2:(fn br_assigned_literal(st, lit) -> (res) {
  idx = lit .< 0 ? -lit : lit;
  values_begin = load8(st + 24);
  res = (load1(values_begin + idx) << 56) .>> 56;
  if lit .< 0 {
    res = -res
  }
})

/-- Inline `assigned_literal` using register-resident `values_begin`, setting `idx` and `val`. -/
def inline_assigned_literal : Cmd := bedrock2_cmd:(
  idx = lit .< 0 ? -lit : lit;
  val = (load1(values_begin + idx) << 56) .>> 56;
  if lit .< 0 {
    val = -val
  }
)

/-- Inline `assign_literal` reusing `idx = |lit|` and register-resident `values_begin`,
`trail_end`, `stat_lit_assigned`. -/
def inline_assign_literal (elit eval : Expr) : Cmd := bedrock2_cmd:(
  store1(values_begin + idx, %❰eval❱);
  store4(trail_end, %❰elit❱);
  trail_end = trail_end + 4;
  stat_lit_assigned = stat_lit_assigned + 1
)

/-- Inline `backtrack` using register-resident `values_begin`, `trail_begin`, `trail_end`. -/
def inline_backtrack : Cmd := bedrock2_cmd:(
  t = trail_begin;
  while (t == trail_end) == 0 {
    tlit = (load4(t) << 32) .>> 32;
    tidx = tlit .< 0 ? -tlit : tlit;
    store1(values_begin + tidx, 0);
    t = t + 4
  };
  trail_end = trail_begin
)

/-- Write back register-resident propagation state to `st`. -/
def flush_prop_state : Cmd := bedrock2_cmd:(
  store8(st + 48, trail_end);
  store8(st + 144, stat_resolved);
  store8(st + 152, stat_lit_assigned)
)

def br_check_clause_non_strictly_by_propagation := bedrock2:(fn br_check_clause_non_strictly_by_propagation(st, id, literals, antecedents) {
  literals_begin = load8(st + 16);
  values_begin = load8(st + 24);
  trail_begin = load8(st + 40);
  trail_end = load8(st + 48);
  stat_resolved = load8(st + 144) + 1;
  stat_lit_assigned = load8(st + 152);
  checked = 0;
  l = literals;
  lit = (load4(l) << 32) .>> 32;
  while lit {
    %❰inline_assigned_literal❱;
    if val .< 0 {
      l = l + 4;
      lit = (load4(l) << 32) .>> 32
    } else {
      if 0 .< val {
        checked = 1;
        lit = 0
      } else {
        %❰inline_assign_literal bedrock2_expr:(-lit) bedrock2_expr:(((-lit) .>> 63) | 1)❱;
        l = l + 4;
        lit = (load4(l) << 32) .>> 32
      }
    }
  };
  if checked == 0 {
    a = antecedents;
    aid = (load4(a) << 32) .>> 32;
    while aid {
      if aid .< 0 {
        %❰flush_prop_state❱;
        interact lrat_fail(1, id, aid, 0, 0)
      };
      als = load8(literals_begin + (aid << 3));
      stat_resolved = stat_resolved + 1;
      unit = 0;
      l = als;
      lit = (load4(l) << 32) .>> 32;
      while lit {
        %❰inline_assigned_literal❱;
        if val .< 0 {
          if unit == -lit {
            %❰flush_prop_state❱;
            interact lrat_fail(2, id, aid, 0, 0)
          }
        } else {
          if unit {
            if (unit == lit) == 0 {
              %❰flush_prop_state❱;
              interact lrat_fail(2, id, aid, 0, 0)
            }
          };
          unit = lit;
          if val == 0 {
            %❰inline_assign_literal bedrock2_expr:(lit) bedrock2_expr:((lit .>> 63) | 1)❱
          }
        };
        l = l + 4;
        lit = (load4(l) << 32) .>> 32
      };
      if unit == 0 {
        checked = 1;
        aid = 0
      } else {
        a = a + 4;
        aid = (load4(a) << 32) .>> 32
      }
    }
  };
  if checked == 0 {
    %❰flush_prop_state❱;
    interact lrat_fail(3, id, 0, 0, 0)
  };
  %❰inline_backtrack❱;
  %❰flush_prop_state❱
})

def br_check_clause_strictly_by_resolution := bedrock2:(fn br_check_clause_strictly_by_resolution(st, id, literals, antecedents) {
  a = antecedents;
  aid = (load4(a) << 32) .>> 32;
  while aid {
    if aid .< 0 {
      interact lrat_fail(1, id, aid, 0, 0)
    };
    a = a + 4;
    aid = (load4(a) << 32) .>> 32
  };
  literals_begin = load8(st + 16);
  marks_begin = load8(st + 32);
  stat_resolved = load8(st + 144);
  resolvent_size = 0;
  first = 1;
  while (a == antecedents) == 0 {
    a = a - 4;
    aid = (load4(a) << 32) .>> 32;
    als = load8(literals_begin + (aid << 3));
    stat_resolved = stat_resolved + 1;
    unit = 0;
    l = als;
    lit = (load4(l) << 32) .>> 32;
    while lit {
      idx = lit .< 0 ? -lit : lit;
      m = marks_begin + idx;
      mark = (load1(m) << 56) .>> 56;
      if mark == 0 {
        store1(m, (lit .>> 63) | 1);
        resolvent_size = resolvent_size + 1
      } else {
        if lit .< 0 {
          mark = -mark
        };
        if (0 .< mark) == 0 {
          if unit {
            store8(st + 144, stat_resolved);
            interact lrat_fail(4, id, unit, lit, aid)
          };
          unit = lit
        }
      };
      l = l + 4;
      lit = (load4(l) << 32) .>> 32
    };
    if first {
      if unit {
        store8(st + 144, stat_resolved);
        interact lrat_fail(4, id, -unit, unit, aid)
      };
      first = 0
    } else {
      if unit == 0 {
        store8(st + 144, stat_resolved);
        interact lrat_fail(5, id, aid, 0, 0)
      } else {
        resolvent_size = resolvent_size - 1;
        idx = unit .< 0 ? -unit : unit;
        m = marks_begin + idx;
        store1(m, 0)
      }
    }
  };
  store8(st + 144, stat_resolved);
  if first {
    interact lrat_fail(3, id, 0, 0, 0)
  };
  l = literals;
  lit = (load4(l) << 32) .>> 32;
  while lit {
    idx = lit .< 0 ? -lit : lit;
    m = marks_begin + idx;
    mark = (load1(m) << 56) .>> 56;
    if mark == 0 {
      interact lrat_fail(6, id, lit, 0, 0)
    };
    if lit .< 0 {
      mark = -mark
    };
    if mark .< 0 {
      interact lrat_fail(7, id, lit, 0, 0)
    };
    store1(m, 0);
    resolvent_size = resolvent_size - 1;
    l = l + 4;
    lit = (load4(l) << 32) .>> 32
  };
  if resolvent_size {
    interact lrat_fail(8, id, resolvent_size, 0, 0)
  }
})

def br_check_clause := bedrock2:(fn br_check_clause(st, id, literals, antecedents) {
  store8(st + 128, load8(st + 128) + 1);
  if load4(literals) == 0 {
    store8(st + 136, load8(st + 136) + 1)
  };
  strict = load8(st + 80);
  if strict {
    br_check_clause_strictly_by_resolution(st, id, literals, antecedents)
  } else {
    br_check_clause_non_strictly_by_propagation(st, id, literals, antecedents)
  }
})

def br_check_proof := bedrock2:(fn br_check_proof(st) {
  checking = load8(st + 96);
  forward = load8(st + 104);
  empty_clause = (load8(st + 64) << 32) .>> 32;
  first_proof_id = (load8(st + 72) << 32) .>> 32;
  if checking {
    if forward == 0 {
      if empty_clause {
        if first_proof_id {
          trimming = load8(st + 88);
          used_begin = load8(st);
          literals_begin = load8(st + 16);
          antecedents_begin = load8(st + 8);
          id = first_proof_id;
          while (empty_clause .< id) == 0 {
            if trimming {
              used_where = (load4(used_begin + (id << 2)) << 32) .>> 32
            } else {
              used_where = -1
            };
            if used_where {
              l = load8(literals_begin + (id << 3));
              a = load8(antecedents_begin + (id << 3));
              br_check_clause(st, id, l, a)
            };
            id = id + 1
          }
        }
      }
    }
  }
})

def lratTrimEntry : List (String × Func) :=
  [br_trim_proof, br_check_proof, br_check_clause]

def lratTrimInternal : List (String × Func) :=
  [br_is_original_clause, br_mark_used, br_assign_literal, br_unassign_literal,
   br_backtrack, br_assigned_literal, br_check_clause_non_strictly_by_propagation,
   br_check_clause_strictly_by_resolution]

def lratTrimC : Except String String := do
  let m ← cModuleForWidth 64 lratTrimEntry lratTrimInternal
  return "#include <stdint.h>\n_Noreturn void lrat_fail(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t);\n\n" ++ m

#guard lratTrimC.isOk

end Kraken.Bedrock2.Test
