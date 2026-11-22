/* Shared PrintCpp (`-DLCNF_TQBE`) runtime wrappers for lcnf_main.c and lcnf_p5_main.c. */
#ifndef LCNF_TQBE_WRAPPERS_H
#define LCNF_TQBE_WRAPPERS_H

typedef ::tqbe::bits<64> W;
static ::tqbe::Mem g_mem;
#define RT_ADDR 0x10000ULL
static u64 g_rt = RT_ADDR;
static inline W w(u64 x) { return W(x); }

W lcnf_alloc(::tqbe::Mem &, W rt, W sz) { return w(rt_lcnf_alloc(rt.word(0), sz.word(0))); }
std::tuple<> lcnf_dec_ref_cold(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_dec_ref_cold(rt.word(0), o.word(0));
  return {};
}
std::tuple<> lcnf_free_obj(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_free_obj(rt.word(0), o.word(0));
  return {};
}
std::tuple<> lcnf_mark_persistent(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_mark_persistent(rt.word(0), o.word(0));
  return {};
}
W lcnf_nat_slow(::tqbe::Mem &, W rt, W op, W a, W b) {
  return w(rt_lcnf_nat_slow(rt.word(0), op.word(0), a.word(0), b.word(0)));
}
W lcnf_clo_under(::tqbe::Mem &, W rt, W f, W k) {
  return w(rt_lcnf_clo_under(rt.word(0), f.word(0), k.word(0)));
}
W lcnf_str_alloc(::tqbe::Mem &, W rt, W blen, W clen) {
  return w(rt_lcnf_str_alloc(rt.word(0), blen.word(0), clen.word(0)));
}
W lcnf_nat_alloc(::tqbe::Mem &, W rt, W nlimbs) {
  return w(rt_lcnf_nat_alloc(rt.word(0), nlimbs.word(0)));
}
W lcnf_nat_to_str(::tqbe::Mem &, W rt, W n) {
  return w(rt_lcnf_nat_to_str(rt.word(0), n.word(0)));
}
W lcnf_char_op(::tqbe::Mem &, W rt, W op, W x) {
  return w(rt_lcnf_char_op(rt.word(0), op.word(0), x.word(0)));
}
W lcnf_oob(::tqbe::Mem &, W rt, W dv) {
  return w(rt_lcnf_oob(rt.word(0), dv.word(0)));
}
W lcnf_array_mk_empty(::tqbe::Mem &, W rt, W cap) {
  return w(rt_lcnf_array_mk_empty(rt.word(0), cap.word(0)));
}
W lcnf_array_mk(::tqbe::Mem &, W rt, W list) {
  return w(rt_lcnf_array_mk(rt.word(0), list.word(0)));
}
W lcnf_array_to_list(::tqbe::Mem &, W rt, W arr) {
  return w(rt_lcnf_array_to_list(rt.word(0), arr.word(0)));
}
W lcnf_array_push(::tqbe::Mem &, W rt, W arr, W v) {
  return w(rt_lcnf_array_push(rt.word(0), arr.word(0), v.word(0)));
}
W lcnf_array_replicate(::tqbe::Mem &, W rt, W n, W v) {
  return w(rt_lcnf_array_replicate(rt.word(0), n.word(0), v.word(0)));
}
W lcnf_array_get(::tqbe::Mem &, W rt, W dv, W arr, W idx, W flags) {
  return w(rt_lcnf_array_get(rt.word(0), dv.word(0), arr.word(0), idx.word(0), flags.word(0)));
}
W lcnf_array_set(::tqbe::Mem &, W rt, W arr, W idx, W v, W unboxed) {
  return w(rt_lcnf_array_set(rt.word(0), arr.word(0), idx.word(0), v.word(0), unboxed.word(0)));
}
W lcnf_array_pop(::tqbe::Mem &, W rt, W arr) {
  return w(rt_lcnf_array_pop(rt.word(0), arr.word(0)));
}
W lcnf_array_swap(::tqbe::Mem &, W rt, W arr, W i, W j, W chk) {
  return w(rt_lcnf_array_swap(rt.word(0), arr.word(0), i.word(0), j.word(0), chk.word(0)));
}
W lcnf_string_push(::tqbe::Mem &, W rt, W s, W c) {
  return w(rt_lcnf_string_push(rt.word(0), s.word(0), c.word(0)));
}
W lcnf_string_append(::tqbe::Mem &, W rt, W s1, W s2) {
  return w(rt_lcnf_string_append(rt.word(0), s1.word(0), s2.word(0)));
}
W lcnf_string_to_list(::tqbe::Mem &, W rt, W s) {
  return w(rt_lcnf_string_to_list(rt.word(0), s.word(0)));
}
W lcnf_string_mk(::tqbe::Mem &, W rt, W cs) {
  return w(rt_lcnf_string_mk(rt.word(0), cs.word(0)));
}
W lcnf_string_cmp_op(::tqbe::Mem &, W rt, W op, W s1, W s2) {
  return w(rt_lcnf_string_cmp_op(rt.word(0), op.word(0), s1.word(0), s2.word(0)));
}
W lcnf_string_pos_op(::tqbe::Mem &, W rt, W op, W s, W i, W e) {
  return w(rt_lcnf_string_pos_op(rt.word(0), op.word(0), s.word(0), i.word(0), e.word(0)));
}
W lcnf_ba_empty(::tqbe::Mem &, W rt) {
  return w(rt_lcnf_ba_empty(rt.word(0)));
}
W lcnf_ba_mk_empty(::tqbe::Mem &, W rt, W cap) {
  return w(rt_lcnf_ba_mk_empty(rt.word(0), cap.word(0)));
}
W lcnf_ba_mk(::tqbe::Mem &, W rt, W arr) {
  return w(rt_lcnf_ba_mk(rt.word(0), arr.word(0)));
}
W lcnf_ba_data(::tqbe::Mem &, W rt, W ba) {
  return w(rt_lcnf_ba_data(rt.word(0), ba.word(0)));
}
W lcnf_ba_push(::tqbe::Mem &, W rt, W ba, W b) {
  return w(rt_lcnf_ba_push(rt.word(0), ba.word(0), b.word(0)));
}
W lcnf_ba_get(::tqbe::Mem &, W rt, W ba, W idx, W unboxed) {
  return w(rt_lcnf_ba_get(rt.word(0), ba.word(0), idx.word(0), unboxed.word(0)));
}
W lcnf_ba_set(::tqbe::Mem &, W rt, W ba, W idx, W b, W unboxed) {
  return w(rt_lcnf_ba_set(rt.word(0), ba.word(0), idx.word(0), b.word(0), unboxed.word(0)));
}
W lcnf_ba_cmp_op(::tqbe::Mem &, W rt, W op, W a, W b) {
  return w(rt_lcnf_ba_cmp_op(rt.word(0), op.word(0), a.word(0), b.word(0)));
}
W lcnf_float_bin(::tqbe::Mem &, W rt, W op, W a, W b) {
  return w(rt_lcnf_float_bin(rt.word(0), op.word(0), a.word(0), b.word(0)));
}
W lcnf_float_un(::tqbe::Mem &, W rt, W op, W a) {
  return w(rt_lcnf_float_un(rt.word(0), op.word(0), a.word(0)));
}
W lcnf_float_of_sci(::tqbe::Mem &, W rt, W m, W neg, W e) {
  return w(rt_lcnf_float_of_sci(rt.word(0), m.word(0), neg.word(0), e.word(0)));
}

static void rt_setup(void) {
  lcnf_tqbe_mem = &g_mem;
  g_mem.alloc(RT_ADDR, LCNF_RT_T_BYTES, 0);
  lcnf_rt_init(g_rt);
}

#endif
