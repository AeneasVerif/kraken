#include <lean/lean.h>

extern lean_object *initialize_bv__decide__qbe_BvDecideQbe_TacticImpl(uint8_t builtin);

LEAN_EXPORT lean_obj_res leanqbe_init_tactics(void) {
  return initialize_bv__decide__qbe_BvDecideQbe_TacticImpl(1);
}
