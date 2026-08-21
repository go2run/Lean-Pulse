#include <lean/lean.h>
#include <stdio.h>
#include <stdint.h>

/* Velvet 驗證過的程式，經 Lean 編譯器 @[export] 出來的 C 符號 */
extern uint64_t velvet_maximum(uint64_t a, uint64_t b);
extern lean_object* initialize_VelvetFFI(uint8_t builtin, lean_object* w);
extern void lean_initialize_runtime_module(void);

int main(void) {
  lean_initialize_runtime_module();
  lean_object* res = initialize_VelvetFFI(1, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); return 1; }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();

  printf("velvet_maximum(3, 7)   = %lu\n", (unsigned long)velvet_maximum(3, 7));
  printf("velvet_maximum(42, 17) = %lu\n", (unsigned long)velvet_maximum(42, 17));
  return 0;
}
