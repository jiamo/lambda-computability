/*
 * Tests of the offline space-bounded machine module
 * (include/ct/spacemachine.h).  Expected values are computed by hand from
 * `writeAt`, `moveWork`, `moveIn`, `Config.space`, `Machine.stepList`,
 * `init` and `constMachine` (the Lean development, `Start/`), and from the lemmas
 * `writeAt_length` and `writeAt_getD` of Start/SpaceMachine.lean.
 */
#include <stdio.h>

#include "ct/spacemachine.h"

static int failures = 0;

#define CHECK(cond)                                                     \
  do {                                                                  \
    if (!(cond)) {                                                      \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, \
              #cond);                                                   \
      failures++;                                                       \
    }                                                                   \
  } while (0)

static void test_tape(void) {
  bool bits[8];
  uint64_t len = 0;
  uint64_t v = 0;
  /* writeAt [] 2 true = [false, false, true] */
  CHECK(ct_sp_write_at(bits, &len, 8, 2, true) == CT_OK && len == 3 &&
        !bits[0] && !bits[1] && bits[2]);
  /* writeAt [f, f, t] 0 true = [t, f, t] */
  CHECK(ct_sp_write_at(bits, &len, 8, 0, true) == CT_OK && len == 3 &&
        bits[0] && !bits[1] && bits[2]);
  /* length (writeAt l 5 b) = max 3 6 = 6 */
  CHECK(ct_sp_write_at(bits, &len, 8, 5, false) == CT_OK && len == 6 &&
        !bits[3] && !bits[4] && !bits[5]);
  CHECK(ct_sp_write_at(bits, &len, 8, 8, true) == CT_ELIMIT && len == 6);
  CHECK(ct_sp_move_work(0, CT_SP_LEFT, &v) == CT_OK && v == 0);
  CHECK(ct_sp_move_work(4, CT_SP_LEFT, &v) == CT_OK && v == 3);
  CHECK(ct_sp_move_work(4, CT_SP_RIGHT, &v) == CT_OK && v == 5);
  CHECK(ct_sp_move_work(4, CT_SP_STAY, &v) == CT_OK && v == 4);
  CHECK(ct_sp_move_in(3, 3, CT_SP_RIGHT, &v) == CT_OK && v == 3);
  CHECK(ct_sp_move_in(3, 2, CT_SP_RIGHT, &v) == CT_OK && v == 3);
  CHECK(ct_sp_move_in(3, 0, CT_SP_LEFT, &v) == CT_OK && v == 0);
  CHECK(ct_sp_move_work(UINT64_MAX, CT_SP_RIGHT, &v) == CT_EOVERFLOW);
}

static void test_step(void) {
  ct_sp_instr instrs[2] = {{1, true, CT_SP_RIGHT, CT_SP_RIGHT},
                           {0, false, CT_SP_STAY, CT_SP_LEFT}};
  ct_sp_entry entries[12];
  bool accept[2] = {false, true};
  ct_sp_machine m = {2, accept, entries, instrs, 2};
  bool x[1] = {true};
  bool tape0[4];
  bool b0[4];
  bool b1[4];
  bool *bufs[2];
  ct_sp_config c;
  ct_sp_config out[2];
  uint64_t count = 9;
  uint64_t v = 0;
  bool acc = true;
  int k;
  for (k = 0; k < 12; k++) {
    entries[k].start = 0;
    entries[k].count = 0;
  }
  /* delta 0 (some true) false = both instructions */
  entries[0 * 6 + 2 * 2 + 0].count = 2;
  bufs[0] = b0;
  bufs[1] = b1;
  CHECK(ct_sp_init(tape0, 4, &c) == CT_OK);
  CHECK(c.state == 0 && c.in_head == 0 && c.tape_len == 0 && c.w_head == 0);
  CHECK(ct_sp_config_space(&c, &v) == CT_OK && v == 1);
  CHECK(ct_sp_step_list(&m, x, 1, &c, out, 2, bufs, 4, &count) == CT_OK);
  CHECK(count == 2);
  /* ⟨1, min 1 1, [true], 1⟩ and ⟨0, 0, [false], 0⟩ */
  CHECK(out[0].state == 1 && out[0].in_head == 1 && out[0].tape_len == 1 &&
        out[0].tape[0] && out[0].w_head == 1);
  CHECK(out[1].state == 0 && out[1].in_head == 0 && out[1].tape_len == 1 &&
        !out[1].tape[0] && out[1].w_head == 0);
  CHECK(ct_sp_config_space(&out[0], &v) == CT_OK && v == 2);
  /* the input head reads the end marker in state 1: no instruction */
  CHECK(ct_sp_step_list(&m, x, 1, &out[0], out, 2, bufs, 4, &count) ==
            CT_OK &&
        count == 0);
  /* a state outside the table has no instruction */
  c.state = 7;
  CHECK(ct_sp_step_list(&m, x, 1, &c, out, 2, bufs, 4, &count) == CT_OK &&
        count == 0);
  c.state = 0;
  CHECK(ct_sp_step_list(&m, x, 1, &c, out, 1, bufs, 4, &count) == CT_ELIMIT);
  CHECK(ct_sp_accept(&m, 1, &acc) == CT_OK && acc);
  CHECK(ct_sp_accept(&m, 9, &acc) == CT_OK && !acc);
}

static void test_const(void) {
  bool accept[1];
  ct_sp_entry entries[6];
  ct_sp_machine m;
  bool tape0[2];
  bool buf[2];
  bool *bufs[1];
  ct_sp_config c;
  ct_sp_config out[1];
  uint64_t count = 9;
  bool acc = false;
  bool x[2] = {false, true};
  bufs[0] = buf;
  CHECK(ct_sp_const_machine(true, accept, entries, &m) == CT_OK);
  CHECK(m.states == 1 && ct_sp_accept(&m, 0, &acc) == CT_OK && acc);
  CHECK(ct_sp_init(tape0, 2, &c) == CT_OK);
  CHECK(ct_sp_step_list(&m, x, 2, &c, out, 1, bufs, 2, &count) == CT_OK &&
        count == 0);
}

int main(void) {
  test_tape();
  test_step();
  test_const();
  if (failures != 0) {
    fprintf(stderr, "test_spacemachine: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_spacemachine: all checks passed\n");
  return 0;
}
