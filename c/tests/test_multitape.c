/*
 * Tests of the multi-tape machine module (include/ct/multitape.h).  Expected
 * values are computed by hand from `Literal.eval`, `GateInput.eval`,
 * `Circuit3.gateCount`, `HeadMove.apply`, `multiTapeStep`,
 * `FiniteMultiTapeMachine.init` and `runSteps` (the Lean development, `Start/`).
 */
#include <stdio.h>

#include "ct/multitape.h"

static int failures = 0;

#define CHECK(cond)                                                     \
  do {                                                                  \
    if (!(cond)) {                                                      \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, \
              #cond);                                                   \
      failures++;                                                       \
    }                                                                   \
  } while (0)

static void test_gates(void) {
  bool x[3] = {true, false, true};
  bool r = false;
  uint64_t n = 0;
  ct_mt_gate_input g;
  CHECK(ct_mt_literal_eval(0, true, x, 3, &r) == CT_OK && r);
  CHECK(ct_mt_literal_eval(1, true, x, 3, &r) == CT_OK && !r);
  CHECK(ct_mt_literal_eval(1, false, x, 3, &r) == CT_OK && r);
  CHECK(ct_mt_literal_eval(3, false, x, 3, &r) == CT_EINVAL);
  g.is_literal = false;
  g.var = 99;
  g.val = true;
  CHECK(ct_mt_gate_input_eval(&g, x, 3, &r) == CT_OK && r);
  g.is_literal = true;
  g.var = 2;
  g.val = false;
  CHECK(ct_mt_gate_input_eval(&g, x, 3, &r) == CT_OK && !r);
  CHECK(ct_mt_gate_count(4, 5, &n) == CT_OK && n == 10);
  CHECK(ct_mt_gate_count(UINT64_MAX, 0, &n) == CT_EOVERFLOW);
}

/* One tape, alphabet {blank, 0, 1} = {0, 1, 2}: scan right over the input,
   halt on the first blank. */
static void test_scanner(void) {
  ct_mt_entry code[3];
  bool accept[1] = {true};
  ct_mt_machine m;
  ct_mt_cfg c;
  uint32_t buf[6];
  uint32_t *bufs[1];
  bool input[3] = {true, false, true};
  bool none = true;
  bool halted = true;
  int s;
  for (s = 0; s < 3; s++) {
    code[s].defined = (s != 0);
    code[s].q = 0;
    code[s].writes[0] = (uint32_t)s;
    code[s].moves[0] = CT_MT_RIGHT;
  }
  m.nk = 1;
  m.ng = 3;
  m.nq = 1;
  m.input_tape = 0;
  m.initial_state = 0;
  m.input_symbol[0] = 1;
  m.input_symbol[1] = 2;
  m.code = code;
  m.accept = accept;
  bufs[0] = buf;
  CHECK(ct_mt_init(&m, input, 3, bufs, 6, 0, &c) == CT_OK);
  /* init: the tape `mk₁ [2, 1, 2]` */
  CHECK(c.q == 0 && c.tapes[0].pos == 0 && buf[0] == 2 && buf[1] == 1 &&
        buf[2] == 2 && buf[3] == 0 && buf[5] == 0);
  CHECK(ct_mt_run_steps(&m, &c, 3, &none) == CT_OK && !none);
  CHECK(c.tapes[0].pos == 3);
  /* the fourth step reads a blank: `step = none` */
  CHECK(ct_mt_step(&m, &c, &halted) == CT_OK && halted);
  CHECK(c.tapes[0].pos == 3);
  /* runSteps 4 from the start is none */
  CHECK(ct_mt_init(&m, input, 3, bufs, 6, 0, &c) == CT_OK);
  CHECK(ct_mt_run_steps(&m, &c, 4, &none) == CT_OK && none);
  /* runSteps 0 c = some c */
  CHECK(ct_mt_run_steps(&m, &c, 0, &none) == CT_OK && !none);
  /* the window is too short for the input */
  CHECK(ct_mt_init(&m, input, 3, bufs, 2, 0, &c) == CT_ELIMIT);
}

/* Two tapes: copy the input tape onto tape 1, then halt. */
static void test_copier(void) {
  ct_mt_entry code[9];
  bool accept[1] = {false};
  ct_mt_machine m;
  ct_mt_cfg c;
  uint32_t b0[8];
  uint32_t b1[8];
  uint32_t *bufs[2];
  bool input[4] = {false, true, true, false};
  bool none = false;
  int r0;
  int r1;
  for (r1 = 0; r1 < 3; r1++) {
    for (r0 = 0; r0 < 3; r0++) {
      ct_mt_entry *e = &code[r0 + 3 * r1];
      e->defined = (r0 != 0);
      e->q = 0;
      e->writes[0] = (uint32_t)r0;
      e->writes[1] = (uint32_t)r0;
      e->moves[0] = CT_MT_RIGHT;
      e->moves[1] = CT_MT_RIGHT;
    }
  }
  m.nk = 2;
  m.ng = 3;
  m.nq = 1;
  m.input_tape = 0;
  m.initial_state = 0;
  m.input_symbol[0] = 1;
  m.input_symbol[1] = 2;
  m.code = code;
  m.accept = accept;
  bufs[0] = b0;
  bufs[1] = b1;
  CHECK(ct_mt_init(&m, input, 4, bufs, 8, 1, &c) == CT_OK);
  CHECK(ct_mt_run_steps(&m, &c, 10, &none) == CT_OK && none);
  CHECK(c.tapes[0].pos == 5 && c.tapes[1].pos == 5);
  CHECK(b1[0] == 0 && b1[1] == 1 && b1[2] == 2 && b1[3] == 2 && b1[4] == 1 &&
        b1[5] == 0);
  /* moving left twice from the origin 1 leaves the window */
  CHECK(ct_mt_init(&m, input, 4, bufs, 8, 1, &c) == CT_OK);
  CHECK(ct_mt_headmove_apply(CT_MT_LEFT, &c.tapes[0]) == CT_OK &&
        c.tapes[0].pos == 0);
  CHECK(ct_mt_headmove_apply(CT_MT_LEFT, &c.tapes[0]) == CT_ELIMIT &&
        c.tapes[0].pos == 0);
  CHECK(ct_mt_headmove_apply(CT_MT_STAY, &c.tapes[0]) == CT_OK &&
        c.tapes[0].pos == 0);
}

int main(void) {
  test_gates();
  test_scanner();
  test_copier();
  if (failures != 0) {
    fprintf(stderr, "test_multitape: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_multitape: all checks passed\n");
  return 0;
}
