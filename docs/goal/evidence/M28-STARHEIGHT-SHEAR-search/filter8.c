/* Necessary-condition filter for a good automaton Y on 8 points (not Lean-verified).
   Letters a, b, c: the identity or one cycle through 0 of length 2, 4 or 8; a in canonical form.
   Keeps Y if it is transitive and each of the words abc, bac, abaca, acaba (whose images in G
   have order 8, with fourth power the central z) acts as an 8-cycle.  With the mod-2 counters
   (exponent 4) this is necessary for z not in Im (see central_bit.py / NOTES).
   Output: one line per survivor, "a b c" as image strings.  Usage: ./filter8 [NO8 [A]] > survivors8.txt; NO8 = 1 skips the 8-cycle condition (needed when
   the base-point counts are added), A in 0..3 restricts the canonical form of a. */
#include <stdio.h>
#include <string.h>
#define N 8
typedef struct { unsigned char p[N]; } perm;
static perm L[6000]; static int nl = 0;
static void mk(const int *cyc, int len) {
  perm q; for (int i = 0; i < N; i++) q.p[i] = i;
  for (int i = 0; i < len; i++) q.p[cyc[i]] = cyc[(i + 1) % len];
  L[nl++] = q;
}
static int used[N], cyc[N];
static void gen(int depth, int len) {
  if (depth == len) { mk(cyc, len); return; }
  for (int v = 1; v < N; v++) if (!used[v]) { used[v] = 1; cyc[depth] = v; gen(depth + 1, len); used[v] = 0; }
}
static perm mul(perm x, perm y) { perm r; for (int i = 0; i < N; i++) r.p[i] = y.p[x.p[i]]; return r; }
static int is8cycle(perm x) { int s = 0, k = 0; do { s = x.p[s]; k++; } while (s != 0 && k <= N); return k == N; }
static int transitive(perm a, perm b, perm c) {
  int seen = 1, todo[N], nt = 1; todo[0] = 0;
  while (nt) { int s = todo[--nt]; perm *ls[3] = {&a, &b, &c};
    for (int j = 0; j < 3; j++) { int t = ls[j]->p[s]; if (!(seen >> t & 1)) { seen |= 1 << t; todo[nt++] = t; } } }
  return seen == (1 << N) - 1;
}
/* dying automaton: states 0..7 = running, 8 = just returned, 9 = dead; start 0 */
static int dstep(int s, const perm *x) {
  if (s >= 8) return 9;
  int t = x->p[s]; return t == 0 ? 8 : t;
}
/* necessary condition for aperiodicity: w^(N+2) = w^(N+1) on every state, for words of length <= 4 */
static int short_aperiodic(perm a, perm b, perm c) {
  const perm *ls[3] = {&a, &b, &c};
  int w[4];
  for (int len = 1; len <= 4; len++) {
    int tot = 1; for (int i = 0; i < len; i++) tot *= 3;
    for (int code = 0; code < tot; code++) {
      int cc = code; for (int i = 0; i < len; i++) { w[i] = cc % 3; cc /= 3; }
      for (int s0 = 0; s0 < 10; s0++) {
        int s = s0, p1 = -1;
        for (int k = 0; k < N + 3; k++) {
          if (k == N + 2) p1 = s;
          for (int i = 0; i < len; i++) s = dstep(s, ls[w[i]]);
        }
        /* s = w^(N+3)(s0), p1 = w^(N+2)(s0) */
        if (s != p1) return 0;
      }
    }
  }
  return 1;
}
int main(int argc, char **argv) {
  int no8 = argc > 1 && argv[1][0] == '1';
  int only_a = argc > 2 ? argv[2][0] - '0' : -1;
  perm id; for (int i = 0; i < N; i++) id.p[i] = i; L[nl++] = id;
  cyc[0] = 0; used[0] = 1;
  int lens[3] = {2, 4, 8};
  for (int k = 0; k < 3; k++) gen(1, lens[k]);
  fprintf(stderr, "%d letters\n", nl);
  int acan[4][N]; int na = 0;
  int Ls[4] = {1, 2, 4, 8};
  for (int k = 0; k < 4; k++) { for (int i = 0; i < N; i++) acan[k][i] = i;
    if (Ls[k] > 1) for (int i = 0; i < Ls[k]; i++) acan[k][i] = (i + 1) % Ls[k]; na++; }
  long cnt = 0, surv = 0;
  for (int k = 0; k < na; k++) {
    if (only_a >= 0 && k != only_a) continue;
    perm a; for (int i = 0; i < N; i++) a.p[i] = acan[k][i];
    for (int ib = 0; ib < nl; ib++) {
      perm b = L[ib]; perm ab = mul(a, b), ba = mul(b, a);
      for (int ic = 0; ic < nl; ic++) {
        perm c = L[ic]; cnt++;
        perm ac = mul(a, c);
        if (!no8) {
          if (!is8cycle(mul(ab, c))) continue;
          if (!is8cycle(mul(ba, c))) continue;
          if (!is8cycle(mul(mul(ab, ac), a))) continue;   /* abaca */
          if (!is8cycle(mul(mul(ac, ab), a))) continue;   /* acaba */
        }
        if (!transitive(a, b, c)) continue;
        if (!short_aperiodic(a, b, c)) continue;
        surv++;
        for (int i = 0; i < N; i++) printf("%d", a.p[i]); printf(" ");
        for (int i = 0; i < N; i++) printf("%d", b.p[i]); printf(" ");
        for (int i = 0; i < N; i++) printf("%d", c.p[i]); printf("\n");
      }
    }
  }
  fprintf(stderr, "checked %ld, survivors %ld\n", cnt, surv);
  return 0;
}
