/* Exact test, single automaton Y on n <= 9 points plus counters of order 8 (not Lean-verified).
   Counters: |u|_a, |u|_b, |u|_c mod 8 and scount acc, bac, ccc mod 2.  With counts mod 8 the order
   obstruction ((abc)^4 is a loop of every component) no longer applies to automata on < 8 points.
   Input lines: "n a b c" (image strings).  Output: the automata with z not in Im (then
   shcount (0,0) mod 2 is a function of Y and the counters).  Usage: ./imtest_gen < automata.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { unsigned char p[8]; } perm;
static perm Gel[128]; static int ng = 0; static int mt[128][128], inv_[128], letter_g[3];
static perm T[3];
static perm pmul(perm x, perm y) { perm r; for (int i = 0; i < 8; i++) r.p[i] = y.p[x.p[i]]; return r; }
static int gidx(perm x) { for (int i = 0; i < ng; i++) if (!memcmp(Gel[i].p, x.p, 8)) return i; return -1; }
static const int cw[3][3] = {{0, 2, 2}, {1, 0, 2}, {2, 2, 2}};
static int cstep(int s, int x) {
  int r = s;
  for (int w = 0; w < 3; w++) {
    int bits = (s >> (3 * w)) & 7, nb = bits;
    for (int j = 2; j >= 0; j--) if (cw[w][j] == x) { int prev = j == 0 ? 1 : (bits >> (j - 1)) & 1; nb ^= prev << j; }
    r = (r & ~(7 << (3 * w))) | (nb << (3 * w));
  }
  return r;
}
#define SZ (1 << 22)
static int stamp[SZ], rep[SZ], queue_[SZ];
int main(void) {
  for (int x = 0; x < 3; x++) for (int A = 0; A < 2; A++) for (int l = 0; l < 2; l++) for (int k = 0; k < 2; k++) {
    int A2 = A, l2 = l, k2 = k;
    if (x == 0) A2 = A ^ 1; if (x == 2) l2 = l ^ A; if (x == 1 && A == 0 && l == 0) k2 = k ^ 1;
    T[x].p[A * 4 + l * 2 + k] = A2 * 4 + l2 * 2 + k2;
  }
  perm e; for (int i = 0; i < 8; i++) e.p[i] = i;
  Gel[ng++] = e;
  for (int i = 0; i < ng; i++) for (int x = 0; x < 3; x++) { perm y = pmul(Gel[i], T[x]); if (gidx(y) < 0) Gel[ng++] = y; }
  for (int i = 0; i < ng; i++) for (int j = 0; j < ng; j++) mt[i][j] = gidx(pmul(Gel[i], Gel[j]));
  for (int i = 0; i < ng; i++) for (int j = 0; j < ng; j++) if (mt[i][j] == 0) inv_[i] = j;
  for (int x = 0; x < 3; x++) letter_g[x] = gidx(T[x]);
  perm zp = {{1, 0, 3, 2, 5, 4, 7, 6}}; int z = gidx(zp);
  int n; char sa[16], sb[16], sc[16]; long cnt = 0, hits = 0; int id = 0;
  while (scanf("%d %15s %15s %15s", &n, sa, sb, sc) == 4) {
    int Y[3][16];
    for (int i = 0; i < n; i++) { Y[0][i] = sa[i] - '0'; Y[1][i] = sb[i] - '0'; Y[2][i] = sc[i] - '0'; }
    cnt++; id++;
    unsigned char sub[128]; memset(sub, 0, 128); sub[0] = 1; int subl[128], ns = 1; subl[0] = 0;
    int qh = 0, qt = 0; stamp[0] = id; rep[0] = 0; queue_[qt++] = 0; int found = 0;
    while (qh < qt && !found) {
      int s = queue_[qh++]; int g = rep[s];
      int ys = s & 15, cn = (s >> 4) & 511, ws = s >> 13;
      for (int x = 0; x < 3 && !found; x++) {
        int c0 = cn & 7, c1 = (cn >> 3) & 7, c2 = cn >> 6;
        if (x == 0) c0 = (c0 + 1) & 7; if (x == 1) c1 = (c1 + 1) & 7; if (x == 2) c2 = (c2 + 1) & 7;
        int t = Y[x][ys] | ((c0 | (c1 << 3) | (c2 << 6)) << 4) | (cstep(ws, x) << 13);
        int gx = mt[g][letter_g[x]];
        if (stamp[t] == id) {
          int sg = mt[gx][inv_[rep[t]]];
          if (!sub[sg]) {
            sub[sg] = 1; subl[ns++] = sg;
            for (int i = 0; i < ns; i++) for (int j = 0; j < ns; j++) { int h = mt[subl[i]][subl[j]]; if (!sub[h]) { sub[h] = 1; subl[ns++] = h; } }
            if (sub[z]) found = 1;
          }
        } else { stamp[t] = id; rep[t] = gx; queue_[qt++] = t; }
      }
    }
    if (!found) { hits++; printf("%d %s %s %s |Im| = %d\n", n, sa, sb, sc, ns); fflush(stdout); }
  }
  fprintf(stderr, "tested %ld, z not in Im for %ld\n", cnt, hits);
  return 0;
}
