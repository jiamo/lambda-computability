/* Exact test for single good automata Y on 8 points (not Lean-verified).
   Reads candidate automata "a b c" (image strings, from filter8) on stdin.  For each, computes
   Im = image in G (|G| = 128, the group of the target automaton of shcount (0,0) mod 2) of the
   words that loop at the start of Y and of the counters scount acc, scount bac, scount ccc mod 2
   (these alone give Im = {1, z}), optionally with the parities of the letters fixing 0 read at 0
   in Y (BASE=1).  Prints the automata with z not in Im (then shcount (0,0) mod 2 is a function of
   the counters and Y).  Usage: ./imtest8 BASE < survivors8.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { unsigned char p[8]; } perm;
static perm Gel[128]; static int ng = 0; static int mt[128][128];
static perm T[3];
static perm pmul(perm x, perm y) { perm r; for (int i = 0; i < 8; i++) r.p[i] = y.p[x.p[i]]; return r; }
static int gidx(perm x) { for (int i = 0; i < ng; i++) if (!memcmp(Gel[i].p, x.p, 8)) return i; return -1; }
static int letter_g[3];
/* counters: words acc, bac, ccc; letters a=0 b=1 c=2 */
static const int cw[3][3] = {{0, 2, 2}, {1, 0, 2}, {2, 2, 2}};
static int cstep(int s, int x) {
  int r = s;
  for (int w = 0; w < 3; w++) {
    int bits = (s >> (3 * w)) & 7, nb = bits;
    for (int j = 2; j >= 0; j--) if (cw[w][j] == x) {
      int prev = j == 0 ? 1 : (bits >> (j - 1)) & 1;
      nb ^= prev << j;
    }
    r = (r & ~(7 << (3 * w))) | (nb << (3 * w));
  }
  return r;
}
int main(int argc, char **argv) {
  int base = argc > 1 ? atoi(argv[1]) : 0;
  /* target automaton: points (A, l, k) -> A*4 + l*2 + k */
  for (int x = 0; x < 3; x++) for (int A = 0; A < 2; A++) for (int l = 0; l < 2; l++) for (int k = 0; k < 2; k++) {
    int A2 = A, l2 = l, k2 = k;
    if (x == 0) A2 = A ^ 1; if (x == 2) l2 = l ^ A; if (x == 1 && A == 0 && l == 0) k2 = k ^ 1;
    T[x].p[A * 4 + l * 2 + k] = A2 * 4 + l2 * 2 + k2;
  }
  perm e; for (int i = 0; i < 8; i++) e.p[i] = i;
  Gel[ng++] = e;
  for (int i = 0; i < ng; i++) for (int x = 0; x < 3; x++) { perm y = pmul(Gel[i], T[x]); if (gidx(y) < 0) Gel[ng++] = y; }
  for (int i = 0; i < ng; i++) for (int j = 0; j < ng; j++) mt[i][j] = gidx(pmul(Gel[i], Gel[j]));
  int inv[128]; for (int i = 0; i < ng; i++) for (int j = 0; j < ng; j++) if (mt[i][j] == 0) inv[i] = j;
  for (int x = 0; x < 3; x++) letter_g[x] = gidx(T[x]);
  perm zp = {{1, 0, 3, 2, 5, 4, 7, 6}}; int z = gidx(zp);
  fprintf(stderr, "|G| = %d, z index %d\n", ng, z);
  static int rep[1 << 16]; static int queue[1 << 16];
  char sa[16], sb[16], sc[16]; long cnt = 0, hits = 0;
  while (scanf("%15s %15s %15s", sa, sb, sc) == 3) {
    int Y[3][8];
    for (int i = 0; i < 8; i++) { Y[0][i] = sa[i] - '0'; Y[1][i] = sb[i] - '0'; Y[2][i] = sc[i] - '0'; }
    cnt++;
    memset(rep, -1, sizeof(rep));
    unsigned char sub[128]; memset(sub, 0, 128); sub[0] = 1; int subl[128], ns = 1; subl[0] = 0;
    int qh = 0, qt = 0; rep[0] = 0; queue[qt++] = 0; int found = 0;
    while (qh < qt && !found) {
      int s = queue[qh++]; int g = rep[s];
      int cs = s & 511, ys = (s >> 9) & 7, kb = s >> 12;
      for (int x = 0; x < 3 && !found; x++) {
        int nk = kb; if (base && ys == 0 && Y[x][0] == 0) nk ^= 1 << x;
        int t = cstep(cs, x) | (Y[x][ys] << 9) | (nk << 12);
        int gx = mt[g][letter_g[x]];
        if (rep[t] >= 0) {
          int sg = mt[gx][inv[rep[t]]];
          if (!sub[sg]) { /* add to subgroup and close */
            sub[sg] = 1; subl[ns++] = sg;
            for (int i = 0; i < ns; i++) for (int j = 0; j < ns; j++) {
              int h = mt[subl[i]][subl[j]]; if (!sub[h]) { sub[h] = 1; subl[ns++] = h; }
            }
            if (sub[z]) found = 1;
          }
        } else { rep[t] = gx; queue[qt++] = t; }
      }
    }
    if (!found) { hits++; printf("%s %s %s |Im| = %d\n", sa, sb, sc, ns); fflush(stdout); }
  }
  fprintf(stderr, "tested %ld, z not in Im for %ld\n", cnt, hits);
  return 0;
}
