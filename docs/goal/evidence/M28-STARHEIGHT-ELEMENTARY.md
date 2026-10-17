# M28-STARHEIGHT-ELEMENTARY-QUOTIENT, M28-STARHEIGHT-HCORE-REDUCTION, M28-STARHEIGHT-ORDER-LT-24

All theorems below are proved in Lean with no `sorry`, no `native_decide`, no `Lean.ofReduceBool`
and no new axioms. Their `#print axioms` output is in
`docs/goal/evidence/M28-STARHEIGHT-ELEMENTARY-axioms.txt`: only `propext`, `Classical.choice` and
`Quot.sound`. The PST candidate is in `M28-STARHEIGHT-PST-CANDIDATE.md`.

## Elementary abelian quotient, every prime (`Start/StarHeightElementary.lean`)

```lean
theorem vcount_height_one_prime {α : Type u} [Finite α] [DecidableEq α] {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (δ : α → V) (q : V) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1
theorem height_one_of_abelian_normal_exponent_prime [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) {p : ℕ} [Fact p.Prime] (hexp : ∀ x : G, x ^ p ∈ N)
    (T : FreeMonoid Alphabet →* G) (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

- Character identity (`charSum_vcount`), with `D` the dual of `V` and `|D| = p·c`:
  `Σ_{φ ∈ D} vcount (φ ∘ δ) (φ q) x w = c·|w|ₓ + (p − 1)·c·vcount δ q x w`.
  For `v ≠ 0` exactly `c` characters vanish at `v` (`card_dual_ker_prime`).
- Each `vcount (φ ∘ δ) (φ q) x` is a `ZMod p` count at the state `φ q`: `vcount_zp_height`
  (from `zpcore`, every state reached through a fresh first letter).
- Corollaries:
  - `height_one_of_abelian_normal_exponent_three_of_prime` (Bourne's `p = 3`). The old
    `height_one_of_abelian_normal_exponent_three` is unchanged.
  - `height_one_of_abelian_normal_exponent_two` (PST's `Gcom ∗ (Z/2)ʳ`). It needs no commutator
    hypothesis, since a quotient of exponent `2` is abelian.
  - `height_one_G3025` for `G3025 = (Z₁₁ × Z₁₁) ⋊ (Z₅ × Z₅)`, where `(i, j)` acts by
    `diag(3^i, 3^j)`.
    - It has no abelian normal subgroup of prime index. Such a subgroup would contain
      `Z₁₁²`, so it is `Z₁₁² ⋊ C` with `C` a line of `(Z₅)²`, and a nonzero element of `C` acts
      nontrivially on `Z₁₁²`.
    - This remark is a comment in the file and is not formalized.

## The `H`-core and the reduction (`Start/StarHeightHCore.lean`, `Start/StarHeightS4.lean`)

```lean
def HCoreHeightOne (H : Type) [Group H] : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (ρ : α → H) (x : α) (g : H) (n k : ℕ),
  k < n → HasHeightAtMost {w : List α | hcount ρ g x w % n = k} 1
theorem height_one_of_abelian_normal_of_core [Finite Alphabet] {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hcore : HCoreHeightOne (G ⧸ N)) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
theorem height_one_S4_of_core (hcore : HCoreHeightOne (Equiv.Perm (Fin 3))) {Alphabet : Type u}
    [Finite Alphabet] (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 4)) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

- `hcount ρ g x w` is the number of positions `i` such that `w[i] = x` and
  `((w.take i).map ρ).prod = g`.
- The reduction is the wreath product principle, as in `IndexPrime`:
  - the telescoping writes `T w` through the pair counts (state in `G ⧸ N`, letter) modulo `|N|`;
  - the final state `ψ w` comes from the same counts modulo `2`, by the flow identity
    `Σₓ #enter(q, x) + [q = 1] = Σₓ #leave(q, x) + [ψ w = q]` (`flow_identity`);
  - so nothing beyond the core is assumed of `G ⧸ N`, not even that its own languages have
    height one.
- `height_one_of_abelian_normal_of_core_equiv` is the same statement for an isomorphism
  `G ⧸ N ≃* H`. The core property is invariant under isomorphism (`HCoreHeightOne.of_mulEquiv`).
- Bridges:
  - `hcount_ofAdd_eq_vcount`, and `hcore_zmod_four_iff : HCoreHeightOne (Multiplicative (ZMod 4)) ↔ Z4CoreHeightOne`.
    `Z4CoreHeightOne` is thus an instance of the `H`-core, and conversely, every state being
    reached by a fresh letter.
  - `hcore_zmod_prime p : HCoreHeightOne (Multiplicative (ZMod p))`, proved for every prime.
- `S₄`:
  - `S4Klein.kleinHom : Perm (Fin 4) →* Perm (Fin 3)` is the action on the three pairings.
  - Its kernel is `V₄ = {x ↦ x xor a}`, which is abelian (`ker_comm`). The map is surjective
    (`decomposeFin`).
  - The finite checks are `decide` on `Fin 4`-valued tuples (4096 cases at most), never on
    `Perm (Fin 4)`.
- `SL(2,3)` over the `A₄`-core was skipped: it would need an explicit `SL(2,3) ⧸ Z ≃* A₄`.

## Groups of order `< 24` (`Start/GroupOrderLtTwentyFour.lean`, `Start/StarHeightOrderLtTwentyFour.lean`)

```lean
theorem height_one_of_card_lt_twentyfour_of_centralizer [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (hG : Fintype.card G < 24)
    (hC : Fintype.card G = 20 → ∀ P : Sylow 5 G, 5 < Nat.card (Subgroup.centralizer (P : Set G)))
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1
```

- As the request allowed, `hF : IsEmpty (G ≃* F20)` is replaced by the centralizer hypothesis.
  The groups it excludes act faithfully on their Sylow `5`-subgroup, i.e. they are `F₂₀`. That
  characterization is not formalized.
- Each case gives an abelian normal subgroup of index `≤ 3`:
  - `< 20`: the existing theorem;
  - `21`: the Sylow `7`-subgroup is normal (`n₇ ∣ 3`);
  - `22`: a subgroup of order `11` has index `2`;
  - `23`: `G` is cyclic;
  - `20`: the Sylow `5`-subgroup `P` is normal and `P ≤ C(P)`:
    - if `|C(P)| = 10`, `C(P)` is abelian (central subgroup of index `2`) and has index `2`;
    - if `|C(P)| = 20`, `P` is central, so `|G| ≤ 4·|Z(G)|`.

## Resources

Max RSS of `lake env lean <module>`, measured with `getrusage`. The `import Mathlib` baseline is 7877 MiB.
- `StarHeightS4`: +331 MiB. This is the largest; its kernel `decide`s run over `Fin 4`-valued tuples.
- Every other new module: +41 to +126 MiB.
