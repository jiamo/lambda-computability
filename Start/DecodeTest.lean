import Start.Encoding
import Start.Undecidable

set_option maxRecDepth 4000

noncomputable section

theorem Lambda.decode_eq (n : ℕ) :
    Lambda.decode n =
      (match h : n.unpair with
       | (0, m) => some (Lambda.var m)
       | (1, m) =>
         match hm : m.unpair with
         | (c₁, c₂) =>
           match Lambda.decode c₁, Lambda.decode c₂ with
           | some t₁, some t₂ => some (Lambda.app t₁ t₂)
           | _, _ => none
       | (2, m) =>
         match Lambda.decode m with
         | some t => some (Lambda.lam t)
         | _ => none
       | _ => none) := by
  conv_lhs => rw [Lambda.decode, Nat.strongRecOn_eq]
  congr! 2

theorem Lambda.encode_of_decode : ∀ (c : ℕ) (t : Lambda),
    Lambda.decode c = some t → Lambda.encode t = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      intro t ht
      rw [Lambda.decode_eq] at ht
      split at ht
      · next m hu =>
          have : t = Lambda.var m := by simpa using ht.symm
          subst this
          rw [Lambda.encode, ← Nat.pair_unpair c, hu]
      · next m hu =>
          split at ht
          next c₁ c₂ hm =>
            have h1 : c₁ < c := Lambda.decode_lt_1 hu hm
            have h2 : c₂ < c := Lambda.decode_lt_2 hu hm
            rcases hd1 : Lambda.decode c₁ with _ | t₁ <;>
              rcases hd2 : Lambda.decode c₂ with _ | t₂ <;>
              rw [hd1, hd2] at ht <;> simp at ht
            subst ht
            have hm' : Nat.pair c₁ c₂ = m := by rw [← Nat.pair_unpair m, hm]
            have hu' : Nat.pair 1 m = c := by rw [← Nat.pair_unpair c, hu]
            rw [Lambda.encode, ih c₁ h1 t₁ hd1, ih c₂ h2 t₂ hd2, hm', hu']
      · next m hu =>
          have h1 : m < c := Lambda.decode_lt_3 hu
          rcases hd : Lambda.decode m with _ | u <;> rw [hd] at ht <;> simp at ht
          subst ht
          rw [Lambda.encode, ih m h1 u hd, ← Nat.pair_unpair c, hu]
      · simp at ht

end
