/-
The s-m-n theorem for the lambda calculus, in uniform (coded) form.

Fixing a parameter of a lambda term is just applying it to a Church numeral, and on codes that
operation is primitive recursive.  `Lambda.exists_smn` packages this as the usual statement: there
is a primitive recursive `s` such that the code `s c n` denotes the term coded by `c` applied to
the numeral `n`, uniformly in both arguments.

`Lambda.smn_realizes` is the computational form: if a closed term `F` computes a binary function
`f` on Church numerals, then `s (encode F) n` is the code of a term computing `fun m => f n m`,
and this code depends primitively recursively on `n`.
-/

import Start.Undecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- The s-m-n function on codes: from the code of a term and a number, the code of the term
applied to the corresponding Church numeral. -/
def smnCode (c n : ℕ) : ℕ := Lambda.app_code c (Lambda.church_code n)

theorem smnCode_primrec : Primrec₂ smnCode := by
  have h : Primrec fun p : ℕ × ℕ => Lambda.app_code p.1 (Lambda.church_code p.2) :=
    Primrec₂.comp Lambda.app_code_primrec Primrec.fst
      (Lambda.church_code_primrec.comp Primrec.snd)
  exact h

theorem smnCode_encode (F : Lambda) (n : ℕ) :
    smnCode (Lambda.encode F) n = Lambda.encode (Lambda.app F (Lambda.church n)) := by
  rw [encode_app, smnCode, Lambda.encode_church_eq_church_code]

theorem decode_smnCode (F : Lambda) (n : ℕ) :
    Lambda.decode (smnCode (Lambda.encode F) n) = some (Lambda.app F (Lambda.church n)) := by
  rw [smnCode_encode]
  exact decode_encode _

/-- **The s-m-n theorem for the lambda calculus.**  There is a primitive recursive function `s`
which, from the code of a term and a parameter `n`, produces the code of the term with that
parameter substituted (that is, applied to `church n`). -/
theorem exists_smn :
    ∃ s : ℕ → ℕ → ℕ, Primrec₂ s ∧
      ∀ (F : Lambda) (n : ℕ),
        Lambda.decode (s (Lambda.encode F) n) = some (Lambda.app F (Lambda.church n)) :=
  ⟨smnCode, smnCode_primrec, decode_smnCode⟩

/-- The computational form of s-m-n: the terms coded by `smnCode (encode F) n` reduce exactly as
`F` applied to two numerals does. -/
theorem smn_realizes (F : Lambda) (n m : ℕ) (u : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app F (Lambda.church n)) (Lambda.church m)) u ↔
      ∃ G : Lambda, Lambda.decode (smnCode (Lambda.encode F) n) = some G ∧
        Lambda.reduces (Lambda.app G (Lambda.church m)) u := by
  constructor
  · intro h
    exact ⟨Lambda.app F (Lambda.church n), decode_smnCode F n, h⟩
  · rintro ⟨G, hG, h⟩
    rw [decode_smnCode F n] at hG
    exact (Option.some_inj.mp hG) ▸ h

end Lambda
