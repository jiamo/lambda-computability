/-
The binary lambda calculus (BLC) bit-string encoding is a bijection onto the de Bruijn terms.

`Start/ChaitinOmega.lean` introduces the classical binary lambda calculus code

* `var i   ↦  1^(i+1) 0`
* `lam t   ↦  00 ++ bits t`
* `app a b ↦  01 ++ bits a ++ bits b`

and proves it self-delimiting, hence injective and prefix free.  Injectivity says the map is
*one-to-one*; it does not by itself give a way back from bit strings to terms.  This file supplies
the missing half — an explicit **parser**

  `Lambda.blcDecode : List Bool → Option (Lambda × List Bool)`

together with the two round-trip theorems

* `Lambda.blcDecode_bits_append` : `blcDecode (bits t ++ rest) = some (t, rest)`;
* `Lambda.blcDecode_sound`       : `blcDecode bs = some (t, rest) → bs = bits t ++ rest`.

Consequently `Lambda.blcDecodeFull` inverts `bits` exactly (`Lambda.blcDecodeFull_eq_some_iff`),
so the BLC bit strings and the de Bruijn terms of this development are interchangeable
representations, and `Lambda.isBLC` decides which bit strings are BLC programs.

The same information at the level of the *numeric* code used everywhere else in the library is
recorded by `Lambda.bitsEquiv`, an explicit equivalence between `Lambda` and the subtype of
BLC-valid bit strings, and by the `Primcodable Lambda` instance, which makes the numeric coding
usable in Mathlib's `Computable`/`Primrec` API.
-/

import Start.ChaitinOmega
import Start.OmegaUncomputable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

------------------------------------------------------------------------
-- Reading a variable index
------------------------------------------------------------------------

/-- Read a (possibly empty) block of `true` bits terminated by a `false`, returning the length of
the block and the remaining bits. -/
def readOnes : List Bool → Option (ℕ × List Bool)
  | [] => none
  | Bool.false :: rest => some (0, rest)
  | Bool.true :: rest => (readOnes rest).map fun p => (p.1 + 1, p.2)

theorem readOnes_replicate (i : ℕ) (rest : List Bool) :
    readOnes (List.replicate i Bool.true ++ (Bool.false :: rest)) = some (i, rest) := by
  induction i with
  | zero => simp [readOnes]
  | succ i ih => simp [List.replicate_succ, readOnes, ih]

theorem readOnes_sound :
    ∀ (bs : List Bool) (i : ℕ) (rest : List Bool), readOnes bs = some (i, rest) →
      bs = List.replicate i Bool.true ++ (Bool.false :: rest) := by
  intro bs
  induction bs with
  | nil => intro i rest h; simp [readOnes] at h
  | cons b bs ih =>
      intro i rest h
      cases b with
      | false =>
          simp only [readOnes, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hi, hr⟩ := h
          subst hi; subst hr; simp
      | true =>
          simp only [readOnes, Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hpe⟩ := h
          obtain ⟨hi, hr⟩ := Prod.mk.injEq .. ▸ hpe
          subst hi
          subst hr
          rw [ih p.1 p.2 hp]
          simp [List.replicate_succ]

------------------------------------------------------------------------
-- The parser
------------------------------------------------------------------------

/-- The BLC parser, with an explicit fuel bound.  `decodeAux n bs` reads one code word off the
front of `bs`, provided that code word is at most `n` bits long. -/
def decodeAux : ℕ → List Bool → Option (Lambda × List Bool)
  | 0, _ => none
  | n + 1, bs =>
      match bs with
      | Bool.false :: Bool.false :: r => (decodeAux n r).map fun p => (Lambda.lam p.1, p.2)
      | Bool.false :: Bool.true :: r =>
          (decodeAux n r).bind fun p =>
            (decodeAux n p.2).map fun q => (Lambda.app p.1 q.1, q.2)
      | Bool.true :: r => (readOnes r).map fun p => (Lambda.var p.1, p.2)
      | _ => none

theorem bits_length_pos (t : Lambda) : 0 < (bits t).length := by
  cases t <;> simp [bits]

/-- **Completeness of the parser**: it reads back every code word. -/
theorem decodeAux_bits :
    ∀ (n : ℕ) (t : Lambda), (bits t).length ≤ n → ∀ rest : List Bool,
      decodeAux n (bits t ++ rest) = some (t, rest) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exact absurd ht (by have := bits_length_pos t; omega)
  | succ n ih =>
      intro t ht rest
      cases t with
      | var i =>
          simp only [bits_var, List.replicate_succ, List.cons_append, List.append_assoc,
            decodeAux, readOnes_replicate]
          simp
      | lam t =>
          have hlen : (bits t).length ≤ n := by
            simp only [bits_lam, List.length_cons] at ht; omega
          simp only [bits_lam, List.cons_append, decodeAux, ih t hlen rest]
          simp
      | app a b =>
          have hla : (bits a).length ≤ n := by
            simp only [bits_app, List.length_cons, List.length_append] at ht
            have := bits_length_pos b; omega
          have hlb : (bits b).length ≤ n := by
            simp only [bits_app, List.length_cons, List.length_append] at ht
            have := bits_length_pos a; omega
          simp only [bits_app, List.cons_append, List.append_assoc, decodeAux,
            ih a hla (bits b ++ rest)]
          simp [ih b hlb rest]

/-- **Soundness of the parser**: whatever it reads really is a code word. -/
theorem decodeAux_sound :
    ∀ (n : ℕ) (bs : List Bool) (t : Lambda) (rest : List Bool),
      decodeAux n bs = some (t, rest) → bs = bits t ++ rest := by
  intro n
  induction n with
  | zero => intro bs t rest h; simp [decodeAux] at h
  | succ n ih =>
      intro bs t rest h
      match bs with
      | [] => simp [decodeAux] at h
      | Bool.true :: r =>
          simp only [decodeAux, Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hpe⟩ := h
          rw [Prod.mk.injEq] at hpe
          obtain ⟨ht, hr⟩ := hpe
          subst ht; subst hr
          rw [readOnes_sound r p.1 p.2 hp]
          simp [bits_var, List.replicate_succ]
      | [Bool.false] => simp [decodeAux] at h
      | Bool.false :: Bool.false :: r =>
          simp only [decodeAux, Option.map_eq_some_iff] at h
          obtain ⟨p, hp, hpe⟩ := h
          rw [Prod.mk.injEq] at hpe
          obtain ⟨ht, hr⟩ := hpe
          subst ht; subst hr
          rw [ih r p.1 p.2 hp]
          simp [bits_lam]
      | Bool.false :: Bool.true :: r =>
          simp only [decodeAux, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨p, hp, q, hq, hqe⟩ := h
          rw [Prod.mk.injEq] at hqe
          obtain ⟨ht, hr⟩ := hqe
          subst ht; subst hr
          rw [ih r p.1 p.2 hp, ih p.2 q.1 q.2 hq]
          simp [bits_app]

/-- The BLC parser: read one term off the front of a bit string. -/
def blcDecode (bs : List Bool) : Option (Lambda × List Bool) := decodeAux bs.length bs

@[simp] theorem blcDecode_bits_append (t : Lambda) (rest : List Bool) :
    blcDecode (bits t ++ rest) = some (t, rest) := by
  refine decodeAux_bits _ t ?_ rest
  simp

theorem blcDecode_sound {bs : List Bool} {t : Lambda} {rest : List Bool}
    (h : blcDecode bs = some (t, rest)) : bs = bits t ++ rest :=
  decodeAux_sound _ bs t rest h

------------------------------------------------------------------------
-- Complete programs
------------------------------------------------------------------------

/-- Decode a bit string that is expected to be exactly one code word. -/
def blcDecodeFull (bs : List Bool) : Option Lambda :=
  match blcDecode bs with
  | some (t, []) => some t
  | _ => none

@[simp] theorem blcDecodeFull_bits (t : Lambda) : blcDecodeFull (bits t) = some t := by
  have h : blcDecode (bits t) = some (t, []) := by
    simpa using blcDecode_bits_append t []
  simp [blcDecodeFull, h]

theorem blcDecodeFull_sound {bs : List Bool} {t : Lambda} (h : blcDecodeFull bs = some t) :
    bs = bits t := by
  unfold blcDecodeFull at h
  match hb : blcDecode bs with
  | none => rw [hb] at h; simp at h
  | some (u, r) =>
      rw [hb] at h
      match r with
      | [] =>
          simp only [Option.some.injEq] at h
          subst h
          simpa using blcDecode_sound hb
      | _ :: _ => simp at h

/-- **The BLC coding is a bijection onto its image**: a bit string decodes to `t` exactly when it
*is* the code of `t`. -/
theorem blcDecodeFull_eq_some_iff (bs : List Bool) (t : Lambda) :
    blcDecodeFull bs = some t ↔ bs = bits t :=
  ⟨blcDecodeFull_sound, fun h => h ▸ blcDecodeFull_bits t⟩

/-- The decidable test "this bit string is a BLC program". -/
def isBLC (bs : List Bool) : Bool := (blcDecodeFull bs).isSome

theorem isBLC_iff (bs : List Bool) : isBLC bs = Bool.true ↔ ∃ t : Lambda, bits t = bs := by
  unfold isBLC
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (by simpa using h)
    exact ⟨t, (blcDecodeFull_sound ht).symm⟩
  · rintro ⟨t, rfl⟩
    simp

@[simp] theorem isBLC_bits (t : Lambda) : isBLC (bits t) = Bool.true := by
  simp [isBLC]

------------------------------------------------------------------------
-- The bit strings that are programs, as a type
------------------------------------------------------------------------

/-- **The bridge**: an explicit equivalence between the de Bruijn terms of this development and
the BLC-valid bit strings. -/
def bitsEquiv : Lambda ≃ {bs : List Bool // isBLC bs = Bool.true} where
  toFun t := ⟨bits t, isBLC_bits t⟩
  invFun bs := (blcDecodeFull bs.1).getD (Lambda.var 0)
  left_inv t := by simp
  right_inv bs := by
    obtain ⟨t, ht⟩ := (isBLC_iff bs.1).1 bs.2
    refine Subtype.ext ?_
    change bits ((blcDecodeFull bs.1).getD (Lambda.var 0)) = bs.1
    rw [← ht, blcDecodeFull_bits]
    simp

@[simp] theorem bitsEquiv_apply (t : Lambda) : (bitsEquiv t : List Bool) = bits t := rfl

------------------------------------------------------------------------
-- The numeric coding is primitive recursive
------------------------------------------------------------------------

theorem decode_eq_some_iff (c : ℕ) (t : Lambda) :
    Lambda.decode c = some t ↔ Lambda.encode t = c :=
  ⟨encode_of_decode c t, fun h => h ▸ Encodable.encodek t⟩

theorem decode_eq_none_of_not_valid {c : ℕ} (h : is_valid_code c ≠ Bool.true) :
    Lambda.decode c = none := by
  rcases hd : Lambda.decode c with _ | t
  · rfl
  · exact absurd ((is_valid_code_iff c).2 ⟨t, encode_of_decode c t hd⟩) h

theorem encode_decode_nat (n : ℕ) :
    Encodable.encode (Encodable.decode (α := Lambda) n) = cond (is_valid_code n) (n + 1) 0 := by
  cases hv : is_valid_code n with
  | true =>
      obtain ⟨t, ht⟩ := (is_valid_code_iff n).1 hv
      subst ht
      have hdec : (Encodable.decode (α := Lambda) (Lambda.encode t)) = some t :=
        Encodable.encodek t
      rw [hdec]
      simp
      rfl
  | false =>
      have hd : (Encodable.decode (α := Lambda) n) = none :=
        decode_eq_none_of_not_valid (by simp [hv])
      rw [hd]
      simp

/-- The numeric coding of terms is primitive recursive, so `Lambda` is a `Primcodable` type and
can be used directly with Mathlib's `Primrec`/`Computable` API. -/
noncomputable instance : Primcodable Lambda where
  prim := by
    have h : Primrec fun n : ℕ => cond (is_valid_code n) (n + 1) 0 :=
      Primrec.cond Lambda.is_valid_code_primrec Primrec.succ (Primrec.const 0)
    exact Primrec.nat_iff.1 (h.of_eq fun n => (encode_decode_nat n).symm)

theorem primrec_encode : Primrec Lambda.encode := Primrec.encode

------------------------------------------------------------------------
-- Translating between the two codings
------------------------------------------------------------------------

/-- The BLC bit string attached to a numeric code. -/
noncomputable def bitsOfNat (c : ℕ) : List Bool := (Lambda.decode c).elim [] bits

/-- The numeric code attached to a BLC bit string. -/
def natOfBits (bs : List Bool) : Option ℕ := (blcDecodeFull bs).map Lambda.encode

@[simp] theorem bitsOfNat_encode (t : Lambda) : bitsOfNat (Lambda.encode t) = bits t := by
  simp [bitsOfNat, decode_encode]

@[simp] theorem natOfBits_bits (t : Lambda) : natOfBits (bits t) = some (Lambda.encode t) := by
  simp [natOfBits]

/-- **The two codings are inter-translatable, one way.**  Reading a valid numeric code out as BLC
bits and parsing the bits back returns the same code. -/
theorem natOfBits_bitsOfNat {c : ℕ} (h : is_valid_code c = Bool.true) :
    natOfBits (bitsOfNat c) = some c := by
  obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 h
  simp

/-- **The two codings are inter-translatable, the other way.**  Parsing a BLC program and writing
its numeric code back out as bits returns the same bit string. -/
theorem bitsOfNat_natOfBits {bs : List Bool} {c : ℕ} (h : natOfBits bs = some c) :
    bitsOfNat c = bs := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [bitsOfNat_encode, (blcDecodeFull_eq_some_iff bs t).1 ht]

end Lambda
