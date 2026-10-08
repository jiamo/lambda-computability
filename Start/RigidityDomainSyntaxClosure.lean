import Start.RigidityDomainParameterizedSyntax

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Constructibility/DomainSyntaxClosure.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedDefinability
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
variable {M : ZFSet.{u}} {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem DomainDefinable.neg (h : DomainDefinable M P) :
    DomainDefinable M (fun N e => ¬ P N e) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  exact ⟨.neg p,d,k,hk,hd,fun N hN hdN e he => not_congr (hp N hN hdN e he)⟩

theorem DomainDefinable.imp (hP : DomainDefinable M P) (hQ : DomainDefinable M Q) :
    DomainDefinable M (fun N e => P N e → Q N e) := by
  apply (hP.and hQ.neg).neg.congr
  intro N e
  classical
  tauto

theorem DomainDefinable.subst (h : DomainDefinable M P) (r : ℕ → ℕ) :
    DomainDefinable M (fun N e => P N (e ∘ r)) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,k,hk,hd,?_⟩
  intro N hN hdN e he
  rw [SentenceForm.sat_rename]
  change p.Sat _ (mix e d ∘ slotMap r id) ↔ _
  rw [mix_slotMap,Function.comp_id]
  exact hp N hN hdN (e ∘ r) (fun i => he (r i))

theorem DomainDefinable.allMem (C : Context M) (h : DomainDefinable M P) (a : ℕ) :
    DomainDefinable M (fun N e => ∀ x ∈ e a, P N (cons x e)) := by
  obtain ⟨p,d,k,hk,hd,hp⟩ := ((member_definable C 0 (a+1)).toDomain.and h.neg).existsSet.neg
  refine ⟨p,d,k,hk,hd,?_⟩
  intro N hN hdN e he
  rw [hp N hN hdN e he]
  change (¬ ∃ x ∈ N, x ∈ e a ∧ ¬ P N (cons x e)) ↔ _
  classical
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x,hN _ (he a) x hx,hx,hn⟩
  · intro h ⟨x,_,hx,hn⟩
    exact hn (h x hx)

end TuringRigidity.BoundedDefinability

