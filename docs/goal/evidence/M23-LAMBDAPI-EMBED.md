# M23-LAMBDAPI-EMBED — the library's `λΠ` embeds in the `λP` corner

Module: `Start/PTSLambdaPiEmbed.lean` (new; imports only `Start.PTSCube`, `Start.PTSTyping`).

## Terminal statements

```lean
def PureTypeSystem.ofTm : LambdaPi.Tm → Expr Srt
theorem PureTypeSystem.toTm_ofTm (t : Tm) : toTm (ofTm t) = t
theorem PureTypeSystem.ofTm_toTm (M : Expr Srt) : ofTm (toTm M) = M
theorem PureTypeSystem.ofTm_rename (t : Tm) (ρ : ℕ → ℕ) :
    ofTm (LambdaPi.rename ρ t) = (ofTm t).rename ρ
theorem PureTypeSystem.ofTm_subst (t : Tm) (σ : ℕ → Tm) :
    ofTm (LambdaPi.subst σ t) = (ofTm t).subst (fun n => ofTm (σ n))
theorem PureTypeSystem.conv_ofTm {t u : Tm} (h : LambdaPi.Conv t u) : Converts (ofTm t) (ofTm u)
theorem PureTypeSystem.typing_ofTm {Γ : LambdaPi.Ctx} {t A : Tm} (h : LambdaPi.Typing Γ t A)
    (hΓ : LambdaPi.Wf Γ) :
    HasType (cubeSpec lambdaP) (Γ.map ofTm) (ofTm t) (ofTm A)
theorem PureTypeSystem.hasType_iff_typing {Γ : List (Expr Srt)} {M A : Expr Srt}
    (hΓ : ValidContext (cubeSpec lambdaP) Γ) :
    HasType (cubeSpec lambdaP) Γ M A ↔ LambdaPi.Typing (Γ.map toTm) (toTm M) (toTm A)
```

Exit criterion 1: `ofTm` with `toTm_ofTm`/`ofTm_toTm` (inverse to `toTm`), `ofTm_rename`,
`ofTm_subst`, `ofTm_inst`, `step_ofTm`, `conv_ofTm` (and the converse `converts_iff_conv`).

Exit criterion 2: `typing_ofTm`, by induction on the `λΠ` derivation, carrying the validity of
the translated context (`wf_ofTm`); the axiom rule is moved into longer contexts by weakening, which
is why `LambdaPi.Wf Γ` is needed.

With this, `M23-PTS` has both halves of its second exit criterion (System F through
`FElab.elaborate`, `λΠ` through `typing_ofTm`) and is set back to `DONE_STRONG`.

Gates: `lake build`, `scripts/check_sorry.py`, `scripts/check_closure.py`,
`scripts/goal_state.py validate`. Axioms of `typing_ofTm` and `hasType_iff_typing`: `[propext, Quot.sound]`
(`#print axioms`).
