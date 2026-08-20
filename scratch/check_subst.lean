
inductive Lambda
  | var : Nat → Lambda
  | app : Lambda → Lambda → Lambda
  | lam : Lambda → Lambda
  deriving Repr, DecidableEq

def Lambda.lift (n : Nat) (k : Nat) : Lambda → Lambda
  | Lambda.var y => if y < k then Lambda.var y else Lambda.var (y + n)
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.lift n k t₁) (Lambda.lift n k t₂)
  | Lambda.lam t => Lambda.lam (Lambda.lift n (k + 1) t)

def Lambda.subst (s : Lambda) (x : Nat) : Lambda → Lambda
  | Lambda.var y =>
    if y = x then s
    else if y > x then Lambda.var (y - 1)
    else Lambda.var y
  | Lambda.app t₁ t₂ => Lambda.app (Lambda.subst s x t₁) (Lambda.subst s x t₂)
  | Lambda.lam t => Lambda.lam (Lambda.subst (Lambda.lift 1 0 s) (x + 1) t)

def check (t s1 s2 : Lambda) (x y : Nat) : Bool :=
  let lhs := (t.subst s2 y).subst s1 x
  -- The user's formula: subst s1 x (subst s2 y t)
  -- Wait, (t.subst s2 y).subst s1 x is exactly that.
  let rhs := (t.subst s1 (x + 1)).subst (s2.subst s1 x) y
  lhs = rhs

def main : IO Unit := do
  let s1 := Lambda.var 10
  let s2 := Lambda.var 20
  let x := 1
  let y := 2 -- x < y
  for z in [0, 1, 2, 3, 4] do
    let t := Lambda.var z
    let lhs := (t.subst s2 y).subst s1 x
    let rhs := (t.subst s1 (x + 1)).subst (s2.subst s1 x) y
    IO.println s!"z={z}: lhs={repr lhs}, rhs={repr rhs}, ok={lhs == rhs}"
