
/-
Lemma: The step function applied to the list of previous values equals the value of the function.
-/
theorem Lambda.is_valid_code_eq_step (n : ℕ) :
  Lambda.isValidCodeStep2 ((List.range n).map Lambda.is_valid_code) = some (Lambda.is_valid_code n) := by
    unfold Lambda.isValidCodeStep2;
    unfold Lambda.is_valid_code;
    rw [ Nat.strongRecOn_eq ] at *;
    aesop;
    · unfold Lambda.case1; aesop;
      all_goals (first | omega | (simp (config := { failIfUnchanged := false }) +decide [List.getElem?_map, List.getElem?_range]; omega) | sorry);
    · unfold Lambda.case2; aesop;
      all_goals (first | omega | (simp (config := { failIfUnchanged := false }) +decide [List.getElem?_map, List.getElem?_range]; omega) | sorry)

/-
