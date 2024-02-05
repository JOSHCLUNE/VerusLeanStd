import VerusLeanStd.VerusLeanMapping
-- Verus source: source/pervasive/nonlinear_arith/internals/mul_internals_nonlinear.rs

/-
/* multiplying two positive integers will result in a positive integer */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
{}
-/
theorem verus_lemma_mul_strictly_positive (x y : Int) : 0 < x ∧ 0 < y → 0 < x * y := by
  aesop

/-
/* Integral Domain */
/* multiplying two nonzero integers will never result in 0 as the poduct */
#[verifier(nonlinear)]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
{}
-/
theorem verus_lemma_mul_nonzero (x y : Int) : x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  aesop

/-
/* multiplication is associative */
#[verifier(nonlinear)]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
{}
-/
theorem verus_lemma_mul_is_associative (x y z : Int) : x * (y * z) = (x * y) * z := by
  rw [Int.mul_assoc]

/-
/* multiplication is distributive */
#[verifier(nonlinear)]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
{}
-/
theorem verus_lemma_mul_is_distributive_add (x y z : Int) : x * (y + z) = x * y + x * z := Int.mul_add x y z

/-
/* the product of two integers is greater than the value of each individual integer */
#[verifier(nonlinear)]
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y
    ensures
        x * y >= x && x * y >= y
{}
-/
theorem verus_lemma_mul_ordering (x y : Int) (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : 0 ≤ x * y) : x * y ≥ x ∧ x * y ≥ y := by
  have h' : ∀ x y : Int, x ≠ 0 → y ≠ 0 → 0 ≤ x * y → x * y ≥ x := by
    intros x y h1 h2 h3
    by_cases h4 : x > 0
    . apply le_mul_of_one_le_right (Int.nonneg_of_pos h4)
      have h5 : y < 0 ∨ 1 ≤ y := by
        rw [← Int.zero_add 1, Int.add_one_le_iff]
        exact Int.lt_or_gt_of_ne h2
      rcases h5 with h5 | h5
      . have := Int.mul_neg_of_pos_of_neg h4 h5
        linarith
      . exact h5
    . have h5 : x < 0 := by
        simp only [gt_iff_lt, not_lt] at h4
        exact lt_of_le_of_ne h4 h1
      linarith
  constructor
  . exact h' x y h1 h2 h3
  . rw [mul_comm] at h3
    rw [mul_comm]
    exact h' y x h2 h1 h3

/-
/* multiplying by a positive integer preserves inequality */
#[verifier(nonlinear)]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0
    ensures
        x * z < y * z
{}
-/
theorem verus_lemma_mul_strict_inequality (x y z : Int) (h1 : x < y) (h2 : z > 0) : x * z < y * z :=
  Int.mul_lt_mul_of_pos_right h1 h2

-- Everything in source/pervasive/nonlinear_arith/internals/mul_internals_nonlinear.rs has been moved to this file
