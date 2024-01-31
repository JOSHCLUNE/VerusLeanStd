import VerusLeanStd.VerusLeanMapping
-- Verus source: source/pervasive/nonlinear_arith/internals/div_internals_nonlinear.rs

/-
/* zero divided by an integer besides 0 is 0 */
#[verifier(nonlinear)]
pub proof fn lemma_div_of0(d: int)
    requires d != 0 as int
    ensures 0 as int / d == 0 as int
{}
-/
-- Note: We don't actually need Verus' precondition that d ≠ 0
theorem verus_lemma_div_of0 (d : Int) : (0 : Int) / d = 0 := Int.zero_ediv d

/-
/* the quotient of an integer divided by itself is 1 */
pub proof fn lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
{}
-/
theorem verus_lemma_div_by_self (d : Int) (h : d ≠ 0) : d / d = 1 := Int.ediv_self h

/-
/* dividing a smaller integer by a larger integer results in a quotient of 0  */
#[verifier(nonlinear)]
pub proof fn lemma_small_div()
    ensures forall |x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger](x / d) == 0
{}
-/
-- Note: We don't actually appear to need Verus' precondition that d > 0
theorem verus_lemma_small_div : ∀ x d : Int, 0 ≤ x ∧ x < d ∧ d > 0 → x / d = 0 := by
  intro x d h
  exact Int.ediv_eq_zero_of_lt h.1 h.2.1
