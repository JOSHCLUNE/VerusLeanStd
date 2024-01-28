import VerusLeanStd.VerusLeanMapping
-- Verus source: source/pervasive/nonlinear_arith/internals/general_internals.rs
/- Note: This file has the line
    `use crate::nonlinear_arith::math::{add as add1, sub as sub1};`
   which means that every occurence of `add1` corresponds to `add` from
   source/pervasive/nonlinear_arith/math.rs and every occurrence of `sub1`
   corresponds to `sub` from that same file. `add` and `sub` are defined
   exactly as you would expect them to be, so in this file, we can map Verus'
   `add1` onto Lean's `+` and Verus' `sub1` onto Lean's `-`.
-/

/-
pub open spec fn is_le(x: int, y: int) -> bool
{
    x <= y
}
-/
def verus_is_le (x y : Int) : Bool := x ≤ y

/-
/* aids in the process of induction for modulus */
// #[verifier::spinoff_prover]
proof fn lemma_induction_helper_pos(n: int, f: FnSpec(int) -> bool, x: int)
    requires
        x >= 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add1(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub1(i, n))
    ensures
        f(x)
    decreases x
{
    if (x >= n)
    {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert (f (add1(x - n, n)));
        assert(f((x - n) + n));
    }
}
-/
theorem verus_lemma_induction_helper_pos (n : Int) (f : Int → Bool) (x : Int)
  (h1 : x ≥ 0) (h2 : n > 0) (h3 : ∀ i : Int, 0 ≤ i ∧ i < n → f i)
  (h4 : ∀ i : Int, i ≥ 0 ∧ f i → f (i + n))
  (h5 : ∀ i : Int, i < n ∧ f i → f (i - n)) : f x := by
  sorry

/-
// #[verifier::spinoff_prover]
proof fn lemma_induction_helper_neg(n: int, f: FnSpec(int) -> bool, x: int)
    requires
        x < 0,
        n > 0,
        forall |i : int| 0 <= i < n ==> #[trigger] f(i),
        forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add1(i, n)),
        forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub1(i, n))
    ensures
        f(x)
    decreases -x
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert (f (sub1(x + n, n)));
        assert(f((x + n) - n));
    }
    else {
        lemma_induction_helper_neg(n, f, x + n);
        assert (f (sub1(x + n, n)));
        assert(f((x + n) - n));
    }
}
-/
theorem verus_lemma_induction_helper_neg (n : Int) (f : Int → Bool) (x : Int)
  (h1 : x < 0) (h2 : n > 0) (h3 : ∀ i : Int, 0 ≤ i ∧ i < n → f i)
  (h4 : ∀ i : Int, i ≥ 0 ∧ f i → f (i + n))
  (h5 : ∀ i : Int, i < n ∧ f i → f (i - n)) : f x := by
  sorry

/-
// #[verifier::spinoff_prover]
pub proof fn lemma_induction_helper(n: int, f: FnSpec(int) -> bool, x: int)
requires
    n > 0,
    forall |i : int| 0 <= i < n ==> #[trigger] f(i),
    forall |i : int| i >= 0 && #[trigger] f(i) ==> #[trigger] f (add1(i, n)),
    forall |i : int| i < n  && #[trigger] f(i) ==> #[trigger] f (sub1(i, n))
ensures
    f(x)
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    }
    else {
        lemma_induction_helper_neg(n, f, x);
    }
}
-/
theorem verus_lemma_induction_helper (n : Int) (f : Int → Bool) (x : Int)
  (h1 : n > 0) (h2 : ∀ i : Int, 0 ≤ i ∧ i < n → f i)
  (h3 : ∀ i : Int, i ≥ 0 ∧ f i → f (i + n))
  (h4 : ∀ i : Int, i < n ∧ f i → f (i - n)) : f x := by
  by_cases h0 : x ≥ 0
  . exact verus_lemma_induction_helper_pos n f x h0 h1 h2 h3 h4
  . simp only [ge_iff_le, not_le] at h0
    exact verus_lemma_induction_helper_neg n f x h0 h1 h2 h3 h4

-- Everything in source/pervasive/nonlinear_arith/internals/general_internals.rs has been moved to this file
