import VerusLeanStd.GeneralInternals
-- Verus source: source/pervasive/nonlinear_arith/internals/div_internals.rs

/-
/// Performs division recursively with positive denominator.
#[verifier(opaque)]
pub open spec fn div_pos(x: int, d: int) -> int
    recommends d > 0
    decreases (if x < 0 {d - x} else {x}) when d > 0
{
    if x < 0
    {
        -1 + div_pos(x + d, d)
    } else if x < d {
        0
    }
    else {
        1 + div_pos(x - d, d)
    }
}
-/
def verus_div_pos (x d : Int) : Int :=
  if x < 0 then -1 + verus_div_pos (x + d) d
  else if x < d then 0
  else 1 + verus_div_pos (x - d) d
termination_by verus_div_pos x d => |x|
decreasing_by
  sorry

/-
/// Performs division recursively.
#[verifier(opaque)]
pub open spec fn div_recursive(x: int, d: int) -> int
    recommends d != 0
{
    // reveal(div_pos);
    if d > 0 {
        div_pos(x, d)
    } else {
        -1 * div_pos(x, -1 * d)
    }
}
-/
def verus_div_recursive (x d : Int) : Int :=
  if d > 0 then verus_div_pos x d
  else -1 * (verus_div_pos x (-d))

/-
/// Proves the basics of the division operation
// #[verifier::spinoff_prover]
pub proof fn lemma_div_basics(n: int)
    requires n > 0
    ensures
        (n / n) == 1 &&  -((-n) / n) == 1,
        forall |x:int| 0 <= x < n <==> #[trigger](x / n) == 0,
        forall |x:int| #[trigger]((x + n) / n) == x / n + 1,
        forall |x:int| #[trigger]((x - n) / n) == x / n - 1,
{
    lemma_mod_auto(n);
    lemma_mod_basics_auto(n);
    div_internals_nonlinear::lemma_small_div();
    div_internals_nonlinear::lemma_div_by_self(n);

    assert forall |x:int| 0 <= x < n <== #[trigger](x / n) == 0 by {
        mod_internals_nonlinear::lemma_fundamental_div_mod(x, n);
    }
}
-/
theorem verus_lemma_div_basics (n : Int) (h : n > 0) :
  (n / n) = 1 ∧ -((-n) / n) == 1 ∧
  (∀ x : Int, (0 ≤ x ∧ x < n) ↔ (x / n = 0)) ∧
  (∀ x : Int, ((x + n) / n) = x / n + 1) ∧
  (∀ x : Int, ((x - n) / n) = x / n - 1) := by
  sorry

/-
/// Automates the division operator process. Contains the identity property, a
/// fact about when quotients are zero, and facts about adding and subtracting
/// integers over a common denominator.
pub open spec fn div_auto(n: int) -> bool
    recommends n > 0
{
    &&& mod_auto(n)
    &&& (n / n == -((-n) / n) == 1)
    &&& forall |x: int| 0 <= x < n <==> #[trigger](x / n) == 0
    &&& (forall |x: int, y: int| #![trigger ((x + y) / n)]
         {let z = (x % n) + (y % n);
         (  (0 <= z < n && ((x + y) / n) == x / n + y / n)
             || (n <= z < n + n && ((x + y) / n) == x / n + y / n + 1))})
    &&& (forall |x: int, y: int| #![trigger ((x - y) / n)]
        {let z = (x % n) - (y % n);
        (  (0 <= z < n && ((x - y) / n) == x / n - y / n)
            || (-n <= z < 0  && ((x - y) / n) == x / n - y / n - 1))})
}
-/
-- Skipping this for now until I understand how to translate `&&&`

-- TODO: Continue translating this file from div_auto onward
