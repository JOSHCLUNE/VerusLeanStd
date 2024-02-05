import VerusLeanStd.VerusLeanMapping

/-
pub open spec fn modulus (x: int, y: int) -> int
{
    x % y
}
-/
-- Verus' modulus operator corresponds with Mathlib's `%`

/-
/* the remainder 0 divided by an integer is 0 */
// #[verifier::spinoff_prover]
proof fn lemma_mod_of_zero_is_zero(m:int)
    requires (0 as int) < m
    ensures   0 as int % m == 0 as int
{}
-/
-- Note: The requirement that 0 < m appears to be unnecessary
theorem verus_lemma_mod_of_zero_is_zero (m : Int) (h : 0 < m) : 0 % m = 0 := by rfl

/-
/* describes fundamentals of the modulus operator */
#[verifier(nonlinear)]
pub proof fn lemma_fundamental_div_mod(x:int, d:int)
    requires d != 0
    ensures  x == d * (x / d) + (x % d)
{}
-/
-- Note: The requirement that d ≠ 0 appears to be unnecessary
theorem verus_lemma_fundamental_div_mod (x d : Int) (h : d ≠ 0) : x = d * (x / d) + (x % d) :=
  (Int.ediv_add_emod x d).symm

/-
/* the remained of 0 divided by any integer is always 0 */
// #[verifier::spinoff_prover]
proof fn lemma_0_mod_any()
    ensures forall |m: int| m > 0 ==> #[trigger] modulus(0, m) == 0
{}
-/
-- Note: We don't need m > 0 (also, this appears to be the same as verus_lemma_mod_of_zero_is_zero)
theorem verus_lemma_0_mod_any : ∀ m : Int, m > 0 → 0 % m = 0 := by intros; rfl

/-
/* a natural number x divided by a larger natural number gives a remainder equal to x */
#[verifier(nonlinear)]
pub proof fn lemma_small_mod(x:nat, m:nat)
    requires
        x < m,
        0 < m
    ensures
        #[trigger] modulus(x as int, m as int) == x as int
{}
-/
-- Note: We don't need 0 < m
theorem verus_lemma_small_mod (x m : Nat) (h : x < m) (h' : 0 < m) : (x : Int) % (m : Int) = (x : Int) := by
  have h1 : 0 ≤ (x : Int) := by simp only [Nat.cast_nonneg]
  have h2 : 0 ≤ (m : Int) := by simp only [Nat.cast_nonneg]
  rw [← Int.mod_eq_emod h1 h2, ← Int.ofNat_mod x m]
  exact ((fun a b => (Mathlib.Tactic.Zify.nat_cast_eq a b).mp) x (x % m) (Nat.mod_eq_of_lt h).symm).symm

/-
/* the range of the modulus of any integer will be [0, m) where m is the divisor */
// Euclid's division lemma
#[verifier(nonlinear)]
pub proof fn lemma_mod_range(x:int, m:int)
    requires m > 0
    ensures  0 <= #[trigger] modulus(x, m) < m
{}
-/
theorem verus_lemma_mod_range (x m : Int) (h : m > 0) : 0 ≤ x % m ∧ x % m < m := by
  have h' : m ≠ 0 := Int.ne_of_gt h
  exact ⟨Int.emod_nonneg x h', Int.emod_lt_of_pos x h⟩
