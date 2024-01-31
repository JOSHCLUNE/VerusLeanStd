import VerusLeanStd.GeneralInternals
import VerusLeanStd.MulInternalsNonlinear
-- Verus source: source/pervasive/nonlinear_arith/internals/mul_internals.rs

/-
/// performs multiplication for positive integers using recursive addition
/// change x to nat?
// NEED TO ASK, here, we either change x into nat or return 0 when x < 0
// This is because we do not have partial functions
// and the recommend clause is too weak so that we actually need to consider
// the x < 0 case
#[verifier(opaque)]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends x >= 0
    decreases x
    // any design reason for using recommends instead of requires?
{
    if x <= 0 {
        0
    } else {
        y + mul_pos(x - 1, y)
    }
}
-/
def verus_mul_pos (x y : Int) : Int :=
  if x ≤ 0 then 0
  else y + verus_mul_pos (x - 1) y
termination_by verus_mul_pos x y => Int.natAbs x
decreasing_by
  simp only [WellFoundedRelation.rel, Nat.lt_wfRel, InvImage, sizeOf_nat, Nat.lt_eq, gt_iff_lt]
  rw [Int.natAbs_lt_iff_sq_lt]
  linarith

/-
/// performs multiplication for both positive and negative integers
pub open spec fn mul_recursive(x: int, y: int) -> int
{
    if x >= 0 { mul_pos(x, y) }
    else { -1 * mul_pos(-1 * x, y) }
}
-/
def verus_mul_recursive (x y : Int) : Int :=
  if x ≥ 0 then verus_mul_pos x y
  else -1 * verus_mul_pos (-1 * x) y

/-
/// performs induction on multiplication
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
        // TODO how about this proof style? seems to distablize one or two proofs
        // forall |i: int, j:int| i >= 0 && j == i + 1 && #[trigger] f(i) ==> #[trigger] f(j),
        // forall |i: int, j:int| i <= 0 && j == i - 1 && #[trigger] f(i) ==> #[trigger] f(j),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}
-/
theorem verus_lemma_mul_induction (f : Int → Bool)
  (h1 : f 0) (h2 : ∀ i : Int, i ≥ 0 ∧ f i → f (i + 1))
  (h3 : ∀ i : Int, i ≤ 0 ∧ f i → f (i - 1)) : ∀ i : Int, f i := by
  sorry

/-
/// proves that multiplication is always commutative
// #[verifier::spinoff_prover]
proof fn lemma_mul_commutes()
    ensures
        forall |x: int, y: int| #[trigger](x * y) == y * x
{}
-/
theorem verus_lemma_mul_commutes : ∀ x y : Int, x * y = y * x := Int.mul_comm

/-
/// proves the distributive property of multiplication when multiplying an interger
/// by (x +/ - 1)
// #[verifier::spinoff_prover]
proof fn lemma_mul_successor()
    ensures
        forall |x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall |x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall |x:int, y:int| #[trigger]((x + 1) * y) == x * y + y by {
        MulINL::lemma_mul_is_distributive_add(y, x, 1);
    }

    assert forall |x:int, y:int| #[trigger]((x - 1) * y) == x * y - y by {
        assert((x - 1) * y  == y * (x - 1));
        MulINL::lemma_mul_is_distributive_add(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}
-/
theorem verus_lemma_mul_successor :
  (∀ x y : Int, ((x + 1) * y) = x * y + y) ∧
  (∀ x y : Int, ((x - 1) * y) = x * y - y) := by exact ⟨add_one_mul, sub_one_mul⟩

/-
/// proves the distributive property of multiplication
#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
    forall |x: int, y: int, z: int| #[trigger]((x + y) * z) == (x * z + y * z),
    forall |x: int, y: int, z: int| #[trigger]((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();

    assert forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
        by
    {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall |i: int| i >= 0 && #[trigger] f1(i) implies #[trigger]f1(add1(i, 1)) by {
            assert(  (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f1(i) implies #[trigger]f1(sub1(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));


    }

    assert forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall |i: int| i >= 0 && #[trigger] f2(i) implies #[trigger]f2(add1(i, 1)) by {
            assert(  (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f2(i) implies #[trigger]f2(sub1(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };

        lemma_mul_induction(f2);
        assert(f2(y));
    }

}
-/
theorem verus_lemma_mul_distributes :
  (∀ x y z : Int, (x + y) * z = x * z + y * z) ∧
  (∀ x y z : Int, (x - y) * z = x * z - y * z) := by exact ⟨Int.add_mul, Int.sub_mul⟩

/-
/// groups distributive and associative properties of multiplication
// #[verifier::spinoff_prover]
pub open spec fn mul_auto() -> bool
{
    &&& forall |x:int, y:int| #[trigger](x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z)
}
-/
-- Skipping this for now until I understand how to translate `&&&`

-- TODO: Continue translating this file from mul_auto onward
