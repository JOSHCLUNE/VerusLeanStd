import Std.Data.Int.Basic
import Mathlib -- This import is clunky, but it makes using Aesop a lot easier.

-- This file is for miscellaneous comments about translating between Verus and Lean.
-- The Verus PR that this repository is meant to translate is at: https://github.com/ahuoguo/verus/pull/3

/- Current translation status:
  - source/pervasive/nonlinear_arith/internals/div_internals_nonlinear.rs ↦ DivInternalsNonlinear.lean
    - Fully translated and proven
    - Note: The Verus forms of these theorems appear to have some redundant/unnecessary preconditions
  - source/pervasive/nonlinear_arith/internals/mul_internals_nonlinear.rs ↦ MulInternalsNonlinear.lean
    - Fully translated and proven
  - source/pervasive/nonlinear_arith/internals/general_internals.rs ↦ GeneralInternals.lean
    - Fully translated (not proven)
  - source/pervasive/nonlinear_arith/internals/div_internals.rs ↦ DivInternals.lean
    - Partially translated (not proven)
    - Blocked by the fact that I don't know how to translate `&&&`
  - source/pervasive/nonlinear_arith/internals/mul_internals.rs ↦ MulInternals.lean
    - Partially translated (not proven)
    - Blocked by the fact that I don't know how to translate `&&&`
  - source/pervasive/nonlinear_arith/math.rs doesn't warrant translation
  - source/pervasive/nonlinear_arith/mod.rs doesn't warrant translation
  - source/pervasive/nonlinear_arith/internals/mod.rs doesn't warrant translation
  - source/pervasive/nonlinear_arith/internals/mod_internals_nonlinear.rs ↦ ModInternalsNonlinear.lean
    - Fully translated and proven
    - Note: The Verus forms of these theorems appear to have some redundant/unnecessary preconditions
  - Everything else
    - Not at all translated yet
-/

/- About integer division in Verus:
    Rust has multiple integer types, but for this library, we don't really need to worry about any
    of them. Instead, the main integer type this library should interact with is Verus' `int` type
    described in https://verus-lang.github.io/verus/guide/integers.html. Unlike Rust's actual
    executable division, Verus' `int` division and modulus operators compute Euclidean division and
    remainder, meaning `x % y` will always be in the range `[0, y)`.

    The corresponding Mathlib operator for Verus' `int` division is `Int.ediv`, and the corresponding
    Mathlib operator for Verus' `int` modulus operator is `Int.emod`. Whenever `Std.Data.Int.Basic`
    is imported, Lean's `/` and `%` symbols are overridden with the operators that we want when
    applied to values of type `Int`. So for our purposes, we want to make sure that `Std.Data.Int.Basic`
    is always imported, and then we should be able to use most of Mathlib's usual lemmas since Mathlib's
    default integer division is what we want.
-/

#check Int.instDivInt_1 -- Here we see that Lean's core division is overridden to Euclidean division
#check -7 /3 -- Inspecting `instHDiv` in the infoview will show that `/` reduces to `Int.instDivInt_1`
#eval -7 / 3
#eval -7 % 3
#eval -7 / -3
#eval -7 % -3

/- About triggers in Verus:
    Triggers in Verus are described in https://verus-lang.github.io/verus/guide/forall.html. As best
    as I currently understand, they are just hints for the SMT solver that we can completely ignore.
-/

/- About `&&&` in Verus:
    &&& is used in div_auto and mul_auto (see MulInternals.lean and DivInternals.lean)
    Unfortunately, section 25.5 of the Verus language guide, which will explain what this actually is,
    doesn't exist yet. So I'm going to skip lemmas involving this for now until someone who actually
    knows Verus can tell me what this is.
-/

/- About termination in Verus:
    Some of Verus' functions have a `decreases ...` or `decreases ... when ...` clause attached to
    its functions to justify termination. The former can be translated to Lean using Lean's `termination_by`
    and `decreasing_by`. But I haven't yet decided how to translate `decreases ... when ...`. There appear
    to be some Verus functions (e.g. `verus_div_pos` in DivInternals.lean) where then `when ...` clause
    is necessary to justify termination. For that reason, it might make sense to turn the `when ...` clause
    into a precondition, but I'm not sure if Verus users may want to call the function even outside of the
    recommended use case.
-/

/- About recommends in Verus:
    The recommends keyword in Verus is described in https://verus-lang.github.io/verus/guide/spec_vs_proof.html.
    As best as I currently understand, these conditions are not actually enforced (instead, they seem to just
    be used for clearer errors). So I think we can safely ignore them.
-/
