/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveParameterCoefficient
public import LeanCanny.ETR.CoerciveInfinitesimalFamily

/-! # Native root-family access for the actual coercive primitive parameter -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.ETR.CoerciveParameterAccess
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveInfinitesimalFamily (rootFamily)
attribute [local irreducible] CoercivePreparationControls.family RationalSubstitutionBits.compiledTerm Matrix.det

/-- Put the modulus between the original context and the alpha/root selectors. -/
def query (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst p)) (pairSnd p))
    (pair (pairSnd (pairSnd (pairFst p))) (pairFst (pairSnd (pairFst p))))

theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
      (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP))

theorem coefficient_packet (P : List Bool → Polynomial (Polynomial ℤ))
    (bits : List Bool) (i j m : ℕ) (hm : 0 < m) :
    (SymbolicFixedTableEntryBits.coefficient P ∘ query)
      (pair (pair bits (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))
        (BinaryNatCode.encode (m - 1))) = DyadicBits.integerResidue (((P bits).coeff i).coeff j) m := by
  change SymbolicFixedTableEntryBits.coefficient P (query _) = DyadicBits.integerResidue _ m
  simp only [query, SymbolicFixedTableEntryBits.coefficient, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (show 1 ≤ m by omega)]
  rfl

noncomputable def access : DyadicPolynomialBits.Access rootFamily where
  coefficient := SymbolicFixedTableEntryBits.coefficient
    (fun bits => (CoercivePreparationControls.family bits).parameter) ∘ query
  coefficient_eq := coefficient_packet _

theorem evaluator : SpaceFunction access.coefficient :=
  CoerciveParameterCoefficient.evaluator.precompose query query_FP

end LeanCanny.ETR.CoerciveParameterAccess
