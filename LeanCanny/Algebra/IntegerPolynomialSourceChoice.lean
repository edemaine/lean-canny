/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Algebra.ModularResidueSpace
/-! # Native choice and reindexing of original integer sources

All branches use the caller's original coefficient index and modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialSourceChoice
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

noncomputable def reindex (S : IntegerPolynomialRootQueriesBits.Source) (f : List Bool → List Bool) :
    IntegerPolynomialRootQueriesBits.Source where
  polynomial := S.polynomial ∘ f
  degree := S.degree ∘ f
  mass := S.mass ∘ f
  degree_bound q := S.degree_bound (f q)
  mass_bound q := S.mass_bound (f q)

theorem reindex_access (S : IntegerPolynomialRootQueriesBits.Source)
    (hS : IntegerPolynomialRootQueriesBits.Access S) {f : List Bool → List Bool} (hf : f∈FP) :
    IntegerPolynomialRootQueriesBits.Access (reindex S f) where
  coefficient := PolynomialFamilyProductBits.reindexEvaluator hS.coefficient f hf
  degree := hS.degree.comp hf
  mass := hS.mass.comp hf

noncomputable def choose (p : List Bool → Prop) (S T : IntegerPolynomialRootQueriesBits.Source) :
    IntegerPolynomialRootQueriesBits.Source where
  polynomial q := if p q then S.polynomial q else T.polynomial q
  degree q := if p q then S.degree q else T.degree q
  mass q := if p q then S.mass q else T.mass q
  degree_bound q := by split_ifs <;> first | exact S.degree_bound q | exact T.degree_bound q
  mass_bound q := by split_ifs <;> first | exact S.mass_bound q | exact T.mass_bound q

theorem choose_access {p : List Bool → Prop} (hp : FPPred p)
    (S T : IntegerPolynomialRootQueriesBits.Source)
    (hS : IntegerPolynomialRootQueriesBits.Access S) (hT : IntegerPolynomialRootQueriesBits.Access T) :
    IntegerPolynomialRootQueriesBits.Access (choose p S T) where
  coefficient := by
    have E := ModularResidueSpace.branchEvaluator pairSnd
      (fun q => (S.polynomial (RationalSubstitution.IntegerBits.context q)).coeff
        (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)))
      (fun q => (T.polynomial (RationalSubstitution.IntegerBits.context q)).coeff
        (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)))
      (fun q => p (RationalSubstitution.IntegerBits.context q))
      (hp.comp RationalSubstitution.IntegerBits.context_mem_FP) hS.coefficient hT.coefficient
    refine E.congr (funext fun q => ?_)
    unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
    dsimp only [choose]
    split_ifs <;> rfl
  degree := BinaryFn.ite hp hS.degree hT.degree
  mass := BinaryFn.ite hp hS.mass hT.mass

end LeanCanny.Algebra.IntegerPolynomialSourceChoice
