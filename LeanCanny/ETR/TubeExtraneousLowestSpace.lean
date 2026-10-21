/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousCoefficientZero
public import LeanCanny.ETR.TubeExtraneousLowest
public import LeanCanny.Algebra.LowestCoefficientSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Computing the actual lowest extraneous deformation coefficient in polynomial space

Whole-coefficient zero tests supply the bounded first-index search. Its result
is the natural trailing deformation degree of the actual extraneous determinant.
The selected original perturbation/projection coefficient can then be read
modularly or signed through the complete existing three-parameter evaluator.
All search, identity-test and original parameter-reader costs are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] determinant coefficient scalarCoefficient

noncomputable def lowestIndex (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (determinant source active n d ell c).natTrailingDegree

theorem lowestIndex_value (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    Nat.fromBitsLE (lowestIndex source active n d ell c) = (determinant source active n d ell c).natTrailingDegree := by
  simp only [lowestIndex, MacaulayBits.fromBits_encode]

theorem lowestIndex_bound (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) : Nat.fromBitsLE (lowestIndex source active n d ell c) ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) := by
  rw [lowestIndex_value]
  exact (determinant source active n d ell c).natTrailingDegree_le_natDegree.trans (determinant_degree source active n d ell c)

theorem lowestIndex_first (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (determinant source active n d ell c).coeff (Nat.fromBitsLE (lowestIndex source active n d ell c)) ≠ 0 ∧
      ∀ i < Nat.fromBitsLE (lowestIndex source active n d ell c), (determinant source active n d ell c).coeff i = 0 := by
  rw [lowestIndex_value]
  exact ⟨Polynomial.coeff_natTrailingDegree_ne_zero.mpr (determinant_ne_zero source active n d ell c),
    fun _ hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi⟩

theorem lowestIndexEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : SpaceFunction (lowestIndex source active n d ell) := by
  have E := (coefficientZeroDecider D).flagEvaluator
  have hM := MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime D.sourceFP)
  have hd (c : List Bool) : (determinant source active n d ell c).natDegree ≤
      Nat.fromBitsLE (MacaulayBits.dimensionCode (TubeCleared.layout source) c) := by
    rw [MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code, MacaulayBits.fromBits_encode]
    exact determinant_degree source active n d ell c
  have Q := LowestCoefficientBits.evaluator E (MacaulayBits.dimensionCode (TubeCleared.layout source)) hM
    (determinant source active n d ell) hd (by
      intro c i
      simp only [coefficientZeroLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
      by_cases hz : (determinant source active n d ell c).coeff i = 0 <;> simp [hz])
  exact Q

noncomputable def lowestScalar (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  ((lowestCoefficient source active n d ell c).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c))

theorem scalar_at_lowest (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    scalarCoefficient source active n d ell c (Nat.fromBitsLE (inner c)) (Nat.fromBitsLE (middle c))
      (determinant source active n d ell c).natTrailingDegree = lowestScalar source active inner middle n d ell c := by
  unfold scalarCoefficient lowestScalar lowestCoefficient Polynomial.trailingCoeff
  rfl

noncomputable def lowestModularValue (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (lowestScalar source active inner middle n d ell c) (Nat.fromBitsLE (modulus c) + 1)

theorem lowestModularEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (lowestModularValue source active modulus inner middle n d ell) := by
  have E := (lowestIndexEvaluator D).withInput
  have R := evaluator (D.reindex pairFst pairFst_mem_FP) pairSnd pairSnd_mem_FP
  have Q := E.chain R
  refine Q.congr (funext fun c => ?_)
  change modularValue (source ∘ pairFst) (active ∘ pairFst) (modulus ∘ pairFst) (inner ∘ pairFst) (middle ∘ pairFst) pairSnd
    (fun q => n (pairFst q)) (fun q => d (pairFst q)) (fun q => ell (pairFst q))
      (pair c (lowestIndex source active n d ell c)) = _
  rw [modularValue, coefficient_reindex]
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, lowestIndex, MacaulayBits.fromBits_encode]
  rw [scalar_at_lowest]
  rfl

noncomputable def lowestSign (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  if lowestScalar source active inner middle n d ell c = 0 then []
  else if lowestScalar source active inner middle n d ell c < 0 then [true] else [false, true]

theorem lowestSignEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (lowestSign source active inner middle n d ell) := by
  have E := (lowestIndexEvaluator D).withInput
  have R := signumEvaluator (D.reindex pairFst pairFst_mem_FP) pairSnd pairSnd_mem_FP
  have Q := E.chain R
  refine Q.congr (funext fun c => ?_)
  change integerSign (source ∘ pairFst) (active ∘ pairFst) (inner ∘ pairFst) (middle ∘ pairFst) pairSnd
    (fun q => n (pairFst q)) (fun q => d (pairFst q)) (fun q => ell (pairFst q))
      (pair c (lowestIndex source active n d ell c)) = _
  rw [integerSign, coefficient_reindex]
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, lowestIndex, MacaulayBits.fromBits_encode]
  rw [scalar_at_lowest]
  rfl

end LeanCanny.ETR.TubeExtraneous
