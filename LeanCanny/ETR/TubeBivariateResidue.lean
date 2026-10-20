/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateBudget

/-! # Varying-modulus access to a fixed integer tube determinant coefficient

The original context fixes the system, parameter polynomials, integer direction
and selected inner/outer degrees. Appending a modulus changes only coefficient
reduction. The complete modular evaluator therefore supplies uniform residues
of one integer, as required by the integer CRT zero and sign routines.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

theorem family_matrix (source active modulus inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (family source active modulus inner outer n d ell B).matrix c =
      (integerMatrix source active n d ell c).map (reduction (Nat.fromBitsLE (modulus c) + 1)) :=
  (Macaulay.matrix_map _ _ _ _).symm

theorem reduction_polynomial_coefficient (p : Polynomial (Polynomial ℤ)) (m u v : ℕ) :
    ((reduction m p).coeff v).coeff u = ((p.coeff v).coeff u : ZMod m) := by
  change (((p.map (Polynomial.mapRingHom (Int.castRingHom (ZMod m)))).coeff v).coeff u) = _
  rw [Polynomial.coeff_map]
  change (((p.coeff v).map (Int.castRingHom (ZMod m))).coeff u) = _
  rw [Polynomial.coeff_map]
  rfl

theorem family_value (source active modulus inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (family source active modulus inner outer n d ell B).value c =
      IntegerBits.coefficientResidue (integerCoefficient source active inner outer n d ell c) (Nat.fromBitsLE (modulus c) + 1) := by
  change residueBits ((((family source active modulus inner outer n d ell B).matrix c).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c))) = _
  rw [family_matrix]
  change residueBits ((((integerMatrix source active n d ell c).map (reduction (Nat.fromBitsLE (modulus c) + 1))).det.coeff
    (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c))) =
      IntegerBits.coefficientResidue (integerCoefficient source active inner outer n d ell c) (Nat.fromBitsLE (modulus c) + 1)
  have hm : ((integerMatrix source active n d ell c).map (reduction (Nat.fromBitsLE (modulus c) + 1))).det =
      reduction (Nat.fromBitsLE (modulus c) + 1) (integerMatrix source active n d ell c).det :=
    ((reduction (Nat.fromBitsLE (modulus c) + 1)).map_det _).symm
  rw [hm, reduction_polynomial_coefficient]
  rfl

theorem integerCoefficient_precompose (source active inner outer f : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) :
    integerCoefficient (source ∘ f) (active ∘ f) (inner ∘ f) (outer ∘ f)
      (fun c => n (f c)) (fun c => d (f c)) (fun c => ell (f c)) q =
        integerCoefficient source active inner outer n d ell (f q) := rfl

attribute [local irreducible] integerCoefficient

noncomputable def residueValue (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) : List Bool → List Bool :=
  (family (source ∘ pairFst) (active ∘ pairFst) pairSnd (inner ∘ pairFst) (outer ∘ pairFst)
    (fun q => n (pairFst q)) (fun q => d (pairFst q)) (fun q => ell (pairFst q)) (B.precomposeUniform pairFst pairFst_mem_FP)).value

theorem residue_eq (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (q : List Bool) :
    residueValue source active inner outer n d ell B q =
      IntegerBits.coefficientResidue (integerCoefficient source active inner outer n d ell (pairFst q)) (Nat.fromBitsLE (pairSnd q) + 1) := by
  rw [residueValue, family_value, integerCoefficient_precompose]

theorem residue_packet (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    residueValue source active inner outer n d ell B (pair c (BinaryNatCode.encode (m - 1))) =
      BinaryNatCode.encode ((integerCoefficient source active inner outer n d ell c : ZMod m).val) := by
  rw [residue_eq]
  simp only [pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, Nat.sub_add_cancel hm]
  rfl

noncomputable def Data.withModulus {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) :
    Data (source ∘ pairFst) (active ∘ pairFst) pairSnd (inner ∘ pairFst) (outer ∘ pairFst)
      (fun q => n (pairFst q)) (fun q => d (pairFst q)) (fun q => ell (pairFst q)) where
  coordinates := D.coordinates.precomposeUniform pairFst pairFst_mem_FP
  bounds := D.bounds.precomposeUniform pairFst pairFst_mem_FP
  direction := D.direction ∘ Query.directionQuery
  sourceFP := mem_FP_comp pairFst_mem_FP D.sourceFP
  activeFP := mem_FP_comp pairFst_mem_FP D.activeFP
  modulusFP := pairSnd_mem_FP
  innerFP := mem_FP_comp pairFst_mem_FP D.innerFP
  outerFP := mem_FP_comp pairFst_mem_FP D.outerFP
  directionFP := mem_FP_comp Query.directionQuery_mem_FP D.directionFP
  direction_eq q i hi := by
    simp only [Function.comp_apply, Query.directionQuery, Query.base, pairFst_pair, pairSnd_pair]
    exact D.direction_eq (pairFst q) i hi

noncomputable def Data.residueEvaluator {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : SpaceFunction (residueValue source active inner outer n d ell D.bounds) :=
  D.withModulus.evaluator

end LeanCanny.ETR.TubeBivariate
