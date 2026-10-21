/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateQuery

/-! # Complete source access for the full bivariate tube matrix

Only parameter-coordinate readers and an FP reader for integer direction
entries are supplied. The row branch, both zero-degree guards, regular source
coefficients, exponent-width conversion and linear coefficient sum are internal.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm rawLinear TubeCleared.rawCoefficient rowCoefficient
attribute [local irreducible] TubeCleared.uniformDegree

theorem zero_fppred {f : List Bool → List Bool} (hf : f ∈ FP) : FPPred (fun q => Nat.fromBitsLE (f q) = 0) :=
  (BinaryNat.le_fppred hf (constFn_mem_FP [])).of_iff (fun q => by
    change Nat.fromBitsLE (f q) ≤ 0 ↔ Nat.fromBitsLE (f q) = 0
    omega)

noncomputable def sourceValue (source active modulus : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (Query.rowCode q) = 0 then
    if Nat.fromBitsLE (Query.innerCode q) = 0 then Query.linearValue source modulus ell q else []
  else if Nat.fromBitsLE (Query.outerCode q) = 0 then Query.regularValue source active modulus n d q else []

theorem sourceEvaluator (source active modulus read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (C : TubeParameter.CoordinateReaders source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) (he : read ∈ FP)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    SpaceFunction (sourceValue source active modulus n d ell) := by
  have EZ := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have EL := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (Query.innerCode q) = 0))
    (zero_fppred Query.innerCode_mem_FP).flag_mem_FP (Query.linearEvaluator source modulus read ell hs hm he hr) EZ
  have ER := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (Query.outerCode q) = 0))
    (zero_fppred Query.outerCode_mem_FP).flag_mem_FP (Query.regularEvaluator source active modulus n d C hs ha hm) EZ
  have ES := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (Query.rowCode q) = 0))
    (zero_fppred Query.rowCode_mem_FP).flag_mem_FP EL ER
  exact ES.congr (funext fun q => by simp only [sourceValue, decide_eq_true_eq])

theorem source_packet (source active modulus : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : Fin (TubeParameter.spatialCount (source c))) (k u v : ℕ) :
    sourceValue source active modulus n d ell (Query.packet c i.val k u v) =
      IntegerBits.coefficientResidue (rowCoefficient source active n d ell c i k u v) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [sourceValue]
  simp only [Query.rowCode_packet, Query.innerCode_packet, Query.outerCode_packet, MacaulayBits.fromBits_encode]
  by_cases hi : i.val = 0
  · rw [ite_eq_left hi, linear_coefficient source active n d ell c i k u v hi]
    by_cases hu : u = 0
    · rw [ite_eq_left hu, ite_eq_left hu, Query.linear_packet]
    · rw [ite_eq_right hu, ite_eq_right hu]
      simp [IntegerBits.coefficientResidue, residueBits, BinaryNatCode.encode]
  · rw [ite_eq_right hi, regular_coefficient source active n d ell c i k u v hi]
    by_cases hv : v = 0
    · rw [ite_eq_left hv, ite_eq_left hv, Query.regular_packet]
    · rw [ite_eq_right hv, ite_eq_right hv]
      simp [IntegerBits.coefficientResidue, residueBits, BinaryNatCode.encode]

noncomputable def access (source active modulus inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) :
    MacaulayBivariate.Access (family source active modulus inner outer n d ell B) where
  modulus := BinaryNat.succ ∘ modulus
  inner := BinaryNat.normalize ∘ inner
  outer := BinaryNat.normalize ∘ outer
  bound := BinaryNat.normalize ∘ TubeCleared.uniformDegree source B.degree
  coefficient := sourceValue source active modulus n d ell
  modulus_eq c := BinaryNat.succ_eq_bits (modulus c)
  inner_eq c := BinaryNat.normalize_eq_bits (inner c)
  outer_eq c := BinaryNat.normalize_eq_bits (outer c)
  bound_eq c := BinaryNat.normalize_eq_bits (TubeCleared.uniformDegree source B.degree c)
  coefficient_eq c i k u v := by
    change Fin (TubeParameter.spatialCount (source c)) at i
    change sourceValue source active modulus n d ell (Query.packet c i.val k u v) =
      residueBits (((((rows source active n d ell c i).map (reduction (Nat.fromBitsLE (modulus c) + 1))).coeff
        (Indexed.exponentVector (TubeParameter.spatialCount (source c))
          (FixedWidthPolynomial.entry (TubeCleared.matrixWidth (source c)) k))).coeff v).coeff u)
    rw [source_packet, reduction_coefficient]
    unfold IntegerBits.coefficientResidue rowCoefficient
    rfl

end LeanCanny.ETR.TubeBivariate
