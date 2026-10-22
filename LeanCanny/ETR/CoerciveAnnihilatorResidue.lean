/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveHomogeneousReaderCorrect
public import LeanCanny.ETR.CoerciveAnnihilatorLayout

/-! # Native residues of the actual canonical coordinate annihilants -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveAnnihilatorResidue
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CoerciveSourceSampling.dimension
  CoerciveSourceSampling.polynomial Matrix.det MacaulayFullBox.matrix

noncomputable def oneValue (rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) :=
  if Nat.fromBitsLE (rootDegree c) = 0 ∧ Nat.fromBitsLE (parameterDegree c) = 0 then
    ArithmeticBits.one (BinaryNat.succ (modulus c)) else []

private lemma zeroFP {f : List Bool → List Bool} (hf : f ∈ FP) :
    FPPred (fun c => Nat.fromBitsLE (f c) = 0) :=
  (BinaryNat.le_fppred hf (constFn_mem_FP [])).of_iff (fun _ => by change _ ≤ 0 ↔ _; omega)

lemma oneValue_FP {rootDegree parameterDegree modulus : List Bool → List Bool}
    (hr : rootDegree ∈ FP) (hp : parameterDegree ∈ FP) (hm : modulus ∈ FP) : oneValue rootDegree parameterDegree modulus ∈ FP := by
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  exact mem_FP_of_eq (((zeroFP hr).and (zeroFP hp)).ite_mem_FP ho (constFn_mem_FP [])) (fun _ => rfl)

lemma oneValue_eq (rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) :
    oneValue rootDegree parameterDegree modulus c = residueBits
      (((((1 : Polynomial (Polynomial ℤ)).coeff (Nat.fromBitsLE (rootDegree c))).coeff
        (Nat.fromBitsLE (parameterDegree c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold oneValue
  rw [BinaryNat.succ_eq_bits]
  by_cases hr : Nat.fromBitsLE (rootDegree c) = 0 <;>
    by_cases hp : Nat.fromBitsLE (parameterDegree c) = 0
  · simpa only [hr, hp, and_self, ite_true, Polynomial.coeff_one_zero, Int.cast_one, BinaryNatCode.encode] using
      ArithmeticBits.one_residueBits (Nat.fromBitsLE (modulus c) + 1)
  all_goals simp [hr, hp, Polynomial.coeff_one, residueBits, BinaryNatCode.encode]

noncomputable def value (input rootDegree parameterDegree modulus : List Bool → List Bool)
    (coordinate : List Bool → ℕ) (c : List Bool) : List Bool :=
  if coordinate c < dimension (input c) then
    MacaulayFullBoxBits.determinantValue (CoerciveAnnihilatorLayout.layout input) modulus rootDegree parameterDegree
      (CoerciveAnnihilatorLayout.family input coordinate) c
  else oneValue rootDegree parameterDegree modulus c

lemma evaluator {input rootDegree parameterDegree modulus : List Bool → List Bool} {coordinate : List Bool → ℕ}
    (hi : input ∈ FP) (hr : rootDegree ∈ FP) (hp : parameterDegree ∈ FP) (hm : modulus ∈ FP)
    (hc : UnaryFn coordinate) : SpaceFunction (value input rootDegree parameterDegree modulus coordinate) := by
  have E := CoerciveHomogeneousRowReader.evaluator hi hm hc
  have hc_source : ∀ c (i : Fin ((CoerciveAnnihilatorLayout.layout input).arity c)) r u v,
      CoerciveHomogeneousRowReader.value input modulus coordinate
        (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r)
          (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      MacaulayFullBoxBits.scalar modulus c u v
        ((CoerciveAnnihilatorLayout.family input coordinate c i).coeff
          (RationalSubstitution.Indexed.exponentVector ((CoerciveAnnihilatorLayout.layout input).arity c)
            (FixedWidthPolynomial.entry ((CoerciveAnnihilatorLayout.layout input).width c) r))) := by
    intro c i r u v
    by_cases hv : coordinate c < dimension (input c)
    · rw [CoerciveAnnihilatorLayout.family, dite_eq_left hv]
      exact CoerciveHomogeneousReaderCorrect.value_packet input modulus coordinate c ⟨coordinate c,hv⟩ rfl r u v i
    · rw [CoerciveAnnihilatorLayout.family, dite_eq_right hv]
      simpa [MacaulayFullBoxBits.scalar, CoerciveHomogeneousReaderCorrect.word,
        residueBits, BinaryNatCode.encode] using
        CoerciveHomogeneousReaderCorrect.value_invalid input modulus coordinate c r u v hv i.val
  have ED := MacaulayFullBoxBits.determinantEvaluator (CoerciveAnnihilatorLayout.layout input)
    (CoerciveAnnihilatorLayout.controls hi) modulus rootDegree parameterDegree (fun _ => BinaryNatCode.encode 1)
    (CoerciveHomogeneousRowReader.value input modulus coordinate) (CoerciveAnnihilatorLayout.family input coordinate)
    (CoerciveAnnihilatorLayout.level_eq input)
    (fun c i e k => by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      CoerciveAnnihilatorLayout.family_inner_degree input coordinate c i e k)
    hc_source E hm hr hp (constFn_mem_FP _)
  have EB := SpaceFunction.branch (fun c => decide (coordinate c < dimension (input c)))
    (FPPred.lt hc (dimension_unary.comp hi)).flag_mem_FP ED (SpaceFunction.ofFP _ (oneValue_FP hr hp hm))
  exact EB.congr (funext fun c => by simp only [value, decide_eq_true_eq])

lemma value_eq (input rootDegree parameterDegree modulus : List Bool → List Bool)
    (coordinate : List Bool → ℕ) (c : List Bool) :
    value input rootDegree parameterDegree modulus coordinate c = residueBits
      (((((CoerciveAnnihilatorControls.original (input c) (coordinate c)).coeff
        (Nat.fromBitsLE (rootDegree c))).coeff (Nat.fromBitsLE (parameterDegree c))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  by_cases hc : coordinate c < dimension (input c)
  · rw [value, ite_eq_left hc, MacaulayFullBoxBits.determinantValue_eq,
      CoerciveAnnihilatorLayout.determinant_eq input coordinate c hc]
    rw [CoerciveAnnihilatorControls.original, dite_eq_left hc, CoerciveBoxGramEliminant.symbolic,
      PolynomialKronecker.swap_coefficient]
    rfl
  · rw [value, ite_eq_right hc, CoerciveAnnihilatorControls.original, dite_eq_right hc]
    exact oneValue_eq _ _ _ c

noncomputable def coefficient (input index rootDegree parameterDegree modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((((CoerciveAnnihilatorControls.original (input c) (Nat.fromBitsLE (index c))).coeff
    (Nat.fromBitsLE (rootDegree c))).coeff (Nat.fromBitsLE (parameterDegree c))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

private lemma original_clamp (bits : List Bool) (i : ℕ) :
    CoerciveAnnihilatorControls.original bits (min i (dimension bits)) = CoerciveAnnihilatorControls.original bits i := by
  by_cases hi : i < dimension bits
  · rw [min_eq_left hi.le]
  · rw [min_eq_right (Nat.le_of_not_lt hi)]
    simp only [CoerciveAnnihilatorControls.original, lt_self_iff_false, dite_false, hi]

/-- Both coordinate and coefficient degrees stay binary; no unary conversion
of an untrusted coordinate query is required. -/
theorem coefficientEvaluator {input index rootDegree parameterDegree modulus : List Bool → List Bool}
    (hi : input ∈ FP) (hj : index ∈ FP) (hr : rootDegree ∈ FP) (hp : parameterDegree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (coefficient input index rootDegree parameterDegree modulus) := by
  let coordinate := fun c => min (Nat.fromBitsLE (index c)) (dimension (input c))
  have hc : UnaryFn coordinate := UnaryFn.fromBitsLE_min hj (dimension_unary.comp hi)
  have E := evaluator hi hr hp hm hc
  refine E.congr (funext fun c => ?_)
  rw [value_eq]
  simp only [coefficient, coordinate, original_clamp]

end LeanCanny.ETR.CoerciveAnnihilatorResidue
