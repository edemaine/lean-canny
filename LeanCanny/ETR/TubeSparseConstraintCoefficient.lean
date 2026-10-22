/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSampleCoefficient
public import LeanCanny.Algebra.FixedWidthMonomial
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Sparse point, constant, and shift coefficient readers for tube constraints -/

@[expose] public section

namespace LeanCanny.ETR.TubeSparseConstraintCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding TubeProjectionEncoding MvPolynomial
open RationalSubstitution.Indexed MatrixPower
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet : List Bool → List Bool) (W : List Bool → ℕ) (target : List Bool → List Bool)
variable (row : (c : List Bool) → PerturbedSource.Index (pairFst (packet c)))

noncomputable def code (c : List Bool) : ℕ := (constraintEquiv (TubeSampleCoefficient.n packet c) (row c)).val
noncomputable def pointIndex (c : List Bool) : ℕ := (code packet row c - 2) / 2 + 2
noncomputable def shiftIndex (c : List Bool) : ℕ := (sampleIndex (packet c) (.inr (row c))).val

theorem shiftIndex_eq (c : List Bool) : shiftIndex packet row c = TubeSampleCoefficient.n packet c + code packet row c + 2 := rfl

theorem pointIndex_lt (c : List Bool) : pointIndex packet row c < TubeSampleCoefficient.A packet c := by
  have hr := (constraintEquiv (TubeSampleCoefficient.n packet c) (row c)).isLt
  change code packet row c < 2 + TubeSampleCoefficient.n packet c * 2 at hr
  change (code packet row c - 2) / 2 + 2 <
    TubeSampleCoefficient.n packet c + (2 + TubeSampleCoefficient.n packet c * 2) + 1 + 1
  omega

theorem shiftIndex_lt (c : List Bool) : shiftIndex packet row c < TubeSampleCoefficient.A packet c :=
  (sampleIndex (packet c) (.inr (row c))).isLt

noncomputable def point (c : List Bool) : Fin (TubeSampleCoefficient.A packet c) :=
  ⟨pointIndex packet row c, pointIndex_lt packet row c⟩

noncomputable def pointCoefficient (modulus : List Bool → List Bool) (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  ((X (point packet row c) : MvPolynomial _ ℤ).coeff (TubeSampleCoefficient.exponent packet W target c) : ℤ)

noncomputable def shiftCoefficient (modulus : List Bool → List Bool) (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  ((X (sampleIndex (packet c) (.inr (row c))) : MvPolynomial _ ℤ).coeff
    (TubeSampleCoefficient.exponent packet W target c) : ℤ)

noncomputable def constantCoefficient (modulus : List Bool → List Bool) (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  ((1 : MvPolynomial (Fin (TubeSampleCoefficient.A packet c)) ℤ).coeff
    (TubeSampleCoefficient.exponent packet W target c) : ℤ)

theorem pointIndex_unary (hr : UnaryFn (code packet row)) : UnaryFn (pointIndex packet row) :=
  ((hr.sub (UnaryFn.const 2)).div (UnaryFn.const 2)).add (UnaryFn.const 2)

theorem shiftIndex_unary (hp : packet ∈ FP) (hr : UnaryFn (code packet row)) : UnaryFn (shiftIndex packet row) := by
  apply (((TubeSampleCoefficient.n_unary packet hp).add hr).add (UnaryFn.const 2)).of_eq
  exact fun c => (shiftIndex_eq packet row c).symm

theorem pointEvaluator (modulus : List Bool → List Bool) (hp : packet ∈ FP) (hW : UnaryFn W)
    (ht : target ∈ FP) (hr : UnaryFn (code packet row)) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (pointCoefficient packet W target row modulus c)) := by
  let E := SpaceFunction.ofFP _ (FixedWidthMonomial.value_mem_FP (TubeSampleCoefficient.A packet) W
    (pointIndex packet row) target true modulus (TubeSampleCoefficient.A_unary packet hp) hW (pointIndex_unary packet row hr) ht hm)
  exact E.congr (funext fun c => FixedWidthMonomial.value_coefficient _ _ _ _ true modulus c (pointIndex_lt packet row c))

theorem shiftEvaluator (modulus : List Bool → List Bool) (hp : packet ∈ FP) (hW : UnaryFn W)
    (ht : target ∈ FP) (hr : UnaryFn (code packet row)) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (shiftCoefficient packet W target row modulus c)) := by
  let E := SpaceFunction.ofFP _ (FixedWidthMonomial.value_mem_FP (TubeSampleCoefficient.A packet) W
    (shiftIndex packet row) target true modulus (TubeSampleCoefficient.A_unary packet hp) hW (shiftIndex_unary packet row hp hr) ht hm)
  exact E.congr (funext fun c => FixedWidthMonomial.value_coefficient _ _ _ _ true modulus c (shiftIndex_lt packet row c))

theorem constantEvaluator (modulus : List Bool → List Bool) (hp : packet ∈ FP) (hW : UnaryFn W)
    (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (constantCoefficient packet W target modulus c)) := by
  have hA (c : List Bool) : 0 < TubeSampleCoefficient.A packet c := by
    unfold TubeSampleCoefficient.A TubeParameter.spatialCount
    omega
  let E := SpaceFunction.ofFP _ (FixedWidthMonomial.value_mem_FP (TubeSampleCoefficient.A packet) W
    (fun _ => 0) target false modulus (TubeSampleCoefficient.A_unary packet hp) hW (UnaryFn.const 0) ht hm)
  exact E.congr (funext fun c => FixedWidthMonomial.value_coefficient _ _ _ _ false modulus c (hA c))

noncomputable def sourceCoefficient (modulus : List Bool → List Bool) (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  (TubeSampleCoefficient.coefficient packet W target c : ℤ)

noncomputable def combined (modulus : List Bool → List Bool) (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  (if code packet row c < 2 then
    (if code packet row c = 0 then sourceCoefficient packet W target modulus c
      else -sourceCoefficient packet W target modulus c)
  else if code packet row c % 2 = 0 then pointCoefficient packet W target row modulus c + constantCoefficient packet W target modulus c
    else constantCoefficient packet W target modulus c - pointCoefficient packet W target row modulus c) +
      shiftCoefficient packet W target row modulus c

theorem combined_eq (modulus : List Bool → List Bool) (c : List Bool) :
    combined packet W target row modulus c =
      ((zeroMarginConstraint (packet c) (row c)).coeff (TubeSampleCoefficient.exponent packet W target c) : ℤ) := by
  dsimp +instances only [TubeSampleCoefficient.A, TubeSampleCoefficient.n, TubeIndexed.arity, TubeParameter.spatialCount, PerturbedSource.Index, TubeEncoding.Constraint] at *
  have hAdd (a b : ℤ) : (a : ZMod (ModularResidueSpace.m modulus c)) + (b : ZMod _) = ((a + b : ℤ) : ZMod _) :=
    (Int.cast_add a b).symm
  have hNeg (a b : ℤ) : -(a : ZMod (ModularResidueSpace.m modulus c)) + (b : ZMod _) = ((-a + b : ℤ) : ZMod _) := by simp
  have hAdd3 (a b d : ℤ) : (a : ZMod (ModularResidueSpace.m modulus c)) + (b : ZMod _) + (d : ZMod _) = ((a + b + d : ℤ) : ZMod _) := by simp
  have hSub (a b d : ℤ) : (a : ZMod (ModularResidueSpace.m modulus c)) - (b : ZMod _) + (d : ZMod _) = ((a - b + d : ℤ) : ZMod _) := by simp
  rcases hi : row c with b | ⟨j, b⟩ <;> cases b
  · have hc : code packet row c = 0 := by unfold code; rw [hi]; rfl
    simp [combined, hc, sourceCoefficient, shiftCoefficient, TubeSampleCoefficient.coefficient, hi, zeroMarginConstraint]
    exact hAdd _ _
  · have hc : code packet row c = 1 := by unfold code; rw [hi]; rfl
    simp [combined, hc, sourceCoefficient, shiftCoefficient, TubeSampleCoefficient.coefficient, hi, zeroMarginConstraint]
    exact hNeg _ _
  · have hc : code packet row c = 2 + 2 * j.val := by
      unfold code
      rw [hi]
      exact (constraintIndex_box _ j _).trans (by simp)
    have hp : point packet row c = sampleIndex (packet c) (.inl j) := by
      apply Fin.ext
      change (code packet row c - 2) / 2 + 2 = (sampleIndex (packet c) (.inl j)).val
      rw [hc]
      exact (by omega : _ = j.val + 2).trans (TubeSampleCoefficient.sampleIndex_point_val packet c j).symm
    have hsmall : ¬ code packet row c < 2 := by rw [hc]; omega
    have heven : code packet row c % 2 = 0 := by rw [hc]; omega
    simp only [combined, hsmall, heven, ite_false, ite_true]
    simp [pointCoefficient, hp, constantCoefficient, shiftCoefficient, hi, zeroMarginConstraint]
    exact hAdd3 _ _ _
  · have hc : code packet row c = 2 + 2 * j.val + 1 := by
      unfold code
      rw [hi]
      exact (constraintIndex_box _ j _).trans (by simp)
    have hp : point packet row c = sampleIndex (packet c) (.inl j) := by
      apply Fin.ext
      change (code packet row c - 2) / 2 + 2 = (sampleIndex (packet c) (.inl j)).val
      rw [hc]
      exact (by omega : _ = j.val + 2).trans (TubeSampleCoefficient.sampleIndex_point_val packet c j).symm
    have hsmall : ¬ code packet row c < 2 := by rw [hc]; omega
    have hodd : ¬ code packet row c % 2 = 0 := by rw [hc]; omega
    simp only [combined, hsmall, hodd, ite_false]
    simp [pointCoefficient, hp, constantCoefficient, shiftCoefficient, hi, zeroMarginConstraint]
    exact hSub _ _ _

theorem evaluator (modulus : List Bool → List Bool) (hp : packet ∈ FP) (hW : UnaryFn W)
    (ht : target ∈ FP) (hr : UnaryFn (code packet row)) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (((zeroMarginConstraint (packet c) (row c)).coeff
      (TubeSampleCoefficient.exponent packet W target c) : ℤ) : ZMod (ModularResidueSpace.m modulus c))) := by
  let C := TubeSampleCoefficient.evaluator packet W target modulus hp hW ht hm
  let P := pointEvaluator packet W target row modulus hp hW ht hr hm
  let K := constantEvaluator packet W target modulus hp hW ht hm
  let T := shiftEvaluator packet W target row modulus hp hW ht hr hm
  let NC := ModularResidueSpace.negEvaluator modulus (sourceCoefficient packet W target modulus) hm C
  let NP := ModularResidueSpace.negEvaluator modulus (pointCoefficient packet W target row modulus) hm P
  let ES := ModularResidueSpace.branchEvaluator modulus _ _ (fun c => code packet row c = 0)
    (FPPred.eq hr (UnaryFn.const 0)) C NC
  let LO := ModularResidueSpace.addEvaluator modulus _ _ hm P K
  have HI : SpaceFunction (fun c => residueBits (constantCoefficient packet W target modulus c -
      pointCoefficient packet W target row modulus c)) := by
    let E := ModularResidueSpace.addEvaluator modulus _ _ hm K NP
    exact E.congr (funext fun c => by rw [sub_eq_add_neg])
  let EB := ModularResidueSpace.branchEvaluator modulus _ _ (fun c => code packet row c % 2 = 0)
    (FPPred.eq (hr.mod (UnaryFn.const 2)) (UnaryFn.const 0)) LO HI
  let EQ := ModularResidueSpace.branchEvaluator modulus _ _ (fun c => code packet row c < 2)
    (FPPred.lt hr (UnaryFn.const 2)) ES EB
  let E := ModularResidueSpace.addEvaluator modulus _ _ hm EQ T
  refine E.congr (funext fun c => ?_)
  have he : residueBits ((if code packet row c < 2 then
      (if code packet row c = 0 then sourceCoefficient packet W target modulus c else -sourceCoefficient packet W target modulus c)
    else if code packet row c % 2 = 0 then pointCoefficient packet W target row modulus c + constantCoefficient packet W target modulus c
      else constantCoefficient packet W target modulus c - pointCoefficient packet W target row modulus c) +
        shiftCoefficient packet W target row modulus c) = residueBits (combined packet W target row modulus c) := rfl
  have hh := he.trans (congrArg residueBits (combined_eq packet W target row modulus c))
  dsimp +instances only [sourceCoefficient, ModularResidueSpace.m] at hh ⊢
  by_cases h0 : code packet row c = 0 <;> by_cases h2 : code packet row c < 2 <;>
    by_cases heven : code packet row c % 2 = 0 <;>
    simp only [h0, h2, heven, ite_true, ite_false] at hh ⊢ <;> exact hh

end LeanCanny.ETR.TubeSparseConstraintCoefficient
