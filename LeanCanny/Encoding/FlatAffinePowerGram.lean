/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerGramSource

/-! # Native reciprocal Gram and all-root annihilator coefficients

Every source coefficient is computed from the original affine records. The
full-box determinant and fixed-degree reflection retain that reader's cost.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerGram
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] FlatAffinePowerPositive.system FlatAffinePowerPositive.degree

noncomputable def polynomial (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) : Polynomial ℤ :=
  AffineBoxGramEliminant.polynomial
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (FlatAffinePowerPositive.degree F c) (FlatAffinePowerControls.width F c) (coordinate c).succ

noncomputable def annihilator (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) : Polynomial ℤ :=
  AffineBoxGramEliminant.annihilator
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (FlatAffinePowerPositive.degree F c) (FlatAffinePowerControls.width F c) (coordinate c).succ

lemma annihilator_eq (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) :
    annihilator F coordinate c = AffineFiniteCoordinates.annihilator
      (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c) (coordinate c) := by
  unfold annihilator AffineFiniteCoordinates.annihilator
  rw [FlatAffinePowerGramLayout.width_eq]

lemma annihilator_degree_le (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) :
    (annihilator F coordinate c).natDegree ≤ FlatAffinePowerGramLayout.dimension F c + 1 :=
  AffineBoxGramEliminant.annihilator_degree_le _ _ _ _

noncomputable def value (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c))
    (modulus parameter : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((polynomial F coordinate c).coeff (Nat.fromBitsLE (parameter c)) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator {F : Inputs} (h : F.Access)
    (coordinate : (c : List Bool) → Fin (count F c)) (hc : UnaryFn (fun c => (coordinate c).val))
    {modulus parameter : List Bool → List Bool} (hm : modulus ∈ FP) (hk : parameter ∈ FP) :
    SpaceFunction (value F coordinate modulus parameter) := by
  let p := fun c => AffineBoxGramEliminant.liftedSystem
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (coordinate c).succ
  have E := MacaulayFullBoxBits.determinantEvaluator (FlatAffinePowerGramLayout.layout F)
    (FlatAffinePowerGramLayout.controls h) modulus (fun _ => []) parameter (fun _ => [])
    (FlatAffinePowerGramSource.value F coordinate modulus) p (FlatAffinePowerGramLayout.level_eq F)
    (fun c i e k => AffineBoxGramEliminant.inner_degree _ _ i e k)
    (fun c i r u v => FlatAffinePowerGramSource.value_packet F coordinate modulus c i r u v)
    (FlatAffinePowerGramSource.evaluator h coordinate hc hm) hm (constFn_mem_FP []) hk (constFn_mem_FP [])
  refine E.congr (funext fun c => ?_)
  rw [MacaulayFullBoxBits.determinantValue_eq]
  rw [FlatAffinePowerGramLayout.degrees_eq]
  change MacaulayFullBoxBits.scalar modulus c 0 (Nat.fromBitsLE (parameter c))
    (ProjectiveBoxGramEliminant.polynomial (p c) (AffineBoxGramEliminant.degrees (FlatAffinePowerPositive.degree F c))
      (FlatAffinePowerControls.width F c)) = _
  rw [show p c = AffineBoxGramEliminant.liftedSystem
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (coordinate c).succ from rfl, AffineBoxGramEliminant.polynomial_lift]
  simp only [MacaulayFullBoxBits.scalar, AffineBoxGramEliminant.lift_coefficient, ite_true]
  rfl

lemma polynomial_comp (F : Inputs) (f : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) :
    polynomial (FlatAffineFullSourceContext.comp F f) (fun q => coordinate (f q)) c = polynomial F coordinate (f c) := by
  have hs := funext (FlatAffinePowerPositive.system_comp F f c)
  have hd := funext (FlatAffinePowerPositive.degree_comp F f c)
  exact congrArg₂
    (fun p d => AffineBoxGramEliminant.polynomial (AffineFiniteCoordinates.homogeneousRows p d) d
      (FlatAffinePowerControls.width F (f c)) (coordinate (f c)).succ) hs hd

theorem coefficient_evaluator {F : Inputs} (h : F.Access)
    (coordinate : (c : List Bool) → Fin (count F c)) (hc : UnaryFn (fun c => (coordinate c).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F coordinate)) := by
  have hf := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have E := evaluator (FlatAffineFullSourceContext.access h hf)
    (fun q => coordinate (pairFst (pairFst q))) (hc.comp hf)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  refine E.congr (funext fun q => ?_)
  simp only [value, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg (fun p : Polynomial ℤ => residueBits
    ((p.coeff (Nat.fromBitsLE (pairSnd (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (polynomial_comp F (pairFst ∘ pairFst) coordinate q)

theorem annihilator_evaluator {F : Inputs} (h : F.Access)
    (coordinate : (c : List Bool) → Fin (count F c)) (hc : UnaryFn (fun c => (coordinate c).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (annihilator F coordinate)) :=
  AffineBoxGramEliminant.annihilator_evaluator (count F)
    (fun c => AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (FlatAffinePowerPositive.degree F) (FlatAffinePowerControls.width F) (fun c => (coordinate c).succ)
    (FlatAffinePowerGramLayout.dimension_binary h) (coefficient_evaluator h coordinate hc)

end LeanCanny.Encoding.FlatAffinePowerGram
