/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NoInfinitySquareGramSource

/-! # Native reciprocal Gram and all-root annihilator coefficients

Every source coefficient is computed from the literal original rows. The
full-box determinant and fixed-degree reflection retain that reader's cost.
-/

@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareGram
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open NoInfinitySquareSample (Family)
open scoped Classical

noncomputable def polynomial (F : Family) (coordinate : (c : List Bool) → Fin (F.count c)) (c : List Bool) : Polynomial ℤ :=
  AffineBoxGramEliminant.polynomial
    (AffineFiniteCoordinates.homogeneousRows (F.rows c) ((fun i=>F.rowDegree c i.val)))
    ((fun i=>F.rowDegree c i.val)) (NoInfinitySquareSample.width F c) (coordinate c).succ

noncomputable def annihilator (F : Family) (coordinate : (c : List Bool) → Fin (F.count c)) (c : List Bool) : Polynomial ℤ :=
  AffineBoxGramEliminant.annihilator
    (AffineFiniteCoordinates.homogeneousRows (F.rows c) ((fun i=>F.rowDegree c i.val)))
    ((fun i=>F.rowDegree c i.val)) (NoInfinitySquareSample.width F c) (coordinate c).succ

lemma annihilator_eq (F : Family) (coordinate : (c : List Bool) → Fin (F.count c)) (c : List Bool) :
    annihilator F coordinate c=NoInfinitySquareSample.polynomial F c (coordinate c) := rfl

lemma annihilator_degree_le (F : Family) (coordinate : (c : List Bool) → Fin (F.count c)) (c : List Bool) :
    (annihilator F coordinate c).natDegree ≤ NoInfinitySquareSample.dimension F c + 1 :=
  AffineBoxGramEliminant.annihilator_degree_le _ _ _ _

noncomputable def value (F : Family) (coordinate : (c : List Bool) → Fin (F.count c))
    (modulus parameter : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((polynomial F coordinate c).coeff (Nat.fromBitsLE (parameter c)) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator {F : Family} (h : NoInfinitySquareSample.Access F)
    (coordinate : (c : List Bool) → Fin (F.count c)) (hc : UnaryFn (fun c => (coordinate c).val))
    {modulus parameter : List Bool → List Bool} (hm : modulus ∈ FP) (hk : parameter ∈ FP) :
    SpaceFunction (value F coordinate modulus parameter) := by
  let p := fun c => AffineBoxGramEliminant.liftedSystem
    (AffineFiniteCoordinates.homogeneousRows (F.rows c) ((fun i=>F.rowDegree c i.val)))
    (coordinate c).succ
  have E := MacaulayFullBoxBits.determinantEvaluator (NoInfinitySquareSample.layout F)
    (NoInfinitySquareSample.controls h) modulus (fun _ => []) parameter (fun _ => [])
    (NoInfinitySquareGramSource.value F coordinate modulus) p (NoInfinitySquareSample.level_eq F)
    (fun c i e k => AffineBoxGramEliminant.inner_degree _ _ i e k)
    (fun c i r u v => NoInfinitySquareGramSource.value_packet F coordinate modulus c i r u v)
    (NoInfinitySquareGramSource.evaluator h coordinate hc hm) hm (constFn_mem_FP []) hk (constFn_mem_FP [])
  refine E.congr (funext fun c => ?_)
  rw [MacaulayFullBoxBits.determinantValue_eq]
  rw [NoInfinitySquareSample.degrees_eq]
  change MacaulayFullBoxBits.scalar modulus c 0 (Nat.fromBitsLE (parameter c))
    (ProjectiveBoxGramEliminant.polynomial (p c) (AffineBoxGramEliminant.degrees ((fun i=>F.rowDegree c i.val)))
      (NoInfinitySquareSample.width F c)) = _
  rw [show p c = AffineBoxGramEliminant.liftedSystem
    (AffineFiniteCoordinates.homogeneousRows (F.rows c) ((fun i=>F.rowDegree c i.val)))
    (coordinate c).succ from rfl, AffineBoxGramEliminant.polynomial_lift]
  simp only [MacaulayFullBoxBits.scalar, AffineBoxGramEliminant.lift_coefficient, ite_true]
  rfl

lemma polynomial_comp (F : Family) (f : List Bool→List Bool)
    (coordinate : (c : List Bool)→Fin (F.count c)) (c : List Bool) :
    polynomial (NoInfinitySquareSample.comp F f) (fun q=>coordinate (f q)) c=polynomial F coordinate (f c) := rfl

theorem coefficient_evaluator {F : Family} (h : NoInfinitySquareSample.Access F)
    (coordinate : (c : List Bool) → Fin (F.count c)) (hc : UnaryFn (fun c => (coordinate c).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F coordinate)) := by
  have hf := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have E := evaluator (NoInfinitySquareSample.access_comp h hf)
    (fun q => coordinate (pairFst (pairFst q))) (hc.comp hf)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  refine E.congr (funext fun q => ?_)
  simp only [value, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg (fun p : Polynomial ℤ => residueBits
    ((p.coeff (Nat.fromBitsLE (pairSnd (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (polynomial_comp F (pairFst ∘ pairFst) coordinate q)

theorem annihilator_evaluator {F : Family} (h : NoInfinitySquareSample.Access F)
    (coordinate : (c : List Bool) → Fin (F.count c)) (hc : UnaryFn (fun c => (coordinate c).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (annihilator F coordinate)) :=
  AffineBoxGramEliminant.annihilator_evaluator (F.count)
    (fun c => AffineFiniteCoordinates.homogeneousRows (F.rows c) ((fun i=>F.rowDegree c i.val)))
    (fun c i=>F.rowDegree c i.val) (NoInfinitySquareSample.width F) (fun c => (coordinate c).succ)
    (NoInfinitySquareSample.dimension_binary h) (coefficient_evaluator h coordinate hc)

end LeanCanny.Encoding.NoInfinitySquareGram
