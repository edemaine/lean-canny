/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairSeparableSpace
public import LeanCanny.Algebra.PrimitivePairConstruction
public import LeanCanny.Computation.BoundedChoice

/-! # Selecting a separating direction in polynomial space

Candidate directions range from zero through the square of the root-pair
degree. Every candidate is tested by the actual integer resultant and its
derivative. Only source coefficient readers and FP degree/height controls are
assumed; all intermediate coefficient readers and height budgets are derived.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical
attribute [local irreducible] BinaryNat.mul BinaryNat.normalize

def Source.candidates (S : Source) : Source where
  left q := S.left (pairFst q)
  right q := S.right (pairFst q)
  direction q := Nat.fromBitsLE (pairSnd q)

def candidateCoefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (context q)) (selectedDegree q)) (pairSnd q)

theorem candidateCoefficientQuery_FP : candidateCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def Readers.candidates (S : Source) (A : Readers S) : Readers S.candidates where
  leftDegree := A.leftDegree ∘ pairFst
  rightDegree := A.rightDegree ∘ pairFst
  direction := BinaryNat.normalize ∘ pairSnd
  leftDegreeFP := mem_FP_comp pairFst_mem_FP A.leftDegreeFP
  rightDegreeFP := mem_FP_comp pairFst_mem_FP A.rightDegreeFP
  directionFP := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  leftDegree_eq _ := A.leftDegree_eq _
  rightDegree_eq _ := A.rightDegree_eq _
  direction_eq _ := BinaryNat.normalize_eq_bits _
  leftEvaluator := (A.leftEvaluator.precompose candidateCoefficientQuery candidateCoefficientQuery_FP).congr
    (funext fun q => by
      simp only [Function.comp_apply, coefficient, candidateCoefficientQuery, context,
        selectedDegree, mValue, pairFst_pair, pairSnd_pair, Source.candidates])
  rightEvaluator := (A.rightEvaluator.precompose candidateCoefficientQuery candidateCoefficientQuery_FP).congr
    (funext fun q => by
      simp only [Function.comp_apply, coefficient, candidateCoefficientQuery, context,
        selectedDegree, mValue, pairFst_pair, pairSnd_pair, Source.candidates])

def Heights.candidates (S : Source) (H : Heights S) : Heights S.candidates where
  leftBits := H.leftBits ∘ pairFst
  rightBits := H.rightBits ∘ pairFst
  leftBitsFP := mem_FP_comp pairFst_mem_FP H.leftBitsFP
  rightBitsFP := mem_FP_comp pairFst_mem_FP H.rightBitsFP
  left_bound _ k := H.left_bound _ k
  right_bound _ k := H.right_bound _ k

def candidateCount (S : Source) (A : Readers S) (c : List Bool) : List Bool :=
  let d := BinaryNat.mul (pair (A.leftDegree c) (A.rightDegree c))
  BinaryNat.succ (BinaryNat.mul (pair d d))

theorem candidateCount_FP (S : Source) (A : Readers S) : candidateCount S A ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair A.leftDegreeFP A.rightDegreeFP) BinaryNat.mul_mem_FP
  have hs := mem_FP_comp (mem_FP_pair hd hd) BinaryNat.mul_mem_FP
  have h := mem_FP_comp hs BinaryNat.succ_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem candidateCount_eq (S : Source) (A : Readers S) (c : List Bool) :
    candidateCount S A c = BinaryNatCode.encode (((S.left c).natDegree * (S.right c).natDegree) ^ 2 + 1) := by
  simp only [candidateCount, A.leftDegree_eq, A.rightDegree_eq, BinaryNat.mul_pair,
    BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, pow_two]

def separatingLanguage (S : Source) : Language :=
  {q | ((cannyResultant (S.left (pairFst q)) (S.right (pairFst q))
    (Nat.fromBitsLE (pairSnd q))).map (Int.castRingHom ℚ)).Separable}

noncomputable def selectedDirection (S : Source) (A : Readers S) (c : List Bool) : ℕ :=
  BoundedChoice.search (separatingLanguage S) c (Nat.fromBitsLE (candidateCount S A c)) - 1

theorem selectedDirection_eq (S : Source) (A : Readers S) (c : List Bool) :
    selectedDirection S A c = PrimitivePair.select (S.left c) (S.right c) := by
  unfold selectedDirection PrimitivePair.select
  rw [candidateCount_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  apply BoundedChoice.search_congr
  intro k _
  simp only [separatingLanguage, PrimitivePair.candidateLanguage, Set.mem_ofPred_eq,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

section Correctness
variable {L : Type*} [Field L] [CharZero L]

theorem selectedDirection_spec (S : Source) (A : Readers S) (c : List Bool)
    (hp : ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ((S.right c).map (Int.castRingHom L)).Splits) :
    selectedDirection S A c ≤ ((S.left c).natDegree * (S.right c).natDegree) ^ 2 ∧
      Set.InjOn (shear (selectedDirection S A c))
        (rootPairs (L := L) ((S.left c).map (Int.castRingHom L))
          ((S.right c).map (Int.castRingHom L)) : Set (L × L)) := by
  simpa only [selectedDirection_eq] using PrimitivePair.select_spec (S.left c) (S.right c) hp hq hsp hsq

theorem selectedDirectionEvaluator (S : Source) (A : Readers S) (H : Heights S)
    (hp : ∀ c, ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ∀ c, ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ∀ c, ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ∀ c, ((S.right c).map (Int.castRingHom L)).Splits) :
    SpaceFunction (fun c => BinaryNatCode.encode (selectedDirection S A c)) := by
  have hd : ∀ w, (cannyResultant (S.candidates.left w) (S.candidates.right w) (S.candidates.direction w)).natDegree =
      (S.candidates.left w).natDegree * (S.candidates.right w).natDegree :=
    fun w => PrimitivePair.resultant_natDegree _ _ _ (hp (pairFst w)) (hq _) (hsp _) (hsq _)
  have hn : ∀ w, cannyResultant (S.candidates.left w) (S.candidates.right w) (S.candidates.direction w) ≠ 0 :=
    fun w => PrimitivePair.integer_resultant_ne_zero _ _ _ (hp (pairFst w)) (hq _) (hsp _) (hsq _)
  have D := separabilityDecider S.candidates (A.candidates S) (H.candidates S) hd hn
  exact BoundedChoice.evaluator D (candidateCount S A) (candidateCount_FP S A)

end Correctness
end LeanCanny.Algebra.PrimitivePairBits
