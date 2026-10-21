/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ValidatedPolynomialDegree
public import LeanCanny.Algebra.PrimitivePairSelected

/-! # Total primitive-pair inputs after square-free preprocessing

Both actual square-free degrees are computed in space and stored with the
original context. Validation supplies exact FP degree fields on every input,
including malformed packets. Correctly prepared inputs retain both original
square-free polynomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.PreprocessedPair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
attribute [local irreducible] BinaryNat.normalize

noncomputable def reduced (F : Family) (c : List Bool) : ℤ[X] := ScaledSquarefree.polynomial (F.polynomial c)
def leftContext (c : List Bool) : List Bool := pair (pairFst c) (pairFst (pairSnd c))
def rightContext (c : List Bool) : List Bool := pair (pairFst c) (pairSnd (pairSnd c))

theorem leftContext_FP : leftContext ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightContext_FP : rightContext ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (F G : Family) : PrimitivePairBits.Source where
  left c := ValidatedDegreeBits.checked (reduced F) (leftContext c)
  right c := ValidatedDegreeBits.checked (reduced G) (rightContext c)
  direction _ := 0

def query (project : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (project (context q)) (pairSnd q)) (selectedDegree q)

theorem query_FP {project : List Bool → List Bool} (hp : project ∈ FP) : query project ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hp) pairSnd_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP

theorem checkedEvaluator (F : Family) (A : Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    SpaceFunction (ValidatedDegreeBits.coefficient (ValidatedDegreeBits.checked (reduced F))) := by
  have E : SpaceFunction (ValidatedDegreeBits.coefficient (reduced F)) :=
    (SeparableBits.squarefreeEvaluator F A).congr (funext fun _ => rfl)
  exact ValidatedDegreeBits.evaluator (reduced F) E (SeparableBits.scaledSquarefreeDegreeEvaluator F A hne)

noncomputable def readers (F G : Family) (A : Readers F) (B : Readers G)
    (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0) : PrimitivePairBits.Readers (source F G) where
  leftDegree c := BinaryNat.normalize (pairFst (pairSnd c))
  rightDegree c := BinaryNat.normalize (pairSnd (pairSnd c))
  direction _ := []
  leftDegreeFP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP
  rightDegreeFP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  directionFP := constFn_mem_FP []
  leftDegree_eq c := by
    simp only [BinaryNat.normalize_eq_bits, source, ValidatedDegreeBits.checked_degree, leftContext, pairSnd_pair]
    rfl
  rightDegree_eq c := by
    simp only [BinaryNat.normalize_eq_bits, source, ValidatedDegreeBits.checked_degree, rightContext, pairSnd_pair]
    rfl
  direction_eq _ := rfl
  leftEvaluator := ((checkedEvaluator F A hF).precompose (query leftContext) (query_FP leftContext_FP)).congr
    (funext fun q => by
      simp only [Function.comp_apply, ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context,
        ValidatedDegreeBits.modulus, query, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient, source,
        context, selectedDegree, mValue]
      rfl)
  rightEvaluator := ((checkedEvaluator G B hG).precompose (query rightContext) (query_FP rightContext_FP)).congr
    (funext fun q => by
      simp only [Function.comp_apply, ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context,
        ValidatedDegreeBits.modulus, query, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient, source,
        context, selectedDegree, mValue]
      rfl)

noncomputable def heights (F G : Family) (A : Readers F) (B : Readers G) : PrimitivePairBits.Heights (source F G) where
  leftBits := SeparableBits.squarefreeBudgetCode F A ∘ pairFst
  rightBits := SeparableBits.squarefreeBudgetCode G B ∘ pairFst
  leftBitsFP := mem_FP_comp pairFst_mem_FP (SeparableBits.squarefreeBudgetCode_FP F A)
  rightBitsFP := mem_FP_comp pairFst_mem_FP (SeparableBits.squarefreeBudgetCode_FP G B)
  left_bound c k := by
    have h := ValidatedDegreeBits.checked_bound (reduced F)
      (fun c => Nat.fromBitsLE (SeparableBits.squarefreeBudgetCode F A c))
      (SeparableBits.squarefree_coefficient_bound F A) (leftContext c) k
    simpa only [Function.comp_apply, source, leftContext, pairFst_pair] using h
  right_bound c k := by
    have h := ValidatedDegreeBits.checked_bound (reduced G)
      (fun c => Nat.fromBitsLE (SeparableBits.squarefreeBudgetCode G B c))
      (SeparableBits.squarefree_coefficient_bound G B) (rightContext c) k
    simpa only [Function.comp_apply, source, rightContext, pairFst_pair] using h

noncomputable def prepare (F G : Family) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (reduced F c).natDegree) (BinaryNatCode.encode (reduced G c).natDegree))

theorem prepareEvaluator (F G : Family) (A : Readers F) (B : Readers G)
    (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0) : SpaceFunction (prepare F G) :=
  ((SeparableBits.scaledSquarefreeDegreeEvaluator F A hF).pairOutputs
    (SeparableBits.scaledSquarefreeDegreeEvaluator G B hG)).withInput

theorem left_packet (F G : Family) (c : List Bool) : (source F G).left (prepare F G c) = reduced F c := by
  simp only [source, prepare, leftContext, pairFst_pair, pairSnd_pair]
  exact ValidatedDegreeBits.checked_packet (reduced F) c

theorem right_packet (F G : Family) (c : List Bool) : (source F G).right (prepare F G c) = reduced G c := by
  simp only [source, prepare, rightContext, pairFst_pair, pairSnd_pair]
  exact ValidatedDegreeBits.checked_packet (reduced G) c

theorem left_separable {L : Type*} [Field L] [CharZero L] (F G : Family)
    (hF : ∀ c, F.polynomial c ≠ 0) (c : List Bool) :
    (((source F G).left c).map (Int.castRingHom L)).Separable :=
  ValidatedDegreeBits.checked_separable (reduced F) (fun c => ScaledSquarefree.separable_in_field _ (hF c)) (leftContext c)

theorem right_separable {L : Type*} [Field L] [CharZero L] (F G : Family)
    (hG : ∀ c, G.polynomial c ≠ 0) (c : List Bool) :
    (((source F G).right c).map (Int.castRingHom L)).Separable :=
  ValidatedDegreeBits.checked_separable (reduced G) (fun c => ScaledSquarefree.separable_in_field _ (hG c)) (rightContext c)

end LeanCanny.Algebra.PreprocessedPair
