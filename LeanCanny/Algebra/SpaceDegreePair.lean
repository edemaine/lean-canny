/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairReaders
public import LeanCanny.Algebra.PreparedPolynomialContext
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Canonical pair coordinates with space-computed source degrees

Already separable inputs need no further square-free preprocessing. Degrees
are computed into checked packets, making the existing FP metadata interface
exact on every word. Source residues and degree computations may use arbitrary
time in polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.SpaceDegreePair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family)
open PreprocessedPair (leftContext rightContext leftContext_FP rightContext_FP query query_FP)
open RationalSubstitution.IntegerBits (context selectedDegree mValue)

noncomputable def source (F G : Family) : PrimitivePairBits.Source where
  left c := ValidatedDegreeBits.checked F.polynomial (leftContext c)
  right c := ValidatedDegreeBits.checked G.polynomial (rightContext c)
  direction _ := 0

theorem checkedEvaluator (F : Family) (E : SpaceFunction (PrimitivePairBits.coefficient F.polynomial))
    (D : SpaceFunction (fun c => BinaryNatCode.encode (F.polynomial c).natDegree)) :
    SpaceFunction (ValidatedDegreeBits.coefficient (ValidatedDegreeBits.checked F.polynomial)) := by
  have R := E.precompose PrimitivePairBits.modularCoefficientQuery PrimitivePairBits.modularCoefficientQuery_FP
  have R' : SpaceFunction (ValidatedDegreeBits.coefficient F.polynomial) := R.congr (funext fun q => by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, PrimitivePairBits.modularCoefficientQuery,
      context, selectedDegree, mValue, pairFst_pair, pairSnd_pair, ValidatedDegreeBits.coefficient,
      ValidatedDegreeBits.context, ValidatedDegreeBits.modulus]
    rfl)
  exact ValidatedDegreeBits.evaluator F.polynomial R' D

attribute [local irreducible] BinaryNat.normalize

noncomputable def readers (F G : Family)
    (EF : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) (EG : SpaceFunction (PrimitivePairBits.coefficient G.polynomial))
    (DF : SpaceFunction (fun c => BinaryNatCode.encode (F.polynomial c).natDegree))
    (DG : SpaceFunction (fun c => BinaryNatCode.encode (G.polynomial c).natDegree)) : PrimitivePairBits.Readers (source F G) where
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
  leftEvaluator := ((checkedEvaluator F EF DF).precompose (query leftContext) (query_FP leftContext_FP)).congr
    (funext fun q => by
      simp only [Function.comp_apply, ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context,
        ValidatedDegreeBits.modulus, query, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient, source,
        context, selectedDegree, mValue]
      rfl)
  rightEvaluator := ((checkedEvaluator G EG DG).precompose (query rightContext) (query_FP rightContext_FP)).congr
    (funext fun q => by
      simp only [Function.comp_apply, ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context,
        ValidatedDegreeBits.modulus, query, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient, source,
        context, selectedDegree, mValue]
      rfl)

noncomputable def heights (F G : Family) (HF : BinaryFn F.height) (HG : BinaryFn G.height) : PrimitivePairBits.Heights (source F G) where
  leftBits c := BinaryNatCode.encode (F.height (pairFst c))
  rightBits c := BinaryNatCode.encode (G.height (pairFst c))
  leftBitsFP := mem_FP_comp pairFst_mem_FP HF.bits_mem_FP
  rightBitsFP := mem_FP_comp pairFst_mem_FP HG.bits_mem_FP
  left_bound c k := by
    simpa only [source, leftContext, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      ValidatedDegreeBits.checked_bound F.polynomial F.height F.coefficient_bound (leftContext c) k
  right_bound c k := by
    simpa only [source, rightContext, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      ValidatedDegreeBits.checked_bound G.polynomial G.height G.coefficient_bound (rightContext c) k

noncomputable def prepare (F G : Family) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (F.polynomial c).natDegree) (BinaryNatCode.encode (G.polynomial c).natDegree))

theorem prepareEvaluator (F G : Family)
    (DF : SpaceFunction (fun c => BinaryNatCode.encode (F.polynomial c).natDegree))
    (DG : SpaceFunction (fun c => BinaryNatCode.encode (G.polynomial c).natDegree)) : SpaceFunction (prepare F G) :=
  (DF.pairOutputs DG).withInput

theorem left_packet (F G : Family) (c : List Bool) : (source F G).left (prepare F G c) = F.polynomial c := by
  simp only [source, prepare, leftContext, pairFst_pair, pairSnd_pair]
  exact ValidatedDegreeBits.checked_packet F.polynomial c

theorem right_packet (F G : Family) (c : List Bool) : (source F G).right (prepare F G c) = G.polynomial c := by
  simp only [source, prepare, rightContext, pairFst_pair, pairSnd_pair]
  exact ValidatedDegreeBits.checked_packet G.polynomial c

theorem coordinateEvaluators (F G : Family)
    (EF : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) (EG : SpaceFunction (PrimitivePairBits.coefficient G.polynomial))
    (DF : SpaceFunction (fun c => BinaryNatCode.encode (F.polynomial c).natDegree))
    (DG : SpaceFunction (fun c => BinaryNatCode.encode (G.polynomial c).natDegree))
    (HF : BinaryFn F.height) (HG : BinaryFn G.height)
    (hF : ∀ c, ((F.polynomial c).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable)
    (hG : ∀ c, ((G.polynomial c).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => PrimitivePair.leftNumerator (F.polynomial c) (G.polynomial c)
      (PrimitivePair.select (F.polynomial c) (G.polynomial c)))) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun c => PrimitivePair.rightNumerator (F.polynomial c) (G.polynomial c)
      (PrimitivePair.select (F.polynomial c) (G.polynomial c)))) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun c => PrimitivePair.denominator (F.polynomial c) (G.polynomial c)
      (PrimitivePair.select (F.polynomial c) (G.polynomial c)))) := by
  let A := readers F G EF EG DF DG
  have hp (c : List Bool) : (((source F G).left c).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable :=
    ValidatedDegreeBits.checked_separable F.polynomial hF (leftContext c)
  have hq (c : List Bool) : (((source F G).right c).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable :=
    ValidatedDegreeBits.checked_separable G.polynomial hG (rightContext c)
  have E := PrimitivePairBits.selectedCoordinateEvaluators (source F G) A (heights F G HF HG) hp hq
    (fun _ => IsAlgClosed.splits _) (fun _ => IsAlgClosed.splits _)
  have P := prepareEvaluator F G DF DG
  refine ⟨?_, ?_, ?_⟩
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.1
    exact Q.congr (funext fun q => by
      simp only [PrimitivePairBits.coefficient, Function.comp_apply, PrimitivePairBits.selectedDirection_eq, left_packet, right_packet])
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.2.1
    exact Q.congr (funext fun q => by
      simp only [PrimitivePairBits.coefficient, Function.comp_apply, PrimitivePairBits.selectedDirection_eq, left_packet, right_packet])
  · have Q := PrimitivePairBits.withContextEvaluator _ (prepare F G) P E.2.2
    exact Q.congr (funext fun q => by
      simp only [PrimitivePairBits.coefficient, Function.comp_apply, PrimitivePairBits.selectedDirection_eq, left_packet, right_packet])

end LeanCanny.Algebra.SpaceDegreePair
