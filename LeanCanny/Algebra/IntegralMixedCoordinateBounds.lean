/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedVirtualBounds
public import LeanCanny.Algebra.IntegralMixedGlobalHeightBounds

/-! # Native original-source heights for relative coordinate cuts

Bank heights and original integer source/syntax bounds derive every raw
coordinate-cut coefficient bound. The one extra nilpotent digit changes
the retained rank, while the spatial degree remains the original degree.
The budget has a native binary computation using metadata alone; no
coefficient or leading reader is supplied to justify that computation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualBounds
open scoped Classical

def inputFactor (n S L : ℕ) : ℕ := (n + 2) * IntegralMixedGlobalHeightBounds.expressionFactor S L

def height (n M W D S L G : ℕ) : ℕ :=
  IntegralCriticalFactorCeiling.factor (n + 1) M W D * (inputFactor n S L * G)

theorem height_binary {n M W D S L G : List Bool → ℕ}
    (hn : UnaryFn n) (hM : BinaryFn M) (hW : UnaryFn W) (hD : BinaryFn D)
    (hS : BinaryFn S) (hL : BinaryFn L) (hG : BinaryFn G) :
    BinaryFn (fun q => height (n q) (M q) (W q) (D q) (S q) (L q) (G q)) :=
  (IntegralCriticalFactorCeiling.factor_binary (hn.add (UnaryFn.const 1)) hM hW hD).mul
    ((((BinaryFn.ofUnary hn).add (BinaryFn.const 2)).mul
      (((hL.add (BinaryFn.const 1)).mul (hS.add (BinaryFn.const 3))))).mul hG)

theorem scaleHeight_scaled {n : ℕ} (r : Rule n) (m S L C G : ℕ)
    (hm : m ≤ S) (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    scaleHeight m G r ≤ IntegralMixedGlobalHeightBounds.expressionFactor S L * G := by
  have HB := IntegralMixedGlobalHeightBounds.scaleBudget_le r.critical C hScale
  have HE : S + 1 ≤ IntegralMixedGlobalHeightBounds.expressionFactor S L := by
    unfold IntegralMixedGlobalHeightBounds.expressionFactor
    nlinarith
  unfold scaleHeight
  nlinarith

theorem retainedHeight_scaled {n : ℕ} (r : Rule n) (m S L C G : ℕ)
    (hm : m ≤ S) (hL : ∀ i, (r.critical.heights i).nodes ≤ L)
    (hE : ∀ i, (r.critical.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C)
    (hSlope : r.slope.natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    retainedHeight m G r ≤ inputFactor n S L * G := by
  have HR := IntegralMixedGlobalHeightBounds.retainedBudget_scaled r.critical m S L C G hm hL hE hG
  have HS := scaleHeight_scaled r m S L C G hm hScale hG
  have HE := IntegralMixedGlobalHeightBounds.expressionFactor_pos S L
  unfold retainedHeight inputFactor
  apply max_le <;> nlinarith

theorem budget_le (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (G C : List Bool → ℕ) (HG : ∀ q, (F.state q).bank.Bounds (G q))
    (HC : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ C q)
    (q : List Bool) (M W D L : ℕ)
    (hM : count (F.birth q + 1) (F.width q) ≤ M)
    (hW : (F.spatial q).degree.size ≤ W) (hD : (F.spatial q).degree ≤ D)
    (hP : (F.spatial q).leading.natAbs.size ≤ C q)
    (hL : ∀ i, ((F.rule q).critical.heights i).nodes ≤ L)
    (hE : ∀ i, ((F.rule q).critical.heights i).CoefficientsBound (C q))
    (hScale : ∀ i, ((F.rule q).critical.scales i).natAbs.size ≤ C q)
    (hSlope : (F.rule q).slope.natAbs.size ≤ C q) (hG : C q + 1 ≤ G q) :
    budget F I G C HG HC q ≤ height (F.ambient q) M W D (F.cap q) L (G q) := by
  let T := inputFactor (F.ambient q) (F.cap q) L * G q
  have HE := IntegralMixedGlobalHeightBounds.expressionFactor_pos (F.cap q) L
  have HT : G q ≤ T := by
    have HF : 1 ≤ inputFactor (F.ambient q) (F.cap q) L := by unfold inputFactor; nlinarith
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (G q) HF
  have HV := retainedHeight_scaled (F.rule q) (F.birth q) (F.cap q) L (C q) (G q)
    (F.birth_bound q) hL hE hScale hSlope hG
  have HQ : (F.ambient q + 1) * scaleHeight (F.birth q) (G q) (F.rule q) ≤ T := by
    have HS := scaleHeight_scaled (F.rule q) (F.birth q) (F.cap q) L (C q) (G q)
      (F.birth_bound q) hScale hG
    dsimp only [T, inputFactor]
    nlinarith
  have HB := IntegralOriginalCriticalFactorBounds.budget_scaled
    (IntegralMixedVirtualSweepSource.source F I) (inputs F I G C HG HC) q T (by omega)
    (by exact (Nat.le_succ (C q)).trans (hG.trans HT)) HV HQ (hP.trans (by omega))
  have HF : IntegralOriginalCriticalFactorBounds.factor (IntegralMixedVirtualSweepSource.source F I) q ≤
      IntegralCriticalFactorCeiling.factor (F.ambient q + 1) M W D := by
    apply IntegralCriticalFactorCeiling.dominates _ q (F.ambient q + 1) M W D
      (Nat.le_refl _) (by exact Nat.add_le_add_right (Nat.sub_le _ _) 1) hM hW hD
    · exact IntegralCriticalFactorCeiling.dimension_mono
        (Nat.add_le_add_right (Nat.sub_le _ _) 1) hD
    · exact IntegralCriticalFactorCeiling.bound_mono
        (Nat.add_le_add_right (Nat.sub_le _ _) 1) hD
  exact HB.trans (Nat.mul_le_mul_right T HF)

theorem coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (G C : List Bool → ℕ) (HG : ∀ q, (F.state q).bank.Bounds (G q))
    (HC : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ C q)
    (q : List Bool) (M W D L : ℕ)
    (hM : count (F.birth q + 1) (F.width q) ≤ M)
    (hW : (F.spatial q).degree.size ≤ W) (hD : (F.spatial q).degree ≤ D)
    (hP : (F.spatial q).leading.natAbs.size ≤ C q)
    (hL : ∀ i, ((F.rule q).critical.heights i).nodes ≤ L)
    (hE : ∀ i, ((F.rule q).critical.heights i).CoefficientsBound (C q))
    (hScale : ∀ i, ((F.rule q).critical.scales i).natAbs.size ≤ C q)
    (hSlope : (F.rule q).slope.natAbs.size ≤ C q) (hG : C q + 1 ≤ G q)
    (index : Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q)
      (.coordinate (I.coordinate q) index) k u v).natAbs ≤
        2 ^ height (F.ambient q) M W D (F.cap q) L (G q) := by
  by_cases HK : k < 2 ^ F.width q
  · rw [← IntegralMixedCutNilpotent.coefficient (F.state q) (F.birth_bound q) (F.rule q)
      (.coordinate (I.coordinate q) index) (F.scalar_cap q) ⟨k, HK⟩ u v]
    exact (IntegralMixedVirtualBounds.coefficient_height F I G C HG HC q index.val _ _).trans
      (Nat.pow_le_pow_right (by decide)
        (budget_le F I G C HG HC q M W D L hM hW hD hP hL hE hScale hSlope hG))
  · rw [IntegralMixedCutNilpotent.coefficient_outside _ _ _ _ (F.scalar_cap q) k (by omega),
      Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

structure OriginalBounds (F : Family) where
  bankHeight : List Bool → ℕ
  sourceHeight : List Bool → ℕ
  rank : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  spatialDegree : List Bool → ℕ
  nodes : List Bool → ℕ
  bank : ∀ q, (F.state q).bank.Bounds (bankHeight q)
  coefficient : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ sourceHeight q
  rank_bound : ∀ q, count (F.birth q + 1) (F.width q) ≤ rank q
  width_bound : ∀ q, (F.spatial q).degree.size ≤ sourceWidth q
  degree_bound : ∀ q, (F.spatial q).degree ≤ spatialDegree q
  leading : ∀ q, (F.spatial q).leading.natAbs.size ≤ sourceHeight q
  expression_nodes : ∀ q i, ((F.rule q).critical.heights i).nodes ≤ nodes q
  expression_coefficients : ∀ q i, ((F.rule q).critical.heights i).CoefficientsBound (sourceHeight q)
  scales : ∀ q i, ((F.rule q).critical.scales i).natAbs.size ≤ sourceHeight q
  slope : ∀ q, (F.rule q).slope.natAbs.size ≤ sourceHeight q
  source_le_bank : ∀ q, sourceHeight q + 1 ≤ bankHeight q

noncomputable def rawBounds (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : OriginalBounds F)
    (index : ∀ q, Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .coordinate (I.coordinate q) (index q)) : RawBounds F where
  height q := height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
    (F.cap q) (H.nodes q) (H.bankHeight q)
  bound q k u v := by
    rw [hkind]
    exact coefficient_height F I H.bankHeight H.sourceHeight H.bank H.coefficient q
      (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (H.nodes q)
      (H.rank_bound q) (H.width_bound q) (H.degree_bound q) (H.leading q)
      (H.expression_nodes q) (H.expression_coefficients q) (H.scales q) (H.slope q)
      (H.source_le_bank q) (index q) k u v

theorem rawBounds_height_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : OriginalBounds F)
    (index : ∀ q, Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .coordinate (I.coordinate q) (index q))
    (hn : UnaryFn F.ambient) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap)
    (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (rawBounds F I H index hkind).height :=
  height_binary hn hM hW hD hS hL hG

end LeanCanny.Algebra.IntegralMixedCoordinateBounds
