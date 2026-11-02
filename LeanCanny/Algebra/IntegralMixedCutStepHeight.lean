/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutHeightControls
/-! # Actual normalized-cut births preserve one multiplicative bank ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutStepHeight
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts IntegralMixedCutSource IntegralMixedCoordinateBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def fixedFamily (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ)
    (hd : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B) : Family where
  ambient _ := n
  cap _ := S
  width _ := B
  birth _ := m
  physical _ := ι
  spatial _ := P
  state _ := x
  birth_bound _ := hm
  rule _ := r
  kind _ := c
  degree _ := d
  degree_bound _ := hd
  scalar_cap _ := hB

noncomputable def indices (F : Family) : IntegralMixedVirtualSweepSource.Indices F where
  coordinate q := ⟨0, Nat.zero_lt_succ _⟩
  coefficientIndex _ := 0
  target _ := 0
  row q := ⟨0, by change 0 < (2 ^ F.width q) ^ (F.birth q + 1); exact pow_pos (Nat.two_pow_pos _) _⟩
  col q := ⟨0, by change 0 < (2 ^ F.width q) ^ (F.birth q + 1); exact pow_pos (Nat.two_pow_pos _) _⟩
  modulus _ := 1
  modulus_ne_zero _ := by decide

noncomputable def bounds (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ)
    (hd : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (G C R W D L : ℕ) (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hR : count (m + 2) B ≤ R) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.critical.heights i).nodes ≤ L) (hE : ∀ i, (r.critical.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C) (hSlope : r.slope.natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    OriginalBounds (fixedFamily x hm r c d hd hB) where
  bankHeight _ := G
  sourceHeight _ := C
  rank _ := R
  sourceWidth _ := W
  spatialDegree _ := D
  nodes _ := L
  bank _ := HG
  coefficient _ := HC
  rank_bound _ := (Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m + 1 ≤ m + 2)).trans hR
  width_bound _ := hW
  degree_bound _ := hD
  leading _ := HP
  expression_nodes _ := hL
  expression_coefficients _ := hE
  scales _ := hScale
  slope _ := hSlope
  source_le_bank _ := hG

theorem raw_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ)
    (hd : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (G C R W D L : ℕ) (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hR : count (m + 2) B ≤ R) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.critical.heights i).nodes ≤ L) (hE : ∀ i, (r.critical.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C) (hSlope : r.slope.natAbs.size ≤ C) (hG : C + 1 ≤ G)
    (k : ℕ) (u v : Fin (count m B)) :
    (IntegralMixedCutMatrix.coefficientMatrix x hm r c k u v).natAbs ≤
      2 ^ (IntegralMixedCutHeightProfile.factor n R W D S L * G) :=
  IntegralMixedCutHeightProfile.coefficient_height (fixedFamily x hm r c d hd hB) (indices _)
    (bounds x hm r c d hd hB G C R W D L HG HC HP hR hW hD hL hE hScale hSlope hG) [] hR k u v

variable [Fintype ι]

theorem step_bounds (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ)
    (hd : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (G C R W D L : ℕ) (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hR : count (m + 2) B ≤ R) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.critical.heights i).nodes ≤ L) (hE : ∀ i, (r.critical.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C) (hSlope : r.slope.natAbs.size ≤ C) (hG : C + 1 ≤ G) :
    (IntegralMixedRelativeCuts.step x hm r c d).bank.Bounds
      (bankGrowth R (2 ^ B) (IntegralMixedCutBounds.normalizedHeight R (IntegralMixedCutHeightProfile.factor n R W D S L)) * G) := by
  let A := IntegralMixedCutHeightProfile.factor n R W D S L
  have HR : count m B ≤ R := (Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m ≤ m + 2)).trans hR
  have hG1 : 1 ≤ G := by omega
  have HA := raw_height x hm r c d hd hB G C R W D L HG HC HP hR hW hD hL hE hScale hSlope hG
  have HN := (IntegralMixedHeightScaling.normalized_mono HR (Nat.le_refl (A * G))).trans
    (IntegralMixedHeightScaling.normalized_scaled R A G hG1)
  apply x.bank.rootStep_scaled_bounds hm _ d (IntegralMixedCutBounds.normalizedHeight (count m B) (A * G)) G R
    (IntegralMixedCutBounds.normalizedHeight R A) _ HG hG1 HR HN
  · exact IntegralMixedCutBounds.normalized_coefficient_height x hm r c d (A * G) HA
  · exact (IntegralMixedCutBounds.leading_height x hm r c d (A * G) HA).trans
      (Nat.pow_le_pow_right (by decide) (by unfold IntegralMixedCutBounds.normalizedHeight; omega))
end LeanCanny.Algebra.IntegralMixedCutStepHeight
