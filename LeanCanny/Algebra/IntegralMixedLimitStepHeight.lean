/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitHeightProfile

/-! # Actual normalized scalar births from truncated limit factors

The polynomial is the literal selected-degree truncation of the actual limit
factor. Original syntax bounds supply its raw coefficient matrices, then the
existing normalization and root-step height estimates give one multiplicative
bank ceiling. No new history tag or matrix evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitStepHeight
open LeanCanny.Encoding FixedWidthPolynomial UniformIntegralPrefix IntegralMixedHistory
open IntegralMixedCutSource
open scoped Classical

noncomputable def raw (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F) (q : List Bool)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial q) (F.rule q))) (d : ℕ) :=
  IntegralRelativeTruncation.truncate
    (IntegralMixedLimitCoordinate.factor (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q) c) d

theorem raw_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial q) (F.rule q))) (d k : ℕ)
    (u v : Fin (count (F.birth q) (F.width q))) :
    (Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis ((raw F I q c d).coeff k) u v).natAbs ≤
      2^(IntegralMixedLimitHeightProfile.factor (F.ambient q) (H.rank q) (H.sourceWidth q)
        (H.spatialDegree q) (F.cap q) (H.nodes q)*H.bankHeight q) := by
  rw [raw,IntegralRelativeTruncation.coefficient]
  split_ifs with HK
  · have HB := IntegralMixedLimitCoordinateBounds.coefficient_height F I H q c k u v
    rw [IntegralMixedLimitCoordinateBounds.height_eq_factor] at HB
    exact HB.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (H.bankHeight q)
      (IntegralMixedLimitHeightProfile.limit_factor_le _ _ _ _ _ _)))
  · simp only [map_zero,Matrix.zero_apply,Int.natAbs_zero,Nat.zero_le]

theorem normalized_coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial q) (F.rule q))) (d k : ℕ)
    (u v : Fin (count (F.birth q) (F.width q))) :
    (Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
      ((normalizedScalarPolynomial (F.state q) (raw F I q c d) d).coeff k) u v).natAbs ≤
      2^IntegralMixedCutBounds.normalizedHeight (count (F.birth q) (F.width q))
        (IntegralMixedLimitHeightProfile.factor (F.ambient q) (H.rank q) (H.sourceWidth q)
          (H.spatialDegree q) (F.cap q) (H.nodes q)*H.bankHeight q) :=
  IntegralMixedNormalizedHeightBounds.coefficient_height (F.state q) (raw F I q c d) d _
    (raw_height F I H q c d) k u v

theorem step_bounds (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool) [Fintype (F.physical q)]
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial q) (F.rule q))) (d : ℕ) :
    (normalizedScalarStep (F.state q) (F.birth_bound q) (raw F I q c d) d).bank.Bounds
      (bankGrowth (H.rank q) (2^F.width q)
        (IntegralMixedCutBounds.normalizedHeight (H.rank q)
          (IntegralMixedLimitHeightProfile.factor (F.ambient q) (H.rank q) (H.sourceWidth q)
            (H.spatialDegree q) (F.cap q) (H.nodes q)))*H.bankHeight q) := by
  have HG : 1 ≤ H.bankHeight q := by have HL:=H.source_le_bank q; omega
  have HR : count (F.birth q) (F.width q) ≤ H.rank q :=
    (Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.le_succ _)).trans (H.rank_bound q)
  exact IntegralMixedNormalizedHeightBounds.scaled_step_bounds (F.state q) (F.birth_bound q)
    (raw F I q c d) d (H.bankHeight q) (H.rank q) _ (H.bank q) HG HR (raw_height F I H q c d)

theorem step_bounds_of_original {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound P r)) (d : ℕ)
    (hd : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree ≤ 2^B)
    (G C R W D L : ℕ) (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2^C)
    (HP : P.leading.natAbs.size ≤ C) (hR : count (m+2) B ≤ R) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hL : ∀ i, (r.critical.heights i).nodes ≤ L) (hE : ∀ i, (r.critical.heights i).CoefficientsBound C)
    (hScale : ∀ i, (r.critical.scales i).natAbs.size ≤ C) (hSlope : r.slope.natAbs.size ≤ C) (hG : C+1 ≤ G) :
    (normalizedScalarStep x hm
      (IntegralRelativeTruncation.truncate (IntegralMixedLimitCoordinate.factor x hm r j c) d) d).bank.Bounds
      (bankGrowth R (2^B) (IntegralMixedCutBounds.normalizedHeight R
        (IntegralMixedLimitHeightProfile.factor n R W D S L))*G) := by
  let F : Family := {
    ambient := fun _ => n,cap := fun _ => S,width := fun _ => B,birth := fun _ => m,physical := fun _ => ι,
    spatial := fun _ => P,state := fun _ => x,birth_bound := fun _ => hm,rule := fun _ => r,
    kind := fun _ => .coordinate j c,degree := fun _ => d,degree_bound := fun _ => hd,scalar_cap := fun _ => hB }
  let I : IntegralMixedVirtualSweepSource.Indices F := {
    coordinate := fun _ => j,coefficientIndex := fun _ => 0,target := fun _ => 0,
    row := fun _ => ⟨0,by change 0 < (2^B)^(m+1); exact pow_pos (Nat.two_pow_pos _) _⟩,
    col := fun _ => ⟨0,by change 0 < (2^B)^(m+1); exact pow_pos (Nat.two_pow_pos _) _⟩,
    modulus := fun _ => 1,modulus_ne_zero := fun _ => by decide }
  let : Fintype (F.physical []) := by change Fintype ι; infer_instance
  let H : IntegralMixedCoordinateBounds.OriginalBounds F := {
    bankHeight := fun _ => G,sourceHeight := fun _ => C,rank := fun _ => R,sourceWidth := fun _ => W,
    spatialDegree := fun _ => D,nodes := fun _ => L,bank := fun _ => HG,coefficient := fun _ => HC,
    rank_bound := fun _ => (Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega : m+1 ≤ m+2)).trans hR,
    width_bound := fun _ => hW,degree_bound := fun _ => hD,leading := fun _ => HP,
    expression_nodes := fun _ => hL,expression_coefficients := fun _ => hE,scales := fun _ => hScale,
    slope := fun _ => hSlope,source_le_bank := fun _ => hG }
  exact step_bounds F I H [] c d

end LeanCanny.Algebra.IntegralMixedLimitStepHeight
