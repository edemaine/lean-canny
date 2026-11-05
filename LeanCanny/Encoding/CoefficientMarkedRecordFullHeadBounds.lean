/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullHeads
/-! # Parameter coefficient bounds for the actual complete full-column heads

The fixed Gram dimension depends only on the original declared row degrees.
Evaluated growth follows from the certified actual full-row affine bound.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullHeadBounds
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open CoefficientMarkedRecordRows CoefficientMarkedRecordFullHeads
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def RowMass (D : CoefficientMarkedRecordRows.Data ℤ) (M : ℕ) : Prop :=
  ∀ i, MvMass.mass (D.rows i) ≤ M

private theorem head_mass (D : CoefficientMarkedRecordRows.Data ℤ) (d : ℕ → ℕ)
    (M : ℕ) (hm : 2 ≤ M) (hr : RowMass D M) (i : Fin D.count) :
    coefficientMass (heads D d i) ≤
      (AffineRingCoordinates.dimension (fun j : Fin D.count => d j.val)).factorial *
        M ^ AffineRingCoordinates.dimension (fun j : Fin D.count => d j.val) :=
  AffineFiniteCoordinates.mass_le D.rows (fun j => d j.val) M hm
    (fun j _e => (MvMass.coeff_le _ _).trans (hr j)) i

private theorem map_count {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (E : CoefficientMarkedRecordRows.Data R) : (CoefficientMarkedRecordRows.map φ E).count = E.count := rfl

private theorem sampler_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : (CoefficientMarkedRecordRowBounds.samplerData P D H key).count =
      IntegralFramedPhysicalSquare.count P D key := rfl

private theorem sampler_nonzero (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin (IntegralFramedPhysicalSquare.count P D key)) :
    samplerAnnihilators P D H key i ≠ 0 :=
  AffineFiniteCoordinates.ne_zero (IntegralFramedPhysicalSquare.sampler P D H key).rows
    (IntegralFramedPhysicalSquare.sampler P D H key).degrees
    (IntegralFramedPhysicalSquare.sampler P D H key).degree_pos
    (IntegralFramedPhysicalSquare.sampler P D H key).noInfinity i

private theorem positive_of_map {a b : ℕ} (f : Fin a → (ℤ[X])[X]) (g : Fin b → ℤ[X])
    (φ : ℤ[X] →+* ℤ) (hc : a = b) (he : HEq (fun i => (f i).map φ) g)
    (hf : ∀ i, (f i).coeff 0 = 0) (hg : ∀ i, g i ≠ 0) : ∀ i, 0 < (f i).natDegree := by
  cases hc
  have hh := eq_of_heq he
  intro i
  have hm : (f i).map φ = g i := congrFun hh i
  have hn : f i ≠ 0 := by
    intro hz
    apply hg i
    rw [← hm, hz, Polynomial.map_zero]
  by_contra hd
  have hd0 : (f i).natDegree ≤ 0 := by omega
  have hz := Polynomial.eq_C_of_natDegree_le_zero hd0
  rw [hf i, Polynomial.C_0] at hz
  exact hn hz

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def dimension (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :=
  AffineRingCoordinates.dimension (fun j : Fin (symbolic hn ht ha ctx k hk).count =>
    degrees hn ht ha ctx k aux j.val)

noncomputable def slope (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :=
  dimension hn ht ha ctx k hk aux * IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx

noncomputable def offset (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :=
  (dimension hn ht ha ctx k hk aux).size * dimension hn ht ha ctx k hk aux +
    dimension hn ht ha ctx k hk aux * (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx + 1)

noncomputable def coefficientBudget (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (slope hn ht ha ctx k hk aux) (offset hn ht ha ctx k hk aux)

attribute [local irreducible] dimension slope offset coefficientBudget
  CoefficientMarkedRecordFullHeads.polynomial CoefficientMarkedRecordFullHeads.heads
  CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordRowBounds.samplerData IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan

/-- No caller supplies a head growth or parameter mass bound. -/
theorem evaluated_mass (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (i : Fin (symbolic hn ht ha ctx k hk).count) (r : ℕ)
    (hr : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ r) :
    coefficientMass ((polynomial hn ht ha ctx k hk aux i).map (evalRingHom ((2 : ℤ)^r))) ≤
      2 ^ (slope hn ht ha ctx k hk aux * r + offset hn ht ha ctx k hk aux) := by
  let D := symbolic hn ht ha ctx k hk
  let d := degrees hn ht ha ctx k aux
  let a := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx
  let b := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx
  let N := AffineRingCoordinates.dimension (fun j : Fin D.count => d j.val)
  have hactual : RowMass (CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx (BinaryFn.const r) k aux)
      (2 ^ (a * r + b)) :=
    fun j => CoefficientMarkedRecordRowBounds.certified_row_mass hn ht ha ctx (BinaryFn.const r) k aux j
  have hmap := CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx (BinaryFn.const r) k hk aux hr
  have hrows : RowMass (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^r)) D) (2 ^ (a * r + b + 1)) := by
    have hh : RowMass (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^r)) D) (2 ^ (a * r + b)) :=
      hmap.symm ▸ hactual
    intro j
    exact (hh j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  have hm : 2 ≤ 2 ^ (a * r + b + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ a * r + b + 1 by omega)
  have hh := head_mass (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^r)) D) d
    (2 ^ (a * r + b + 1)) hm hrows i
  unfold CoefficientMarkedRecordFullHeads.heads at hh
  have he := AffineRingCoordinateMap.annihilator (evalRingHom ((2 : ℤ)^r)) D.rows (fun j => d j.val) i
  have hf : N.factorial ≤ 2 ^ (N.size * N) :=
    (Nat.factorial_le_pow N).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self N).le N).trans_eq (pow_mul _ _ _).symm)
  unfold polynomial heads
  rw [he]
  calc
    _ ≤ N.factorial * (2 ^ (a * r + b + 1)) ^ N := hh
    _ ≤ 2 ^ (N.size * N) * (2 ^ (a * r + b + 1)) ^ N := Nat.mul_le_mul_right _ hf
    _ = 2 ^ (slope hn ht ha ctx k hk aux * r + offset hn ht ha ctx k hk aux) := by
      rw [← pow_mul, ← pow_add]
      apply congrArg (fun j : ℕ => (2 : ℕ) ^ j)
      unfold slope offset dimension
      change N.size * N + (a * r + b + 1) * N = N * a * r + (N.size * N + N * (b + 1))
      ring

theorem target_degree_le (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (i : Fin (symbolic hn ht ha ctx k hk).count) :
    (polynomial hn ht ha ctx k hk aux i).natDegree ≤ dimension hn ht ha ctx k hk aux + 1 := by
  unfold polynomial heads dimension
  exact AffineRingCoordinates.degree_le _ _ i

/-- Every formal head has positive target degree, derived from its actual complete sampler. -/
theorem positive_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :
    ∀ i, 0 < (polynomial hn ht ha ctx k hk aux i).natDegree := by
  let C := CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (BinaryFn.const C)
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (BinaryFn.const C)
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (BinaryFn.const C)
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  have hdata := CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx (BinaryFn.const C) k hk aux le_rfl
  have hc0 := congrArg (fun E : CoefficientMarkedRecordRows.Data ℤ => E.count) hdata
  unfold CoefficientMarkedRecordRowBounds.certifiedIndexed at hc0
  have hc : (symbolic hn ht ha ctx k hk).count = IntegralFramedPhysicalSquare.count P D key :=
    (map_count (evalRingHom ((2 : ℤ)^C)) (symbolic hn ht ha ctx k hk)).symm.trans
      (hc0.trans (sampler_count P D H key))
  have he := (CoefficientMarkedRecordFullHeads.specializes hn ht ha ctx (BinaryFn.const C) k hk aux le_rfl).trans
    (CoefficientMarkedRecordFullHeads.native_eq hn ht ha ctx (BinaryFn.const C) k aux)
  apply positive_of_map (polynomial hn ht ha ctx k hk aux) (samplerAnnihilators P D H key)
    (evalRingHom ((2 : ℤ)^C)) hc he
  · intro i
    unfold polynomial heads AffineRingCoordinates.annihilator AffineRingGramEliminant.annihilator
    simp only [Polynomial.coeff_X_mul_zero]
  · exact sampler_nonzero P D H key

theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (i : Fin (symbolic hn ht ha ctx k hk).count) (j : ℕ) :
    ((polynomial hn ht ha ctx k hk aux i).coeff j).natDegree ≤ slope hn ht ha ctx k hk aux ∧
      coefficientMass ((polynomial hn ht ha ctx k hk aux i).coeff j) ≤ 2 ^ coefficientBudget hn ht ha ctx k hk aux := by
  unfold coefficientBudget
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have hh := (coeff_natAbs_le_coefficientMass
    ((polynomial hn ht ha ctx k hk aux i).map (evalRingHom ((2 : ℤ)^r))) j).trans
      (evaluated_mass hn ht ha ctx k hk aux i r hr)
  simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using hh

end LeanCanny.Encoding.CoefficientMarkedRecordFullHeadBounds
