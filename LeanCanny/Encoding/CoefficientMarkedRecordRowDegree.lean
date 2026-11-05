/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordFullHeads
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegree
/-! # The actual symbolic full rows have the original native spatial degree bound

Specializations on a whole dyadic tail rule out any higher spatial monomial.
No preservation of degree under a coefficient map is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRowDegree
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem zero_of_tail (p : ℤ[X]) (C : ℕ) (h : ∀ r, C ≤ r → p.eval ((2 : ℤ)^r) = 0) : p = 0 := by
  have hd := IntegerPolynomialDyadic.natDegree_le p C 0 0 (fun r hr => by
    rw [h r hr]
    exact Nat.zero_le _)
  have hc := Polynomial.eq_C_of_natDegree_le_zero hd
  have he := h C le_rfl
  rw [hc, Polynomial.eval_C] at he
  rw [hc, he, Polynomial.C_0]

private theorem spatial_degree_of_tail {σ : Type*} (p : MvPolynomial σ ℤ[X]) (C E : ℕ)
    (h : ∀ r, C ≤ r → (p.map (evalRingHom ((2 : ℤ)^r))).totalDegree ≤ E) : p.totalDegree ≤ E := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro v hv
  by_contra he
  have hvd : E < v.sum (fun _ e => e) := by omega
  have hz : p.coeff v = 0 := zero_of_tail (p.coeff v) C (fun r hr => by
    have hh := MvPolynomial.coeff_eq_zero_of_totalDegree_lt ((h r hr).trans_lt hvd)
    simpa only [MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] using hh)
  exact (MvPolynomial.mem_support_iff.mp hv) hz

private def SpatialBound (D : CoefficientMarkedRecordRows.Data ℤ) (E : ℕ) : Prop :=
  ∀ i, (D.rows i).totalDegree ≤ E

private theorem sampler_degree (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool) : SpatialBound (CoefficientMarkedRecordRowBounds.samplerData P D H key)
      (IntegralMixedFramedPhysicalRowDegree.upper P (pairFst key)) := by
  intro i
  have hd : IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode i.val)) =
      (IntegralFramedPhysicalSquare.sampler P D H key).degrees i :=
    IntegralMixedFramedPhysicalDegree.degree_eq P D H T hr key i
  have hu := IntegralMixedFramedPhysicalRowDegree.degree_le_upper P T (pair key (BinaryNatCode.encode i.val))
  have hb : (IntegralFramedPhysicalSquare.sampler P D H key).degrees i ≤
      IntegralMixedFramedPhysicalRowDegree.upper P (pairFst key) := by
    rw [← hd]
    simpa only [pairFst_pair] using hu
  exact ((IntegralFramedPhysicalSquare.sampler P D H key).row_degree i).trans hb

private def DeclaredBound (D : CoefficientMarkedRecordRows.Data ℤ) (d : ℕ → ℕ) : Prop :=
  ∀ i, (D.rows i).totalDegree ≤ d i.val

private theorem sampler_declared (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool) : DeclaredBound (CoefficientMarkedRecordRowBounds.samplerData P D H key)
      (fun j => IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode j))) := by
  intro i
  have hd : IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode i.val)) =
      (IntegralFramedPhysicalSquare.sampler P D H key).degrees i :=
    IntegralMixedFramedPhysicalDegree.degree_eq P D H T hr key i
  exact ((IntegralFramedPhysicalSquare.sampler P D H key).row_degree i).trans_eq hd.symm

private theorem upper_planned (P : IntegralCriticalHistoryTask.Parameters) (L F C : List Bool → ℕ) (root : List Bool) :
    IntegralMixedFramedPhysicalRowDegree.upper (IntegralMixedFramedNormalizationBits.planned P L F C) root =
      IntegralMixedFramedPhysicalRowDegree.upper P root := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def spatialDegree (ctx : List Bool) :=
  IntegralMixedFramedPhysicalRowDegree.upper (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) ctx

theorem spatialDegree_binary : BinaryFn (spatialDegree hn ht ha) :=
  IntegralMixedFramedPhysicalRowDegree.upper_binary _ (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha)

private theorem certified_degree (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ) (aux : List Bool) :
    SpatialBound (CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx hR k aux) (spatialDegree hn ht ha ctx) := by
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  have hb := sampler_degree P D H (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) key
  have he : IntegralMixedFramedPhysicalRowDegree.upper P (pairFst key) = spatialDegree hn ht ha ctx :=
    (upper_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) (fun _ => 3)
      (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (pairFst key)).trans
        (congrArg (IntegralMixedFramedPhysicalRowDegree.upper (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha))
          (CoefficientMarkedRecordRowLayout.key_root (n := n) ctx k aux))
  exact he ▸ hb

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan

/-- One original bound applies to every literal symbolic physical row at every prefix. -/
theorem row_degree (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (i : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count) :
    ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).rows i).totalDegree ≤ spatialDegree hn ht ha ctx := by
  apply spatial_degree_of_tail _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
  intro r hr
  have hb := certified_degree hn ht ha ctx (BinaryFn.const r) k []
  have he := CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx (BinaryFn.const r) k hk [] hr
  have hh : SpatialBound (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^r))
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk)) (spatialDegree hn ht ha ctx) := he.symm ▸ hb
  exact hh i

private theorem certified_declared (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ) (aux : List Bool) :
    DeclaredBound (CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx hR k aux)
      (CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k aux) := by
  rw [CoefficientMarkedRecordFullHeads.degrees_eq hn ht ha ctx hR k aux]
  unfold CoefficientMarkedRecordRowBounds.certifiedIndexed CoefficientMarkedRecordFullHeads.nativeDegrees
  exact sampler_declared
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)

/-- The same argument binds each row to its exact ORIGINAL advertised degree. -/
theorem declared_row_degree (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (i : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count) :
    ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).rows i).totalDegree ≤
      CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k aux i.val := by
  apply spatial_degree_of_tail _ (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
  intro r hr
  have hb := certified_declared hn ht ha ctx (BinaryFn.const r) k aux
  have he := CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx (BinaryFn.const r) k hk aux hr
  have hh : DeclaredBound (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^r))
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk))
      (CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k aux) := he.symm ▸ hb
  exact hh i

/-- Every actual symbolic row root is covered by ALL constructed coordinate heads,
including at singular or nondyadic real parameter values. -/
theorem heads_root (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (β : ℝ)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count → ℝ)
    (hz : ∀ i, ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).rows i).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) z = 0) :
    ∀ i, (CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk aux i).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) (z i) = 0 :=
  AffineRingCoordinates.eval_eq_zero (SymbolicScaledSquarefree.scalarEvaluation β)
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).rows
    (fun i => CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k aux i.val)
    (declared_row_degree hn ht ha ctx k hk aux) z hz

end LeanCanny.Encoding.CoefficientMarkedRecordRowDegree
