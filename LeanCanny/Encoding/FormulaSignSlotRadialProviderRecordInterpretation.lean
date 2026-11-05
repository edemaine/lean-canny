/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrelude
/-! # Correlated provider roots in the actual saved prelude state -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realizes_commands {n S B : ℕ} {Q : SpatialSource n}
    (initial : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes (run initial ds hd) v) :
    IntegralMixedIntegerRealization.Realizes (run initial cs hc) v := by
  cases he
  exact hv

private theorem realizes_reframe {n n' S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (R : SpatialSource n')
    (hr : PurePowerReductionBounds.dimension (n'+1) R.degree≤2^B) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes x v) :
    IntegralMixedIntegerRealization.Realizes (reframe x R hr) v := hv

private theorem source_prefix_realizes (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
    (hT : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r) (key : List Bool)
    (hc : commands P D key=IntegralMixedSourceIntegerPrelude.commands P D.initialSource
      (fun r=>(initial P D r).critical_cap) T N hz hT (pairFst key)) (v : ℕ→ℝ)
    (hv : ∀i<N (pairFst key),(T.polynomial (pair (pairFst key) (BinaryNatCode.encode i))).eval₂
      (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes ((family P D J).state key) (fun j=>v (N (pairFst key)-1-j)) := by
  have HR := IntegralMixedSourceIntegerPrelude.realizes P D.initialSource
    (fun r=>(initial P D r).critical_cap) T N hz hT (pairFst key)
    (initial P D (pairFst key)) (fun i : Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i)
    (by rw [←hc,commands,paddedPast_length]; exact (min_le_right _ _).trans (Nat.le_succ _)) v hv
  have HF : IntegralMixedIntegerRealization.Realizes
      (run (initial P D (pairFst key)) (commands P D key)
        (by rw [commands,paddedPast_length]; exact (min_le_right _ _).trans (Nat.le_succ _)))
      (fun j=>v (N (pairFst key)-1-j)) := realizes_commands _ _ _ _ _ hc _ HR
  exact realizes_reframe _ _ _ _ HF

private theorem append_integer_commands (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
    (hn : ∀r,0<P.ambient r) (hd : ∀r,(Q r).degree=P.degree r)
    (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
    (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
    (hT : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
    (hroom : ∀r,IntegralMixedCausalRecordPlanBits.count r+N r+2≤P.cap r+1)
    (key : List Bool) (hb : prefixLength P key=N (pairFst key)) :
    let D := IntegralMixedSourceIntegerRecordAppend.plan P (fun r _=>Q r) hn (fun r _=>hd r) hcap N T hz hT hroom
    commands P D key=IntegralMixedSourceIntegerPrelude.commands P D.initialSource
      (fun r=>(initial P D r).critical_cap) T N hz hT (pairFst key) :=
  IntegralMixedSourceIntegerRecordAppend.prelude_commands_at P (fun r _=>Q r) hn
    (fun r _=>hd r) hcap N T hz hT hroom key hb

private theorem planned_realizes (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ) (key : List Bool) (v : ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes ((family
      (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D J L F C)).state key) v ↔
        IntegralMixedIntegerRealization.Realizes ((family P D J).state key) v := Iff.rfl

attribute [local irreducible] parameters source spatial
  FormulaSignSlotRadialProviderIntegerSource.source FormulaSignSlotRadialExternalCoordinates.source

theorem prelude_state_realizes (key : List Bool) (hb : prefixLength parameters key=count (pairFst key)) (v : ℕ→ℝ)
    (hv : ∀i<count (pairFst key),(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (providerContext (pairFst key)) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes ((IntegralMixedFramedHistoryFamilyBits.family parameters plan data).state key)
      (fun j=>v (count (pairFst key)-1-j)) := by
  apply source_prefix_realizes parameters plan data count source source_nonzero source_degree_cap key
  · exact append_integer_commands parameters spatial positive spatial_degree spatial_cap count source source_nonzero source_degree_cap room key hb
  · intro i hi
    rw [source_polynomial_packet]
    exact hv i hi

theorem certified_prelude_state_realizes (key : List Bool) (hb : prefixLength parameters key=count (pairFst key)) (v : ℕ→ℝ)
    (hv : ∀i<count (pairFst key),(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (providerContext (pairFst key)) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes
      ((IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).state key)
      (fun j=>v (count (pairFst key)-1-j)) :=
  (planned_realizes parameters plan data (fun _=>3) factor seed key _).mpr (prelude_state_realizes key hb v hv)

theorem certified_prelude_key_realizes (root tail : List Bool) (v : ℕ→ℝ)
    (hv : ∀i<count root,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (providerContext root) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes
      ((IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).state
        (keyAt root (count root) tail)) (fun j=>v (count root-1-j)) := by
  have HB : prefixLength parameters (keyAt root (count root) tail)=count (pairFst (keyAt root (count root) tail)) := by
    rw [pairFst_pair]
    exact keyAt_prefix parameters root _ tail (by have H := room root; omega)
  simpa only [pairFst_pair] using certified_prelude_state_realizes (keyAt root (count root) tail) HB v
    (by simpa only [pairFst_pair] using hv)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
