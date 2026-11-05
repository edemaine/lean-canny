/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordNative
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPrefix
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
/-! # The exact provider prelude at the full record width and horizon -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source

private theorem reindex_polynomial (Q : IntegerPolynomialRootQueriesBits.Source) (f : List Bool → List Bool)
    (q : List Bool) : (IntegerPolynomialSourceChoice.reindex Q f).polynomial q = Q.polynomial (f q) := rfl

theorem source_polynomial_packet (root bits : List Bool) : source.polynomial (pair root bits) =
    FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair (providerContext root) bits) := by
  rw [source,reindex_polynomial]
  simp only [sourceQuery,pairFst_pair,pairSnd_pair]

noncomputable def recordPrelude := IntegralMixedSourceIntegerRecordAppend.preludePlan parameters
  (fun root _=>spatial root) (fun root _=>spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room

theorem record_prelude_commands (root tail : List Bool) :
    commands parameters plan (keyAt root (count root) tail)=
      recordPrelude.rules (pairFst (keyAt root (count root) tail)) :=
  IntegralMixedSourceIntegerRecordAppend.prelude_commands_key parameters (fun root _=>spatial root)
    positive (fun root _=>spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room root tail

theorem record_prelude_initial (root : List Bool) : initial parameters plan root=initial parameters recordPrelude root :=
  IntegralMixedSourceIntegerRecordAppend.prelude_initial parameters (fun root _=>spatial root)
    positive (fun root _=>spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room root

theorem recordPrelude_length (root : List Bool) : (recordPrelude.rules root).length=count root :=
  IntegralMixedSourceIntegerRecordAppend.prelude_length parameters (fun root _=>spatial root)
    (fun root _=>spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room root

attribute [local irreducible] parameters plan recordPrelude spatial source

noncomputable def certifiedRecordPrelude := IntegralMixedFramedNormalizationBits.plannedPlan parameters recordPrelude (fun _=>3) factor seed

private theorem commands_planned (P : Parameters) (D : Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    commands (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key=commands P D key := rfl

theorem certified_prelude_commands (root tail : List Bool) :
    commands certifiedParameters certifiedPlan (keyAt root (count root) tail)=
      certifiedRecordPrelude.rules (pairFst (keyAt root (count root) tail)) :=
  (commands_planned parameters plan (fun _=>3) factor seed _).trans (record_prelude_commands root tail)

noncomputable def preludeRun (root : List Bool) := run (initial parameters recordPrelude root)
  (recordPrelude.rules root) (by rw [recordPrelude_length]; have H := room root; omega)

private theorem realizes_plan (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
    (hdegree : ∀r,(Q r).degree=P.degree r)
    (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
    (T : IntegerPolynomialRootQueriesBits.Source) (N : List Bool → ℕ)
    (hz : ∀q,T.polynomial q≠0) (hd : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
    (hroom : ∀r,N r+2≤P.cap r+1) (r : List Bool) (v : ℕ → ℝ)
    (hv : ∀i<N r,(T.polynomial (pair r (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    let D := IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap T N hz hd hroom
    IntegralMixedIntegerRealization.Realizes
      (run (initial P D r) (D.rules r) (by have H := D.room r; omega)) (fun j=>v (N r-1-j)) := by
  let D := IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap T N hz hd hroom
  let hq := fun c=>(initial P D c).critical_cap
  exact IntegralMixedSourceIntegerPrelude.realizes P Q hq T N hz hd r
    (initial P D r) (fun i : Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i)
    (by rw [IntegralMixedSourceIntegerPrelude.commands_length]; have H := hroom r; omega) v hv

theorem prelude_realizes (root : List Bool) (v : ℕ → ℝ)
    (hv : ∀i<count root,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (providerContext root) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    IntegralMixedIntegerRealization.Realizes (preludeRun root) (fun j=>v (count root-1-j)) := by
  unfold preludeRun recordPrelude IntegralMixedSourceIntegerRecordAppend.preludePlan
  exact realizes_plan parameters spatial spatial_degree spatial_cap source count source_nonzero source_degree_cap
    (fun r=>by have H := room r; omega) root v (fun i hi=>by rw [source_polynomial_packet]; exact hv i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
