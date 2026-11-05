/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedFields
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical
/-! # A source-aware critical own word in the endpoint component -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem vector_mem_congr {A : Type} (n : A→ℕ) (Q : (a : A)→MvPolynomial (Fin (n a)) ℤ)
    (a b : A) (he : a=b) (v : ℕ→ℝ) :
    (Q a).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=0 ↔
      (Q b).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=0 := by cases he;rfl

private theorem joined_context {A : Type} (n : A→ℕ) (Q : (a : A)→MvPolynomial (Fin (n a)) ℤ)
    (a b : A) (he : a=b) (v : ℕ→ℝ) (p : Fin (n a)→ℝ)
    (HJ : JoinedIn {x | (Q a).eval₂ (Int.castRingHom ℝ) x=0} (fun i=>v i.val) p) :
    ∃q : Fin (n b)→ℝ, HEq p q ∧ JoinedIn {x | (Q b).eval₂ (Int.castRingHom ℝ) x=0} (fun i=>v i.val) q := by
  cases he
  exact ⟨p,HEq.rfl,HJ⟩

private theorem root_critical (c : List Bool) (v : ℕ→ℝ)
    (hz : (fun i=>v i.val)∈FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
      (FormulaSignSlotRadialProviderRecordPlan.providerContext (root c))) :
    FormulaSignSlotRadialProviderFirstCritical.CriticalInComponent
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)) (fun i=>v i.val) :=
  FormulaSignSlotRadialProviderFirstCritical.exists_critical
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root c)) (fun i=>v i.val) hz

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
open FormulaSignSlotRadialProviderMarkedGeometry (number polynomial zeroSet)
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source
  CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial

theorem exists_component_word (c : List Bool) (v : ℕ→ℝ)
    (hv : ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0)
    (hz : (fun i=>v i.val)∈zeroSet c) :
    ∃p : Fin ((P).ambient (root c)+1)→ℝ, ∃_W : WordReceipt c v p,
      ∃q : Fin (number c+4)→ℝ, HEq p q ∧ JoinedIn (zeroSet c) (fun i=>v i.val) q := by
  let d := FormulaSignSlotRadialProviderRecordPlan.providerContext (root c)
  have HE : d=c := root_provider c
  have HZ : (fun i=>v i.val)∈zeroSet d :=
    (vector_mem_congr (fun c=>number c+4) polynomial d c HE v).mpr hz
  obtain ⟨p,hp,hg,hj⟩ := root_critical c v HZ
  obtain ⟨W⟩ := exists_word c v hv p hp hg
  have HJ : JoinedIn {x | (polynomial d).eval₂ (Int.castRingHom ℝ) x=0} (fun i=>v i.val) p := hj
  obtain ⟨q,hpq,hJ⟩ := joined_context (fun c=>number c+4) polynomial d c HE v p HJ
  exact ⟨p,W,q,hpq,hJ⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
