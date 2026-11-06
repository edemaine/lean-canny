/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedConstruct
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAtomicGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayRetention
/-! # Fresh accepted seeds at genuine chosen critical points, retaining the old prelude -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_transport {n m :ℕ} (Q :SpatialSource n) (R :SpatialSource m)
    (hd :n=m) (hs :HEq Q R) (p :Fin (n+1)→ℝ) (q :Fin (m+1)→ℝ) (hp :HEq p q)
    (hz :(FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
      (Int.castRingHom ℝ) p=0) :
    (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) q=0 ∧
    ∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial R.low R.leading R.degree)).eval₂
      (Int.castRingHom ℝ) q=0:=by
  cases hd
  cases eq_of_heq hs
  cases eq_of_heq hp
  exact ⟨hz,hg⟩

private theorem context_source (c d :List Bool) (he :c=d) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial c)
      (FormulaSignSlotRadialProviderIntegerPlan.spatial d):=by cases he;rfl

private def pointCast {n m :ℕ} (h :n=m) (p :Fin m→ℝ) :Fin n→ℝ:=fun i=>p (Fin.cast h i)
private theorem pointCast_heq {n m :ℕ} (h :n=m) (p :Fin m→ℝ) :HEq (pointCast h p) p:=by cases h;rfl

private theorem record_source (r :List Bool) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial r)
      (FormulaSignSlotRadialProviderIntegerPlan.spatial (FormulaSignSlotRadialProviderRecordPlan.providerContext r)):=HEq.rfl
private theorem provider_count (c :List Bool) :FormulaSignSlotRadialProviderIntegerPlan.count c=
    FormulaSignSlotRadialProviderMarkedGeometry.number c+8:=rfl

local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "Q"=>FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderIntegerSource.source
  FormulaSignSlotRadialProviderAtomicGeometry.source FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderRecordPlan.bank

theorem chosen_root_dimension (c :List Bool) :(P).ambient (root c)=num c+3:=ambient_root c

theorem chosen_root_source (c :List Bool) :
    HEq (Q (root c)) (FormulaSignSlotRadialProviderAtomicGeometry.source c):=
  (record_source (root c)).trans ((context_source _ _ (root_provider c)).trans
    (FormulaSignSlotRadialProviderAtomicGeometry.source_heq c).symm)

theorem exists_at_root_critical (old :List Bool) (hv :A old)
    (p :Fin ((P).ambient (root (provider old))+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (root (provider old))).low
      (Q (root (provider old))).leading (Q (root (provider old))).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q (root (provider old))).low
      (Q (root (provider old))).leading (Q (root (provider old))).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃q,∃hq:A q,provider q=provider old ∧ FormulaSignSlotRadialProviderAtomic.depth q=0 ∧
      HEq (FormulaSignSlotRadialProviderAtomic.point q hq) p ∧
      ∀i<FormulaSignSlotRadialProviderAtomic.initial old,
        FormulaSignSlotRadialProviderAtomic.field q hq i=FormulaSignSlotRadialProviderAtomic.field old hv i:=by
  let c:=provider old
  let v:=FormulaSignSlotRadialProviderAtomic.field old hv
  have HR:∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0:=by
    intro i hi
    have HI:i<num c+8:=by simpa only [count_root,provider_count] using hi
    exact FormulaSignSlotRadialProviderAtomic.MarkedPrelude.source_roots old hv i HI
  obtain ⟨W⟩:=exists_word c v HR p hp hg
  let q:=packet c W.word
  have HF:∀i<num c+8,FormulaSignSlotRadialProviderAtomic.bankField
      (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
      W.full_valid_packet i=v i:=by
    intro i hi
    change FormulaSignSlotRadialProviderAtomic.MarkedLanguage.values (packet c W.word) W.full_valid_packet i=v i
    rw [W.values_packet]
    exact W.prelude_field i (by rw [count_root];exact hi)
  have HProvider:provider q=provider old:=provider_packet c W.word
  have HMarked:=FormulaSignSlotRadialProviderAtomic.marked_of_initial_fields old hv q W.full_valid_packet HProvider HF
  have HReplay:=FormulaSignSlotRadialProviderAtomic.replay_of_initial_fields old hv q W.full_valid_packet HProvider
    (fun i hi=>(HF i (by change i<FormulaSignSlotRadialExternalContext.number (provider old)+8;omega)).symm)
  have HW:SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (pair (root c) []) W.word:=W.valid
  have HValid:A q:=⟨checked c W.word,W.full_valid_packet,before_probe c W.word HW,
    W.all_critical,W.companions,HMarked,HReplay⟩
  refine ⟨q,HValid,HProvider,depth_packet c W.word,W.point_packet HValid,?_⟩
  intro i hi
  exact W.field_packet HValid i (by
    rw [count_root]
    rw [FormulaSignSlotRadialProviderAtomic.initial_provider] at hi
    exact hi)

theorem exists_at_critical (old :List Bool) (hv :A old) (p :Fin ((num (provider old)+3)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).low
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).leading
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).low
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).leading
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃q,∃hq:A q,provider q=provider old ∧ FormulaSignSlotRadialProviderAtomic.depth q=0 ∧
      HEq (FormulaSignSlotRadialProviderAtomic.point q hq) p ∧
      ∀i<FormulaSignSlotRadialProviderAtomic.initial old,
        FormulaSignSlotRadialProviderAtomic.field q hq i=FormulaSignSlotRadialProviderAtomic.field old hv i:=by
  let pRoot:=pointCast (congrArg (·+1) (chosen_root_dimension (provider old))) p
  have HE:HEq pRoot p:=pointCast_heq _ p
  have HC:=critical_transport _ _ (chosen_root_dimension (provider old)).symm
    (chosen_root_source (provider old)).symm p pRoot HE.symm hp hg
  obtain ⟨q,hq,hprovider,hd,hpoint,hfields⟩:=exists_at_root_critical old hv pRoot HC.1 HC.2
  exact ⟨q,hq,hprovider,hd,hpoint.trans HE,hfields⟩

theorem exists_at_occurrence (old :List Bool) (hv :A old) (p :Fin ((num (provider old)+3)+1)→ℝ)
    {values :ℕ→ℝ} (hp :@IntegralMixedAtomicOccurrence.Occurrence (num (provider old)+3)
      (FormulaSignSlotRadialProviderAtomicGeometry.source (provider old)) 0 values p) :
    ∃q,∃hq:A q,provider q=provider old ∧ FormulaSignSlotRadialProviderAtomic.depth q=0 ∧
      HEq (FormulaSignSlotRadialProviderAtomic.point q hq) p ∧
      ∀i<FormulaSignSlotRadialProviderAtomic.initial old,
        FormulaSignSlotRadialProviderAtomic.field q hq i=FormulaSignSlotRadialProviderAtomic.field old hv i:=
  exists_at_critical old hv p hp.zero (fun i hi=>hp.critical i (Nat.zero_le _) hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
