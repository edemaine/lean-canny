/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutCreationReceipt
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # Instruction equality transports the entire actual creating-factor receipt -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCreationReceipt
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family instruction selection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def ofInstruction {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (i : Instruction n B):Option Data:=
 ofCommand (reframe x i.source i.source_cap) i.command

noncomputable def atKey (P : Parameters) (D : Plan P) (_H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool):Option Data:=
 ofInstruction (IntegralMixedFramedFamilyRunView.familyRun P D key) (instruction P D key)

noncomputable def native (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool):Data:=
 ⟨IntegralMixedPrefixSnapshot.ofState ((family P D H).state key),selection P D H key⟩

theorem native_root_iff (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (values : ℕ→ℝ) (a : ℝ) :
    (native P D H key).HasRoot values a ↔
    ∃φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (((family P D H).state key).bank.numerator i)/(((family P D H).state key).bank.denominator i:ℝ)=values i.val) ∧
      IntegralMixedRelativeCuts.Valid ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) φ ((family P D H).kind key) ∧
      ((IntegralMixedRelativeCuts.factor ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) ((family P D H).kind key)).map φ.toRingHom).natDegree=(family P D H).degree key ∧
      (IntegralMixedRelativeCuts.factor ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) ((family P D H).kind key)).eval₂ φ.toRingHom a=0:=by
 constructor
 · rintro ⟨_,φ,hφ,hv,hd,hr⟩
   exact ⟨φ,hφ,hv,hd,hr⟩
 · rintro ⟨φ,hφ,hv,hd,hr⟩
   exact ⟨(family P D H).birth_bound key,φ,hφ,hv,hd,hr⟩

theorem native_factor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (hm : (native P D H key).birth≤(native P D H key).horizon) :
    IntegralMixedRelativeCuts.factor (native P D H key).state hm (native P D H key).selected.rule (native P D H key).selected.kind=
      IntegralMixedRelativeCuts.factor ((family P D H).state key) ((family P D H).birth_bound key)
        ((family P D H).rule key) ((family P D H).kind key):=rfl

theorem atKey_command (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool):
    atKey P D H key=ofCommand ((family P D H).state key) (instruction P D key).command:=rfl

theorem atKey_isCut (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : Data) (hr : atKey P D H key=some r) :
    IntegralFramedCreatingCut.IsCut (instruction P D key).command:=by
 rw [atKey_command] at hr
 unfold ofCommand at hr
 cases hc:(instruction P D key).command with
 | integer p hp hd=>rw [hc] at hr;cases hr
 | critical r'=>rw [hc] at hr;cases hr
 | cut r' k d ha hd=>trivial

theorem atKey_some_native (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : Data) (hr : atKey P D H key=some r):r=native P D H key:=by
 rw [atKey_command] at hr
 unfold ofCommand at hr
 cases hc:(instruction P D key).command with
 | integer p hp hd=>rw [hc] at hr;cases hr
 | critical r'=>rw [hc] at hr;cases hr
 | cut r' k d ha hd=>
   rw [hc] at hr
   have HE:=Option.some.inj hr
   unfold native
   rw [IntegralMixedFramedHistoryFamilyBits.selection_of_command P D H key r' k d ha hd hc]
   exact HE.symm

theorem coded_instruction {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (Q : SpatialSource n) (hn : 0<n)
    (Qcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (labels : List Bool) (values : ℕ→ℝ) (a : ℝ) (code : List Bool)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (h : (IntegralMixedPrefixSnapshot.ofState (reframe x Q Qcap)).CodedFactor labels values a code):
    ∃receipt,ofInstruction x (instantiate x (IntegralMixedCausalUnitRecordBits.record Q hn m code hcap))=some receipt ∧
      receipt.HasRoot values a:=by
 have HC:=coded_command (reframe x Q Qcap) hn labels values a code hcap h
 exact HC

end LeanCanny.Algebra.IntegralMixedCutCreationReceipt
