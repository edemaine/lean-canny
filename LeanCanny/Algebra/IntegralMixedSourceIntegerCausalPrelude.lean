/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
public import LeanCanny.Algebra.IntegralMixedCausalPlan
/-! # Charged integer roots are literal causal prelude records

Serializing later records together with these original integer templates lets
later current-Q slopes see the actual prelude bank. No later prefix is replayed
from an empty bank or reinterpreted under a different source.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def record (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) (i : Fin (count root)) : Record (P.ambient root) (P.width root) where
  source:=Q root
  source_cap:=hq root
  template:=.integer (S.polynomial (pair root (BinaryNatCode.encode (count root-1-i.val))))
    (hz _) ((S.degree_bound _).trans (hd root _))

noncomputable def records (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) := List.ofFn (record P Q hq S count hz hd root)

theorem records_length (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) : (records P Q hq S count hz hd root).length=count root := List.length_ofFn

noncomputable def freeze {n B : ℕ} (r : Record n B) : Instruction n B :=
  ⟨r.source,r.source_cap,r.template.command 1 one_ne_zero⟩
def Stable {n B : ℕ} (r : Record n B) : Prop :=
  ∀ (v : ℤ) (hv : v≠0),r.template.command v hv=r.template.command 1 one_ne_zero

theorem causal_commands_stable {n horizon B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State Q horizon B 0 ι) (rs : List (Record n B)) (hr : rs.length≤horizon+1)
    (hs : ∀r∈rs,Stable r) : IntegralMixedCausalPlanBits.commands initial rs hr=rs.map freeze := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [IntegralMixedCausalPlanBits.commands_cons,List.map_cons]
    apply congrArg₂ List.cons
    · exact congrArg (fun cmd=>Instruction.mk r.source r.source_cap cmd)
        (hs r List.mem_cons_self _ _)
    · exact ih _ (fun s hs'=>hs s (List.mem_cons_of_mem r hs'))

theorem records_commands (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) {horizon : ℕ} {ι : Type} [Fintype ι] (initial : State (Q root) horizon (P.width root) 0 ι)
    (hr : (records P Q hq S count hz hd root).length≤horizon+1) :
    IntegralMixedCausalPlanBits.commands initial (records P Q hq S count hz hd root) hr=
      commands P Q hq S count hz hd root := by
  rw [causal_commands_stable]
  · simp only [records,commands,List.map_ofFn]
    rfl
  · intro r hr'
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr'
    intro v hv
    rfl

/- The older bank is interpreted once, before any new record is instantiated. -/
theorem causal_commands_drop {n horizon B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State Q horizon B 0 ι) (rs : List (Record n B)) (hr : rs.length≤horizon+1) (k : ℕ) :
    (IntegralMixedCausalPlanBits.commands initial rs hr).drop k=
      IntegralMixedCausalPlanBits.commands initial (rs.drop k)
        (by rw [List.length_drop]; omega) := by
  induction rs generalizing k with
  | nil => cases k <;> rfl
  | cons r rs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [IntegralMixedCausalPlanBits.commands_cons,List.drop_succ_cons] using ih _ k

theorem appended_integer_suffix (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) {horizon : ℕ} {ι : Type} [Fintype ι] (initial : State (Q root) horizon (P.width root) 0 ι)
    (later : List (Record (P.ambient root) (P.width root)))
    (hr : (later++records P Q hq S count hz hd root).length≤horizon+1) :
    (IntegralMixedCausalPlanBits.commands initial (later++records P Q hq S count hz hd root) hr).drop later.length=
      commands P Q hq S count hz hd root := by
  rw [causal_commands_drop]
  simpa only [List.drop_left] using records_commands P Q hq S count hz hd root initial
    (by simp only [List.length_append] at hr; omega)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
