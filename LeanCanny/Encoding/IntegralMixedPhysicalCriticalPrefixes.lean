/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalQuery
/-! # Consecutive full physical prefixes at one original prepared root

The last record is the probe; both samplers retain the same target cap.
No root word is transported between different power schedules.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalPrefixes
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalCriticalQuery (root)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def birth (n : List Bool→ℕ) (outer child : Bool) (q : List Bool) :=
  IntegralMixedPhysicalMarkedPlan.leafCount n outer (pair (root q) [])+
    IntegralMixedCausalRecordPlanBits.count (root q)-(if child then 0 else 1)

include hn in
theorem birth_unary (child : Bool) : UnaryFn (birth n outer child) :=
  (((IntegralMixedPhysicalMarkedPlan.leafCount_unary hn outer).comp
    (mem_FP_pair pairFst_mem_FP (constFn_mem_FP []))).add
      (IntegralMixedCausalRecordPlanBits.count_unary.comp pairFst_mem_FP)).sub
        (UnaryFn.const (if child then 0 else 1))

theorem birth_pos (n : List Bool→ℕ) (outer child : Bool) (q : List Bool) : 0<birth n outer child q := by
  unfold birth IntegralMixedPhysicalMarkedPlan.leafCount IntegralMixedAuxiliaryMarkedIntegerSource.number
    IntegralMixedAuxiliaryMarkedIntegerSource.original IntegralMixedAuxiliaryMarkedIntegerSource.candidate root
  simp only [pairFst_pair]
  split_ifs <;> omega

theorem birth_le (child : Bool) (q : List Bool) :
    birth n outer child q≤(bank hn ht ha hR outer).parameters.cap (root q)+1 := by
  cases outer
  · change birth n false child q≤IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+
      8+IntegralMixedCausalRecordPlanBits.count (root q)+2+1
    simp only [birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,Bool.false_eq_true,ite_false]
    split_ifs <;> omega
  · change birth n true child q≤IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+
      10+IntegralMixedCausalRecordPlanBits.count (root q)+2+1
    simp only [birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,ite_true]
    split_ifs <;> omega

def key (n : List Bool→ℕ) (outer child : Bool) (q : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (root q) (birth n outer child q) q

include hn in
theorem key_FP (child : Bool) : key n outer child∈FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (BinaryFn.ofUnary (birth_unary hn outer child)).bits_mem_FP
    id_mem_FP)

theorem key_birth (child : Bool) (q : List Bool) :
    (family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).birth (key n outer child q)=birth n outer child q :=
  (IntegralMixedFramedHistoryFamilyBits.family_birth _ _ _ _).trans
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ (birth_le hn ht ha hR outer child q))

theorem positive (child : Bool) (q : List Bool) :
    0<(family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).birth (key n outer child q) := by
  rw [key_birth hn ht ha hR outer]
  exact birth_pos n outer child q

noncomputable abbrev input (child : Bool) :=IntegralFramedPhysicalSquare.input
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (key n outer child) (positive hn ht ha hR outer child)

theorem below_cap (child : Bool) (q : List Bool) :
    birth n outer child q<(bank hn ht ha hR outer).parameters.cap (root q) := by
  cases outer
  · change birth n false child q<IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+
      8+IntegralMixedCausalRecordPlanBits.count (root q)+2
    simp only [birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,Bool.false_eq_true,ite_false]
    split_ifs <;> omega
  · change birth n true child q<IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+
      10+IntegralMixedCausalRecordPlanBits.count (root q)+2
    simp only [birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,ite_true]
    split_ifs <;> omega


attribute [local irreducible] bank native tables

theorem row_evaluator (child : Bool) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer child)) := by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact IntegralFramedPhysicalSquare.native_row_evaluator B.parameters A.parameters B.plan B.data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    B.nodes B.factor B.seed B.bounds (key n outer child) (key_FP hn outer child)
    (positive hn ht ha hR outer child) A.liftedData A.controls A.bounds

theorem access (child : Bool) : (input hn ht ha hR outer child).Access := by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact IntegralFramedPhysicalSquare.native_access B.parameters A.parameters B.plan B.data
    (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    B.nodes B.factor B.seed B.bounds A.nodes A.factor A.seed (key n outer child) (key_FP hn outer child)
    (positive hn ht ha hR outer child) A.liftedData A.controls A.bounds

theorem consecutive (n : List Bool→ℕ) (outer : Bool) (q : List Bool) : birth n outer true q=birth n outer false q+1 := by
  have H:=birth_pos n outer false q
  change (IntegralMixedPhysicalMarkedPlan.leafCount n outer (pair (root q) [])+
    IntegralMixedCausalRecordPlanBits.count (root q))=
    (IntegralMixedPhysicalMarkedPlan.leafCount n outer (pair (root q) [])+
    IntegralMixedCausalRecordPlanBits.count (root q)-1)+1
  change 0<IntegralMixedPhysicalMarkedPlan.leafCount n outer (pair (root q) [])+
    IntegralMixedCausalRecordPlanBits.count (root q)-1 at H
  omega

theorem same_root (n : List Bool→ℕ) (outer : Bool) (q : List Bool) : pairFst (key n outer false q)=pairFst (key n outer true q) := by
  simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]


end LeanCanny.Encoding.IntegralMixedPhysicalCriticalPrefixes
