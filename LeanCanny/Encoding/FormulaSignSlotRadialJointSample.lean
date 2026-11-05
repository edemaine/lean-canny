/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkedPrelude
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateRadius
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
/-! # One actual native joint source and one unchanged sampler context

The packet pairs an actual atomic node with selection metadata. Metadata
changes only the auxiliary context, so every cut family uses the same word
and chronological center references. Replay supplies the literal core root;
association of its projected lifts with the two input components is separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def radius := IntegralMixedAuxiliaryCandidateRadius.radius
  FormulaSignSlotRadialJointLayout.dimension_unary FormulaSignSlotRadialJointCore.equation_FP
  FormulaSignSlotRadialJointCore.scope
theorem radius_binary : BinaryFn radius := IntegralMixedAuxiliaryCandidateRadius.radius_binary
  FormulaSignSlotRadialJointLayout.dimension_unary FormulaSignSlotRadialJointCore.equation_FP
  FormulaSignSlotRadialJointCore.scope
local notation "HN" => FormulaSignSlotRadialJointLayout.dimension_unary
local notation "HT" => FormulaSignSlotRadialJointCore.equation_FP
local notation "HA" => FormulaSignSlotRadialJointCore.scope
local notation "HR" => radius_binary
attribute [local irreducible] radius FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank
noncomputable def input := IntegralMixedPhysicalMarkedTest.input HN HT HA
  (IntegralMixedOriginalRegularSource.radius_binary HR) false

def node (p : List Bool) := pairFst p
def metadata (p : List Bool) := pairSnd p
noncomputable def headerContext (c : List Bool) := IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst c)
noncomputable def header (p : List Bool) := headerContext (pair (IntegralMixedRoadmapAtomic.root (node p)) [])
def context (p : List Bool) := pair (IntegralMixedRoadmapAtomic.root (node p)) (metadata p)
def word (p : List Bool) := IntegralMixedRoadmapAtomic.word (node p)
def slot (i : ℕ) (c : List Bool) := WordList.reader (pair (pairSnd c) (BinaryNatCode.encode i))
noncomputable def radialContext (c : List Bool) := FormulaSignSlotRadialJointLayout.source true (headerContext c)
noncomputable def centerRefs (c : List Bool) := FormulaSignSlotRadialJointLayout.centerRefs (headerContext c)
noncomputable def anchorRefs (c : List Bool) := FormulaSignSlotRadialJointLayout.anchorRefs (headerContext c)
noncomputable def valueContext (c : List Bool) := pair (radialContext c) (pair (slot 0 c) (slot 1 c))

theorem node_FP : node ∈ FP := pairFst_mem_FP
theorem context_FP : context ∈ FP := mem_FP_pair
  (mem_FP_comp node_FP IntegralMixedRoadmapAtomic.root_FP) pairSnd_mem_FP
theorem word_FP : word ∈ FP := mem_FP_comp node_FP IntegralMixedRoadmapAtomic.word_FP
theorem headerContext_FP : headerContext ∈ FP := by
  polytime [headerContext, IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate]
theorem header_FP : header ∈ FP := by
  exact mem_FP_comp (mem_FP_pair (mem_FP_comp node_FP IntegralMixedRoadmapAtomic.root_FP)
    (constFn_mem_FP [])) headerContext_FP
theorem slot_FP (i : ℕ) : slot i ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
theorem radialContext_FP : radialContext ∈ FP := mem_FP_comp headerContext_FP (FormulaSignSlotRadialJointLayout.source_FP true)
theorem centerRefs_FP : centerRefs ∈ FP := mem_FP_comp headerContext_FP FormulaSignSlotRadialJointLayout.centerRefs_FP
theorem anchorRefs_FP : anchorRefs ∈ FP := mem_FP_comp headerContext_FP FormulaSignSlotRadialJointLayout.anchorRefs_FP
theorem valueContext_FP : valueContext ∈ FP := mem_FP_pair radialContext_FP (mem_FP_pair (slot_FP 0) (slot_FP 1))

theorem header_context (p : List Bool) : headerContext (context p) = header p := by
  simp only [headerContext, context, header, pairFst_pair]
theorem root_context (p : List Bool) : pairFst (context p) = IntegralMixedRoadmapAtomic.root (node p) := pairFst_pair _ _

noncomputable def Valid (p : List Bool) := IntegralMixedRoadmapAtomic.Valid HN HT HA HR (node p)
noncomputable def Replay (p : List Bool) := IntegralMixedRoadmapMarkedPrelude.Replay HN HT HA HR (node p)
noncomputable def values (p : List Bool) (hv : Valid p) : ℕ → ℝ :=
  IntegralMixedRoadmapMarkedPrelude.value HN HT HA HR (node p) hv

theorem full_valid (p : List Bool) (hv : Valid p) :
    SquareSampleCompleteVertices.Valid input (context p) (word p) := by
  have HW := IntegralMixedRoadmapAtomic.full_valid HN HT HA HR (node p) hv
  exact (IntegralMixedPhysicalMarkedContext.valid_iff HN HT HA
    (IntegralMixedOriginalRegularSource.radius_binary HR)
    (IntegralMixedRoadmapAtomic.context (node p)) (context p) (word p) (by
      simp only [IntegralMixedRoadmapAtomic.context, context, pairFst_pair])).mp HW

private theorem original_zero {n : List Bool → ℕ} {t : List Bool → Term} (hn : UnaryFn n)
    (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR q)
    (hr : IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR q) :
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original (IntegralMixedRoadmapAtomic.root q))).eval
      (IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR q hv) = 0 := by
  obtain ⟨_, z, HZ, _⟩ := IntegralMixedRoadmapMarkedPrelude.exists_marked hn ht ha hR q hv hr
  let x := BoundedRegularSource.markedProjection _ _ _ _ z
  have HX := x.property.1
  rw [Term.eval_finitePolynomial] at HX
  have HE := (t (IntegralMixedAuxiliaryMarkedIntegerSource.original (IntegralMixedRoadmapAtomic.root q))).eval_congr
    (Formula.extend x.val) (IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR q hv) (by
      intro i hi
      have HI : i < IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q) := hi.trans_le (ha _)
      simp only [Formula.extend, dite_eq_left HI]
      rw [BoundedRegularSource.markedProjection_apply, HZ]
      rfl)
  exact HE.symm.trans HX

theorem core_zero (p : List Bool) (hv : Valid p) (hr : Replay p) :
    (FormulaSignSlotRadialJointCore.equation (header p)).eval (values p hv) = 0 :=
by
  unfold values header headerContext
  simp only [pairFst_pair]
  exact original_zero HN HT HA HR (node p) hv hr

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
