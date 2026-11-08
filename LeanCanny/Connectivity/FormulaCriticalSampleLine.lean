/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaCriticalSampleRationalSlice
public import LeanCanny.Encoding.BoundedCriticalSampleLineCorrect

/-! # Native formula connectivity on lines through actual samples

Both coordinate families are constructed from the original sample readers.
Their denominators never vanish at an actual sample parameter. The guarded
formula set is therefore exactly the original formula on the coordinate line.
Native connectivity and cell-label paths validate the sample descriptor and
the free coordinate, without any supplied coordinate or incidence oracle.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaCriticalSampleLine
open Set LeanCanny.ETR LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedCriticalSampleSlice
open Turing.MultiTapeTM
open scoped Classical

noncomputable def family (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) :
    BivariateQueryProductBits.Family :=
  FormulaRationalSource.family read (BoundedCriticalSampleLineCoordinates.family P f true)
    (BoundedCriticalSampleLineCoordinates.family P f false)

noncomputable def access {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : BivariateQueryProductBits.Access (family P f read) :=
  FormulaRationalSource.family_access read hr (BoundedCriticalSampleLineCoordinates.access h hf true ha)
    (BoundedCriticalSampleLineCoordinates.access h hf false ha)

noncomputable def sampleWord (P : Readers) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : List Bool :=
  pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r

theorem sampleWord_valid (P : Readers) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    sampleWord P c r x ∈ valid P := by
  change pairFst _ ∈ BoundedCriticalSampleDescriptors.language P
  simp only [sampleWord, pairFst_pair]
  change ∃ y : BoundedFullCriticalSamples.Samples P (pairFst (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))),
    BoundedCriticalSampleHashChoice.descriptor P _ y = pairSnd (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))
  rw [pairFst_pair, pairSnd_pair]
  exact ⟨x, rfl⟩

@[simp] theorem context_sampleWord (P : Readers) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    context (sampleWord P c r x) = pair c r := by
  simp only [sampleWord, context, pairFst_pair, pairSnd_pair]

noncomputable def solutionSet (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool)
    (u : List Bool) : Set ℝ :=
  FormulaCriticalSampleRationalSlice.solutionSet P read (BoundedCriticalSampleLineCoordinates.family P f true)
    (BoundedCriticalSampleLineCoordinates.family P f false) u

theorem solutionSet_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) :
    solutionSet P f read (sampleWord P c r x) =
      {t | (FormulaView.formula (read (pair c r))).Holds
        (Function.update (Formula.extend x.val) (f (pair c r)) t)} := by
  ext t
  change (FormulaCriticalSampleRationalSlice.domain read _ _ _ t ∧ _) ↔ _
  simp only [sampleWord, context, pairFst_pair, pairSnd_pair, point_sample]
  have hd : FormulaCriticalSampleRationalSlice.domain read
      (BoundedCriticalSampleLineCoordinates.family P f false) (pair c r)
      (BoundedCriticalSampleLabels.parameter P c x).val t :=
    fun i _ => BoundedCriticalSampleLineCoordinates.denominator_nonzero P f c r x t i
  rw [and_iff_right hd, BoundedCriticalSampleLineCoordinates.environment_sample]
  rfl

theorem solutionSet_finite_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    solutionSet P f read (sampleWord P c r x) =
      {t | (FormulaView.formula (read (pair c r))).Holds
        (Formula.extend (Function.update x.val ⟨f (pair c r), hi⟩ t))} := by
  rw [solutionSet_sample]
  ext t
  simp only [Set.mem_ofPred_eq]
  rw [BoundedCriticalSampleLineCoordinates.extend_update x.val ⟨f (pair c r), hi⟩ t]

def coordinateValid (P : Readers) (f : List Bool → ℕ) (u : List Bool) : Prop :=
  f (context u) < P.dim (pairFst (pairFst u)) + 4

theorem coordinateValid_pred {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f) :
    FPPred (coordinateValid P f) := by
  have hf' : BinaryFn (fun u => f (context u)) := hf.comp context_FP
  have hn : BinaryFn (fun u => P.dim (pairFst (pairFst u)) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))).add (BinaryFn.const 4)
  exact hf'.lt hn

private theorem guarded_decider {L : Language} (D : SpaceDecider L)
    {g : List Bool → List Bool} (hg : g ∈ FP) {P : Readers} (h : P.PolyTime)
    {f : List Bool → ℕ} (hf : BinaryFn f) :
    SpaceDecider {q | coordinateValid P f (g q) ∧ q ∈ L} := by
  have H := (coordinateValid_pred h hf).comp hg
  have F : ComputableInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_tidyPolyTime (ComputableTidilyInPolyTime.const false)
  apply SpaceDecider.of_computable ((ComputableInPolySpace.of_tidyPolyTime H.computable).ite D.computable F)
  intro q
  by_cases hq : coordinateValid P f (g q) <;>
    simp only [Set.mem_ofPred_eq, hq, true_and, false_and, decide_true, decide_false,
      ite_true, ite_false, decide_eq_true_eq, Bool.false_eq_true]

noncomputable def connectedLanguage (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) : Language :=
  {u | coordinateValid P f u ∧ u ∈ valid P ∧ IsPreconnected (solutionSet P f read u)}

theorem connected_decider {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (connectedLanguage P f read) :=
  guarded_decider (SpaceDecider.ofPSPACE (FormulaCriticalSampleRationalSlice.connected_mem_PSPACE h read hr
    (BoundedCriticalSampleLineCoordinates.access h hf true ha)
    (BoundedCriticalSampleLineCoordinates.access h hf false ha) ha)) id_mem_FP h hf

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : connectedLanguage P f read ∈ PSPACE :=
  (connected_decider h hf read hr ha).mem_PSPACE

theorem connected_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    sampleWord P c r x ∈ connectedLanguage P f read ↔
      IsPreconnected {t : ℝ | (FormulaView.formula (read (pair c r))).Holds
        (Formula.extend (Function.update x.val ⟨f (pair c r), hi⟩ t))} := by
  have hc : coordinateValid P f (sampleWord P c r x) := by
    simpa only [coordinateValid, sampleWord, context, pairFst_pair, pairSnd_pair] using hi
  simp only [connectedLanguage, Set.mem_ofPred_eq, hc, sampleWord_valid, true_and, solutionSet_finite_sample P f read c r x hi]

noncomputable def reachableLanguage (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) : Language :=
  {q | coordinateValid P f (pairFst q) ∧ q ∈ CriticalSampleSliceBooleanReachability.language P
    (family P f read) (FormulaRationalSource.source read)}

theorem reachable_decider {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (reachableLanguage P f read) :=
  guarded_decider (CriticalSampleSliceBooleanReachability.decider h (access h hf read hr ha) ha
    (FormulaRationalSource.source read) (FormulaRationalSource.source_access read hr)) pairFst_mem_FP h hf

theorem reachable_mem_PSPACE {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : reachableLanguage P f read ∈ PSPACE :=
  (reachable_decider h hf read hr ha).mem_PSPACE

theorem reachable_packet (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool)
    (u : List Bool) (hu : u ∈ valid P) (hi : coordinateValid P f u)
    (a b : CriticalSampleSliceCellCover.Index P (family P f read) u) (s t : ℝ)
    (hs : s ∈ solutionSet P f read u) (ht : t ∈ solutionSet P f read u)
    (hsa : s ∈ CriticalSampleSliceCellCover.piece P (family P f read) u a)
    (htb : t ∈ CriticalSampleSliceCellCover.piece P (family P f read) u b) :
    pair u (pair (CriticalSampleSliceCellLabels.label P (family P f read) u a)
      (CriticalSampleSliceCellLabels.label P (family P f read) u b)) ∈ reachableLanguage P f read ↔
        JoinedIn (solutionSet P f read u) s t := by
  change (_ ∧ _) ↔ _
  rw [pairFst_pair, and_iff_right hi]
  exact FormulaCriticalSampleRationalSlice.reachable_packet P read _ _ u hu a b s t hs ht hsa htb

theorem connected_invalid_coordinate (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool)
    (u : List Bool) (hi : ¬ coordinateValid P f u) : u ∉ connectedLanguage P f read := fun h => hi h.1

theorem reachable_invalid_coordinate (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool)
    (u a b : List Bool) (hi : ¬ coordinateValid P f u) : pair u (pair a b) ∉ reachableLanguage P f read := by
  intro h
  exact hi (by simpa only [pairFst_pair] using h.1)

end LeanCanny.Connectivity.FormulaCriticalSampleLine
