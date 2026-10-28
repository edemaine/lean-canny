/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FullSampleChildCoverage
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native pairwise tests on the children of an actual parent

The input is `pair childSource parentDescriptor`. Two binary scans enumerate
regular joint candidates and retain only the specified parent fiber. The
supplied pair language receives `pair input (pair leftWord rightWord)`.
Its space cost, both enumerations, and parent selection are charged. A later
recursive path procedure must supply that pair language.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FullSampleChildPairs
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def source (q : List Bool) : List Bool := pairFst q
def parentWord (q : List Bool) : List Bool := pairSnd q
def parentLabel (q : List Bool) : List Bool := pair (pairFst (source q)) (parentWord q)
def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def leftQuery (z : List Bool) : List Bool := pair (source (origin z)) (pairSnd (pairFst z))
def rightQuery (z : List Bool) : List Bool := pair (source (origin z)) (pairSnd z)

theorem source_FP : source ∈ FP := pairFst_mem_FP
theorem parentWord_FP : parentWord ∈ FP := pairSnd_mem_FP
theorem parentLabel_FP : parentLabel ∈ FP :=
  mem_FP_pair (mem_FP_comp source_FP pairFst_mem_FP) parentWord_FP
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem leftQuery_FP : leftQuery ∈ FP := mem_FP_pair (mem_FP_comp origin_FP source_FP)
  (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP := mem_FP_pair (mem_FP_comp origin_FP source_FP) pairSnd_mem_FP

noncomputable def enumerate (F : Inputs) (q : List Bool) : List Bool :=
  SignStatisticBits.integerCode (BoundedFullSampleChildHashEnumeration.value F q)

noncomputable def prepare (F : Inputs) (z : List Bool) : List Bool :=
  pair (origin z) (pair (enumerate F (leftQuery z)) (enumerate F (rightQuery z)))

theorem prepare_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (prepare F) :=
  (SpaceFunction.ofFP origin origin_FP).pairOutputs
    (((BoundedFullSampleChildHashEnumeration.evaluator h).precompose leftQuery leftQuery_FP).pairOutputs
      ((BoundedFullSampleChildHashEnumeration.evaluator h).precompose rightQuery rightQuery_FP))

def leftSelection (q : List Bool) : List Bool :=
  pair (source (pairFst q)) (pair (parentWord (pairFst q)) (pairFst (pairSnd q)))
def rightSelection (q : List Bool) : List Bool :=
  pair (source (pairFst q)) (pair (parentWord (pairFst q)) (pairSnd (pairSnd q)))

theorem leftSelection_FP : leftSelection ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP source_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP parentWord_FP) (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
theorem rightSelection_FP : rightSelection ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP source_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP parentWord_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

def Good (F : Inputs) (L : Language) (q : List Bool) : Prop :=
  leftSelection q ∈ BoundedFullSampleChildParentSelection.language F →
    rightSelection q ∈ BoundedFullSampleChildParentSelection.language F → q ∈ L

private def accept (z : List Bool) : Bool := decide
  (pairFst z = [true] → pairFst (pairSnd z) = [true] → pairSnd (pairSnd z) = [true])

private theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have H := ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).not.or
    ((Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [true])).not.or
      (Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])))).flag_mem_FP
  exact mem_FP_of_eq H (fun z => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [accept, Function.comp_apply, imp_iff_not_or, decide_eq_true_eq])

theorem good_decider {F : Inputs} (h : F.PolyTime) {L : Language} (D : SpaceDecider L) :
    SpaceDecider {q | Good F L q} := by
  have A := ((BoundedFullSampleChildParentSelection.decider h).precompose leftSelection leftSelection_FP).flagEvaluator
  have B := ((BoundedFullSampleChildParentSelection.decider h).precompose rightSelection rightSelection_FP).flagEvaluator
  apply (A.pairOutputs (B.pairOutputs D.flagEvaluator)).decider accept accept_FP
  intro q
  simp only [Good, Set.mem_ofPred_eq, Set.mem_preimage, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

noncomputable def count (F : Inputs) (q : List Bool) : ℕ :=
  2 ^ BoundedFullSampleChildThom.labelWidth F (source q)

theorem count_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (count F) :=
  (BinaryFn.const 2).powUnary ((BoundedFullSampleChildThom.labelWidth_unary h).comp source_FP)

theorem regularCount_le (F : Inputs) (q : List Bool) :
    BoundedFullSampleChildRegularCount.count F (source q) ≤ count F q :=
  BoundedFullSampleChildRegularCount.count_le F (source q)

noncomputable def Scanned (F : Inputs) (L : Language) (q : List Bool) : Prop :=
  ∀ i < count F q, ∀ j < count F q,
    Good F L (prepare F (pair (pair q (BinaryNatCode.encode i)) (BinaryNatCode.encode j)))

theorem scanned_evaluator {F : Inputs} (h : F.PolyTime) {L : Language} (D : SpaceDecider L) :
    SpaceFunction (fun q => [decide (Scanned F L q)]) := by
  have E := (prepare_evaluator h).chain (good_decider h D).flagEvaluator
  have B := SpaceFunction.forall_binary E ((count_binary h).comp pairFst_mem_FP)
  have A := SpaceFunction.forall_binary B (count_binary h)
  exact A.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Scanned, Function.comp_apply, pairFst_pair, List.cons.injEq, and_true,
      decide_eq_true_eq, Set.mem_ofPred_eq])

noncomputable def language (F : Inputs) (L : Language) : Language :=
  {q | parentLabel q ∈ BoundedCriticalSampleDescriptors.language F.block.parent ∧ Scanned F L q}

theorem decider {F : Inputs} (h : F.PolyTime) {L : Language} (D : SpaceDecider L) :
    SpaceDecider (language F L) := by
  have P := ((BoundedCriticalSampleDescriptors.decider h.block.parent h.parentArity).precompose parentLabel parentLabel_FP).flagEvaluator
  apply (P.andFlags (scanned_evaluator h D)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.PolyTime) {L : Language} (D : SpaceDecider L) :
    language F L ∈ PSPACE := (decider h D).mem_PSPACE

theorem at_parent (F : Inputs) (L : Language) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    pair u (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) ∈ language F L ↔
      ∀ x y : BoundedFullSampleChildActualSamples.Samples F u p,
        pair (pair u (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p))
          (pair (BoundedFullSampleChildActualSamples.word F u p x)
            (BoundedFullSampleChildActualSamples.word F u p y)) ∈ L := by
  let q := pair u (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p)
  have hp : parentLabel q ∈ BoundedCriticalSampleDescriptors.language F.block.parent := by
    rw [show parentLabel q = pair (pairFst u)
      (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) from by
        simp only [parentLabel, source, parentWord, q, pairFst_pair, pairSnd_pair]]
    rw [BoundedCriticalSampleDescriptors.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
    exact ⟨p, rfl⟩
  have he (i j : ℕ) : prepare F (pair (pair q (BinaryNatCode.encode i)) (BinaryNatCode.encode j)) =
      pair q (pair (enumerate F (pair u (BinaryNatCode.encode i)))
        (enumerate F (pair u (BinaryNatCode.encode j)))) := by
    simp only [prepare, origin, leftQuery, rightQuery, source, q, pairFst_pair, pairSnd_pair]
  change (_ ∧ Scanned F L q) ↔ _
  rw [and_iff_right hp]
  constructor
  · intro hs x y
    obtain ⟨i, hi⟩ := BoundedFullSampleChildActualSamples.enumerated F u p x
    obtain ⟨j, hj⟩ := BoundedFullSampleChildActualSamples.enumerated F u p y
    change BoundedFullSampleChildActualSamples.word F u p x =
      enumerate F (pair u (BinaryNatCode.encode i.val)) at hi
    change BoundedFullSampleChildActualSamples.word F u p y =
      enumerate F (pair u (BinaryNatCode.encode j.val)) at hj
    have hn : BoundedFullSampleChildRegularCount.count F u ≤ count F q := by
      simpa only [source, q, pairFst_pair] using regularCount_le F q
    have H := hs i.val (i.isLt.trans_le hn) j.val (j.isLt.trans_le hn)
    rw [he] at H
    rw [← hi, ← hj] at H
    apply H
    · simpa only [leftSelection, source, parentWord, q, pairFst_pair, pairSnd_pair] using
        BoundedFullSampleChildActualSamples.word_valid F u p x
    · simpa only [rightSelection, source, parentWord, q, pairFst_pair, pairSnd_pair] using
        BoundedFullSampleChildActualSamples.word_valid F u p y
  · intro hs i _ j _
    rw [he]
    intro hx hy
    simp only [leftSelection, source, parentWord, q, pairFst_pair, pairSnd_pair] at hx
    simp only [rightSelection, source, parentWord, q, pairFst_pair, pairSnd_pair] at hy
    obtain ⟨x, hx⟩ := (BoundedFullSampleChildActualSamples.language_iff F u _ p).mp hx
    obtain ⟨y, hy⟩ := (BoundedFullSampleChildActualSamples.language_iff F u _ p).mp hy
    simpa only [hx, hy] using hs x y

/-- This transfer leaves only paths inside the actual lower-dimensional slice
to the recursive procedure. It includes all label and enumeration costs. -/
theorem preconnected_iff (F : Inputs) (L : Language) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4)
    (hcritical : ∀ y, (∀ i, (BoundedFullSampleChildActualSamples.spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (BoundedFullSampleChildActualSamples.spatial F u p i).eval z) y).IsInvertible)
    (hL : ∀ x y : BoundedFullSampleChildActualSamples.Samples F u p,
      pair (pair u (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p))
        (pair (BoundedFullSampleChildActualSamples.word F u p x)
          (BoundedFullSampleChildActualSamples.word F u p y)) ∈ L ↔
        JoinedIn {z | (FullSampleChildCoverage.polynomial F u p).eval z = 0}
          (BoundedFullSampleChildActualSamples.point F u p x)
          (BoundedFullSampleChildActualSamples.point F u p y)) :
    pair u (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) ∈ language F L ↔
      IsPreconnected {y | (FullSampleChildCoverage.polynomial F u p).eval y = 0} := by
  rw [at_parent, FullSampleChildCoverage.preconnected_iff_samples F u p hfit hcritical]
  exact forall_congr' fun x => forall_congr' fun y => hL x y

/-- A selected direction supplies every critical-system regularity premise. -/
theorem selected_preconnected_iff (F : BoundedFullBlockDirectionChoice.Inputs) (L : Language) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hfit : F.offset (pairFst u) + (F.free (pairFst u) + 1) ≤ F.source.dim (pairFst u) + 4)
    (hL : ∀ x y : BoundedFullSampleChildActualSamples.Samples (BoundedFullSampleSelectedDirection.child F) u p,
      pair (pair u (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p))
        (pair (BoundedFullSampleChildActualSamples.word (BoundedFullSampleSelectedDirection.child F) u p x)
          (BoundedFullSampleChildActualSamples.word (BoundedFullSampleSelectedDirection.child F) u p y)) ∈ L ↔
        JoinedIn {z | (FullSampleChildCoverage.polynomial (BoundedFullSampleSelectedDirection.child F) u p).eval z = 0}
          (BoundedFullSampleChildActualSamples.point (BoundedFullSampleSelectedDirection.child F) u p x)
          (BoundedFullSampleChildActualSamples.point (BoundedFullSampleSelectedDirection.child F) u p y)) :
    pair u (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) ∈
      language (BoundedFullSampleSelectedDirection.child F) L ↔
        IsPreconnected {y | (FullSampleChildCoverage.polynomial (BoundedFullSampleSelectedDirection.child F) u p).eval y = 0} :=
  preconnected_iff (BoundedFullSampleSelectedDirection.child F) L u p hfit
    (FullSampleChildCoverage.selected_critical_regular F u hg p) hL

/-- The initial whole source supplies selection success and containment.
Only the path language and its correctness remain for the recursive procedure. -/
theorem whole_preconnected_iff (P S : BoundedFullWriter.Readers) (L : Language) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u))
    (hL : ∀ x y : BoundedFullSampleChildActualSamples.Samples
        (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p,
      pair (pair u (BoundedCriticalSampleHashChoice.descriptor P (pairFst u) p))
        (pair (BoundedFullSampleChildActualSamples.word
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x)
          (BoundedFullSampleChildActualSamples.word
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p y)) ∈ L ↔
        JoinedIn {z | (FullSampleChildCoverage.polynomial
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p).eval z = 0}
          (BoundedFullSampleChildActualSamples.point
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x)
          (BoundedFullSampleChildActualSamples.point
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p y)) :
    pair u (BoundedCriticalSampleHashChoice.descriptor P (pairFst u) p) ∈
      language (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) L ↔
        IsPreconnected {y | (FullSampleChildCoverage.polynomial
          (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p).eval y = 0} := by
  apply selected_preconnected_iff (BoundedFullBlockDirectionChoice.whole P S) L u
    (BoundedFullBlockDirectionChoice.whole_record_good P S (pairFst u)) p ?_ hL
  change 0 + (S.dim (pairFst u) + 3 + 1) ≤ S.dim (pairFst u) + 4
  omega

theorem invalid_parent (F : Inputs) (L : Language) (q : List Bool)
    (hp : parentLabel q ∉ BoundedCriticalSampleDescriptors.language F.block.parent) :
    q ∉ language F L := fun h => hp h.1

end LeanCanny.Connectivity.FullSampleChildPairs
