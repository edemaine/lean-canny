/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberTestSign
public import LeanCanny.Encoding.BoundedCriticalSampleLineTerm
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Native term signs at ordered zeros on an actual-sample coordinate line

Both line polynomials are constructed from original term readers. The head
defines the distinct child roots; the test supplies a term to evaluate at
one root. The parent sample and all frozen coordinates stay fixed. A zero
head has no child labels, as in the polynomial root-list convention.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberLineTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleSlice
open scoped Classical

noncomputable def value (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool) : List Bool → List Bool :=
  BoundedCriticalSampleFiberTestSign.value P (BoundedCriticalSampleLineTerm.family P f head)
    (BoundedCriticalSampleLineTerm.family P f test)

theorem evaluator {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (head test : List Bool → List Bool) (hh : head ∈ FP) (ht : test ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P f head test) :=
  BoundedCriticalSampleFiberTestSign.evaluator h (BoundedCriticalSampleLineTerm.access h hf head hh ha)
    (BoundedCriticalSampleLineTerm.access h hf test ht ha) ha

def coordinateAllowed (P : Readers) (f : List Bool → ℕ) (u : List Bool) : Prop :=
  f (context (pairFst u)) < P.dim (pairFst (pairFst (pairFst u))) + 4
theorem coordinateAllowed_pred {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f) :
    FPPred (coordinateAllowed P f) := by
  have hfree : BinaryFn (fun u => f (context (pairFst u))) := hf.comp (mem_FP_comp pairFst_mem_FP context_FP)
  have hs : (fun u => pairFst (pairFst (pairFst u))) ∈ FP := by polytime
  have hn : BinaryFn (fun u => P.dim (pairFst (pairFst (pairFst u))) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp hs)).add (BinaryFn.const 4)
  exact hfree.lt hn

noncomputable def language (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool) (s : SignType) : Language :=
  {u | coordinateAllowed P f u ∧ u ∈ BoundedCriticalSampleFiberTestSign.language P
    (BoundedCriticalSampleLineTerm.family P f head) (BoundedCriticalSampleLineTerm.family P f test) s}

theorem language_mem_PSPACE {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (head test : List Bool → List Bool) (hh : head ∈ FP) (ht : test ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : language P f head test s ∈ PSPACE := by
  have L := (BoundedCriticalSampleFiberTestSign.decider h (BoundedCriticalSampleLineTerm.access h hf head hh ha)
    (BoundedCriticalSampleLineTerm.access h hf test ht ha) ha s).flagEvaluator
  have C := SpaceFunction.ofFP _ (coordinateAllowed_pred h hf).flag_mem_FP
  have E := C.andFlags L
  have D := E.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP (L := language P f head test s) (by
      intro u
      simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq])
  exact D.mem_PSPACE

theorem value_sample (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c)
    (r : Fin (RootCount.count P (BoundedCriticalSampleLineTerm.family P f head)
      (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d))) :
    value P f head test
      (pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val)) =
        InfinitesimalSign.encode (SignType.sign ((TermView.term (test (pair c d))).eval
          (Function.update (Formula.extend x.val) (f (pair c d))
            (BoundedCriticalSampleFiberRoot.root P (BoundedCriticalSampleLineTerm.family P f head)
              (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) r).val))) := by
  rw [value, BoundedCriticalSampleFiberTestSign.value_original, specialized_sample, BoundedCriticalSampleLineTerm.sign_sample]

theorem root_sample (P : Readers) (f : List Bool → ℕ) (head : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c)
    (r : Fin (RootCount.count P (BoundedCriticalSampleLineTerm.family P f head)
      (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d))) :
    (TermView.term (head (pair c d))).eval
      (Function.update (Formula.extend x.val) (f (pair c d))
        (BoundedCriticalSampleFiberRoot.root P (BoundedCriticalSampleLineTerm.family P f head)
          (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) r).val) = 0 := by
  have hr := BoundedCriticalSampleFiberRoot.root_eval_zero P (BoundedCriticalSampleLineTerm.family P f head) _ r
  rw [specialized_sample, BoundedCriticalSampleLineTerm.zero_sample] at hr
  exact hr

theorem value_finite_sample (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c d) < P.dim c + 4)
    (r : Fin (RootCount.count P (BoundedCriticalSampleLineTerm.family P f head)
      (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d))) :
    value P f head test
      (pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val)) =
        InfinitesimalSign.encode (SignType.sign ((TermView.term (test (pair c d))).eval
          (Formula.extend (Function.update x.val ⟨f (pair c d), hi⟩
            (BoundedCriticalSampleFiberRoot.root P (BoundedCriticalSampleLineTerm.family P f head)
              (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) r).val)))) := by
  rw [value_sample, BoundedCriticalSampleLineCoordinates.extend_update x.val ⟨f (pair c d), hi⟩]

theorem language_sample (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool) (c d : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c d) < P.dim c + 4)
    (r : Fin (RootCount.count P (BoundedCriticalSampleLineTerm.family P f head)
      (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d))) (s : SignType) :
    pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val) ∈
      language P f head test s ↔
        SignType.sign ((TermView.term (test (pair c d))).eval
          (Function.update (Formula.extend x.val) (f (pair c d))
            (BoundedCriticalSampleFiberRoot.root P (BoundedCriticalSampleLineTerm.family P f head)
              (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) r).val)) = s := by
  have hc : coordinateAllowed P f
      (pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val)) := by
    simpa only [coordinateAllowed, context, pairFst_pair, pairSnd_pair] using hi
  have hr : Nat.fromBitsLE (pairSnd
      (pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val))) <
      RootCount.count P (BoundedCriticalSampleLineTerm.family P f head)
        (pairFst (pair (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) (BinaryNatCode.encode r.val))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  change (_ ∧ _ ∧ value P f head test _ = _) ↔ _
  rw [and_iff_right hc, and_iff_right hr, value_sample]
  generalize SignType.sign ((TermView.term (test (pair c d))).eval
    (Function.update (Formula.extend x.val) (f (pair c d))
      (BoundedCriticalSampleFiberRoot.root P (BoundedCriticalSampleLineTerm.family P f head)
        (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) r).val)) = a
  cases a <;> cases s <;> decide

theorem language_invalid (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool)
    (s : SignType) (u : List Bool)
    (hu : RootCount.count P (BoundedCriticalSampleLineTerm.family P f head) (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) :
    u ∉ language P f head test s := fun h =>
  BoundedCriticalSampleFiberTestSign.language_invalid P _ _ s u hu h.2

theorem language_invalid_coordinate (P : Readers) (f : List Bool → ℕ) (head test : List Bool → List Bool)
    (s : SignType) (u : List Bool)
    (hu : P.dim (pairFst (pairFst (pairFst u))) + 4 ≤ f (context (pairFst u))) : u ∉ language P f head test s :=
  fun h => (Nat.not_lt_of_ge hu) h.1

end LeanCanny.Encoding.BoundedCriticalSampleFiberLineTest
