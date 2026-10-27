/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLineTerm

/-! # Native existence of term zeros on sample coordinate lines

The zero-polynomial flag handles terms vanishing on the entire line.
Otherwise a native distinct-root count decides existence. The guarded
language validates both the actual sample descriptor and the free coordinate.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleLineTerm
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open scoped Classical

theorem exists_zero_iff (p : ℝ[X]) : (∃ t : ℝ, p.eval t = 0) ↔ p = 0 ∨ 0 < p.roots.toFinset.card := by
  by_cases hp : p = 0
  · simp only [hp, Polynomial.eval_zero, exists_const, true_or]
  · constructor
    · rintro ⟨t, ht⟩
      right
      apply Finset.card_pos.mpr
      refine ⟨t, ?_⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
      exact ht
    · rintro (hz | hc)
      · exact (hp hz).elim
      · obtain ⟨t, ht⟩ := Finset.card_pos.mp hc
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def] at ht
        exact ⟨t, ht⟩

noncomputable def hasZero (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) : Language :=
  {u | ∃ t : ℝ, (BoundedCriticalSampleSlice.specialized P (family P f read) u).eval t = 0}
private def rootAccept (z : List Bool) : Bool := decide (pairFst z = [] ∨ pairSnd z ≠ [])
private theorem rootAccept_FP : (fun z => [rootAccept z]) ∈ FP :=
  ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).or
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])).not).flag_mem_FP

private theorem hasZero_decider {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (hasZero P f read) := by
  let A := access h hf read hr ha
  have O := BoundedCriticalSampleSlice.offset_evaluator h A ha
  have C := BoundedCriticalSampleSlice.RootCount.count_evaluator h A ha
  apply (O.pairOutputs C).decider rootAccept rootAccept_FP
  intro u
  have ho : BinaryNatCode.encode (BoundedCriticalSampleSlice.offset P (family P f read) u) = [] ↔
      BoundedCriticalSampleSlice.specialized P (family P f read) u = 0 := by
    rw [BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff, BoundedCriticalSampleSlice.offset]
    split_ifs <;> simp_all
  have hc : BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P (family P f read) u) ≠ [] ↔
      0 < (BoundedCriticalSampleSlice.specialized P (family P f read) u).roots.toFinset.card := by
    simp only [BinaryNatCode.encode, ne_eq, BinaryNat.bits_eq_nil_iff]
    change _ ↔ 0 < BoundedCriticalSampleSlice.RootCount.count P (family P f read) u
    omega
  simp only [hasZero, Set.mem_ofPred_eq, rootAccept, pairFst_pair, pairSnd_pair, decide_eq_true_eq]
  rw [ho, hc, exists_zero_iff]

noncomputable def language (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) : Language :=
  {u | u ∈ BoundedCriticalSampleSlice.valid P ∧
    f (BoundedCriticalSampleSlice.context u) < P.dim (pairFst (pairFst u)) + 4 ∧ u ∈ hasZero P f read}

def accept (P : Readers) (f : List Bool → ℕ) (z : List Bool) : Bool := decide
  (pairFst (pairSnd z) = [true] ∧ f (BoundedCriticalSampleSlice.context (pairFst z)) <
    P.dim (pairFst (pairFst (pairFst z))) + 4 ∧ pairSnd (pairSnd z) = [true])
theorem accept_FP {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f) :
    (fun z => [accept P f z]) ∈ FP := by
  have hq : (fun z => BoundedCriticalSampleSlice.context (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := BoundedCriticalSampleSlice.context) pairFst_mem_FP BoundedCriticalSampleSlice.context_FP
  have ho : (fun z => pairFst (pairFst (pairFst z))) ∈ FP := by polytime
  have hn : BinaryFn (fun z => P.dim (pairFst (pairFst (pairFst z))) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp ho)).add (BinaryFn.const 4)
  have hfree : BinaryFn (fun z => f (BoundedCriticalSampleSlice.context (pairFst z))) := hf.comp hq
  exact ((stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [true])).and
    ((hfree.lt hn).and (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true])))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P f read) := by
  have V := (BoundedCriticalSampleSlice.valid_decider h ha).flagEvaluator
  have R := (hasZero_decider h hf read hr ha).flagEvaluator
  apply (V.pairOutputs R).withInput.decider (accept P f) (accept_FP h hf)
  intro u
  simp only [language, Set.mem_ofPred_eq, accept, pairFst_pair, pairSnd_pair, List.cons.injEq,
    and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : language P f read ∈ PSPACE :=
  (decider h hf read hr ha).mem_PSPACE

theorem language_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r ∈ language P f read ↔
      ∃ t : ℝ, (TermView.term (read (pair c r))).eval (Function.update (Formula.extend x.val) (f (pair c r)) t) = 0 := by
  have hv : pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r ∈ BoundedCriticalSampleSlice.valid P := by
    change pairFst _ ∈ BoundedCriticalSampleDescriptors.language P
    rw [pairFst_pair]
    change ∃ y : BoundedFullCriticalSamples.Samples P (pairFst (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))),
      BoundedCriticalSampleHashChoice.descriptor P _ y = pairSnd (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨x, rfl⟩
  change _ ∧ _ ∧ (∃ t : ℝ, (BoundedCriticalSampleSlice.specialized P (family P f read) _).eval t = 0) ↔ _
  rw [and_iff_right hv]
  have hfree : f (BoundedCriticalSampleSlice.context (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r)) <
      P.dim (pairFst (pairFst (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r))) + 4 := by
    simpa only [BoundedCriticalSampleSlice.context, pairFst_pair, pairSnd_pair] using hi
  rw [and_iff_right hfree]
  apply exists_congr
  intro t
  rw [BoundedCriticalSampleSlice.specialized_sample]
  exact zero_sample P f read c r x t

theorem language_invalid (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (u : List Bool)
    (hu : u ∉ BoundedCriticalSampleSlice.valid P) : u ∉ language P f read := fun h => hu h.1

theorem language_finite_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r ∈ language P f read ↔
      ∃ t : ℝ, (TermView.term (read (pair c r))).eval
        (Formula.extend (Function.update x.val ⟨f (pair c r), hi⟩ t)) = 0 := by
  rw [language_sample P f read c r x hi]
  apply exists_congr
  intro t
  rw [BoundedCriticalSampleLineCoordinates.extend_update x.val ⟨f (pair c r), hi⟩ t]

theorem language_invalid_coordinate (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (u : List Bool)
    (hu : P.dim (pairFst (pairFst u)) + 4 ≤ f (BoundedCriticalSampleSlice.context u)) : u ∉ language P f read :=
  fun h => (Nat.not_lt_of_ge hu) h.2.1

end LeanCanny.Encoding.BoundedCriticalSampleLineTerm
