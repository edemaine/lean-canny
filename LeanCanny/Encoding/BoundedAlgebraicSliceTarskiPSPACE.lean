/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceTarski
public import LeanCanny.Algebra.TarskiQueryPSPACE

/-! # PSPACE decisions for Tarski queries in algebraic slices -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical

noncomputable def zeroLanguage (P : Readers) (F G : Family) : Language :=
  {u | RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) = 0}
noncomputable def positiveLanguage (P : Readers) (F G : Family) : Language :=
  {u | 0 < RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u)}
noncomputable def negativeLanguage (P : Readers) (F G : Family) : Language :=
  {u | RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) < 0}

theorem zero_decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (zeroLanguage P F G) := by
  have hf := ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))).flag_mem_FP
  apply (evaluator h A B ha).decider (fun z => decide (pairFst z = [] ∧ pairSnd z = [])) hf
  intro u
  simp only [zeroLanguage, Set.mem_ofPred_eq, value, decide_eq_true_eq,
    TarskiQueryBits.integerCode_fst_zero_iff, TarskiQueryBits.integerCode_snd_zero_iff]
  omega

theorem positive_decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (positiveLanguage P F G) := by
  apply (evaluator h A B ha).decider (fun z => decide (pairFst z ≠ []))
    (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [positiveLanguage, Set.mem_ofPred_eq, value, decide_eq_true_eq, ne_eq,
    TarskiQueryBits.integerCode_fst_zero_iff]
  omega

theorem negative_decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (negativeLanguage P F G) := by
  apply (evaluator h A B ha).decider (fun z => decide (pairSnd z ≠ []))
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [negativeLanguage, Set.mem_ofPred_eq, value, decide_eq_true_eq, ne_eq,
    TarskiQueryBits.integerCode_snd_zero_iff]
  omega

theorem zero_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : zeroLanguage P F G ∈ PSPACE :=
  (zero_decider h A B ha).mem_PSPACE
theorem positive_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : positiveLanguage P F G ∈ PSPACE :=
  (positive_decider h A B ha).mem_PSPACE
theorem negative_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : negativeLanguage P F G ∈ PSPACE :=
  (negative_decider h A B ha).mem_PSPACE

end LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
