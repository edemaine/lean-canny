/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CriticalSampleSliceCellSigns
public import LeanCanny.Connectivity.AlgebraicSliceBooleanAtoms

/-! # Native Boolean-circuit atoms on algebraic-slice cells

Each atom names an original indexed factor and a requested sign. Its native
reader computes that factor's sign on the entire cell. Gate metadata comes
from the original source, independently of the base-root and cell labels.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleSliceBooleanAtoms
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice CriticalSampleSliceCellCover
open scoped Classical

export AlgebraicSliceBooleanAtoms (Source Access semanticAtom)

def originalGate (q : List Bool) : List Bool :=
  pair (context (pairFst (pairFst q))) (pairSnd q)
theorem originalGate_FP : originalGate ∈ FP :=
  mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) context_FP) pairSnd_mem_FP

def query (S : Source) (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (BinaryNatCode.encode (S.factor (originalGate q))) (pairSnd (pairFst q)))
theorem query_FP (S : Source) (B : Access S) : query S ∈ FP := by
  have hi : BinaryFn (fun q => S.factor (originalGate q)) := B.factor.comp originalGate_FP
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair hi.bits_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : Language := {q |
  S.factor (originalGate q) < Q.count (context (pairFst (pairFst q))) ∧
    CriticalSampleSliceCellSigns.value P Q (query S q) = InfinitesimalSign.encode (S.sign (originalGate q))}

def accept (Q : BivariateQueryProductBits.Family) (S : Source) (z : List Bool) : Bool := decide
  (S.factor (originalGate (pairFst z)) < Q.count (context (pairFst (pairFst (pairFst z)))) ∧
    pairSnd z = InfinitesimalSign.encode (S.sign (originalGate (pairFst z))))

theorem accept_FP {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) (S : Source) (B : Access S) :
    (fun z => [accept Q S z]) ∈ FP := by
  have hg := mem_FP_comp pairFst_mem_FP originalGate_FP
  have hi : BinaryFn (fun z => S.factor (originalGate (pairFst z))) := B.factor.comp hg
  have hc := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) context_FP
  have hn : BinaryFn (fun z => Q.count (context (pairFst (pairFst (pairFst z))))) := A.count_binary.comp hc
  have hs := Brackets.stringEq_fppred pairSnd_mem_FP (mem_FP_comp hg B.sign)
  exact ((hi.lt hn).and hs).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceDecider (language P Q S) := by
  have E := (CriticalSampleSliceCellSigns.evaluator h A ha).precompose (query S) (query_FP S B)
  apply E.withInput.decider (accept Q S) (accept_FP A S B)
  intro q
  simp only [language, Set.mem_ofPred_eq, accept, pairFst_pair, pairSnd_pair, Function.comp_apply, decide_eq_true_eq]

noncomputable def atom (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (q : List Bool) : Bool :=
  decide (q ∈ language P Q S)

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) (k : ℕ) (y : ℝ) (hy : y ∈ piece P Q u c) :
    atom P Q S (pair (pair u (CriticalSampleSliceCellLabels.label P Q u c)) (BinaryNatCode.encode k)) =
      semanticAtom S (signVector P Q u y) (pair (context u) (BinaryNatCode.encode k)) := by
  let q := pair (context u) (BinaryNatCode.encode k)
  have hi' : originalGate (pair (pair u (CriticalSampleSliceCellLabels.label P Q u c)) (BinaryNatCode.encode k)) = q := by
    simp only [originalGate, pairFst_pair, pairSnd_pair, q]
  apply Bool.eq_iff_iff.mpr
  simp only [atom, decide_eq_true_eq, language, Set.mem_ofPred_eq, query, hi', pairFst_pair, pairSnd_pair]
  change _ ↔ semanticAtom S (signVector P Q u y) q = true
  by_cases hi : S.factor q < Q.count (context u)
  · rw [CriticalSampleSliceCellSigns.packet P Q u hu ⟨S.factor q, hi⟩ c y hy]
    simp only [hi, true_and, semanticAtom, ↓reduceDIte, signVector]
    have he (a b : SignType) : InfinitesimalSign.encode a = InfinitesimalSign.encode b ↔ decide (a = b) = true := by
      cases a <;> cases b <;> decide
    exact he _ _
  · simp only [hi, false_and, semanticAtom, ↓reduceDIte, Bool.false_eq_true]

end LeanCanny.Connectivity.CriticalSampleSliceBooleanAtoms
