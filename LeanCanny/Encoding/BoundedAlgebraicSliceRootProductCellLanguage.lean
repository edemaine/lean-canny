/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceRootProductQueries

/-! # Validated native cell-sign languages for an indexed family

Both the factor index and the ordered root ordinal are checked against
counts computed from the original readers. On consecutive roots of the
constructed product, acceptance is the chosen factor's sign throughout
the entire intervening cell; no divisibility hypothesis is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSliceRootProductCellLanguage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Set
open BoundedAlgebraicSlice BoundedAlgebraicSliceRootProduct
open scoped Classical

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (fromLeft : Bool) (s : SignType) : Language := {q |
  Nat.fromBitsLE (pairFst (pairSnd q)) < Q.count (pairFst (pairFst q)) ∧
    Nat.fromBitsLE (pairSnd (pairSnd q)) < count P Q (pairFst q) ∧
      BoundedAlgebraicSliceRootProductQueries.value P Q fromLeft q = InfinitesimalSign.encode s}

noncomputable def accept (Q : BivariateQueryProductBits.Family) (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairFst (pairSnd (pairFst z))) < Q.count (pairFst (pairFst (pairFst z))) ∧
    Nat.fromBitsLE (pairSnd (pairSnd (pairFst z))) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
      pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem accept_FP {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) (s : SignType) :
    (fun z => [accept Q s z]) ∈ FP := by
  have hq := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hi := BinaryFn.fromBits (mem_FP_comp hq pairFst_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp hq pairSnd_mem_FP)
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hm : BinaryFn (fun z => Q.count (pairFst (pairFst (pairFst z)))) := A.count_binary.comp hc
  have hn := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hs := Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s))
  exact ((hi.lt hm).and ((hr.lt hn).and hs)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (fromLeft : Bool) (s : SignType) : SpaceDecider (language P Q fromLeft s) := by
  have N := (count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have V := BoundedAlgebraicSliceRootProductQueries.evaluator h A ha fromLeft
  apply (N.pairOutputs V).withInput.decider (accept Q s) (accept_FP A s)
  intro q
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (fromLeft : Bool) (s : SignType) : language P Q fromLeft s ∈ PSPACE := (decider h A ha fromLeft s).mem_PSPACE

theorem interval_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (r t : Fin (count P Q u)) (hrt : t.val = r.val + 1) (s : SignType)
    (y : ℝ) (hy : y ∈ Ioo (BoundedAlgebraicSliceRootProductQueries.root P Q u r).val
      (BoundedAlgebraicSliceRootProductQueries.root P Q u t).val) :
    pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r.val)) ∈ language P Q false s ↔
      SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) = s := by
  change _ ∧ _ ∧ _ = _ ↔ _
  have hi : Nat.fromBitsLE (BinaryNatCode.encode i.val) = i.val := Nat.fromBitsLE_bits _
  have hr : Nat.fromBitsLE (BinaryNatCode.encode r.val) = r.val := Nat.fromBitsLE_bits _
  simp only [pairFst_pair, pairSnd_pair, hi, hr]
  rw [and_iff_right i.isLt, and_iff_right r.isLt, BoundedAlgebraicSliceRootProductQueries.interval_packet P Q u hu i r t hrt y hy]
  generalize SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y) = v
  cases v <;> cases s <;> decide

theorem invalid_index (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) (fromLeft : Bool) (s : SignType)
    (hq : Q.count (pairFst (pairFst q)) ≤ Nat.fromBitsLE (pairFst (pairSnd q))) :
    q ∉ language P Q fromLeft s := fun H => (Nat.not_lt_of_ge hq) H.1

theorem invalid_root (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) (fromLeft : Bool) (s : SignType)
    (hq : count P Q (pairFst q) ≤ Nat.fromBitsLE (pairSnd (pairSnd q))) :
    q ∉ language P Q fromLeft s := fun H => (Nat.not_lt_of_ge hq) H.2.1

end LeanCanny.Encoding.BoundedAlgebraicSliceRootProductCellLanguage
