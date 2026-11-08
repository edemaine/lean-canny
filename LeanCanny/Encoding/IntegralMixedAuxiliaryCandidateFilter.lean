/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateTermSemantics
/-! # Original-equation filtering of actual finite candidates is in PSPACE

The guard retains the actual fixed-width candidate validity. The original
equation is evaluated at that candidate's same joint-root bank point; neither
coordinate-root combinations nor a relative-validity oracle are inputs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Brackets
open Turing.MultiTapeTM
open scoped Classical

noncomputable def filteredLanguage {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : Language :=
  {q | ∃ hq : Valid hn ht ha q,(t (pairFst q)).eval (Formula.extend (point hn ht ha q hq))=0}

theorem filtered_decider {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    SpaceDecider (filteredLanguage hn ht ha) := by
  let Z : Language := {q | termValue hn ht ha (termQuery hn ht ha q)=InfinitesimalSign.encode 0}
  have DZ : SpaceDecider Z :=
    ((termValue_space hn ht ha).precompose (termQuery hn ht ha) (termQuery_FP hn ht ha)).decider
      (fun z=>decide (z=InfinitesimalSign.encode 0))
      (stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).flag_mem_FP
      (fun _=>by simp only [Z,Set.mem_ofPred_eq,Function.comp_apply,decide_eq_true_eq])
  have HF := ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable ((decider hn ht ha).computable.ite DZ.computable HF)
  intro q
  by_cases hq : Valid hn ht ha q
  · simp only [language,Set.mem_ofPred_eq,hq,decide_true,ite_true,decide_eq_true_eq]
    change (∃ h : Valid hn ht ha q,(t (pairFst q)).eval (Formula.extend (point hn ht ha q h))=0)↔q∈Z
    simp only [Z,Set.mem_ofPred_eq,term_sign hn ht ha q hq,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]
    exact ⟨fun ⟨_,h⟩=>h,fun h=>⟨hq,h⟩⟩
  · simp only [language,Set.mem_ofPred_eq,hq,decide_false,ite_false,Bool.false_eq_true]
    change (∃ h : Valid hn ht ha q,_)↔False
    exact ⟨fun ⟨h,_⟩=>hq h,False.elim⟩

theorem filtered_mem_PSPACE {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    filteredLanguage hn ht ha∈PSPACE := (filtered_decider hn ht ha).mem_PSPACE

private theorem extend_transport {a b : ℕ} (h : a=b) (f : Fin a→ℝ) :
    Formula.extend f=Formula.extend (fun i : Fin b=>f ⟨i.val,by omega⟩) := by
  cases h
  rfl

theorem filtered_iff_pointAt_eval {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) :
    pair original label∈filteredLanguage hn ht ha ↔
      ∃ hv : Valid hn ht ha (pair original label),
        (t original).eval (Formula.extend (pointAt hn ht ha original label hv))=0 := by
  change (∃ hv : Valid hn ht ha (pair original label),_)↔_
  apply exists_congr
  intro hv
  have HE : Formula.extend (point hn ht ha (pair original label) hv)=
      Formula.extend (pointAt hn ht ha original label hv) :=
    extend_transport (congrArg n (pairFst_pair original label)) _
  exact Iff.of_eq (congrArg (fun v : ℝ=>v=0)
    (congrArg₂ Term.eval HE (congrArg t (pairFst_pair original label))))

theorem filtered_iff_pointAt {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) :
    pair original label∈filteredLanguage hn ht ha ↔
      ∃ hv : Valid hn ht ha (pair original label),
        ((t original).finitePolynomial (n original)).eval₂ (Int.castRingHom ℝ) (pointAt hn ht ha original label hv)=0 := by
  simp only [Term.eval_finitePolynomial]
  exact filtered_iff_pointAt_eval hn ht ha original label

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
