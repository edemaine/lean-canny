/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceBounds
/-! # A candidate source depends only on its fixed-width original advice prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def adviceWidth (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool) :=
  2*n original*scalarWidth n t original

def advice (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :=
  (pairSnd q).take (adviceWidth n t (pairFst q))

def sourceInput (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) := pair (pairFst q) (advice n t q)

noncomputable def source (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :=
  IntegralMixedAuxiliaryChoiceAdvice.prepare n t (sourceInput n t q)

theorem adviceWidth_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : UnaryFn (adviceWidth n t) :=
  ((UnaryFn.const 2).mul hn).mul (scalarWidth_unary hn ht)

theorem advice_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : advice n t∈FP :=
  take_mem_FP pairSnd_mem_FP ((adviceWidth_unary hn ht).comp pairFst_mem_FP)

theorem sourceInput_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : sourceInput n t∈FP :=
  mem_FP_pair pairFst_mem_FP (advice_FP hn ht)

theorem source_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : source n t∈FP :=
  mem_FP_comp (sourceInput_FP hn ht) (IntegralMixedAuxiliaryChoiceAdvice.prepare_FP hn ht)

theorem sourceInput_length (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :
    (sourceInput n t q).length≤IntegralMixedAuxiliaryChoiceAdvice.inputLength n t (pairFst q) := by
  unfold sourceInput advice IntegralMixedAuxiliaryChoiceAdvice.inputLength adviceWidth
  rw [pair_length,List.length_take]
  exact Nat.add_le_add_left (min_le_left _ _) _

theorem source_length_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    ∃ p : Polynomial ℕ, ∀ q,(source n t q).length≤p.eval (pairFst q).length := by
  obtain ⟨r,hr⟩:=output_length_poly_of_mem_FP (IntegralMixedAuxiliaryChoiceAdvice.inputLength_unary hn ht).mem_FP
  obtain ⟨p,hp⟩:=IntegralMixedAuxiliaryChoiceAdvice.prepare_length_polynomial hn ht
  refine ⟨p.comp r,fun q => ?_⟩
  have HI : (sourceInput n t q).length≤r.eval (pairFst q).length :=
    (sourceInput_length n t q).trans (by simpa only [List.length_replicate] using hr (pairFst q))
  simpa only [source,Polynomial.eval_comp] using (hp (sourceInput n t q)).trans (p.eval_mono HI)

theorem source_input (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :
    pairFst (source n t q)=pairFst q := by
  unfold source IntegralMixedAuxiliaryChoiceAdvice.prepare
  rw [IntegralMixedAuxiliaryLimitRecords.prepare_input]
  exact pairFst_pair _ _

theorem source_eq_of_prefix (n : List Bool → ℕ) (t : List Bool → Term) (original a b : List Bool)
    (h : a.take (adviceWidth n t original)=b.take (adviceWidth n t original)) :
    source n t (pair original a)=source n t (pair original b) := by
  unfold source sourceInput advice
  simp only [pairFst_pair,pairSnd_pair,h]
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
