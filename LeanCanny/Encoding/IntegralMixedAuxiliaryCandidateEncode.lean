/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateLabel
/-! # Native bounded candidate writing and exact advice-prefix readback -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
set_option backward.isDefEq.respectTransparency false

def pad (N : ℕ) (w : List Bool) := w.take N++List.replicate (N-w.length) false

theorem pad_length (N : ℕ) (w : List Bool) : (pad N w).length=N := by
  simp only [pad,List.length_append,List.length_take,List.length_replicate]
  omega

theorem pad_eq (N : ℕ) (w : List Bool) (hw : w.length≤N) : pad N w=w++List.replicate (N-w.length) false := by
  rw [pad,List.take_of_length_le hw]

theorem pad_FP {N : List Bool → ℕ} {w : List Bool → List Bool} (hN : UnaryFn N) (hw : w∈FP) :
    (fun q => pad (N q) (w q))∈FP :=
  appendFn_mem_FP (take_mem_FP hw hN) ((hN.sub (UnaryFn.length hw)).replicate_mem_FP false)

noncomputable def encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) := pad (adviceWidth n t original) a++pad (vertexBudget hn ht ha original) w

noncomputable def encoder {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (p : List Bool) :=
  pair (pairFst p) (encode hn ht ha (pairFst p) (pairFst (pairSnd p)) (pairSnd (pairSnd p)))

theorem encoder_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : encoder hn ht ha∈FP :=
  mem_FP_pair pairFst_mem_FP (appendFn_mem_FP
    (pad_FP ((adviceWidth_unary hn ht).comp pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (pad_FP ((vertexBudget_unary hn ht ha).comp pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))

theorem encode_length {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) : (encode hn ht ha original a w).length=labelWidth hn ht ha original := by
  simp only [encode,List.length_append,pad_length,labelWidth]

theorem encode_form {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original) (hw : w.length≤vertexBudget hn ht ha original) :
    encode hn ht ha original a w=a++(w++List.replicate (vertexBudget hn ht ha original-w.length) false) := by
  rw [encode,pad_eq _ a hA.le,pad_eq _ w hw,hA,Nat.sub_self,List.replicate_zero,List.append_nil]

theorem encode_advice {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original) :
    (encode hn ht ha original a w).take (adviceWidth n t original)=a := by
  rw [encode,pad_eq _ a hA.le,hA,Nat.sub_self,List.replicate_zero,List.append_nil,←hA,List.take_left]

theorem source_encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original) :
    source n t (pair original (encode hn ht ha original a w))=IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a) := by
  unfold source sourceInput advice
  simp only [pairFst_pair,pairSnd_pair,encode_advice hn ht ha original a w hA]

theorem source_exact_advice (n : List Bool → ℕ) (t : List Bool → Term) (original a : List Bool)
    (hA : a.length=adviceWidth n t original) :
    source n t (pair original a)=IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a) := by
  unfold source sourceInput advice
  simp only [pairFst_pair,pairSnd_pair,←hA,List.take_length]

theorem vertex_fits {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original)
    (hw : w.length=SquareSampleCompleteVertices.width (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a))) :
    w.length≤vertexBudget hn ht ha original := by
  have H:=actualWidth_le_budget hn ht ha (pair original a)
  simpa only [actualWidth,source_exact_advice n t original a hA,pairFst_pair,←hw] using H
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
