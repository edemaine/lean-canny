/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateEncode
/-! # Canonical padding preserves each genuine complete-square vertex exactly -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
set_option backward.isDefEq.respectTransparency false

theorem vertex_encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original)
    (hw : w.length=SquareSampleCompleteVertices.width (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a))) :
    vertex hn ht ha (pair original (encode hn ht ha original a w))=w := by
  have HI : actualWidth hn ht ha (pair original (encode hn ht ha original a w))=w.length := by
    unfold actualWidth
    rw [source_encode hn ht ha original a w hA]
    exact hw.symm
  unfold vertex
  rw [pairSnd_pair,pairFst_pair,HI,encode_form hn ht ha original a w hA (vertex_fits hn ht ha original a w hA hw),
    ←hA,List.drop_left,List.take_left]

theorem padding_encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original)
    (hw : w.length=SquareSampleCompleteVertices.width (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a))) :
    padding hn ht ha (pair original (encode hn ht ha original a w))=
      List.replicate (vertexBudget hn ht ha original-w.length) false := by
  have HI : actualWidth hn ht ha (pair original (encode hn ht ha original a w))=w.length := by
    unfold actualWidth
    rw [source_encode hn ht ha original a w hA]
    exact hw.symm
  unfold padding
  rw [pairSnd_pair,pairFst_pair,HI,encode_form hn ht ha original a w hA (vertex_fits hn ht ha original a w hA hw),
    ←hA,List.drop_left,List.drop_left]

theorem guard_encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original)
    (hw : w.length=SquareSampleCompleteVertices.width (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a))) :
    Guard hn ht ha (pair original (encode hn ht ha original a w)) := by
  constructor
  · simp only [pairSnd_pair,pairFst_pair]
    exact encode_length hn ht ha original a w
  · rw [padding_encode hn ht ha original a w hA hw]
    rw [List.count_replicate]
    rfl

theorem valid_encode {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original a w : List Bool) (hA : a.length=adviceWidth n t original)
    (hw : w.length=SquareSampleCompleteVertices.width (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a)))
    (hV : SquareSampleCompleteVertices.Valid (input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original a)) w) :
    Valid hn ht ha (pair original (encode hn ht ha original a w)) := by
  refine ⟨guard_encode hn ht ha original a w hA hw,?_⟩
  rw [source_encode hn ht ha original a w hA,vertex_encode hn ht ha original a w hA hw]
  exact hV

theorem vertex_length_of_guard {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Guard hn ht ha q) :
    (vertex hn ht ha q).length=actualWidth hn ht ha q := by
  unfold vertex
  rw [List.length_take,List.length_drop,hq.1]
  change min (actualWidth hn ht ha q)
    (adviceWidth n t (pairFst q)+vertexBudget hn ht ha (pairFst q)-adviceWidth n t (pairFst q))=_
  rw [Nat.add_sub_cancel_left,min_eq_left (actualWidth_le_budget hn ht ha q)]

theorem padding_zero_iff {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (q : List Bool) :
    (padding hn ht ha q).count true=0 ↔ ∀ b∈padding hn ht ha q,b=false := by
  rw [List.count_eq_zero]
  constructor
  · intro h b hb
    cases b
    · rfl
    · exact False.elim (h hb)
  · intro h ht
    have H:=h true ht
    cases H
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
