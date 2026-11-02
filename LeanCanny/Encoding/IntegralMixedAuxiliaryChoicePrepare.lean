/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
/-! # Every bounded geometric label table has polynomial-length native advice -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

theorem table_encode (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ)
    (hc : ∀ i,(labels i).1<2^scalarWidth n t original)
    (hd : ∀ i,(labels i).2<2^scalarWidth n t original) :
    IntegralMixedAuxiliaryLimitRecords.table (fun q => n (pairFst q)) (fun _ => 0)
      (choice (scalarWidth n t)) (degree n (scalarWidth n t))
      (pair original (encode (scalarWidth n t original) labels)) =
      WordList.encode (IntegralMixedAuxiliaryRecipeRoot.words labels) := by
  unfold IntegralMixedAuxiliaryLimitRecords.table
  simp only [pairFst_pair]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,IntegralMixedAuxiliaryRecipeRoot.words,List.length_ofFn]
  · intro i hi hi'
    have HI : i<n original := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,IntegralMixedAuxiliaryRecipeRoot.words,List.getElem_ofFn,
      IntegralMixedAuxiliaryLimitRecords.entry,pairFst_pair,pairSnd_pair,List.length_replicate]
    rw [choice_encode n (scalarWidth n t) original labels ⟨i,HI⟩ (hc ⟨i,HI⟩),
      degree_encode n (scalarWidth n t) original labels ⟨i,HI⟩ (hd ⟨i,HI⟩)]

theorem prepare_encode (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ)
    (hc : ∀ i,(labels i).1≤scalarCeiling n t original)
    (hd : ∀ i,(labels i).2≤scalarCeiling n t original) :
    prepare n t (pair original (encode (scalarWidth n t original) labels)) =
      IntegralMixedAuxiliaryRecipeRoot.root original labels (encode (scalarWidth n t original) labels) := by
  have HC (i) : (labels i).1<2^scalarWidth n t original :=
    (hc i).trans_lt (Nat.lt_size_self _)
  have HD (i) : (labels i).2<2^scalarWidth n t original :=
    (hd i).trans_lt (Nat.lt_size_self _)
  unfold prepare IntegralMixedAuxiliaryLimitRecords.prepare
  rw [pairFst_pair,pairSnd_pair,table_encode n t original labels HC HD]
  rfl

theorem prepare_length_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    ∃ p : Polynomial ℕ, ∀ q,(prepare n t q).length≤p.eval q.length :=
  output_length_poly_of_mem_FP (prepare_FP hn ht)

end LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceAdvice
