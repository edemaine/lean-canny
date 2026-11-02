/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateDecode
/-! # Every candidate source is a literal root with its decoded original label table

This identity holds on ALL words. The decoded binary labels need not lie
below the scalar ceiling; the existing total rule decoder clips those fields.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def fieldPacket (n : List Bool → ℕ) (t : List Bool → Term) (p : List Bool) :=
  pair (sourceInput n t (pairFst p)) (pairSnd p)

def decodedChoice (n : List Bool → ℕ) (t : List Bool → Term) (p : List Bool) :=
  IntegralMixedAuxiliaryChoiceAdvice.choice (scalarWidth n t) (fieldPacket n t p)

def decodedDegree (n : List Bool → ℕ) (t : List Bool → Term) (p : List Bool) :=
  IntegralMixedAuxiliaryChoiceAdvice.degree n (scalarWidth n t) (fieldPacket n t p)

def decodedLabels (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool)
    (i : Fin (n (pairFst q))) :=
  (decodedChoice n t (pair q (List.replicate i.val true)),
    decodedDegree n t (pair q (List.replicate i.val true)))

attribute [local irreducible] sourceInput adviceWidth scalarWidth scalarCeiling spatialDegree degreeCharge augmented

theorem fieldPacket_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : fieldPacket n t∈FP :=
by
  have H := mem_FP_pair (mem_FP_comp pairFst_mem_FP (sourceInput_FP hn ht)) pairSnd_mem_FP
  exact mem_FP_of_eq H (fun p => rfl)

theorem decodedChoice_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : BinaryFn (decodedChoice n t) :=
by
  have H : BinaryFn (fun p => IntegralMixedAuxiliaryChoiceAdvice.choice (scalarWidth n t) (fieldPacket n t p)) :=
    (IntegralMixedAuxiliaryChoiceAdvice.choice_binary (scalarWidth_unary hn ht)).comp (fieldPacket_FP hn ht)
  exact BinaryFn.of_eq H (fun p => rfl)

theorem decodedDegree_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) : BinaryFn (decodedDegree n t) :=
by
  have H : BinaryFn (fun p => IntegralMixedAuxiliaryChoiceAdvice.degree n (scalarWidth n t) (fieldPacket n t p)) :=
    (IntegralMixedAuxiliaryChoiceAdvice.degree_binary hn (scalarWidth_unary hn ht)).comp (fieldPacket_FP hn ht)
  exact BinaryFn.of_eq H (fun p => rfl)

theorem table_decoded (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :
    IntegralMixedAuxiliaryLimitRecords.table (fun p => n (pairFst p)) (fun _ => 0)
      (IntegralMixedAuxiliaryChoiceAdvice.choice (scalarWidth n t))
      (IntegralMixedAuxiliaryChoiceAdvice.degree n (scalarWidth n t)) (sourceInput n t q)=
      WordList.encode (IntegralMixedAuxiliaryRecipeRoot.words (decodedLabels n t q)) := by
  unfold IntegralMixedAuxiliaryLimitRecords.table
  simp only [sourceInput,pairFst_pair]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,IntegralMixedAuxiliaryRecipeRoot.words,List.length_ofFn]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,IntegralMixedAuxiliaryRecipeRoot.words,List.getElem_ofFn,
      IntegralMixedAuxiliaryLimitRecords.entry,decodedLabels,decodedChoice,decodedDegree,fieldPacket,
      sourceInput,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem source_root (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :
    source n t q=IntegralMixedAuxiliaryRecipeRoot.root (pairFst q) (decodedLabels n t q) (advice n t q) := by
  unfold source IntegralMixedAuxiliaryChoiceAdvice.prepare IntegralMixedAuxiliaryLimitRecords.prepare
  rw [table_decoded]
  simp only [sourceInput,pairFst_pair,pairSnd_pair,IntegralMixedAuxiliaryRecipeRoot.root,
    IntegralMixedAuxiliaryPreparedRoot.pack,IntegralMixedAuxiliaryPreparedRoot.packWords]

theorem source_stateHorizon (n : List Bool → ℕ) (t : List Bool → Term) (q : List Bool) :
    IntegralMixedAuxiliarySchedule.stateHorizon (IntegralMixedAuxiliaryPreparedRoot.dimension n) (source n t q)=n (pairFst q)+3 := by
  rw [source_root]
  exact IntegralMixedAuxiliaryRecipeRoot.root_stateHorizon n (pairFst q) (decodedLabels n t q) (advice n t q)
end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
