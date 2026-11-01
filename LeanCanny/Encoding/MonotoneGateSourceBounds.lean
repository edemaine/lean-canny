/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateSource
public import LeanCanny.ETR.TubeZeroBounds
/-! # Literal gate scoping and fixed degree bounds for the native source -/
@[expose] public section
namespace LeanCanny.Encoding.MonotoneGateSource
open LeanCanny.Computation ETR
open scoped Classical

def outputDimension (F : Family) (c : List Bool) : ℕ := F.dimension c+3*F.count c

theorem child_arity (F : Family) (q : List Bool) (side : Bool) :
    (child F side q).arity ≤ valueIndex F q (index q) := by
  cases side <;> dsimp only [child,Bool.false_eq_true,ite_false,ite_true] <;>
    split_ifs <;> simp only [Term.arity,valueIndex] <;> omega

theorem body_arity (F : Family) (q : List Bool) (hi : index q<count F q)
    (ha : (F.atom q).arity≤dimension F q) : (body F q).arity≤valueIndex F q (index q) := by
  have HL := child_arity F q false
  have HR := child_arity F q true
  unfold body
  split_ifs
  · exact Nat.zero_le _
  · simp only [atomBody,Term.arity,witnessIndex,Bool.toNat_false,Bool.toNat_true]
    dsimp [valueIndex] at HL HR ⊢
    omega
  · simpa only [Term.arity,max_self] using max_le HL HR
  · exact max_le HL HR
  · exact Nat.zero_le _

theorem constraint_arity (F : Family) (q : List Bool) (hi : index q<count F q)
    (ha : (F.atom q).arity≤dimension F q) : (constraint F q).arity≤valueIndex F q (index q)+1 := by
  have HB := body_arity F q hi ha
  simp only [constraint,Term.arity]
  omega

theorem root_arity (F : Family) (c : List Bool) : (root F c).arity≤outputDimension F c := by
  unfold root
  split
  · exact Nat.zero_le _
  · simp only [Term.arity,outputDimension]
    omega

theorem polynomial_arity (F : Family) (c : List Bool)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (polynomial F c).arity≤outputDimension F c := by
  apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
  simp only [terms,List.forall_mem_cons,List.forall_mem_map,List.mem_range]
  refine ⟨root_arity F c,?_⟩
  intro i hi
  have HA := constraint_arity F (pair c (List.replicate i true))
    (by simpa only [index,count,pairFst_pair,pairSnd_pair,List.length_replicate] using hi) (by simpa only [dimension,pairFst_pair] using ha i hi)
  simp only [valueIndex,dimension,count,index,pairFst_pair,pairSnd_pair,List.length_replicate] at HA
  dsimp [outputDimension]
  omega

theorem outputDimension_unary (F : Family) (hF : Access F) : UnaryFn (outputDimension F) :=
  hF.dimension.add ((UnaryFn.const 3).mul hF.count)

theorem child_degree (F : Family) (q : List Bool) (side : Bool) : (child F side q).degreeBound≤1 := by
  cases side <;> dsimp only [child,Bool.false_eq_true,ite_false,ite_true] <;>
    split_ifs <;> simp only [Term.degreeBound] <;> omega

theorem body_degree (F : Family) (q : List Bool) : (body F q).degreeBound≤max (F.atom q).degreeBound 2 := by
  have HL := child_degree F q false
  have HR := child_degree F q true
  unfold body
  split_ifs
  · exact Nat.zero_le _
  · simp only [atomBody,Term.degreeBound]
    omega
  · simp only [Term.degreeBound]
    omega
  · simp only [Term.degreeBound]
    omega
  · exact Nat.zero_le _

theorem constraint_degree (F : Family) (q : List Bool) :
    (constraint F q).degreeBound≤max (F.atom q).degreeBound 2 := by
  have H := body_degree F q
  simp only [constraint,Term.degreeBound]
  omega

theorem root_degree (F : Family) (c : List Bool) : (root F c).degreeBound≤1 := by
  unfold root
  split_ifs <;> simp only [Term.degreeBound] <;> omega

private theorem accumulate_degree (ts : List Term) (acc : Term) (D : ℕ)
    (HA : acc.degreeBound≤2*D) (HT : ∀ t∈ts, t.degreeBound≤D) :
    (SumSquares.accumulate ts acc).degreeBound≤2*D := by
  induction ts generalizing acc with
  | nil => exact HA
  | cons t ts IH =>
    apply IH
    · have H := HT t (List.mem_cons_self)
      simp only [Term.square,Term.degreeBound]
      omega
    · exact fun t ht => HT t (List.mem_cons_of_mem _ ht)

theorem polynomial_degree (F : Family) (c : List Bool) (D : ℕ)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).degreeBound≤D) :
    (polynomial F c).degreeBound≤2*max D 2 := by
  apply accumulate_degree _ _ (max D 2) (Nat.zero_le _)
  simp only [terms,List.forall_mem_cons,List.forall_mem_map,List.mem_range]
  refine ⟨(root_degree F c).trans (by omega),?_⟩
  intro i hi
  exact (constraint_degree F _).trans (max_le_max (ha i hi) (le_refl 2))

end LeanCanny.Encoding.MonotoneGateSource
