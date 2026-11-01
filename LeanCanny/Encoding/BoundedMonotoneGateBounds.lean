/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateSource
public import LeanCanny.Connectivity.InputFP
/-! # One original-atom degree cap for the bounded circle compiler -/
@[expose] public section
namespace LeanCanny.Encoding.BoundedMonotoneGateSource
open ETR LeanCanny.Computation MonotoneGateSource
open scoped Classical

private theorem accumulate_degree (ts : List Term) (acc : Term) (D : ℕ)
    (HA : acc.degreeBound≤2*D) (HT : ∀ t∈ts, t.degreeBound≤D) :
    (SumSquares.accumulate ts acc).degreeBound≤2*D := by
  induction ts generalizing acc with
  | nil => exact HA
  | cons t ts IH =>
    apply IH
    · have H := HT t List.mem_cons_self
      simp only [Term.square,Term.degreeBound]
      omega
    · exact fun t ht => HT t (List.mem_cons_of_mem _ ht)

theorem budget_arity (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (query c i)).arity≤F.dimension c) :
    (budget F c).arity≤F.dimension c := by
  have H : (SumSquares.accumulate (atoms F c) (.const 0)).arity≤F.dimension c := by
    apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
    simpa only [atoms,List.forall_mem_map,List.mem_range] using ha
  simp only [budget,Term.arity]
  omega

theorem budget_degree (F : Family) (c : List Bool) (D : ℕ)
    (ha : ∀ i < F.count c, (F.atom (query c i)).degreeBound≤D) :
    (budget F c).degreeBound≤2*D := by
  have H : (SumSquares.accumulate (atoms F c) (.const 0)).degreeBound≤2*D := by
    apply accumulate_degree _ _ _ (Nat.zero_le _)
    simpa only [atoms,List.forall_mem_map,List.mem_range] using ha
  simp only [budget,Term.degreeBound]
  omega

theorem slack_arity (F : Family) (c : List Bool) (i : ℕ) (hi : i < F.count c)
    (ha : ∀ j < F.count c, (F.atom (query c j)).arity≤F.dimension c) :
    (slack F (query c i)).arity≤total F c := by
  have H := budget_arity F c ha
  simp only [slack,Term.arity,witnessIndex,slackIndex,dimension,count,index,query,
    pairFst_pair,pairSnd_pair,List.length_replicate,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  dsimp [total]
  omega

theorem slack_degree (F : Family) (c : List Bool) (i D : ℕ)
    (ha : ∀ j < F.count c, (F.atom (query c j)).degreeBound≤D) :
    (slack F (query c i)).degreeBound≤2*max D 2 := by
  have H := budget_degree F c D ha
  simp only [slack,Term.degreeBound,query,pairFst_pair]
  omega

theorem polynomial_arity (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (query c i)).arity≤F.dimension c) :
    (polynomial F c).arity≤total F c := by
  have H := MonotoneGateSource.polynomial_arity F c ha
  have HS : (SumSquares.accumulate (slacks F c) (.const 0)).arity≤total F c := by
    apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
    simp only [slacks,List.forall_mem_map,List.mem_range]
    exact fun i hi => slack_arity F c i hi ha
  simp only [polynomial,Term.arity]
  dsimp [MonotoneGateSource.outputDimension,total] at H HS ⊢
  omega

theorem polynomial_degree (F : Family) (c : List Bool) (D : ℕ)
    (ha : ∀ i < F.count c, (F.atom (query c i)).degreeBound≤D) :
    (polynomial F c).degreeBound≤4*max D 2 := by
  have H := MonotoneGateSource.polynomial_degree F c D ha
  have HS : (SumSquares.accumulate (slacks F c) (.const 0)).degreeBound≤2*(2*max D 2) := by
    apply accumulate_degree _ _ _ (Nat.zero_le _)
    simp only [slacks,List.forall_mem_map,List.mem_range]
    exact fun i _ => slack_degree F c i D ha
  simp only [polynomial,Term.degreeBound]
  omega

def description (F : Family) (c : List Bool) : Connectivity.Description :=
  ⟨total F c,.eqZero (polynomial F c)⟩
theorem description_wellFormed (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (query c i)).arity≤F.dimension c) :
    (description F c).WellFormed := polynomial_arity F c ha

theorem whole_record_FP (F : Family) (hF : Access F) :
    (fun c => (Connectivity.Input.whole (description F c)).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP (total_unary F hF))
    (Codec.taggedOne_mem_FP 1 (polynomial_FP F hF))
  apply mem_FP_of_eq H
  intro c
  simp only [Codec.taggedOne_toBits,Codec.taggedTwo_toBits,Connectivity.Input.encode,
    Connectivity.Input.toData,description,Formula.toData]

end LeanCanny.Encoding.BoundedMonotoneGateSource
