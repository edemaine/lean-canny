/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.StrictUnionWitnessFormula
public import LeanCanny.Connectivity.ClosedFormulaWitness
/-! # The literal closed witness preserves components of an actual finite strict-union formula -/
@[expose] public section
namespace LeanCanny.Connectivity.StrictUnionWitnessFormula
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical

def original (m : ℕ) (t : Fin m → Term) : Formula :=
  (List.ofFn (fun i => Formula.ltZero (.mul (.const (-1)) (t i)))).foldr Formula.or .falsum

def originalDescription (n m : ℕ) (t : Fin m → Term) : Description := ⟨n,original m t⟩
def liftedDescription (n m : ℕ) (t : Fin m → Term) : Description := ⟨(n+m)+2*m,lifted n m t⟩

private theorem disjunction_holds (ps : List Formula) (env : ℕ → ℝ) :
    (ps.foldr Formula.or .falsum).Holds env ↔ ∃ p∈ps,p.Holds env := by
  induction ps with
  | nil => simp [Formula.Holds]
  | cons p ps IH => simp only [List.foldr_cons,Formula.Holds,IH,List.mem_cons,exists_eq_or_imp]

theorem original_holds (n m : ℕ) (t : Fin m → Term) (x : Fin n → ℝ) :
    (original m t).Holds (Formula.extend x) ↔ ∃ i,0<family n m t i x := by
  rw [original,disjunction_holds]
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨p,⟨i,rfl⟩,H⟩
    refine ⟨i,?_⟩
    simpa only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one,neg_one_mul,neg_lt_zero,family] using H
  · rintro ⟨i,H⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    simpa only [Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one,neg_one_mul,neg_lt_zero,family] using H

private theorem sum_scope (ts : List Term) (acc : Term) (N : ℕ)
    (ha : acc.arity≤N) (ht : ∀ t∈ts,t.arity≤N) : (TermSum.accumulate ts acc).arity≤N := by
  induction ts generalizing acc with
  | nil => exact ha
  | cons t ts IH =>
    exact IH (.add t acc) (max_le (ht t List.mem_cons_self) ha)
      (fun q hq => ht q (List.mem_cons_of_mem t hq))

theorem lifted_scope (n m : ℕ) (t : Fin m → Term) (ht : ∀ i,(t i).arity≤n) :
    (lifted n m t).arity≤(n+m)+2*m := by
  apply max_le
  · change (sumEquation n m).arity≤(n+m)+2*m
    unfold sumEquation
    apply max_le _ (Nat.zero_le _)
    apply sum_scope _ _ _ (Nat.zero_le _)
    simp only [List.forall_mem_map,List.mem_range,Term.arity]
    intro i hi
    omega
  · apply FormulaConjunctionWriter.arity
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    have HI:=i.isLt
    have HA:=ht i
    simp only [atomFormula,atomEquation,squares,Formula.arity,Term.arity,weightIndex,circleIndex,
      Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega

private theorem conjunction_closed (ps : List Formula) (h : ∀ p∈ps,ClosedFormulaWitness.Closed p) :
    ClosedFormulaWitness.Closed (FormulaConjunctionWriter.conjunction ps) := by
  induction ps with
  | nil => exact .verum
  | cons p ps IH => exact .and (h p List.mem_cons_self) (IH (fun q hq => h q (List.mem_cons_of_mem p hq)))

theorem lifted_closed (n m : ℕ) (t : Fin m → Term) : ClosedFormulaWitness.Closed (lifted n m t) := by
  apply ClosedFormulaWitness.Closed.and (.eqZero _)
  apply conjunction_closed
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact .and (.nonnegative _) (.eqZero _)

noncomputable def witnessHomeomorph (n m : ℕ) (t : Fin m → Term) (ht : ∀ i,(t i).arity≤n) :
    OpenUnionCircleWitness.Space (family n m t) ≃ₜ (liftedDescription n m t).realization :=
  (FiniteWeightedCircularCoordinates.homeomorph n m).subtype (fun z => (lifted_holds n m t ht z).symm)

noncomputable def baseHomeomorph (n m : ℕ) (t : Fin m → Term) :
    OpenUnionCircleWitness.Base (family n m t) ≃ₜ (originalDescription n m t).realization where
  toFun x := ⟨x.val,(original_holds n m t x.val).mpr x.property⟩
  invFun x := ⟨x.val,(original_holds n m t x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem lifted_preconnected_iff (n m : ℕ) (t : Fin m → Term) (ht : ∀ i,(t i).arity≤n) :
    IsPreconnected (liftedDescription n m t).realization ↔ IsPreconnected (originalDescription n m t).realization := by
  have HL := (witnessHomeomorph n m t ht).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (witnessHomeomorph n m t ht).surjective] at HL
  have HR := (baseHomeomorph n m t).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (baseHomeomorph n m t).surjective] at HR
  have HE := OpenUnionCircleWitness.preconnected_iff (family n m t)
    (fun i => FormulaStrictWitness.continuous_eval n (t i))
  have HS {A : Type} [TopologicalSpace A] (T : Set A) :
      IsPreconnected T ↔ IsPreconnected (univ : Set T) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  exact (HS (liftedDescription n m t).realization).trans
    (HL.trans (HE.trans (HR.symm.trans (HS (originalDescription n m t).realization).symm)))

end LeanCanny.Connectivity.StrictUnionWitnessFormula
