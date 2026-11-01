/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OpenUnionCirclePaths
public import LeanCanny.Geometry.FiniteWeightedCircularCoordinates
public import LeanCanny.Encoding.FormulaConjunctionWriter
public import LeanCanny.ETR.TermSumFP
/-! # Literal closed polynomial constraints for a finite strict union's attenuated witness -/
@[expose] public section
namespace LeanCanny.Connectivity.StrictUnionWitnessFormula
open ETR Set LeanCanny.Encoding LeanCanny.Geometry CircularWitness
open scoped BigOperators Classical

def weightIndex (n : ℕ) {m : ℕ} (i : Fin m) := n+i.val
def circleIndex (n m : ℕ) (i : Fin m) (b : Bool) := (n+m)+2*i.val+b.toNat

def squares (n m : ℕ) (i : Fin m) : Term :=
  .add (.mul (.var (circleIndex n m i false)) (.var (circleIndex n m i false)))
    (.mul (.var (circleIndex n m i true)) (.var (circleIndex n m i true)))

def atomEquation (n m : ℕ) (t : Fin m → Term) (i : Fin m) : Term :=
  .add (.mul (t i) (squares n m i))
    (.mul (.const (-1)) (.mul (.var (weightIndex n i)) (.var (weightIndex n i))))

def atomFormula (n m : ℕ) (t : Fin m → Term) (i : Fin m) : Formula :=
  .and (.not (.ltZero (.var (weightIndex n i)))) (.eqZero (atomEquation n m t i))

def sumEquation (n m : ℕ) : Term :=
  .add (TermSum.accumulate ((List.range m).map (fun i => Term.var (n+i))) (.const 0)) (.const (-1))

def lifted (n m : ℕ) (t : Fin m → Term) : Formula :=
  .and (.eqZero (sumEquation n m)) (FormulaConjunctionWriter.conjunction (List.ofFn (atomFormula n m t)))

noncomputable def family (n m : ℕ) (t : Fin m → Term) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  (t i).eval (Formula.extend x)

theorem atom_holds (n m : ℕ) (t : Fin m → Term) (ht : ∀ i, (t i).arity≤n)
    (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) (i : Fin m) :
    (atomFormula n m t i).Holds (Formula.extend (FiniteWeightedCircularCoordinates.encode n m z)) ↔
      0≤z.2.1 i ∧ family n m t i z.1*‖z.2.2 i‖^2=(z.2.1 i)^2 := by
  have H0 := FiniteWeightedCircularCoordinates.circle_eval n m z i 0
  have H1 := FiniteWeightedCircularCoordinates.circle_eval n m z i 1
  simp only [Fin.val_zero,Nat.add_zero] at H0
  simp only [Fin.val_one] at H1
  have HN : ‖z.2.2 i‖^2=(z.2.2 i 0)^2+(z.2.2 i 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  simp only [atomFormula,atomEquation,squares,Formula.Holds,Term.eval,weightIndex,circleIndex,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero,Int.cast_neg,Int.cast_one,neg_one_mul,not_lt,
    ← sub_eq_add_neg,sub_eq_zero]
  rw [FiniteWeightedCircularCoordinates.old_eval n m z (t i) (ht i),FiniteWeightedCircularCoordinates.weight_eval,
    H0,H1,HN]
  simp only [family,pow_two]

private theorem sum_range (m : ℕ) (f : ℕ → ℝ) : ((List.range m).map f).sum=∑ i∈Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m IH => simp [List.range_succ,Finset.sum_range_succ,IH]

theorem sum_eval (n m : ℕ) (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) :
    (sumEquation n m).eval (Formula.extend (FiniteWeightedCircularCoordinates.encode n m z))=(∑ i,z.2.1 i)-1 := by
  rw [sumEquation,Term.eval,TermSum.eval_accumulate]
  simp only [Term.eval,Int.cast_neg,Int.cast_one,List.map_map,Function.comp_def]
  rw [sum_range,← Fin.sum_univ_eq_sum_range]
  have HS : (∑ i : Fin m, Formula.extend (FiniteWeightedCircularCoordinates.encode n m z) (n+i.val))=∑ i,z.2.1 i := by
    apply Finset.sum_congr rfl
    intro i _
    exact FiniteWeightedCircularCoordinates.weight_eval n m z i
  rw [HS]
  ring

theorem lifted_holds (n m : ℕ) (t : Fin m → Term) (ht : ∀ i, (t i).arity≤n)
    (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) :
    (lifted n m t).Holds (Formula.extend (FiniteWeightedCircularCoordinates.encode n m z)) ↔
      (∀ i,0≤z.2.1 i) ∧ (∑ i,z.2.1 i)=1 ∧ ∀ i, family n m t i z.1*‖z.2.2 i‖^2=(z.2.1 i)^2 := by
  simp only [lifted,Formula.Holds,sum_eval,sub_eq_zero,FormulaConjunctionWriter.holds,List.mem_ofFn]
  constructor
  · rintro ⟨HS,H⟩
    have HA : ∀ i, 0≤z.2.1 i ∧ family n m t i z.1*‖z.2.2 i‖^2=(z.2.1 i)^2 :=
      fun i => (atom_holds n m t ht z i).mp (H _ ⟨i,rfl⟩)
    exact ⟨fun i => (HA i).1,HS,fun i => (HA i).2⟩
  · rintro ⟨HL,HS,HE⟩
    refine ⟨HS,?_⟩
    rintro p ⟨i,rfl⟩
    exact (atom_holds n m t ht z i).mpr ⟨HL i,HE i⟩

end LeanCanny.Connectivity.StrictUnionWitnessFormula
