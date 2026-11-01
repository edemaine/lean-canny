/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaWitness
public import LeanCanny.Connectivity.FormulaStrictWitnessWriter
/-! # Original syntax bounds all closed-Boolean witness dimensions and degrees -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaWitness
open LeanCanny.ETR Set MvPolynomial LeanCanny.Computation
open scoped Classical

theorem slots_card_le_length (p : Formula) : Nat.card (Slot p) ≤ (atoms p).length := by
  let e : Slot p ≃ (atoms p).toFinset :=
    { toFun := fun q => ⟨q.val,List.mem_toFinset.mpr q.property⟩
      invFun := fun q => ⟨q.val,List.mem_toFinset.mp q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_finsetCard]
  exact List.toFinset_card_le _

theorem atoms_length_le_size {p : Formula} (hp : Closed p) : (atoms p).length ≤ p.toData.size := by
  induction hp with
  | falsum => exact Nat.zero_le _
  | verum => exact Nat.zero_le _
  | eqZero t => simp only [atoms,List.length_singleton,Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]; omega
  | nonnegative t => simp only [atoms,List.length_singleton,Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]; omega
  | and _ _ HA HB | or _ _ HA HB =>
    simp only [atoms,List.length_append,Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
    omega

theorem atomTerm_degree_le_size {p : Formula} (hp : Closed p) :
    ∀ q ∈ atoms p, (atomTerm q).degreeBound ≤ 2*p.toData.size := by
  induction hp with
  | falsum => simp [atoms]
  | verum => simp [atoms]
  | eqZero t =>
    intro q hq
    have HQ : q=.eqZero t := by simpa only [atoms,List.mem_singleton] using hq
    rw [HQ]
    have HD := t.degreeBound_le_dataSize
    simp only [atomTerm,Term.degreeBound,Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
    omega
  | nonnegative t =>
    intro q hq
    have HQ : q=.not (.ltZero t) := by simpa only [atoms,List.mem_singleton] using hq
    rw [HQ]
    have HD := t.degreeBound_le_dataSize
    simp only [atomTerm,Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
    omega
  | and _ _ HA HB | or _ _ HA HB =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have HD := HA q hq
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega
    · have HD := HB q hq
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega

theorem polynomial_degree_le (n : ℕ) (p : Formula) (i : Slot p) :
    (polynomial n p i).totalDegree ≤ max (atomTerm i.val).degreeBound 2 := by
  have Hlow : (rename Sum.inl ((atomTerm i.val).finitePolynomial n) :
      MvPolynomial (Fin n ⊕ (Slot p × Fin 2)) ℤ).totalDegree ≤ (atomTerm i.val).degreeBound :=
    (MvPolynomial.totalDegree_rename_le _ _).trans ((atomTerm i.val).totalDegree_finitePolynomial n)
  unfold polynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (Hlow.trans (le_max_left _ _))
      (by simp only [MvPolynomial.totalDegree_X_pow]; exact le_max_right _ _))
  · simp only [MvPolynomial.totalDegree_X_pow]
    exact le_max_right _ _

theorem polynomial_original_degree {p : Formula} (hp : Closed p) (n : ℕ) (i : Slot p) :
    (polynomial n p i).totalDegree ≤ max (2*p.toData.size) 2 :=
  (polynomial_degree_le n p i).trans (max_le_max (atomTerm_degree_le_size hp i.val i.property) (le_refl 2))

def dimensionBudget (n : ℕ) (p : Formula) : ℕ := n+2*p.toData.size

theorem dimension_le {p : Formula} (hp : Closed p) (n : ℕ) :
    n+2*Nat.card (Slot p) ≤ dimensionBudget n p :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 2 ((slots_card_le_length p).trans (atoms_length_le_size hp))) n

theorem dimensionBudget_unary {n : List Bool → ℕ} {p : List Bool → Formula}
    (hn : LeanCanny.UnaryFn n) (hp : (fun q => (p q).encode) ∈ LeanCanny.FP) :
    LeanCanny.UnaryFn (fun q => dimensionBudget (n q) (p q)) := by
  have HS : LeanCanny.UnaryFn (fun q => (p q).toData.size) :=
    (LeanCanny.UnaryFn.length hp).of_eq (fun _ => LeanCanny.Data.length_toBits _)
  exact hn.add ((LeanCanny.UnaryFn.const 2).mul HS)

end LeanCanny.Connectivity.ClosedFormulaWitness
