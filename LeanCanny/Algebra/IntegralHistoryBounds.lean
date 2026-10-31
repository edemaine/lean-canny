/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryCriticalStep

/-! # Uniform degree and dimension bounds for retained histories

One bound, fixed from the birth cap and source degree, controls every old
and new row. A physical block followed by a scalar birth adds exactly
2n+4 variables. The degree bound has a native binary computation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open UniformIntegralPowerSchedule FlatAffineCriticalStage LeanCanny.Encoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m n : ℕ} {ι : Type}

def degreeBudget (S N D : ℕ) : ℕ := N * birth S N S + D * physical S N (S + 1)

theorem physical_bound (hm : m ≤ S) : physical S N m ≤ physical S N (S + 1) := by
  unfold physical
  simp only [Nat.add_sub_cancel]
  exact Nat.mul_le_mul_left _ (birth_le S N (m - 1) ((Nat.sub_le m 1).trans hm))

theorem scalar_degree_bound {D : ℕ} [Fintype ι] (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) (hF : ∀ i, F.degrees i ≤ degreeBudget S N D)
    (j : ι ⊕ Unit) : (scalarStep F hm hN p d).degrees j ≤ degreeBudget S N D := by
  cases j with
  | inl i => exact hF i
  | inr u =>
    exact (Nat.mul_le_mul_left N (birth_le S N m hm)).trans (Nat.le_add_right _ _)

theorem critical_degree_bound {D : ℕ} [Fintype ι] (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (hD : data.degree ≤ D) (hF : ∀ i, F.degrees i ≤ degreeBudget S N D)
    (j : ι ⊕ Variables (n + 1)) : (criticalStep F data).degrees j ≤ degreeBudget S N D := by
  cases j with
  | inl i => exact hF i
  | inr i =>
    apply (PhysicalPowerCriticalRows.degrees_le data.frozen data.degree (physical S N m) (by have := data.degree_two; omega) i).trans
    exact (Nat.mul_le_mul hD (physical_bound data.birth_bound)).trans (Nat.le_add_left _ _)

noncomputable def criticalScalarStep [Fintype ι] (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (data : CriticalData F.scalarPrefix n) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) :
    Sampler S N (m + 1) ((ι ⊕ Variables (n + 1)) ⊕ Unit) :=
  scalarStep (criticalStep F data) hm hN p d

theorem criticalScalarStep_degree_bound {D : ℕ} [Fintype ι] (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (data : CriticalData F.scalarPrefix n) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ)
    (hD : data.degree ≤ D) (hF : ∀ i, F.degrees i ≤ degreeBudget S N D)
    (j : (ι ⊕ Variables (n + 1)) ⊕ Unit) :
    (criticalScalarStep F hm hN data p d).degrees j ≤ degreeBudget S N D :=
  scalar_degree_bound (criticalStep F data) hm hN p d (critical_degree_bound F data hD hF) j

theorem criticalScalarStep_card [Fintype ι] :
    Fintype.card ((ι ⊕ Variables (n + 1)) ⊕ Unit) = Fintype.card ι + (2 * n + 4) := by
  simp only [Variables, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
  omega

theorem degreeBudget_binary {S N D : List Bool → ℕ} (hS : UnaryFn S) (hN : BinaryFn N) (hD : BinaryFn D) :
    BinaryFn (fun c => degreeBudget (S c) (N c) (D c)) :=
  (hN.mul (birth_binary hS hN hS)).add
    (hD.mul (physical_binary hS hN (hS.add (UnaryFn.const 1))))

end LeanCanny.Algebra.IntegralHistorySampler
