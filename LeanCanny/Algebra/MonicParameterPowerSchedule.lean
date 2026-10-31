/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterRows
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # One odd-power schedule for dependent scalar heights

The schedule depends on a uniform local degree bound, an unweighted
coefficient-degree bound, and the parameter's birth stage. It does not
depend on root labels or earlier parameter values. Old powers never change.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterPowerSchedule
open CoordinatePowerSubstitution
open scoped Classical

def ratio (D E : ℕ) : ℕ := 2 * (D * E) + 1
def weight (D E s : ℕ) : ℕ := ratio D E ^ s

theorem ratio_pos (D E : ℕ) : 0 < ratio D E := by unfold ratio; omega
theorem ratio_odd (D E : ℕ) : Odd (ratio D E) := ⟨D * E, by unfold ratio; ring⟩
theorem weight_pos (D E s : ℕ) : 0 < weight D E s := pow_pos (ratio_pos D E) s
theorem weight_odd (D E s : ℕ) : Odd (weight D E s) := (ratio_odd D E).pow

theorem weight_succ (D E s : ℕ) : weight D E (s + 1) = weight D E s * ratio D E := pow_succ _ _

theorem weight_mono (D E : ℕ) {s t : ℕ} (h : s ≤ t) : weight D E s ≤ weight D E t :=
  Nat.pow_le_pow_right (by have := ratio_pos D E; omega) h

theorem dominates (D E s d : ℕ) (hd : d ≤ D) :
    d * (weight D E s * E) < weight D E (s + 1) := by
  have HC : d * E < ratio D E := (Nat.mul_le_mul_right E hd).trans_lt (by unfold ratio; omega)
  rw [weight_succ]
  calc
    _ = weight D E s * (d * E) := by ring
    _ < weight D E s * ratio D E := Nat.mul_lt_mul_of_pos_left HC (weight_pos D E s)

theorem ratio_binary {D E : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) :
    BinaryFn (fun c => ratio (D c) (E c)) :=
  ((BinaryFn.const 2).mul (hD.mul hE)).add (BinaryFn.const 1)

theorem weight_binary {D E s : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) (hs : UnaryFn s) :
    BinaryFn (fun c => weight (D c) (E c) (s c)) := (ratio_binary hD hE).powUnary hs

theorem weight_bits (D E s : ℕ) : (weight D E s).size ≤ (ratio D E).size * s + 1 := by
  have H : weight D E s ≤ 2 ^ ((ratio D E).size * s) := by
    simpa only [weight, ← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (ratio D E)).le s
  simpa only [Nat.size_pow] using Nat.size_le_size H

variable {ι R : Type*} [CommRing R] [Fintype ι]

theorem coefficient_degree (D E s : ℕ) (w : ι → ℕ) (hw : ∀ i, w i ≤ weight D E s)
    (p : Polynomial (MvPolynomial ι R)) (hp : ∀ k, (p.coeff k).totalDegree ≤ E) (k : ℕ) :
    (substitute w (p.coeff k)).totalDegree ≤ weight D E s * E :=
  (degree_le w (p.coeff k) (weight D E s) hw).trans (Nat.mul_le_mul_left _ (hp k))

theorem row_lower_degree (D E s d : ℕ) (hd : 0 < d) (hbound : d ≤ D) (w : ι → ℕ)
    (hw : ∀ i, w i ≤ weight D E s) (p : Polynomial (MvPolynomial ι R))
    (hp : ∀ k, (p.coeff k).totalDegree ≤ E) :
    (MonicParameterRows.lower p d w (weight D E (s + 1))).totalDegree < d * weight D E (s + 1) :=
  MonicParameterRows.lower_degree p d (weight D E s * E) w (weight D E (s + 1)) hd
    (dominates D E s d hbound) (coefficient_degree D E s w hw p hp)

end LeanCanny.Algebra.MonicParameterPowerSchedule
