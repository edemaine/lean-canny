/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveStack

/-! # A decreasing potential for recursive calls without child execution clocks -/

@[expose] public section

namespace LeanCanny.Computation.RecursiveStack

def waiting {F : Type} (rank fuel : F → ℕ) (N : ℕ) (stack : List F) : ℕ :=
  (stack.map fun s => fuel s * (N + 2) ^ rank s).sum

def potential {F : Type} (rank fuel : F → ℕ) (N : ℕ) (s : State F) : ℕ :=
  if s.1 then 0 else (fuel s.2.2.1 + 1) * (N + 2) ^ rank s.2.2.1 + waiting rank fuel N s.2.2.2

theorem potential_pos {F : Type} (rank fuel : F → ℕ) (N : ℕ) (s : State F) (hs : s.1 = false) :
    0 < potential rank fuel N s := by
  simp only [potential, hs, Bool.false_eq_true, ite_false]
  have hw : 0 < (N + 2) ^ rank s.2.2.1 := Nat.pow_pos (by omega)
  positivity

private theorem weighted_le (N f g r t : ℕ) (hf : g < f) (hr : t ≤ r) :
    (g + 1) * (N + 2) ^ t ≤ f * (N + 2) ^ r :=
  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hr)

private theorem child_weight_lt (N f r t : ℕ) (hf : f ≤ N) (hr : t < r) :
    (f + 1) * (N + 2) ^ t < (N + 2) ^ r := by
  calc
    _ ≤ (N + 1) * (N + 2) ^ t := Nat.mul_le_mul_right _ (by omega)
    _ < (N + 2) * (N + 2) ^ t := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
    _ = (N + 2) ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem potential_step_lt {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (hh : s.1 = false) :
    potential rank fuel N (step localStep receive s) < potential rank fuel N s := by
  rcases s with ⟨halted, output, current, stack⟩
  change halted = false at hh
  subst halted
  have hv : valid current := hs.1
  have hc : Chain localStep value rank valid (value current) (rank current) stack := hs.2
  have hpos : 0 < (fuel current + 1) * (N + 2) ^ rank current := by
    have hw : 0 < (N + 2) ^ rank current := Nat.pow_pos (by omega)
    positivity
  by_cases hd : (localStep current).1 = true
  · have ha := rules.done current hv hd
    cases stack with
    | nil => simpa only [step, Bool.false_eq_true, ite_false, ite_eq_left hd, potential, ite_true, waiting, List.map_nil, List.sum_nil, Nat.add_zero] using hpos
    | cons parent rest =>
      have hr := rules.call parent hc.1 hc.2.1 hc.2.2.1
      have he : (localStep current).2.2.1 = value (localStep parent).2.2.2 := ha.trans hc.2.2.2.1
      have hw := weighted_le N (fuel parent) (fuel (receive (parent, value (localStep parent).2.2.2)))
        (rank parent) (rank (receive (parent, value (localStep parent).2.2.2))) hr.2.2.2.2.1 hr.2.2.2.1
      simp only [step, Bool.false_eq_true, ite_false, ite_eq_left hd, he, potential, waiting, List.map_cons, List.sum_cons]
      omega
  · have hd' : (localStep current).1 = false := Bool.eq_false_iff.mpr hd
    by_cases hcall : (localStep current).2.1 = true
    · have hr := rules.call current hv hd' hcall
      have hw := child_weight_lt N (fuel (localStep current).2.2.2) (rank current) (rank (localStep current).2.2.2)
        (rules.bound _ hr.1) hr.2.1
      simp only [step, hd', hcall, Bool.false_eq_true, ite_false, ite_true, potential, waiting, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
      simp only [Nat.add_mul, Nat.one_mul] at hw hpos
      omega
    · have hcall' : (localStep current).2.1 = false := Bool.eq_false_iff.mpr hcall
      have hr := rules.next current hv hd' hcall'
      have hw := weighted_le N (fuel current) (fuel (localStep current).2.2.2) (rank current) (rank (localStep current).2.2.2) hr.2.2.1 hr.2.1
      simp only [step, hd', hcall', Bool.false_eq_true, ite_false, potential]
      have hp : 0 < (N + 2) ^ rank current := Nat.pow_pos (by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hw hpos ⊢
      omega

theorem potential_iterate_le {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (k : ℕ) :
    potential rank fuel N ((step localStep receive)^[k] s) ≤ potential rank fuel N s - k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hh : ((step localStep receive)^[k] s).1 = true
    · simp only [step, hh, ite_true, potential]
      exact Nat.zero_le _
    · have hf : ((step localStep receive)^[k] s).1 = false := Bool.eq_false_iff.mpr hh
      have h := potential_step_lt rules _ (good_iterate rules s hs k) hf
      omega

theorem halt_after {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (k : ℕ) (hk : potential rank fuel N s ≤ k) :
    ((step localStep receive)^[k] s).1 = true := by
  have h := potential_iterate_le rules s hs k
  by_contra hh
  have hp := potential_pos rank fuel N ((step localStep receive)^[k] s) (Bool.eq_false_iff.mpr hh)
  omega

theorem output_after {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (k : ℕ) (hk : potential rank fuel N s ≤ k) :
    ((step localStep receive)^[k] s).2.1 = denote receive value s := by
  have hh := halt_after rules s hs k hk
  simpa only [denote, hh, ite_true] using denote_iterate rules s hs k

theorem initial_potential_le {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : F) (hs : valid s) (R : ℕ) (hr : rank s ≤ R) :
    potential rank fuel N (initial s) ≤ (N + 2) ^ (R + 1) := by
  simp only [potential, initial, Bool.false_eq_true, ite_false, waiting, List.map_nil, List.sum_nil, Nat.add_zero]
  calc
    _ ≤ (N + 2) * (N + 2) ^ R := Nat.mul_le_mul (by have := rules.bound s hs; omega) (Nat.pow_le_pow_right (by omega) hr)
    _ = _ := by rw [pow_succ, Nat.mul_comm]

end LeanCanny.Computation.RecursiveStack
