/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRoot
public import LeanCanny.Algebra.FixedLeadingTiltedGradient

/-! # The unit-E, slope-one rule on a level-lifted spatial source

E is the first frozen coordinate, followed by selected retained parameters;
the last free coordinate is the level objective. Every rule scale is one.
The actual data scales are consequently the bank denominator, giving E=eta/Q
under the SAME interpreting hom. No legacy doubled-scale rule is identified
with this new rule.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalDilation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n k m : ℕ}

def heightExpr (select : Fin k → Fin m) (i : Fin (n+2)) : AffineExpr :=
  if hi : i.val=0 then .constant 0
  else if hk : i.val<k+1 then .reference (select ⟨i.val-1,by omega⟩).val
  else .constant 0

def rule (hkn : k ≤ n) (select : Fin k → Fin m) : Rule (n+1) where
  critical := {
    offset := ⟨k+1,by omega⟩
    objective := n-k
    coordinate := 0
    scales := fun _ => 1
    scales_ne_zero := fun _ => one_ne_zero
    heights := heightExpr select }
  height := 0
  height_frozen := by simp
  slope := 1
  slope_ne_zero := one_ne_zero

theorem objective_last (hkn : k ≤ n) (select : Fin k → Fin m) :
    (objective (rule hkn select)).val=n-k := by
  simp only [objective,rule]
  rw [Nat.mod_eq_of_lt]
  omega

theorem heightExpr_zero (select : Fin k → Fin m) : heightExpr (n:=n) select 0=.constant 0 := by
  simp [heightExpr]

theorem heightExpr_parameter (select : Fin k → Fin m) (j : Fin n) (hj : j.val<k) :
    heightExpr select j.succ.castSucc=.reference (select ⟨j.val,hj⟩).val := by
  have HN : ¬j.val+1=0 := by omega
  simp only [heightExpr,Fin.val_castSucc,Fin.val_succ,HN,dite_false]
  rw [dite_eq_left (by omega)]
  congr 2

variable {S B : ℕ} {P : SpatialSource (n+1)} {ι : Type}

theorem scale_eq (x : State P S B m ι) (hm : m ≤ S) (hkn : k ≤ n) (select : Fin k → Fin m)
    (i : Fin (n+2)) : (data x hm (rule hkn select).critical).scales i=commonDenominator x := by
  simp only [data,rule,mul_one]

theorem value_zero (x : State P S B m ι) (hkn : k ≤ n) (select : Fin k → Fin m)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (eta : ℝ) :
    heightValue x (rule hkn select) φ eta 0=eta := by
  simp [heightValue,rule,heightExpr_zero,expression]

theorem value_parameter (x : State P S B m ι) (hkn : k ≤ n) (select : Fin k → Fin m)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (eta : ℝ) (j : Fin n) (hj : j.val<k) :
    heightValue x (rule hkn select) φ eta j.succ.castSucc=
      (commonDenominator x:ℝ)*values (select ⟨j.val,hj⟩) := by
  have HN : j.succ.castSucc≠(0:Fin (n+2)) := by
    intro HZ
    have HV := congrArg Fin.val HZ
    simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero] at HV
    omega
  rw [heightValue,show (rule hkn select).critical.heights j.succ.castSucc=
      .reference (select ⟨j.val,hj⟩).val from heightExpr_parameter select j hj]
  simp only [rule,HN,ite_false,add_zero]
  rw [expression_recover x φ values H]
  simp only [AffineExpr.evaluate,dite_eq_left (select ⟨j.val,hj⟩).isLt]

noncomputable def point (x : State P S B m ι) (eta : ℝ) (old : Fin n → ℝ) (v : ℝ) : Fin (n+2) → ℝ :=
  Fin.snoc (FixedLeadingTiltedGradient.point k (eta/(commonDenominator x:ℝ)) old) v

theorem frozen (x : State P S B m ι) (hm : m ≤ S) (hkn : k ≤ n) (select : Fin k → Fin m)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (eta : ℝ) (old : Fin n → ℝ) (v : ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, old j=values (select ⟨j.val,hj⟩)) :
    ∀ i, i.val<(rule hkn select).critical.offset.val →
      ((data x hm (rule hkn select).critical).scales i:ℝ)*point (k:=k) x eta old v i=
        heightValue x (rule hkn select) φ eta i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hi
    simp only [rule,Fin.val_last] at hi
    omega
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      have H0 : (0:Fin (n+1)).castSucc=(0:Fin (n+2)) := Fin.ext rfl
      rw [scale_eq,point,Fin.snoc_castSucc]
      simp only [FixedLeadingTiltedGradient.point,Fin.cases_zero]
      rw [H0,value_zero]
      have HQ : (commonDenominator x:ℝ)≠0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
      rw [← mul_div_assoc,mul_div_cancel_left₀ _ HQ]
    · intro hi
      have HJ : j.val<k := by simp only [rule,Fin.val_castSucc,Fin.val_succ] at hi; omega
      rw [scale_eq,point,Fin.snoc_castSucc]
      simp only [FixedLeadingTiltedGradient.point,Fin.cases_succ,HJ,ite_true]
      rw [value_parameter x hkn select φ values H eta j HJ,Hparam j HJ]

end LeanCanny.Algebra.IntegralMixedCanonicalDilation
