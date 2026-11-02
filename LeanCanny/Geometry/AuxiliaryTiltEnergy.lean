/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TiltedCoerciveComponentSampling
public import LeanCanny.Geometry.PurePowerSublevelLift

/-! # A bounded auxiliary tilt on an unbounded original zero set

The new equation is q(x)^2+z^2. Only z is tilted. Its quartic energy has a
common lower bound, independent of x, so comparison at any original zero
bounds the entire Fermat penalty. The original tilted-coordinate counterexample
q=0 does not apply to this augmented source.
-/
@[expose] public section
namespace LeanCanny.Geometry.AuxiliaryTiltEnergy
open LeanCanny.Algebra MvPolynomial CoercivePolynomialSampling
open scoped Classical BigOperators
variable {n : ℕ}

noncomputable def augmented (q : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  (rename Fin.castSucc q)^2+X (Fin.last n)^2

theorem eval_augmented (q : MvPolynomial (Fin n) ℝ) (y : Fin (n+1) → ℝ) :
    (augmented q).eval y=(q.eval (y ∘ Fin.castSucc))^2+(y (Fin.last n))^2 := by
  simp only [augmented,eval_add,eval_pow,eval_rename,eval_X]

theorem augmented_zero_iff (q : MvPolynomial (Fin n) ℝ) (y : Fin (n+1) → ℝ) :
    (augmented q).eval y=0 ↔ q.eval (y ∘ Fin.castSucc)=0 ∧ y (Fin.last n)=0 := by
  rw [eval_augmented]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (q.eval (y ∘ Fin.castSucc)),sq_nonneg (y (Fin.last n))]
  · rintro ⟨h,hz⟩
    rw [h,hz]
    norm_num

theorem quartic_lower (a z δ : ℝ) (hδ : δ=4*a^3) : a^4-δ*a ≤ z^4-δ*z := by
  have H : 0≤(z-a)^2*((z+a)^2+2*a^2) := mul_nonneg (sq_nonneg _) (by positivity)
  rw [hδ]
  nlinarith only [H]

theorem exists_comparison (δ : ℝ) (hδ : 0<δ) (hδ4 : δ≤4) :
    ∃ a : ℝ, 0≤a ∧ a≤1 ∧ δ=4*a^3 := by
  obtain ⟨a,ha⟩ := PurePowerSublevelLift.real_pow_surjective 3 (by decide : Odd 3) (δ/4)
  change a^3=δ/4 at ha
  have ha0 : 0≤a := by
    by_contra HN
    have H := (by decide : Odd 3).pow_neg (lt_of_not_ge HN)
    linarith
  have ha1 : a≤1 := by
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (by norm_num : (0:ℝ)≤1)
    rw [ha]
    norm_num
    linarith
  exact ⟨a,ha0,ha1,by linarith⟩

theorem objective_lower (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (δ a : ℝ) (hδ : δ=4*a^3)
    (y : Fin (n+1) → ℝ) :
    a^4-δ*a+δ^2*penalty D y ≤ TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ y := by
  rw [TiltedCoerciveComponentSampling.objective,eval_augmented]
  have H := quartic_lower a (y (Fin.last n)) δ hδ
  nlinarith [sq_nonneg (q.eval (y ∘ Fin.castSucc)),sq_nonneg (y (Fin.last n)),
    mul_nonneg (sq_nonneg (q.eval (y ∘ Fin.castSucc))) (sq_nonneg (y (Fin.last n)))]

theorem penalty_snoc (D : ℕ) (x : Fin n → ℝ) (a : ℝ) :
    penalty D (Fin.snoc x a)=penalty D x+a^(2*D+2) := by
  simp only [penalty,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

theorem objective_at_zero (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (δ a : ℝ)
    (x : Fin n → ℝ) (hx : q.eval x=0) :
    TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ (Fin.snoc x a)=
      a^4-δ*a+δ^2*(penalty D x+a^(2*D+2)) := by
  rw [TiltedCoerciveComponentSampling.objective,eval_augmented,penalty_snoc]
  have HE : (Fin.snoc x a) ∘ Fin.castSucc=x := by funext i; simp
  rw [HE,hx,Fin.snoc_last]
  ring

theorem comparison_penalty (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (δ a : ℝ)
    (hδ : 0<δ) (ha0 : 0≤a) (ha1 : a≤1) (he : δ=4*a^3)
    (x : Fin n → ℝ) (hx : q.eval x=0) (y : Fin (n+1) → ℝ)
    (hcompare : TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ y≤
      TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ (Fin.snoc x a)) :
    penalty D y≤penalty D x+1 := by
  have H := (objective_lower q D δ a he y).trans hcompare
  rw [objective_at_zero q D δ a x hx] at H
  have HA : a^(2*D+2)≤1 := by simpa using pow_le_pow_left₀ ha0 ha1 (2*D+2)
  have HE : δ^2*penalty D y≤δ^2*(penalty D x+1) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hδ)).mp HE

end LeanCanny.Geometry.AuxiliaryTiltEnergy
