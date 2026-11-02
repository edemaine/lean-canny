/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.AuxiliaryTiltEnergy

/-! # Uniformly bounded auxiliary-tilted minimizers on a closed cylinder

The original closed set can be unbounded. Comparison uses the same original
zero and a freely chosen auxiliary coordinate; hence the uniform penalty bound
does not follow from, or assume, compactness of the original zero set.
-/
@[expose] public section
namespace LeanCanny.Geometry.AuxiliaryTiltConstrainedSampling
open AuxiliaryTiltEnergy CoercivePolynomialSampling TiltedCoerciveComponentSampling
open Set Filter MvPolynomial
open scoped Classical Topology
variable {n : ℕ}

def restrict (y : Fin (n+1) → ℝ) : Fin n → ℝ := y ∘ Fin.castSucc

theorem continuous_restrict : Continuous (restrict (n:=n)) :=
  continuous_pi fun i => continuous_apply i.castSucc

def cylinder (S : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) := restrict ⁻¹' S

theorem cylinder_closed (S : Set (Fin n → ℝ)) (hS : IsClosed S) : IsClosed (cylinder S) :=
  hS.preimage continuous_restrict

theorem exists_minimizer_on (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (S : Set (Fin n → ℝ)) (hS : IsClosed S) (x0 : Fin n → ℝ) (hx0 : x0∈S) (hq : q.eval x0=0)
    (δ : ℝ) (hδ : 0<δ) (hδ4 : δ≤4) :
    ∃ y : Fin (n+1) → ℝ, y∈cylinder S ∧ penalty D y≤penalty D x0+1 ∧
      IsMinOn (TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ) (cylinder S) y ∧
      ((augmented q).eval y)^2≤δ*(penalty D x0+2)+δ^2*(penalty D x0+1) := by
  obtain ⟨a,ha0,ha1,he⟩ := exists_comparison δ hδ hδ4
  let K : Set (Fin (n+1) → ℝ) := {y | penalty D y≤penalty D x0+1}∩cylinder S
  have HA : a^(2*D+2)≤1 := by simpa using pow_le_pow_left₀ ha0 ha1 (2*D+2)
  have HC : Fin.snoc x0 a∈K := by
    constructor
    · change penalty D (Fin.snoc x0 a)≤penalty D x0+1
      rw [penalty_snoc]
      linarith
    · change (Fin.snoc x0 a) ∘ Fin.castSucc∈S
      simpa only [Function.comp_def,Fin.snoc_castSucc] using hx0
  obtain ⟨y,hy,hm⟩ := ((isCompact_sublevel D (penalty D x0+1)).inter_right (cylinder_closed S hS)).exists_isMinOn
    ⟨Fin.snoc x0 a,HC⟩ (TiltedCoerciveComponentSampling.continuous_objective (augmented q) D (Fin.last n) δ).continuousOn
  have Hpen : penalty D y≤penalty D x0+1 := hy.1
  have Hcomp : TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ y≤
      TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ (Fin.snoc x0 a) := hm HC
  have Hbound : TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) δ y≤
      a^4-δ*a+δ^2*(penalty D x0+1) := by
    rw [objective_at_zero q D δ a x0 hq] at Hcomp
    have HH := mul_le_mul_of_nonneg_left HA (sq_nonneg δ)
    nlinarith only [Hcomp,HH]
  refine ⟨y,hy.2,hy.1,?_,?_⟩
  · intro x hx
    by_cases HP : penalty D x≤penalty D x0+1
    · exact hm ⟨HP,hx⟩
    · have HL := objective_lower q D δ a he x
      have HH := mul_le_mul_of_nonneg_left (le_of_not_ge HP) (sq_nonneg δ)
      exact Hbound.trans ((add_le_add (le_refl _) HH).trans HL)
  · have HE : a^4-δ*a≤0 := by rw [he]; nlinarith [sq_nonneg (a^2)]
    have HU := coordinate_le_penalty D y (Fin.last n)
    have HY : y (Fin.last n)≤penalty D x0+2 := (le_abs_self _).trans (by linarith [Hpen])
    have HH := mul_le_mul_of_nonneg_left HY hδ.le
    have HN := mul_nonneg (sq_nonneg δ) (penalty_nonneg D y)
    unfold TiltedCoerciveComponentSampling.objective at Hbound
    nlinarith

theorem exists_minimizers_subsequence_on (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (S : Set (Fin n → ℝ)) (hS : IsClosed S) (x0 : Fin n → ℝ) (hx0 : x0∈S) (hq : q.eval x0=0)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0<δ k) (hδ4 : ∀ k, δ k≤4) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ (y : ℕ → Fin (n+1) → ℝ) (a : Fin (n+1) → ℝ) (φ : ℕ → ℕ),
      (∀ k, y k∈cylinder S) ∧
      (∀ k, IsMinOn (TiltedCoerciveComponentSampling.objective (augmented q) D (Fin.last n) (δ k)) (cylinder S) (y k)) ∧
      (∀ k, penalty D (y k)≤penalty D x0+1) ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 a) ∧ a∈cylinder S ∧ q.eval (restrict a)=0 ∧ a (Fin.last n)=0 := by
  choose y hy hb hm hr using fun k => exists_minimizer_on q D S hS x0 hx0 hq (δ k) (hδ k) (hδ4 k)
  obtain ⟨a,ha,φ,hφ,hl⟩ := ((isCompact_sublevel D (penalty D x0+1)).inter_right (cylinder_closed S hS)).tendsto_subseq
    (fun k => ⟨hb k,hy k⟩)
  have HT := hδ0.comp hφ.tendsto_atTop
  have HB : Tendsto (fun k => δ (φ k)*(penalty D x0+2)+(δ (φ k))^2*(penalty D x0+1)) atTop (𝓝 0) := by
    simpa using (HT.mul_const _).add ((HT.pow 2).mul_const _)
  have HQ := ((MvPolynomial.continuous_eval (augmented q)).continuousAt.tendsto.comp hl).pow 2
  have HE := le_of_tendsto_of_tendsto HQ HB (Eventually.of_forall fun k => hr (φ k))
  have HZ : (augmented q).eval a=0 := sq_eq_zero_iff.mp (le_antisymm HE (sq_nonneg _))
  have H := (augmented_zero_iff q a).mp HZ
  exact ⟨y,a,φ,hy,hm,hb,hφ,hl,ha.2,H.1,H.2⟩

end LeanCanny.Geometry.AuxiliaryTiltConstrainedSampling
