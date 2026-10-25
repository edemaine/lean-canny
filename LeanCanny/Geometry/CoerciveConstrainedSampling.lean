/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoercivePolynomialSampling

/-! # Coercive sampling at isolated coordinate values

Minimization on a closed coordinate slab retains each isolated projected value
of a polynomial zero set. Compactness gives a limiting zero with that same
coordinate, and the minimizers are eventually interior critical points.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoerciveConstrainedSampling
open scoped Classical BigOperators Topology
open Filter Set MvPolynomial CoercivePolynomialSampling
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- Restricting to a closed set containing the comparison root retains the
uniform compact penalty bound. -/
theorem exists_minimizer_on (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (S : Set (Fin n → ℝ)) (hS : IsClosed S)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ S) (hroot : eval x0 q = 0)
    (s : ℝ) (hs : 0 < s) :
    ∃ y : Fin n → ℝ, y ∈ S ∧ penalty D y ≤ penalty D x0 ∧
      IsMinOn (objective q D s) S y ∧ (eval y q) ^ 2 ≤ s * penalty D x0 := by
  have hxK : x0 ∈ {x | penalty D x ≤ penalty D x0} ∩ S := by
    exact ⟨show penalty D x0 ≤ penalty D x0 from le_rfl, hx0⟩
  obtain ⟨y, hy, hm⟩ :=
    ((isCompact_sublevel (n := n) D (penalty D x0)).inter_right hS).exists_isMinOn
      ⟨x0, hxK⟩ (continuous_objective q D s).continuousOn
  have hcompare := hm hxK
  change objective q D s y ≤ objective q D s x0 at hcompare
  simp only [objective, hroot, zero_pow (by decide : 2 ≠ 0), zero_add] at hcompare
  refine ⟨y, hy.2, hy.1, ?_, ?_⟩
  · intro x hx
    by_cases hp : penalty D x ≤ penalty D x0
    · exact hm ⟨hp, hx⟩
    · have hmul : s * penalty D x0 ≤ s * penalty D x :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hp) hs.le
      exact hcompare.trans (hmul.trans (le_add_of_nonneg_left (sq_nonneg _)))
  · exact (le_add_of_nonneg_right (mul_nonneg hs.le (penalty_nonneg D y))).trans hcompare

/-- The constrained minimizers have a convergent subsequence in the same
closed set, and its limit is a zero of the original polynomial. -/
theorem exists_minimizers_subsequence_on (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (S : Set (Fin n → ℝ)) (hS : IsClosed S)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ S) (hroot : eval x0 q = 0)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Fin n → ℝ) (φ : ℕ → ℕ),
      (∀ k, y k ∈ S) ∧ (∀ k, IsMinOn (objective q D (s k)) S (y k)) ∧
      (∀ k, penalty D (y k) ≤ penalty D x0) ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 a) ∧ a ∈ S ∧ eval a q = 0 := by
  choose y hy hb hm hres using
    fun k => exists_minimizer_on q D S hS x0 hx0 hroot (s k) (hs k)
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    ((isCompact_sublevel (n := n) D (penalty D x0)).inter_right hS).tendsto_subseq
      (fun k => ⟨hb k, hy k⟩)
  refine ⟨y, a, φ, hy, hm, hb, hφ, hlim, ha.2, ?_⟩
  have hq : Tendsto (fun k => (eval (y (φ k)) q) ^ 2) atTop (𝓝 ((eval a q) ^ 2)) :=
    ((MvPolynomial.continuous_eval q).continuousAt.tendsto.comp hlim).pow 2
  have hz : Tendsto (fun k => s (φ k) * penalty D x0) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (hs0.comp hφ.tendsto_atTop).mul_const (penalty D x0)
  have hle : (eval a q) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hq hz (Eventually.of_forall fun k => hres (φ k))
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))

/-- A finite set admits a closed isolating interval at each of its points. -/
theorem exists_isolating_interval (A : Set ℝ) (hA : A.Finite) (c : ℝ) :
    ∃ a b : ℝ, a < c ∧ c < b ∧ ∀ t ∈ A, t ∈ Icc a b → t = c := by
  have hc : c ∈ (A \ {c})ᶜ := by simp
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hA.sdiff (t := {c})).isClosed.isOpen_compl.mem_nhds hc)
  refine ⟨(l + c) / 2, (c + u) / 2, by linarith [hlu.1], by linarith [hlu.2], ?_⟩
  intro t ht htab
  have htu : t ∈ Ioo l u := ⟨by linarith [htab.1, hlu.1], by linarith [htab.2, hlu.2]⟩
  by_contra hne
  exact hsub htu ⟨ht, by simpa using hne⟩

/-- For every isolated projected zero, bounded critical samples converge to
that coordinate. Criticality is needed only eventually along the subsequence. -/
theorem exists_critical_samples_at_coordinate (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (i : Fin n) (x0 : Fin n → ℝ) (hroot : eval x0 q = 0)
    (hfinite : {t : ℝ | ∃ x : Fin n → ℝ, eval x q = 0 ∧ x i = t}.Finite) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Fin n → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 a) ∧ a i = x0 i ∧ eval a q = 0 ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k))
        (pderiv j (regularization q D (1 / ((φ k : ℝ) + 1)))) = 0 := by
  obtain ⟨l, u, hl, hu, hiso⟩ := exists_isolating_interval _ hfinite (x0 i)
  let S : Set (Fin n → ℝ) := {x | x i ∈ Icc l u}
  have hS : IsClosed S := isClosed_Icc.preimage (continuous_apply i)
  obtain ⟨y, a, φ, _hy, hm, _hb, hφ, hlim, ha, hq⟩ :=
    exists_minimizers_subsequence_on q D S hS x0 ⟨hl.le, hu.le⟩ hroot
      (fun k => 1 / ((k : ℝ) + 1)) (fun k => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hai : a i = x0 i := hiso (a i) ⟨a, hq, rfl⟩ ha
  refine ⟨y, a, φ, hφ, hlim, hai, hq, ?_⟩
  have hcoord : Tendsto (fun k => y (φ k) i) atTop (𝓝 (x0 i)) := by
    rw [← hai]
    exact (continuous_apply i).continuousAt.tendsto.comp hlim
  filter_upwards [hcoord.eventually (Ioo_mem_nhds hl hu)] with k hk
  have hneigh : S ∈ 𝓝 (y (φ k)) :=
    mem_of_superset ((isOpen_Ioo.preimage (continuous_apply i)).mem_nhds hk)
      (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hlocal : IsLocalMin
      (fun x => eval x (regularization q D (1 / ((φ k : ℝ) + 1)))) (y (φ k)) := by
    simpa only [eval_regularization] using (hm (φ k)).isLocalMin hneigh
  exact (PolynomialCalculus.critical_iff (RingHom.id ℝ) _ _).mp hlocal.fderiv_eq_zero

end LeanCanny.Geometry.CoerciveConstrainedSampling
