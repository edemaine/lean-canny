/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactApproximation
public import LeanCanny.Geometry.CubePolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Small additive perturbations of a compact polynomial equation

The equation is represented by two weak inequalities and the inner cube by two
constraints per coordinate. Independent shifts have prescribed squared radius.
Nonemptiness is equivalent to feasibility at arbitrarily small positive radii.
Every fixed-radius perturbed set is compact. Generic regularity is not assumed
or proved here.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open CubeCoordinates
open scoped BigOperators

abbrev Constraint (ι : Type*) := Sum Bool (ι × Bool)

variable {ι : Type*} [Fintype ι]

noncomputable def value (p : MvPolynomial ι ℤ) (epsilon : ℝ) : Constraint ι → (ι → ℝ) → ℝ
  | .inl false, y => p.eval₂ (Int.castRingHom ℝ) y
  | .inl true, y => -p.eval₂ (Int.castRingHom ℝ) y
  | .inr (i, false), y => y i + 1 - epsilon
  | .inr (i, true), y => 1 - epsilon - y i

def feasible (p : MvPolynomial ι ℤ) (epsilon : ℝ) : Set (ι → ℝ) := {y | ∀ i, 0 ≤ value p epsilon i y}

def perturbed (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Set ((ι → ℝ) × (Constraint ι → ℝ)) :=
  {z | (∀ i, 0 ≤ value p epsilon i z.1 + z.2 i) ∧ ∑ i, z.2 i ^ 2 = delta ^ 2}

omit [Fintype ι] in
theorem feasible_eq (p : MvPolynomial ι ℤ) (epsilon : ℝ) :
    feasible p epsilon = closedCube ι epsilon ∩ {y | p.eval₂ (Int.castRingHom ℝ) y = 0} := by
  ext y
  constructor
  · intro h
    have hp := h (.inl false)
    have hn := h (.inl true)
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · have := h (.inr (i, false))
      change 0 ≤ y i + 1 - epsilon at this
      linarith
    · have := h (.inr (i, true))
      change 0 ≤ 1 - epsilon - y i at this
      linarith
    · change 0 ≤ p.eval₂ (Int.castRingHom ℝ) y at hp
      change 0 ≤ -p.eval₂ (Int.castRingHom ℝ) y at hn
      change p.eval₂ (Int.castRingHom ℝ) y = 0
      linarith
  · rintro ⟨⟨hlo, hhi⟩, hp⟩ i
    change p.eval₂ (Int.castRingHom ℝ) y = 0 at hp
    rcases i with b | ⟨j, b⟩ <;> cases b
    · simpa only [value, hp] using le_refl (0 : ℝ)
    · simp only [value, hp, neg_zero, le_refl]
    · change 0 ≤ y j + 1 - epsilon
      linarith [hlo j]
    · change 0 ≤ 1 - epsilon - y j
      linarith [hhi j]

omit [Fintype ι] in
theorem continuous_value (p : MvPolynomial ι ℤ) (epsilon : ℝ) (i : Constraint ι) : Continuous (value p epsilon i) := by
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact CubePolynomial.continuous_eval p
  · exact (CubePolynomial.continuous_eval p).neg
  · exact ((continuous_apply j).add continuous_const).sub continuous_const
  · exact (continuous_const.sub continuous_const).sub (continuous_apply j)

theorem shift_bounds (a : Constraint ι → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (ha : ∑ i, a i ^ 2 = delta ^ 2) (i : Constraint ι) : -delta ≤ a i ∧ a i ≤ delta := by
  have h : a i ^ 2 ≤ delta ^ 2 := by
    rw [← ha]
    exact Finset.single_le_sum (f := fun j => a j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq' h hd

theorem nonempty_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (hd : 0 ≤ delta)
    (h : (feasible p epsilon).Nonempty) : (perturbed p epsilon delta).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := h
  let a : Constraint ι → ℝ := fun i => if i = .inl false then delta else 0
  refine ⟨(y, a), ?_, ?_⟩
  · intro i
    apply add_nonneg (hy i)
    dsimp [a]
    split_ifs
    · exact hd
    · exact le_refl _
  · simp [a]

theorem coordinate_bounds (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hd : 0 ≤ delta)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) (hz : z ∈ perturbed p epsilon delta) :
    z.1 ∈ closedCube ι (-delta) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h := hz.1 (.inr (i, false))
    have hb := (shift_bounds z.2 delta hd hz.2 (.inr (i, false))).2
    change 0 ≤ z.1 i + 1 - epsilon + z.2 (.inr (i, false)) at h
    linarith
  · have h := hz.1 (.inr (i, true))
    have hb := (shift_bounds z.2 delta hd hz.2 (.inr (i, true))).2
    change 0 ≤ 1 - epsilon - z.1 i + z.2 (.inr (i, true)) at h
    linarith

theorem isClosed_perturbed (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : IsClosed (perturbed p epsilon delta) := by
  have hc : IsClosed {z : (ι → ℝ) × (Constraint ι → ℝ) | ∀ i, 0 ≤ value p epsilon i z.1 + z.2 i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      (((continuous_value p epsilon i).comp continuous_fst).add ((continuous_apply i).comp continuous_snd))
  have hs : Continuous (fun z : (ι → ℝ) × (Constraint ι → ℝ) => ∑ i, z.2 i ^ 2) :=
    continuous_finsetSum Finset.univ fun i _ => ((continuous_apply i).comp continuous_snd).pow 2
  exact hc.inter (isClosed_eq hs continuous_const)

theorem isCompact_perturbed (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (he : 0 ≤ epsilon) (hd : 0 ≤ delta) :
    IsCompact (perturbed p epsilon delta) := by
  have hK : IsCompact (closedCube ι (-delta) ×ˢ Set.Icc (fun _ : Constraint ι => -delta) (fun _ => delta)) :=
    (isCompact_closedCube ι (-delta)).prod isCompact_Icc
  apply hK.of_isClosed_subset (isClosed_perturbed p epsilon delta)
  intro z hz
  exact ⟨coordinate_bounds p epsilon delta he hd z hz,
    ⟨fun i => (shift_bounds z.2 delta hd hz.2 i).1, fun i => (shift_bounds z.2 delta hd hz.2 i).2⟩⟩

theorem feasible_of_arbitrarily_small (p : MvPolynomial ι ℤ) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (h : ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧ delta < eta ∧ (perturbed p epsilon delta).Nonempty) :
    (feasible p epsilon).Nonempty := by
  have ha : ∀ eta : ℝ, 0 < eta → ∃ y ∈ closedCube ι (-1), ∀ i, -eta ≤ value p epsilon i y := by
    intro eta heta
    obtain ⟨delta, hd, hde, z, hz⟩ := h (min 1 eta) (lt_min (by norm_num) heta)
    refine ⟨z.1, closedCube_mono (epsilon := -delta) (eta := -1) (by linarith [(lt_min_iff.mp hde).1])
      (coordinate_bounds p epsilon delta he hd.le z hz), ?_⟩
    intro i
    have hi := hz.1 i
    have hb := (shift_bounds z.2 delta hd.le hz.2 i).2
    have he' := (lt_min_iff.mp hde).2
    linarith
  obtain ⟨y, _, hy⟩ := CompactApproximation.exists_feasible (closedCube ι (-1)) (isCompact_closedCube ι (-1))
    (value p epsilon) (continuous_value p epsilon) ha
  exact ⟨y, hy⟩

theorem nonempty_iff_arbitrarily_small (p : MvPolynomial ι ℤ) (epsilon : ℝ) (he : 0 ≤ epsilon) :
    (feasible p epsilon).Nonempty ↔
      ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧ delta < eta ∧ (perturbed p epsilon delta).Nonempty := by
  constructor
  · intro h eta heta
    exact ⟨eta / 2, half_pos heta, half_lt_self heta, nonempty_of_feasible p epsilon _ (half_pos heta).le h⟩
  · exact feasible_of_arbitrarily_small p epsilon he

theorem nonempty_iff_eventually (p : MvPolynomial ι ℤ) (epsilon : ℝ) (he : 0 ≤ epsilon) :
    (feasible p epsilon).Nonempty ↔ ∃ d : ℝ, 0 < d ∧
      ∀ delta : ℝ, 0 < delta → delta < d → (perturbed p epsilon delta).Nonempty := by
  constructor
  · intro h
    exact ⟨1, by norm_num, fun delta hd _ => nonempty_of_feasible p epsilon delta hd.le h⟩
  · rintro ⟨d, hd, h⟩
    apply feasible_of_arbitrarily_small p epsilon he
    intro eta heta
    let delta := min d eta / 2
    have hp : 0 < min d eta := lt_min hd heta
    exact ⟨delta, half_pos hp, (half_lt_self hp).trans_le (min_le_right _ _),
      h delta (half_pos hp) ((half_lt_self hp).trans_le (min_le_left _ _))⟩

end LeanCanny.Geometry.PolynomialPerturbation
