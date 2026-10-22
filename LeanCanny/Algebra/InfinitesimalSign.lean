/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic

/-!
# Signs for a sufficiently small positive parameter

Canny's deterministic construction in Lemma 2.4 uses powers of an arbitrarily
small positive parameter. A nonzero polynomial has, throughout some positive
interval, the sign of its lowest nonzero coefficient. The zero polynomial is
included, and a finite collection admits a common interval.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalSign
open Polynomial Filter Set
open scoped Topology

theorem factor_at_trailingDegree {R : Type*} [Semiring R] (p : R[X]) :
    ∃ q : R[X], p = X ^ p.natTrailingDegree * q ∧ q.coeff 0 = p.trailingCoeff := by
  obtain ⟨q, hq⟩ := (Polynomial.X_pow_dvd_iff.mpr
    (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi) : X ^ p.natTrailingDegree ∣ p)
  refine ⟨q, hq, ?_⟩
  have hc := congrArg (fun f : R[X] => f.coeff p.natTrailingDegree) hq
  simpa only [Polynomial.coeff_X_pow_mul', Nat.le_refl, ↓reduceIte, Nat.sub_self, Polynomial.trailingCoeff] using hc.symm

theorem natTrailingDegree_map_injective {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    (p.map f).natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · have hc : (p.map f).coeff p.natTrailingDegree ≠ 0 := by
      rw [Polynomial.coeff_map]
      intro h
      exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp) (hf (h.trans f.map_zero.symm))
    have hm : p.map f ≠ 0 := by
      intro h
      exact hc (by simp only [h, Polynomial.coeff_zero])
    apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
    apply Polynomial.le_natTrailingDegree hm
    intro i hi
    simp only [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, map_zero]

theorem trailingCoeff_map_injective {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    (p.map f).trailingCoeff = f p.trailingCoeff := by
  simp only [Polynomial.trailingCoeff, natTrailingDegree_map_injective f hf, Polynomial.coeff_map]

theorem sign_eval_eq_trailingCoeff (p : ℝ[X]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ → SignType.sign (p.eval x) = SignType.sign p.trailingCoeff := by
  by_cases hp : p = 0
  · exact ⟨1, by norm_num, by simp [hp]⟩
  obtain ⟨q, hq, hq0⟩ := factor_at_trailingDegree p
  have hzero : q.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hq0]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hsame : ∀ᶠ x in 𝓝 (0 : ℝ), SignType.sign (q.eval x) = SignType.sign (q.eval 0) := by
    have hcont : ContinuousAt (fun x : ℝ => SignType.sign (q.eval x)) 0 :=
      ContinuousAt.comp (f := fun x : ℝ => q.eval x) (x := 0)
        (continuousAt_sign_of_ne_zero hzero) q.continuousAt
    simpa only [ContinuousAt, nhds_discrete, tendsto_pure] using hcont
  obtain ⟨l, u, hlu, hsub⟩ := hsame.exists_Ioo_subset
  refine ⟨u, hlu.2, ?_⟩
  intro x hx hxu
  have hs := hsub (show x ∈ Ioo l u from ⟨hlu.1.trans hx, hxu⟩)
  change SignType.sign (q.eval x) = SignType.sign (q.eval 0) at hs
  have heval : p.eval x = x ^ p.natTrailingDegree * q.eval x := by
    conv_lhs => rw [hq]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, sign_mul, sign_pos (pow_pos hx _), one_mul]
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, hq0] using hs

theorem finite_sign_eval_eq_trailingCoeff {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, ∀ x, 0 < x → x < δ →
      SignType.sign ((p i).eval x) = SignType.sign (p i).trailingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨δ, hδ, hs⟩ := ih
    obtain ⟨ε, hε, hi⟩ := sign_eval_eq_trailingCoeff (p i)
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro j hj x hx hmin
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi x hx (hmin.trans_le (min_le_right _ _))
    · exact hs j hj x hx (hmin.trans_le (min_le_left _ _))

theorem integer_sign_eval_eq_trailingCoeff (p : ℤ[X]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      SignType.sign (p.eval₂ (Int.castRingHom ℝ) x) = SignType.sign p.trailingCoeff := by
  obtain ⟨δ, hδ, hs⟩ := sign_eval_eq_trailingCoeff (p.map (Int.castRingHom ℝ))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd
  have hcast : Function.Injective (Int.castRingHom ℝ) := by
    intro a b hab
    exact Int.cast_injective hab
  have he := hs x hx hxd
  rw [Polynomial.eval_map, trailingCoeff_map_injective (Int.castRingHom ℝ) hcast] at he
  change SignType.sign (p.eval₂ (Int.castRingHom ℝ) x) = SignType.sign (p.trailingCoeff : ℝ) at he
  simpa only [sign_intCast] using he

theorem finite_integer_sign_eval_eq_trailingCoeff {ι : Type*} (s : Finset ι) (p : ι → ℤ[X]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, ∀ x, 0 < x → x < δ →
      SignType.sign ((p i).eval₂ (Int.castRingHom ℝ) x) = SignType.sign (p i).trailingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨δ, hδ, hs⟩ := ih
    obtain ⟨ε, hε, hi⟩ := integer_sign_eval_eq_trailingCoeff (p i)
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro j hj x hx hmin
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi x hx (hmin.trans_le (min_le_right _ _))
    · exact hs j hj x hx (hmin.trans_le (min_le_left _ _))

end LeanCanny.Algebra.InfinitesimalSign
