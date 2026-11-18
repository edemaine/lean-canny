/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Topology.Algebra.Polynomial

/-! # Locally uniform root bounds on fixed-degree pieces -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter
open scoped Topology BigOperators Classical

variable {A : Type*} [TopologicalSpace A]

/-- A continuously varying polynomial whose actual degree is fixed has a
locally uniform upper bound on its real roots. The parameter space may itself
be a degree-piece subtype with no ambient closedness assumption. -/
theorem exists_local_polynomial_root_bound (P : A → Polynomial ℝ) (d : ℕ)
    (hcoeff : ∀ i, Continuous (fun x => (P x).coeff i))
    (hdegree : ∀ x, (P x).natDegree ≤ d) (hlead : ∀ x, (P x).coeff d ≠ 0) (x₀ : A) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ x in 𝓝 x₀, ∀ v : ℝ, R ≤ v → (P x).eval v ≠ 0 := by
  let M : A → NNReal := fun x => ∑ i ∈ Finset.range (d + 1), ‖(P x).coeff i‖₊
  let B : A → NNReal := fun x => M x / ‖(P x).coeff d‖₊ + 1
  have hM : Continuous M := continuous_finsetSum _ (fun i _ => (hcoeff i).nnNorm)
  have hB : Continuous B := (hM.div (hcoeff d).nnNorm (fun x => (by simpa only [ne_eq, nnNorm_eq_zero] using hlead x))).add continuous_const
  have hBreal : Continuous (fun x => (B x : ℝ)) := continuous_subtype_val.comp hB
  have hbound (x : A) : (P x).cauchyBound ≤ B x := by
    have hd : (P x).natDegree = d := le_antisymm (hdegree x) (le_natDegree_of_ne_zero (hlead x))
    have hsup : (Finset.range d).sup (fun i => ‖(P x).coeff i‖₊) ≤ M x := by
      apply Finset.sup_le
      intro i hi
      have hidx : i ∈ Finset.range (d + 1) := by
        have hin := Finset.mem_range.mp hi
        exact Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum (f := fun j => ‖(P x).coeff j‖₊) (fun _ _ => by positivity) hidx
    simp only [Polynomial.cauchyBound, Polynomial.leadingCoeff, hd, B]
    gcongr
  let R : ℝ := (B x₀ : ℝ) + 1
  refine ⟨R, by dsimp only [R]; positivity, ?_⟩
  have hnear : ∀ᶠ x in 𝓝 x₀, (B x : ℝ) < R :=
    hBreal.continuousAt.eventually (Iio_mem_nhds (lt_add_one (B x₀ : ℝ)))
  filter_upwards [hnear] with x hx
  intro v hv hz
  have hnz : P x ≠ 0 := by intro he; exact hlead x (by rw [he, Polynomial.coeff_zero])
  have hr := (Polynomial.IsRoot.norm_lt_cauchyBound hnz hz).trans_le (hbound x)
  have habs : |v| < (B x : ℝ) := by exact_mod_cast hr
  exact (not_lt_of_ge hv) ((le_abs_self v).trans_lt (habs.trans hx))

end LeanCanny.CountingHierarchy
