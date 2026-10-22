/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/RealClosed/Sign.lean.
Changes: selected proof slice, project namespace, real specialization where needed,
and compatibility with the pinned Mathlib. See STURM_SOURCES.md.
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

/-! # Constant signs and simple-root crossings over the reals
-/

public section

namespace LeanCanny.Algebra.Sturm

open Polynomial List

section



/-- A polynomial has a constant sign on a root-free interval. -/
theorem sign_eval_const (p : ℝ[X]) {a b : ℝ} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  have ha := hz a ⟨le_rfl, hab⟩
  have hb := hz b ⟨hab, le_rfl⟩
  have hroot (h : p.eval a ≤ 0 ∧ 0 ≤ p.eval b) : False := by
    obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc hab p.continuous.continuousOn h
    exact hz x hx hzero
  have hroot' (h : p.eval b ≤ 0 ∧ 0 ≤ p.eval a) : False := by
    obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc' hab p.continuous.continuousOn h
    exact hz x hx hzero
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · rw [sign_neg ha, sign_neg hb]
  · exact (hroot ⟨ha.le, hb.le⟩).elim
  · exact (hroot' ⟨hb.le, ha.le⟩).elim
  · rw [sign_pos ha, sign_pos hb]

/-- If a polynomial has no zeros except possibly at an interior point, and does
not vanish there either, both endpoint signs agree with its sign at that point. -/
theorem signs_at_nonroot (p : ℝ[X]) {a r b : ℝ} (har : a < r) (hrb : r < b)
    (hr : p.eval r ≠ 0) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval r) ∧
      SignType.sign (p.eval b) = SignType.sign (p.eval r) := by
  have hne (x : ℝ) (hx : x ∈ Set.Icc a b) : p.eval x ≠ 0 := by
    rcases eq_or_ne x r with rfl | hxr
    · exact hr
    · exact hz x hx hxr
  exact ⟨sign_eval_const p har.le (fun x hx => hne x ⟨hx.1, hx.2.trans hrb.le⟩),
    (sign_eval_const p hrb.le (fun x hx => hne x ⟨har.le.trans hx.1, hx.2⟩)).symm⟩

/-- Near an isolated simple root, a polynomial changes from the negative
of its derivative's sign to its derivative's sign. -/
theorem signs_at_root (p : ℝ[X]) {a r b : ℝ} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.derivative.eval r) ∧
    SignType.sign (p.eval b) = SignType.sign (p.derivative.eval r) := by
  obtain ⟨d, hp⟩ := (dvd_iff_isRoot.mpr hr : X - C r ∣ p)
  have hdr : p.derivative.eval r = d.eval r := by
    rw [hp, derivative_mul]
    simp
  have hdz : ∀ x ∈ Set.Icc a b, d.eval x ≠ 0 := by
    intro x hx
    by_cases hxr : x = r
    · simpa [hxr, hdr] using hd
    · intro hdx
      apply hz x hx hxr
      simp [hp, hdx]
  have hda := sign_eval_const _ har.le (fun x hx => hdz x ⟨hx.1, hx.2.trans hrb.le⟩)
  have hdb := sign_eval_const _ hrb.le (fun x hx => hdz x ⟨har.le.trans hx.1, hx.2⟩)
  constructor
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_neg (sub_neg.mpr har), neg_one_mul, hda]
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_pos (sub_pos.mpr hrb), one_mul, ← hdb]

end

end LeanCanny.Algebra.Sturm
