/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialLocalSign

/-! # Extending a one-sided sign throughout a root-free interval -/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialLocalSign
open Polynomial Set
open scoped Classical

theorem sign_eq_right_on_interval (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hz : ∀ y ∈ Ioo a b, p.eval y ≠ 0) (y : ℝ) (hy : y ∈ Ioo a b) :
    SignType.sign (p.eval y) = right p a := by
  obtain ⟨δ, hδ, H⟩ := right_eventually p a
  let ε := min δ (b - a)
  have hε : 0 < ε := lt_min hδ (sub_pos.mpr hab)
  have ht : 0 < ε / 2 := by linarith
  have htd : ε / 2 < δ := by have hm := min_le_left δ (b - a); dsimp [ε] at *; linarith
  have htb : a + ε / 2 < b := by have hm := min_le_right δ (b - a); dsimp [ε] at *; linarith
  have he := isPreconnected_Ioo.sign_eq_of_continuousOn p.continuousOn hz hy
    (show a + ε / 2 ∈ Ioo a b from ⟨by linarith, htb⟩)
  exact he.trans (H (ε / 2) ht htd)

end LeanCanny.Algebra.PolynomialLocalSign
