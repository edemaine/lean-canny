/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Original changing LOW syntax with a literal unit leading coefficient

This descriptor contains only original spatial polynomials and their fixed
source degree proof. It contains no interpreted history, retained bank, matrix,
height, or evaluator. Different scalar births may carry different LOW bodies.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalUnitSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory

structure Originals (P : Parameters) where
  degree_two : ∀ root, 2 ≤ P.degree root
  low : (root : List Bool) → ℕ → MvPolynomial (Fin (P.ambient root+1)) ℤ
  low_degree : ∀ root b, (low root b).totalDegree < P.degree root

noncomputable def source (P : Parameters) (O : Originals P) (root : List Bool) (b : ℕ) : SpatialSource (P.ambient root) where
  low := O.low root b
  leading := 1
  degree := P.degree root
  degree_two := O.degree_two root
  low_degree := O.low_degree root b
  leading_ne_zero := one_ne_zero

theorem source_leading (P : Parameters) (O : Originals P) (root : List Bool) (b : ℕ) : (source P O root b).leading = 1 := rfl
theorem source_degree (P : Parameters) (O : Originals P) (root : List Bool) (b : ℕ) : (source P O root b).degree = P.degree root := rfl

def ofSources (P : Parameters) (S : (root : List Bool) → ℕ → SpatialSource (P.ambient root))
    (hd : ∀ root b, (S root b).degree=P.degree root) : Originals P where
  degree_two root := (S root 0).degree_two.trans_eq (hd root 0)
  low root b := (S root b).low
  low_degree root b := (S root b).low_degree.trans_eq (hd root b)

theorem source_ofSources (P : Parameters) (S : (root : List Bool) → ℕ → SpatialSource (P.ambient root))
    (hd : ∀ root b, (S root b).degree=P.degree root) (hl : ∀ root b, (S root b).leading=1)
    (root : List Bool) (b : ℕ) : source P (ofSources P S hd) root b = S root b := by
  cases hs : S root b with
  | mk low leading degree htwo hlow hnonzero =>
    have HD := hd root b
    have HL := hl root b
    simp only [hs] at HD HL
    cases HD
    cases HL
    unfold source ofSources
    simp only [hs]

noncomputable def seed (P : Parameters) (O : Originals P)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
    (hroom : ∀ root, 2 ≤ P.cap root+1) : IntegralMixedFramedHistoryFamilyBits.Plan P where
  initialSource root := source P O root 0
  initial_degree _ := rfl
  scalar_cap := hcap
  rules _ := []
  room := hroom
end LeanCanny.Algebra.IntegralMixedCanonicalUnitSourceBits
