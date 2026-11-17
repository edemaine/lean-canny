/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CandidateCoordinateBounds
public import LeanCanny.CountingHierarchy.CoordinateFingerprintSelection
public import LeanCanny.Geometry.CoerciveComponentSampling

/-! # Bounded discrete choices and two existential tests select good parameters -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial LeanCanny.Algebra
open scoped Classical

variable {n : ℕ}

noncomputable def candidateSelection (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (j : Fin n → ℕ) (L : Fin n → FingerprintLabelData) (c : Fin n → ℝ) : Prop :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) c q = 0 ∧
    coordinateFingerprintSelection (fun i => addressedCandidateCoordinate q D hD i (j i))
      ((2 * (D + 1) + 1) ^ n) (coordinateCharacteristicMassExponent n (2 * (D + 1)) (2 * b)) L c

theorem good_parameter_iff_bounded_two_tests {K A Z : Type*}
    (q : K → MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : ∀ k, (q k).totalDegree ≤ D) (hb : ∀ k, MvMass.mass (q k) ≤ 2 ^ b)
    (parameter : (Fin n → ℝ) → A) (bad : A → Z → Prop)
    (hcover : (∃ x : A, ∀ z, ¬bad x z) →
      ∃ k, ∃ c : Geometry.CoerciveComponentSampling.Zeros ((q k).map (Int.castRingHom ℝ)),
        (∀ z, ¬bad (parameter c.val) z) ∧
          ∀ i, (candidateCoordinate (q k) D (hD k) i).eval₂ (Int.castRingHom ℝ) (c.val i) = 0) :
    (∃ x : A, ∀ z, ¬bad x z) ↔
      ∃ k : K, ∃ j : Fin n → ℕ, ∃ L : Fin n → FingerprintLabelData,
        (∀ i, j i ≤ coordinateParameterDegreeBound n (2 * (D + 1))) ∧
        (∀ i, (L i).Bounded ((2 * (D + 1) + 1) ^ n)) ∧
        (∃ c, candidateSelection (q k) D b (hD k) j L c) ∧
        ¬∃ c z, candidateSelection (q k) D b (hD k) j L c ∧ bad (parameter c) z := by
  constructor
  · intro hx
    obtain ⟨k, c, hc, hroots⟩ := hcover hx
    let j := candidateCoordinateIndex (q k) D (hD k)
    let P := fun i => addressedCandidateCoordinate (q k) D (hD k) i (j i)
    have hident (i : Fin n) : P i = candidateCoordinate (q k) D (hD k) i :=
      addressedCandidateCoordinate_at_index (q k) D (hD k) i
    have hP (i : Fin n) : P i ≠ 0 := by
      rw [hident]
      exact candidateCoordinate_ne_zero (q k) D (hD k) i
    obtain ⟨L, hL, hselect⟩ := exists_coordinateFingerprintSelection P ((2 * (D + 1) + 1) ^ n)
      (coordinateCharacteristicMassExponent n (2 * (D + 1)) (2 * b)) hP
      (fun i => addressedCandidateCoordinate_degree_le (q k) D (hD k) i (j i))
      (fun i => addressedCandidateCoordinate_mass_le (q k) D b (hD k) (hb k) i (j i)) c.val
      (fun i => by rw [hident]; exact hroots i)
    refine ⟨k, j, L, candidateCoordinateIndex_le (q k) D (hD k), hL, ?_, ?_⟩
    · refine ⟨c.val, ?_, (hselect c.val).mpr rfl⟩
      have hzero : MvPolynomial.eval c.val ((q k).map (Int.castRingHom ℝ)) = 0 := c.property
      simpa only [MvPolynomial.eval_map] using hzero
    · rintro ⟨c', z, hs, hbad⟩
      have heq := (hselect c').mp hs.2
      exact hc z (heq ▸ hbad)
  · rintro ⟨k, j, L, _, _, hnonempty, hnocounter⟩
    exact exists_good_of_two_tests (candidateSelection (q k) D b (hD k) j L) parameter bad hnonempty hnocounter

end LeanCanny.CountingHierarchy
