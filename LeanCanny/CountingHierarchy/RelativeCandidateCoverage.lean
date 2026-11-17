/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeDegreePieceGeometry
public import LeanCanny.CountingHierarchy.DegreePieceProjection
public import LeanCanny.CountingHierarchy.CandidateCoordinateCoverage

/-! # Source-derived degree-piece candidates cover every good fiber -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial Set
open scoped Topology Classical

attribute [local irreducible] finiteRelativeSection finiteRelativeCharacteristic
  relativeCharacteristic relativeBivariate specializedRelativeSection firstVariableCoefficient
  degreePiecePolynomial candidateCoordinate parametricCoordinatePolynomial

variable {n m : ℕ}

theorem relative_candidate_covers_good_fiber (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (hFn : ∀ x z, 0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P)
    (N : ℕ) (hN : (finiteRelativeSection d P hP).totalDegree ≤ N)
    (D : ℕ) (hD : ∀ k : Fin (N + 1),
      (degreePiecePolynomial (finiteRelativeSection d P hP) N k.val).totalDegree ≤ D)
    (hgood : ∃ x : Fin m → ℝ, ¬∃ z : Fin n → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P = 0) :
    ∃ k : Fin (N + 1), ∃ c : Geometry.CoerciveComponentSampling.Zeros
      ((degreePiecePolynomial (finiteRelativeSection d P hP) N k.val).map (Int.castRingHom ℝ)),
      (¬∃ z : Fin n → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (Fin.addCases z (fun i => c.val i.succ)) P = 0) ∧
      ∀ i, (candidateCoordinate (degreePiecePolynomial (finiteRelativeSection d P hP) N k.val)
        D (hD k) i).eval₂ (Int.castRingHom ℝ) (c.val i) = 0 := by
  obtain ⟨x, hx⟩ := hgood
  let E := finiteRelativeSection d P hP
  let Q := specializedRelativeSection d P hP x
  have hQ : Q ≠ 0 := specializedRelativeSection_ne_zero d P hP x
  have hQN : Q.natDegree ≤ N := (specializedRelativeSection_degree_le d P hP x).trans hN
  let k : Fin (N + 1) := ⟨Q.natDegree, by omega⟩
  have hxpiece : x ∈ degreePiece (firstCoefficientValues E N) k := by
    constructor
    · change MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient E k.val) ≠ 0
      rw [← specializedRelativeSection_coeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    · intro j hj
      change MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient E j.val) = 0
      rw [← specializedRelativeSection_coeff]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hj
  let W := degreePiecePolynomial E N k.val
  let Z := Geometry.CoerciveComponentSampling.Zeros (W.map (Int.castRingHom ℝ))
  let C : Set Z := {c | ¬∃ z : Fin n → ℝ,
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (fun i => c.val i.succ)) P = 0}
  have hC : IsClopen C := by
    exact (relative_good_isClopen_on_degreePiece d hd he P hP hFn N hN k).preimage
      (degreePiecePolynomialProjection_continuous E N k)
  let c₀ : Z := degreePiecePolynomialSection E N k ⟨x, hxpiece⟩
  have hc₀ : c₀ ∈ C := by
    simpa only [C, c₀, degreePiecePolynomialSection, Fin.cons_succ, Set.mem_ofPred_eq] using hx
  obtain ⟨c, hc, hroots⟩ := candidateCoordinates_meet_clopen W D (hD k) C hC c₀ hc₀
  exact ⟨k, c, hc, hroots⟩

end LeanCanny.CountingHierarchy
