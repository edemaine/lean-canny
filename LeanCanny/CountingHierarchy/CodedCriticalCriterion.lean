/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceNormDeterminantCorrectness

/-! # Feasibility witnesses with bounded binary label entries and shifts -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra

@[expose] def RootLabelCodeBound (D N : ℕ) (data : List (ℕ × ℕ)) : Prop :=
  data.length ≤ N ∧ ∀ t ∈ data, t.1 < D ∧ t.2 < 3

theorem encodeRootLabel_bound {D N : ℕ} (L : List (Fin D × SignType)) (hL : L.length ≤ N) :
    RootLabelCodeBound D N (encodeRootLabel L) := by
  refine ⟨?_, ?_⟩
  · simpa only [encodeRootLabel, List.length_map] using hL
  · intro t ht
    obtain ⟨s, _hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨s.1.isLt, rootSignEncoding_lt_three s.2⟩

/-- Completeness uses only short canonical codes, while soundness holds for
every raw code because the total evaluator truncates and normalizes it. -/
theorem real_zero_iff_negative_codedCriticalDeterminant {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (heven : Even (d + 2)) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ eval x (F.map (Int.castRingHom ℝ))) :
    (∃ x : Fin n → ℝ, eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ data : List (ℕ × ℕ), RootLabelCodeBound ((d + 1) ^ n) (criticalRootLabelLength n d) data ∧
        ∃ e : ℕ, e ≤ (d + 1) ^ n ∧ codedFiniteCriticalDeterminant d b F hF data e < 0 := by
  rw [real_zero_iff_negative_finiteCriticalDeterminant d hd heven b F hF hM hFn]
  constructor
  · rintro ⟨L, hL, e, he, hneg⟩
    refine ⟨encodeRootLabel L, encodeRootLabel_bound L hL, e, he, ?_⟩
    simpa only [codedFiniteCriticalDeterminant, sourceCodedLabel,
      codedRootLabel_encode (by positivity) L hL, sourceNormShift,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le he)] using hneg
  · rintro ⟨data, _hdata, e, _he, hneg⟩
    exact ⟨sourceCodedLabel n d data, codedRootLabel_length_le _ _ _ data,
      sourceNormShift n d e, sourceNormShift_le n d e, hneg⟩

/-- No malformed or oversized raw code can create a false feasibility witness. -/
theorem real_zero_of_negative_codedCriticalDeterminant {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (heven : Even (d + 2)) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ eval x (F.map (Int.castRingHom ℝ)))
    (data : List (ℕ × ℕ)) (e : ℕ) (hneg : codedFiniteCriticalDeterminant d b F hF data e < 0) :
    ∃ x : Fin n → ℝ, eval x (F.map (Int.castRingHom ℝ)) = 0 := by
  apply (real_zero_iff_negative_finiteCriticalDeterminant d hd heven b F hF hM hFn).mpr
  exact ⟨sourceCodedLabel n d data, codedRootLabel_length_le _ _ _ data,
    sourceNormShift n d e, sourceNormShift_le n d e, hneg⟩

end LeanCanny.CountingHierarchy
