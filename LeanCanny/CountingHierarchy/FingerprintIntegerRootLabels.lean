/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintLabelPolynomial
public import LeanCanny.CountingHierarchy.FingerprintRootSelection
public import LeanCanny.CountingHierarchy.DerivativeTestBounds

/-! # Integer polynomial labels for any prescribed real root -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical BigOperators

noncomputable def fingerprintTests (p b₀ : Polynomial ℤ) (D : ℕ) : Fin (D + 1) → Polynomial ℤ :=
  Fin.cases b₀ (fun j => Polynomial.derivative^[j.val + 1] p)

noncomputable def fingerprintIntegerRootLabel (p b₀ : Polynomial ℤ) (D b mu gamma : ℕ)
    (target : ℤ) : Polynomial ℤ :=
  fingerprintLabelPolynomial (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (1 + D * mu)) (fingerprintTests p b₀ D)
    (fun i => fingerprintWeight mu gamma i.val) target

theorem fingerprintTests_sign (p b₀ : Polynomial ℤ) (D : ℕ) (x : ℝ) (i : Fin D) :
    SignType.sign ((fingerprintTests p b₀ D i.succ).eval₂ (Int.castRingHom ℝ) x) =
      ThomEncoding.sign (p.map (Int.castRingHom ℝ)) x (i.val + 1) := by
  simp only [fingerprintTests, Fin.cases_succ, ThomEncoding.sign,
    Polynomial.iterate_derivative_map, Polynomial.eval_map]

/-- Every label tests its exact weighted derivative-sign sum and distinguished
positivity condition, with a fixed positive or negative margin on all roots. -/
theorem fingerprintIntegerRootLabel_margin (p b₀ : Polynomial ℤ) (hp : p ≠ 0)
    (D b mu gamma : ℕ) (target : ℤ) (hmu : 0 < mu)
    (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (x : ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    ((1 : ℝ) / 2 ≤ (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) x ∨
      (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) x ≤ -(1 : ℝ) / 2) ∧
    (0 < (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) x ↔
      derivativeFingerprint (p.map (Int.castRingHom ℝ)) D mu gamma x = target ∧
      0 < b₀.eval₂ (Int.castRingHom ℝ) x) := by
  have hw : ∑ i : Fin D, fingerprintWeight mu gamma i.val ≤ 1 + D * mu := by
    calc
      _ ≤ ∑ _i : Fin D, mu := Finset.sum_le_sum (fun i _ => (Nat.mod_lt _ hmu).le)
      _ ≤ 1 + D * mu := by simp
  have hv (i : Fin (D + 1)) : (fingerprintTests p b₀ D i).eval₂ (Int.castRingHom ℝ) x = 0 ∨
      (((2 : ℝ) ^ algebraicTestPrecision D D b (derivativeTestMassExponent D b))⁻¹ ≤
          |(fingerprintTests p b₀ D i).eval₂ (Int.castRingHom ℝ) x| ∧
        |(fingerprintTests p b₀ D i).eval₂ (Int.castRingHom ℝ) x| ≤
          (2 : ℝ) ^ algebraicTestPrecision D D b (derivativeTestMassExponent D b)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · apply algebraic_test_value_range p b₀ hp D D b (derivativeTestMassExponent D b) hD hb₀ hpm _ x hx
      exact hb₀m.trans (Nat.pow_le_pow_right (by decide) (by unfold derivativeTestMassExponent; omega))
    · exact iterated_derivative_value_range p hp D b hD hpm x hx (j.val + 1)
  have h := fingerprintLabelPolynomial_margin _ (1 + D * mu) (fingerprintTests p b₀ D)
    (fun i => fingerprintWeight mu gamma i.val) target x (by omega) hw hv
  have hz : fingerprintTests p b₀ D 0 = b₀ := rfl
  simpa only [fingerprintIntegerRootLabel, derivativeFingerprint, fingerprintTests_sign, hz] using h

/-- A bounded triple of integers selects any prescribed qualifying root.
All other real roots receive a negative value with margin one half. -/
theorem exists_fingerprintIntegerRootLabel (p b₀ : Polynomial ℤ) (hp : p ≠ 0)
    (D b : ℕ) (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (x : ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) (hx₀ : 0 < b₀.eval₂ (Int.castRingHom ℝ) x) :
    ∃ mu gamma : ℕ, ∃ target : ℤ,
      mu.Prime ∧ 2 < mu ∧ mu ≤ 2 * (D ^ 3 + 2) ∧ gamma < mu ∧ target.natAbs ≤ D * mu ∧
      (1 : ℝ) / 2 ≤ (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) x ∧
      ∀ y : ℝ, p.eval₂ (Int.castRingHom ℝ) y = 0 → y ≠ x →
        (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) y ≤ -(1 : ℝ) / 2 := by
  let q := p.map (Int.castRingHom ℝ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  let S := q.roots.toFinset
  have hmem (y : ℝ) : y ∈ S ↔ p.eval₂ (Int.castRingHom ℝ) y = 0 := by
    simp only [S, Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot,
      q, Polynomial.eval_map]
  obtain ⟨mu, gamma, hmu, hmu₂, hmub, hgamma, hsep⟩ := exists_derivative_fingerprint q hq D
    (Polynomial.natDegree_map_le.trans hD) S
    (fun y hy => by simpa only [q, Polynomial.eval_map] using (hmem y).mp hy)
  let target := derivativeFingerprint q D mu gamma x
  have hmargin (y : ℝ) (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :=
    fingerprintIntegerRootLabel_margin p b₀ hp D b mu gamma target (by omega) hD hb₀ hpm hb₀m y hy
  have hpos : 0 < (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) x :=
    (hmargin x hx).2.mpr ⟨rfl, hx₀⟩
  refine ⟨mu, gamma, target, hmu, hmu₂, hmub, hgamma,
    derivativeFingerprint_natAbs_le q D mu gamma x (by omega), ?_, ?_⟩
  · rcases (hmargin x hx).1 with h | h
    · exact h
    · linarith
  · intro y hy hne
    have hn : ¬0 < (fingerprintIntegerRootLabel p b₀ D b mu gamma target).eval₂ (Int.castRingHom ℝ) y := by
      intro hh
      have he := ((hmargin y hy).2.mp hh).1
      have heq := hsep (a₁ := ⟨y, (hmem y).mpr hy⟩) (a₂ := ⟨x, (hmem x).mpr hx⟩) he
      exact hne (congrArg Subtype.val heq)
    rcases (hmargin y hy).1 with h | h
    · linarith
    · exact h

end LeanCanny.CountingHierarchy
