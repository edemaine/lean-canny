/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicSquarefreeExceptionalMass
public import LeanCanny.Geometry.ParameterizedOrderedRootBranches

/-! # Derived mass bounds for the actual root-query continuation cuts

Only degree and parameter-coefficient mass bounds of the actual head and
queries are inputs. Product coefficients and every selected exceptional PSC
are bounded internally; no bound on an already constructed cut family is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedRootQuerySign
open Polynomial LeanCanny.Algebra SymbolicScaledSquarefree
open scoped Classical

def cutMassBound (D H : ℕ) : ℕ := exceptionalMassBound (2 * D) (2 * (H + (D + 1).size))

theorem product_coefficient_mass (p q : Polynomial Coefficient) (D H : ℕ)
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D)
    (hP : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H)
    (hQ : ∀ k, coefficientMass (q.coeff k) ≤ 2 ^ H) (k : ℕ) :
    coefficientMass ((p * q).coeff k) ≤ 2 ^ (2 * (H + (D + 1).size)) := by
  calc
    _ ≤ NestedMass.mass (p * q) := NestedMass.coeff_le _ _
    _ ≤ NestedMass.mass p * NestedMass.mass q := NestedMass.mul_le _ _
    _ ≤ 2 ^ (H + (D + 1).size) * 2 ^ (H + (D + 1).size) :=
      Nat.mul_le_mul (NestedMass.le_pow p D H hp hP) (NestedMass.le_pow q D H hq hQ)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem cuts_mass_le {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient)
    (D H : ℕ) (hp : p.natDegree ≤ D) (hq : ∀ j, (Q j).natDegree ≤ D)
    (hP : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H)
    (hQ : ∀ j k, coefficientMass ((Q j).coeff k) ≤ 2 ^ H) (i : Option (J × Bool)) :
    coefficientMass (cuts p Q i) ≤ 2 ^ cutMassBound D H := by
  have hh : H ≤ 2 * (H + (D + 1).size) := by omega
  have hP' (k : ℕ) : coefficientMass (p.coeff k) ≤ 2 ^ (2 * (H + (D + 1).size)) :=
    (hP k).trans (Nat.pow_le_pow_right (by decide) hh)
  have hQ' (j : J) (k : ℕ) : coefficientMass ((Q j).coeff k) ≤ 2 ^ (2 * (H + (D + 1).size)) :=
    (hQ j k).trans (Nat.pow_le_pow_right (by decide) hh)
  cases i with
  | none => exact exceptional_mass_le p (2 * D) _ (by omega) hP'
  | some i =>
    rcases i with ⟨j, side⟩
    cases side <;> simp only [cuts]
    · split_ifs
      · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
          Nat.one_le_two_pow (n := cutMassBound D H)
      · exact exceptional_mass_le (Q j) (2 * D) _ (by have := hq j; omega) (hQ' j)
    · split_ifs
      · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
          Nat.one_le_two_pow (n := cutMassBound D H)
      · exact exceptional_mass_le (p * Q j) (2 * D) _
          (Polynomial.natDegree_mul_le.trans (by have := hq j; omega))
          (product_coefficient_mass p (Q j) D H hp (hq j) hP (hQ j))

theorem cutMassBound_linear (D H : ℕ) : cutMassBound D H = (8 * D + 2) * H + cutMassBound D 0 := by
  unfold cutMassBound exceptionalMassBound gcdMassExponent
  ring

theorem cutMassBound_binary {D H : List Bool → ℕ} (hD : BinaryFn D) (hH : BinaryFn H) :
    BinaryFn (fun q => cutMassBound (D q) (H q)) :=
  exceptionalMassBound_binary ((BinaryFn.const 2).mul hD)
    ((BinaryFn.const 2).mul (hH.add (hD.add (BinaryFn.const 1)).size))

theorem actual_cutMass_le {J : Type*} [Fintype J]
    (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient) (D H : ℕ)
    (hp : p.natDegree ≤ D) (hq : ∀ j, (Q j).natDegree ≤ D)
    (hP : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H)
    (hQ : ∀ j k, coefficientMass ((Q j).coeff k) ≤ 2 ^ H) :
    ParameterizedOrderedRootBranches.cutMass p Q ≤ 2 ^ cutMassBound D H := by
  apply Finset.sup_le
  intro i _
  exact cuts_mass_le p Q D H hp hq hP hQ i

theorem avoids_after_input_bounds {J : Type*} (p : Polynomial Coefficient) (hpn : p ≠ 0)
    (Q : J → Polynomial Coefficient) (D H : ℕ)
    (hp : p.natDegree ≤ D) (hq : ∀ j, (Q j).natDegree ≤ D)
    (hP : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H)
    (hQ : ∀ j k, coefficientMass ((Q j).coeff k) ≤ 2 ^ H)
    (a b : ℝ) (ha : (2 : ℝ) ^ (cutMassBound D H + 1) ≤ a) : Avoids p Q a b :=
  avoids_after_binary_mass p hpn Q (cutMassBound D H) (cuts_mass_le p Q D H hp hq hP hQ) a b ha

end LeanCanny.Geometry.ParameterizedRootQuerySign
