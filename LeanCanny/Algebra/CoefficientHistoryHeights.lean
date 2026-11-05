/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientCanonicalScalarAppend
public import LeanCanny.Algebra.IntegralHistoryCriticalStep

/-! # Actual height preparation and physical critical-row specialization

Representatives are powered and embedded in the actual scalar slots. The
critical rows remain the existing generic physical append construction.
-/

@[expose] public section
namespace LeanCanny.Algebra
open MvPolynomial
open scoped Classical

namespace FlatAffineCriticalStage
variable {ι R T : Type*} [CommRing R] [CommRing T] {n : ℕ}

theorem map_row (φ : R →+* T) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (H : Fin n → MvPolynomial ι R) (j : Variables n) :
    MvPolynomial.map φ (row p s a H j) =
      row (MvPolynomial.map φ p) s (fun k i => φ (a k i)) (fun i => MvPolynomial.map φ (H i)) j := by
  cases j with
  | inl i =>
    simp only [row, gradient, map_sub, MvPolynomial.map_rename, ← pderiv_map,
      map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  | inr j =>
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [row, Fin.cases_zero, MvPolynomial.map_rename]
    · by_cases hi : i ∈ s
      · simp only [row, Fin.cases_succ, ite_eq_left hi, map_sub, MvPolynomial.map_rename,
          AffineHeightPolynomial.polynomial, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
      · simp only [row, Fin.cases_succ, ite_eq_right hi, MvPolynomial.map_X]

end FlatAffineCriticalStage

namespace PhysicalPowerCriticalRows
variable {R T : Type*} [CommRing R] [CommRing T] {n : ℕ}

theorem map_coordinateNormals (φ : R →+* T) (b : R) (c : Fin (n + 1) → R)
    (r : Fin (n + 1)) (j : Fin (n + 2)) (i : Fin (n + 1)) :
    φ (coordinateNormals b c r j i) = coordinateNormals (φ b) (fun k => φ (c k)) r j i := by
  refine Fin.cases ?_ (fun k => ?_) j
  · by_cases h : i = r <;> simp [coordinateNormals, h]
  · by_cases h : i = k <;> simp [coordinateNormals, h]

end PhysicalPowerCriticalRows

namespace PhysicalPowerCriticalAppend
variable {ι R T : Type*} [CommRing R] [CommRing T] {n : ℕ}

theorem map_rows (φ : R →+* T) (q : ι → MvPolynomial ι R)
    (low : MvPolynomial (Fin (n + 1)) R) (a b : R) (c : Fin (n + 1) → R)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) (j : ι ⊕ FlatAffineCriticalStage.Variables (n + 1)) :
    MvPolynomial.map φ (rows q low a b c s r H w D W j) =
      rows (fun i => MvPolynomial.map φ (q i)) (MvPolynomial.map φ low) (φ a) (φ b)
        (fun i => φ (c i)) s r (fun i => MvPolynomial.map φ (H i)) w D W j := by
  cases j with
  | inl i => simp only [rows, TriangularPolynomialSystem.append, Sum.elim_inl, MvPolynomial.map_rename]
  | inr j =>
    simp only [rows, TriangularPolynomialSystem.append, Sum.elim_inr, PhysicalPowerCriticalRows.rows,
      CoordinatePowerSubstitution.map_substitute, FlatAffineCriticalStage.map_row,
      FermatCriticalHomogenization.map_polynomial, PhysicalPowerCriticalRows.map_coordinateNormals]

end PhysicalPowerCriticalAppend

namespace CoefficientHistoryHeights
open UniformIntegralPowerSchedule
set_option backward.isDefEq.respectTransparency false
variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {m N : ℕ}

noncomputable def historyHeights {κ : Type*} (S : ℕ) (f : Fin m → ι)
    (b : CoefficientCoordinateBasis R A m N) (H : κ → A) : κ → MvPolynomial ι R := fun i =>
  rename f (CoordinatePowerSubstitution.substitute (weights S N m) (b.representative (H i)))

theorem historyHeights_map {κ T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    {φ : R →+* T} {ψ : A →+* B} {b : CoefficientCoordinateBasis R A m N}
    {c : CoefficientCoordinateBasis T B m N} (HS : CoefficientCoordinateBasis.Specializes φ ψ b c)
    (S : ℕ) (f : Fin m → ι) (H : κ → A) :
    (fun i => MvPolynomial.map φ (historyHeights S f b H i)) = historyHeights S f c (fun i => ψ (H i)) := by
  funext i
  simp only [historyHeights, MvPolynomial.map_rename, CoordinatePowerSubstitution.map_substitute,
    HS.representative_map]

theorem historyHeights_degree {κ : Type*} (S : ℕ) (hm : m ≤ S) (f : Fin m → ι)
    (b : CoefficientCoordinateBasis R A m N) (H : κ → A) (i : κ) :
    (historyHeights S f b H i).totalDegree < physical S N m := by
  apply (totalDegree_rename_le _ _).trans_lt
  exact ((CoordinatePowerSubstitution.degree_le _ _ _ (weights_le S N m)).trans
    (Nat.mul_le_mul_left _ ((b.representative_degree (H i)).trans (cap_le S N m hm)))).trans_lt
      (physical_dominates S N m)

theorem historyHeights_native {ι : Type} {S n : ℕ} (F : IntegralHistorySampler.Sampler S N m ι)
    (H : Fin (n + 1) → F.scalarPrefix.carrier) :
    historyHeights S F.scalar (CoefficientCoordinateBasis.ofIntegral F.scalarPrefix.basis) H =
      IntegralHistorySampler.historyHeights F H := rfl

theorem critical_rows_map {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    {φ : R →+* T} {ψ : A →+* B} {b : CoefficientCoordinateBasis R A m N}
    {c : CoefficientCoordinateBasis T B m N} (HS : CoefficientCoordinateBasis.Specializes φ ψ b c)
    (S : ℕ) (f : Fin m → ι) (q : ι → MvPolynomial ι R) (q' : ι → MvPolynomial ι T)
    (HQ : ∀ i, MvPolynomial.map φ (q i) = q' i)
    (ambient : ℕ) (low : MvPolynomial (Fin (ambient + 1)) R) (a objective : R)
    (scales : Fin (ambient + 1) → R) (s : Finset (Fin (ambient + 1))) (r : Fin (ambient + 1))
    (H : Fin (ambient + 1) → A) (D : ℕ) :
    (fun j => MvPolynomial.map φ (PhysicalPowerCriticalAppend.rows q low a objective scales s r
      (historyHeights S f b H) (fun _ => 1) D (physical S N m) j)) =
    PhysicalPowerCriticalAppend.rows q' (MvPolynomial.map φ low) (φ a) (φ objective)
      (fun i => φ (scales i)) s r (historyHeights S f c (fun i => ψ (H i)))
      (fun _ => 1) D (physical S N m) := by
  funext j
  rw [PhysicalPowerCriticalAppend.map_rows]
  have Hq : (fun i => MvPolynomial.map φ (q i)) = q' := funext HQ
  rw [Hq, historyHeights_map HS]

theorem critical_rows_native {ι : Type} {S n : ℕ} [Fintype ι]
    (F : IntegralHistorySampler.Sampler S N m ι) (data : IntegralHistorySampler.CriticalData F.scalarPrefix n) :
    PhysicalPowerCriticalAppend.rows F.rows data.low data.leading data.objective data.scales
      data.frozen data.free
      (historyHeights S F.scalar (CoefficientCoordinateBasis.ofIntegral F.scalarPrefix.basis) data.heights)
      (fun _ => 1) data.degree (physical S N m) = (IntegralHistorySampler.criticalStep F data).rows := rfl

end CoefficientHistoryHeights
end LeanCanny.Algebra
