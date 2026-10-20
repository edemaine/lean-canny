/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCanonicalMatrixMap
public import LeanCanny.Algebra.MacaulayGenericShift
public import LeanCanny.Algebra.CharacteristicQuotientDegree

/-! # Characteristic invertibility of the generic weighted homotopy operator

The pure-power homotopy `H` gives `H D + D H` on each finite weighted
piece. For the shifted input system its matrix is the characteristic pencil
of the corresponding unshifted operator. It therefore has nonzero
determinant over the rational function field.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem canonicalMatrix_powers_map (φ : R →+* S) (d : Fin n → ℕ) (L W : ℕ) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix (Macaulay.powers (R := S) d) d L W (powers_homogeneous d) hW k =
      (canonicalMatrix (Macaulay.powers (R := R) d) d L W (powers_homogeneous d) hW k).map φ := by
  have he : (fun i => (Macaulay.powers (R := R) d i).map φ) = Macaulay.powers (R := S) d := by
    funext i
    simp only [Macaulay.powers, MvPolynomial.map_monomial, map_one]
  exact (canonicalMatrix_congr he d L W (fun i => (powers_homogeneous (R := R) d i).map φ)
    (powers_homogeneous d) hW k).symm.trans
      (canonicalMatrix_map φ (Macaulay.powers (R := R) d) d L W (powers_homogeneous d) hW k)

theorem canonicalMatrix_subtractiveSystem (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix (Macaulay.subtractiveSystem p d) d L W (Macaulay.subtractiveSystem_homogeneous p d hp) hW k =
      (canonicalMatrix p d L W hp hW k).map Polynomial.C - (Polynomial.X : Polynomial R) •
        (canonicalMatrix (Macaulay.powers (R := R) d) d L W (powers_homogeneous d) hW k).map Polynomial.C := by
  have he : Macaulay.subtractiveSystem p d =
      (fun i => (p i).map Polynomial.C - MvPolynomial.C Polynomial.X * Macaulay.powers (R := Polynomial R) d i) := by
    funext i
    simp only [Macaulay.subtractiveSystem, Macaulay.powers, MvPolynomial.C_mul_monomial, mul_one]
  have hsub : ∀ i, ((p i).map Polynomial.C - MvPolynomial.C Polynomial.X *
      Macaulay.powers (R := Polynomial R) d i).IsHomogeneous (d i) := by
    intro i
    have hi := Macaulay.subtractiveSystem_homogeneous p d hp i
    simpa only [he] using hi
  have h := canonicalMatrix_sub_smul (fun i => (p i).map Polynomial.C) (Macaulay.powers (R := Polynomial R) d)
    Polynomial.X d L W (fun i => (hp i).map Polynomial.C) (powers_homogeneous d) hsub hW k
  rw [canonicalMatrix_map (Polynomial.C : R →+* Polynomial R) p d L W hp hW k,
    canonicalMatrix_powers_map (Polynomial.C : R →+* Polynomial R)] at h
  exact (canonicalMatrix_congr he d L W (Macaulay.subtractiveSystem_homogeneous p d hp) hsub hW k).trans h

noncomputable def contractionMatrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Matrix (CanonicalIndex d (Macaulay.level d) W (k + 1)) (CanonicalIndex d (Macaulay.level d) W (k + 1)) R :=
  homotopyMatrix d W hW (k + 1) * canonicalMatrix p d (Macaulay.level d) W hp hW (k + 1) +
    canonicalMatrix p d (Macaulay.level d) W hp hW k * homotopyMatrix d W hW k

private theorem mapped_pair {I J K : Type*} [Fintype J] [Fintype K]
    (φ : R →+* S) (H : Matrix I J R) (B : Matrix J I R) (A : Matrix I K R) (J' : Matrix K I R) :
    H.map φ * B.map φ + A.map φ * J'.map φ = (H * B + A * J').map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  funext a b
  exact (φ.map_add _ _).symm

theorem contractionMatrix_map (φ : R →+* S) (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    contractionMatrix (fun i => (p i).map φ) d W (fun i => (hp i).map φ) hW k =
      (contractionMatrix p d W hp hW k).map φ := by
  unfold contractionMatrix
  rw [canonicalMatrix_map, canonicalMatrix_map, homotopyMatrix_map φ, homotopyMatrix_map φ]
  exact mapped_pair φ _ _ _ _

private theorem subtractive_pair {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (H : Matrix I J R) (B B₀ : Matrix J I R) (A A₀ : Matrix I K R) (J' : Matrix K I R)
    (h₀ : H * B₀ + A₀ * J' = 1) :
    H.map Polynomial.C * (B.map Polynomial.C - (Polynomial.X : Polynomial R) • B₀.map Polynomial.C) +
      (A.map Polynomial.C - (Polynomial.X : Polynomial R) • A₀.map Polynomial.C) * J'.map Polynomial.C =
      AffineCharacteristic.subtractiveMatrix (H * B + A * J') := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul]
  have hbase := mapped_pair (Polynomial.C : R →+* Polynomial R) H B A J'
  have hcoord := mapped_pair (Polynomial.C : R →+* Polynomial R) H B₀ A₀ J'
  rw [h₀, Matrix.map_one Polynomial.C (map_zero _) (map_one _)] at hcoord
  calc
    _ = (H.map Polynomial.C * B.map Polynomial.C + A.map Polynomial.C * J'.map Polynomial.C) -
        (Polynomial.X : Polynomial R) •
          (H.map Polynomial.C * B₀.map Polynomial.C + A₀.map Polynomial.C * J'.map Polynomial.C) := by
      rw [smul_add]
      abel
    _ = (H * B + A * J').map Polynomial.C - (Polynomial.X : Polynomial R) • (1 : Matrix I I (Polynomial R)) := by
      rw [hbase, hcoord]
    _ = _ := by
      funext a b
      change Polynomial.C ((H * B + A * J') a b) - Polynomial.X * (1 : Matrix I I (Polynomial R)) a b =
        Polynomial.C ((H * B + A * J') a b) - Polynomial.X * Polynomial.C ((1 : Matrix I I R) a b)
      simp only [Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero]

theorem contractionMatrix_subtractiveSystem (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    contractionMatrix (Macaulay.subtractiveSystem p d) d W (Macaulay.subtractiveSystem_homogeneous p d hp) hW k =
      AffineCharacteristic.subtractiveMatrix (contractionMatrix p d W hp hW k) := by
  unfold contractionMatrix
  rw [canonicalMatrix_subtractiveSystem, canonicalMatrix_subtractiveSystem,
    homotopyMatrix_map (Polynomial.C : R →+* Polynomial R), homotopyMatrix_map (Polynomial.C : R →+* Polynomial R)]
  exact subtractive_pair _ _ _ _ _ _ (homotopyMatrix_identity d W hW k)

variable [IsDomain R]

theorem contractionMatrix_genericShift (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    contractionMatrix (Macaulay.genericShift p d) d W (Macaulay.genericShift_homogeneous p d hp) hW k =
      (AffineCharacteristic.subtractiveMatrix (contractionMatrix p d W hp hW k)).map
        (algebraMap (Polynomial R) (RatFunc R)) := by
  have h := contractionMatrix_map (algebraMap (Polynomial R) (RatFunc R)) (Macaulay.subtractiveSystem p d)
    d W (Macaulay.subtractiveSystem_homogeneous p d hp) hW k
  rw [contractionMatrix_subtractiveSystem p d W hp hW k] at h
  exact h

theorem contractionMatrix_genericShift_det_ne_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (contractionMatrix (Macaulay.genericShift p d) d W (Macaulay.genericShift_homogeneous p d hp) hW k).det ≠ 0 := by
  rw [contractionMatrix_genericShift p d W hp hW k]
  have h : (algebraMap (Polynomial R) (RatFunc R))
      (AffineCharacteristic.subtractiveMatrix (contractionMatrix p d W hp hW k)).det =
      ((AffineCharacteristic.subtractiveMatrix (contractionMatrix p d W hp hW k)).map
        (algebraMap (Polynomial R) (RatFunc R))).det :=
    (algebraMap (Polynomial R) (RatFunc R)).map_det _
  rw [← h]
  exact RatFunc.algebraMap_ne_zero (AffineCharacteristic.subtractive_det_ne_zero _)

end LeanCanny.Algebra.KoszulWeighted
