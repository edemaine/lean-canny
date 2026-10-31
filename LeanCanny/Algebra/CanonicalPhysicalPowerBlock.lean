/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPowerSchedule
public import LeanCanny.Algebra.PhysicalPowerCriticalCone
public import LeanCanny.Algebra.PhysicalPowerCriticalDegree

/-! # Canonical integral heights in physical blocks of any later prefix

A block keeps the physical power assigned at its birth. Its canonical
height representatives are embedded in every later scalar prefix, where
the original variable powers are unchanged. Thus the degree and infinity
claims need no new height-degree assumptions at later depths.
-/

@[expose] public section
namespace LeanCanny.Algebra.CanonicalPhysicalPowerBlock
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] {a m N n : ℕ}

noncomputable def heights (b : IntegralCoordinateBasis A a N) (h : a ≤ m)
    (H : Fin (n + 1) → A) : Fin (n + 1) → MvPolynomial (Fin m) ℤ :=
  fun i => rename (embed h) (b.representative (H i))

theorem height_degree (S : ℕ) (ha : a ≤ S) (b : IntegralCoordinateBasis A a N)
    (h : a ≤ m) (H : Fin (n + 1) → A) (i : Fin (n + 1)) :
    (CoordinatePowerSubstitution.substitute (weights S N m) (heights b h H i)).totalDegree < physical S N a :=
  physical_ancestor_degree S h ha b (H i)

noncomputable def rows (S : ℕ) (b : IntegralCoordinateBasis A a N) (h : a ≤ m)
    (H : Fin (n + 1) → A) (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ)
    (scales : Fin (n + 1) → ℤ) (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (D : ℕ) :
    Variables (n + 1) → MvPolynomial (Fin m ⊕ Variables (n + 1)) ℤ :=
  PhysicalPowerCriticalRows.rows (FermatCriticalHomogenization.polynomial low c D) s
    (PhysicalPowerCriticalRows.coordinateNormals b₀ scales r) (heights b h H)
    (weights S N m) D (physical S N a)

theorem row_degree (S : ℕ) (ha : a ≤ S) (b : IntegralCoordinateBasis A a N)
    (h : a ≤ m) (H : Fin (n + 1) → A) (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ)
    (scales : Fin (n + 1) → ℤ) (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (D : ℕ)
    (hD : 2 ≤ D) (hlow : low.totalDegree < D) (j : Variables (n + 1)) :
    (rows S b h H low c b₀ scales s r D j).totalDegree ≤
      PhysicalPowerCriticalRows.degrees s D (physical S N a) j :=
  PhysicalPowerCriticalRows.row_degree low c s _ _ _ D _ hD (physical_pos S N a) hlow
    (fun i _ => height_degree S ha b h H i) j

theorem physical_zero {K : Type*} [Field K] [CharZero K] (φ : ℤ →+* K)
    (S : ℕ) (ha : a ≤ S) (b : IntegralCoordinateBasis A a N) (h : a ≤ m)
    (H : Fin (n + 1) → A) (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ)
    (scales : Fin (n + 1) → ℤ) (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s)
    (D : ℕ) (hD : 2 ≤ D) (hlow : low.totalDegree < D)
    (hc : φ c ≠ 0) (hb : φ b₀ ≠ 0) (hs : ∀ i, φ (scales i) ≠ 0)
    (y : Option (Fin m ⊕ Variables (n + 1)) → K) (hy : y none = 0)
    (hz : ∀ j, (WeightedHomogenization.homogenize (fun _ => 1)
      (PhysicalPowerCriticalRows.degrees s D (physical S N a) j)
      (rows S b h H low c b₀ scales s r D j)).eval₂ φ y = 0) :
    (fun i => y (some (ambient i))) = 0 ∧ (fun j => y (some (multiplier j))) = 0 :=
  PhysicalPowerCriticalRows.physical_zero φ low c b₀ scales s r hr _ _ D _ hD
    (physical_pos S N a) hlow hc hb hs (fun i _ => height_degree S ha b h H i) y hy hz

end LeanCanny.Algebra.CanonicalPhysicalPowerBlock
