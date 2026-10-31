/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefix
public import LeanCanny.Algebra.CanonicalPhysicalPowerBlock
public import LeanCanny.Algebra.PhysicalPowerCriticalAppend
public import LeanCanny.Algebra.PolynomialSystemReindex

/-! # Finite critical samplers over actual integral scalar prefixes

The complete square system retains the scalar prefix and uses the actual
canonical heights for a coordinate-critical block. Its finite layout has
one row per variable. Degree bounds and exclusion at infinity construct
nonzero integer coordinate annihilators, retaining singular affine roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.CanonicalIntegralPhysicalSampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {S N m a n : ℕ}

def layout (m n : ℕ) : (Fin m ⊕ Variables (n + 1)) ≃ Fin (m + ((n + 1) + (n + 2))) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

noncomputable def rows (P : UniformIntegralPrefix.Prefix S N m)
    (b : IntegralCoordinateBasis A a N) (h : a ≤ m) (H : Fin (n + 1) → A)
    (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ) (scales : Fin (n + 1) → ℤ)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (D : ℕ) :
    Fin (m + ((n + 1) + (n + 2))) → MvPolynomial (Fin (m + ((n + 1) + (n + 2)))) ℤ :=
  PolynomialSystemReindex.system (layout m n) (PhysicalPowerCriticalAppend.rows P.rows
    low c b₀ scales s r (CanonicalPhysicalPowerBlock.heights b h H) (weights S N m) D (physical S N a))

def degrees (P : UniformIntegralPrefix.Prefix S N m) (s : Finset (Fin (n + 1))) (D : ℕ) :
    Fin (m + ((n + 1) + (n + 2))) → ℕ :=
  PhysicalPowerCriticalAppend.degrees P.degrees s D (physical S N a) ∘ (layout m n).symm

theorem row_degree (P : UniformIntegralPrefix.Prefix S N m) (ha : a ≤ S)
    (b : IntegralCoordinateBasis A a N) (h : a ≤ m) (H : Fin (n + 1) → A)
    (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ) (scales : Fin (n + 1) → ℤ)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (D : ℕ) (hD : 2 ≤ D) (hlow : low.totalDegree < D)
    (j : Fin (m + ((n + 1) + (n + 2)))) :
    (rows P b h H low c b₀ scales s r D j).totalDegree ≤ degrees (a := a) P s D j :=
  (totalDegree_rename_le _ _).trans (PhysicalPowerCriticalAppend.row_degree P.rows P.degrees P.row_degree
    low c b₀ scales s r _ _ D _ hD (physical_pos S N a) hlow
    (fun i _ => CanonicalPhysicalPowerBlock.height_degree S ha b h H i) _)

theorem degree_pos (P : UniformIntegralPrefix.Prefix S N m) (s : Finset (Fin (n + 1)))
    (D : ℕ) (hD : 2 ≤ D) (j : Fin (m + ((n + 1) + (n + 2)))) :
    0 < degrees (a := a) P s D j := by
  change 0 < PhysicalPowerCriticalAppend.degrees P.degrees s D (physical S N a) ((layout m n).symm j)
  cases (layout m n).symm j with
  | inl i => exact P.degree_pos i
  | inr i => exact PhysicalPowerCriticalRows.degrees_pos s D _ hD (physical_pos S N a) i

theorem noInfinity (P : UniformIntegralPrefix.Prefix S N m) (ha : a ≤ S)
    (b : IntegralCoordinateBasis A a N) (h : a ≤ m) (H : Fin (n + 1) → A)
    (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ) (scales : Fin (n + 1) → ℤ)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s) (D : ℕ)
    (hD : 2 ≤ D) (hlow : low.totalDegree < D) (hc : c ≠ 0) (hb : b₀ ≠ 0) (hs : ∀ i, scales i ≠ 0) :
    AffineFiniteCoordinates.NoInfinity (rows P b h H low c b₀ scales s r D) (degrees (a := a) P s D) := by
  intro y hy hz
  have HE : y ∘ Option.map (layout m n) = 0 := by
    apply PhysicalPowerCriticalAppend.noInfinity (Int.castRingHom ℂ) P.rows P.degrees P.noInfinity
      low c b₀ scales s r hr _ _ D _ hD (physical_pos S N a) hlow
      (by change (c : ℂ) ≠ 0; exact_mod_cast hc)
      (by change (b₀ : ℂ) ≠ 0; exact_mod_cast hb)
      (fun i => by change (scales i : ℂ) ≠ 0; exact_mod_cast hs i)
      (fun i _ => CanonicalPhysicalPowerBlock.height_degree S ha b h H i) _ hy
    intro j
    have HI := hz (layout m n j)
    simp only [rows, degrees, Function.comp_apply, PolynomialSystemReindex.system,
      Equiv.symm_apply_apply, homogenize_rename, eval₂_rename] at HI
    exact HI
  funext i
  cases i with
  | none => exact hy
  | some i => simpa only [Function.comp_apply, Option.map_some, Equiv.apply_symm_apply, Pi.zero_apply]
      using congrFun HE (some ((layout m n).symm i))

theorem finite_roots {K : Type*} [Field K] [CharZero K]
    (P : UniformIntegralPrefix.Prefix S N m) (ha : a ≤ S)
    (b : IntegralCoordinateBasis A a N) (h : a ≤ m) (H : Fin (n + 1) → A)
    (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ) (scales : Fin (n + 1) → ℤ)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s) (D : ℕ)
    (hD : 2 ≤ D) (hlow : low.totalDegree < D) (hc : c ≠ 0) (hb : b₀ ≠ 0) (hs : ∀ i, scales i ≠ 0) :
    {z : Fin (m + ((n + 1) + (n + 2))) → K |
      ∀ j, (rows P b h H low c b₀ scales s r D j).eval₂ (Int.castRingHom K) z = 0}.Finite :=
  AffineFiniteCoordinates.finite_roots _ _ (row_degree P ha b h H low c b₀ scales s r D hD hlow)
    (degree_pos P s D hD) (noInfinity P ha b h H low c b₀ scales s r hr D hD hlow hc hb hs)

end LeanCanny.Algebra.CanonicalIntegralPhysicalSampler
