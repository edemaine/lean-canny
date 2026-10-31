/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalIntegralPhysicalSampler
public import LeanCanny.Algebra.IntegralCoordinateEvaluation

/-! # Exact interpretation of retained scalar and physical sampler roots

The scalar coordinates determine a unique evaluation of the prefix algebra.
Canonical height representatives evaluate to the actual height elements.
The physical coordinates and multipliers satisfy the original critical
equations after undoing their powers; derivatives precede substitution.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open UniformIntegralPowerSchedule
open scoped Classical
variable {S N m : ℕ}

theorem interpret_unique {K : Type} [CommRing K] (P : Prefix S N m) (z : Fin m → K)
    (hz : ∀ i, (P.rows i).eval₂ (Int.castRingHom K) z = 0) :
    ∃! φ : P.carrier →ₐ[ℤ] K, ∀ i, φ (P.basis.generator i) = z i ^ weights S N m i := by
  obtain ⟨φ, hφ⟩ := P.interpret K z hz
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact P.basis.algHom_ext ψ φ (fun i => (hψ i).trans (hφ i).symm)

end LeanCanny.Algebra.UniformIntegralPrefix

namespace LeanCanny.Algebra.CanonicalPhysicalPowerBlock
open UniformIntegralPowerSchedule MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A K : Type*} [CommRing A] [CommRing K] {a m N n : ℕ}

theorem height_eval (b : IntegralCoordinateBasis A a N) (h : a ≤ m) (H : Fin (n + 1) → A)
    (φ : A →ₐ[ℤ] K) (u : Fin m → K) (hu : ∀ j, u (embed h j) = φ (b.generator j)) (i : Fin (n + 1)) :
    (heights b h H i).eval₂ (Int.castRingHom K) u = φ (H i) := by
  rw [heights, eval₂_rename]
  have HE : u ∘ embed h = fun j => φ (b.generator j) := funext hu
  rw [HE]
  exact b.representative_eval_algHom (H i) φ

end LeanCanny.Algebra.CanonicalPhysicalPowerBlock

namespace LeanCanny.Algebra.CanonicalIntegralPhysicalSampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {S N m n : ℕ} {K : Type} [CommRing K]

theorem roots_interpret (P : UniformIntegralPrefix.Prefix S N m) (H : Fin (n + 1) → P.carrier)
    (low : MvPolynomial (Fin (n + 1)) ℤ) (c b₀ : ℤ) (scales : Fin (n + 1) → ℤ)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (D : ℕ)
    (z : Fin (m + ((n + 1) + (n + 2))) → K)
    (hz : ∀ j, (rows P P.basis le_rfl H low c b₀ scales s r D j).eval₂ (Int.castRingHom K) z = 0) :
    let v := z ∘ layout m n
    let x := fun i => v (ambient i) ^ physical S N m
    let mu := fun j => v (multiplier j) ^ ((D - 1) * physical S N m)
    ∃ φ : P.carrier →ₐ[ℤ] K,
      (∀ i, φ (P.basis.generator i) = v (Sum.inl i) ^ weights S N m i) ∧
      (FermatCriticalHomogenization.polynomial low c D).eval₂ (Int.castRingHom K) x = 0 ∧
      (∀ i ∈ s, (∑ j, (Int.castRingHom K) (PhysicalPowerCriticalRows.coordinateNormals b₀ scales r i.succ j) * x j) = φ (H i)) ∧
      (∀ i, (pderiv i (FermatCriticalHomogenization.polynomial low c D)).eval₂ (Int.castRingHom K) x =
        ∑ j, (Int.castRingHom K) (PhysicalPowerCriticalRows.coordinateNormals b₀ scales r j i) * mu j) ∧
      ∀ i, i ∉ s → mu i.succ = 0 := by
  dsimp only
  have HR := (PolynomialSystemReindex.roots_iff (Int.castRingHom K) (layout m n) _ z).mp hz
  have HT := (TriangularPolynomialSystem.roots_append (Int.castRingHom K) P.rows _ (z ∘ layout m n)).mp HR
  obtain ⟨φ, hφ⟩ := P.interpret K (fun i => (z ∘ layout m n) (Sum.inl i)) HT.1
  have HP := (PhysicalPowerCriticalRows.roots_iff_original (Int.castRingHom K) _ s _ _ _ D (physical S N m)
    (z ∘ layout m n)).mp HT.2
  have HE := (FlatAffineCriticalStage.roots_iff (Int.castRingHom K) _ s _ _ _).mp HP
  refine ⟨φ, hφ, HE.1, ?_, HE.2.2⟩
  intro i hi
  exact (HE.2.1 i hi).trans (CanonicalPhysicalPowerBlock.height_eval P.basis le_rfl H φ
    (fun j => (z ∘ layout m n) (Sum.inl j) ^ weights S N m j)
    (fun j => by simpa only [embed, Nat.sub_self, Nat.zero_add] using (hφ j).symm) i)

end LeanCanny.Algebra.CanonicalIntegralPhysicalSampler
