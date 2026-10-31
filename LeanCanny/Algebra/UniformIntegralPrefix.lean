/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixRows
public import LeanCanny.Algebra.AffineFiniteCoordinates

/-! # Iterated finite scalar prefixes with a fixed global power schedule

Starting from the empty integer prefix, each extension constructs its
equations, bounded monomial basis, and degree bounds. Every complex infinity
root is zero, and every affine root interprets the actual integral algebra.
The chosen polynomials and advertised degrees may vary between branches.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Prefix (S N m : ℕ) where
  carrier : Type
  ring : CommRing carrier
  nontrivial : Nontrivial carrier
  basis : @IntegralCoordinateBasis carrier ring m N
  rows : Fin m → MvPolynomial (Fin m) ℤ
  degrees : Fin m → ℕ
  row_degree : ∀ i, (rows i).totalDegree ≤ degrees i
  degree_pos : ∀ i, 0 < degrees i
  degree_bound : ∀ i, degrees i ≤ N * birth S N (m - 1)
  noInfinity : AffineFiniteCoordinates.NoInfinity rows degrees
  interpret : letI := ring
    ∀ (K : Type) [CommRing K] (z : Fin m → K),
    (∀ i, (rows i).eval₂ (Int.castRingHom K) z = 0) →
    ∃ φ : carrier →ₐ[ℤ] K,
      ∀ i, φ (basis.generator i) = z i ^ weights S N m i

attribute [instance] Prefix.ring Prefix.nontrivial

noncomputable def base (S N : ℕ) : Prefix S N 0 where
  carrier := ℤ
  ring := inferInstance
  nontrivial := inferInstance
  basis := IntegralCoordinateBasis.base N
  rows := Fin.elim0
  degrees := Fin.elim0
  row_degree := by intro i; exact Fin.elim0 i
  degree_pos := by intro i; exact Fin.elim0 i
  degree_bound := by intro i; exact Fin.elim0 i
  noInfinity := by
    intro y hy hz
    funext i
    cases i with
    | none => exact hy
    | some i => exact Fin.elim0 i
  interpret := by
    intro K instK z hz
    exact ⟨Algebra.ofId ℤ K, fun i => Fin.elim0 i⟩

variable {S N m : ℕ}

noncomputable def step (P : Prefix S N m) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial P.carrier) (d : ℕ) : Prefix S N (m + 1) where
  carrier := PaddedIntegralParameterExtension.Extension p d N
  ring := inferInstance
  nontrivial := PaddedIntegralParameterExtension.nontrivial p d N hN
  basis := PaddedIntegralParameterExtension.coordinateBasis P.basis p d
  rows := UniformIntegralPrefixRows.rows S P.rows P.basis p d
  degrees := UniformIntegralPrefixRows.degrees S N P.degrees
  row_degree := UniformIntegralPrefixRows.row_degree S hm hN P.rows P.degrees P.row_degree P.basis p d
  degree_pos := UniformIntegralPrefixRows.degrees_pos S hN P.degrees P.degree_pos
  degree_bound := by
    intro i
    simp only [Nat.add_sub_cancel]
    refine Fin.cases le_rfl (fun j => ?_) i
    exact (P.degree_bound j).trans (Nat.mul_le_mul_left N
      (MonicParameterPowerSchedule.weight_mono N (cap S N) (Nat.sub_le m 1)))
  noInfinity := UniformIntegralPrefixRows.noInfinity (Int.castRingHom ℂ) S hm hN
    P.rows P.degrees P.noInfinity P.basis p d
  interpret := by
    intro K instK z hz
    exact UniformIntegralPrefixRows.interpret S hN P.rows P.basis p d (P.interpret K) z hz

noncomputable def annihilator (P : Prefix S N m) (i : Fin m) : Polynomial ℤ :=
  AffineFiniteCoordinates.annihilator P.rows P.degrees i

theorem annihilator_ne_zero (P : Prefix S N m) (i : Fin m) : annihilator P i ≠ 0 :=
  AffineFiniteCoordinates.ne_zero P.rows P.degrees P.degree_pos P.noInfinity i

theorem annihilator_degree (P : Prefix S N m) (i : Fin m) :
    (annihilator P i).natDegree ≤ AffineFiniteCoordinates.dimension P.degrees + 1 :=
  AffineFiniteCoordinates.degree_le P.rows P.degrees i

theorem annihilator_root {K : Type*} [Field K] (P : Prefix S N m) (z : Fin m → K)
    (hz : ∀ i, (P.rows i).eval₂ (Int.castRingHom K) z = 0) (i : Fin m) :
    (annihilator P i).eval₂ (Int.castRingHom K) (z i) = 0 :=
  AffineFiniteCoordinates.eval_eq_zero P.rows P.degrees P.row_degree z hz i

theorem finite_roots {K : Type*} [Field K] [CharZero K] (P : Prefix S N m) :
    {z : Fin m → K | ∀ i, (P.rows i).eval₂ (Int.castRingHom K) z = 0}.Finite :=
  AffineFiniteCoordinates.finite_roots P.rows P.degrees P.row_degree P.degree_pos P.noInfinity

end LeanCanny.Algebra.UniformIntegralPrefix
