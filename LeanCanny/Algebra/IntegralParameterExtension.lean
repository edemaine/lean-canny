/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedDegreeIntegralNormalization
public import LeanCanny.Algebra.IntegralParameterInverse
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower

/-! # Adjoining a scalar height with an integer denominator

A polynomial over an existing finite free integer algebra can specialize to
an equation of smaller degree. Choosing that effective degree gives a monic
extension of exactly the advertised rank, even on other branches where the
selected leading coefficient vanishes. At every valid specialization the
new root represents the requested height with a nonzero integer denominator.
No reducedness or irreducibility assumption is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterExtension
open Polynomial
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A]

noncomputable abbrev Extension (p : Polynomial A) (d : ℕ) :=
  AdjoinRoot (FixedDegreeIntegralNormalization.polynomial p d)

noncomputable def relativeBasis [Nontrivial A] (p : Polynomial A) (d : ℕ) :
    Module.Basis (Fin d) A (Extension p d) :=
  (AdjoinRoot.powerBasis' (FixedDegreeIntegralNormalization.monic p d)).basis.reindex
    (finCongr (FixedDegreeIntegralNormalization.natDegree p d))

noncomputable def basis [Nontrivial A] {ι : Type*} (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    Module.Basis (ι × Fin d) ℤ (Extension p d) :=
  b.smulTower (relativeBasis p d)

theorem basis_card {ι : Type*} [Fintype ι] (d : ℕ) :
    Fintype.card (ι × Fin d) = Fintype.card ι * d := by simp

variable {K : Type*} [Field K]

noncomputable def evaluate (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] K) (t : K)
    (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    Extension p d →ₐ[ℤ] K :=
  AdjoinRoot.liftAlgHom _ φ (φ (p.coeff d) * t)
    (FixedDegreeIntegralNormalization.scaled_root p d φ.toRingHom hd hpos t ht)

theorem evaluate_of (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] K) (t : K) hd hpos ht (a : A) :
    evaluate p d φ t hd hpos ht (AdjoinRoot.of _ a) = φ a :=
  AdjoinRoot.liftAlgHom_of _ φ _ _ a

theorem evaluate_root (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] K) (t : K) hd hpos ht :
    evaluate p d φ t hd hpos ht (AdjoinRoot.root _) = φ (p.coeff d) * t :=
  AdjoinRoot.liftAlgHom_root _ φ _ _

theorem selected_coefficient_ne_zero (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] K)
    (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) : φ (p.coeff d) ≠ 0 := by
  have hp : p.map φ.toRingHom ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hd
    omega
  have H : (p.map φ.toRingHom).coeff d ≠ 0 := by
    rw [← hd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  simpa only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using H

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def denominator (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) : ℤ :=
  IntegralParameterInverse.denominator (Algebra.leftMulMatrix b (p.coeff d)).charpoly

noncomputable def numerator (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) : Extension p d :=
  AdjoinRoot.root _ * AdjoinRoot.of _
    (Polynomial.aeval (p.coeff d)
      (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b (p.coeff d)).charpoly))

theorem denominator_ne_zero (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    denominator b p d ≠ 0 :=
  IntegralParameterInverse.charpoly_denominator_ne_zero b (p.coeff d)

variable [CharZero K]

theorem recover (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) (φ : A →ₐ[ℤ] K) (t : K)
    (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    evaluate p d φ t hd hpos ht (numerator b p d) / ((denominator b p d : ℤ) : K) = t := by
  have H := IntegralParameterInverse.recover_algebra_value b (p.coeff d) φ
    (selected_coefficient_ne_zero p d φ hd hpos) t
  simp only [numerator, map_mul, evaluate_root, evaluate_of, ← Polynomial.aeval_algHom_apply]
  exact H

end LeanCanny.Algebra.IntegralParameterExtension
