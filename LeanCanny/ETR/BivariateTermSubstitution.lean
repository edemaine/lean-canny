/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansionSize
public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Bivariate coordinate substitution in original arithmetic terms

Both variable degrees and coefficient mass are bounded by the original
literal term size and the coordinate bounds. Ring homomorphisms commute
with substitution, including Kronecker encoding and real specialization.
-/

@[expose] public section
namespace LeanCanny.ETR.Term
open Polynomial LeanCanny.Algebra

theorem eval_hom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : Term) (v : ℕ → R) :
    φ (t.eval v) = t.eval (fun i => φ (v i)) := by
  induction t <;> simp_all [eval]

theorem eval_natDegree_le_size {R : Type*} [CommRing R] (t : Term) (v : ℕ → R[X]) (D : ℕ)
    (hv : ∀ i, (v i).natDegree ≤ D) : (t.eval v).natDegree ≤ t.toData.size * D := by
  induction t with
  | const z => simp only [eval, natDegree_intCast]; exact Nat.zero_le _
  | var i =>
    exact (hv i).trans (by rw [dataSize_var]; nlinarith)
  | add a b ha hb =>
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact ha.trans (Nat.mul_le_mul_right D (by rw [dataSize_add]; omega))
    · exact hb.trans (Nat.mul_le_mul_right D (by rw [dataSize_add]; omega))
  | mul a b ha hb =>
    apply natDegree_mul_le.trans
    calc
      _ ≤ a.toData.size * D + b.toData.size * D := Nat.add_le_add ha hb
      _ = (a.toData.size + b.toData.size) * D := by rw [Nat.add_mul]
      _ ≤ (a.mul b).toData.size * D := Nat.mul_le_mul_right D (by rw [dataSize_mul]; omega)

theorem eval_innerDegree_le_size (t : Term) (v : ℕ → (ℤ[X])[X]) (E : ℕ)
    (hv : ∀ i j, ((v i).coeff j).natDegree ≤ E) (j : ℕ) :
    ((t.eval v).coeff j).natDegree ≤ t.toData.size * E := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ j
  change (Polynomial.Bivariate.swap.toRingHom (t.eval v)).natDegree ≤ _
  rw [eval_hom Polynomial.Bivariate.swap.toRingHom t v]
  exact eval_natDegree_le_size t _ E (fun i => (PolynomialKronecker.inner_degree_iff_swap _ _).mp (hv i))

private theorem pow_add_bound (u v : ℕ) : 2 ^ u + 2 ^ v ≤ 2 ^ (u + v + 1) := by
  have hu : 2 ^ u ≤ 2 ^ (u + v) := Nat.pow_le_pow_right (by decide) (by omega)
  have hv : 2 ^ v ≤ 2 ^ (u + v) := Nat.pow_le_pow_right (by decide) (by omega)
  have H := Nat.add_le_add hu hv
  rw [pow_succ]
  omega

theorem eval_nestedMass_le_size (t : Term) (v : ℕ → (ℤ[X])[X]) (b : ℕ)
    (hv : ∀ i, NestedMass.mass (v i) ≤ 2 ^ b) :
    NestedMass.mass (t.eval v) ≤ 2 ^ (t.toData.size * (b + 1)) := by
  induction t with
  | const z =>
    have he : (z : (ℤ[X])[X]) = Polynomial.C (Polynomial.C z) := by simp
    rw [eval, he, NestedMass.C, coefficientMass_C]
    have H := (Term.const z).monomialCoefficient_natAbs_le_pow_dataSize 0
    simp only [monomialCoefficient] at H
    exact H.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  | var i =>
    exact (hv i).trans (Nat.pow_le_pow_right (by decide) (by rw [dataSize_var]; nlinarith))
  | add a b ha hb =>
    apply (NestedMass.add_le _ _).trans
    apply (Nat.add_le_add ha hb).trans
    apply (pow_add_bound _ _).trans
    apply Nat.pow_le_pow_right (by decide)
    rw [dataSize_add]
    nlinarith
  | mul a b ha hb =>
    apply (NestedMass.mul_le _ _).trans
    apply (Nat.mul_le_mul ha hb).trans
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    rw [dataSize_mul]
    nlinarith

end LeanCanny.ETR.Term
