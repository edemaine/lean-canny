/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerQuotient
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.Finset.Max

/-!
# The normal-monomial basis over an arbitrary coefficient ring

The low-degree residue pairing detects a coefficient of maximal total
degree in any proposed dependence. This proves independence without
assuming that the coefficient ring is a field or that the roots are simple.
-/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial Module
open scoped Classical BigOperators

variable {S : Type*} [CommRing S] {n ell : ℕ}

@[expose] def normalDegree (a : NormalIndex n ell) : ℕ := ∑ i, (a i).val

@[expose] noncomputable def complementExponent (b : NormalIndex n ell) : Fin n →₀ ℕ :=
  exponent (fun i => ell - 1 - (b i).val)

theorem boxExponent_degree (a : NormalIndex n ell) :
    (boxExponent a).sum (fun _ e => e) = normalDegree a := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rfl

theorem complement_degree (b : NormalIndex n ell) :
    normalDegree b + (complementExponent b).sum (fun _ e => e) = n * (ell - 1) := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  change (∑ i, (b i).val) + (∑ i, (ell - 1 - (b i).val)) = _
  rw [← Finset.sum_add_distrib]
  have hi (i : Fin n) : (b i).val + (ell - 1 - (b i).val) = ell - 1 := by
    have := (b i).isLt
    omega
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem box_add_complement_iff (a b : NormalIndex n ell) :
    boxExponent a + complementExponent b = exponent (fun _ => ell - 1) ↔ a = b := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have hh := congrArg (fun e : Fin n →₀ ℕ => e i) h
    simp only [Finsupp.add_apply, boxExponent_apply, complementExponent, exponent_apply] at hh
    have := (b i).isLt
    omega
  · rintro rfl
    ext i
    simp only [Finsupp.add_apply, boxExponent_apply, complementExponent, exponent_apply]
    have := (a i).isLt
    omega

/-- Below the maximal-degree block the residue pairing is the identity matrix. -/
theorem residue_normal_pair (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (a b : NormalIndex n ell) (hab : normalDegree a ≤ normalDegree b) :
    residue ell r (monomial (boxExponent a) 1 * monomial (complementExponent b) 1) =
      if a = b then 1 else 0 := by
  have ha := MvPolynomial.totalDegree_monomial_le (boxExponent a) (1 : S)
  have hb := MvPolynomial.totalDegree_monomial_le (complementExponent b) (1 : S)
  have hd := MvPolynomial.totalDegree_mul
    (monomial (boxExponent a) (1 : S)) (monomial (complementExponent b) 1)
  have hcomp := complement_degree b
  change (monomial (boxExponent a) (1 : S)).totalDegree ≤
    (boxExponent a).sum (fun _ e => e) at ha
  change (monomial (complementExponent b) (1 : S)).totalDegree ≤
    (complementExponent b).sum (fun _ e => e) at hb
  rw [boxExponent_degree] at ha
  have htotal : (monomial (boxExponent a) (1 : S) *
      monomial (complementExponent b) 1).totalDegree ≤ n * (ell - 1) := by omega
  rw [residue_low_degree hell r hr _ htotal]
  simp only [MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.coeff_monomial,
    box_add_complement_iff]

/-- No nonzero relation can have a coefficient of maximal monomial degree. -/
theorem normalClass_linearIndependent (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    LinearIndependent S (normalClass ell r) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  by_contra hca
  let s : Finset (NormalIndex n ell) := Finset.univ.filter (fun b => c b ≠ 0)
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image s normalDegree hs
  have hcb : c b ≠ 0 := (Finset.mem_filter.mp hb).2
  let q : MvPolynomial (Fin n) S := ∑ j, c j • monomial (boxExponent j) 1
  have hp : projection ell r q = 0 := by
    simpa only [q, map_sum, map_smul, normalClass] using hc
  have hq : q ∈ relationIdeal ell r := (projection_eq_zero_iff ell r q).mp hp
  let m : MvPolynomial (Fin n) S := monomial (complementExponent b) 1
  have hz : linear hell r hr (q * m) = 0 := by
    rw [mul_comm]
    exact linear_mul_mem_ideal hell r hr q hq m
  have hterm (j : NormalIndex n ell) :
      linear hell r hr ((c j • monomial (boxExponent j) 1) * m) =
        c j * (if j = b then 1 else 0) := by
    by_cases hcj : c j = 0
    · simp only [hcj, zero_smul, zero_mul, map_zero]
    · have hj : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
      rw [smul_mul_assoc, map_smul, linear_apply]
      rw [show m = monomial (complementExponent b) (1 : S) from rfl,
        residue_normal_pair hell r hr j b (hmax j hj), smul_eq_mul]
  have hsum : linear hell r hr (q * m) = c b := by
    dsimp only [q]
    rw [Finset.sum_mul, map_sum]
    simp_rw [hterm]
    simp
  exact hcb (hsum.symm.trans hz)

/-- The concrete normal-monomial basis of the pure-power quotient. -/
@[expose] noncomputable def normalBasis (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    Basis (NormalIndex n ell) S (QuotientAlgebra ell r) :=
  Basis.mk (normalClass_linearIndependent hell r hr) (by rw [normal_span_eq_top r hr])

@[simp] theorem normalBasis_apply (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (a : NormalIndex n ell) : normalBasis hell r hr a = normalClass ell r a :=
  Basis.mk_apply _ _ a

@[simp] theorem card_normalIndex (n ell : ℕ) : Fintype.card (NormalIndex n ell) = ell ^ n := by
  simp [NormalIndex]

end LeanCanny.CountingHierarchy.PurePowerResidue
