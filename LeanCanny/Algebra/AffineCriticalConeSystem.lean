/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericAffineConeFlag
public import LeanCanny.Algebra.NestedTotalDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Homogeneous critical equations for an affine-height cone slice

Ambient coordinates have weight one and multipliers have weight D-1.
Replacing each multiplier by a (D-1)-st power gives ordinary homogeneous
rows without discarding the gradient/multiplier balance at infinity.
The new objective is the only parameter block, with coefficient degree one.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalConeSystem
open MvPolynomial FlatAffineCriticalStage GenericAffineCriticalJacobian GenericAffineConeFlag
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

noncomputable def lift (q : MvPolynomial (Variables n) K) :
    MvPolynomial (Variables n) (MvPolynomial (Fin n) K) := q.map C

noncomputable def oldGradient (A : Fin n → Fin n → K) (D : ℕ) (i : Fin n) :
    MvPolynomial (Variables n) K := ∑ r, C (A r i) * X (Sum.inr r.succ) ^ (D - 1)

noncomputable def oldHeight (A : Fin n → Fin n → K) (r : Fin n) :
    MvPolynomial (Variables n) K := ∑ i, C (A r i) * X (Sum.inl i)

noncomputable def rows (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) : Variables n → MvPolynomial (Variables n) (MvPolynomial (Fin n) K)
  | .inl i => lift (rename Sum.inl (pderiv i p)) -
      C (X i) * lift (X (Sum.inr 0) ^ (D - 1)) - lift (oldGradient A D i)
  | .inr j => Fin.cases (lift (rename Sum.inl p))
      (fun r => if r ∈ s then lift (oldHeight A r) else lift (X (Sum.inr r.succ) ^ (D - 1))) j

def degrees (D : ℕ) (s : Finset (Fin n)) : Variables n → ℕ
  | .inl _ => D - 1
  | .inr j => Fin.cases D (fun r => if r ∈ s then 1 else D - 1) j

theorem degrees_pos (D : ℕ) (hD : 1 < D) (s : Finset (Fin n)) (j : Variables n) :
    0 < degrees D s j := by
  cases j with
  | inl i => change 0 < D - 1; omega
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · change 0 < D; omega
    · change 0 < if r ∈ s then 1 else D - 1
      split_ifs <;> omega

theorem degrees_le (D : ℕ) (s : Finset (Fin n)) (hD : 0 < D) (j : Variables n) :
    degrees D s j ≤ D := by
  cases j with
  | inl i => exact Nat.sub_le _ _
  | inr j =>
    refine Fin.cases le_rfl (fun r => ?_) j
    change (if r ∈ s then 1 else D - 1) ≤ D
    split_ifs <;> omega

theorem homogeneous (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (j : Variables n) :
    (rows p D s A j).IsHomogeneous (degrees D s j) := by
  have hpow (r : Fin (n + 1)) : (X (Sum.inr r) ^ (D - 1) :
      MvPolynomial (Variables n) K).IsHomogeneous (D - 1) := by
    simpa only [one_mul] using (isHomogeneous_X (R := K) (Sum.inr r)).pow (D - 1)
  cases j with
  | inl i =>
    apply IsHomogeneous.sub
    · apply IsHomogeneous.sub
      · exact (hD.pderiv.rename_isHomogeneous).map C
      · exact ((hpow 0).map C).C_mul _
    · apply IsHomogeneous.map
      apply IsHomogeneous.sum
      intro r _
      exact (hpow r.succ).C_mul _
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · exact hD.rename_isHomogeneous.map C
    · by_cases hr : r ∈ s
      · simp only [rows, degrees, Fin.cases_succ, hr, ite_true, lift, oldHeight]
        apply IsHomogeneous.map
        apply IsHomogeneous.sum
        intro i _
        exact (isHomogeneous_X (R := K) (Sum.inl i)).C_mul _
      · simpa only [rows, degrees, Fin.cases_succ, hr, ite_false, lift] using (hpow r.succ).map C

theorem lift_parameter_degree (q : MvPolynomial (Variables n) K) (B : ℕ) :
    NestedTotalDegree.Bound (lift q) B := by
  intro e
  simp only [lift, coeff_map, totalDegree_C]
  exact Nat.zero_le B

theorem parameter_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (j : Variables n) : NestedTotalDegree.Bound (rows p D s A j) 1 := by
  cases j with
  | inl i =>
    apply NestedTotalDegree.sub
    · apply NestedTotalDegree.sub
      · exact lift_parameter_degree _ _
      · have hCX : NestedTotalDegree.Bound (C (X i) :
            MvPolynomial (Variables n) (MvPolynomial (Fin n) K)) 1 := by
          intro e
          rw [coeff_C]
          split_ifs <;> simp
        exact (NestedTotalDegree.mul hCX (lift_parameter_degree _ 0))
    · exact lift_parameter_degree _ _
  | inr j =>
    refine Fin.cases (lift_parameter_degree _ _) (fun r => ?_) j
    by_cases hr : r ∈ s <;> simpa only [rows, Fin.cases_succ, hr, ite_true, ite_false] using lift_parameter_degree (K := K) (n := n) _ 1

theorem eval_lift (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (q : MvPolynomial (Variables n) K) (z : Variables n → L) :
    (lift q).eval₂ φ z = aeval z q := by rw [lift, eval₂_map, hφ, aeval_def]

theorem roots_iff (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (z : Variables n → L) :
    (∀ j, (rows p D s A j).eval₂ φ z = 0) ↔
      aeval (z ∘ Sum.inl) p = 0 ∧
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * z (Sum.inl i) = 0) ∧
      (∀ i, aeval (z ∘ Sum.inl) (pderiv i p) = φ (X i) * z (Sum.inr 0) ^ (D - 1) +
        ∑ r, algebraMap K L (A r i) * z (Sum.inr r.succ) ^ (D - 1)) ∧
      ∀ r, r ∉ s → z (Sum.inr r.succ) ^ (D - 1) = 0 := by
  have hgrad (i : Fin n) : (rows p D s A (Sum.inl i)).eval₂ φ z = 0 ↔
      aeval (z ∘ Sum.inl) (pderiv i p) = φ (X i) * z (Sum.inr 0) ^ (D - 1) +
        ∑ r, algebraMap K L (A r i) * z (Sum.inr r.succ) ^ (D - 1) := by
    simp only [rows, eval₂_sub, eval₂_mul, eval₂_C, eval_lift φ hφ, aeval_def,
      eval₂_rename, oldGradient, eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    constructor <;> intro h <;> linear_combination h
  have hsource : (rows p D s A (Sum.inr 0)).eval₂ φ z = aeval (z ∘ Sum.inl) p := by
    simp only [rows, Fin.cases_zero, eval_lift φ hφ, aeval_def, eval₂_rename]
  have hheight (r : Fin n) (hr : r ∈ s) :
      (rows p D s A (Sum.inr r.succ)).eval₂ φ z = ∑ i, algebraMap K L (A r i) * z (Sum.inl i) := by
    simp only [rows, Fin.cases_succ, hr, ite_true, eval_lift φ hφ, oldHeight,
      map_sum, map_mul, aeval_C, aeval_X]
  have hunused (r : Fin n) (hr : r ∉ s) :
      (rows p D s A (Sum.inr r.succ)).eval₂ φ z = z (Sum.inr r.succ) ^ (D - 1) := by
    simp only [rows, Fin.cases_succ, hr, ite_false, eval_lift φ hφ, map_pow, aeval_X]
  constructor
  · intro h
    exact ⟨hsource ▸ h (Sum.inr 0), fun r hr => hheight r hr ▸ h (Sum.inr r.succ),
      fun i => (hgrad i).mp (h (Sum.inl i)), fun r hr => hunused r hr ▸ h (Sum.inr r.succ)⟩
  · rintro ⟨hp, hl, hg, hu⟩ j
    cases j with
    | inl i => exact (hgrad i).mpr (hg i)
    | inr j =>
      refine Fin.cases (hsource.symm ▸ hp) (fun r => ?_) j
      by_cases hr : r ∈ s
      · exact (hheight r hr).symm ▸ hl r hr
      · exact (hunused r hr).symm ▸ hu r hr

/-- Power substitution does not introduce projective roots: vanishing of
all multiplier powers forces all substituted multiplier coordinates to zero. -/
theorem no_root [CharZero K] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (hind : AlgebraicIndependent K (fun i => φ (X i)))
    (hA : NormalIndependent (L := L) s A)
    (hcone : ∀ x : Fin n → L, aeval x p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) → x ≠ 0 →
      ConstraintIndependent p s A x)
    (z : Variables n → L) (hz : ∀ j, (rows p D s A j).eval₂ φ z = 0) : z = 0 := by
  obtain ⟨hp, hl, hg, hu⟩ := (roots_iff φ hφ p D s A z).mp hz
  obtain ⟨hx, hμ⟩ := critical_root_zero p D hD hD2 s hs A (fun i => φ (X i))
    (z ∘ Sum.inl) (fun r => z (Sum.inr r) ^ (D - 1)) hind hA hcone hp hl hg hu
  funext j
  cases j with
  | inl i => exact congrFun hx i
  | inr r => exact (pow_eq_zero_iff (by omega : D - 1 ≠ 0)).mp (congrFun hμ r)

/-- Over an algebraically closed field every original multiplier admits
a power-coordinate lift, so the homogeneous system retains every critical root. -/
theorem lift_critical_root [IsAlgClosed L] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (x : Fin n → L) (μ : Fin (n + 1) → L)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = φ (X i) * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) :
    ∃ z : Variables n → L, z ∘ Sum.inl = x ∧
      (∀ r, z (Sum.inr r) ^ (D - 1) = μ r) ∧ ∀ j, (rows p D s A j).eval₂ φ z = 0 := by
  choose ν hν using fun r => IsAlgClosed.exists_pow_nat_eq (μ r) (by omega : 0 < D - 1)
  refine ⟨Sum.elim x ν, rfl, hν, (roots_iff φ hφ p D s A (Sum.elim x ν)).mpr ?_⟩
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, hν] using And.intro hp (And.intro hl (And.intro hg hu))

/-- The square system has exactly 2*n+1 variables and rows. -/
def layout (n : ℕ) : Variables n ≃ Fin (2 * n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

noncomputable def nativeRows (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (j : Fin (2 * n + 1)) :
    MvPolynomial (Fin (2 * n + 1)) (MvPolynomial (Fin n) K) :=
  rename (layout n) (rows p D s A ((layout n).symm j))

def nativeDegrees (D : ℕ) (s : Finset (Fin n)) (j : Fin (2 * n + 1)) : ℕ :=
  degrees D s ((layout n).symm j)

theorem native_homogeneous (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (j : Fin (2 * n + 1)) :
    (nativeRows p D s A j).IsHomogeneous (nativeDegrees D s j) :=
  (homogeneous p D hD s A ((layout n).symm j)).rename_isHomogeneous

theorem native_parameter_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (j : Fin (2 * n + 1)) :
    NestedTotalDegree.Bound (nativeRows p D s A j) 1 :=
  NestedTotalDegree.rename (layout n) (parameter_degree p D s A ((layout n).symm j))

theorem independent_parameters (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (hinj : Function.Injective φ) :
    AlgebraicIndependent K (fun i => φ (X i)) := by
  let f : MvPolynomial (Fin n) K →ₐ[K] L :=
    { toRingHom := φ
      commutes' := fun k => by
        change φ (C k) = algebraMap K L k
        exact congrArg (fun g : K →+* L => g k) hφ }
  exact (algebraicIndependent_X (Fin n) K).map (f := f) hinj.injOn

theorem native_no_root [CharZero K] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (hinj : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D) (hD2 : 1 < D)
    (s : Finset (Fin n)) (hs : s.card < n) (A : Fin n → Fin n → K)
    (hA : NormalIndependent (L := L) s A)
    (hcone : ∀ x : Fin n → L, aeval x p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) → x ≠ 0 →
      ConstraintIndependent p s A x)
    (z : Fin (2 * n + 1) → L) (hz : ∀ j, (nativeRows p D s A j).eval₂ φ z = 0) : z = 0 := by
  have hz' (j : Variables n) : (rows p D s A j).eval₂ φ (z ∘ layout n) = 0 := by
    simpa only [nativeRows, eval₂_rename, Equiv.symm_apply_apply] using hz (layout n j)
  have H := no_root φ hφ p D hD hD2 s hs A (independent_parameters φ hφ hinj) hA hcone
    (z ∘ layout n) hz'
  funext j
  have he := congrFun H ((layout n).symm j)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using he

/-- Root-freeness of the power-coordinate system excludes original critical
roots too, including roots with a zero objective multiplier. -/
theorem critical_root_zero_of_native [IsAlgClosed L] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K)
    (hfree : ∀ z : Fin (2 * n + 1) → L, (∀ j, (nativeRows p D s A j).eval₂ φ z = 0) → z = 0)
    (x : Fin n → L) (μ : Fin (n + 1) → L)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = φ (X i) * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) : x = 0 ∧ μ = 0 := by
  obtain ⟨z, hx, hμ, hz⟩ := lift_critical_root φ hφ p D hD s A x μ hp hl hg hu
  have hzn : (z ∘ (layout n).symm) = 0 := by
    apply hfree
    intro j
    simpa only [nativeRows, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply] using hz ((layout n).symm j)
  have hz0 : z = 0 := by
    funext j
    have H := congrFun hzn (layout n j)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using H
  refine ⟨?_, ?_⟩
  · rw [← hx, hz0]; rfl
  · funext r
    have H := hμ r
    rw [hz0, Pi.zero_apply, zero_pow (by omega : D - 1 ≠ 0)] at H
    exact H.symm

end LeanCanny.Algebra.AffineCriticalConeSystem
