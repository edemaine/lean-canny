/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalGeneric
public import LeanCanny.Algebra.ProjectiveDirectionGrid

/-! # Bounded integer critical directions for regular pure-power-leading hypersurfaces

The singular-critical system is root-free over the generic direction field.
A nonzero maximal Macaulay minor then selects a bounded integer direction.
The allowance has polynomial binary length in dimension and source degree
length. Regularity is required over field extensions, including complex roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatBoundedCriticalDirection
open MvPolynomial FermatCriticalHomogenization FermatCriticalBadSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

universe u
variable {n : ℕ} {K : Type u} [Field K] [CharZero K]

def width (n N : ℕ) : ℕ := (Macaulay.level (nativeDegrees n N)).size
def allowance (n N : ℕ) : ℕ := FixedWidthPolynomial.count (n + 2) (width n N) * (n + 1)

theorem allowance_size_le (n N : ℕ) :
    (allowance n N).size ≤ (n + 2) * width n N + (n + 1).size :=
  ProjectiveDirectionGrid.allowance_size_le (n + 1) (width n N) (n + 1)

theorem width_le (n N : ℕ) :
    width n N ≤ (n + 2).size + (n + 1).size + N.size + 1 := by
  let C := (n + 2) * (n + 1) * N
  let T := (n + 2).size + (n + 1).size + N.size
  have hd (j : Fin (n + 2)) : nativeDegrees n N j ≤ (n + 1) * N := by
    dsimp only [nativeDegrees]
    cases h : layout.symm j with
    | none => exact le_rfl
    | some i =>
      apply le_trans (show FermatCriticalInfinity.degrees n N i ≤ N from
        Fin.cases le_rfl (fun _ => Nat.sub_le N 1) i)
      calc
        N = 1 * N := by simp
        _ ≤ (n + 1) * N := Nat.mul_le_mul_right _ (by omega)
  have hlevel : Macaulay.level (nativeDegrees n N) ≤ C + 1 := by
    have hs : (∑ j : Fin (n + 2), (nativeDegrees n N j - 1)) ≤ (n + 2) * ((n + 1) * N) :=
      (Finset.sum_le_sum fun j _ => (Nat.sub_le _ _).trans (hd j)).trans_eq (by simp)
    have he : (n + 2) * ((n + 1) * N) = C := by simp only [C, Nat.mul_assoc]
    unfold Macaulay.level
    omega
  have hC : C < 2 ^ T := by
    calc
      C ≤ (2 ^ (n + 2).size * 2 ^ (n + 1).size) * N := Nat.mul_le_mul_right N
        (Nat.mul_le_mul (Nat.lt_size_self (n + 2)).le (Nat.lt_size_self (n + 1)).le)
      _ < (2 ^ (n + 2).size * 2 ^ (n + 1).size) * 2 ^ N.size :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self N) (by positivity)
      _ = 2 ^ T := by rw [← pow_add, ← pow_add]
  apply Nat.size_le.mpr
  change Macaulay.level (nativeDegrees n N) < 2 ^ (T + 1)
  rw [pow_succ]
  have hpos : 0 < 2 ^ T := by positivity
  omega

theorem allowance_size_le_source (n N : ℕ) :
    (allowance n N).size ≤
      (n + 2) * ((n + 2).size + (n + 1).size + N.size + 1) + (n + 1).size :=
  (allowance_size_le n N).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (width_le n N)) _)

def binaryWidth (n N : ℕ) : ℕ := (n + 2) * (2 * n + N.size + 4) + n + 1

theorem allowance_size_le_binaryWidth (n N : ℕ) : (allowance n N).size ≤ binaryWidth n N := by
  have hn2 : (n + 2).size ≤ n + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hn1 : (n + 1).size ≤ n + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hi : (n + 2).size + (n + 1).size + N.size + 1 ≤ 2 * n + N.size + 4 := by omega
  have hm := Nat.mul_le_mul_left (n + 2) hi
  have h := allowance_size_le_source n N
  unfold binaryWidth
  omega

theorem allowance_lt_two_pow (n N : ℕ) : allowance n N < 2 ^ binaryWidth n N :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (allowance_size_le_binaryWidth n N))

/-- The selected direction works over all extensions of the original
coefficient field, with a bound independent of coefficient magnitudes. -/
theorem exists_bounded_root_free (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0)
    (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (polynomial low a N) = 0 → ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n N) ∧
      ∀ (L : Type u) [Field L] [Algebra K L] (y : Fin (n + 2) → L),
        (∀ j, (nativeRows low a N j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) y = 0) → y = 0 := by
  let R := MvPolynomial (Fin n) K
  let G := FractionRing R
  let L := AlgebraicClosure G
  let ψ : R →+* L := (algebraMap G L).comp (algebraMap R G)
  let : Algebra K L := (ψ.comp C).toAlgebra
  have hψ : Function.Injective ψ :=
    (algebraMap G L).injective.comp (IsFractionRing.injective R G)
  have hψC : ψ.comp C = algebraMap K L := rfl
  have hroot (y : Fin (n + 2) → L) (hy : ∀ j, (nativeRows low a N j).eval₂ ψ y = 0) : y = 0 :=
    FermatCriticalGeneric.native_no_root ψ hψ hψC low a ha N hlow hN
      (FermatCriticalGeneric.independent_direction ψ hψ hψC) (hregular L) y hy
  exact ProjectiveDirectionGrid.exists_bounded (nativeRows low a N) (nativeDegrees n N)
    (width n N) (n + 1) (Nat.lt_size_self _) (homogeneous low a N)
    (fun j => degrees_pos N hN (layout.symm j)) (native_parameter_degree low a N) ψ hroot

/-- Every spatial critical root in the selected integer direction has a
nonzero spatial Jacobian. No exceptional-direction polynomial is supplied. -/
theorem exists_bounded (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0)
    (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (polynomial low a N) = 0 → ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n N) ∧
      ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (equations low a N j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) x = 0) →
        (jacobian low a N).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) x ≠ 0 := by
  obtain ⟨v, hv, hgood⟩ := exists_bounded_root_free low a ha N hlow hN hregular
  refine ⟨v, hv, ?_⟩
  intro L _ _ x hx hJ
  let φ := eval₂Hom (algebraMap K L) (fun i => (v i : L))
  have hchart (i : Option (Fin (n + 1))) : (rows low a N i).eval₂ φ (fun j => j.elim 1 x) = 0 :=
    HomogeneousBadSystem.chart_root φ (equations low a N) (FermatCriticalInfinity.degrees n N)
      (jacobian low a N) (jacobianDegree n N) (equations_degree low a N hlow) (jacobian_degree low a N hlow)
      x hx hJ i
  let y : Fin (n + 2) → L := fun j => (layout.symm j).elim 1 x
  have hy (j : Fin (n + 2)) : (nativeRows low a N j).eval₂ φ y = 0 := by
    simpa only [nativeRows, eval₂_rename, Function.comp_def, y, Equiv.symm_apply_apply] using hchart (layout.symm j)
  have he := congrFun (hgood L y hy) (layout none)
  have h10 : (1 : L) = 0 := by simpa only [y, Equiv.symm_apply_apply, Option.elim_none, Pi.zero_apply] using he
  exact one_ne_zero h10

end LeanCanny.Algebra.FermatBoundedCriticalDirection
