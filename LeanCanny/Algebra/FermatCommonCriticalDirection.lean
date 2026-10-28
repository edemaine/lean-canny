/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveDirectionFamily
public import LeanCanny.Algebra.FermatBoundedCriticalDirection

/-! # A bounded common critical direction for finitely many regular sources

A finite family of pure-power-leading hypersurfaces has one integer direction
making every critical root regular. The grid allowance is the family size
times the single-source allowance, so an exponential family count contributes
only its exponent to the direction bit width. Regularity over coefficient
field extensions is an explicit premise for every member of the family.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCommonCriticalDirection
open MvPolynomial FermatCriticalHomogenization FermatCriticalBadSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {n : ℕ} {K : Type u} [Field K] [CharZero K]

def allowance (n N count : ℕ) : ℕ := count * FermatBoundedCriticalDirection.allowance n N
def binaryWidth (n N countBits : ℕ) : ℕ := countBits + FermatBoundedCriticalDirection.binaryWidth n N

theorem allowance_lt_two_pow (n N count countBits : ℕ) (hc : count ≤ 2 ^ countBits) :
    allowance n N count < 2 ^ binaryWidth n N countBits := by
  unfold allowance binaryWidth
  calc
    _ ≤ 2 ^ countBits * FermatBoundedCriticalDirection.allowance n N := Nat.mul_le_mul_right _ hc
    _ < 2 ^ countBits * 2 ^ FermatBoundedCriticalDirection.binaryWidth n N :=
      Nat.mul_lt_mul_of_pos_left (FermatBoundedCriticalDirection.allowance_lt_two_pow n N) (by positivity)
    _ = _ := by rw [← pow_add]

theorem exists_common_root_free {σ : Type*} [Fintype σ]
    (low : σ → MvPolynomial (Fin (n + 1)) K) (a : σ → K) (ha : ∀ s, a s ≠ 0)
    (N : ℕ) (hlow : ∀ s, (low s).totalDegree < N) (hN : 1 < N)
    (hregular : ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (polynomial (low s) (a s) N) = 0 → ∃ j, aeval x (pderiv j (polynomial (low s) (a s) N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n N (Fintype.card σ)) ∧
      ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (y : Fin (n + 2) → L),
        (∀ j, (nativeRows (low s) (a s) N j).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (v i : L))) y = 0) → y = 0 := by
  let R := MvPolynomial (Fin n) K
  let G := FractionRing R
  let L := AlgebraicClosure G
  let ψ : R →+* L := (algebraMap G L).comp (algebraMap R G)
  let : Algebra K L := (ψ.comp C).toAlgebra
  have hψ : Function.Injective ψ := (algebraMap G L).injective.comp (IsFractionRing.injective R G)
  have hψC : ψ.comp C = algebraMap K L := rfl
  have hroot (s : σ) (y : Fin (n + 2) → L)
      (hy : ∀ j, (nativeRows (low s) (a s) N j).eval₂ ψ y = 0) : y = 0 :=
    FermatCriticalGeneric.native_no_root ψ hψ hψC (low s) (a s) (ha s) N (hlow s) hN
      (FermatCriticalGeneric.independent_direction ψ hψ hψC) (hregular s L) y hy
  exact ProjectiveDirectionFamily.exists_common_bounded (fun s => nativeRows (low s) (a s) N)
    (nativeDegrees n N) (FermatBoundedCriticalDirection.width n N) (n + 1) (Nat.lt_size_self _)
    (fun s => homogeneous (low s) (a s) N) (fun j => degrees_pos N hN (layout.symm j))
    (fun s => native_parameter_degree (low s) (a s) N) ψ hroot

theorem exists_common {σ : Type*} [Fintype σ]
    (low : σ → MvPolynomial (Fin (n + 1)) K) (a : σ → K) (ha : ∀ s, a s ≠ 0)
    (N : ℕ) (hlow : ∀ s, (low s).totalDegree < N) (hN : 1 < N)
    (hregular : ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
      aeval x (polynomial (low s) (a s) N) = 0 → ∃ j, aeval x (pderiv j (polynomial (low s) (a s) N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n N (Fintype.card σ)) ∧
      ∀ s, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (equations (low s) (a s) N j).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (v i : L))) x = 0) →
          (jacobian (low s) (a s) N).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) x ≠ 0 := by
  obtain ⟨v, hv, hgood⟩ := exists_common_root_free low a ha N hlow hN hregular
  refine ⟨v, hv, ?_⟩
  intro s L _ _ x hx hJ
  let φ := eval₂Hom (algebraMap K L) (fun i => (v i : L))
  have hchart (i : Option (Fin (n + 1))) : (rows (low s) (a s) N i).eval₂ φ (fun j => j.elim 1 x) = 0 :=
    HomogeneousBadSystem.chart_root φ (equations (low s) (a s) N) (FermatCriticalInfinity.degrees n N)
      (jacobian (low s) (a s) N) (jacobianDegree n N) (equations_degree (low s) (a s) N (hlow s))
      (jacobian_degree (low s) (a s) N (hlow s)) x hx hJ i
  let y : Fin (n + 2) → L := fun j => (layout.symm j).elim 1 x
  have hy (j : Fin (n + 2)) : (nativeRows (low s) (a s) N j).eval₂ φ y = 0 := by
    simpa only [nativeRows, eval₂_rename, Function.comp_def, y, Equiv.symm_apply_apply] using hchart (layout.symm j)
  have he := congrFun (hgood s L y hy) (layout none)
  have h10 : (1 : L) = 0 := by
    simpa only [y, Equiv.symm_apply_apply, Option.elim_none, Pi.zero_apply] using he
  exact one_ne_zero h10

end LeanCanny.Algebra.FermatCommonCriticalDirection
