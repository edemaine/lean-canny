/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulExterior
public import LeanCanny.Algebra.MacaulayGenericShift

/-! # Connecting the exterior differential with the finite Macaulay map

The degree-one exterior differential is polynomial multiplication. On
degree-compatible multiplier families its kernel agrees with the finite
Macaulay coefficient kernel. The earlier Koszul relation vectors are the
boundaries of monomial multiples of exterior pairs.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulExterior
open scoped BigOperators
variable {R I : Type*} [CommRing R] [Fintype I]

theorem differential_ι (p v : I → R) :
    differential p (ExteriorAlgebra.ι R v) = algebraMap R (Total R I) (∑ i, v i * p i) :=
  CliffordAlgebra.contractLeft_ι _ (linearForm p) v

theorem differential_ι_eq_zero_iff (p v : I → R) :
    differential p (ExteriorAlgebra.ι R v) = 0 ↔ ∑ i, v i * p i = 0 := by
  rw [differential_ι]
  exact ExteriorAlgebra.algebraMap_eq_zero_iff (I → R) _

variable [DecidableEq I]

theorem linearForm_single (p : I → R) (i : I) : linearForm p (Pi.single i 1) = p i := by
  simp [linearForm, Pi.single_apply]

omit [Fintype I] in
theorem ι_single (i : I) (a : R) :
    ExteriorAlgebra.ι R (Pi.single i a) = a • ExteriorAlgebra.ι R (Pi.single i 1 : I → R) := by
  have he : (Pi.single i a : I → R) = a • (Pi.single i 1 : I → R) := by
    funext k
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [he, map_smul]

theorem differential_pair (p : I → R) (i j : I) :
    differential p (ExteriorAlgebra.ι R (Pi.single j 1 : I → R) * ExteriorAlgebra.ι R (Pi.single i 1 : I → R)) =
      ExteriorAlgebra.ι R (Pi.single i (p j) - Pi.single j (p i)) := by
  rw [differential_ι_mul, linearForm_single, differential_ι]
  change p j • ExteriorAlgebra.ι R (Pi.single i 1 : I → R) -
      ExteriorAlgebra.ι R (Pi.single j 1 : I → R) * algebraMap R (Total R I) (linearForm p (Pi.single i 1)) = _
  rw [linearForm_single]
  have hrhs : ExteriorAlgebra.ι R (Pi.single i (p j) - Pi.single j (p i)) =
      p j • ExteriorAlgebra.ι R (Pi.single i 1 : I → R) -
        p i • ExteriorAlgebra.ι R (Pi.single j 1 : I → R) := by
    rw [map_sub]
    exact congrArg₂ (· - ·) (ι_single i (p j)) (ι_single j (p i))
  have hc : ExteriorAlgebra.ι R (Pi.single j 1 : I → R) * algebraMap R (Total R I) (p i) =
      p i • ExteriorAlgebra.ι R (Pi.single j 1 : I → R) := by
    rw [← Algebra.commutes, Algebra.smul_def]
  rw [hc, hrhs]

end LeanCanny.Algebra.KoszulExterior

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem koszulMultipliers_exterior_boundary (p : Fin n → MvPolynomial (Fin n) R)
    (i j : Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential p
      (MvPolynomial.monomial m (1 : R) •
        (ExteriorAlgebra.ι (MvPolynomial (Fin n) R) (Pi.single j 1 : Fin n → MvPolynomial (Fin n) R) *
          ExteriorAlgebra.ι (MvPolynomial (Fin n) R) (Pi.single i 1 : Fin n → MvPolynomial (Fin n) R))) =
      ExteriorAlgebra.ι (MvPolynomial (Fin n) R) (koszulMultipliers p i j m) := by
  have hq : koszulMultipliers p i j m = MvPolynomial.monomial m (1 : R) •
      (Pi.single i (p j) - Pi.single j (p i)) := by
    funext k
    simp only [koszulMultipliers, Pi.sub_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
      mul_sub, mul_ite, mul_zero]
  rw [map_smul, KoszulExterior.differential_pair, hq, map_smul]

theorem finite_kernel_iff_exterior (p q : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (hq : ∀ i m, m ∈ (q i).support → m.degree + d i = level d) :
    Matrix.vecMul (sourceCoefficients q d W) (fullMatrix p d W) = 0 ↔
      KoszulExterior.differential p (ExteriorAlgebra.ι (MvPolynomial (Fin n) R) q) = 0 := by
  rw [KoszulExterior.differential_ι_eq_zero_iff]
  constructor
  · intro hv
    have he : assemble p d W (sourceCoefficients q d W) = 0 := by
      apply homogeneous_eq_of_active_coefficients _ 0 d W hW
        (assemble_homogeneous p d W hp _) (MvPolynomial.isHomogeneous_zero (Fin n) R (level d))
      intro r
      have hr := congrFun hv r
      change Matrix.vecMul (sourceCoefficients q d W) (fullMatrix p d W) r = 0 at hr
      rw [vecMul_fullMatrix] at hr
      simpa using hr
    rwa [assemble_coefficients p q d W hW hq] at he
  · intro he
    funext r
    change Matrix.vecMul (sourceCoefficients q d W) (fullMatrix p d W) r = 0
    rw [vecMul_fullMatrix, assemble_coefficients p q d W hW hq, he]
    simp

end LeanCanny.Algebra.Macaulay
