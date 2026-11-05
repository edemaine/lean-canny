/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
public import LeanCanny.Algebra.CoefficientCoordinateBasisMatrix
public import LeanCanny.Algebra.PaddedIntegralHeightMatrix
/-! # Exact specialization of fixed-index leading normalization

The basis-coordinate specialization derives the multiplication matrix and
characteristic polynomial. The final native normalizer uses guards on the
actual specialized coefficients, allowing earlier symbolic coefficients to die.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
open Polynomial
open scoped Classical
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {m N :ℕ}
  {φ :R→+*S} {ψ :A→+*B}
  {b :CoefficientCoordinateBasis R A m N} {c :CoefficientCoordinateBasis S B m N}

theorem denominatorAt_map (H :CoefficientCoordinateBasis.Specializes φ ψ b c)
    (a :A) (τ :ℕ) :
    φ (denominatorAt b.basis a τ)=denominatorAt c.basis (ψ a) τ:=by
  rw [denominatorAt,denominatorAt,H.charpoly_map,coeff_map]

theorem inverseValueAt_map (H :CoefficientCoordinateBasis.Specializes φ ψ b c)
    (a :A) (τ :ℕ) :
    ψ (inverseValueAt b.basis a τ)=inverseValueAt c.basis (ψ a) τ:=by
  have HC :ψ.comp (algebraMap R A)=(algebraMap S B).comp φ:=by
    ext r
    exact H.coefficients r
  rw [inverseValueAt,inverseValueAt,H.charpoly_map,
    ←IntegralParameterInverse.inverseAt_map,hom_eval₂,eval₂_map,HC]

theorem normalizeAt_map (H :CoefficientCoordinateBasis.Specializes φ ψ b c)
    (p :A[X]) (d τ :ℕ) :
    (normalizeAt b.basis p d τ).map ψ=normalizeAt c.basis (p.map ψ) d τ:=by
  simp only [normalizeAt,Polynomial.map_add,map_monomial,Polynomial.map_mul,map_C,
    Polynomial.map_sub,coeff_map]
  rw [H.coefficients,denominatorAt_map H,inverseValueAt_map H]

/-- The target is the actual integer normalizer, not a chosen symbolic branch.
The two guards select the trailing index after specialization. -/
theorem normalizeAt_map_native {φ :R→+*ℤ} {ψ :A→+*B}
    {c :CoefficientCoordinateBasis ℤ B m N}
    (H :CoefficientCoordinateBasis.Specializes φ ψ b c) (p :A[X]) (d τ :ℕ)
    (Hbelow :∀k<τ,φ ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff k)=0)
    (Hτ :φ ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff τ)≠0) :
    (normalizeAt b.basis p d τ).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.basis (p.map ψ) d:=by
  have HT :(Algebra.leftMulMatrix c.basis ((p.map ψ).coeff d)).charpoly.natTrailingDegree=τ:=by
    rw [coeff_map,H.charpoly_map]
    exact IntegralParameterInverse.natTrailingDegree_map_at φ _ τ Hbelow Hτ
  rw [normalizeAt_map H,←HT,normalizeAt_native]

/-- The fixed-width native basis has the same characteristic polynomial as
its monomial-coordinate basis, so this is the normalizer used by script cuts. -/
theorem normalizeAt_map_native_finBasis {φ :R→+*ℤ} {ψ :A→+*B} {w :ℕ}
    {b :CoefficientCoordinateBasis R A m (2^w)} (c :IntegralCoordinateBasis B m (2^w))
    (H :CoefficientCoordinateBasis.Specializes φ ψ b (CoefficientCoordinateBasis.ofIntegral c))
    (p :A[X]) (d τ :ℕ)
    (Hbelow :∀k<τ,φ ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff k)=0)
    (Hτ :φ ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff τ)≠0) :
    (normalizeAt b.basis p d τ).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.finBasis (p.map ψ) d:=by
  rw [normalizeAt_map_native H p d τ Hbelow Hτ]
  simp only [CoefficientCoordinateBasis.ofIntegral,
    IntegralRelativeLeadingNormalization.normalize,
    IntegralRelativeLeadingNormalization.denominator,
    IntegralRelativeLeadingNormalization.inverseValue,c.finBasis_charpoly]

end LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
