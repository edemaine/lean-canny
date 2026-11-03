/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryCriticalStep
public import LeanCanny.Algebra.CoordinatePowerCoefficients
public import LeanCanny.Algebra.IntegralMixedAffineMatrix
public import LeanCanny.Algebra.IntegralCoordinateBasisFin
public import LeanCanny.Algebra.EmbeddedCoefficient
/-! # Physical heights read literal affine matrix columns

A valid powered scalar monomial reads one representative coefficient, hence
one column-zero multiplication entry. The affine matrix identity then splits
that entry into original affine coefficients, old cleared coordinates and Q.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial IntegralCoordinateBasis FixedWidthPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {ι : Type}

theorem historyHeights_embedded_coefficient (F : Sampler S (2^B) m ι)
    (hs : Function.Injective F.scalar) (H : Fin (n+1)→F.scalarPrefix.carrier)
    (i : Fin (n+1)) (e : ι→₀ℕ) :
    (historyHeights F H i).coeff e=EmbeddedCoefficient.value F.scalar hs
      (CoordinatePowerSubstitution.substitute (weights S (2^B) m) (F.scalarPrefix.basis.representative (H i))) e :=
  EmbeddedCoefficient.coeff_rename F.scalar hs _ e

theorem historyHeights_matrix_coefficient (F : Sampler S (2^B) m ι)
    (hs : Function.Injective F.scalar) (H : Fin (n+1)→F.scalarPrefix.carrier)
    (i : Fin (n+1)) (r : Fin (count m B)) :
    (historyHeights F H i).coeff
      ((CoordinatePowerSubstitution.exponent (weights S (2^B) m) (vector m B r)).mapDomain F.scalar)=
      Algebra.leftMulMatrix F.scalarPrefix.basis.finBasis (H i) r (zeroFin m B) := by
  rw [historyHeights,coeff_rename_mapDomain F.scalar hs,
    CoordinatePowerSubstitution.coefficient_scaled _ (weights_pos S (2^B) m)]
  exact F.scalarPrefix.basis.coefficient_finMatrix (H i) r

end LeanCanny.Algebra.IntegralHistorySampler

namespace LeanCanny.Algebra.IntegralMixedHistory
open MvPolynomial IntegralCoordinateBasis FixedWidthPolynomial UniformIntegralPowerSchedule IntegralHistorySampler
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {P : SpatialSource n} {ι : Type}

theorem physical_height_affine_coefficient (x : State P S B m ι) (hm : m≤S)
    (hs : Function.Injective x.sampler.scalar) (r : CriticalRule n)
    (i : Fin (n+1)) (u : Fin (count m B)) :
    (historyHeights x.sampler (data x hm r).heights i).coeff
      ((CoordinatePowerSubstitution.exponent (weights S (2^B) m) (vector m B u)).mapDomain x.sampler.scalar)=
      (commonDenominator x*IntegralMixedAffineCoefficients.constantCoefficient (r.heights i))*
        (if u=zeroFin m B then 1 else 0)+
      ∑j : Fin m,IntegralMixedAffineCoefficients.referenceCoefficient (r.heights i) j.val*
        Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x j) u (zeroFin m B) := by
  rw [historyHeights_matrix_coefficient x.sampler hs (data x hm r).heights i u]
  exact IntegralMixedAffineMatrix.entry x (r.heights i) u (zeroFin m B)

end LeanCanny.Algebra.IntegralMixedHistory
