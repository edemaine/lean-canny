/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryCriticalStep
public import LeanCanny.Algebra.PaddedIntegralEquationMass
/-! # Mass of full physical critical histories

These estimates concern the sampler's full rows, including physical and
multiplier rows. Algebra-element bounds are proved matrix inequalities,
not computational access assumptions. Power substitutions cannot increase mass.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule FixedWidthPolynomial IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem historyHeights_mass (F : Sampler S (2^B) m ι)
    (H : Fin (n+1)→F.scalarPrefix.carrier) (G : ℕ)
    (hH : ∀i r,(Algebra.leftMulMatrix F.scalarPrefix.basis.finBasis (H i) r (zeroFin m B)).natAbs≤2^G)
    (i : Fin (n+1)) :
    MvMass.mass (historyHeights F H i)≤count m B*2^G :=
  (MvMass.rename_le F.scalar _).trans ((CoordinatePowerSubstitution.mass_le _ _).trans
    (PaddedIntegralParameterExtension.representative_mass F.scalarPrefix.basis (H i) G (hH i)))

theorem criticalStep_old_row_mass (F : Sampler S (2^B) m ι) (d : CriticalData F.scalarPrefix n) (i : ι) :
    MvMass.mass ((criticalStep F d).rows (Sum.inl i))≤MvMass.mass (F.rows i) :=
  MvMass.rename_le Sum.inl _

theorem criticalStep_new_row_mass (F : Sampler S (2^B) m ι) (d : CriticalData F.scalarPrefix n)
    (U G : ℕ)
    (ha : ∀j i,(PhysicalPowerCriticalRows.coordinateNormals d.objective d.scales d.free j i).natAbs≤U)
    (hH : ∀i r,(Algebra.leftMulMatrix F.scalarPrefix.basis.finBasis (d.heights i) r (zeroFin m B)).natAbs≤2^G)
    (j : Variables (n+1)) :
    MvMass.mass ((criticalStep F d).rows (Sum.inr j))≤
      FlatAffineCriticalStage.massBound (FermatCriticalHomogenization.polynomial d.low d.leading d.degree) U (count m B*2^G) :=
  (CoordinatePowerSubstitution.mass_le _ _).trans
    (FlatAffineCriticalStage.mass_le _ d.frozen _ _ U _ ha (historyHeights_mass F d.heights G hH) j)

theorem criticalStep_row_mass (F : Sampler S (2^B) m ι) (d : CriticalData F.scalarPrefix n)
    (old U G : ℕ) (ho : ∀i,MvMass.mass (F.rows i)≤old)
    (ha : ∀j i,(PhysicalPowerCriticalRows.coordinateNormals d.objective d.scales d.free j i).natAbs≤U)
    (hH : ∀i r,(Algebra.leftMulMatrix F.scalarPrefix.basis.finBasis (d.heights i) r (zeroFin m B)).natAbs≤2^G)
    (j : ι⊕Variables (n+1)) :
    MvMass.mass ((criticalStep F d).rows j)≤max old
      (FlatAffineCriticalStage.massBound (FermatCriticalHomogenization.polynomial d.low d.leading d.degree) U (count m B*2^G)) := by
  cases j with
  | inl i => exact (criticalStep_old_row_mass F d i).trans ((ho i).trans (Nat.le_max_left _ _))
  | inr j => exact (criticalStep_new_row_mass F d U G ha hH j).trans (Nat.le_max_right _ _)

theorem scalarStep_head_row_mass (F : Sampler S (2^B) m ι) (hm : m≤S)
    (p : Polynomial F.scalarPrefix.carrier) (d G : ℕ)
    (hM : ∀r s,(Algebra.leftMulMatrix
      (PaddedIntegralParameterExtension.coordinateBasis F.scalarPrefix.basis p d).finBasis
      (AdjoinRoot.root _) r s).natAbs≤2^G) :
    MvMass.mass ((scalarStep F hm (Nat.two_pow_pos B) p d).rows (Sum.inr ()))≤
      2^PaddedIntegralParameterExtension.rowMassHeight m B G :=
  (MvMass.rename_le (CanonicalIntegralScalarAppend.layout F.scalar) _).trans
    (PaddedIntegralParameterExtension.equation_row_mass F.scalarPrefix.basis p d G
      (weights S (2^B) m) (birth S (2^B) m) hM)

theorem scalarStep_old_row_mass (F : Sampler S (2^B) m ι) (hm : m≤S)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) (i : ι) :
    MvMass.mass ((scalarStep F hm (Nat.two_pow_pos B) p d).rows (Sum.inl i))≤MvMass.mass (F.rows i) :=
  MvMass.rename_le Sum.inl _

theorem scalarStep_row_mass (F : Sampler S (2^B) m ι) (hm : m≤S)
    (p : Polynomial F.scalarPrefix.carrier) (d old G : ℕ)
    (ho : ∀i,MvMass.mass (F.rows i)≤old)
    (hM : ∀r s,(Algebra.leftMulMatrix
      (PaddedIntegralParameterExtension.coordinateBasis F.scalarPrefix.basis p d).finBasis
      (AdjoinRoot.root _) r s).natAbs≤2^G) (j : ι⊕Unit) :
    MvMass.mass ((scalarStep F hm (Nat.two_pow_pos B) p d).rows j)≤
      max old (2^PaddedIntegralParameterExtension.rowMassHeight m B G) := by
  cases j with
  | inl i => exact (scalarStep_old_row_mass F hm p d i).trans ((ho i).trans (Nat.le_max_left _ _))
  | inr u => cases u; exact (scalarStep_head_row_mass F hm p d G hM).trans (Nat.le_max_right _ _)

end LeanCanny.Algebra.IntegralHistorySampler
