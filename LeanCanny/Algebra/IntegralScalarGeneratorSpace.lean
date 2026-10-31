/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScalarNormalizationSpace
public import LeanCanny.Algebra.PaddedIntegralGeneratorFinSpace

/-! # Actual companion-root readers with an integer selected coefficient

The actual canonical generator matrix uses the scalar normalization
reader. Its shift and padding branches remain those of the general
padded construction. Only one original coefficient and one scalar leading
residue supply each nonzero normalization entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family extends PaddedIntegralGeneratorBits.Family where
  leading : (c : List Bool) → ZMod (modulus c)
  leading_eq : ∀ c, coefficient c (selectedDegree c) = leading c • 1

structure Access (F : Family) extends PaddedIntegralGeneratorBits.Access F.toFamily where
  leading : List Bool → List Bool
  leading_eq : ∀ c, leading c = residueBits (F.leading c)

noncomputable def normalizationFamily (F : Family) : IntegralScalarNormalizationBits.Family where
  toFamily := PaddedIntegralGeneratorBits.normalizationFamily F.toFamily
  leading := F.leading
  leading_eq := F.leading_eq

noncomputable def normalizationAccess (F : Family) (a : Access F) : IntegralScalarNormalizationBits.Access (normalizationFamily F) where
  toAccess := PaddedIntegralGeneratorBits.normalizationAccess F.toFamily a.toAccess
  leading := a.leading
  leading_eq := a.leading_eq

theorem evaluator (F : Family) (a : Access F) (EC : SpaceFunction a.entry) (EL : SpaceFunction a.leading) :
    SpaceFunction F.toFamily.value :=
  PaddedIntegralGeneratorBits.evaluator_with_normalization F.toFamily a.toAccess
    (IntegralScalarNormalizationBits.negative_evaluator (normalizationFamily F) (normalizationAccess F a) EC EL)

theorem scalar_matrix {A : Type*} [CommRing A] {M : ℕ} (b : Module.Basis (Fin M) ℤ A) (z : ℤ) (m : ℕ) :
    (Algebra.leftMulMatrix b (z : A)).map (Int.castRingHom (ZMod m)) = (z : ZMod m) • 1 := by
  ext i j
  rw [Matrix.map_apply, map_intCast, Matrix.intCast_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp [smul_eq_mul]

noncomputable def finFamily (F : PaddedIntegralGeneratorFinBits.Family) (z : List Bool → ℤ)
    (hz : ∀ c, letI := F.ring c; (F.polynomial c).coeff (F.degree c) = (z c : F.carrier c)) : Family where
  toFamily := PaddedIntegralGeneratorFinBits.rawFamily F
  leading c := (z c : ZMod (F.modulus c))
  leading_eq c := by
    let := F.ring c
    dsimp only [PaddedIntegralGeneratorFinBits.rawFamily, PaddedIntegralGeneratorFinBits.Family.coefficient]
    rw [hz c]
    exact scalar_matrix (F.basis c).finBasis (z c) (F.modulus c)

noncomputable def finAccess (F : PaddedIntegralGeneratorFinBits.Family) (a : PaddedIntegralGeneratorFinBits.Access F)
    (z : List Bool → ℤ) (hz : ∀ c, letI := F.ring c; (F.polynomial c).coeff (F.degree c) = (z c : F.carrier c))
    (leading : List Bool → List Bool) (hL : ∀ c, leading c = residueBits (z c : ZMod (F.modulus c))) :
    Access (finFamily F z hz) where
  toAccess := PaddedIntegralGeneratorFinBits.rawAccess F a
  leading := leading
  leading_eq := hL

theorem fin_evaluator (F : PaddedIntegralGeneratorFinBits.Family) (a : PaddedIntegralGeneratorFinBits.Access F)
    (z : List Bool → ℤ) (hz : ∀ c, letI := F.ring c; (F.polynomial c).coeff (F.degree c) = (z c : F.carrier c))
    (leading : List Bool → List Bool) (hL : ∀ c, leading c = residueBits (z c : ZMod (F.modulus c)))
    (EC : SpaceFunction a.entry) (EL : SpaceFunction leading) : SpaceFunction F.value :=
  (evaluator (finFamily F z hz) (finAccess F a z hz leading hL) EC EL).congr
    (PaddedIntegralGeneratorFinBits.value_eq F)

end LeanCanny.Algebra.IntegralScalarGeneratorBits
