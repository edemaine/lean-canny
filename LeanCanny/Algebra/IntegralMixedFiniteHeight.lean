/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedBankCanonical
public import LeanCanny.Algebra.CommonHeightResidueFP

/-! # The actual finite height/midpoint matrix fragment

Coordinate height records use twice one retained value; midpoint records
use the sum of two retained values. Their common-cleared matrix entries
use at most two actual old generators and complementary denominator
residues. Invalid scalar references contribute zero. Integer constants
use the complete common denominator and an identity entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFiniteHeight
open IntegralMixedHistory FixedWidthPolynomial
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

inductive Level where
  | constant (value : ℤ)
  | height (reference : ℕ)
  | midpoint (left right : ℕ)

def Level.expression : Level → AffineExpr
  | .constant c => .constant c
  | .height i => .scale 2 (.reference i)
  | .midpoint i j => .add (.reference i) (.reference j)

noncomputable def cofactor (x : State P S B m ι) (i : ℕ) : ℤ :=
  ∏ j : Fin m, if j.val = i then 1 else x.bank.denominator j

noncomputable def generator (x : State P S B m ι) (i : ℕ) (r t : Fin (count m B)) : ℤ :=
  if hi : i < m then Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
    (x.sampler.scalarPrefix.basis.generator ⟨i, hi⟩) r t else 0

theorem cofactor_erase (x : State P S B m ι) (i : Fin m) :
    cofactor x i.val = CommonIntegerDenominator.denominator (Finset.univ.erase i) x.bank.denominator := by
  unfold cofactor CommonIntegerDenominator.denominator
  simp only [Fin.val_inj]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

theorem reference_entry (x : State P S B m ι) (H : Canonical x) (i : ℕ) (r t : Fin (count m B)) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (expression x (.reference i)) r t =
      cofactor x i * generator x i r t := by
  by_cases hi : i < m
  · rw [expression, dite_eq_left hi]
    change Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (x.bank.numerator ⟨i, hi⟩ *
        (CommonIntegerDenominator.denominator (Finset.univ.erase ⟨i, hi⟩) x.bank.denominator : x.sampler.scalarPrefix.carrier)) r t = _
    rw [CommonHeightBits.numerator_matrix, H, ← cofactor_erase]
    rw [generator, dite_eq_left hi]
  · rw [expression, dite_eq_right hi, map_zero, Matrix.zero_apply, generator, dite_eq_right hi, mul_zero]

noncomputable def Level.entry (x : State P S B m ι) (r t : Fin (count m B)) : Level → ℤ
  | .constant c => commonDenominator x * c * (if r = t then 1 else 0)
  | .height i => 2 * (cofactor x i * generator x i r t)
  | .midpoint i j => cofactor x i * generator x i r t + cofactor x j * generator x j r t

theorem matrix (x : State P S B m ι) (H : Canonical x) (l : Level) (r t : Fin (count m B)) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (expression x l.expression) r t = l.entry x r t := by
  cases l with
  | constant c =>
    change Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((commonDenominator x : x.sampler.scalarPrefix.carrier) * (c : x.sampler.scalarPrefix.carrier)) r t =
        commonDenominator x * c * (if r = t then 1 else 0)
    rw [← Int.cast_mul, map_intCast, Matrix.intCast_apply]
    split_ifs <;> simp only [mul_one, mul_zero] <;> rfl
  | height i =>
    change Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (((2 : ℤ) : x.sampler.scalarPrefix.carrier) * expression x (.reference i)) r t =
        2 * (cofactor x i * generator x i r t)
    have HE := CommonHeightBits.numerator_matrix x.sampler.scalarPrefix.basis.finBasis
      (expression x (.reference i)) 2 r t
    rw [mul_comm] at HE
    rw [HE, reference_entry x H]
  | midpoint i j =>
    change Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (expression x (.reference i) + expression x (.reference j)) r t = _
    rw [map_add, Matrix.add_apply, reference_entry x H, reference_entry x H]
    rfl

end LeanCanny.Algebra.IntegralMixedFiniteHeight
