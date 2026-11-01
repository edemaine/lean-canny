/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedRelativeCuts
public import LeanCanny.Algebra.IntegralRelativeNormalizationMatrix
public import LeanCanny.Algebra.IntegralScalarGeneratorOrigin
public import LeanCanny.Algebra.PaddedIntegralGeneratorSource

/-! # Actual old-prefix matrix stages for relative cut births

A cut's coefficient requests address its literal relative polynomial over
the creating prefix. Truncation is an explicit index guard. The integer
leading and inverse stages use the original selected coefficient matrix,
and the resulting companion is the actual new retained generator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutMatrix
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open IntegralRelativeNormalizationMatrix IntegralRelativeLeadingNormalization
open FixedWidthPolynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def raw (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ) :=
  IntegralRelativeTruncation.truncate (factor x hm r c) d

noncomputable def coefficientMatrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (k : ℕ) :=
  Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis ((factor x hm r c).coeff k)

theorem raw_coefficient_matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d k : ℕ) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis ((raw x hm r c d).coeff k) =
      if k ≤ d then coefficientMatrix x hm r c k else 0 := by
  rw [raw, IntegralRelativeTruncation.coefficient]
  split_ifs <;> simp only [map_zero, coefficientMatrix]

theorem top_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d : ℕ) :
    top x.sampler.scalarPrefix.basis.finBasis (raw x hm r c d) d = coefficientMatrix x hm r c d := by
  exact raw_coefficient_matrix x hm r c d d |>.trans (ite_eq_left (Nat.le_refl d))

theorem leading_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d : ℕ) :
    normalizedScalarLeading x (raw x hm r c d) d =
      IntegralParameterInverse.denominator (coefficientMatrix x hm r c d).charpoly := by
  exact congrArg (fun M => IntegralParameterInverse.denominator M.charpoly) (top_eq x hm r c d)

theorem normalized_coefficient_matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d k : ℕ) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((normalizedScalarPolynomial x (raw x hm r c d) d).coeff k) =
      if k = d then normalizedScalarLeading x (raw x hm r c d) d •
        (1 : Matrix (Fin (count m B)) (Fin (count m B)) ℤ)
      else if k ≤ d then
        Polynomial.aeval (coefficientMatrix x hm r c d)
          (IntegralParameterInverse.inverse (coefficientMatrix x hm r c d).charpoly) *
            coefficientMatrix x hm r c k
      else 0 := by
  rw [normalizedScalarPolynomial, matrix_eq]
  by_cases HD : k = d
  · rw [ite_eq_left HD, ite_eq_left HD]
    rfl
  · rw [ite_eq_right HD, ite_eq_right HD, raw_coefficient_matrix]
    unfold inverseMatrix
    rw [top_eq]
    split_ifs <;> simp only [mul_zero]

variable [Fintype ι]

noncomputable def origin (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d : ℕ) (hd : d ≤ 2 ^ B) :
    IntegralScalarRootHistoryBounds.GeneratorOrigin (step x hm r c d).sampler.scalarPrefix
      (step x hm r c d).bank 0 where
  birth := m
  order := by simp
  oldPrefix := x.sampler.scalarPrefix
  birth_bound := hm
  polynomial := normalizedScalarPolynomial x (raw x hm r c d) d
  degree := d
  degree_bound := hd
  leading := normalizedScalarLeading x (raw x hm r c d) d
  leading_eq := IntegralRelativeLeadingNormalization.coefficient _ _ _
  leading_ne_zero := IntegralRelativeLeadingNormalization.denominator_ne_zero _ _
  chain := .refl _
  generator_eq := rfl
  denominator_eq := rfl

theorem origin_earlier (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d : ℕ) (hd : d ≤ 2 ^ B) :
    (origin x hm r c d hd).birth < m + 1 := Nat.lt_succ_self m

end LeanCanny.Algebra.IntegralMixedCutMatrix
