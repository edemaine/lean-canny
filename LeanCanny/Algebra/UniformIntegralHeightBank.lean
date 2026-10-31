/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonIntegerDenominatorBounds
public import LeanCanny.Algebra.PaddedIntegralHeightBounds

/-! # A bank of actual canonical heights in a scalar prefix

Extending the bank prepends the constructed numerator and denominator of
the new scalar and embeds every earlier numerator. Entry bounds apply to
the actual prefix bases, including singular selected leading matrices.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m : ℕ}

structure HeightBank (P : Prefix S (2 ^ B) m) where
  numerator : Fin m → P.carrier
  denominator : Fin m → ℤ

structure HeightBank.Bounds {P : Prefix S (2 ^ B) m} (H : HeightBank P) (V : ℕ) : Prop where
  numerator : ∀ i r t, (Algebra.leftMulMatrix P.basis.finBasis (H.numerator i) r t).natAbs ≤ 2 ^ V
  denominator : ∀ i, (H.denominator i).natAbs ≤ 2 ^ V

noncomputable def HeightBank.base (S B : ℕ) : HeightBank (base S (2 ^ B)) where
  numerator := Fin.elim0
  denominator := Fin.elim0

theorem HeightBank.base_bounds (S B V : ℕ) : (HeightBank.base S B).Bounds V where
  numerator i := Fin.elim0 i
  denominator i := Fin.elim0 i

noncomputable def HeightBank.step {P : Prefix S (2 ^ B) m} (H : HeightBank P)
    (hm : m ≤ S) (p : Polynomial P.carrier) (d : ℕ) : HeightBank (step P hm (Nat.two_pow_pos B) p d) where
  numerator := Fin.cons (PaddedIntegralParameterExtension.numerator P.basis p d)
    (fun i => AdjoinRoot.of _ (H.numerator i))
  denominator := Fin.cons (PaddedIntegralParameterExtension.denominator P.basis p d) H.denominator

def bankStepHeight (R N C : ℕ) : ℕ :=
  PaddedIntegralParameterExtension.numeratorHeight R N C + CharacteristicIntegerBounds.budget R C + 1

def bankFactor (R N : ℕ) : ℕ := 2 * (N + 2 * R + 3) ^ 2

theorem bankStepHeight_linear (R N C : ℕ) : bankStepHeight R N C ≤ bankFactor R N * (C + 1) := by
  have HD : CharacteristicIntegerBounds.budget R C ≤ PaddedIntegralParameterExtension.numeratorHeight R N C := by
    unfold PaddedIntegralParameterExtension.numeratorHeight IntegralInverseMatrixBounds.height
      IntegralInverseMatrixBounds.polynomialHeight
    omega
  have HL := PaddedIntegralParameterExtension.numeratorHeight_linear R N C
  unfold bankStepHeight bankFactor
  nlinarith

theorem bankFactor_binary {R N : List Bool → ℕ} (hR : BinaryFn R) (hN : BinaryFn N) :
    BinaryFn (fun c => bankFactor (R c) (N c)) :=
  by
    have HF : BinaryFn (fun c => N c + 2 * R c + 3) :=
      (hN.add ((BinaryFn.const 2).mul hR)).add (BinaryFn.const 3)
    exact ((BinaryFn.const 2).mul (HF.mul HF)).of_eq (fun c => by simp only [bankFactor, pow_two])

theorem HeightBank.Bounds.mono {P : Prefix S (2 ^ B) m} {H : HeightBank P} {V W : ℕ}
    (h : H.Bounds V) (hVW : V ≤ W) : H.Bounds W where
  numerator i r t := (h.numerator i r t).trans (Nat.pow_le_pow_right (by decide) hVW)
  denominator i := (h.denominator i).trans (Nat.pow_le_pow_right (by decide) hVW)

theorem HeightBank.step_bounds {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d C V : ℕ) (hH : H.Bounds V)
    (hp : ∀ k r t, (Algebra.leftMulMatrix P.basis.finBasis (p.coeff k) r t).natAbs ≤ 2 ^ C) :
    (H.step hm p d).Bounds (max V (bankStepHeight (count m B) (2 ^ B) C)) := by
  have HN : PaddedIntegralParameterExtension.numeratorHeight (count m B) (2 ^ B) C ≤
      max V (bankStepHeight (count m B) (2 ^ B) C) :=
    (by unfold bankStepHeight; omega)
  have HD : CharacteristicIntegerBounds.budget (count m B) C ≤
      max V (bankStepHeight (count m B) (2 ^ B) C) :=
    (by unfold bankStepHeight; omega)
  constructor
  · intro i r t
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (PaddedIntegralParameterExtension.numerator_height P.basis p d C hp r t).trans
        (Nat.pow_le_pow_right (by decide) HN)
    · obtain ⟨⟨r', a⟩, rfl⟩ := (IntegralCoordinateBasis.pairIndex m B).surjective r
      obtain ⟨⟨t', b⟩, rfl⟩ := (IntegralCoordinateBasis.pairIndex m B).surjective t
      change (Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis P.basis p d).finBasis
        (AdjoinRoot.of _ (H.numerator j)) _ _).natAbs ≤ _
      rw [PaddedIntegralParameterExtension.coordinateBasis, IntegralCoordinateBasis.finBasis_of_matrix]
      split_ifs
      · exact (hH.numerator j r' t').trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      · exact Nat.zero_le _
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (PaddedIntegralParameterExtension.denominator_height P.basis p d C (hp d)).trans
        (Nat.pow_le_pow_right (by decide) HD)
    · exact (hH.denominator j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))

theorem bankFactor_mono {R T N : ℕ} (h : R ≤ T) : bankFactor R N ≤ bankFactor T N := by
  unfold bankFactor
  gcongr

def bankGrowth (R N K : ℕ) : ℕ := bankFactor R N * (K + 1) + 1

theorem bankGrowth_pos (R N K : ℕ) : 1 ≤ bankGrowth R N K := by unfold bankGrowth; omega

theorem bankGrowth_binary {R N K : List Bool → ℕ} (hR : BinaryFn R) (hN : BinaryFn N) (hK : BinaryFn K) :
    BinaryFn (fun c => bankGrowth (R c) (N c) (K c)) :=
  ((bankFactor_binary hR hN).mul (hK.add (BinaryFn.const 1))).add (BinaryFn.const 1)

theorem HeightBank.step_scaled_bounds {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d C V R K : ℕ) (hH : H.Bounds V) (hV : 1 ≤ V)
    (hR : count m B ≤ R) (hC : C ≤ K * V)
    (hp : ∀ k r t, (Algebra.leftMulMatrix P.basis.finBasis (p.coeff k) r t).natAbs ≤ 2 ^ C) :
    (H.step hm p d).Bounds (bankGrowth R (2 ^ B) K * V) := by
  apply (H.step_bounds hm p d C V hH hp).mono
  apply max_le
  · simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (bankGrowth_pos R (2 ^ B) K)
  · have HC : C + 1 ≤ (K + 1) * V := by nlinarith
    calc
      _ ≤ bankFactor (count m B) (2 ^ B) * (C + 1) := bankStepHeight_linear _ _ _
      _ ≤ bankFactor R (2 ^ B) * ((K + 1) * V) := Nat.mul_le_mul (bankFactor_mono hR) HC
      _ ≤ bankGrowth R (2 ^ B) K * V := by unfold bankGrowth; nlinarith

end LeanCanny.Algebra.UniformIntegralPrefix
