/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralHeightBank
public import LeanCanny.Algebra.UniformIntegralPrefixRealExtension
public import LeanCanny.Algebra.IntegralHistoryRealExtension

/-! # Scalar-root height banks for integer selected leading coefficients

When the selected coefficient is an integer z, the actual new monic root
represents the desired height after division by z. Its multiplication
matrix is the constructed companion matrix. No inverse-polynomial value
is needed for this representation, even when z is a nonunit integer.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open IntegralCoordinateBasis FixedWidthPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m : ℕ}

noncomputable def HeightBank.rootStep {P : Prefix S (2 ^ B) m} (H : HeightBank P)
    (hm : m ≤ S) (p : Polynomial P.carrier) (d : ℕ) (z : ℤ) : HeightBank (UniformIntegralPrefix.step P hm (Nat.two_pow_pos B) p d) where
  numerator := Fin.cons (AdjoinRoot.root _) (fun i => AdjoinRoot.of _ (H.numerator i))
  denominator := Fin.cons z H.denominator

theorem HeightBank.rootStep_bounds {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d C V : ℕ) (z : ℤ) (hH : H.Bounds V)
    (hp : ∀ k r t, (Algebra.leftMulMatrix P.basis.finBasis (p.coeff k) r t).natAbs ≤ 2 ^ C)
    (hz : z.natAbs ≤ 2 ^ C) :
    (H.rootStep hm p d z).Bounds (max V (bankStepHeight (count m B) (2 ^ B) C)) := by
  have HR : 1 ≤ count m B := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
  have HC : C ≤ CharacteristicIntegerBounds.budget (count m B) C := by
    have HE := Nat.mul_le_mul_right (C + 1) HR
    unfold CharacteristicIntegerBounds.budget
    nlinarith
  have HN : PaddedIntegralParameterExtension.rootHeight (count m B) (2 ^ B) C ≤
      max V (bankStepHeight (count m B) (2 ^ B) C) := by
    unfold bankStepHeight PaddedIntegralParameterExtension.numeratorHeight
    omega
  have HZ : C ≤ max V (bankStepHeight (count m B) (2 ^ B) C) := by
    unfold bankStepHeight
    omega
  constructor
  · intro i r t
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (PaddedIntegralParameterExtension.root_height P.basis p d C hp r t).trans
        (Nat.pow_le_pow_right (by decide) HN)
    · obtain ⟨⟨r', a⟩, rfl⟩ := (pairIndex m B).surjective r
      obtain ⟨⟨t', b⟩, rfl⟩ := (pairIndex m B).surjective t
      change (Algebra.leftMulMatrix (PaddedIntegralParameterExtension.coordinateBasis P.basis p d).finBasis
        (AdjoinRoot.of _ (H.numerator j)) _ _).natAbs ≤ _
      rw [PaddedIntegralParameterExtension.coordinateBasis, finBasis_of_matrix]
      split_ifs
      · exact (hH.numerator j r' t').trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      · exact Nat.zero_le _
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hz.trans (Nat.pow_le_pow_right (by decide) HZ)
    · exact (hH.denominator j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))

theorem HeightBank.rootStep_scaled_bounds {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d C V R K : ℕ) (z : ℤ) (hH : H.Bounds V) (hV : 1 ≤ V)
    (hR : count m B ≤ R) (hC : C ≤ K * V)
    (hp : ∀ k r t, (Algebra.leftMulMatrix P.basis.finBasis (p.coeff k) r t).natAbs ≤ 2 ^ C)
    (hz : z.natAbs ≤ 2 ^ C) : (H.rootStep hm p d z).Bounds (bankGrowth R (2 ^ B) K * V) := by
  apply (H.rootStep_bounds hm p d C V z hH hp hz).mono
  apply max_le
  · simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (bankGrowth_pos R (2 ^ B) K)
  · have HC : C + 1 ≤ (K + 1) * V := by nlinarith
    calc
      _ ≤ bankFactor (count m B) (2 ^ B) * (C + 1) := bankStepHeight_linear _ _ _
      _ ≤ bankFactor R (2 ^ B) * ((K + 1) * V) := Nat.mul_le_mul (bankFactor_mono hR) HC
      _ ≤ bankGrowth R (2 ^ B) K * V := by unfold bankGrowth; nlinarith

theorem HeightBank.rootStep_denominator_ne_zero {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d : ℕ) (z : ℤ) (hz : z ≠ 0) (hH : ∀ i, H.denominator i ≠ 0)
    (i : Fin (m + 1)) : (H.rootStep hm p d z).denominator i ≠ 0 := by
  exact Fin.cases hz hH i

theorem HeightBank.rootStep_generators {P : Prefix S (2 ^ B) m} (H : HeightBank P) (hm : m ≤ S)
    (p : Polynomial P.carrier) (d : ℕ) (z : ℤ)
    (hH : ∀ i, H.numerator i = P.basis.generator i) (i : Fin (m + 1)) :
    (H.rootStep hm p d z).numerator i =
      (UniformIntegralPrefix.step P hm (Nat.two_pow_pos B) p d).basis.generator i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change AdjoinRoot.of _ (H.numerator j) = AdjoinRoot.of _ (P.basis.generator j)
    rw [hH j]

theorem real_extend_recover_root_integer {N : ℕ} (P : Prefix S N m) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial P.carrier) (d : ℕ) (hdN : d ≤ N) (z : ℤ) (hz0 : z ≠ 0) (hz : p.coeff d = (z : P.carrier))
    (x : Fin m → ℝ) (hx : ∀ i, (P.rows i).eval₂ (Int.castRingHom ℝ) x = 0)
    (φ : P.carrier →ₐ[ℤ] ℝ) (hφ : ∀ i, φ (P.basis.generator i) = x i ^ weights S N m i)
    (t : ℝ) (hd : (p.map φ.toRingHom).natDegree = d) (hdpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    ∃ y : Fin (m + 1) → ℝ,
      (∀ i, ((step P hm hN p d).rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y i.succ = x i) ∧
      ∀ ψ : (step P hm hN p d).carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((step P hm hN p d).basis.generator i) = y i ^ weights S N (m + 1) i) →
        ψ (AdjoinRoot.root _) / (z : ℝ) = t := by
  obtain ⟨y, hy, htail, hhead⟩ := real_extend_selected P hm hN p d hdN x hx φ hφ t hd hdpos ht
  refine ⟨y, hy, htail, ?_⟩
  intro ψ hψ
  have HI := hψ 0
  change ψ (AdjoinRoot.root _) = y 0 ^ weights S N (m + 1) 0 at HI
  rw [head, hhead, hz, map_intCast] at HI
  rw [HI]
  exact mul_div_cancel_left₀ t (Int.cast_ne_zero.mpr hz0)

end LeanCanny.Algebra.UniformIntegralPrefix

namespace LeanCanny.Algebra.IntegralHistorySampler
open UniformIntegralPowerSchedule
set_option backward.isDefEq.respectTransparency false
variable {S N m : ℕ} {ι : Type} [Fintype ι]

theorem scalarStep_real_extend_recover_root_integer (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) (hdN : d ≤ N)
    (s : ℤ) (hs0 : s ≠ 0) (hs : p.coeff d = (s : F.scalarPrefix.carrier))
    (z : ι → ℝ) (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i)
    (x : ℝ) (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (hx : p.eval₂ φ.toRingHom x = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((scalarStep F hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (scalarStep F hm hN p d).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((scalarStep F hm hN p d).scalarPrefix.basis.generator i) =
          y ((scalarStep F hm hN p d).scalar i) ^ weights S N (m + 1) i) →
        ψ (AdjoinRoot.root _) / (s : ℝ) = x := by
  obtain ⟨y, hy, htail, hhead⟩ := scalarStep_real_extend F hm hN p d z hz φ hφ (φ (p.coeff d) * x)
    (PaddedIntegralParameterExtension.equation_root F.scalarPrefix.basis p d hdN φ x hd hpos hx)
  refine ⟨y, hy, htail, ?_⟩
  intro ψ hψ
  have HI := hψ 0
  change ψ (AdjoinRoot.root _) = y (Sum.inr ()) ^ weights S N (m + 1) 0 at HI
  rw [head, hhead, hs, map_intCast] at HI
  rw [HI]
  exact mul_div_cancel_left₀ x (Int.cast_ne_zero.mpr hs0)

end LeanCanny.Algebra.IntegralHistorySampler
