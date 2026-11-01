/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueTrailing
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar
public import LeanCanny.Algebra.IntegralRelativeTruncation

/-! # All three actual relative exceptional cut births

Tagged coordinate-trailing, selected squarefree and equation-value-trailing
cuts are literal polynomials over the CURRENT retained algebra. Validity
is their exact selected-component coefficient-zero semantics. Every real
root of every valid cut is adjoined without a physical critical point,
using one initial original-source scalar-degree cap and exact truncation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedExceptionalBounds UniformIntegralPowerSchedule Polynomial
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

inductive Kind (P : SpatialSource n) (r : Rule n) where
  | coordinate (j : Fin (n - r.critical.offset.val + 1)) (index : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r))
  | squarefree (j : Fin (n - r.critical.offset.val + 1)) (index : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
  | value (row : Fin (n - r.critical.offset.val + 1)) (index : Fin (IntegralMixedValueTrailing.ChoiceBound P r))

def Valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : Kind P r → Prop
  | .coordinate j k => IntegralMixedCoordinateTrailing.Valid x hm r j φ k
  | .squarefree j k => IntegralMixedCoordinateSquarefree.Valid x hm r j φ k
  | .value i k => IntegralMixedValueTrailing.Valid x hm r i φ k

noncomputable def factor (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : Kind P r → Polynomial x.sampler.scalarPrefix.carrier
  | .coordinate j k => IntegralMixedCoordinateTrailing.factor x hm r j k
  | .squarefree j k => IntegralMixedCoordinateSquarefree.exceptional x hm r j k
  | .value i k => IntegralMixedValueTrailing.factor x hm r i k

theorem selected_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Kind P r) (hc : Valid x hm r φ c) :
    (factor x hm r c).map φ.toRingHom ≠ 0 := by
  cases c with
  | coordinate _ _ => exact hc.2
  | squarefree j k => exact IntegralMixedCoordinateSquarefree.exceptional_nonzero x hm r j φ k hc
  | value _ _ => exact hc.2

theorem factor_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) :
    (factor x hm r c).natDegree ≤ auxiliaryCap (n + 1) P.degree := by
  have HE : E (n + 1) P.degree ≤ auxiliaryCap (n + 1) P.degree := by unfold auxiliaryCap; omega
  have HR : regularCap (n + 1) P.degree ≤ auxiliaryCap (n + 1) P.degree := by unfold auxiliaryCap; omega
  have HV : valueCap (n + 1) P.degree ≤ auxiliaryCap (n + 1) P.degree := by unfold auxiliaryCap; omega
  cases c with
  | coordinate j k => exact (IntegralMixedSweepBounds.factor_degree x hm r j k).trans HE
  | value i k => exact (IntegralMixedValueTrailing.factor_degree x hm r i k).trans HV
  | squarefree j k =>
    have HK := coordinateCap_le P.degree r
    have Hη := IntegralMixedSweepBounds.parameterDegree_le P.degree r
    have HC := (IntegralMixedSquarefreeBounds.exceptional_degree x hm r j k).trans
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 HK) 1) Hη)
    have HM : (2 * K (n + 1) P.degree + 1) * E (n + 1) P.degree ≤ regularCap (n + 1) P.degree := by
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact HC.trans (HM.trans HR)

theorem finite_cuts (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Kind P r) (hc : Valid x hm r φ c) :
    {t : ℝ | (factor x hm r c).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using Polynomial.finite_setOfPred_isRoot (selected_nonzero x hm r φ c hc)

structure Choices (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) where
  coordinateIndex : Fin (n - r.critical.offset.val + 1) → Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)
  coordinateValid : ∀ j, IntegralMixedCoordinateTrailing.Valid x hm r j φ (coordinateIndex j)
  squarefreeIndex : Fin (n - r.critical.offset.val + 1) → Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)
  squarefreeValid : ∀ j, IntegralMixedCoordinateSquarefree.Valid x hm r j φ (squarefreeIndex j)
  valueIndex : Fin (n - r.critical.offset.val + 1) → Fin (IntegralMixedValueTrailing.ChoiceBound P r)
  valueValid : ∀ i, IntegralMixedValueTrailing.Valid x hm r i φ (valueIndex i)

theorem exists_choices (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : Nonempty (Choices x hm r φ) := by
  choose a ha using (fun j => IntegralMixedCoordinateTrailing.exists_valid x hm r j φ)
  choose b hb using (fun j => IntegralMixedCoordinateSquarefree.exists_valid x hm r j φ)
  choose c hc using (fun i => IntegralMixedValueTrailing.exists_valid x hm r i φ)
  exact ⟨⟨a, ha, b, hb, c, hc⟩⟩

variable [Fintype ι]

noncomputable def step (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) (d : ℕ) :
    State P S B (m + 1) (ι ⊕ Unit) :=
  normalizedScalarStep x hm (IntegralRelativeTruncation.truncate (factor x hm r c) d) d

theorem real_extend (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Kind P r) (hc : Valid x hm r φ c)
    (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i) = z (x.sampler.scalar i) ^ weights S (2 ^ B) m i)
    (t : ℝ) (ht : (factor x hm r c).eval₂ φ.toRingHom t = 0) :
    ∃ d ≤ auxiliaryCap (n + 1) P.degree, ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ i, ((step x hm r c d).sampler.rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (step x hm r c d).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((step x hm r c d).sampler.scalarPrefix.basis.generator i) =
          y ((step x hm r c d).sampler.scalar i) ^ weights S (2 ^ B) (m + 1) i) →
        ψ ((step x hm r c d).bank.numerator 0) / ((step x hm r c d).bank.denominator 0 : ℝ) = t := by
  let p := factor x hm r c
  let d := (p.map φ.toRingHom).natDegree
  have HP : p.map φ.toRingHom ≠ 0 := selected_nonzero x hm r φ c hc
  have HD : d ≤ auxiliaryCap (n + 1) P.degree := Polynomial.natDegree_map_le.trans (factor_degree x hm r c)
  have Hroot : (p.map φ.toRingHom).eval₂ (RingHom.id ℝ) t = 0 := by
    rw [Polynomial.eval₂_id, Polynomial.eval_map]
    exact ht
  have Hpos : 1 ≤ d := Polynomial.natDegree_pos_of_eval₂_root HP (RingHom.id ℝ) Hroot (fun _ H => H)
  have HA : φ ((IntegralRelativeTruncation.truncate p d).coeff d) ≠ 0 := by
    rw [IntegralRelativeTruncation.coefficient, ite_eq_left (Nat.le_refl d)]
    have H := Polynomial.leadingCoeff_ne_zero.mpr HP
    rw [Polynomial.leadingCoeff, Polynomial.coeff_map] at H
    exact H
  have HT : (IntegralRelativeTruncation.truncate p d).eval₂ φ.toRingHom t = 0 :=
    (IntegralRelativeTruncation.eval_eq p d φ (Nat.le_refl d) t).trans ht
  exact ⟨d, HD, normalizedScalar_real_extend x hm (IntegralRelativeTruncation.truncate p d) d
    (IntegralRelativeTruncation.natDegree_le p d) Hpos (HD.trans hcap) z hz φ hφ HA t HT⟩

end LeanCanny.Algebra.IntegralMixedRelativeCuts
