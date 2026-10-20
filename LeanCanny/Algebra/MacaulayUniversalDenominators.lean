/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalSystem
public import LeanCanny.Algebra.GroupedDenominatorCancellation

/-! # Normalized universal extraneous denominators have no common factor

The extraneous determinant for an ordering omits the coefficient group of
the last input. Simultaneously permuting inputs and spatial variables lets
every original input be last, while preserving the common power
specialization. Hence any common divisor of these explicit universal
denominators is a unit. Quotient comparison between orderings remains a
separate requirement for applying the polynomial cancellation criterion.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

abbrev WithoutGroup (n : ℕ) (g : Fin n) := {v : CoefficientIndex n // v.1 ≠ g}

noncomputable def restrictGroup (g : Fin n) : CoefficientRing n R →+* MvPolynomial (WithoutGroup n g) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => if h : v.1 ≠ g then MvPolynomial.X ⟨v, h⟩ else 0)

noncomputable def eraseGroup (g : Fin n) : CoefficientRing n R →+* CoefficientRing n R :=
  (MvPolynomial.rename (Subtype.val : WithoutGroup n g → CoefficientIndex n)).toRingHom.comp (restrictGroup g)

theorem eraseGroup_X (g : Fin n) (v : CoefficientIndex n) (hv : v.1 ≠ g) :
    eraseGroup (R := R) g (MvPolynomial.X v) = MvPolynomial.X v := by
  rw [eraseGroup, RingHom.comp_apply]
  change MvPolynomial.rename (Subtype.val : WithoutGroup n g → CoefficientIndex n)
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun v => if h : v.1 ≠ g then MvPolynomial.X ⟨v, h⟩ else 0) (MvPolynomial.X v)) = _
  rw [MvPolynomial.eval₂Hom_X', dite_eq_left hv, MvPolynomial.rename_X]

theorem mem_vars_eraseGroup (g : Fin n) (p : CoefficientRing n R) (v : CoefficientIndex n)
    (hv : v ∈ (eraseGroup g p).vars) : v.1 ≠ g := by
  change v ∈ (MvPolynomial.rename (Subtype.val : WithoutGroup n g → CoefficientIndex n) (restrictGroup g p)).vars at hv
  obtain ⟨w, _, hw⟩ := MvPolynomial.mem_vars_rename _ _ hv
  rw [← hw]
  exact w.property

theorem system_map_eraseGroup (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i g : Fin n)
    (hi : π i ≠ g) : (system (R := R) d W π i).map (eraseGroup g) = system (R := R) d W π i := by
  rw [system, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · rw [MvPolynomial.map_monomial, eraseGroup_X _ _ hi]
  · exact map_zero _

noncomputable def denominator (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) : CoefficientRing n R :=
  (Macaulay.extraneousMinor (system (R := R) d W π) (d ∘ π) W).det

theorem denominator_eraseGroup (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (last : Fin n) (hlast : ∀ j, j ≤ last) :
    eraseGroup (R := R) (π last) (denominator (R := R) d W π) = denominator (R := R) d W π := by
  rw [denominator, Macaulay.det_extraneousMinor_map]
  apply congrArg Matrix.det
  apply Macaulay.extraneousMinor_eq_off_last _ _ _ _ last hlast
  intro i hi
  exact system_map_eraseGroup d W π i (π last) (π.injective.ne hi)

theorem denominator_omits_last (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (last : Fin n) (hlast : ∀ j, j ≤ last) (v : CoefficientIndex n)
    (hv : v ∈ (denominator (R := R) d W π).vars) : v.1 ≠ π last := by
  have he := denominator_eraseGroup (R := R) d W π last hlast
  rw [← he] at hv
  exact mem_vars_eraseGroup _ _ _ hv

theorem denominator_power_specialization (d : Fin n → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (π : Equiv.Perm (Fin n)) : MvPolynomial.eval (powerPoint (R := R) d) (denominator (R := R) d W π) = 1 := by
  rw [denominator, Macaulay.det_extraneousMinor_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.eval (powerPoint (R := R) d))) =
      Macaulay.powers (R := R) (d ∘ π) := by
    funext i
    exact system_power_specialization d W hW π i
  rw [hs, ← Macaulay.extraneousPadded_det, Macaulay.extraneousPadded_powers, Matrix.det_one]

noncomputable def orderingFor (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) := Equiv.swap (Fin.last n) i

noncomputable def denominatorFamily (d : Fin (n + 1) → ℕ) (W : ℕ) (i : Fin (n + 1)) :
    CoefficientRing (n + 1) R := denominator d W (orderingFor i)

theorem denominatorFamily_omits (d : Fin (n + 1) → ℕ) (W : ℕ) (i : Fin (n + 1)) (v : CoefficientIndex (n + 1))
    (hv : v ∈ (denominatorFamily (R := R) d W i).vars) : v.1 ≠ i := by
  have h := denominator_omits_last (R := R) d W (orderingFor i) (Fin.last n) Fin.le_last v hv
  simpa only [orderingFor, Equiv.swap_apply_left] using h

theorem denominatorFamily_power_specialization (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (i : Fin (n + 1)) :
    MvPolynomial.eval (powerPoint (R := R) d) (denominatorFamily (R := R) d W i) = 1 :=
  denominator_power_specialization d W hW (orderingFor i)

theorem denominatorFamily_common_divisor_isUnit [IsDomain R] (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hW : ∀ i, d i < 2 ^ W) (g : CoefficientRing (n + 1) R)
    (hg : ∀ i, g ∣ denominatorFamily (R := R) d W i) : IsUnit g :=
  GroupedPolynomialDivisors.isUnit_common_divisor Prod.fst (denominatorFamily (R := R) d W)
    (denominatorFamily_omits d W) (powerPoint d) (denominatorFamily_power_specialization d W hW) g hg

theorem exists_quotient_of_comparisons [IsDomain R] [UniqueFactorizationMonoid R]
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (a : Fin (n + 1) → CoefficientRing (n + 1) R)
    (hcross : ∀ i j, a i * denominatorFamily d W j = a j * denominatorFamily d W i) :
    ∃ q : CoefficientRing (n + 1) R, ∀ i, a i = denominatorFamily d W i * q :=
  GroupedDenominatorCancellation.exists_polynomial_quotient Prod.fst a (denominatorFamily d W)
    (denominatorFamily_omits d W) (powerPoint d) (denominatorFamily_power_specialization d W hW) hcross

noncomputable def numerator (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) : CoefficientRing n R :=
  (Macaulay.activeMinor (system (R := R) d W π) (d ∘ π) W).det

noncomputable def numeratorFamily (d : Fin (n + 1) → ℕ) (W : ℕ) (i : Fin (n + 1)) :
    CoefficientRing (n + 1) R := numerator d W (orderingFor i)

theorem numerator_power_specialization (d : Fin n → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (π : Equiv.Perm (Fin n)) : MvPolynomial.eval (powerPoint (R := R) d) (numerator (R := R) d W π) = 1 := by
  rw [numerator, Macaulay.det_activeMinor_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.eval (powerPoint (R := R) d))) =
      Macaulay.powers (R := R) (d ∘ π) := by
    funext i
    exact system_power_specialization d W hW π i
  rw [hs]
  have hm : Macaulay.activeMinor (Macaulay.powers (R := R) (d ∘ π)) (d ∘ π) W = 1 := by
    ext r s
    change Macaulay.matrix (Macaulay.powers (R := R) (d ∘ π)) (d ∘ π) W r.val s.val = _
    rw [Macaulay.matrix_powers]
    simp only [Matrix.one_apply, Subtype.val_injective.eq_iff]
  rw [hm, Matrix.det_one]

theorem denominatorFamily_ne_zero [Nontrivial R] (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hW : ∀ i, d i < 2 ^ W) (i : Fin (n + 1)) : denominatorFamily (R := R) d W i ≠ 0 := by
  intro hz
  have h := denominatorFamily_power_specialization (R := R) d W hW i
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem comparison_iff_unique_normalized_quotient [IsDomain R] [UniqueFactorizationMonoid R]
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W) :
    (∀ i j, numeratorFamily (R := R) d W i * denominatorFamily d W j =
      numeratorFamily d W j * denominatorFamily d W i) ↔
      ∃! q : CoefficientRing (n + 1) R,
        (∀ i, numeratorFamily d W i = denominatorFamily d W i * q) ∧
          MvPolynomial.eval (powerPoint (R := R) d) q = 1 := by
  constructor
  · intro hcross
    obtain ⟨q, hq⟩ := exists_quotient_of_comparisons d W hW (numeratorFamily (R := R) d W) hcross
    refine ⟨q, ⟨hq, ?_⟩, ?_⟩
    · have h := congrArg (MvPolynomial.eval (powerPoint (R := R) d)) (hq (Fin.last n))
      rw [numeratorFamily, numerator_power_specialization d W hW, map_mul,
        denominatorFamily_power_specialization d W hW, one_mul] at h
      exact h.symm
    · intro q' hq'
      apply mul_left_cancel₀ (denominatorFamily_ne_zero (R := R) d W hW (Fin.last n))
      exact (hq'.1 (Fin.last n)).symm.trans (hq (Fin.last n))
  · rintro ⟨q, ⟨hq, _⟩, _⟩ i j
    rw [hq i, hq j]
    ring

theorem divisibility_of_order_comparisons [IsDomain R] [UniqueFactorizationMonoid R]
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : ∀ i, d i < 2 ^ W)
    (hcross : ∀ i j, numeratorFamily (R := R) d W i * denominatorFamily d W j =
      numeratorFamily d W j * denominatorFamily d W i) :
    denominator (R := R) d W (Equiv.refl _) ∣ numerator (R := R) d W (Equiv.refl _) := by
  obtain ⟨q, ⟨hq, _⟩, _⟩ := (comparison_iff_unique_normalized_quotient (R := R) d W hW).mp hcross
  refine ⟨q, ?_⟩
  simpa only [numeratorFamily, denominatorFamily, orderingFor, Equiv.swap_self] using hq (Fin.last n)

end LeanCanny.Algebra.MacaulayUniversal
