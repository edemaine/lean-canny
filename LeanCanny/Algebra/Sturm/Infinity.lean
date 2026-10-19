/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison


Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/Sturm/Infinity.lean.
Changes: project namespace, real specialization, and a direct whole-line proof
without one-sided endpoint machinery. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.Sturm.Tarski
public import LeanCanny.Algebra.Sturm.EvalInfinity

/-! # Whole-line Sturm–Tarski from leading coefficients and degree parity

The finite-interval theorem applies beyond every chain root on both sides.
Only real coefficients are needed here; finite endpoints at roots and abstract
real closed fields are deliberately outside this proof slice.
-/

public section


namespace LeanCanny.Algebra.Sturm

open Polynomial

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- Sign variations at positive infinity. -/
noncomputable def signVariationsAtTop (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map Polynomial.leadingCoeff)

/-- Unfold positive-infinity variations as variations of the leading coefficients. -/
theorem signVariationsAtTop_def (cs : List (Polynomial R)) :
    signVariationsAtTop cs = List.signVariations (cs.map Polynomial.leadingCoeff) := (rfl)

@[simp, grind =]
theorem signVariationsAtTop_nil : signVariationsAtTop ([] : List R[X]) = 0 := by
  simp [signVariationsAtTop_def]

@[simp, grind =]
theorem signVariationsAtTop_singleton (p : R[X]) : signVariationsAtTop [p] = 0 := by
  simp [signVariationsAtTop_def]

/-- Matching the leading-coefficient signs realizes positive-infinity variations. -/
theorem signVariationsAt_eq_atTop {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff) :
    signVariationsAt cs x = signVariationsAtTop cs := by
  rw [signVariationsAt_def, signVariationsAtTop_def]
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left h

end Semiring

section Ring

variable {R : Type*} [Ring R] [LinearOrder R]

/-- Sign variations at negative infinity. -/
noncomputable def signVariationsAtBot (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree))

/-- Unfold negative-infinity variations using leading coefficients and degree parity. -/
theorem signVariationsAtBot_def (cs : List (Polynomial R)) :
    signVariationsAtBot cs =
      List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree)) := (rfl)

@[simp, grind =]
theorem signVariationsAtBot_nil : signVariationsAtBot ([] : List R[X]) = 0 := by
  simp [signVariationsAtBot_def]

@[simp, grind =]
theorem signVariationsAtBot_singleton (p : R[X]) : signVariationsAtBot [p] = 0 := by
  simp [signVariationsAtBot_def]

/-- Matching the parity-adjusted leading signs realizes negative-infinity variations. -/
theorem signVariationsAt_eq_atBot {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs,
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree)) :
    signVariationsAt cs x = signVariationsAtBot cs := by
  rw [signVariationsAt_def, signVariationsAtBot_def]
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left h

end Ring

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The variation count stabilizes at positive infinity, even for lists containing zero. -/
theorem exists_signVariationsAtTop (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs := by
  obtain ⟨B, hB⟩ := exists_signs_atTop cs
  exact ⟨B, fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)⟩

/-- The variation count stabilizes at negative infinity, even for lists containing zero. -/
theorem exists_signVariationsAtBot (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs := by
  obtain ⟨B, hB⟩ := exists_signs_atBot cs
  exact ⟨B, fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)⟩

/-- Far enough to the right, finite evaluation realizes the infinity signs and
lies beyond every chain root. The bound belongs to the ordered field itself. -/
theorem exists_atTop (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → r ≤ B := by
  obtain ⟨B, hB⟩ := exists_signs_atTop cs
  refine ⟨B, ?_, ?_⟩
  · exact fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)
  · intro p hp r hr
    by_contra! hBr
    have hs := hB p hp r hBr
    rw [hr, sign_zero] at hs
    exact leadingCoeff_ne_zero.mpr (hne p hp) (sign_eq_zero_iff.mp hs.symm)

/-- Far enough to the left, finite evaluation realizes the negative-infinity
variations, and every chain root lies above the bound. -/
theorem exists_atBot (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → B ≤ r := by
  obtain ⟨B, hB⟩ := exists_signs_atBot cs
  refine ⟨B, ?_, ?_⟩
  · exact fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)
  · intro p hp r hr
    by_contra! hrB
    have hs := hB p hp r hrB
    rw [hr, sign_zero] at hs
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr (hne p hp))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sign_eq_zero_iff.mp hs.symm)




/-- Sturm–Tarski on the whole real line for a positively scaled remainder chain. -/
theorem sum_sign_univ {p f : ℝ[X]} {cs : List ℝ[X]}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0)) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsAtTop (p :: cs) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨A, hA, hRA⟩ := exists_atBot _ h.nonzero
  obtain ⟨B, hB, hRB⟩ := exists_atTop _ h.nonzero
  let a := min A B - 1
  let b := max A B + 1
  have haA : a < A := (sub_one_lt _).trans_le (min_le_left _ _)
  have hBb : B < b := (le_max_right _ _).trans_lt (lt_add_one _)
  have hab : a < b := haA.trans_le ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have ha : p.eval a ≠ 0 := fun hz => (hRA p (by simp) a hz).not_gt haA
  have hb : p.eval b ≠ 0 := fun hz => (hRB p (by simp) b hz).not_gt hBb
  have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset := by
    apply Finset.filter_true_of_mem
    intro r hr
    have hz := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    exact ⟨haA.trans_le (hRA p (by simp) r hz), (hRB p (by simp) r hz).trans_lt hBb⟩
  have ht := sum_sign h hseed hab ha hb
  rwa [hA a haA, hB b hBb, hf] at ht

/-- The signed-remainder formula computes each Tarski query, even for repeated roots.
The zero head gives zero on both sides by the polynomial-root convention. -/
theorem sum_sign_sturmSeq_univ (p f : ℝ[X]) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_univ hsigned hseed

/-- Leading-coefficient variations count all distinct real roots. -/
theorem card_roots_toFinset_univ (p : ℝ[X]) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) = p.roots.toFinset.card := by
  simpa using sum_sign_sturmSeq_univ p 1

end LeanCanny.Algebra.Sturm
