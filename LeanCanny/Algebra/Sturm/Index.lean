/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The parity recurrence proof adapts TauCeti's
Algebra/Polynomial/Sturm/CauchyIndex/Sequence.lean at revision
034e577c895d28c058d92af4036f7ce0b03081cf.
Copyright (c) 2026 The Tau Ceti contributors. Authors: The Tau Ceti contributors.
Changes: define the index directly by coefficient variations, with no analytic
Cauchy-index API or real-closed-field assumption. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.SturmQuery
public import LeanCanny.Algebra.Sturm.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! # A coefficient-variation index and its Euclidean recurrence -/

@[expose] public section

namespace LeanCanny.Algebra.Sturm
open Polynomial

variable {K : Type*} [Field K] [LinearOrder K]

/-- The whole-line variation difference for an arbitrary signed remainder pair. -/
noncomputable def remainderIndex (p q : K[X]) : ℤ :=
  (signVariationsAtBot (sturmSeq p q) : ℤ) - signVariationsAtTop (sturmSeq p q)

@[simp] theorem remainderIndex_zero_left (q : K[X]) : remainderIndex 0 q = 0 := by
  simp [remainderIndex]

@[simp] theorem remainderIndex_zero_right (p : K[X]) : remainderIndex p 0 = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [remainderIndex, sturmSeq_zero_right, hp]

variable [IsStrictOrderedRing K]

/-- One signed Euclidean step contributes only when the two leading degrees
have opposite parity. This identity uses no root or Cauchy-index oracle. -/
theorem remainderIndex_recur {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    remainderIndex p q =
      (if Odd (p.natDegree + q.natDegree) then
        (SignType.sign p.leadingCoeff : ℤ) * SignType.sign q.leadingCoeff else 0) +
      remainderIndex q (-(p % q)) := by
  have hp' : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  rw [remainderIndex, remainderIndex, sturmSeq_cons hp, neg_mod, sturmSeq_cons hq]
  simp only [signVariationsAtTop_def, signVariationsAtBot_def, List.map_cons]
  rw [List.signVariations_cons_cons_of_ne_zero _ (by simpa using hp') (by simpa using hq'),
    List.signVariations_cons_cons_of_ne_zero _ hp' hq']
  simp only [sign_mul, sign_pow, Left.sign_neg, sign_one]
  rw [← ite_mul_neg_one_pow_sub_ite _ _ (sign_ne_zero.mpr hp') (sign_ne_zero.mpr hq')]
  push_cast
  ring

/-- Any valid Tarski seed computes the query, including a reduced derivative product. -/
theorem remainderIndex_tarskiSeed {p f q : ℝ[X]} (hseed : IsTarskiSeed p f q) :
    remainderIndex p q = RootSignQueries.tarskiQuery p f := by
  classical
  by_cases hp : p = 0
  · simp [hp, RootSignQueries.tarskiQuery, RootSignQueries.signSum]
  have hsigned := IsSignedRemainderSeq.sturmSeq p q
  have hseed' := hseed.sturmSeq
  unfold remainderIndex
  rw [sturmSeq_cons hp] at hsigned hseed' ⊢
  exact sum_sign_univ hsigned hseed'

end LeanCanny.Algebra.Sturm
