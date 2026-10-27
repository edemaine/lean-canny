/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ThomEncoding

/-! # Comparing real roots by streamed derivative signs

At the highest differing derivative, the common next derivative sign fixes
the orientation. An ascending scan retains only the latest comparison bit.
No complete Thom signature or numerical root approximation is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.ThomEncoding
open Polynomial
open scoped Classical

theorem tail_interval (p : ℝ[X]) (D : ℕ) (hD : p.natDegree ≤ D) (a b : ℝ) (hab : a ≤ b)
    (k : ℕ) (hs : ∀ j, k < j → sign p a j = sign p b j) :
    ∀ z ∈ Set.Icc a b, sign p z (k + 1) = sign p a (k + 1) := by
  let q := Polynomial.derivative^[k + 1] p
  have hq : q.natDegree ≤ D := (natDegree_iterate_derivative p _).trans ((Nat.sub_le _ _).trans hD)
  have he : ∀ j ≤ D, sign q a j = sign q b j := by
    intro j _
    simpa only [q, sign, ← Function.iterate_add_apply] using hs (j + (k + 1)) (by omega)
  intro z hz
  simpa only [q, sign, Function.iterate_zero_apply] using interval D q a b hq hab he z hz 0 (Nat.zero_le _)

private theorem highest_difference_of_le (p : ℝ[X]) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (hab : a ≤ b) (k : ℕ) (hne : sign p a k ≠ sign p b k)
    (hs : ∀ j, k < j → sign p a j = sign p b j) :
    (sign p a (k + 1) = .pos ∧ sign p a k < sign p b k) ∨
      (sign p a (k + 1) = .neg ∧ sign p b k < sign p a k) := by
  let q := Polynomial.derivative^[k] p
  have hda : SignType.sign (q.derivative.eval a) = sign p a (k + 1) := by
    simp only [q, sign, Function.iterate_succ_apply']
  have hd : ∀ z ∈ Set.Icc a b, SignType.sign (q.derivative.eval z) = SignType.sign (q.derivative.eval a) := by
    intro z hz
    simpa only [q, sign, Function.iterate_succ_apply'] using tail_interval p D hD a b hab k hs z hz
  have mono (hp : 0 ≤ q.derivative.eval a) : MonotoneOn q.eval (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) q.differentiable.continuous.continuousOn q.differentiableOn (by
      intro z hz
      rw [(q.hasDerivAt z).deriv]
      apply sign_nonneg_iff.mp
      rw [hd z (interior_subset hz)]
      exact sign_nonneg_iff.mpr hp)
  have anti (hn : q.derivative.eval a ≤ 0) : AntitoneOn q.eval (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) q.differentiable.continuous.continuousOn q.differentiableOn (by
      intro z hz
      rw [(q.hasDerivAt z).deriv]
      apply sign_nonpos_iff.mp
      rw [hd z (interior_subset hz)]
      exact sign_nonpos_iff.mpr hn)
  have hA : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hB : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  change SignType.sign (q.eval a) ≠ SignType.sign (q.eval b) at hne
  rcases lt_trichotomy 0 (q.derivative.eval a) with hp | hz | hn
  · exact Or.inl ⟨hda.symm.trans (sign_pos hp),
      lt_of_le_of_ne (SignType.sign.monotone (mono hp.le hA hB hab)) hne⟩
  · have he := le_antisymm (SignType.sign.monotone (mono (by linarith) hA hB hab))
      (SignType.sign.monotone (anti (by linarith) hA hB hab))
    exact (hne he).elim
  · exact Or.inr ⟨hda.symm.trans (sign_neg hn),
      lt_of_le_of_ne (SignType.sign.monotone (anti hn.le hA hB hab)) hne.symm⟩

theorem highest_difference_lt_iff (p : ℝ[X]) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (k : ℕ) (hne : sign p a k ≠ sign p b k)
    (hs : ∀ j, k < j → sign p a j = sign p b j) :
    a < b ↔ (sign p a (k + 1) = .pos ∧ sign p a k < sign p b k) ∨
      (sign p a (k + 1) = .neg ∧ sign p b k < sign p a k) := by
  constructor
  · intro hab
    exact highest_difference_of_le p D hD a b hab.le k hne hs
  · intro H
    by_contra hab
    have G := highest_difference_of_le p D hD b a (le_of_not_gt hab) k hne.symm (fun j hj => (hs j hj).symm)
    rw [← hs (k + 1) (by omega)] at G
    rcases H with H | H <;> rcases G with G | G <;> simp_all <;> order

def direction (a b next : SignType) : Bool :=
  decide ((next = .pos ∧ a < b) ∨ (next = .neg ∧ b < a))

def orderScan (a b : ℕ → SignType) : ℕ → Bool
  | 0 => false
  | k + 1 => if a k = b k then orderScan a b k else direction (a k) (b k) (a (k + 1))

theorem orderScan_same (a : ℕ → SignType) (n : ℕ) : orderScan a a n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orderScan, ↓reduceIte, ih]

theorem orderScan_last (a b : ℕ → SignType) (k n : ℕ) (hk : k < n) (hne : a k ≠ b k)
    (hs : ∀ j, k < j → j < n → a j = b j) :
    orderScan a b n = direction (a k) (b k) (a (k + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k = n
    · subst n
      simp only [orderScan, hne, ↓reduceIte]
    · rw [orderScan, ite_eq_left (hs n (by omega) (by omega))]
      exact ih (by omega) (fun j hj hji => hs j hj (by omega))

theorem orderScan_roots (p : ℝ[X]) (hp : p ≠ 0) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (ha : p.IsRoot a) (hb : p.IsRoot b) :
    orderScan (sign p a) (sign p b) (D + 1) = decide (a < b) := by
  by_cases he : a = b
  · subst b
    simp only [orderScan_same, lt_self_iff_false, decide_false]
  · have hex : ∃ k ≤ D, sign p a k ≠ sign p b k := by
      by_contra hn
      push Not at hn
      exact he (root_eq p hp D hD a b ha hb hn)
    let S := (Finset.range (D + 1)).filter (fun k => sign p a k ≠ sign p b k)
    have hS : S.Nonempty := by
      obtain ⟨k, hk, hne⟩ := hex
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩⟩
    let k := S.max' hS
    have hkS : k ∈ S := Finset.max'_mem S hS
    have hk : k ≤ D := by have := Finset.mem_range.mp (Finset.mem_filter.mp hkS).1; omega
    have hne : sign p a k ≠ sign p b k := (Finset.mem_filter.mp hkS).2
    have hs : ∀ j, k < j → sign p a j = sign p b j := by
      intro j hj
      by_cases hjD : j ≤ D
      · by_contra hdiff
        have hm : j ≤ k := Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hdiff⟩)
        omega
      · have hz : Polynomial.derivative^[j] p = 0 := iterate_derivative_eq_zero (hD.trans_lt (by omega))
        simp only [sign, hz, eval_zero]
    rw [orderScan_last _ _ k _ (by omega) hne (fun j hj _ => hs j hj)]
    unfold direction
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (highest_difference_lt_iff p D hD a b k hne hs).symm

end LeanCanny.Algebra.ThomEncoding
