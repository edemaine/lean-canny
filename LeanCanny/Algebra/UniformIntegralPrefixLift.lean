/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefix
public import LeanCanny.Algebra.IntegralCoordinateBasisFinStep
public import LeanCanny.Algebra.IntegralCoordinateEvaluation

/-! # Exact lifting through several actual scalar extensions

A chain records actual padded extensions of a scalar prefix. Its embedding
preserves the old algebra, and its multiplication matrices ignore precisely
the new low basis digits. The combined radix is a power of the fixed scalar
degree, regardless of the chosen polynomials or advertised degrees.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

inductive Chain (S B : ℕ) : {m : ℕ} → Prefix S (2 ^ B) m → {n : ℕ} → Prefix S (2 ^ B) n → Type 1
  | refl {m : ℕ} (P : Prefix S (2 ^ B) m) : Chain S B P P
  | step {m n : ℕ} {P : Prefix S (2 ^ B) m} {Q : Prefix S (2 ^ B) n}
      (C : Chain S B P Q) (hn : n ≤ S) (p : Polynomial Q.carrier) (d : ℕ) :
      Chain S B P (step Q hn (Nat.two_pow_pos B) p d)

variable {S B m n : ℕ} {P : Prefix S (2 ^ B) m} {Q : Prefix S (2 ^ B) n}

def Chain.length {S B : ℕ} : {m : ℕ} → {P : Prefix S (2 ^ B) m} →
    {n : ℕ} → {Q : Prefix S (2 ^ B) n} → Chain S B P Q → ℕ
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .step C _ _ _ => C.length + 1

theorem Chain.arity (C : Chain S B P Q) : n = m + C.length := by
  induction C with
  | refl => simp only [Chain.length, Nat.add_zero]
  | step C hn p d ih => exact congrArg (fun k => k + 1) ih

noncomputable def Chain.embed {S B : ℕ} : {m : ℕ} → {P : Prefix S (2 ^ B) m} →
    {n : ℕ} → {Q : Prefix S (2 ^ B) n} → (C : Chain S B P Q) → P.carrier →+* Q.carrier
  | _, _, _, _, .refl _ => RingHom.id _
  | _, _, _, _, .step C _ p d => (AdjoinRoot.of (PaddedIntegralNormalization.polynomial p d (2 ^ B))).comp C.embed

theorem Chain.le (C : Chain S B P Q) : m ≤ n := by
  have H := C.arity
  omega

theorem Chain.generator (C : Chain S B P Q) (i : Fin m) :
    C.embed (P.basis.generator i) =
      Q.basis.generator (UniformIntegralPowerSchedule.embed C.le i) := by
  induction C with
  | refl P =>
    have HE : UniformIntegralPowerSchedule.embed (Chain.refl P).le i = i := by
      apply Fin.ext
      simp only [UniformIntegralPowerSchedule.embed, Nat.sub_self, Nat.zero_add]
    rw [HE]
    simp only [Chain.embed, RingHom.id_apply]
  | @step n P Q C hn p d ih =>
    have HE : UniformIntegralPowerSchedule.embed (C.step hn p d).le i =
        (UniformIntegralPowerSchedule.embed C.le i).succ := by
      apply Fin.ext
      simp only [UniformIntegralPowerSchedule.embed, Fin.val_succ]
      have H := C.le
      omega
    rw [HE]
    change AdjoinRoot.of _ (C.embed (P.basis.generator i)) =
      AdjoinRoot.of _ (Q.basis.generator (UniformIntegralPowerSchedule.embed C.le i))
    rw [ih]

theorem Chain.representative_eval (C : Chain S B P Q) (x : P.carrier) :
    (P.basis.representative x).aeval
      (fun i => Q.basis.generator (UniformIntegralPowerSchedule.embed C.le i)) = C.embed x := by
  have H := P.basis.representative_eval_algHom x C.embed.toIntAlgHom
  change (P.basis.representative x).aeval (fun i => C.embed (P.basis.generator i)) = C.embed x at H
  simpa only [C.generator] using H

def Chain.radix (C : Chain S B P Q) : ℕ := (2 ^ B) ^ C.length

theorem Chain.radix_pos (C : Chain S B P Q) : 0 < C.radix := pow_pos (Nat.two_pow_pos B) _

theorem Chain.dimension_eq (C : Chain S B P Q) : count n B = count m B * C.radix :=
  (congrArg (fun k => count k B) C.arity).trans (pow_add _ _ _)

def Chain.oldIndex (C : Chain S B P Q) (i : Fin (count n B)) : Fin (count m B) :=
  ⟨i.val / C.radix, (Nat.div_lt_iff_lt_mul C.radix_pos).mpr (by rw [← C.dimension_eq]; exact i.isLt)⟩

private theorem same_digits (i j N R : ℕ) :
    i % (N * R) = j % (N * R) ↔ i % N = j % N ∧ i / N % R = j / N % R := by
  constructor
  · intro h
    exact ⟨by simpa only [Nat.mod_mul_right_mod] using congrArg (fun k => k % N) h,
      by simpa only [Nat.mod_mul_right_div_self] using congrArg (fun k => k / N) h⟩
  · rintro ⟨h₀, h₁⟩
    rw [Nat.mod_mul, Nat.mod_mul, h₀, h₁]

theorem Chain.oldIndex_step (C : Chain S B P Q) (hn : n ≤ S) (p : Polynomial Q.carrier) (d : ℕ)
    (i : Fin (count (n + 1) B)) :
    (C.step hn p d).oldIndex i = C.oldIndex ((pairIndex n B).symm i).1 := by
  apply Fin.ext
  change i.val / ((2 ^ B) ^ (C.length + 1)) = (i.val / 2 ^ B) / C.radix
  rw [Nat.div_div_eq_div_mul, pow_succ', Chain.radix]

theorem Chain.matrix (C : Chain S B P Q) (x : P.carrier) (i j : Fin (count n B)) :
    Algebra.leftMulMatrix Q.basis.finBasis (C.embed x) i j =
      if i.val % C.radix = j.val % C.radix then
        Algebra.leftMulMatrix P.basis.finBasis x (C.oldIndex i) (C.oldIndex j) else 0 := by
  induction C with
  | refl P =>
    simp only [Chain.embed, RingHom.id_apply, Chain.oldIndex, Chain.radix, Chain.length,
      pow_zero, Nat.mod_one, ite_true, Nat.div_one]
  | @step n P Q C hn p d ih =>
    obtain ⟨⟨r, a⟩, rfl⟩ := (pairIndex n B).surjective i
    obtain ⟨⟨t, b⟩, rfl⟩ := (pairIndex n B).surjective j
    change Algebra.leftMulMatrix (Q.basis.step _ _ _).finBasis
      (AdjoinRoot.of _ (C.embed x)) (pairIndex n B (r, a)) (pairIndex n B (t, b)) = _
    rw [finBasis_of_matrix, ih, C.oldIndex_step hn p d, C.oldIndex_step hn p d]
    simp only [Equiv.symm_apply_apply]
    have HR : (pairIndex n B (r, a)).val / 2 ^ B = r.val :=
      congrArg (fun v : Fin (count n B) × Fin (2 ^ B) => v.1.val) ((pairIndex n B).symm_apply_apply (r, a))
    have HT : (pairIndex n B (t, b)).val / 2 ^ B = t.val :=
      congrArg (fun v : Fin (count n B) × Fin (2 ^ B) => v.1.val) ((pairIndex n B).symm_apply_apply (t, b))
    have HA : (pairIndex n B (r, a)).val % 2 ^ B = a.val :=
      congrArg (fun v : Fin (count n B) × Fin (2 ^ B) => v.2.val) ((pairIndex n B).symm_apply_apply (r, a))
    have HB : (pairIndex n B (t, b)).val % 2 ^ B = b.val :=
      congrArg (fun v : Fin (count n B) × Fin (2 ^ B) => v.2.val) ((pairIndex n B).symm_apply_apply (t, b))
    rw [show (C.step hn p d).radix = 2 ^ B * C.radix by exact pow_succ' _ _]
    simp only [same_digits, HR, HT, HA, HB, Fin.ext_iff]
    split_ifs <;> simp_all

end LeanCanny.Algebra.UniformIntegralPrefix
