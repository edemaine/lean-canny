/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScalarRootHistoryBounds
public import LeanCanny.Algebra.UniformIntegralPrefixLift

/-! # The actual birth of each retained scalar generator

An entry in a scalar-root height bank comes from one concrete critical
birth. Its current numerator is the embedded root of that birth, and its
integer denominator is the same nonzero selected leading coefficient.
The index identifies the birth by newest-first order.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarRootHistoryBounds
open UniformIntegralPrefix IntegralHistoryCriticalBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure GeneratorOrigin {S B m : ℕ} (P : Prefix S (2 ^ B) m) (bank : HeightBank P) (i : Fin m) where
  birth : ℕ
  order : birth + 1 + i.val = m
  oldPrefix : Prefix S (2 ^ B) birth
  birth_bound : birth ≤ S
  polynomial : Polynomial oldPrefix.carrier
  degree : ℕ
  degree_bound : degree ≤ 2 ^ B
  leading : ℤ
  leading_eq : polynomial.coeff degree = (leading : oldPrefix.carrier)
  leading_ne_zero : leading ≠ 0
  chain : Chain S B (UniformIntegralPrefix.step oldPrefix birth_bound (Nat.two_pow_pos B) polynomial degree) P
  generator_eq : chain.embed (AdjoinRoot.root _) = P.basis.generator i
  denominator_eq : bank.denominator i = leading

theorem History.generator_origin {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) (i : Fin m) : Nonempty (GeneratorOrigin P bank i) := by
  induction history with
  | base S B => exact Fin.elim0 i
  | step F c bank previous select heights scales hC hP hn hW hD hdegree ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨{
        birth := F.birth c
        order := by simp only [Fin.val_zero, Nat.add_zero]
        oldPrefix := F.scalarPrefix c
        birth_bound := (F.data c).birth_bound
        polynomial := (source F).annihilator c
        degree := degree F c
        degree_bound := hdegree
        leading := IntegralClearedCriticalLeadingBits.integer (source F) c
        leading_eq := IntegralClearedCriticalLeadingBits.coefficient (source F) c
        leading_ne_zero := integer_nonzero F c
        chain := .refl _
        generator_eq := rfl
        denominator_eq := rfl }⟩
    · obtain ⟨origin⟩ := ih j
      refine ⟨{
        birth := origin.birth
        order := by have H := origin.order; simp only [Fin.val_succ]; omega
        oldPrefix := origin.oldPrefix
        birth_bound := origin.birth_bound
        polynomial := origin.polynomial
        degree := origin.degree
        degree_bound := origin.degree_bound
        leading := origin.leading
        leading_eq := origin.leading_eq
        leading_ne_zero := origin.leading_ne_zero
        chain := origin.chain.step (F.data c).birth_bound ((source F).annihilator c) (degree F c)
        generator_eq := ?_
        denominator_eq := origin.denominator_eq }⟩
      change AdjoinRoot.of _ (origin.chain.embed (AdjoinRoot.root _)) =
        AdjoinRoot.of _ ((F.scalarPrefix c).basis.generator j)
      rw [origin.generator_eq]

namespace GeneratorOrigin
variable {S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P} {i : Fin m}

theorem birth_lt (o : GeneratorOrigin P bank i) : o.birth < m := by
  have H := o.order
  omega

theorem birth_eq (o : GeneratorOrigin P bank i) : o.birth = m - 1 - i.val := by
  have H := o.order
  omega

theorem length_eq (o : GeneratorOrigin P bank i) : o.chain.length = i.val := by
  have H := o.chain.arity
  have J := o.order
  omega

theorem radix_eq (o : GeneratorOrigin P bank i) : o.chain.radix = (2 ^ B) ^ i.val := by
  rw [Chain.radix, o.length_eq]

theorem matrix (o : GeneratorOrigin P bank i) (r t : Fin (FixedWidthPolynomial.count m B)) :
    Algebra.leftMulMatrix P.basis.finBasis (P.basis.generator i) r t =
      if r.val % o.chain.radix = t.val % o.chain.radix then
        Algebra.leftMulMatrix
          (UniformIntegralPrefix.step o.oldPrefix o.birth_bound (Nat.two_pow_pos B) o.polynomial o.degree).basis.finBasis
          (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) else 0 := by
  rw [← o.generator_eq]
  exact o.chain.matrix _ r t

end GeneratorOrigin
end LeanCanny.Algebra.IntegralScalarRootHistoryBounds
