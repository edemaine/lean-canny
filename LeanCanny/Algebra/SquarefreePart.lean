/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Removing repeated roots by division by the derivative GCD

For a nonzero polynomial, division by `gcd(p,p')` gives a nonzero separable
polynomial. In characteristic zero it has exactly the original roots. The
construction commutes with field embeddings and includes constant inputs.
-/

@[expose] public section

namespace LeanCanny.Algebra.SquarefreePart
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def common (p : K[X]) : K[X] := EuclideanDomain.gcd p p.derivative
noncomputable def part (p : K[X]) : K[X] := p / common p

theorem common_ne_zero (p : K[X]) (hp : p ≠ 0) : common p ≠ 0 := by
  intro h
  exact hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1

theorem factorization (p : K[X]) (hp : p ≠ 0) : common p * part p = p :=
  EuclideanDomain.mul_div_cancel' (common_ne_zero p hp) (EuclideanDomain.gcd_dvd_left p p.derivative)

theorem part_ne_zero (p : K[X]) (hp : p ≠ 0) : part p ≠ 0 := by
  intro hz
  have h := factorization p hp
  rw [hz, mul_zero] at h
  exact hp h.symm

theorem part_dvd (p : K[X]) : part p ∣ p :=
  EuclideanDomain.div_dvd_of_dvd (EuclideanDomain.gcd_dvd_left p p.derivative)

theorem part_natDegree (p : K[X]) (hp : p ≠ 0) :
    (part p).natDegree = p.natDegree - (common p).natDegree := by
  have h := natDegree_mul (common_ne_zero p hp) (part_ne_zero p hp)
  rw [factorization p hp] at h
  omega

theorem part_map {L : Type*} [Field L] [DecidableEq L] (f : K →+* L) (p : K[X]) :
    (part p).map f = part (p.map f) := by
  rw [part, part, common, common, Polynomial.map_div, derivative_map, gcd_map]

theorem rootMultiplicity_le_one (p : K[X]) (hp : p ≠ 0) (a : K) : (part p).rootMultiplicity a ≤ 1 := by
  have hpow : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ common p :=
    EuclideanDomain.dvd_gcd
      ((pow_dvd_pow (X - C a) (Nat.sub_le _ _)).trans (p.pow_rootMultiplicity_dvd a))
      (pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd a))
  have hcommon : p.rootMultiplicity a - 1 ≤ (common p).rootMultiplicity a :=
    (le_rootMultiplicity_iff (common_ne_zero p hp)).mpr hpow
  have h := congrArg (fun q : K[X] => q.rootMultiplicity a) (factorization p hp)
  rw [rootMultiplicity_mul (by rw [factorization p hp]; exact hp)] at h
  omega

theorem separable_of_splits (p : K[X]) (hp : p ≠ 0) (hs : p.Splits) : (part p).Separable := by
  apply (nodup_roots_iff_of_splits (part_ne_zero p hp) (hs.of_dvd hp (part_dvd p))).mp
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [count_roots]
  exact rootMultiplicity_le_one p hp a

theorem separable (p : K[X]) (hp : p ≠ 0) : (part p).Separable := by
  apply (separable_map (algebraMap K (AlgebraicClosure K))).mp
  rw [part_map]
  exact separable_of_splits _ (Polynomial.map_ne_zero hp) (IsAlgClosed.splits _)

theorem roots_iff [CharZero K] (p : K[X]) (hp : p ≠ 0) (a : K) :
    (part p).IsRoot a ↔ p.IsRoot a := by
  constructor
  · intro h
    change p.eval a = 0
    rw [← factorization p hp, eval_mul, h, mul_zero]
  · intro h
    apply isRoot_of_isRoot_of_dvd_derivative_mul hp ?_ h
    obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_right p p.derivative
    refine ⟨q, ?_⟩
    change p.derivative * part p = p * q
    calc
      p.derivative * part p = (common p * q) * part p := congrArg (fun r => r * part p) hq
      _ = (common p * part p) * q := by ring
      _ = p * q := congrArg (fun r => r * q) (factorization p hp)

theorem eval₂_eq_zero_iff {L : Type*} [Field L] [DecidableEq L] [CharZero L]
    (f : K →+* L) (p : K[X]) (hp : p ≠ 0) (a : L) :
    (part p).eval₂ f a = 0 ↔ p.eval₂ f a = 0 := by
  have h := roots_iff (p.map f) (Polynomial.map_ne_zero hp) a
  rw [← part_map f p] at h
  simpa only [IsRoot, Polynomial.eval_map] using h

end LeanCanny.Algebra.SquarefreePart
