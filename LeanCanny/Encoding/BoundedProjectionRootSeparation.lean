/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootCount
public import LeanCanny.Algebra.IntegerRootSeparation
public import LeanCanny.Algebra.DyadicIsolatingInterval
public import LeanCanny.Encoding.BoundedSampleLabelCertificate

/-! # Source-derived dyadic precision for projection-root isolation

The precision exponent has an FP binary writer. The dyadic numerators are not
constructed here, and their bit strings need not have polynomial length.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRootSeparation
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial

noncomputable def precision (P : Readers) (c : List Bool) : ℕ :=
  IntegerRootSeparation.precision (BoundedProjectionRootCount.degree P c) (BoundedCriticalProjection.coefficientBits P c)

theorem precision_binary {P : Readers} (h : P.PolyTime) : BinaryFn (precision P) :=
  IntegerRootSeparation.precision_binary (BoundedProjectionRootCount.degree_binary h)
    (BoundedCriticalProjection.coefficientBits_binary h)

noncomputable def indexBits (P : Readers) (c : List Bool) : ℕ :=
  precision P c + BoundedProjectionRootCount.massExponent P c + 2

theorem indexBits_binary {P : Readers} (h : P.PolyTime) : BinaryFn (indexBits P) :=
  ((precision_binary h).add (BoundedProjectionRootCount.massExponent_binary h)).add (BinaryFn.const 2)

theorem eval_root (P : Readers) (c : List Bool) (x : ℝ) (hx : x ∈ BoundedCriticalLabels.rootSet P c) :
    (BoundedCriticalProjection.polynomial P c).eval₂ (Int.castRingHom ℝ) x = 0 := by
  rw [BoundedCriticalLabels.rootSet, Multiset.mem_toFinset,
    Polynomial.mem_roots (BoundedCriticalLabels.mapped_ne_zero P c)] at hx
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hx

theorem separated (P : Readers) (c : List Bool) (a b : ℝ)
    (ha : a ∈ BoundedCriticalLabels.rootSet P c) (hb : b ∈ BoundedCriticalLabels.rootSet P c) (hab : a ≠ b) :
    ((2 : ℝ) ^ precision P c)⁻¹ < |a - b| :=
  IntegerRootSeparation.separated (BoundedCriticalProjection.polynomial P c)
    (BoundedCriticalProjection.polynomial_ne_zero P c) (BoundedProjectionRootCount.degree P c)
    (BoundedCriticalProjection.coefficientBits P c) (BoundedCriticalProjection.polynomial_degree P c)
    (fun k => (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
      (BoundedCriticalProjection.polynomial_coefficient_bits P c k))) a b hab (eval_root P c a ha) (eval_root P c b hb)

theorem abs_root (P : Readers) (c : List Bool) (x : ℝ) (hx : x ∈ BoundedCriticalLabels.rootSet P c) :
    |x| < (2 : ℝ) ^ (BoundedProjectionRootCount.massExponent P c + 1) := by
  have hr := abs_root_lt_coefficientMass_add_one (BoundedCriticalProjection.polynomial P c)
    (BoundedCriticalProjection.polynomial_ne_zero P c) x (eval_root P c x hx)
  have hm : coefficientMass (BoundedCriticalProjection.polynomial P c) + 1 ≤
      2 ^ (BoundedProjectionRootCount.massExponent P c + 1) := by
    have := BoundedProjectionRootCount.mass_bound P c
    have := Nat.one_le_two_pow (n := BoundedProjectionRootCount.massExponent P c)
    rw [pow_succ]
    omega
  exact hr.trans_le (by exact_mod_cast hm)

theorem isolating_grid (P : Readers) (c : List Bool) (x : ℝ) (hx : x ∈ BoundedCriticalLabels.rootSet P c) :
    ∃ k : ℤ,
      (DyadicIsolatingInterval.lower k (precision P c) : ℝ) ≤ x ∧
      x < (DyadicIsolatingInterval.upper k (precision P c) : ℝ) ∧
      (BoundedCriticalLabels.rootSet P c).filter (fun y => y < (DyadicIsolatingInterval.lower k (precision P c) : ℝ)) =
        (BoundedCriticalLabels.rootSet P c).filter (fun y => y < x) ∧
      (BoundedCriticalLabels.rootSet P c).filter (fun y => y < (DyadicIsolatingInterval.upper k (precision P c) : ℝ)) =
        insert x ((BoundedCriticalLabels.rootSet P c).filter (fun y => y < x)) :=
  DyadicIsolatingInterval.isolates (BoundedCriticalLabels.rootSet P c) (precision P c)
    (fun a ha b hb hab => separated P c a b ha hb hab) x hx

/-- Every matching sample has an accepted certificate on the same explicitly
bounded grid. This does not construct the numerator k in native space. -/
theorem sample_certificate (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (p : Formula) (hp : BoundedCriticalSampleQuery.Matches P c p x) :
    ∃ k : ℤ, k.natAbs.size ≤ indexBits P c ∧ BoundedSampleLabelCertificate.Certified P
      (fun _ => RationalCutBits.payload (DyadicIsolatingInterval.lower k (precision P c)))
      (fun _ => RationalCutBits.payload (DyadicIsolatingInterval.upper k (precision P c)))
      (fun _ => BoundedCriticalLabels.label P c x) (fun _ => p) c := by
  obtain ⟨k, hl, hu, hL, hU⟩ := isolating_grid P c
    (BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val)
    (BoundedCriticalLabels.projectedRoot P c x).property
  have hb := DyadicIsolatingInterval.index_size k (precision P c)
    (BoundedProjectionRootCount.massExponent P c + 1)
    (BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val) hl hu
    (abs_root P c _ (BoundedCriticalLabels.projectedRoot P c x).property)
  refine ⟨k, ?_, BoundedSampleLabelCertificate.of_isolating_cuts P c x p hp _ _ hL hU⟩
  simpa only [indexBits, Nat.add_assoc, Nat.reduceAdd] using hb

end LeanCanny.Encoding.BoundedProjectionRootSeparation
