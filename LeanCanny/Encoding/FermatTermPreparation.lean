/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatDirectionChoice
public import LeanCanny.ETR.PolynomialMass

/-! # Regular sweep preparation from the actual encoded low term

The normalized syntax supplies the degree and coefficient-mass allowances.
The chosen pure-power degree is even and strictly exceeds the low degree.
Only the source reader and unary spatial dimension enter the native space
certificate; correctness requires that the term's variables fit.
-/

@[expose] public section
namespace LeanCanny.ETR.Term
open MvPolynomial

theorem toPolynomial_eq_rename_finitePolynomial (t : Term) (n : ℕ) (hn : t.arity ≤ n) :
    t.toPolynomial = MvPolynomial.rename Fin.val (t.finitePolynomial n) := by
  induction t with
  | const z => simp only [toPolynomial, finitePolynomial, rename_C]
  | var i =>
    have hi : i < n := hn
    simp only [toPolynomial, finitePolynomial, hi, dite_true, rename_X]
  | add t u ht hu =>
    simp only [arity, max_le_iff] at hn
    simp only [toPolynomial, finitePolynomial, map_add, ht hn.1, hu hn.2]
  | mul t u ht hu =>
    simp only [arity, max_le_iff] at hn
    simp only [toPolynomial, finitePolynomial, map_mul, ht hn.1, hu hn.2]

end LeanCanny.ETR.Term

namespace LeanCanny.Encoding.FermatTermPreparation
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation LeanCanny.Geometry LeanCanny.Algebra
open FermatSweepCertificate MvPolynomial

noncomputable def size (source : List Bool → List Bool) (c : List Bool) : ℕ :=
  (TermView.term (source c)).toData.size

noncomputable def degree (source : List Bool → List Bool) (c : List Bool) : ℕ := 2 * (size source c + 1)

noncomputable def mass (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) : ℕ :=
  size source c + (dim c + 3).size

noncomputable def low (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) :
    MvPolynomial (Fin (dim c + 2)) ℤ := (TermView.term (source c)).finitePolynomial (dim c + 2)

noncomputable def record (source : List Bool → List Bool) (dim : List Bool → ℕ) : List Bool → List Bool :=
  FermatDirectionChoice.record source dim (degree source)
    (FermatDirectionChoice.regularExponent dim (degree source) (mass source dim)) (fun _ => 1)

theorem size_unary {source : List Bool → List Bool} (ht : source ∈ FP) : UnaryFn (size source) :=
  FrozenSource.source_start_unary ht

theorem degree_unary {source : List Bool → List Bool} (ht : source ∈ FP) : UnaryFn (degree source) :=
  (UnaryFn.const 2).mul ((size_unary ht).add (UnaryFn.const 1))

theorem mass_binary {source : List Bool → List Bool} {dim : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) : BinaryFn (mass source dim) :=
  (BinaryFn.ofUnary (size_unary ht)).add (BinaryFn.ofUnary (hd.add (UnaryFn.const 3))).size

theorem degree_even (source : List Bool → List Bool) (c : List Bool) : Even (degree source c) := by
  exact ⟨size source c + 1, by simp only [degree]; omega⟩

theorem degree_gt_one (source : List Bool → List Bool) (c : List Bool) : 1 < degree source c := by
  unfold degree
  omega

theorem low_degree (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) :
    (low source dim c).totalDegree < degree source c := by
  have h := (Term.totalDegree_finitePolynomial (TermView.term (source c)) (dim c + 2)).trans
    (Term.degreeBound_le_dataSize _)
  change (low source dim c).totalDegree ≤ size source c at h
  unfold degree
  omega

theorem polynomial_mass (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) :
    MvMass.mass (FermatCriticalHomogenization.polynomial (low source dim c) 1 (degree source c)) ≤
      2 ^ mass source dim c :=
  FermatRegularSource.mass_le (low source dim c) 1 (degree source c) (size source c)
    (Term.finitePolynomial_mass _ _) (by simpa only [Int.natAbs_one] using Nat.one_le_two_pow)

theorem evaluator {source : List Bool → List Bool} {dim : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) : SpaceFunction (record source dim) :=
  FermatDirectionChoice.regular_evaluator ht hd (BinaryFn.ofUnary (degree_unary ht)) (mass_binary ht hd)
    (constFn_mem_FP (Term.const 1).toData.toBits)

theorem record_length (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool) :
    (record source dim c).length = (dim c + 1) * width (dim c) (degree source c) :=
  FermatDirectionChoice.record_length _ _ _ _ _ _

theorem record_valid (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool)
    (ht : (TermView.term (source c)).arity ≤ dim c + 2) :
    Valid ((IntegerRegularSource.lower (low source dim c) (degree source c) (mass source dim c)).map
        (Int.castRingHom ℚ))
      (IntegerRegularSource.leading (dim c + 1) 1 (degree source c) (mass source dim c) : ℚ)
      (degree source c) (record source dim c) :=
  FermatDirectionChoice.regular_record_valid source dim (degree source) (mass source dim) (fun _ => 1) c
    (low source dim c) (Term.toPolynomial_eq_rename_finitePolynomial _ _ ht) (by decide)
    (low_degree source dim c) (degree_gt_one source c) (polynomial_mass source dim c)

theorem record_regular {L : Type*} [Field L]
    [Algebra (FermatGenericSliceDirection.GenericField ℚ) L]
    (source : List Bool → List Bool) (dim : List Bool → ℕ) (c : List Bool)
    (ht : (TermView.term (source c)).arity ≤ dim c + 2) :
    let q := (IntegerRegularSource.lower (low source dim c) (degree source c) (mass source dim c)).map
      (Int.castRingHom ℚ)
    let a : ℚ := IntegerRegularSource.leading (dim c + 1) 1 (degree source c) (mass source dim c)
    let F := FermatGenericSliceDirection.GenericField ℚ
    ∀ x : Fin (dim c + 1) → L,
      (∀ j, (FermatCriticalBadSystem.equations (FermatGenericSliceDirection.lower q a (degree source c))
        (algebraMap ℚ F a) (degree source c) j).eval₂
          (eval₂Hom (algebraMap F L) (fun i => (direction (dim c) (degree source c) (record source dim c) i : L))) x = 0) →
      (FermatCriticalBadSystem.jacobian (FermatGenericSliceDirection.lower q a (degree source c))
        (algebraMap ℚ F a) (degree source c)).eval₂
          (eval₂Hom (algebraMap F L) (fun i => (direction (dim c) (degree source c) (record source dim c) i : L))) x ≠ 0 := by
  dsimp only
  exact valid_regular _ _ _
    ((PolynomialMapDegree.degree_le _ _).trans_lt
      (IntegerRegularSource.lower_degree _ _ _ (low_degree source dim c)))
    (degree_gt_one source c) _ (record_valid source dim c ht)

end LeanCanny.Encoding.FermatTermPreparation
