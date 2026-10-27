/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceProducts
public import LeanCanny.Encoding.BoundedAlgebraicSliceRootCount

/-! # Simultaneous sign constraints in algebraic fibers

Nine product Tarski moments count distinct roots satisfying two prescribed
signs. Every moment is computed from the original bivariate readers. The
integer indicator identity supplies the exact factor four; native division
recovers the count. Zero heads and invalid base ordinals have no roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.JointCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical BigOperators

private theorem addEvaluator {f g : List Bool → ℤ}
    (hf : SpaceFunction (fun u => SignStatisticBits.integerCode (f u)))
    (hg : SpaceFunction (fun u => SignStatisticBits.integerCode (g u))) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (f u + g u)) := by
  have E := (hf.pairOutputs (hg.postcompose RootCount.negateCode RootCount.negateCode_FP)).postcompose
    SignedIntegerArithmetic.subtract SignedIntegerArithmetic.subtract_FP
  refine E.congr (funext fun u => ?_)
  simp only [Function.comp_apply, RootCount.negateCode_packet, SignedIntegerArithmetic.subtract_packet, sub_neg_eq_add]

private theorem scaleEvaluator (a : ℤ) {f : List Bool → ℤ}
    (hf : SpaceFunction (fun u => SignStatisticBits.integerCode (f u))) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (a * f u)) := by
  have C := SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode a))
  have E := (C.pairOutputs hf).postcompose IntegerSumBits.multiply IntegerSumBits.multiply_mem_FP
  exact E.congr (funext fun u => by simp only [Function.comp_apply, IntegerSumBits.multiply_codes])

private theorem sumEvaluator {J : Type*} [DecidableEq J] (s : Finset J) (f : J → List Bool → ℤ)
    (hf : ∀ j ∈ s, SpaceFunction (fun u => SignStatisticBits.integerCode (f j u))) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (∑ j ∈ s, f j u)) := by
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty] using SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))
  | @insert j s hj ih =>
    intro hf
    have E := addEvaluator (hf j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    simpa only [Finset.sum_insert hj] using E

noncomputable def tests (P : Readers) (G H : Family) (u : List Bool) : Bool → ℝ[X] :=
  fun b => if b then specialized P H u else specialized P G u

def pattern (s t : SignType) : Bool → SignType := fun b => if b then t else s

noncomputable def moment (P : Readers) (F G H : Family) (e : Bool → Fin 3) (u : List Bool) : ℤ :=
  RootSignQueries.tarskiQuery (specialized P F u) (RootSignQueries.queryPolynomial (tests P G H u) e)

theorem moment_evaluator {P : Readers} (h : P.PolyTime) {F G H : Family}
    (A : F.Access) (B : G.Access) (C : H.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (e : Bool → Fin 3) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (moment P F G H e u)) := by
  have E := Tarski.evaluator h A (productAccess (smallPowerAccess C (e true)) (smallPowerAccess B (e false))) ha
  refine E.congr (funext fun u => ?_)
  by_cases hu : u ∈ valid P
  · simp only [Tarski.value, moment, specialized, ite_eq_left hu, product_slice, smallPower_slice,
      RootSignQueries.queryPolynomial, Fintype.prod_bool, tests, Bool.false_eq_true, ↓reduceIte]
  · simp only [Tarski.value, moment, specialized, ite_eq_right hu, RootSignQueries.tarskiQuery,
      RootSignQueries.signSum, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.sum_empty]

noncomputable def scaled (P : Readers) (F G H : Family) (s t : SignType) (u : List Bool) : ℤ :=
  RootSignQueries.scaledRootCount (specialized P F u) (tests P G H u) (pattern s t)

theorem scaled_evaluator {P : Readers} (h : P.PolyTime) {F G H : Family}
    (A : F.Access) (B : G.Access) (C : H.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s t : SignType) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (scaled P F G H s t u)) := by
  have E := sumEvaluator Finset.univ (fun e u => RootSignQueries.patternWeight (pattern s t) e * moment P F G H e u)
    (fun e _ => scaleEvaluator _ (moment_evaluator h A B C ha e))
  refine E.congr (funext fun u => ?_)
  simp only [scaled, RootSignQueries.scaledRootCount, moment]
  apply congrArg SignStatisticBits.integerCode
  exact Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun _ _ => rfl)

noncomputable def count (P : Readers) (F G H : Family) (s t : SignType) (u : List Bool) : ℕ :=
  RootSignQueries.signCount (specialized P F u).roots.toFinset (tests P G H u) (pattern s t)

theorem count_eq_filter (P : Readers) (F G H : Family) (s t : SignType) (u : List Bool) :
    count P F G H s t u = ((specialized P F u).roots.toFinset.filter (fun y =>
      SignType.sign ((specialized P G u).eval y) = s ∧ SignType.sign ((specialized P H u).eval y) = t)).card := by
  unfold count RootSignQueries.signCount
  apply congrArg Finset.card
  ext y
  simp [tests, pattern, Bool.forall_bool]

theorem diagonal_count (P : Readers) (F G : Family) (s : SignType) (u : List Bool) :
    count P F G G s s u = RootCount.signCount P F G s u := by
  simp only [count_eq_filter, RootCount.signCount, RootSignQueries.singleSignCount, and_self]

theorem invalid_base (P : Readers) (F G H : Family) (s t : SignType) (u : List Bool) (hu : u ∉ valid P) :
    count P F G H s t u = 0 := by
  simp only [count_eq_filter, specialized, ite_eq_right hu, Polynomial.roots_zero,
    Multiset.toFinset_zero, Finset.filter_empty, Finset.card_empty]

theorem scaled_eq_count (P : Readers) (F G H : Family) (s t : SignType) (u : List Bool) :
    scaled P F G H s t u = ((4 * count P F G H s t u : ℕ) : ℤ) := by
  rw [scaled, RootSignQueries.scaledRootCount_eq, Fintype.card_bool]
  norm_num [count, Nat.cast_mul]

def unscale (z : List Bool) : List Bool := BinaryNat.div (pair (pairFst z) (BinaryNatCode.encode 4))
theorem unscale_FP : unscale ∈ FP := by
  have E := mem_FP_comp (mem_FP_pair pairFst_mem_FP (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.div_mem_FP
  exact mem_FP_of_eq E (fun z => by simp only [unscale, Function.comp_apply])

theorem evaluator {P : Readers} (h : P.PolyTime) {F G H : Family}
    (A : F.Access) (B : G.Access) (C : H.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s t : SignType) :
    SpaceFunction (fun u => BinaryNatCode.encode (count P F G H s t u)) := by
  have E := (scaled_evaluator h A B C ha s t).postcompose unscale unscale_FP
  refine E.congr (funext fun u => ?_)
  rw [Function.comp_apply, scaled_eq_count]
  simp only [unscale, SignStatisticBits.integerCode, pairFst_pair, BinaryNat.div_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Int.toNat_natCast, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]

theorem count_packet (P : Readers) (F G H : Family) (s t : SignType) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) :
    count P F G H s t (pair c (BinaryNatCode.encode r.val)) =
      ((F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset.filter (fun y =>
        SignType.sign ((G.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = s ∧
        SignType.sign ((H.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = t)).card := by
  simp only [count_eq_filter, specialized_packet]

noncomputable def realizable (P : Readers) (F G H : Family) (s t : SignType) : Language :=
  {u | 0 < count P F G H s t u}

theorem realizable_decider {P : Readers} (h : P.PolyTime) {F G H : Family}
    (A : F.Access) (B : G.Access) (C : H.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s t : SignType) :
    SpaceDecider (realizable P F G H s t) := by
  apply (evaluator h A B C ha s t).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [realizable, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega

theorem realizable_packet (P : Readers) (F G H : Family) (s t : SignType) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) (hp : F.slice c (BoundedProjectionOrderedRoot.root P c r).val ≠ 0) :
    pair c (BinaryNatCode.encode r.val) ∈ realizable P F G H s t ↔
      ∃ y, (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y = 0 ∧
        SignType.sign ((G.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = s ∧
        SignType.sign ((H.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = t := by
  change 0 < count P F G H s t _ ↔ _
  rw [count_packet, Finset.card_pos]
  simp only [Finset.Nonempty, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hp,
    Polynomial.IsRoot.def]

theorem realizable_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G H : Family}
    (A : F.Access) (B : G.Access) (C : H.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s t : SignType) :
    realizable P F G H s t ∈ PSPACE := (realizable_decider h A B C ha s t).mem_PSPACE

end LeanCanny.Encoding.BoundedAlgebraicSlice.JointCount
