/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceSeedSpecialization
public import LeanCanny.Algebra.SignStatisticOrderedQuery
public import LeanCanny.Algebra.PseudoRemainderQuery
public import LeanCanny.Algebra.SignQueryBounds

/-! # Native Tarski queries in an ordered algebraic slice

Actual head degrees are computed internally. The original head and query
readers supply a fixed even pseudo-remainder seed, whose actual principal
signs feed the descending permanence/variation scan. Constant and invalid
slices return zero, including the zero polynomial.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open PrincipalSubresultant
open scoped Classical
attribute [local irreducible] specialized degree BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

noncomputable def coefficient (P : Readers) (F G : Family) (w : List Bool) (j : ℕ) : ℝ :=
  if w ∈ valid (P.comp origin) then
    signedPsc (specialized (P.comp origin) (headFamily F) w) (specialized (P.comp origin) (seedFamily F G) w)
      (specialized (P.comp origin) (headFamily F) w).natDegree
      (specialized (P.comp origin) (seedFamily F G) w).natDegree j
  else 0

theorem coefficient_sign (P : Readers) (F G : Family) (w : List Bool) (j : ℕ) :
    Principal.value (P.comp origin) (headFamily F) (seedFamily F G) (pair w (BinaryNatCode.encode j)) =
      InfinitesimalSign.encode (SignType.sign (coefficient P F G w j)) := by
  by_cases hw : w ∈ valid (P.comp origin)
  · rw [Principal.value_packet _ _ _ w hw j, coefficient, ite_eq_left hw]
    simp only [degree]
  · rw [Principal.value_invalid _ _ _ _ (by simpa only [pairFst_pair] using hw), coefficient, ite_eq_right hw]
    simp only [sign_zero, InfinitesimalSign.encode]

noncomputable def statistic (P : Readers) (F G : Family) (w : List Bool) : ℤ :=
  permanencesMinusVariations ((List.range (declared F G (pairFst w) + 1)).reverse.map (coefficient P F G w))

theorem statistic_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun w => SignStatisticBits.integerCode (statistic P F G w)) := by
  have E := Principal.evaluator (h.comp origin_FP) (headAccess A) (seedAccess A B) (fun v => ha (origin v))
  have hd : BinaryFn (fun w => declared F G (pairFst w)) := (declared_binary A B).comp pairFst_mem_FP
  have H := SignStatisticBits.descendingOrderedEvaluator E _ hd.bits_mem_FP (coefficient P F G) (coefficient_sign P F G)
  refine H.congr (funext fun w => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, statistic]

noncomputable def answer (P : Readers) (F G : Family) (u : List Bool) : ℤ :=
  statistic P F G (liftQuery (prepare P F u))

theorem answer_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (answer P F G u)) :=
  ((prepare_evaluator h A ha).postcompose liftQuery liftQuery_FP).chain (statistic_evaluator h A B ha)

theorem answer_eq_query (P : Readers) (F G : Family) (u : List Bool) (hu : 0 < degree P F u) :
    answer P F G u = RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) := by
  let v := prepare P F u
  have hf : pairFst v = u := pairFst_pair _ _
  have hv : pairFst v ∈ valid P := by simpa only [hf] using degree_valid P F u hu
  have hl := lift_valid P v hv
  have hc : coefficient P F G (liftQuery v) = fun j => signedPsc (specialized P F u)
      (PseudoRemainder.seed (specialized P F u) (specialized P G u) (declared F G v) (bound F G v))
      (degree P F u)
      (PseudoRemainder.seed (specialized P F u) (specialized P G u) (declared F G v) (bound F G v)).natDegree j := by
    funext j
    rw [coefficient, ite_eq_left hl, head_lift P F v hv, seed_lift P F G v hv, hf]
    simp only [degree]
  have hd : declared F G v = degree P F u := declared_prepare P F G u hu
  change permanencesMinusVariations ((List.range (declared F G (pairFst (liftQuery v)) + 1)).reverse.map
    (coefficient P F G (liftQuery v))) = _
  rw [hc]
  simp only [liftQuery, pairFst_pair]
  rw [hd]
  symm
  exact RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery (specialized P F u) (specialized P G u)
    (degree P F u) (bound F G v) (by rw [degree]) hu (input_degree P F G u)

theorem zero_query (P : Readers) (F G : Family) (u : List Bool) (hu : degree P F u = 0) :
    RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) = 0 := by
  have hd : (specialized P F u).natDegree = 0 := by simpa only [degree] using hu
  have hb := RootSignQueries.tarskiQuery_bounds (specialized P F u) (specialized P G u)
  simp only [hd, Nat.cast_zero, neg_zero] at hb
  omega

noncomputable def value (P : Readers) (F G : Family) (u : List Bool) : List Bool :=
  SignStatisticBits.integerCode (RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u))

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) := by
  have D : SpaceDecider {u | degree P F u = 0} := by
    apply (degree_evaluator h A ha).decider (fun z => decide (z = []))
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
    intro u
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  have E := SpaceFunction.branchDecider D (SpaceFunction.ofFP (fun _ => SignStatisticBits.integerCode 0) (constFn_mem_FP _))
    (answer_evaluator h A B ha)
  refine E.congr (funext fun u => ?_)
  split_ifs with hu
  · have hz : degree P F u = 0 := hu
    rw [value, zero_query P F G u hz]
  · have hz : degree P F u ≠ 0 := hu
    rw [value, answer_eq_query P F G u (by omega)]

theorem value_packet (P : Readers) (F G : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    value P F G (pair c (BinaryNatCode.encode r.val)) = SignStatisticBits.integerCode
      (RootSignQueries.tarskiQuery (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)
        (G.slice c (BoundedProjectionOrderedRoot.root P c r).val)) := by
  rw [value, specialized_packet, specialized_packet]

end LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
