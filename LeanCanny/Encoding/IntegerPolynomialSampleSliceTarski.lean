/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSlicePrincipal
public import LeanCanny.Encoding.BoundedAlgebraicSliceTarski

/-! # Native Tarski queries over complete algebraic sample parameters

Complete scalar labels retain repeated parameter roots. Actual head and seed degrees are read internally. Pseudo-remainder seeds
reuse the original bivariate coefficient machines. All attached degree and
principal-index records preserve the same complete scalar sample label.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice.Tarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial Brackets
open IntegerPolynomialRootQueriesBits (Source)
open BoundedAlgebraicSlice (Family)
open PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local irreducible] specialized degree point

def seedContext (v : List Bool) : List Bool :=
  pair (pair (dropRecord v) []) (pairSnd (pairSnd v))
theorem seedContext_FP : seedContext ∈ FP :=
  mem_FP_pair (mem_FP_pair dropRecord_FP (constFn_mem_FP [])) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def bound (F G : Family) (v : List Bool) : ℕ := BoundedAlgebraicSlice.Tarski.bound F G (seedContext v)
def declared (F G : Family) (v : List Bool) : ℕ := BoundedAlgebraicSlice.Tarski.declared F G (seedContext v)
theorem declared_binary {F G : Family} (A : F.Access) (B : G.Access) : BinaryFn (declared F G) :=
  (BoundedAlgebraicSlice.Tarski.declared_binary A B).comp seedContext_FP

def headFamily (F : Family) : Family := F.comp dropRecord
def headAccess {F : Family} (A : F.Access) : (headFamily F).Access := A.comp dropRecord dropRecord_FP
noncomputable def seedFamily (F G : Family) : Family := (BoundedAlgebraicSlice.Tarski.seedFamily F G).comp seedContext
noncomputable def seedAccess {F G : Family} (A : F.Access) (B : G.Access) : (seedFamily F G).Access :=
  (BoundedAlgebraicSlice.Tarski.seedAccess A B).comp seedContext seedContext_FP

def prepareFinish (z : List Bool) : List Bool := attach (pairFst z) (BinaryNat.pred (pairSnd z))
theorem prepareFinish_FP : prepareFinish ∈ FP := by polytime [prepareFinish, attach]
noncomputable def prepare (P : Source) (F : Family) (u : List Bool) : List Bool :=
  attach u (BinaryNatCode.encode (degree P F u - 1))
theorem prepare_evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F : Family} (A : F.Access) : SpaceFunction (prepare P F) := by
  have E := (degreeEvaluator h A).withInput.postcompose prepareFinish prepareFinish_FP
  exact E.congr (funext fun u => by simp only [prepareFinish, prepare, Function.comp_apply, pairFst_pair,
    pairSnd_pair, BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, degree])

theorem head_attach (P : Source) (F : Family) (u r : List Bool) :
    specialized P (headFamily F) (attach u r) = specialized P F u := specialized_attach P F u r

theorem seed_attach (P : Source) (F G : Family) (u r : List Bool) (hu : u ∈ valid P) :
    specialized P (seedFamily F G) (attach u r) =
      PseudoRemainder.seed (specialized P F u) (specialized P G u)
        (declared F G (context (attach u r))) (bound F G (context (attach u r))) := by
  rw [specialized, ite_eq_left ((attach_valid P u r).mpr hu), specialized, ite_eq_left hu,
    specialized, ite_eq_left hu]
  rw [point_attach]
  simp only [Family.slice, seedFamily, Family.comp, BoundedAlgebraicSlice.Tarski.seedFamily,
    BoundedAlgebraicSlice.Tarski.source, BivariateTarskiSeedBits.Family.seed, seedContext, dropRecord,
    attach, context, pairFst_pair, pairSnd_pair, BoundedAlgebraicSlice.Tarski.origin, declared, bound]
  rw [PseudoRemainder.seed_map]

theorem declared_prepare (P : Source) (F G : Family) (u : List Bool) (hu : 0 < degree P F u) :
    declared F G (context (prepare P F u)) = degree P F u := by
  have hd : degree P F u ≤ F.degree (context u) := by simpa only [degree] using specialized_degree P F u
  simp only [declared, BoundedAlgebraicSlice.Tarski.declared, BoundedAlgebraicSlice.Tarski.bound,
    BoundedAlgebraicSlice.Tarski.origin, seedContext, dropRecord, context, prepare, attach,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold context at hd
  omega

theorem input_degree (P : Source) (F G : Family) (u : List Bool) :
    (specialized P G u * (specialized P F u).derivative).natDegree ≤ bound F G (context (prepare P F u)) := by
  have hp := (Polynomial.natDegree_derivative_le (specialized P F u)).trans (Nat.sub_le _ _)
  have hF := specialized_degree P F u
  have hG := specialized_degree P G u
  apply Polynomial.natDegree_mul_le.trans
  simp only [bound, BoundedAlgebraicSlice.Tarski.bound, BoundedAlgebraicSlice.Tarski.origin,
    seedContext, dropRecord, context, prepare, attach, pairFst_pair, pairSnd_pair]
  unfold context at hF hG
  omega

noncomputable def coefficient (P : Source) (F G : Family) (w : List Bool) (j : ℕ) : ℝ :=
  if w ∈ valid P then signedPsc (specialized P (headFamily F) w) (specialized P (seedFamily F G) w)
    (degree P (headFamily F) w) (degree P (seedFamily F G) w) j else 0

theorem coefficient_sign (P : Source) (F G : Family) (w : List Bool) (j : ℕ) :
    Principal.value P (headFamily F) (seedFamily F G) (pair w (BinaryNatCode.encode j)) =
      InfinitesimalSign.encode (SignType.sign (coefficient P F G w j)) := by
  by_cases hw : w ∈ valid P
  · rw [Principal.value_packet P _ _ w hw j, coefficient, ite_eq_left hw]
  · rw [Principal.value_invalid P _ _ _ (by simpa only [pairFst_pair] using hw), coefficient, ite_eq_right hw]
    simp only [sign_zero, InfinitesimalSign.encode]

noncomputable def statistic (P : Source) (F G : Family) (w : List Bool) : ℤ :=
  permanencesMinusVariations ((List.range (declared F G (context w) + 1)).reverse.map (coefficient P F G w))
theorem statistic_evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) :
    SpaceFunction (fun w => SignStatisticBits.integerCode (statistic P F G w)) := by
  have E := Principal.evaluator h (headAccess A) (seedAccess A B)
  have hd : BinaryFn (fun w => declared F G (context w)) := (declared_binary A B).comp context_FP
  have H := SignStatisticBits.descendingOrderedEvaluator E _ hd.bits_mem_FP (coefficient P F G) (coefficient_sign P F G)
  exact H.congr (funext fun w => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, statistic])

noncomputable def answer (P : Source) (F G : Family) (u : List Bool) : ℤ := statistic P F G (prepare P F u)
theorem answer_evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (answer P F G u)) :=
  (prepare_evaluator h A).chain (statistic_evaluator h A B)

theorem answer_eq_query (P : Source) (F G : Family) (u : List Bool) (hu : 0 < degree P F u) :
    answer P F G u = RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) := by
  let w := prepare P F u
  have hw : w ∈ valid P := (attach_valid P u _).mpr (degree_valid P F u hu)
  have hc : coefficient P F G w = fun j => signedPsc (specialized P F u)
      (PseudoRemainder.seed (specialized P F u) (specialized P G u) (declared F G (context w)) (bound F G (context w)))
      (degree P F u)
      (PseudoRemainder.seed (specialized P F u) (specialized P G u) (declared F G (context w)) (bound F G (context w))).natDegree j := by
    funext j
    rw [coefficient, ite_eq_left hw]
    simp only [degree, w, prepare, head_attach, seed_attach P F G u _ (degree_valid P F u hu)]
  change permanencesMinusVariations ((List.range (declared F G (context w) + 1)).reverse.map (coefficient P F G w)) = _
  rw [hc, declared_prepare P F G u hu]
  symm
  exact RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ (degree P F u) (bound F G (context w))
    (by rw [degree]) hu (input_degree P F G u)

theorem zero_query (P : Source) (F G : Family) (u : List Bool) (hu : degree P F u = 0) :
    RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u) = 0 := by
  have hb := RootSignQueries.tarskiQuery_bounds (specialized P F u) (specialized P G u)
  have hd : (specialized P F u).natDegree = 0 := by simpa only [degree] using hu
  rw [hd] at hb
  simp only [Nat.cast_zero, neg_zero] at hb
  omega

noncomputable def value (P : Source) (F G : Family) (u : List Bool) : List Bool :=
  SignStatisticBits.integerCode (RootSignQueries.tarskiQuery (specialized P F u) (specialized P G u))
theorem evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) : SpaceFunction (value P F G) := by
  have D : SpaceDecider {u | degree P F u = 0} := by
    apply (degreeEvaluator h A).decider (fun z => decide (z = []))
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
    intro u
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff, degree]
  have E := SpaceFunction.branchDecider D (SpaceFunction.ofFP (fun _ => SignStatisticBits.integerCode 0) (constFn_mem_FP _))
    (answer_evaluator h A B)
  apply E.congr
  funext u
  split_ifs with hu
  · rw [value, zero_query P F G u hu]
  · have hz : degree P F u ≠ 0 := hu
    rw [value, answer_eq_query P F G u (by omega)]

end LeanCanny.Encoding.IntegerPolynomialSampleSlice.Tarski
