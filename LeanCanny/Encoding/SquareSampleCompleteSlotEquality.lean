/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectedThom
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native equality of two selected slots of one complete root

The target slot's annihilator is probed at both slot values. Order zero
checks that the source value is also a root of that annihilator, and the
remaining Thom signs identify the values. The original root label and source
stay fixed. Invalid slot numbers are rejected rather than clipped into range.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteSlotEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def word (q : List Bool) : List Bool := pairSnd (pairFst q)
def slotWord (right : Bool) (q : List Bool) : List Bool :=
  if right then pairSnd (pairSnd q) else pairFst (pairSnd q)
def vertex (q : List Bool) : List Bool := pair (source q) (word q)
theorem source_FP : source ∈ FP := by polytime [source]
theorem vertex_FP : vertex ∈ FP := by polytime [vertex, source, word]
theorem slotWord_FP (right : Bool) : slotWord right ∈ FP := by cases right <;> polytime [slotWord]

def reindex (z : List Bool) : List Bool :=
  pair (pairFst z) (pair (pairSnd (pairFst (pairSnd z))) (pairSnd (pairSnd z)))
theorem reindex_FP : reindex ∈ FP := by polytime [reindex]

noncomputable def targetSource (F : Inputs) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := (SquareSampleProjectedThom.source F).polynomial ∘ reindex
  degree := (SquareSampleProjectedThom.source F).degree ∘ reindex
  mass := (SquareSampleProjectedThom.source F).mass ∘ reindex
  degree_bound z := (SquareSampleProjectedThom.source F).degree_bound (reindex z)
  mass_bound z := (SquareSampleProjectedThom.source F).mass_bound (reindex z)

theorem targetAccess {F : Inputs} (h : F.Access) : IntegerPolynomialRootQueriesBits.Access (targetSource F) := by
  let A := SquareSampleProjectedThom.sourceAccess h
  exact ⟨PolynomialFamilyProductBits.reindexEvaluator A.coefficient reindex reindex_FP,
    A.degree.comp reindex_FP, A.mass.comp reindex_FP⟩

def coordinate (F : Inputs) (c d : List Bool) : Fin (F.count c) :=
  SquareSampleInput.selected F c (pairFst (pairFst d))
theorem coordinate_unary {F : Inputs} (h : F.Access) :
    UnaryFn (fun z => (coordinate F (pairFst z) (pairSnd z)).val) :=
  UnaryFn.fromBitsLE_min (by polytime) ((h.count.comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def leftValue (F : Inputs) : List Bool → List Bool :=
  SquareSampleCompleteUnivariateTest.value F (targetSource F) (coordinate F)
theorem left_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (leftValue F) :=
  SquareSampleCompleteUnivariateTest.evaluator h (targetAccess h) _ (coordinate_unary h)

def probe (right : Bool) (z : List Bool) : List Bool :=
  pair (vertex (pairFst z))
    (if right then pair (slotWord true (pairFst z)) (pairSnd z)
      else pair (pair (slotWord false (pairFst z)) (slotWord true (pairFst z))) (pairSnd z))
theorem probe_FP (right : Bool) : probe right ∈ FP := by
  cases right <;> polytime [probe, vertex, source, word, slotWord]

noncomputable def signaturesEqual (F : Inputs) (q : List Bool) : Prop :=
  ∀ k < F.annDegree (source q) + 1,
    leftValue F (probe false (pair q (BinaryNatCode.encode k))) =
      SquareSampleCompleteCoordinateThom.value F (probe true (pair q (BinaryNatCode.encode k)))

def bounds (F : Inputs) (q : List Bool) : Prop :=
  Nat.fromBitsLE (slotWord false q) < F.count (source q) ∧
    Nat.fromBitsLE (slotWord true q) < F.count (source q)

noncomputable def language (F : Inputs) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (word q) ∧ bounds F q ∧ signaturesEqual F q}

theorem bounds_fppred {F : Inputs} (h : F.Access) : FPPred (bounds F) :=
  ((BinaryFn.fromBits (slotWord_FP false)).lt (BinaryFn.ofUnary (h.count.comp source_FP))).and
    ((BinaryFn.fromBits (slotWord_FP true)).lt (BinaryFn.ofUnary (h.count.comp source_FP)))

theorem scanEvaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun q => [decide (signaturesEqual F q)]) := by
  have L := (left_evaluator h).precompose (probe false) (probe_FP false)
  have R := (SquareSampleCompleteCoordinateThom.evaluator h).precompose (probe true) (probe_FP true)
  have E := (L.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have N : BinaryFn (fun q => F.annDegree (source q)) := h.annDegree.comp source_FP
  exact (E.forall_binary (N.add (BinaryFn.const 1))).congr
    (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
        List.cons.injEq, and_true, decide_eq_true_eq]
      rfl)

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have V := ((SquareSampleCompleteVertices.decider h).precompose vertex vertex_FP).flagEvaluator
  have B := SpaceFunction.ofFP _ (bounds_fppred h).flag_mem_FP
  apply (V.andFlags (B.andFlags (scanEvaluator h))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem left_packet (F : Inputs) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (i j : Fin (F.count c)) (k : ℕ) :
    leftValue F (pair (pair c w)
      (pair (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) (BinaryNatCode.encode k))) =
    InfinitesimalSign.encode (ThomEncoding.sign ((F.annihilator c j).map (Int.castRingHom ℝ))
      ((SquareSampleCompleteVertices.candidate F c w hw).val i) k) := by
  rw [leftValue, SquareSampleCompleteUnivariateTest.packet F (targetSource F) (coordinate F) c w _ hw]
  have HI : coordinate F c
      (pair (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) (BinaryNatCode.encode k)) = i := by
    simp only [coordinate, pairFst_pair, SquareSampleInput.selected_encode]
  have HP : (targetSource F).polynomial (pair c
      (pair (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (F.annihilator c j) := by
    unfold targetSource reindex SquareSampleProjectedThom.source SquareSampleCompleteCoordinateThom.polynomial
      IndexedIntegerDerivativeBits.polynomial
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
      SquareSampleCompleteCoordinateThom.base, SquareSampleCompleteCoordinateThom.order,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change Polynomial.derivative^[k] (SquareSampleCompleteCoordinateThom.baseAt F c
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k))) = _
    rw [SquareSampleCompleteCoordinateThom.baseAt, SquareSampleCompleteCoordinateThom.coordinate,
      pairFst_pair, SquareSampleInput.selected_encode]
  rw [HI, HP]
  simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]

theorem packet (F : Inputs) (complete : SquareSampleComplete.Complete F) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (i j : Fin (F.count c)) :
    pair (pair c w) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) ∈ language F ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val i =
        (SquareSampleCompleteVertices.candidate F c w hw).val j := by
  have HL (k : ℕ) := left_packet F c w hw i j k
  have HR (k : ℕ) := SquareSampleCompleteCoordinateThom.packet F c w hw j k
  simp only [BinaryNatCode.encode] at HL HR
  simp only [language, Set.mem_ofPred_eq, source, word, bounds, signaturesEqual, probe, vertex, slotWord,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, hw, i.isLt, j.isLt, true_and]
  simp_rw [HL, HR, SquareSampleTestSign.encode_eq_iff]
  let p := (F.annihilator c j).map (Int.castRingHom ℝ)
  let a := (SquareSampleCompleteVertices.candidate F c w hw).val i
  let b := (SquareSampleCompleteVertices.candidate F c w hw).val j
  have HB : p.eval b = 0 := by
    rw [Polynomial.eval_map]
    exact complete c _ (SquareSampleCompleteVertices.candidate F c w hw).property j
  constructor
  · intro hs
    have H0 : SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
      simpa only [ThomEncoding.sign, Function.iterate_zero_apply] using hs 0 (by omega)
    have HA : p.eval a = 0 := sign_eq_zero_iff.mp (H0.trans (by rw [HB, sign_zero]))
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (F.ann_nonzero c j))
      (F.annDegree c) (Polynomial.natDegree_map_le.trans (F.ann_degree c j)) a b HA HB
        (fun k hk => hs k (by omega))
  · intro he k _
    rw [he]

end LeanCanny.Encoding.SquareSampleCompleteSlotEquality
