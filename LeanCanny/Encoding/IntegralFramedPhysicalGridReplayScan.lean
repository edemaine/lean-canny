/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalGridReplay
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
/-! # Native external-to-physical equality with both own words fixed

Every derivative of one actual coordinate annihilator is checked. Order zero
checks the root equation and the remaining signs distinguish conjugate roots.
The physical original coordinate is addressed by the external slot divided by
four. Full-row access is derived from native current-Q controls.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalGridReplayScan
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def target (q : List Bool) := pairFst (pairFst q)
def targetWord (q : List Bool) := pairSnd (pairFst q)
def external (q : List Bool) := pairFst (pairFst (pairSnd q))
def ownWord (q : List Bool) := pairSnd (pairFst (pairSnd q))
def indexWord (q : List Bool) := pairSnd (pairSnd q)
def query (target targetWord external ownWord : List Bool) (i : ℕ) :=
  pair (pair target targetWord) (pair (pair external ownWord) (BinaryNatCode.encode i))

theorem target_FP : target ∈ FP := by polytime [target]
theorem targetWord_FP : targetWord ∈ FP := by polytime [targetWord]
theorem external_FP : external ∈ FP := by polytime [external]
theorem ownWord_FP : ownWord ∈ FP := by polytime [ownWord]
theorem indexWord_FP : indexWord ∈ FP := by polytime [indexWord]

noncomputable def selected (S : Source) (hp : ∀ u, 0 < S.arity u) (q : List Bool) :=
  SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) (external q) (indexWord q)

theorem selected_unary (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : UnaryFn (fun q => (selected S hp q).val) :=
  UnaryFn.fromBitsLE_min indexWord_FP
    (((ImplicitSourceGramGrid.count_unary S AS).comp external_FP).sub (UnaryFn.const 1))

noncomputable def ownProbe (S : Source) (hp : ∀ u, 0 < S.arity u) (r : List Bool) :=
  pair (pair (external (pairFst r)) (ownWord (pairFst r)))
    (pair (BinaryNatCode.encode (selected S hp (pairFst r)).val) (pairSnd r))

noncomputable def targetProbe (S : Source) (hp : ∀ u, 0 < S.arity u) (r : List Bool) :=
  pair (pair (target (pairFst r)) (targetWord (pairFst r)))
    (pair (external (pairFst r)) (pair (BinaryNatCode.encode (selected S hp (pairFst r)).val) (pairSnd r)))

theorem ownProbe_FP (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : ownProbe S hp ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := external) pairFst_mem_FP external_FP)
    (mem_FP_comp (f := pairFst) (g := ownWord) pairFst_mem_FP ownWord_FP))
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP (BinaryFn.ofUnary (selected_unary S AS hp)).bits_mem_FP) pairSnd_mem_FP)

theorem targetProbe_FP (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : targetProbe S hp ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := target) pairFst_mem_FP target_FP)
    (mem_FP_comp (f := pairFst) (g := targetWord) pairFst_mem_FP targetWord_FP))
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := external) pairFst_mem_FP external_FP)
      (mem_FP_pair (mem_FP_comp pairFst_mem_FP (BinaryFn.ofUnary (selected_unary S AS hp)).bits_mem_FP) pairSnd_mem_FP))

noncomputable def agrees (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank) (q : List Bool) : Prop :=
  ∀ k < ImplicitSourceGramGrid.degree S (external q) + 1,
    SquareSampleCompleteCoordinateThom.value (ImplicitSourceGramGrid.input S hp)
      (ownProbe S hp (pair q (BinaryNatCode.encode k))) =
    IntegralFramedPhysicalGridReplay.value S hp B (targetProbe S hp (pair q (BinaryNatCode.encode k)))

theorem scanEvaluator (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceFunction (fun q => [decide (agrees S hp B q)]) := by
  have L := (SquareSampleCompleteCoordinateThom.evaluator (ImplicitSourceGramGrid.access S AS hp)).precompose
    (ownProbe S hp) (ownProbe_FP S AS hp)
  have R := (IntegralFramedPhysicalGridReplay.evaluator S AS hp B A T hT hr).precompose
    (targetProbe S hp) (targetProbe_FP S AS hp)
  have E := (L.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have HD0 : BinaryFn (fun q => ImplicitSourceGramGrid.degree S (external q)) :=
    (ImplicitSourceGramGrid.degree_binary S AS).comp external_FP
  have HD := BinaryFn.add HD0 (BinaryFn.const 1)
  exact (E.forall_binary HD).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees, Function.comp_apply, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def language (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank) : Language :=
  {q | SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) (target q) (targetWord q) ∧
    SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) (external q) (ownWord q) ∧ agrees S hp B q}

theorem decider (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceDecider (language S hp B) := by
  have L := ((SquareSampleCompleteVertices.decider
    (IntegralFramedPhysicalGridReplay.input_access B A T hT hr)).precompose
      (fun q => pair (target q) (targetWord q)) (mem_FP_pair target_FP targetWord_FP)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider (ImplicitSourceGramGrid.access S AS hp)).precompose
    (fun q => pair (external q) (ownWord q)) (mem_FP_pair external_FP ownWord_FP)).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator S AS hp B A T hT hr))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, Set.mem_preimage,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    language S hp B ∈ PSPACE := (decider S AS hp B A T hT hr).mem_PSPACE

theorem selected_query (S : Source) (hp : ∀ u, 0 < S.arity u) (t w c v : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) : (selected S hp (query t w c v i.val)).val = i.val := by
  have HE : external (query t w c v i.val) = c := by
    simp only [external, query, pairFst_pair, pairSnd_pair]
  have HI : indexWord (query t w c v i.val) = BinaryNatCode.encode i.val := by
    simp only [indexWord, query, pairSnd_pair]
  let f (c b : List Bool) : ℕ := (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c b).val
  change f (external (query t w c v i.val)) (indexWord (query t w c v i.val)) = _
  rw [HE, HI]
  change (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c (BinaryNatCode.encode i.val)).val = _
  rw [SquareSampleInput.selected_encode]

theorem ownProbe_query (S : Source) (hp : ∀ u, 0 < S.arity u) (t w c v : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) (k : ℕ) :
    ownProbe S hp (pair (query t w c v i.val) (BinaryNatCode.encode k)) =
      pair (pair c v) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)) := by
  unfold ownProbe
  rw [pairFst_pair, pairSnd_pair, selected_query]
  simp only [external, ownWord, query, pairFst_pair, pairSnd_pair]

theorem targetProbe_query (S : Source) (hp : ∀ u, 0 < S.arity u) (t w c v : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) (k : ℕ) :
    targetProbe S hp (pair (query t w c v i.val) (BinaryNatCode.encode k)) =
      pair (pair t w) (ImplicitSourceGramGridReplayDatum.packet c i.val k) := by
  unfold targetProbe
  rw [pairFst_pair, pairSnd_pair, selected_query]
  simp only [target, targetWord, external, query, pairFst_pair, pairSnd_pair, ImplicitSourceGramGridReplayDatum.packet]

theorem agrees_query (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank) (t w c v : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) :
    agrees S hp B (query t w c v i.val) ↔
      ∀ k ≤ ImplicitSourceGramGrid.degree S c,
        SquareSampleCompleteCoordinateThom.value (ImplicitSourceGramGrid.input S hp)
          (pair (pair c v) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
        IntegralFramedPhysicalGridReplay.value S hp B
          (pair (pair t w) (ImplicitSourceGramGridReplayDatum.packet c i.val k)) := by
  unfold agrees
  simp only [ownProbe_query, targetProbe_query]
  simp only [external, query, pairFst_pair, pairSnd_pair, Nat.lt_add_one_iff]

theorem packet (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank) (t w c v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalGridReplay.input B) t w)
    (hv : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c v)
    (i : Fin (ImplicitSourceGramGrid.count S c)) :
    query t w c v i.val ∈ language S hp B ↔
      (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c v hv).val i =
        IntegralFramedPhysicalGridReplay.point B t w hw i.val := by
  unfold language
  simp only [Set.mem_ofPred_eq]
  rw [agrees_query]
  simpa only [target, targetWord, external, ownWord, query, pairFst_pair, pairSnd_pair, hw, hv, true_and] using
    IntegralFramedPhysicalGridReplay.signs_iff S hp B t w c v hw hv i

end LeanCanny.Encoding.IntegralFramedPhysicalGridReplayScan
