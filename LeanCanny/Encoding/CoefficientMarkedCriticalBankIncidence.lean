/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankPhysical
public import LeanCanny.Encoding.CoefficientMarkedCriticalPrefixIncidence
/-! # Installed critical-bank query signs at the SAME own raw tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankIncidence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def natural {N : ℕ} (z : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then z ⟨i, h⟩ else 0

private theorem natural_heq {N M : ℕ} (hc : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ)
    (h : HEq z w) : natural z = natural w := by
  cases hc
  cases eq_of_heq h
  rfl

private theorem eval_natural {N : ℕ} (p : ℤ[X]) (i : Fin N) (z : Fin N → ℝ) :
    (MvPolynomial.rename Fin.val (p.toMvPolynomial i)).eval₂ (Int.castRingHom ℝ) (natural z) =
      p.eval₂ (Int.castRingHom ℝ) (z i) := by
  rw [MvPolynomial.eval₂_rename]
  have hh : natural z ∘ Fin.val = z := by
    funext j
    exact dite_eq_left j.isLt
  rw [hh]
  exact DiagonalUnivariateSystem.eval p i (Int.castRingHom ℝ) z

private theorem clear_packet (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (hp : ∀ c, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
    (coordinate : (c d : List Bool) → Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c)))
    (Q : IntegerPolynomialRootQueriesBits.Source) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w) :
    IntegralFramedPhysicalUnivariateTest.value P D H L F C hs key hp coordinate Q (pair (pair c w) d) =
      InfinitesimalSign.encode (SignType.sign
        ((MvPolynomial.rename Fin.val
          (((IntegralFramedPhysicalUnivariateTest.source P D H L F C hs key coordinate Q).polynomial (pair c d)).toMvPolynomial
            (IntegralFramedPhysicalUnivariateTest.column P D H key coordinate c d))).eval₂ (Int.castRingHom ℝ)
              (natural (SquareSampleCompleteVertices.candidate
                (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hw).val))) := by
  have hh := SquareSampleCompleteUnivariateTest.packet
    (IntegralFramedPhysicalSquare.input P D H L F C hs key hp)
    (IntegralFramedPhysicalUnivariateTest.source P D H L F C hs key coordinate Q)
    (IntegralFramedPhysicalUnivariateTest.column P D H key coordinate) c w d hw
  have he := eval_natural
    ((IntegralFramedPhysicalUnivariateTest.source P D H L F C hs key coordinate Q).polynomial (pair c d))
    (IntegralFramedPhysicalUnivariateTest.column P D H key coordinate c d)
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hw).val
  exact hh.trans (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) he.symm)

private theorem input_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool → List Bool) (hp : ∀ c, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
    (q : List Bool) : (IntegralFramedPhysicalSquare.input P D H L F C hs key hp).count q =
      IntegralFramedPhysicalSquare.count P D (key q) := rfl

private theorem planned_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key =
      IntegralFramedPhysicalSquare.count P D key := rfl

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) =
      SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem count_eq (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child).count q =
      (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  have h1 := input_count B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralMixedPhysicalCriticalPrefixes.key n false child)
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha hR false child) q
  have h2 := planned_count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) (IntegralMixedPhysicalCriticalPrefixes.key n false child q)
  have h3 := CoefficientMarkedRecordRowLayout.count_eq hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) R
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _) q
  rw [← CoefficientMarkedCriticalBankQuery.prefix_key n child q hc] at h3
  exact h1.trans (h2.trans h3)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedCriticalBankQuery.physical
  CoefficientMarkedCriticalBankQuery.nativePhysical CoefficientMarkedRecordRows.symbolic

private theorem native_packet (child : Bool) (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w)
    (i k : ℕ) :
    IntegralMixedPhysicalCriticalBankEquality.value hn ht ha hR false child
      (pair (pair q w) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (SignType.sign
        ((CoefficientMarkedCriticalBankQuery.nativePhysical hn ht ha hR child q i k).eval₂ (Int.castRingHom ℝ)
          (natural (SquareSampleCompleteVertices.candidate
            (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hw).val))) := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  unfold CoefficientMarkedCriticalBankQuery.nativePhysical
  exact clear_packet B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralMixedPhysicalCriticalPrefixes.key n false child)
    (IntegralMixedPhysicalCriticalPrefixes.positive hn ht ha hR false child)
    (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child)
    (IntegralMixedPhysicalCriticalBankEquality.derivatives hn ht ha hR false)
    q w (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)) hw

/-- The literal installed derivative-sign query is the sign of the constructed
parameter polynomial on this SAME full physical prefix tuple. -/
theorem value_eq (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false child) q w hw).val z)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    IntegralMixedPhysicalCriticalBankEquality.value hn ht ha hR false child
      (pair (pair q w) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (SignType.sign
        ((CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) (natural z))) := by
  have hp := CoefficientMarkedCriticalBankQuery.physical_specializes hn ht ha hR child q hc hlarge i k
  have he := congrArg (fun p : MvPolynomial ℕ ℤ => p.eval₂ (Int.castRingHom ℝ) (natural z)) hp
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at he
  rw [native_packet hn ht ha hR child q w hw i.val k,
    natural_heq (count_eq hn ht ha hR child q hc) _ z hz, ← he]

private theorem birth_eq (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    CoefficientMarkedCriticalBankSource.birth n q = IntegralMixedPhysicalCriticalPrefixes.birth n false false q := by
  unfold CoefficientMarkedCriticalBankSource.birth IntegralMixedPhysicalCriticalPrefixes.birth
    CoefficientMarkedCriticalBankSource.stage
  rw [CoefficientMarkedPreludeActual.indices_length, CoefficientMarkedRecordActual.codes_length]
  simp only [IntegralMixedPhysicalMarkedPlan.leafCount, pairFst_pair, Bool.false_eq_true, ite_false]
  omega

private theorem probe_packet (child : Bool) (q v : List Bool) (i k : ℕ) :
    IntegralMixedPhysicalCriticalBankEquality.probe child
      (pair (pair (pair q v) (List.replicate i true)) (BinaryNatCode.encode k)) =
      pair (pair q (if child then v else IntegralMixedPhysicalCriticalQuery.parentWord q))
        (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)) := by
  cases child <;> simp only [IntegralMixedPhysicalCriticalBankEquality.probe,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true, List.length_replicate]

/-- The entire installed parent/child incidence test on ONE shared pair of
computed raw tuples, retaining every derivative order in the native scan. -/
noncomputable def Agrees (q : List Bool) (β : ℝ)
    (parent : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _)).count → ℝ)
    (child : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _)).count → ℝ) : Prop :=
  ∀ i : Fin (CoefficientMarkedCriticalBankSource.birth n q),
    ∀ k < IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q + 1,
      SignType.sign ((CoefficientMarkedCriticalBankQuery.physical hn ht ha false q i k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (natural parent)) =
      SignType.sign ((CoefficientMarkedCriticalBankQuery.physical hn ht ha true q i k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (natural child))

theorem agrees_iff (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (wp wc : List Bool) (hpword : wp = IntegralMixedPhysicalCriticalQuery.parentWord q)
    (hp : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false) q wp)
    (hcword : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q wc)
    (parent : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _)).count → ℝ)
    (child : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _)).count → ℝ)
    (hparent : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false false) q wp hp).val parent)
    (hchild : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q wc hcword).val child) :
    IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR false (pair q wc) ↔
      Agrees hn ht ha q ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q)) parent child := by
  subst wp
  unfold IntegralMixedPhysicalCriticalBankEquality.agrees Agrees
  simp only [pairFst_pair]
  have hb := birth_eq (n := n) q hc
  constructor
  · intro h i k hk
    have hi := h i.val (hb ▸ i.isLt) k
    rw [IntegralMixedPhysicalCriticalBankEquality.degree_catalog hn ht ha hR, pairFst_pair] at hi
    have hh := hi hk
    simp only [probe_packet, Bool.false_eq_true, ite_false, ite_true] at hh
    rw [
      value_eq hn ht ha hR false q hc hlarge _ hp parent hparent i k,
      value_eq hn ht ha hR true q hc hlarge wc hcword child hchild i k] at hh
    exact (SquareSampleTestSign.encode_eq_iff _ _).mp hh
  · intro h i hi k hk
    rw [IntegralMixedPhysicalCriticalBankEquality.degree_catalog hn ht ha hR, pairFst_pair] at hk
    let j : Fin (CoefficientMarkedCriticalBankSource.birth n q) := ⟨i, hb.symm ▸ hi⟩
    simp only [probe_packet, Bool.false_eq_true, ite_false, ite_true]
    rw [
      value_eq hn ht ha hR false q hc hlarge _ hp parent hparent j k,
      value_eq hn ht ha hR true q hc hlarge wc hcword child hchild j k]
    exact (SquareSampleTestSign.encode_eq_iff _ _).mpr (h j k hk)

end LeanCanny.Encoding.CoefficientMarkedCriticalBankIncidence
