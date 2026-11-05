/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldRadius
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldQueryBounds
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Exact installed default Field queries on shared complete raw tuples -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldIncidence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem natural_heq {N M : ℕ} (hc : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ)
    (h : HEq z w) : CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w := by
  cases hc
  cases eq_of_heq h
  rfl

private theorem eval_natural {N : ℕ} (p : ℤ[X]) (i : Fin N) (z : Fin N → ℝ) :
    (MvPolynomial.rename Fin.val (p.toMvPolynomial i)).eval₂ (Int.castRingHom ℝ) (CoefficientFinitePhysicalQuery.natural z) =
      p.eval₂ (Int.castRingHom ℝ) (z i) := by
  rw [MvPolynomial.eval₂_rename]
  have hh : CoefficientFinitePhysicalQuery.natural z ∘ Fin.val = z := by
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
              (CoefficientFinitePhysicalQuery.natural (SquareSampleCompleteVertices.candidate
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

private theorem full_key (n : List Bool → ℕ) (c : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) [] = IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

private theorem sample_canonical (right : Bool) (z : List Bool) :
    IntegralMixedPhysicalFieldEquality.sample right (IntegralMixedPhysicalFieldEquality.canonical z) =
      pair (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z) := by
  cases right <;> simp only [IntegralMixedPhysicalFieldEquality.canonical,
    IntegralMixedPhysicalFieldEquality.packet, IntegralMixedPhysicalFieldEquality.sample,
    Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair]

theorem packet_wellformed (cL wL cR wR : List Bool) (a b : ℕ) :
    IntegralMixedPhysicalFieldEquality.Wellformed (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) := by
  unfold IntegralMixedPhysicalFieldEquality.Wellformed IntegralMixedPhysicalFieldEquality.canonical
  rcases IntegralMixedPhysicalFieldEquality.packet_fields cL wL cR wR a b with ⟨hcL, hwL, hcR, hwR, ha, hb⟩
  rw [hcL, hwL, hcR, hwR, ha, hb]

private theorem symbolic_count {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
    (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count =
      (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk).count := rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedRecordRows.symbolic

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev Point (right : Bool) (z : List Bool) :=
  Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (CoefficientMarkedRecordFieldQuery.rightRoot right z)) le_rfl).count → ℝ

private theorem bank_count_base {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan key =
      IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) key := by
  have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR := by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [HB]
  exact planned_count _ _ _ _ _ _

private theorem count_eq {R : List Bool → ℕ} (hR : BinaryFn R) (c : List Bool) :
    (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false).count c =
      (CoefficientMarkedRecordRows.symbolic hn ht ha (pairFst c)
        (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl).count := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  have h1 := input_count B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c
  have h3 := CoefficientMarkedRecordRowLayout.count_eq hn ht ha (pairFst c) R
    (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl []
  rw [full_key n c, ← IntegralMixedPhysicalFieldEquality.bank_key_catalog hn ht ha hR c] at h3
  exact h1.trans ((bank_count_base hn ht ha hR _).trans
    (h3.trans (symbolic_count hn ht ha (pairFst c) (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl).symm))

private theorem probe_packet {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool)
    (hz : IntegralMixedPhysicalFieldEquality.Wellformed z) (k : ℕ) :
    IntegralMixedPhysicalFieldEquality.probe hn ht ha hR right (pair z (BinaryNatCode.encode k)) =
      pair (pair (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z))
        (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
          (pair (BinaryNatCode.encode (IntegralMixedPhysicalFieldEquality.catalogSelected n right z)) (BinaryNatCode.encode k))) := by
  rw [IntegralMixedPhysicalFieldEquality.probe_catalog]
  unfold IntegralMixedPhysicalFieldEquality.catalogProbe
  have hs := (congrArg (IntegralMixedPhysicalFieldEquality.sample right) hz).trans (sample_canonical right z)
  rw [hs]

variable {R : List Bool → ℕ} (hRad : BinaryFn R)

noncomputable def nativePhysical (right : Bool) (z : List Bool) (k : ℕ) : MvPolynomial ℕ ℤ :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false
  MvPolynomial.rename Fin.val
    (((IntegralMixedPhysicalFieldEquality.querySource hn ht ha hRad).polynomial
      (IntegralMixedPhysicalFieldEquality.contextProbe n right z k)).toMvPolynomial
        (IntegralFramedPhysicalUnivariateTest.column B.parameters B.plan B.data B.key
          (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hRad)
          (IntegralMixedPhysicalFieldEquality.context right z)
          (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
            (pair (BinaryNatCode.encode (IntegralMixedPhysicalFieldEquality.catalogSelected n right z)) (BinaryNatCode.encode k)))))

attribute [local irreducible] nativePhysical CoefficientMarkedRecordFieldQuery.physical

private theorem native_packet (right : Bool) (z : List Bool)
    (hz : IntegralMixedPhysicalFieldEquality.Wellformed z)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z)) (k : ℕ) :
    IntegralMixedPhysicalFieldEquality.value hn ht ha hRad
      (IntegralMixedPhysicalFieldEquality.probe hn ht ha hRad right (pair z (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (SignType.sign
        ((nativePhysical hn ht ha hRad right z k).eval₂ (Int.castRingHom ℝ)
          (CoefficientFinitePhysicalQuery.natural (SquareSampleCompleteVertices.candidate
            (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
            (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z) hw).val))) := by
  rw [probe_packet hn ht ha hRad right z hz k]
  unfold nativePhysical
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false
  exact clear_packet B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
    (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hRad)
    (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hRad)
    (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z)
    (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
      (pair (BinaryNatCode.encode (IntegralMixedPhysicalFieldEquality.catalogSelected n right z)) (BinaryNatCode.encode k))) hw

/-- Actual default Field queries use their own decoded full tuple and the
constructed left characteristic. Wellformed is literal syntax, not a reader oracle. -/
theorem value_eq (right : Bool) (z : List Bool)
    (hz : IntegralMixedPhysicalFieldEquality.Wellformed z)
    (hEq : R (CoefficientMarkedRecordFieldSource.root z) = R (CoefficientMarkedRecordFieldQuery.rightRoot right z))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldSource.root z) ≤ R (CoefficientMarkedRecordFieldSource.root z))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot right z) ≤ R (CoefficientMarkedRecordFieldQuery.rightRoot right z))
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z))
    (x : Point hn ht ha right z)
    (hx : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context right z) (IntegralMixedPhysicalFieldEquality.word right z) hw).val x) (k : ℕ) :
    IntegralMixedPhysicalFieldEquality.value hn ht ha hRad
      (IntegralMixedPhysicalFieldEquality.probe hn ht ha hRad right (pair z (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (CoefficientMarkedRecordFieldSource.root z))) (CoefficientFinitePhysicalQuery.natural x))) := by
  have hp := CoefficientMarkedRecordFieldQuery.physical_specializes_radius hn ht ha hRad right z k hEq hL hR
  have he := congrArg (fun p : MvPolynomial ℕ ℤ => p.eval₂ (Int.castRingHom ℝ) (CoefficientFinitePhysicalQuery.natural x)) hp
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at he
  rw [native_packet hn ht ha hRad right z hz hw k,
    natural_heq (count_eq hn ht ha hRad (IntegralMixedPhysicalFieldEquality.context right z)) _ x hx]
  unfold nativePhysical
  exact congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) he.symm

noncomputable def Agrees (z : List Bool) (β : ℝ) (left : Point hn ht ha false z) (right : Point hn ht ha true z) : Prop :=
  ∀ k < IntegralMixedPhysicalFieldEquality.catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z) + 1,
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha false z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural left)) =
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha true z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural right))

attribute [local irreducible] SquareSampleCompleteVertices.Valid

theorem agrees_iff (z : List Bool) (hz : IntegralMixedPhysicalFieldEquality.Wellformed z)
    (hEq : R (CoefficientMarkedRecordFieldSource.root z) = R (CoefficientMarkedRecordFieldQuery.rightRoot true z))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldSource.root z) ≤ R (CoefficientMarkedRecordFieldSource.root z))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot true z) ≤ R (CoefficientMarkedRecordFieldQuery.rightRoot true z))
    (hwL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context false z) (IntegralMixedPhysicalFieldEquality.word false z))
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context true z) (IntegralMixedPhysicalFieldEquality.word true z))
    (left : Point hn ht ha false z) (right : Point hn ht ha true z)
    (heL : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context false z) (IntegralMixedPhysicalFieldEquality.word false z) hwL).val left)
    (heR : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context true z) (IntegralMixedPhysicalFieldEquality.word true z) hwR).val right) :
    IntegralMixedPhysicalFieldEquality.agrees hn ht ha hRad z ↔ Agrees hn ht ha z ((2 : ℝ)^R (CoefficientMarkedRecordFieldSource.root z)) left right := by
  unfold IntegralMixedPhysicalFieldEquality.agrees Agrees
  rw [IntegralMixedPhysicalFieldEquality.degree_catalog]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  rw [value_eq hn ht ha hRad false z hz rfl hL hL hwL left heL k,
    value_eq hn ht ha hRad true z hz hEq hL hR hwR right heR k, SquareSampleTestSign.encode_eq_iff]

def Labels (z : List Bool) : Prop :=
  IntegralMixedPhysicalFieldEquality.label false z < IntegralMixedPhysicalFieldEquality.catalogCount n
    (IntegralMixedPhysicalFieldEquality.context false z) ∧
  IntegralMixedPhysicalFieldEquality.label true z < IntegralMixedPhysicalFieldEquality.catalogCount n
    (IntegralMixedPhysicalFieldEquality.context true z)

/-- The entire native default Field predicate, including literal syntax and
label bounds, is this computed shared-tuple formula. No native guard is assumed. -/
theorem language_iff (z : List Bool)
    (hEq : R (CoefficientMarkedRecordFieldSource.root z) = R (CoefficientMarkedRecordFieldQuery.rightRoot true z))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldSource.root z) ≤ R (CoefficientMarkedRecordFieldSource.root z))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot true z) ≤ R (CoefficientMarkedRecordFieldQuery.rightRoot true z))
    (hwL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context false z) (IntegralMixedPhysicalFieldEquality.word false z))
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context true z) (IntegralMixedPhysicalFieldEquality.word true z))
    (left : Point hn ht ha false z) (right : Point hn ht ha true z)
    (heL : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context false z) (IntegralMixedPhysicalFieldEquality.word false z) hwL).val left)
    (heR : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false)
      (IntegralMixedPhysicalFieldEquality.context true z) (IntegralMixedPhysicalFieldEquality.word true z) hwR).val right) :
    z ∈ IntegralMixedPhysicalFieldEquality.language hn ht ha hRad ↔
      IntegralMixedPhysicalFieldEquality.Wellformed z ∧ Labels (n := n) z ∧ Agrees hn ht ha z ((2 : ℝ)^R (CoefficientMarkedRecordFieldSource.root z)) left right := by
  have hl : IntegralMixedPhysicalFieldEquality.Labels hn ht ha hRad z ↔ Labels (n := n) z := by
    unfold IntegralMixedPhysicalFieldEquality.Labels Labels
    rw [IntegralMixedPhysicalFieldEquality.count_catalog, IntegralMixedPhysicalFieldEquality.count_catalog]
  constructor
  · rintro ⟨hsyntax, _, _, hlabels, hagrees⟩
    exact ⟨hsyntax, hl.mp hlabels, (agrees_iff hn ht ha hRad z hsyntax hEq hL hR hwL hwR left right heL heR).mp hagrees⟩
  · rintro ⟨hsyntax, hlabels, hagrees⟩
    exact ⟨hsyntax, hwL, hwR, hl.mpr hlabels, (agrees_iff hn ht ha hRad z hsyntax hEq hL hR hwL hwR left right heL heR).mpr hagrees⟩

end LeanCanny.Encoding.CoefficientMarkedRecordFieldIncidence
