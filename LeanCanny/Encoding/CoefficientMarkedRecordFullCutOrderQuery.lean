/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordTuple
public import LeanCanny.Encoding.IntegralMixedPhysicalCutOrderedInterval
/-! # The literal positive-cleared endpoint order polynomial over the parameter -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def raw {A : Type*} [CommRing A] (m : ℕ) (Q c : A) (index power : ℕ) : MvPolynomial (Fin m) A :=
  if hi : index < m then MvPolynomial.monomial (Finsupp.single ⟨index, hi⟩ power) (Q*c) else 0

private theorem raw_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (m : ℕ) (Q c : A) (index power : ℕ) :
    MvPolynomial.map φ (raw m Q c index power) = raw m (φ Q) (φ c) index power := by
  unfold raw
  split_ifs <;> simp only [MvPolynomial.map_monomial, map_mul, map_zero]

private theorem raw_heq {m n : ℕ} (hm : m = n) (Q c Q' c' : ℤ) (i power power' : ℕ)
    (hQ : Q = Q') (hc : c = c') (hp : power = power') :
    HEq (raw m Q c i power) (raw n Q' c' i power') := by
  cases hm
  cases hQ
  cases hc
  cases hp
  rfl

private theorem raw_native (F : RationalMonomialWindowQuery.Family) (q : List Bool) :
    raw (F.arity q) (F.scalars.denominator q) (F.scalars.numerator q) (F.index q) (F.weight q) =
      RationalMonomialWindowQuery.raw F q := rfl

private theorem raw_index_heq {m n : ℕ} (hm : m = n) (Q c Q' c' : ℤ) (i j power power' : ℕ)
    (hQ : Q = Q') (hc : c = c') (hi : i = j) (hp : power = power') :
    HEq (raw m Q c i power) (raw n Q' c' j power') := by
  cases hm
  cases hQ
  cases hc
  cases hi
  cases hp
  rfl

private theorem sub_heq {m n : ℕ} (hm : m = n)
    (p q : MvPolynomial (Fin m) ℤ) (p' q' : MvPolynomial (Fin n) ℤ)
    (hp : HEq p p') (hq : HEq q q') : HEq (p-q) (p'-q') := by
  cases hm
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

private theorem evaluate_heq {m n : ℕ} (hm : m = n)
    (p : MvPolynomial (Fin m) ℤ) (q : MvPolynomial (Fin n) ℤ) (hp : HEq p q)
    (z : Fin m → ℝ) (w : Fin n → ℝ) (hz : HEq z w) :
    p.eval₂ (Int.castRingHom ℝ) z = q.eval₂ (Int.castRingHom ℝ) w := by
  cases hm
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) = SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

private theorem integer_evaluation {m : ℕ} (p : MvPolynomial (Fin m) ℤ[X]) (r : ℕ) (z : Fin m → ℝ) :
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p).eval₂ (Int.castRingHom ℝ) z =
      p.eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r)) z := by
  rw [MvPolynomial.eval₂_map, scalar_evaluation]

private theorem native_value (B : IntegralFramedBankQuery.Bank) (left right : List Bool → ℕ)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedFramedHeaderBits.Represents (B).parameters (B).plan (B).data T)
    (q w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) q w) :
    IntegralFramedPhysicalBankOrderSource.value B left right T hT (pair (pair q w) []) =
      InfinitesimalSign.encode (SignType.sign
        ((IntegralFramedPhysicalBankOrderSource.polynomial B left right q).eval₂ (Int.castRingHom ℝ)
          (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv))) := by
  have HE := IntegralFramedPhysicalSuffixTest.packet_scalar B T hT (IntegralFramedPhysicalBankOrderSource.source B left right) q w [] hv
  have HC (i : Fin (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key q)).count) :
      Fin.cast ((IntegralFramedPhysicalBankOrderSource.source B left right).dimension q []) (FixedWidthSuffixLiftBits.shift 0 i) = i := by
    apply Fin.ext
    change 0+i.val=i.val
    omega
  change IntegralFramedPhysicalBankOrderSource.value B left right T hT (pair (pair q w) []) = _ at HE
  simpa only [IntegralFramedPhysicalBankOrderSource.source, HC] using HE

private theorem raw_bank_heq (B C : IntegralFramedBankQuery.Bank) (h : B = C)
    (index : List Bool → ℕ) (q : List Bool) :
    HEq (IntegralFramedPhysicalBankOrderSource.raw B index q) (IntegralFramedPhysicalBankOrderSource.raw C index q) := by
  cases h
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def scalarRaw (ctx : List Bool) (index : ℕ) :=
  raw (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx)
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx))
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) index)
    index (CoefficientMarkedRecordFullCutWindow.weight hn ht ha ctx index)

noncomputable def scalar (ctx : List Bool) (left right : ℕ) := scalarRaw hn ht ha ctx right-scalarRaw hn ht ha ctx left

noncomputable def polynomial (ctx : List Bool) (left right : ℕ) : MvPolynomial ℕ ℤ[X] :=
  MvPolynomial.rename (fun i => scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) i.val)
    (scalar hn ht ha ctx left right)

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem scalarRaw_specializes (ctx : List Bool) (k left right : ℕ) (side : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (scalarRaw hn ht ha ctx (if side then right else left)))
      (IntegralFramedPhysicalBankOrderSource.raw B (IntegralMixedPhysicalCutOpenInterval.selected side) (CTX ctx k left right)) := by
  let index := if side then right else left
  have HP := CoefficientMarkedRecordFullCutWindow.terminal_products hn ht ha hR ctx index hlarge
  have HW := CoefficientMarkedRecordFullCutWindow.weight_native hn ht ha hR ctx index
  have HM := CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx
  have HK := CoefficientMarkedRecordFullCutInstalled.terminal_context hn ht ha hR ctx k left right
  have HI : IntegralMixedPhysicalCutOpenInterval.selected side (CTX ctx k left right) = index := by
    cases side <;> simp only [CoefficientMarkedRecordFullCutInstalled.context, IntegralMixedPhysicalCutOpenInterval.selected,
      pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true, BinaryNatCode.encode, Nat.fromBitsLE_bits, index]
  unfold scalarRaw
  rw [raw_map]
  have HE := raw_heq HM.symm _ _ _ _ index _ _ HP.1 HP.2 HW.symm
  have HN := raw_native (IntegralMixedFramedWindowQuery.family PC DC HC (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR) (fun _ => TERM ctx) (fun _ => index)) []
  have HR : HEq (IntegralFramedPhysicalBankOrderSource.raw B (IntegralMixedPhysicalCutOpenInterval.selected side) (CTX ctx k left right))
      (RationalMonomialWindowQuery.raw (IntegralMixedFramedWindowQuery.family PC DC HC (fun _ => 3)
        (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR) (fun _ => TERM ctx) (fun _ => index)) []) := by
    have HB : B = IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR := rfl
    have HSnap := congrArg (fun bank : IntegralFramedBankQuery.Bank =>
      IntegralMixedFramedBankSnapshotBits.atKey bank.parameters bank.plan bank.data (TERM ctx)) HB
    change IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (TERM ctx) =
      IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx) at HSnap
    have HBanks := (congrArg (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data) HK).trans HSnap
    have HW0 := congrArg (fun bank : IntegralFramedBankQuery.Bank => IntegralMixedFramedBankCoordinateBits.weight
      bank.parameters bank.plan bank.data (IntegralMixedFramedBankSnapshotBits.packet (TERM ctx) [] index 0)) HB
    change IntegralMixedFramedBankCoordinateBits.weight (B).parameters (B).plan (B).data
        (IntegralMixedFramedBankSnapshotBits.packet (TERM ctx) [] index 0) =
      IntegralMixedFramedBankCoordinateBits.weight PC DC HC
        (IntegralMixedFramedBankSnapshotBits.packet (TERM ctx) [] index 0) at HW0
    let FN := IntegralFramedPhysicalBankOrderSource.window B (IntegralMixedPhysicalCutOpenInterval.selected side)
    have HW1 : FN.weight (CTX ctx k left right) =
        IntegralMixedFramedBankCoordinateBits.weight PC DC HC
          (IntegralMixedFramedBankSnapshotBits.packet (TERM ctx) [] index 0) := by
      change IntegralMixedFramedBankCoordinateBits.weight (B).parameters (B).plan (B).data
        (IntegralMixedFramedBankSnapshotBits.packet ((B).key (CTX ctx k left right)) []
          (IntegralMixedPhysicalCutOpenInterval.selected side (CTX ctx k left right)) 0) = _
      rw [HK, HI]
      exact HW0
    have HQ0 : FN.scalars.denominator (CTX ctx k left right) =
        (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).common := congrArg (fun s => s.common) HBanks
    have HA0 : FN.scalars.numerator (CTX ctx k left right) =
        (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).cofactor index := by
      change (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key (CTX ctx k left right))).cofactor
        (IntegralMixedPhysicalCutOpenInterval.selected side (CTX ctx k left right)) = _
      rw [HI]
      exact congrArg (fun s => s.cofactor index) HBanks
    have HRaw := raw_index_heq (congrArg (fun s => s.count) HBanks)
      _ _ _ _ _ _ _ _ HQ0 HA0 HI HW1
    exact (heq_of_eq (raw_native FN (CTX ctx k left right)).symm).trans HRaw
  exact HE.trans ((heq_of_eq HN).trans HR.symm)

theorem scalar_specializes (ctx : List Bool) (k left right : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (scalar hn ht ha ctx left right))
      (IntegralFramedPhysicalBankOrderSource.polynomial B (IntegralMixedPhysicalCutOpenInterval.selected false)
        (IntegralMixedPhysicalCutOpenInterval.selected true) (CTX ctx k left right)) := by
  have HL := scalarRaw_specializes hn ht ha hR ctx k left right false hlarge
  have HR := scalarRaw_specializes hn ht ha hR ctx k left right true hlarge
  simp only [Bool.false_eq_true, ite_false, ite_true] at HL HR
  unfold scalar
  rw [map_sub]
  exact sub_heq (CoefficientMarkedRecordFullCutWordTuple.terminal_count hn ht ha hR ctx k left right).symm _ _ _ _ HR HL

attribute [local irreducible] IntegralFramedPhysicalBankOrderSource.value
  IntegralMixedPhysicalMarkedPlan.bank scalar scalarRaw raw
  IntegralFramedPhysicalBankOrderSource.polynomial IntegralFramedPhysicalBankOrderSource.raw
  IntegralFramedPhysicalSquare.scalarTuple CoefficientMarkedRecordRows.symbolic

/-- This is the literal native order value on the OWN complete sampler word.
No endpoint bounds or ordered-value assumption is needed for the arithmetic
identity, including the native zero extension of invalid selectors. -/
theorem value_eq (ctx : List Bool) (k left right : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w)
    (z : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w hv).val z) :
    IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hR false (pair (CTX ctx k left right) w) =
      InfinitesimalSign.encode (SignType.sign ((polynomial hn ht ha ctx left right).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) (CoefficientFinitePhysicalQuery.natural z))) := by
  have HS := scalar_specializes hn ht ha hR ctx k left right hlarge
  have HJ := CoefficientMarkedRecordFullCutWordTuple.scalar_tuple hn ht ha hR ctx k left right hlarge w hv z hj
  have HE := @evaluate_heq (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx)
    (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key (CTX ctx k left right))).count
    (CoefficientMarkedRecordFullCutWordTuple.terminal_count hn ht ha hR ctx k left right).symm
    (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (scalar hn ht ha ctx left right))
    (IntegralFramedPhysicalBankOrderSource.polynomial B (IntegralMixedPhysicalCutOpenInterval.selected false)
      (IntegralMixedPhysicalCutOpenInterval.selected true) (CTX ctx k left right)) HS
    (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) =>
      CoefficientFinitePhysicalQuery.natural z (scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) i.val))
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive (CTX ctx k left right) w hv) HJ.symm
  have HM := integer_evaluation (scalar hn ht ha ctx left right) (R ctx)
    (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) =>
      CoefficientFinitePhysicalQuery.natural z (scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) i.val))
  have HF := HM.symm.trans HE
  have HN := native_value B (IntegralMixedPhysicalCutOpenInterval.selected false) (IntegralMixedPhysicalCutOpenInterval.selected true)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false)
    (CTX ctx k left right) w hv
  change IntegralMixedPhysicalCutOrderedInterval.order hn ht ha hR false (pair (CTX ctx k left right) w) = _ at HN
  have HR : (polynomial hn ht ha ctx left right).eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx))
      (CoefficientFinitePhysicalQuery.natural z) =
      (scalar hn ht ha ctx left right).eval₂ (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx))
        (fun i => CoefficientFinitePhysicalQuery.natural z (scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) i.val)) :=
    MvPolynomial.eval₂_rename _ _ _ _
  exact HN.trans (congrArg (fun r : ℝ => InfinitesimalSign.encode (SignType.sign r)) (HF.symm.trans HR.symm))

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutOrderQuery
