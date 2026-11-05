/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutLex
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutInstalled
/-! # Own complete words supply the literal scalar tuple for full-cut principals -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordTuple
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem natural_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ) (he : HEq z w) :
    CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w := by
  cases h
  cases eq_of_heq he
  rfl

private theorem point_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : ℕ → ℝ) (he : ∀ i, z i = w i.val) :
    HEq z (fun i : Fin M => w i.val) := by
  cases h
  exact heq_of_eq (funext he)

private theorem scalar_data (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool → List Bool)
    (hp : ∀ c, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
    (E : CoefficientMarkedRecordRows.Data ℤ[X]) (φ : ℤ[X] →+* ℤ) (c w : List Bool)
    (he : CoefficientMarkedRecordRows.map φ E = physicalData P D H (key c))
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w)
    (z : Fin E.count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv).val z)
    (i : Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count) :
    IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hp c w hv i =
      CoefficientFinitePhysicalQuery.natural z (scalarAt E i.val) := by
  have hc : (IntegralFramedPhysicalSquare.input P D H L F C hs key hp).count c = E.count :=
    (congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => d.count) he).symm
  have hn := natural_heq hc _ z hj
  have hi : i.val < (physicalData P D H (key c)).birth := i.isLt
  have ha := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ => scalarAt d i.val) he
  change scalarAt E i.val = scalarAt (physicalData P D H (key c)) i.val at ha
  have hb : scalarAt (physicalData P D H (key c)) i.val =
      (IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) i).val := by
    rw [scalarAt, dite_eq_left hi]
    rfl
  rw [IntegralFramedPhysicalSquare.scalarTuple_map, ha, hb]
  let j := IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) i
  change (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv).val j = _
  exact (show CoefficientFinitePhysicalQuery.natural
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv).val j.val =
      (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv).val j from dite_eq_left j.isLt).symm.trans
    (congrFun hn j.val)

private theorem evaluate_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}
    (φ : R →+* S) (ψ : S →+* ℝ) (z : Fin m → ℝ) (p : MvPolynomial (Fin (m+2)) R) :
    MvTwoParameterCoefficient.evaluate ψ z (MvPolynomial.map φ p) =
      MvTwoParameterCoefficient.evaluate (ψ.comp φ) z p := by
  apply Polynomial.ext
  intro delta
  apply Polynomial.ext
  intro epsilon
  rw [MvTwoParameterCoefficient.selected_coefficient, MvTwoParameterCoefficient.selected_coefficient,
    ← slice_map, MvPolynomial.eval₂_map]

private theorem evaluate_heq {N M : ℕ} (h : N = M)
    (p : MvPolynomial (Fin (N+2)) ℤ) (q : MvPolynomial (Fin (M+2)) ℤ) (hp : HEq p q)
    (z : Fin N → ℝ) (w : Fin M → ℝ) (hz : HEq z w) :
    MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z p =
      MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) w q := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) = SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

private theorem evaluate_integer_map {N M : ℕ} (h : N = M+2) (p : MvPolynomial (Fin N) ℤ[X])
    (r : ℕ) (z : Fin M → ℝ) :
    MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z
      (castVariables h (MvPolynomial.map (evalRingHom ((2 : ℤ)^r)) p)) =
    MvTwoParameterCoefficient.evaluate (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r)) z
      (castVariables h p) := by
  rw [← castVariables_map, evaluate_map, scalar_evaluation]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "E" => CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem terminal_data (ctx : List Bool) (k left right : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R ctx)) (E ctx) =
      physicalData (B).parameters (B).plan (B).data ((B).key (CTX ctx k left right)) := by
  have he := CoefficientMarkedRecordFullCutPhysical.terminal_data hn ht ha hR ctx hlarge
  have hk := CoefficientMarkedRecordFullCutInstalled.terminal_context hn ht ha hR ctx k left right
  exact he.trans (congrArg (physicalData (B).parameters (B).plan (B).data) hk.symm)

theorem terminal_count (ctx : List Bool) (k left right : ℕ) :
    (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key (CTX ctx k left right))).count =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  have hk := CoefficientMarkedRecordFullCutInstalled.terminal_context hn ht ha hR ctx k left right
  exact (congrArg (fun key => (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data key).count) hk).trans
    (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx)

theorem scalar_tuple (ctx : List Bool) (k left right : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w)
    (z : Fin (E ctx).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w hv).val z) :
    HEq (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive (CTX ctx k left right) w hv)
      (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) => CoefficientFinitePhysicalQuery.natural z (scalarAt (E ctx) i.val)) := by
  apply point_heq (terminal_count hn ht ha hR ctx k left right)
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive (CTX ctx k left right) w hv)
    (fun i => CoefficientFinitePhysicalQuery.natural z (scalarAt (E ctx) i))
  exact scalar_data (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
      (E ctx) _ (CTX ctx k left right) w (terminal_data hn ht ha hR ctx k left right hlarge) hv z hj

theorem dimensions (side negative : Bool) (q : List Bool) :
    (CoefficientMarkedRecordFullCutInstalled.installedFamily hn ht ha hR side 1 negative).arity q =
      (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key q)).count+2 := by
  change 1+((IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key q)).count+1) =
    (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key q)).count+2
  omega

noncomputable def nativePrincipal (side negative : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w) (j : ℕ) :=
  IntegralMixedFramedTerminalTarskiSelected.specialization (B).parameters (B).plan (B).data (B).key q
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive q w hv)
    (FixedWidthTarskiPrincipalBits.polynomial (CoefficientMarkedRecordFullCutInstalled.installedFamily hn ht ha hR side 1 negative) q j)

/-- Exact principal identity for the OWN decoded word. The entire native
metadata and scalar embedding are derived; no interpreting factor hom or
specialized degree premise is introduced. -/
theorem principal_eq (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) (side negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w)
    (z : Fin (E ctx).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w hv).val z) (j : ℕ) :
    nativePrincipal hn ht ha hR side negative (CTX ctx k left right) w hv j =
      CoefficientMarkedRecordFullCutLex.principal hn ht ha ctx k hk (if side then right else left) negative j ((2 : ℝ)^R ctx) z := by
  have HP := CoefficientMarkedRecordFullCutInstalled.specializes hn ht ha hR ctx k hk hc left right side 1 negative hlarge j
  have HN := (terminal_count hn ht ha hR ctx k left right).symm
  have HC := castVariables_heq
    (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) = IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+2)
    (dimensions hn ht ha hR side negative (CTX ctx k left right)) _ _ (congrArg (fun m => 1+(m+1)) HN) HP
  have HZ := scalar_tuple hn ht ha hR ctx k left right hlarge w hv z hj
  have HE := evaluate_heq HN _ _ HC
    (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) =>
      CoefficientFinitePhysicalQuery.natural z (scalarAt (E ctx) i.val))
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive (CTX ctx k left right) w hv) HZ.symm
  have HM := evaluate_integer_map
    (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) = IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+2)
    (CoefficientMarkedRecordFullCutPrincipal.polynomial hn ht ha ctx k hk (if side then right else left) 1 negative j)
    (R ctx) (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) =>
      CoefficientFinitePhysicalQuery.natural z (scalarAt (E ctx) i.val))
  have HF := HM.symm.trans HE
  change CoefficientMarkedRecordFullCutLex.principal hn ht ha ctx k hk (if side then right else left) negative j ((2 : ℝ)^R ctx) z =
    nativePrincipal hn ht ha hR side negative (CTX ctx k left right) w hv j at HF
  exact HF.symm

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordTuple
