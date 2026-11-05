/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSeries
/-! # Native ordinary/mean words supply their own complete scalar tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWordTuple
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedRoadmapProperRow CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem natural_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ) (he : HEq z w) :
    CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w := by
  cases h
  cases eq_of_heq he
  rfl

private theorem point_heq {N M : ℕ} (h : N = M) (z : Fin N → ℝ) (w : ℕ → ℝ)
    (he : ∀ i, z i = w i.val) : HEq z (fun i : Fin M => w i.val) := by
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
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false

noncomputable abbrev input (mean : Bool) := IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data
  (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)

theorem data_map (mean : Bool) (z : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    CoefficientMarkedRecordRows.map
        (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))
        (properPhysicalData hn ht ha mean z) = physicalData (B).parameters (B).plan (B).data (terminal hn ht ha hR0 mean z) :=
  proper_terminal_physical_data hn ht ha hR0 mean z hlarge

theorem terminal_count (mean : Bool) (z : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (terminal hn ht ha hR0 mean z)).count =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z) :=
  principal_terminal_count hn ht ha hR0 mean z

noncomputable abbrev nearInstalled (right : Bool) (power : Fin 3) (eta eps : Bool) :=
  IntegralFramedTerminalTarskiStatistic.mf (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) power eta eps

noncomputable abbrev rankInstalled (power : Fin 3) (eps : Bool) :=
  IntegralFramedZeroTarskiStatistic.mf (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
    (pointIndex hn ht ha hR0 true true) power eps

private theorem near_dimensions_native (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool) :
    (nearInstalled hn ht ha hR0 right power eta eps).arity z =
      (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (terminal hn ht ha hR0 false z)).count + 2 := by
  change 1 + ((IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data
    (terminal hn ht ha hR0 false z)).count + 1) = _
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed properPhysicalData

noncomputable def nearNative (right : Bool) (power : Fin 3) (eta eps : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0 false) z w) (j : ℕ) :=
  IntegralMixedFramedTerminalTarskiSelected.specialization (B).parameters (B).plan (B).data
    (terminal hn ht ha hR0 false) z
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false) z w hv)
    (FixedWidthTarskiPrincipalBits.polynomial (nearInstalled hn ht ha hR0 right power eta eps) z j)

noncomputable def rankNative (power : Fin 3) (eps : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0 true) z w) (j : ℕ) :=
  MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true) z w hv)
    (FixedWidthTarskiPrincipalBits.polynomial (rankInstalled hn ht ha hR0 power eps) z j)

/-- Every native scalar comes from THIS own full tuple at the actual radius
reader. All column, count and parameter specialization facts are derived. -/
theorem scalar_tuple (mean : Bool) (z : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0 mean) z w)
    (raw : Fin (properPhysicalData hn ht ha mean z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (input hn ht ha hR0 mean) z w hv).val raw) :
    HEq (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) z w hv)
      (CoefficientMarkedRecordProperPrincipalSeries.scalars hn ht ha mean z raw) := by
  apply point_heq (terminal_count hn ht ha hR0 mean z)
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) z w hv)
    (fun i => CoefficientFinitePhysicalQuery.natural raw (scalarAt (properPhysicalData hn ht ha mean z) i))
  exact scalar_data (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) (properPhysicalData hn ht ha mean z) _ z w
    (data_map hn ht ha hR0 mean z hlarge) hv raw hj

/-- The installed ordinary principal uses THIS own full word and the SAME
formal eta/epsilon series. Every source and coordinate map is derived. -/
theorem near_principal_eq (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0 false) z w)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (input hn ht ha hR0 false) z w hv).val raw) (j : ℕ) :
    nearNative hn ht ha hR0 right power eta eps z w hv j =
      CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) raw := by
  have HP := proper_near_principal_map hn ht ha hR0 right power eta eps z hc hg hlarge j
  rw [nearFamily_installed hn ht ha hR0] at HP
  have HN := (terminal_count hn ht ha hR0 false z).symm
  have HC := castVariables_heq
    (by omega : 1 + (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 2)
    (near_dimensions_native hn ht ha hR0 right power eta eps z) _ _ (congrArg (fun m => 1 + (m + 1)) HN) HP
  have HZ := scalar_tuple hn ht ha hR0 false z hlarge w hv raw hj
  have HE := evaluate_heq HN _ _ HC (CoefficientMarkedRecordProperPrincipalSeries.scalars hn ht ha false z raw)
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false) z w hv) HZ.symm
  have HM := evaluate_integer_map
    (by omega : 1 + (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 2)
    (properNearPrincipal hn ht ha right power eta eps z hc j)
    (IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z))
    (CoefficientMarkedRecordProperPrincipalSeries.scalars hn ht ha false z raw)
  have HF := HM.symm.trans HE
  change CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
    ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n false z)) raw =
      nearNative hn ht ha hR0 right power eta eps z w hv j at HF
  exact HF.symm

/-- The installed mean-zero principal uses its OWN mean word, not the
ordinary word or a transported ordinal label. -/
theorem rank_principal_eq (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0 true) z w)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (input hn ht ha hR0 true) z w hv).val raw) (j : ℕ) :
    rankNative hn ht ha hR0 power eps z w hv j =
      CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) raw := by
  have HP := proper_rank_principal_map hn ht ha hR0 power eps z hc hg hlarge j
  rw [rankFamily_installed hn ht ha hR0] at HP
  have HN := (terminal_count hn ht ha hR0 true z).symm
  have HZ := scalar_tuple hn ht ha hR0 true z hlarge w hv raw hj
  have HE := evaluate_heq HN _ _ HP (CoefficientMarkedRecordProperPrincipalSeries.scalars hn ht ha true z raw)
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data
      (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true) z w hv) HZ.symm
  have HM := evaluate_map (evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)))
    (Int.castRingHom ℝ) (CoefficientMarkedRecordProperPrincipalSeries.scalars hn ht ha true z raw)
    (properRankPrincipal hn ht ha power eps z hc j)
  rw [scalar_evaluation] at HM
  have HF := HM.symm.trans HE
  change CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
    ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n true z)) raw =
      rankNative hn ht ha hR0 power eps z w hv j at HF
  exact HF.symm

end LeanCanny.Encoding.CoefficientMarkedRecordProperWordTuple
