/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessLayout
/-! # Actual principal series depend on history metadata, not its sampled word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperSeriesErasure
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWitnessLayout
open CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem coordinate_request (z word : List Bool) : coordinate (request z word) = coordinate z := by
  simp only [coordinate, request, pairSnd_pair]
private theorem offset_request (z word : List Bool) : offset (request z word) = offset z := by
  simp only [offset, request, atomic, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapAtomic.depth, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]
private theorem dimension_request (n : List Bool → ℕ) (z word : List Bool) :
    catalogDimension n (request z word) = catalogDimension n z := by
  simp only [catalogDimension, request, atomic, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.candidate, pairFst_pair]
private theorem initial_request (n : List Bool → ℕ) (z word : List Bool) :
    catalogInitial n (request z word) = catalogInitial n z := by
  simp only [catalogInitial, request, atomic, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.candidate, pairFst_pair]
private theorem creating_request (n : List Bool → ℕ) (z word : List Bool) :
    catalogCreating n (request z word) = catalogCreating n z := by
  rw [catalogCreating, catalogCreating, initial_request]
  unfold IntegralMixedRoadmapBadProbePacket.creating
  rw [count_request]
private theorem producer_request (right : Bool) (z word : List Bool) :
    oldProducer right (request z word) = oldProducer right z := by
  simp only [oldProducer, request, atomic, IntegralMixedRoadmapProper.producer,
    IntegralMixedRoadmapProper.levelIndex, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]
private theorem pointProducer_request (n : List Bool → ℕ) (mid : Bool) (z word : List Bool) :
    catalogPointProducer (n := n) mid (request z word) = catalogPointProducer (n := n) mid z := by
  simp only [catalogPointProducer, dimension_request, initial_request, coordinate_request]
  simp only [request, atomic, IntegralMixedRoadmapProper.midFirst, IntegralMixedRoadmapProper.midBirth,
    IntegralMixedRoadmapProper.baseBirth, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapAtomic.first, IntegralMixedRoadmapAtomic.anchor, IntegralMixedRoadmapAtomic.free,
    IntegralMixedRoadmapAtomic.endBirth, IntegralMixedRoadmapAtomic.depth, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

theorem data_request (mean : Bool) (z word : List Bool) :
    properPhysicalData hn ht ha mean (request z word) = properPhysicalData hn ht ha mean z := by
  exact congrArg (fun ctx => CoefficientMarkedRecordRows.symbolic hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl) (catalogRoot_request n mean z word)

theorem degree_request (mean : Bool) (z word : List Bool) :
    catalogDegree hn ht ha mean (request z word) = catalogDegree hn ht ha mean z := by
  unfold catalogDegree
  rw [catalogRoot_request, dimension_request, offset_request]

@[ext] private structure Description (n : List Bool → ℕ) where
  root : List Bool
  stage : ℕ
  coordinate : ℕ
  degree : ℕ
  shiftDegree : ℕ
  center : ℕ
  selected : ℕ
  castArity : 1 + (CoefficientMarkedRecordCutSource.birth (n := n) root stage + 1) =
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root + 1

private noncomputable def description (mean right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) : Description n :=
  ⟨catalogRoot n mean z, catalogStage z, relativeCoordinate z, catalogDegree hn ht ha mean z,
    catalogShiftDegree hn ht ha mean z, catalogCenterIndex (n := n) right z,
    catalogPointIndex (n := n) mean mean z, proper_terminal_cast_arity hn ht ha mean z hc⟩

private noncomputable def rawData (ctx : List Bool) := CoefficientMarkedRecordRows.symbolic hn ht ha ctx
  (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl

private noncomputable def head (d : Description n) :=
  castHead d.castArity (pairLift true (CoefficientMarkedRecordCoordinateHead.polynomial hn ht ha d.root d.stage
    ⟨d.coordinate % _, Nat.mod_lt _ (Nat.succ_pos _)⟩ d.degree
    (2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width d.root-1)))

private noncomputable def weight (ctx : List Bool) (i : ℕ) :=
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let m := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx
  UniformIntegralPowerSchedule.birth (P.cap ctx+1) (2^P.width ctx) (m-1-min i m)

private noncomputable def recipe (mean : Bool) (power : Fin 3) (eta eps : Bool) (j : ℕ) (d : Description n)
    (β : ℝ) (raw : Fin (rawData hn ht ha d.root).count → ℝ) :=
  let m := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n d.root
  let Q := CoefficientMarkedRecordBankProducts.common hn ht ha d.root (IntegralMixedCausalRecordPlanBits.count d.root)
  let cofactor := CoefficientMarkedRecordBankProducts.cofactor hn ht ha d.root (IntegralMixedCausalRecordPlanBits.count d.root)
  let W := window (m := m) Q (cofactor d.selected) d.selected (weight hn ht ha d.root d.selected) eps
  let P := if mean then
    principal (CoefficientTarskiZeroParameterQueries.zeroHead (head hn ht ha d))
      (CoefficientTarskiZeroParameterQueries.epsilonHead W^power.val) (max 1 d.degree)
      (max 1 d.degree-1) (max 1 d.degree+2) j
    else
      castVariables (by omega : 1+(m+1)=m+2)
        (principal (pairLift true (shiftedHead (head hn ht ha d) d.shiftDegree Q (cofactor d.center)
          d.center (weight hn ht ha d.root d.center) eta)) (pairLift false W^power.val)
          (max 1 d.degree) (max 1 d.degree-1) (max 1 d.degree+2) j)
  MvTwoParameterCoefficient.evaluate (SymbolicScaledSquarefree.scalarEvaluation β)
    (fun i : Fin m => CoefficientFinitePhysicalQuery.natural raw (scalarAt (rawData hn ht ha d.root) i.val)) P

private theorem near_factor (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :
    CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j =
      recipe hn ht ha false power eta eps j (description hn ht ha false right z hc) := rfl

private theorem rank_factor (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :
    CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j =
      recipe hn ht ha true power false eps j (description hn ht ha true false z hc) := rfl

private theorem description_request (mean right : Bool) (z word : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    description hn ht ha mean right (request z word) ((count_request z word).symm ▸ hc) =
      description hn ht ha mean right z hc := by
  apply Description.ext
  all_goals
    simp only [description, catalogRoot_request, catalogStage, count_request, relativeCoordinate,
      coordinate_request, offset_request, catalogDegree, dimension_request, catalogShiftDegree,
      catalogNativeWidth, catalogPackedDegree, creating_request, catalogCenterIndex, producer_request,
      catalogPointIndex, pointProducer_request]

private theorem recipe_congr (mean : Bool) (power : Fin 3) (eta eps : Bool) (j : ℕ)
    (d e : Description n) (h : d = e) : HEq (recipe hn ht ha mean power eta eps j d)
      (recipe hn ht ha mean power eta eps j e) := by
  cases h
  rfl

/-- The literal factory is factored through derived numerical descriptors;
its physical raw tuple is never replaced or independently chosen. -/
theorem near_function_heq (right : Bool) (power : Fin 3) (eta eps : Bool) (z word : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :
    HEq (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps (request z word)
      ((count_request z word).symm ▸ hc) j)
      (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j) := by
  rw [near_factor hn ht ha, near_factor hn ht ha]
  exact recipe_congr hn ht ha false power eta eps j _ _ (description_request hn ht ha false right z word hc)

theorem rank_function_heq (power : Fin 3) (eps : Bool) (z word : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) :
    HEq (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps (request z word)
      ((count_request z word).symm ▸ hc) j)
      (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j) := by
  rw [rank_factor hn ht ha, rank_factor hn ht ha]
  exact recipe_congr hn ht ha true power false eps j _ _ (description_request hn ht ha true false z word hc)

end LeanCanny.Encoding.CoefficientMarkedRecordProperSeriesErasure
