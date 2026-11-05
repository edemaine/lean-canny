/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowFields
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedSelected

/-! # Original structural keys for ordinary and mean-coordinate rank queries

The catalog uses original candidate/history bytes and coordinate metadata.
No radius or sampler-word interpretation occurs in its definitions. The
actual saved parent is identified only on its genuine accepted domain.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}

def catalogDimension (n : List Bool → ℕ) (z : List Bool) := n (IntegralMixedRoadmapAtomic.original (atomic z)) + 3
def catalogInitial (n : List Bool → ℕ) (z : List Bool) := n (IntegralMixedRoadmapAtomic.original (atomic z)) + 8
def catalogCreating (n : List Bool → ℕ) (z : List Bool) :=
  IntegralMixedRoadmapBadProbePacket.creating (catalogInitial n z) (oldPacket z)
noncomputable def catalogCode (n : List Bool → ℕ) (mean : Bool) (z : List Bool) := if mean then
  IntegralMixedChronologicalMeanCutCode.code (catalogDimension n z) (labels z)
    (oldProducer false z) (oldProducer true z) (offset z) (coordinate z) 0 0 0
  else IntegralMixedChronologicalCutCode.code (catalogDimension n z) (labels z) (offset z) (coordinate z) 0 0 0
noncomputable def catalogRoot (n : List Bool → ℕ) (mean : Bool) (z : List Bool) :=
  pair (IntegralMixedRoadmapAtomic.candidate (atomic z))
    (pair (WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z) ++ [catalogCode n mean z])) [])
noncomputable def catalogTerminal (n : List Bool → ℕ) (mean : Bool) (z : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (catalogRoot n mean z)
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)) []
noncomputable def catalogParent (n : List Bool → ℕ) (mean : Bool) (z : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (catalogRoot n mean z) (catalogCreating n z) (BinaryNatCode.encode 2)

theorem catalog_ignores_word (n : List Bool → ℕ) (mean : Bool) (c payload w w' index : List Bool) :
    catalogRoot n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w) index) =
      catalogRoot n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w') index) ∧
    catalogTerminal n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w) index) =
      catalogTerminal n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w') index) ∧
    catalogParent n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w) index) =
      catalogParent n mean (pair (IntegralMixedRoadmapAtomic.packet c payload w') index) := by
  simp only [catalogRoot, catalogTerminal, catalogParent, catalogCreating, catalogCode,
    catalogDimension, catalogInitial, labels, oldProducer, offset, coordinate, oldPacket, atomic,
    IntegralMixedRoadmapProper.badPacket, IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapProper.producer, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload,
    IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapBadProbePacket.creating, IntegralMixedRoadmapBadProbePacket.prefixCodes,
    IntegralMixedRoadmapBadProbePacket.count, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]
  exact ⟨trivial, trivial, trivial⟩

variable (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

private theorem marked_width {R : List Bool → ℕ} (hR : BinaryFn R) (r : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.width r =
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width r := by
  simp only [IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,
    IntegralMixedFramedNormalizationBits.planned]

private theorem family_ambient (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key = P.ambient (pairFst key) := rfl

private theorem family_degree (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).spatial key).degree = P.degree (pairFst key) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_spatial]
  exact H.degree_eq key

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem dimension_catalog (z : List Bool) : dimension hn ht ha hR0 z = catalogDimension n z :=
  IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 (atomic z)

theorem initial_catalog (z : List Bool) : initial hn ht ha hR0 z = catalogInitial n z :=
  IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 (atomic z)

theorem creating_catalog (z : List Bool) : creating hn ht ha hR0 z = catalogCreating n z := by
  unfold creating catalogCreating
  rw [initial_catalog]

theorem code_catalog (mean : Bool) (z : List Bool) : code hn ht ha hR0 mean z = catalogCode n mean z := by
  unfold code catalogCode
  rw [dimension_catalog]

theorem root_catalog (mean : Bool) (z : List Bool) : root hn ht ha hR0 mean z = catalogRoot n mean z := by
  unfold root raw catalogRoot
  rw [code_catalog]

theorem terminal_catalog (mean : Bool) (z : List Bool) :
    terminal hn ht ha hR0 mean z = catalogTerminal n mean z := by
  simp only [terminal, Function.comp_apply, IntegralMixedPhysicalMarkedPlan.bank,
    Bool.false_eq_true, ite_false, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, context, pairFst_pair, catalogTerminal, root_catalog]

theorem parentKey_catalog (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    parentKey hn ht ha hR0 mean z = catalogParent n mean z := by
  rw [parentKey_aux hn ht ha hR0 mean z hv, root_catalog, creating_catalog]
  rfl

theorem coordinate_catalog (mean : Bool) (z : List Bool)
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    get (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters Field.slot13
      (parent hn ht ha hR0 mean z) = relativeCoordinate z :=
  parent_coordinate hn ht ha hR0 mean z hg

theorem parameter_catalog (mean : Bool) (z : List Bool) :
    IntegralMixedSelectedCoordinateHead.fullParameter
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (parent hn ht ha hR0 mean) z =
      2 ^ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (catalogRoot n mean z) - 1 := by
  unfold IntegralMixedSelectedCoordinateHead.fullParameter
  rw [parent_root, root_catalog]
  rw [marked_width hn ht ha (radius_binary hR0)]

noncomputable def catalogDegree (mean : Bool) (z : List Bool) :=
  PurePowerReductionBounds.dimension (catalogDimension n z - offset z + 1)
    ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).degree (catalogRoot n mean z))

theorem degree_catalog (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    IntegralMixedSelectedCoordinateHead.fullDegree
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedFramedHistoryFamilyBits.family
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).data)
      (parent hn ht ha hR0 mean) z = catalogDegree hn ht ha mean z := by
  rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
  change PurePowerReductionBounds.dimension
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).ambient (parentKey hn ht ha hR0 mean z) -
      ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).rule (parentKey hn ht ha hR0 mean z)).critical.offset.val + 1)
    ((IntegralMixedFramedHistoryFamilyBits.family _ _ _).spatial (parentKey hn ht ha hR0 mean z)).degree = _
  rw [rule_offset hn ht ha hR0 mean z hv hg, family_degree, family_ambient, parentKey_root,
    root_dimension, dimension_catalog, root_catalog]
  simp only [catalogDegree, IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,
    IntegralMixedFramedNormalizationBits.planned]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
