/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCenter
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalSelection
/-! # Coordinate selection changes only auxiliary metadata of the joint node -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

-- The child packet is pair originalJointPacket binaryCoordinate.
def indexedPacket (z : List Bool) := pair (node (pairFst z))
  (pair (metadata (pairFst z)) (pairSnd z))
def indexed (p : List Bool) (i : ℕ) := indexedPacket (pair p (BinaryNatCode.encode i))
noncomputable def indexedRadial (c : List Bool) := FormulaSignSlotRadialCoordinatePacket.writer
  (pair (radialContext c) (pairSnd (pairSnd c)))

theorem indexedPacket_FP : indexedPacket ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP node_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
theorem indexedRadial_FP : indexedRadial ∈ FP := mem_FP_comp
  (mem_FP_pair radialContext_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
  FormulaSignSlotRadialCoordinatePacket.writer_FP

theorem indexed_node (p : List Bool) (i : ℕ) : node (indexed p i) = node p := by
  simp only [indexed, indexedPacket, pairFst_pair, node]
theorem indexed_word (p : List Bool) (i : ℕ) : word (indexed p i) = word p :=
  congrArg IntegralMixedRoadmapAtomic.word (indexed_node p i)
theorem indexed_header (p : List Bool) (i : ℕ) : header (indexed p i) = header p := by
  unfold header
  rw [indexed_node]
theorem indexed_valid (p : List Bool) (i : ℕ) (hv : Valid p) : Valid (indexed p i) := by
  unfold Valid
  rw [indexed_node]
  exact hv

theorem indexed_source (p : List Bool) (i : ℕ) : indexedRadial (context (indexed p i)) =
    FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p)) i := by
  have HH : radialContext (context (indexed p i)) = FormulaSignSlotRadialJointLayout.source true (header p) := by
    simp only [radialContext, header_context, indexed_header]
  unfold indexedRadial
  rw [HH]
  have HI : pairSnd (pairSnd (context (indexed p i))) = BinaryNatCode.encode i := by
    simp only [context, metadata, indexed, indexedPacket, pairSnd_pair, pairFst_pair]
  rw [HI]
  exact FormulaSignSlotRadialCoordinatePacket.writer_packet _ _

theorem indexed_values (p : List Bool) (i : ℕ) (hv : Valid p) :
    values (indexed p i) (indexed_valid p i hv) = values p hv := by
  unfold values
  congr 1
  exact indexed_node p i

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
