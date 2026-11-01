/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeNativeSource
public import LeanCanny.Algebra.IntegralMixedValueCoordinateChild
public import LeanCanny.Computation.NativeSingleCallBranch
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
/-! # The literal PSC source over the saved first-nilpotent parent

Slot 8 is the PSC index, slots 9 and 10 are its spatial row and column,
and slot 13 retains the selected coordinate. The matrix reference is
mathematical; only its actual numeric metadata receive native readers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis

noncomputable def degree (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralMixedCoordinateSquarefree.coordinateDegree
    ((IntegralMixedVirtualTaskBits.family P F).spatial q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
theorem degree_pos (P : Parameters) (F : Family) (q : List Bool) : 0 < degree P F q :=
  Nat.pow_pos (Nat.two_pow_pos _)
noncomputable def index (P : Parameters) (F : Family) (q : List Bool) : Fin (degree P F q) :=
  ⟨get P .slot8 q % degree P F q, Nat.mod_lt _ (degree_pos P F q)⟩
noncomputable def parameters (P : Parameters) (F : Family) : PrincipalDerivativeEntryRequest.Parameters where
  degree := degree P F
  index q := (index P F q).val
  modulus := modulus P

theorem degree_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (degree P F) :=
  IntegralMixedValueDeterminantMetadata.coordinateDegree_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)
theorem index_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (fun q => (index P F q).val) := (get_binary P a .slot8).mod (degree_binary P a F h)
theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    PrincipalDerivativeEntryRequest.Controls (parameters P F) :=
  ⟨degree_binary P a F h, index_binary P a F h, modulus_binary P a⟩

def packet (P : Parameters) (q : List Bool) : List Bool :=
  pair (IntegralBlockMomentBits.context q (get P .row q) (get P .col q))
    (pair (BinaryNatCode.encode (get P .slot9 q)) (BinaryNatCode.encode (get P .slot10 q)))
theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (mem_FP_pair (get_binary P a .row).bits_mem_FP (get_binary P a .col).bits_mem_FP))
    (mem_FP_pair (get_binary P a .slot9).bits_mem_FP (get_binary P a .slot10).bits_mem_FP)
theorem packet_original (P : Parameters) (q : List Bool) : PrincipalDerivativeEntryRequest.original (packet P q) = q := by
  simp only [packet, PrincipalDerivativeEntryRequest.original, IntegralBerkowitzBlockBits.original,
    IntegralBlockMomentBits.context, pairFst_pair]

noncomputable def source (P : Parameters) (F : Family) : IntegralBerkowitzBlockBits.Source :=
  { IntegralMixedSquarefreeNativeSource.source (IntegralMixedVirtualTaskBits.family P F)
      (IntegralMixedVirtualTaskBits.indices P F) (index P F) with coefficient _ := 0 }
noncomputable def rank (P : Parameters) (F : Family) (q : List Bool) := (source P F).rank q
noncomputable def dimension (P : Parameters) (F : Family) (q : List Bool) := (source P F).dimension q

theorem rank_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (rank P F) :=
  IntegralMixedVirtualNativeBits.rank_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)
theorem dimension_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (dimension P F) :=
  ((degree_binary P a F h).sub (index_binary P a F h)).add
    (((degree_binary P a F h).sub (BinaryFn.const 1)).sub (index_binary P a F h))

noncomputable def table (P : Parameters) (F : Family) (q : List Bool) (i j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r t) i j
noncomputable def integerValue (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  table P F q (get P .slot9 q) (get P .slot10 q) (get P .row q) (get P .col q)
noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerValue P F q : ZMod (modulus P q))

theorem table_finite (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q)) :
    table P F q i.val j.val r.val t.val = (source P F).entryMatrix q i j r t :=
  (IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (fun a b => IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).entryMatrix q a b) r.val t.val) i j).trans
      (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((source P F).entryMatrix q i j) r t)

end LeanCanny.Algebra.IntegralMixedPscEntryBits
