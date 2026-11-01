/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReciprocalEntryRequest
public import LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata

/-! # Actual native metadata for the reciprocal digit selector

Both formal digits use the one original cap. The original spatial degree
fits the homogeneous exponent width; it is never replaced by an absolute
norm degree. Deleting the second digit returns an actual first-prefix
basis index, without clamping invalid incoming labels.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueSystemControls
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits

noncomputable def parameters (F : Family) (I : Indices F) : IntegralReciprocalEntryRequest.Parameters where
  free q := F.ambient q - (F.rule q).critical.offset.val + 1
  width q := IntegralMixedGridValue.width (F.spatial q) (F.rule q)
  digit q := 2 ^ F.width q
  oldRank q := count (F.birth q + 1) (F.width q)
  degree q := (F.spatial q).degree
  modulus := I.modulus

theorem controls (F : Family) (I : Indices F) (h : Metadata F I) :
    IntegralReciprocalEntryRequest.Controls (parameters F I) where
  free := free_unary F I h
  width := IntegralMixedValueDeterminantMetadata.width_unary F I h
  digit := (BinaryFn.const 2).powUnary h.width
  oldRank := rank_binary F I h
  degree := h.degree
  modulus := h.modulus

noncomputable abbrev program (F : Family) (I : Indices F) :=
  IntegralReciprocalEntryRequest.program (parameters F I)

theorem program_controls (F : Family) (I : Indices F) (h : Metadata F I) : (program F I).Controls :=
  IntegralReciprocalEntryRequest.controls _ (controls F I h)

theorem rank_eq (F : Family) (I : Indices F) (q : List Bool) :
    (parameters F I).oldRank q * (parameters F I).digit q = count (F.birth q + 2) (F.width q) := by
  change count (F.birth q + 1) (F.width q) * 2 ^ F.width q = _
  unfold count
  exact (pow_succ (2 ^ F.width q) (F.birth q + 1)).symm

theorem degree_lt (F : Family) (I : Indices F) (q : List Bool) :
    (parameters F I).degree q < 2 ^ (parameters F I).width q := by
  have HD := (F.spatial q).degree_two
  have HL := IntegralMixedValueDeterminantMetadata.level_eq (F.spatial q) (F.rule q)
  have HB : (F.spatial q).degree ≤ Macaulay.level (RelativeProjectiveValueGram.degrees
      (fun _ : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) =>
        IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) (F.spatial q).degree) := by
    rw [HL]
    omega
  exact HB.trans_lt (Nat.lt_size_self _)

theorem oldRow_lt (F : Family) (I : Indices F) (p : List Bool)
    (h : IntegralReciprocalEntryRequest.valid (parameters F I) p) :
    IntegralReciprocalEntryRequest.oldRow (parameters F I) p < (parameters F I).oldRank (MacaulayFullBoxBits.ctx p) := by
  have HD : 0 < (parameters F I).digit (MacaulayFullBoxBits.ctx p) := Nat.two_pow_pos _
  exact (Nat.div_lt_iff_lt_mul HD).mpr h.2.2.1

theorem oldCol_lt (F : Family) (I : Indices F) (p : List Bool)
    (h : IntegralReciprocalEntryRequest.valid (parameters F I) p) :
    IntegralReciprocalEntryRequest.oldCol (parameters F I) p < (parameters F I).oldRank (MacaulayFullBoxBits.ctx p) := by
  have HD : 0 < (parameters F I).digit (MacaulayFullBoxBits.ctx p) := Nat.two_pow_pos _
  exact (Nat.div_lt_iff_lt_mul HD).mpr h.2.2.2

end LeanCanny.Algebra.IntegralMixedValueSystemControls
