/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalCriticalAccess
/-! # Query snapshots of a physical critical source over a saved mixed prefix

The saved semantic input is an explicit word map, independent of phase,
coefficient, derivative, and row fields. Equality of saved words gives
value transport by a canonical natural-index matrix model.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

noncomputable def pull (F : Family) (base : List Bool → List Bool) : Family where
  ambient := F.ambient ∘ base
  cap := F.cap ∘ base
  width := F.width ∘ base
  birth := F.birth ∘ base
  physical := F.physical ∘ base
  spatial q := F.spatial (base q)
  state q := F.state (base q)
  birth_bound q := F.birth_bound (base q)
  rule q := F.rule (base q)

structure InputMetadata (F : Family) : Prop where
  ambient : UnaryFn F.ambient
  birth : UnaryFn F.birth
  width : UnaryFn F.width
  offset : UnaryFn (fun q => (F.rule q).offset.val)
  degree : BinaryFn (fun q => (F.spatial q).degree)
  objective : BinaryFn (fun q => (F.rule q).objective)

theorem pull_metadata (F : Family) (h : InputMetadata F) (base : List Bool → List Bool) (hb : base ∈ FP) :
    InputMetadata (pull F base) where
  ambient := h.ambient.comp hb
  birth := h.birth.comp hb
  width := h.width.comp hb
  offset := h.offset.comp hb
  degree := h.degree.comp hb
  objective := h.objective.comp hb

structure Queries where
  coordinate : List Bool → ℕ
  coefficientIndex : List Bool → ℕ
  target : List Bool → ℕ
  row : List Bool → ℕ
  col : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ q, modulus q ≠ 0

structure QueryMetadata (Q : Queries) : Prop where
  coordinate : BinaryFn Q.coordinate
  coefficientIndex : BinaryFn Q.coefficientIndex
  target : BinaryFn Q.target
  row : BinaryFn Q.row
  col : BinaryFn Q.col
  modulus : BinaryFn Q.modulus

noncomputable def indices (F : Family) (Q : Queries) : Indices F where
  coordinate q := ⟨Q.coordinate q % (F.ambient q - (F.rule q).offset.val + 1), Nat.mod_lt _ (by omega)⟩
  coefficientIndex := Q.coefficientIndex
  target := Q.target
  row q := ⟨Q.row q % count (F.birth q) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  col q := ⟨Q.col q % count (F.birth q) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  modulus := Q.modulus
  modulus_ne_zero := Q.modulus_ne_zero

theorem metadata (F : Family) (h : InputMetadata F) (Q : Queries) (a : QueryMetadata Q) :
    Metadata F (indices F Q) where
  ambient := h.ambient
  birth := h.birth
  width := h.width
  offset := h.offset
  degree := h.degree
  objective := h.objective
  target := a.target
  row := a.row.mod (((BinaryFn.const 2).powUnary h.width).powUnary h.birth)
  col := a.col.mod (((BinaryFn.const 2).powUnary h.width).powUnary h.birth)
  modulus := a.modulus
  coordinate := a.coordinate.mod (BinaryFn.ofUnary ((h.ambient.sub h.offset).add (UnaryFn.const 1)))
  coefficientIndex := a.coefficientIndex

def taskQueries (P : IntegralCriticalHistoryTask.Parameters) (coordinate : List Bool → ℕ) : Queries where
  coordinate := coordinate
  coefficientIndex := IntegralCriticalHistoryTask.get P .coefficient
  target := IntegralCriticalHistoryTask.get P .target
  row := IntegralCriticalHistoryTask.get P .row
  col := IntegralCriticalHistoryTask.get P .col
  modulus := IntegralCriticalHistoryTask.modulus P
  modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero P

theorem task_metadata (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (coordinate : List Bool → ℕ) (hc : BinaryFn coordinate) : QueryMetadata (taskQueries P coordinate) where
  coordinate := hc
  coefficientIndex := IntegralCriticalHistoryTask.get_binary P a .coefficient
  target := IntegralCriticalHistoryTask.get_binary P a .target
  row := IntegralCriticalHistoryTask.get_binary P a .row
  col := IntegralCriticalHistoryTask.get_binary P a .col
  modulus := IntegralCriticalHistoryTask.modulus_binary P a

noncomputable def polynomial (F : Family) (q : List Bool) (j : ℕ) : Polynomial (F.state q).sampler.scalarPrefix.carrier :=
  CoordinateFrozenCriticalElimination.polynomial (F.spatial q).degree
    (IntegralMixedHistory.data (F.state q) (F.birth_bound q) (F.rule q)).scales
    (IntegralMixedHistory.data (F.state q) (F.birth_bound q) (F.rule q)).heights
    (F.rule q).offset.val (by have H := (F.rule q).offset.isLt; omega)
    ((F.spatial q).low.map (Int.castRingHom _)) ((F.spatial q).leading : _)
    ⟨(F.rule q).objective % (F.ambient q - (F.rule q).offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨j % (F.ambient q - (F.rule q).offset.val + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def matrixCoefficient (F : Family) (q : List Bool) (j k r t : ℕ) : ℤ := by
  letI := (F.state q).sampler.scalarPrefix.ring
  exact Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
    ((polynomial F q j).coeff k)
    ⟨r % count (F.birth q) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count (F.birth q) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem value_snapshot (F : Family) (Q : Queries) (q : List Bool) :
    (source F (indices F Q)).value q =
      residueBits (matrixCoefficient F q (Q.coordinate q) (Q.coefficientIndex q) (Q.row q) (Q.col q) : ZMod (Q.modulus q)) := by
  rw [IntegralMixedPhysicalCriticalBits.value_eq]
  unfold IntegralMixedPhysicalCriticalBits.value
  rw [IntegralMixedPhysicalCriticalBits.annihilator_eq]
  rfl

theorem matrix_pull (F : Family) (base : List Bool → List Bool) (q : List Bool) (j k r t : ℕ) :
    matrixCoefficient (pull F base) q j k r t = matrixCoefficient F (base q) j k r t := rfl

theorem value_invariance (F : Family) (base : List Bool → List Bool) (Q : Queries)
    (q c : List Bool) (hb : base c = base q) (hj : Q.coordinate c = Q.coordinate q)
    (hk : Q.coefficientIndex c = Q.coefficientIndex q) (hr : Q.row c = Q.row q)
    (ht : Q.col c = Q.col q) (hm : Q.modulus c = Q.modulus q) :
    (source (pull F base) (indices (pull F base) Q)).value c =
      (source (pull F base) (indices (pull F base) Q)).value q := by
  rw [value_snapshot, value_snapshot, matrix_pull, matrix_pull, hb, hj, hk, hr, ht, hm]
end LeanCanny.Algebra.IntegralMixedPhysicalQueryBits
