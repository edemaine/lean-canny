/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalDerivativeEntryRequest
public import LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
public import LeanCanny.Algebra.IntegralMixedVirtualSweepSource

/-! # Actual squarefree PSC sources with a native coefficient request

The matrix is the literal principal subresultant over the old algebra
with one formal nilpotent. Each of its integer block entries uses the
native single-call selector, whose only child is one coefficient of the
actual virtual coordinate polynomial. No whole-history space evaluator
or arbitrary PSC matrix reader is assumed here.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeNativeSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateSquarefree
open scoped Classical

noncomputable def parameters (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) : PrincipalDerivativeEntryRequest.Parameters where
  degree q := coordinateDegree (F.spatial q) (F.rule q)
  index q := (index q).val
  modulus := I.modulus

noncomputable def source (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) : IntegralBerkowitzBlockBits.Source where
  dimension q := (coordinateDegree (F.spatial q) (F.rule q) - (index q).val) +
    (coordinateDegree (F.spatial q) (F.rule q) - 1 - (index q).val)
  rank q := count (F.birth q + 1) (F.width q)
  carrier := IntegralMixedVirtualSweepSource.Coefficient F
  ring _ := inferInstance
  nontrivial q := nontrivial_of_ne _ _
    ((IntegralMixedCutNilpotent.basis (F.state q)).finBasis.ne_zero (I.row q))
  basis q := (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
  matrix q := IntegralMixedSquarefreeMatrixSource.matrix (F.state q) (F.birth_bound q)
    (F.rule q) (I.coordinate q) (index q)
  modulus := I.modulus
  modulus_ne_zero := I.modulus_ne_zero
  coefficient := I.coefficientIndex
  basisRow := I.row
  basisCol := I.col

noncomputable abbrev program (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) :=
  PrincipalDerivativeEntryRequest.program (parameters F I index)

structure Controls (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) where
  birth : UnaryFn F.birth
  width : UnaryFn F.width
  ambient : UnaryFn F.ambient
  offset : UnaryFn (fun q => (F.rule q).critical.offset.val)
  degree : BinaryFn (fun q => (F.spatial q).degree)
  index : BinaryFn (fun q => (index q).val)
  modulus : BinaryFn I.modulus
  coefficient : BinaryFn I.coefficientIndex
  row : BinaryFn (fun q => (I.row q).val)
  col : BinaryFn (fun q => (I.col q).val)

theorem degree_binary (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) (a : Controls F I index) :
    BinaryFn (fun q => coordinateDegree (F.spatial q) (F.rule q)) :=
  PurePowerReductionBounds.dimension_binary ((a.ambient.sub a.offset).add (UnaryFn.const 1)) a.degree

theorem program_controls (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) (a : Controls F I index) :
    (program F I index).Controls :=
  PrincipalDerivativeEntryRequest.controls (parameters F I index) ⟨degree_binary F I index a, a.index, a.modulus⟩

theorem entry_value (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) (answer : List Bool → List Bool)
    (ha : ∀ q k (r t : Fin (count (F.birth q + 1) (F.width q))),
      answer (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q)
            (F.rule q) (I.coordinate q)).coeff k) r t : ℤ) : ZMod (I.modulus q)))
    (q : List Bool) (i j : Fin ((source F I index).dimension q))
    (r t : Fin (count (F.birth q + 1) (F.width q))) :
    (program F I index).value answer (pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (((source F I index).entryMatrix q i j r t : ℤ) : ZMod (I.modulus q)) := by
  apply PrincipalDerivativeEntryRequest.actual_value
    (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (parameters F I index)
    (IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)) q i j r t answer
  intro _
  rw [PrincipalDerivativeEntryRequest.query_packet]
  exact ha q _ r t

noncomputable def access (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (coordinateDegree (F.spatial q) (F.rule q))) (a : Controls F I index)
    (answer : List Bool → List Bool)
    (ha : ∀ q k (r t : Fin (count (F.birth q + 1) (F.width q))),
      answer (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q)
            (F.rule q) (I.coordinate q)).coeff k) r t : ℤ) : ZMod (I.modulus q))) :
    IntegralBerkowitzBlockBits.Access (source F I index) where
  dimension := ((degree_binary F I index a).sub a.index).add
    (((degree_binary F I index a).sub (BinaryFn.const 1)).sub a.index)
  rank := ((BinaryFn.const 2).powUnary a.width).powUnary (a.birth.add (UnaryFn.const 1))
  modulus := a.modulus
  coefficient := a.coefficient
  basisRow := a.row
  basisCol := a.col
  entry := (program F I index).value answer
  entry_eq := entry_value F I index answer ha

end LeanCanny.Algebra.IntegralMixedSquarefreeNativeSource
