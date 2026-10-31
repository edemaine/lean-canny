/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPurePowerPolynomialSpace
public import LeanCanny.Algebra.PurePowerReductionCoefficientMap

/-! # Original lower-coefficient readers for relative pure-power reductions

The native reduction entry reads one lower coefficient or the common
integer diagonal coefficient. Its query writers retain the original
record and requested old basis ranks, and explicitly transpose the
integer reduction program's source-column protocol.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPurePowerActionBits (Source reductionSource)
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Access (S : Source) where
  layout : S.layout.toLayout.PolyTime
  coordinate : UnaryFn (fun c => (S.layout.coordinate c).val)
  bound : BinaryFn S.layout.bound
  rank : BinaryFn S.rank
  modulus : BinaryFn S.modulus
  coefficient : BinaryFn S.coefficient
  basisRow : BinaryFn (fun c => (S.basisRow c).val)
  basisCol : BinaryFn (fun c => (S.basisCol c).val)
  low : List Bool → List Bool
  leading : List Bool → List Bool
  leading_eq : ∀ c, leading c = residueBits (S.leading c : ZMod (S.modulus c))
  low_eq : ∀ c (i : Fin (S.layout.arity c)) (k : ℕ) (r t : Fin (S.rank c)),
    letI := S.ring c
    low (pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((S.low c i).coeff (RationalSubstitution.Indexed.exponentVector (S.layout.arity c)
          (FixedWidthPolynomial.entry (S.layout.width c) k))) r t : ℤ) : ZMod (S.modulus c))

def layout (S : Source) : PurePowerReductionBits.Layout where
  arity z := S.layout.arity (pairFst z)
  width z := S.layout.width (pairFst z)
  degree z := S.layout.degree (pairFst z)

theorem layout_polyTime (S : Source) (a : Access S) : (layout S).PolyTime := by
  refine ⟨a.layout.arity.comp pairFst_mem_FP, a.layout.width.comp pairFst_mem_FP, ?_⟩
  have HQ : (fun q => pair (pairFst (pairFst q)) (pairSnd q)) ∈ FP :=
    mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have H : BinaryFn (fun q => S.layout.degree (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))
      (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))).length) := a.layout.degree.comp HQ
  exact BinaryFn.of_eq H (fun q => by simp only [pairFst_pair, pairSnd_pair, layout])

def lowQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)

theorem lowQuery_FP : lowQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

def constant (a : Access S) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (basisRowCode q) = Nat.fromBitsLE (basisColCode q) then a.leading (original q) else []

theorem constant_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.leading) : SpaceFunction (constant a) := by
  have HG := (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisRowCode_FP).eq
    (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisColCode_FP)
  exact (SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (basisRowCode q) = Nat.fromBitsLE (basisColCode q)))
    HG.flag_mem_FP (E.precompose original IntegralBerkowitzBlockBits.original_FP)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))).congr
      (funext fun _ => by simp only [constant, decide_eq_true_eq, Function.comp_apply])

def writer (S : Source) (p : List Bool) : List Bool :=
  pair (pair (pairFst p) (BinaryNatCode.encode (S.modulus (original p) - 1)))
    (pair (MatrixMoment.EntryBits.colIndex p) (MatrixMoment.EntryBits.rowIndex p))

theorem writer_FP (S : Source) (a : Access S) : writer S ∈ FP := by
  have HM : BinaryFn (fun p => S.modulus (original p) - 1) :=
    (a.modulus.sub (BinaryFn.const 1)).comp IntegralBerkowitzBlockBits.original_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP HM.bits_mem_FP)
    (mem_FP_pair MatrixMoment.EntryBits.colIndex_mem_FP MatrixMoment.EntryBits.rowIndex_mem_FP)

theorem writer_packet (S : Source) (c : List Bool) (i j r t : ℕ) :
    writer S (IntegralReductionActionBits.packet c i j r t) =
      PurePowerReductionBits.packet
        (pair (IntegralBlockMomentBits.context c r t) (BinaryNatCode.encode (S.modulus c - 1))) j i := by
  simp only [writer, IntegralReductionActionBits.packet, PurePowerReductionBits.packet,
    MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex, original,
    IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair]

def entryProgram (S : Source) (a : Access S) : List Bool → List Bool :=
  PurePowerReductionBits.entry (layout S) (fun z => S.layout.bound (pairFst z))
    (constant a) (a.low ∘ lowQuery) ∘ writer S

attribute [local irreducible] PurePowerReductionBits.entry

theorem entry_evaluator (S : Source) (a : Access S) (EL : SpaceFunction a.low) (EC : SpaceFunction a.leading) :
    SpaceFunction (entryProgram S a) := by
  have HB : BinaryFn (fun z => S.layout.bound (pairFst z)) := a.bound.comp pairFst_mem_FP
  exact (PurePowerReductionBits.entryEvaluator (layout_polyTime S a) HB (constant_evaluator S a EC)
    (EL.precompose lowQuery lowQuery_FP)).precompose (writer S) (writer_FP S a)

end LeanCanny.Algebra.IntegralPurePowerReductionBits
