/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzMomentAccessFP
public import LeanCanny.Algebra.MatrixPowerStepSpace

/-!
# The complete factor-entry child evaluator

Zero, one, and negative-diagonal requests start already finished. A moment
request initializes the certified trailing-block power controller. The output
projection negates only the moment result. Every primitive is FP given FP
dimension, modulus, and original-entry access. The mathematical clock is not
computed by the transition.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.FactorChild
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open MatrixPower

structure Access where
  dimension : List Bool → List Bool
  modulus : List Bool → List Bool
  entry : List Bool → List Bool

structure Access.PolyTime (a : Access) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  entry : a.entry ∈ FP

def callbacks (a : Access) : Controller.Callbacks :=
  MatrixMoment.EntryBits.callbacks (EntryAccess.momentAccess a.dimension a.entry)
    (EntryAccess.childModulus a.modulus)

def fastValue (a : Access) (p : List Bool) : List Bool :=
  if QueryBits.selector a.dimension p = [true] then ArithmeticBits.one (a.modulus (pairFst p))
  else if QueryBits.selector a.dimension p = [false, true] then
    ArithmeticBits.negate (pair (a.modulus (pairFst p)) (a.entry (EntryAccess.diagonalInput a.dimension p)))
  else []

def immediate (a : Access) (p : List Bool) : List Bool := pair p (Controller.doneBits (fastValue a p))

def start (a : Access) (p : List Bool) : List Bool :=
  if QueryBits.selector a.dimension p = [true, true] then
    MatrixMoment.EntryBits.start (EntryAccess.momentAccess a.dimension a.entry)
      (QueryBits.momentExponent a.dimension) p
  else immediate a p

def advance (a : Access) : List Bool → List Bool := Controller.step (callbacks a)
def halted : List Bool → Bool := Controller.halted

def output (a : Access) (packet : List Bool) : List Bool :=
  if QueryBits.selector a.dimension (pairFst packet) = [true, true] then
    MatrixMoment.EntryBits.negativeResult (EntryAccess.childModulus a.modulus) packet
  else MatrixMoment.EntryBits.result packet

def time (a : Access) (p : List Bool) : ℕ :=
  if QueryBits.selector a.dimension p = [true, true] then
    let d := Nat.fromBitsLE (QueryBits.remaining a.dimension p)
    let e := Nat.fromBitsLE (QueryBits.momentExponent a.dimension p) + 2
    MatrixPower.work (d + 2) e.size e + 1
  else 0

theorem callbacks_polyTime (a : Access) (ha : a.PolyTime) : (callbacks a).PolyTime :=
  EntryAccess.momentCallbacks_polyTime ha.dimension ha.entry ha.modulus

theorem fastValue_mem_FP (a : Access) (ha : a.PolyTime) : fastValue a ∈ FP := by
  have hs := QueryBits.selector_mem_FP ha.dimension
  have hm := mem_FP_comp pairFst_mem_FP ha.modulus
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  have he := mem_FP_comp (EntryAccess.diagonalInput_mem_FP ha.dimension) ha.entry
  have hn := mem_FP_comp (mem_FP_pair hm he) ArithmeticBits.negate_mem_FP
  have h := (stringEq_fppred hs (constFn_mem_FP [true])).ite_mem_FP ho
    ((stringEq_fppred hs (constFn_mem_FP [false, true])).ite_mem_FP hn (constFn_mem_FP []))
  refine mem_FP_of_eq (g := fastValue a) h ?_
  intro p
  simp only [Function.comp_apply, fastValue]

theorem immediate_mem_FP (a : Access) (ha : a.PolyTime) : immediate a ∈ FP := by
  have h := mem_FP_pair id_mem_FP (Controller.doneBits_mem_FP (fastValue_mem_FP a ha))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem start_mem_FP (a : Access) (ha : a.PolyTime) : start a ∈ FP := by
  have h := (stringEq_fppred (QueryBits.selector_mem_FP ha.dimension) (constFn_mem_FP [true, true])).ite_mem_FP
    (EntryAccess.momentStart_mem_FP ha.dimension ha.entry) (immediate_mem_FP a ha)
  refine mem_FP_of_eq (g := start a) h ?_
  intro p
  simp only [start]

theorem advance_mem_FP (a : Access) (ha : a.PolyTime) : advance a ∈ FP :=
  Controller.step_mem_FP _ (callbacks_polyTime a ha)

theorem halted_mem_FP : (fun p => [halted p]) ∈ FP := Controller.halted_mem_FP

theorem output_mem_FP (a : Access) (ha : a.PolyTime) : output a ∈ FP := by
  have hs := mem_FP_comp pairFst_mem_FP (QueryBits.selector_mem_FP ha.dimension)
  have hn := MatrixMoment.EntryBits.negativeResult_mem_FP (EntryAccess.childModulus_mem_FP ha.modulus)
  have h := (stringEq_fppred hs (constFn_mem_FP [true, true])).ite_mem_FP hn
    MatrixMoment.EntryBits.result_mem_FP
  refine mem_FP_of_eq (g := output a) h ?_
  intro p
  simp only [Function.comp_apply, output]

theorem time_immediate (a : Access) (p : List Bool)
    (h : QueryBits.selector a.dimension p ≠ [true, true]) : time a p = 0 := by simp [time, h]

theorem immediate_halted (a : Access) (p : List Bool) : halted (immediate a p) = true := by
  simp [halted, immediate, Controller.halted, Controller.doneBits]

theorem immediate_output (a : Access) (p : List Bool)
    (h : QueryBits.selector a.dimension p ≠ [true, true]) : output a (immediate a p) = fastValue a p := by
  simp [output, immediate, h, MatrixMoment.EntryBits.result, Controller.doneBits]

end LeanCanny.Algebra.Berkowitz.FactorChild
