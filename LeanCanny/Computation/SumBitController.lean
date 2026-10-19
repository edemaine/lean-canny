/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutineFunction
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Algebra.BinarySumCarry

/-!
# An encoded controller for streamed sum bits

The parent stores the original input, one binary step counter, and a short
column accumulator. A row has `N+1` positions: `N` child bit requests followed
by division of the accumulator by two. Queries have format `pair c (pair i k)`.
The selected bit `K` is ready at step `K*(N+1)+N`. Child bit computation may
itself use polynomial space; its entire result is not treated as an FP step.
-/

@[expose] public section

namespace LeanCanny.Computation.SumBits
open Complexity
open LeanCanny.Encoding

def counter (p : List Bool) : List Bool := pairFst (pairSnd p)
def accumulator (p : List Bool) : List Bool := pairSnd (pairSnd p)
def width (count : List Bool → List Bool) (c : List Bool) : List Bool := BinaryNat.succ (count c)
def limit (count index : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.mul (pair (index c) (width count c))) (count c))
def coordinate (count : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.divMod (pair (counter p) (width count (pairFst p)))
def column (count : List Bool → List Bool) (p : List Bool) : List Bool := pairFst (coordinate count p)
def position (count : List Bool → List Bool) (p : List Bool) : List Bool := pairSnd (coordinate count p)
def query (count : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (position count p) (column count p))
def request (count : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (position count p) < Nat.fromBitsLE (count (pairFst p)))
def halted (count index : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (limit count index (pairFst p)) ≤ Nat.fromBitsLE (counter p))
def ordinary (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNat.succ (counter p)) (BinaryNat.div (pair (accumulator p) [false, true])))
def response {f : List Bool → List Bool} (E : SpaceFunction f) (z : List Bool) : List Bool :=
  if (E.output (pairSnd z))[0]?.getD false then [true] else []
def resume {f : List Bool → List Bool} (E : SpaceFunction f) (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (BinaryNat.succ (counter (pairFst z)))
    (BinaryNat.add (pair (accumulator (pairFst z)) (response E z))))
def output (p : List Bool) : List Bool := BinaryNat.mod (pair (accumulator p) [false, true])

def program {f : List Bool → List Bool} (E : SpaceFunction f) (count : List Bool → List Bool) :
    SubroutineIteration.Program where
  ordinary := ordinary
  request := request count
  start := E.init ∘ query count
  advance := E.advance
  halt := E.halt
  resume := resume E

def childTime {f : List Bool → List Bool} (E : SpaceFunction f) (count : List Bool → List Bool)
    (p : List Bool) : ℕ := E.time (query count p)

def packet (c : List Bool) (t v : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode t) (BinaryNatCode.encode v))

def init (c : List Bool) : List Bool := packet c 0 0

theorem counter_mem_FP : counter ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem accumulator_mem_FP : accumulator ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem width_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) : width count ∈ FP :=
  mem_FP_comp hc BinaryNat.succ_mem_FP

theorem limit_mem_FP {count index : List Bool → List Bool} (hc : count ∈ FP) (hi : index ∈ FP) :
    limit count index ∈ FP := by
  have hm := mem_FP_comp (mem_FP_pair hi (width_mem_FP hc)) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm hc) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := limit count index) h ?_
  intro c
  simp only [Function.comp_apply, limit]

theorem coordinate_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) : coordinate count ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP (width_mem_FP hc)
  have h := mem_FP_comp (mem_FP_pair counter_mem_FP hw) BinaryNat.divMod_mem_FP
  refine mem_FP_of_eq (g := coordinate count) h ?_
  intro p
  simp only [Function.comp_apply, coordinate]

theorem column_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) : column count ∈ FP :=
  mem_FP_comp (coordinate_mem_FP hc) pairFst_mem_FP
theorem position_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) : position count ∈ FP :=
  mem_FP_comp (coordinate_mem_FP hc) pairSnd_mem_FP

theorem query_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) : query count ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair (position_mem_FP hc) (column_mem_FP hc))
  refine mem_FP_of_eq (g := query count) h ?_
  intro p
  simp only [query]

theorem request_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) :
    (fun p => [request count p]) ∈ FP :=
  (BinaryNat.lt_fppred (position_mem_FP hc) (mem_FP_comp pairFst_mem_FP hc)).flag_mem_FP

theorem halted_mem_FP {count index : List Bool → List Bool} (hc : count ∈ FP) (hi : index ∈ FP) :
    (fun p => [halted count index p]) ∈ FP :=
  (BinaryNat.le_fppred (mem_FP_comp pairFst_mem_FP (limit_mem_FP hc hi)) counter_mem_FP).flag_mem_FP

theorem ordinary_mem_FP : ordinary ∈ FP := by
  have hv := mem_FP_comp (mem_FP_pair accumulator_mem_FP (constFn_mem_FP [false, true])) BinaryNat.div_mem_FP
  have ht := mem_FP_comp counter_mem_FP BinaryNat.succ_mem_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair ht hv)
  refine mem_FP_of_eq (g := ordinary) h ?_
  intro p
  simp only [Function.comp_apply, ordinary]

theorem response_mem_FP {f : List Bool → List Bool} (E : SpaceFunction f) : response E ∈ FP :=
  (FPPred.getBit (mem_FP_comp pairSnd_mem_FP E.outputFP) (UnaryFn.const 0)).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem resume_mem_FP {f : List Bool → List Bool} (E : SpaceFunction f) : resume E ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have ht := mem_FP_comp (mem_FP_comp pairFst_mem_FP counter_mem_FP) BinaryNat.succ_mem_FP
  have hv := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP accumulator_mem_FP) (response_mem_FP E))
    BinaryNat.add_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair ht hv)
  refine mem_FP_of_eq (g := resume E) h ?_
  intro z
  simp only [Function.comp_apply, resume]

theorem output_mem_FP : output ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair accumulator_mem_FP (constFn_mem_FP [false, true])) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := output) h ?_
  intro p
  simp only [Function.comp_apply, output]

theorem program_polyTime {f : List Bool → List Bool} (E : SpaceFunction f)
    {count : List Bool → List Bool} (hc : count ∈ FP) : (program E count).PolyTime := by
  have hs := mem_FP_comp (query_mem_FP hc) E.initFP
  exact ⟨ordinary_mem_FP, request_mem_FP hc, hs, E.advanceFP, E.haltFP, resume_mem_FP E⟩

theorem init_mem_FP : init ∈ FP := by
  have h := mem_FP_pair id_mem_FP (constFn_mem_FP (pair [] []))
  exact mem_FP_of_eq (g := init) h (fun _ => rfl)

end LeanCanny.Computation.SumBits
