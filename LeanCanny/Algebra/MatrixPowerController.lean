/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerQueryFP
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-!
# A polynomial-time bitstring controller for streamed matrix powering

Packets retain the original context alongside the current encoded state. Entry
access and scalar operations receive that context explicitly. Every component
callback must have an FP certificate; this interface grants no free entry oracle.

The controller reads only the active query and top frame. It is total on all
strings and agrees with the typed transition on encoded states, as proved in
`MatrixPowerControllerCorrect`. It does not validate arbitrary input states;
establishing a valid initial state is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.Controller

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

structure Callbacks where
  dimension : List Bool → List Bool
  zero : List Bool → List Bool
  one : List Bool → List Bool
  entry : List Bool → List Bool
  combine : List Bool → List Bool

structure Callbacks.PolyTime (ops : Callbacks) : Prop where
  dimension : ops.dimension ∈ FP
  zero : ops.zero ∈ FP
  one : ops.one ∈ FP
  entry : ops.entry ∈ FP
  combine : ops.combine ∈ FP

def evalBits (q stack : List Bool) : List Bool := false :: false :: pair q stack
def retBits (x stack : List Bool) : List Bool := false :: true :: pair x stack
def doneBits (x : List Bool) : List Bool := true :: x
def leftBits (q k acc : List Bool) : List Bool := false :: pair q (pair k acc)
def rightBits (q k acc lhs : List Bool) : List Bool := true :: pair q (pair k (pair acc lhs))
def pushBits (f stack : List Bool) : List Bool := true :: pair f stack

theorem evalBits_mem_FP {q s : List Bool → List Bool} (hq : q ∈ FP) (hs : s ∈ FP) :
    (fun z => evalBits (q z) (s z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair hq hs) (cons_mem_FP false))
    (cons_mem_FP false)

theorem retBits_mem_FP {x s : List Bool → List Bool} (hx : x ∈ FP) (hs : s ∈ FP) :
    (fun z => retBits (x z) (s z)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair hx hs) (cons_mem_FP true))
    (cons_mem_FP false)

theorem doneBits_mem_FP {x : List Bool → List Bool} (hx : x ∈ FP) :
    (fun z => doneBits (x z)) ∈ FP := mem_FP_comp hx (cons_mem_FP true)

theorem leftBits_mem_FP {q k a : List Bool → List Bool} (hq : q ∈ FP) (hk : k ∈ FP) (ha : a ∈ FP) :
    (fun z => leftBits (q z) (k z) (a z)) ∈ FP :=
  mem_FP_comp (mem_FP_pair hq (mem_FP_pair hk ha)) (cons_mem_FP false)

theorem rightBits_mem_FP {q k a l : List Bool → List Bool}
    (hq : q ∈ FP) (hk : k ∈ FP) (ha : a ∈ FP) (hl : l ∈ FP) :
    (fun z => rightBits (q z) (k z) (a z) (l z)) ∈ FP :=
  mem_FP_comp (mem_FP_pair hq (mem_FP_pair hk (mem_FP_pair ha hl))) (cons_mem_FP true)

theorem pushBits_mem_FP {f s : List Bool → List Bool} (hf : f ∈ FP) (hs : s ∈ FP) :
    (fun z => pushBits (f z) (s z)) ∈ FP :=
  mem_FP_comp (mem_FP_pair hf hs) (cons_mem_FP true)

def body (p : List Bool) : List Bool := (pairSnd p).drop 2
def payload (p : List Bool) : List Bool := pairFst (body p)
def stack (p : List Bool) : List Bool := pairSnd (body p)
def top (p : List Bool) : List Bool := pairFst ((stack p).drop 1)
def rest (p : List Bool) : List Bool := pairSnd ((stack p).drop 1)
def frameBody (p : List Bool) : List Bool := (top p).drop 1
def parent (p : List Bool) : List Bool := pairFst (frameBody p)
def fields (p : List Bool) : List Bool := pairSnd (frameBody p)
def pivot (p : List Bool) : List Bool := pairFst (fields p)
def scalars (p : List Bool) : List Bool := pairSnd (fields p)

theorem body_mem_FP : body ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 2)
theorem payload_mem_FP : payload ∈ FP := mem_FP_comp body_mem_FP pairFst_mem_FP
theorem stack_mem_FP : stack ∈ FP := mem_FP_comp body_mem_FP pairSnd_mem_FP
theorem top_mem_FP : top ∈ FP :=
  mem_FP_comp (drop_mem_FP stack_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
theorem rest_mem_FP : rest ∈ FP :=
  mem_FP_comp (drop_mem_FP stack_mem_FP (UnaryFn.const 1)) pairSnd_mem_FP
theorem frameBody_mem_FP : frameBody ∈ FP := drop_mem_FP top_mem_FP (UnaryFn.const 1)
theorem parent_mem_FP : parent ∈ FP := mem_FP_comp frameBody_mem_FP pairFst_mem_FP
theorem fields_mem_FP : fields ∈ FP := mem_FP_comp frameBody_mem_FP pairSnd_mem_FP
theorem pivot_mem_FP : pivot ∈ FP := mem_FP_comp fields_mem_FP pairFst_mem_FP
theorem scalars_mem_FP : scalars ∈ FP := mem_FP_comp fields_mem_FP pairSnd_mem_FP

def evalNext (ops : Callbacks) (p : List Bool) : List Bool :=
  let c := pairFst p
  let q := payload p
  let s := stack p
  if QueryBits.exponent q = [] then
    retBits (if QueryBits.row q = QueryBits.col q then ops.one c else ops.zero c) s
  else if QueryBits.exponent q = [true] then
    retBits (ops.entry (pair c (pair (QueryBits.row q) (QueryBits.col q)))) s
  else if QueryBits.height q = [] then retBits (ops.zero c) s
  else
    let k := BinaryNat.pred (ops.dimension c)
    evalBits (QueryBits.childLeft (pair q k)) (pushBits (leftBits q k (ops.zero c)) s)

def returnLeft (p : List Bool) : List Bool :=
  evalBits (QueryBits.childRight (pair (parent p) (pivot p)))
    (pushBits (rightBits (parent p) (pivot p) (scalars p) (payload p)) (rest p))

def returnRight (ops : Callbacks) (p : List Bool) : List Bool :=
  let acc := ops.combine (pair (pairFst p)
    (pair (pairFst (scalars p)) (pair (pairSnd (scalars p)) (payload p))))
  if pivot p = [] then retBits acc (rest p)
  else
    let k := BinaryNat.pred (pivot p)
    evalBits (QueryBits.childLeft (pair (parent p) k))
      (pushBits (leftBits (parent p) k acc) (rest p))

def returnNext (ops : Callbacks) (p : List Bool) : List Bool :=
  if stack p = [] then doneBits (payload p)
  else if (top p)[0]?.getD false = true then returnRight ops p else returnLeft p

def nextState (ops : Callbacks) (p : List Bool) : List Bool :=
  if (pairSnd p)[0]?.getD false = true then pairSnd p
  else if (pairSnd p)[1]?.getD false = true then returnNext ops p else evalNext ops p

def step (ops : Callbacks) (p : List Bool) : List Bool := pair (pairFst p) (nextState ops p)

theorem evalNext_mem_FP (ops : Callbacks) (hops : ops.PolyTime) : evalNext ops ∈ FP := by
  have hq := payload_mem_FP
  have hs := stack_mem_FP
  have he := mem_FP_comp hq QueryBits.exponent_mem_FP
  have hh := mem_FP_comp hq QueryBits.height_mem_FP
  have hi := mem_FP_comp hq QueryBits.row_mem_FP
  have hj := mem_FP_comp hq QueryBits.col_mem_FP
  have hz := mem_FP_comp pairFst_mem_FP hops.zero
  have ho := mem_FP_comp pairFst_mem_FP hops.one
  have hdiag := (stringEq_fppred hi hj).ite_mem_FP ho hz
  have hzero := retBits_mem_FP hdiag hs
  have hentry := mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hj)) hops.entry
  have hone := retBits_mem_FP hentry hs
  have hbase := retBits_mem_FP hz hs
  have hk := mem_FP_comp (mem_FP_comp pairFst_mem_FP hops.dimension) BinaryNat.pred_mem_FP
  have hchild := mem_FP_comp (mem_FP_pair hq hk) QueryBits.childLeft_mem_FP
  have hframe := leftBits_mem_FP hq hk hz
  have hsplit := evalBits_mem_FP hchild (pushBits_mem_FP hframe hs)
  have h := (stringEq_fppred he (constFn_mem_FP [])).ite_mem_FP hzero
    ((stringEq_fppred he (constFn_mem_FP [true])).ite_mem_FP hone
      ((stringEq_fppred hh (constFn_mem_FP [])).ite_mem_FP hbase hsplit))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem returnLeft_mem_FP : returnLeft ∈ FP := by
  have hchild := mem_FP_comp (mem_FP_pair parent_mem_FP pivot_mem_FP) QueryBits.childRight_mem_FP
  have hf := rightBits_mem_FP parent_mem_FP pivot_mem_FP scalars_mem_FP payload_mem_FP
  have h := evalBits_mem_FP hchild (pushBits_mem_FP hf rest_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem returnRight_mem_FP (ops : Callbacks) (hops : ops.PolyTime) : returnRight ops ∈ FP := by
  have ha := mem_FP_comp scalars_mem_FP pairFst_mem_FP
  have hl := mem_FP_comp scalars_mem_FP pairSnd_mem_FP
  have hacc := mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_pair ha (mem_FP_pair hl payload_mem_FP))) hops.combine
  have hret := retBits_mem_FP hacc rest_mem_FP
  have hk := mem_FP_comp pivot_mem_FP BinaryNat.pred_mem_FP
  have hc := mem_FP_comp (mem_FP_pair parent_mem_FP hk) QueryBits.childLeft_mem_FP
  have hf := leftBits_mem_FP parent_mem_FP hk hacc
  have heval := evalBits_mem_FP hc (pushBits_mem_FP hf rest_mem_FP)
  have h := (stringEq_fppred pivot_mem_FP (constFn_mem_FP [])).ite_mem_FP hret heval
  exact mem_FP_of_eq h (fun _ => rfl)

theorem returnNext_mem_FP (ops : Callbacks) (hops : ops.PolyTime) : returnNext ops ∈ FP := by
  have hr := (FPPred.getBit top_mem_FP (UnaryFn.const 0)).ite_mem_FP
    (returnRight_mem_FP ops hops) returnLeft_mem_FP
  have h := (stringEq_fppred stack_mem_FP (constFn_mem_FP [])).ite_mem_FP
    (doneBits_mem_FP payload_mem_FP) hr
  exact mem_FP_of_eq h (fun _ => rfl)

theorem nextState_mem_FP (ops : Callbacks) (hops : ops.PolyTime) : nextState ops ∈ FP := by
  have hr := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1)).ite_mem_FP
    (returnNext_mem_FP ops hops) (evalNext_mem_FP ops hops)
  have h := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).ite_mem_FP pairSnd_mem_FP hr
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_mem_FP (ops : Callbacks) (hops : ops.PolyTime) : step ops ∈ FP :=
  mem_FP_pair pairFst_mem_FP (nextState_mem_FP ops hops)

/-- The field functions write the exponent and the row/column indices in binary.
The context is retained for every subsequent callback. Input validation is separate. -/
def initialPacket (exponent row col : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair c (evalBits (QueryBits.initial (pair (exponent c) (pair (row c) (col c)))) [])

theorem initialPacket_mem_FP {exponent row col : List Bool → List Bool}
    (he : exponent ∈ FP) (hi : row ∈ FP) (hj : col ∈ FP) : initialPacket exponent row col ∈ FP := by
  have hq := mem_FP_comp (mem_FP_pair he (mem_FP_pair hi hj)) QueryBits.initial_mem_FP
  have hs := evalBits_mem_FP hq (constFn_mem_FP [])
  exact mem_FP_pair id_mem_FP hs

end LeanCanny.Algebra.MatrixPower.Controller
