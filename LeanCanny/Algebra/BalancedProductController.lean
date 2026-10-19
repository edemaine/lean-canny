/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductQueryFP
public import LeanCanny.Encoding.BinaryMulFP

/-!
# FP control for balanced product bits

Packets pair an unchanged context with the binary continuation state. The
controller reads only the active query and top frame. Leaf queries contain the
context, factor address, and bit index. A suspended evaluator can intercept
these requests; the ordinary controller also accepts an FP leaf callback.

All functions are total on bitstrings. Simulation is asserted separately on
encoded states, so these functions need no expensive state validation.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct.Controller
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def putBit (x tail : List Bool) : List Bool := x[0]?.getD false :: tail
def evalBits (q s : List Bool) : List Bool := false :: false :: pair q s
def scanBits (q t a s : List Bool) : List Bool := false :: true :: pair q (pair t (pair a s))
def retBits (x s : List Bool) : List Bool := true :: false :: putBit x s
def doneBits (x : List Bool) : List Bool := true :: true :: putBit x []
def leftBits (q t a : List Bool) : List Bool := false :: pair q (pair t a)
def rightBits (q t a x : List Bool) : List Bool := true :: putBit x (pair q (pair t a))
def pushBits (f s : List Bool) : List Bool := true :: pair f s

theorem putBit_mem_FP {x s : List Bool → List Bool} (hx : x ∈ FP) (hs : s ∈ FP) :
    (fun p => putBit (x p) (s p)) ∈ FP := by
  have h := (FPPred.getBit hx (UnaryFn.const 0)).ite_mem_FP
    (mem_FP_comp hs (Cobham.cons_mem_FP true)) (mem_FP_comp hs (Cobham.cons_mem_FP false))
  refine mem_FP_of_eq h (fun p => ?_)
  simp only [putBit]
  cases (x p)[0]?.getD false <;> rfl

theorem evalBits_mem_FP {q s : List Bool → List Bool} (hq : q ∈ FP) (hs : s ∈ FP) :
    (fun p => evalBits (q p) (s p)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair hq hs) (Cobham.cons_mem_FP false)) (Cobham.cons_mem_FP false)

theorem scanBits_mem_FP {q t a s : List Bool → List Bool}
    (hq : q ∈ FP) (ht : t ∈ FP) (ha : a ∈ FP) (hs : s ∈ FP) :
    (fun p => scanBits (q p) (t p) (a p) (s p)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair hq (mem_FP_pair ht (mem_FP_pair ha hs)))
    (Cobham.cons_mem_FP true)) (Cobham.cons_mem_FP false)

theorem retBits_mem_FP {x s : List Bool → List Bool} (hx : x ∈ FP) (hs : s ∈ FP) :
    (fun p => retBits (x p) (s p)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (putBit_mem_FP hx hs) (Cobham.cons_mem_FP false)) (Cobham.cons_mem_FP true)

theorem doneBits_mem_FP {x : List Bool → List Bool} (hx : x ∈ FP) :
    (fun p => doneBits (x p)) ∈ FP :=
  mem_FP_comp (mem_FP_comp (putBit_mem_FP hx (constFn_mem_FP []))
    (Cobham.cons_mem_FP true)) (Cobham.cons_mem_FP true)

theorem leftBits_mem_FP {q t a : List Bool → List Bool} (hq : q ∈ FP) (ht : t ∈ FP) (ha : a ∈ FP) :
    (fun p => leftBits (q p) (t p) (a p)) ∈ FP :=
  mem_FP_comp (mem_FP_pair hq (mem_FP_pair ht ha)) (Cobham.cons_mem_FP false)

theorem rightBits_mem_FP {q t a x : List Bool → List Bool}
    (hq : q ∈ FP) (ht : t ∈ FP) (ha : a ∈ FP) (hx : x ∈ FP) :
    (fun p => rightBits (q p) (t p) (a p) (x p)) ∈ FP :=
  mem_FP_comp (putBit_mem_FP hx (mem_FP_pair hq (mem_FP_pair ht ha))) (Cobham.cons_mem_FP true)

theorem pushBits_mem_FP {f s : List Bool → List Bool} (hf : f ∈ FP) (hs : s ∈ FP) :
    (fun p => pushBits (f p) (s p)) ∈ FP :=
  mem_FP_comp (mem_FP_pair hf hs) (Cobham.cons_mem_FP true)

def body (p : List Bool) : List Bool := (pairSnd p).drop 2
def query (p : List Bool) : List Bool := pairFst (body p)
def evalStack (p : List Bool) : List Bool := pairSnd (body p)
def scanTime (p : List Bool) : List Bool := pairFst (evalStack p)
def scanAcc (p : List Bool) : List Bool := pairFst (pairSnd (evalStack p))
def scanStack (p : List Bool) : List Bool := pairSnd (pairSnd (evalStack p))
def retStack (p : List Bool) : List Bool := (pairSnd p).drop 3
def top (p : List Bool) : List Bool := pairFst ((retStack p).drop 1)
def rest (p : List Bool) : List Bool := pairSnd ((retStack p).drop 1)
def frameBody (p : List Bool) : List Bool :=
  if (top p)[0]?.getD false = true then (top p).drop 2 else (top p).drop 1
def parent (p : List Bool) : List Bool := pairFst (frameBody p)
def frameTime (p : List Bool) : List Bool := pairFst (pairSnd (frameBody p))
def frameAcc (p : List Bool) : List Bool := pairSnd (pairSnd (frameBody p))
def selector (p : List Bool) : List Bool := (top p).drop 1

theorem body_mem_FP : body ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 2)
theorem query_mem_FP : query ∈ FP := mem_FP_comp body_mem_FP pairFst_mem_FP
theorem evalStack_mem_FP : evalStack ∈ FP := mem_FP_comp body_mem_FP pairSnd_mem_FP
theorem scanTime_mem_FP : scanTime ∈ FP := mem_FP_comp evalStack_mem_FP pairFst_mem_FP
theorem scanAcc_mem_FP : scanAcc ∈ FP := mem_FP_comp (mem_FP_comp evalStack_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem scanStack_mem_FP : scanStack ∈ FP := mem_FP_comp (mem_FP_comp evalStack_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem retStack_mem_FP : retStack ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 3)
theorem top_mem_FP : top ∈ FP := mem_FP_comp (drop_mem_FP retStack_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
theorem rest_mem_FP : rest ∈ FP := mem_FP_comp (drop_mem_FP retStack_mem_FP (UnaryFn.const 1)) pairSnd_mem_FP
theorem frameBody_mem_FP : frameBody ∈ FP :=
  (FPPred.getBit top_mem_FP (UnaryFn.const 0)).ite_mem_FP
    (drop_mem_FP top_mem_FP (UnaryFn.const 2)) (drop_mem_FP top_mem_FP (UnaryFn.const 1))
theorem parent_mem_FP : parent ∈ FP := mem_FP_comp frameBody_mem_FP pairFst_mem_FP
theorem frameTime_mem_FP : frameTime ∈ FP := mem_FP_comp (mem_FP_comp frameBody_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem frameAcc_mem_FP : frameAcc ∈ FP := mem_FP_comp (mem_FP_comp frameBody_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem selector_mem_FP : selector ∈ FP := drop_mem_FP top_mem_FP (UnaryFn.const 1)

def queryLimit (q : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.mul (pair (QueryBits.index q) (QueryBits.width q)))
    (BinaryNat.succ (QueryBits.index q)))

theorem queryLimit_mem_FP : queryLimit ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair QueryBits.index_mem_FP QueryBits.width_mem_FP) BinaryNat.mul_mem_FP
  have hc := mem_FP_comp QueryBits.index_mem_FP BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hp hc) BinaryNat.add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

def leafQuery (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (QueryBits.node (query p)) (QueryBits.index (query p)))

theorem leafQuery_mem_FP : leafQuery ∈ FP := by
  have hn := mem_FP_comp query_mem_FP QueryBits.node_mem_FP
  have hk := mem_FP_comp query_mem_FP QueryBits.index_mem_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair hn hk)
  refine mem_FP_of_eq (g := leafQuery) h ?_
  intro p
  simp only [Function.comp_apply, leafQuery]

def evalNext (leaf : List Bool → List Bool) (p : List Bool) : List Bool :=
  if QueryBits.height (query p) = [] then retBits (leaf (leafQuery p)) (evalStack p)
  else scanBits (query p) [] [] (evalStack p)

def scanNext (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (queryLimit (query p)) ≤ Nat.fromBitsLE (scanTime p) then
    retBits (scanAcc p) (scanStack p)
  else if Nat.fromBitsLE (pairSnd (QueryBits.coordinate (pair (query p) (scanTime p)))) <
      Nat.fromBitsLE (BinaryNat.succ (QueryBits.index (query p))) then
    evalBits (QueryBits.childLeft (pair (query p) (scanTime p)))
      (pushBits (leftBits (query p) (scanTime p) (scanAcc p)) (scanStack p))
  else scanBits (query p) (BinaryNat.succ (scanTime p)) (BinaryNat.half (scanAcc p)) (scanStack p)

def returnLeft (p : List Bool) : List Bool :=
  evalBits (QueryBits.childRight (pair (parent p) (frameTime p)))
    (pushBits (rightBits (parent p) (frameTime p) (frameAcc p) (body p)) (rest p))

def addContribution (p : List Bool) : List Bool :=
  if (selector p)[0]?.getD false = true ∧
      Nat.fromBitsLE (pairSnd (QueryBits.coordinate (pair (parent p) (frameTime p)))) ≤
        Nat.fromBitsLE (pairFst (QueryBits.coordinate (pair (parent p) (frameTime p)))) ∧
      (body p)[0]?.getD false = true then BinaryNat.succ (frameAcc p) else frameAcc p

def returnRight (p : List Bool) : List Bool :=
  scanBits (parent p) (BinaryNat.succ (frameTime p)) (addContribution p) (rest p)

def returnNext (p : List Bool) : List Bool :=
  if retStack p = [] then doneBits (body p)
  else if (top p)[0]?.getD false = true then returnRight p else returnLeft p

def nextState (leaf : List Bool → List Bool) (p : List Bool) : List Bool :=
  if (pairSnd p)[0]?.getD false = true then
    if (pairSnd p)[1]?.getD false = true then pairSnd p else returnNext p
  else if (pairSnd p)[1]?.getD false = true then scanNext p else evalNext leaf p

def step (leaf : List Bool → List Bool) (p : List Bool) : List Bool := pair (pairFst p) (nextState leaf p)

theorem evalNext_mem_FP {leaf : List Bool → List Bool} (hl : leaf ∈ FP) : evalNext leaf ∈ FP := by
  have hh := mem_FP_comp query_mem_FP QueryBits.height_mem_FP
  have hr := retBits_mem_FP (mem_FP_comp leafQuery_mem_FP hl) evalStack_mem_FP
  have hs := scanBits_mem_FP query_mem_FP (constFn_mem_FP []) (constFn_mem_FP []) evalStack_mem_FP
  exact mem_FP_of_eq ((stringEq_fppred hh (constFn_mem_FP [])).ite_mem_FP hr hs) (fun _ => rfl)

theorem scanNext_mem_FP : scanNext ∈ FP := by
  have hl := mem_FP_comp query_mem_FP queryLimit_mem_FP
  have hc := mem_FP_comp (mem_FP_pair query_mem_FP scanTime_mem_FP) QueryBits.coordinate_mem_FP
  have hp := mem_FP_comp hc pairSnd_mem_FP
  have hn := mem_FP_comp (mem_FP_comp query_mem_FP QueryBits.index_mem_FP) BinaryNat.succ_mem_FP
  have he := evalBits_mem_FP
    (mem_FP_comp (mem_FP_pair query_mem_FP scanTime_mem_FP) QueryBits.childLeft_mem_FP)
    (pushBits_mem_FP (leftBits_mem_FP query_mem_FP scanTime_mem_FP scanAcc_mem_FP) scanStack_mem_FP)
  have hs := scanBits_mem_FP query_mem_FP (mem_FP_comp scanTime_mem_FP BinaryNat.succ_mem_FP)
    (mem_FP_comp scanAcc_mem_FP BinaryNat.half_mem_FP) scanStack_mem_FP
  have h := (BinaryNat.le_fppred hl scanTime_mem_FP).ite_mem_FP
    (retBits_mem_FP scanAcc_mem_FP scanStack_mem_FP) ((BinaryNat.lt_fppred hp hn).ite_mem_FP he hs)
  refine mem_FP_of_eq (g := scanNext) h ?_
  intro p
  simp only [Function.comp_apply, scanNext]

theorem returnLeft_mem_FP : returnLeft ∈ FP := by
  have hc := mem_FP_comp (mem_FP_pair parent_mem_FP frameTime_mem_FP) QueryBits.childRight_mem_FP
  have hf := rightBits_mem_FP parent_mem_FP frameTime_mem_FP frameAcc_mem_FP body_mem_FP
  have h := evalBits_mem_FP hc (pushBits_mem_FP hf rest_mem_FP)
  refine mem_FP_of_eq (g := returnLeft) h ?_
  intro p
  simp only [Function.comp_apply, returnLeft]

theorem addContribution_mem_FP : addContribution ∈ FP := by
  have hc := mem_FP_comp (mem_FP_pair parent_mem_FP frameTime_mem_FP) QueryBits.coordinate_mem_FP
  have hl := FPPred.getBit selector_mem_FP (UnaryFn.const 0)
  have hi := BinaryNat.le_fppred (mem_FP_comp hc pairSnd_mem_FP) (mem_FP_comp hc pairFst_mem_FP)
  have hr := FPPred.getBit body_mem_FP (UnaryFn.const 0)
  have h := (hl.and (hi.and hr)).ite_mem_FP (mem_FP_comp frameAcc_mem_FP BinaryNat.succ_mem_FP) frameAcc_mem_FP
  refine mem_FP_of_eq (g := addContribution) h ?_
  intro p
  simp only [Function.comp_apply, addContribution]

theorem returnRight_mem_FP : returnRight ∈ FP := by
  have ht := mem_FP_comp frameTime_mem_FP BinaryNat.succ_mem_FP
  have h := scanBits_mem_FP parent_mem_FP ht addContribution_mem_FP rest_mem_FP
  refine mem_FP_of_eq (g := returnRight) h ?_
  intro p
  simp only [Function.comp_apply, returnRight]

theorem returnNext_mem_FP : returnNext ∈ FP := by
  have hr := (FPPred.getBit top_mem_FP (UnaryFn.const 0)).ite_mem_FP returnRight_mem_FP returnLeft_mem_FP
  have h := (stringEq_fppred retStack_mem_FP (constFn_mem_FP [])).ite_mem_FP (doneBits_mem_FP body_mem_FP) hr
  exact mem_FP_of_eq h (fun _ => rfl)

theorem nextState_mem_FP {leaf : List Bool → List Bool} (hl : leaf ∈ FP) : nextState leaf ∈ FP := by
  have hb := FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1)
  have h := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).ite_mem_FP
    (hb.ite_mem_FP pairSnd_mem_FP returnNext_mem_FP) (hb.ite_mem_FP scanNext_mem_FP (evalNext_mem_FP hl))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_mem_FP {leaf : List Bool → List Bool} (hl : leaf ∈ FP) : step leaf ∈ FP :=
  mem_FP_pair pairFst_mem_FP (nextState_mem_FP hl)

def initialPacket (count index : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair c (evalBits (QueryBits.initial count index c) [])

theorem initialPacket_mem_FP {count index : List Bool → List Bool} (hc : count ∈ FP) (hi : index ∈ FP) :
    initialPacket count index ∈ FP :=
  mem_FP_pair id_mem_FP (evalBits_mem_FP (QueryBits.initial_mem_FP hc hi) (constFn_mem_FP []))

end LeanCanny.Algebra.BalancedProduct.Controller
