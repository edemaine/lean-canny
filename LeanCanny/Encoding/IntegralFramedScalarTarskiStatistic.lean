/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSpace
public import LeanCanny.Encoding.IntegralFramedScalarTarskiSpecialization
public import LeanCanny.Algebra.CanonicalSignStatisticSpace
/-! # A total streamed principal statistic on one full physical vertex

The principal counter changes only the index. The source, vertex and two
parameter layout remain fixed; malformed sign words have a total decoding.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthTarskiPrincipalBits.polynomial
  IntegralFramedScalarTarskiIteratedSign.value CanonicalSignStatisticBits.value

def base (z : List Bool) :=pair (pairFst z) (pairFst (pairSnd z))
def query (q : List Bool) :=pair (pairFst (pairFst q)) (pair (pairSnd (pairFst q)) (pairSnd q))
theorem base_FP : base∈FP:=by polytime [base]
theorem query_FP : query∈FP:=by polytime [query]
theorem base_pair (c b : List Bool) : base (pair c b)=pair c (pairFst b) :=by
  simp only [base,pairFst_pair,pairSnd_pair]

def index (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool) (z : List Bool) :=
  MF.degree (read (base z))-Nat.fromBitsLE (pairSnd (pairSnd z))
def count (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool) (u : List Bool) :=
  MF.degree (read (IntegralFramedScalarTarskiIteratedSign.inputContext u))+1

theorem index_binary (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
    (hr : read∈FP) (hD : BinaryFn MF.degree) : BinaryFn (index MF read) :=by
  have H : BinaryFn (fun z=>MF.degree (read (base z))):=hD.comp (mem_FP_comp base_FP hr)
  exact H.sub (BinaryFn.fromBits (by polytime))

theorem count_binary (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
    (hr : read∈FP) (hD : BinaryFn MF.degree) : BinaryFn (count MF read) :=by
  have H : BinaryFn (fun u=>MF.degree (read (IntegralFramedScalarTarskiIteratedSign.inputContext u))):=
    hD.comp (mem_FP_comp IntegralFramedScalarTarskiIteratedSign.inputContext_FP hr)
  exact H.add (BinaryFn.const 1)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b j,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) j).totalDegree≤budget (pair c b))
variable (hmass : ∀c b j,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) j)≤2^height (pair c b))
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

noncomputable def signs (q : List Bool) :=
  IntegralFramedScalarTarskiIteratedSign.value P D H L F C hs key hpos O hc MF (read∘base) (index MF read)
    (budget∘base) (height∘base)
    (fun c b=>by simpa only [Function.comp_apply,base,pairFst_pair,pairSnd_pair] using dim c (pairFst b))
    (fun c b=>(congrArg (fun z=>(FixedWidthTarskiPrincipalBits.polynomial MF (read z) (index MF read (pair c b))).totalDegree≤budget z)
      (base_pair c b)).mpr (hdegree c (pairFst b) _))
    (fun c b=>(congrArg (fun z=>MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read z) (index MF read (pair c b)))≤2^height z)
      (base_pair c b)).mpr (hmass c (pairFst b) _)) (query q)

noncomputable def value :=CanonicalSignStatisticBits.value
  (signs P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass) (count MF read)

variable (T : IntegralMixedHeaderTablesBits.Tables) (hrT : IntegralMixedFramedHeaderBits.Represents P D H T)
variable (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T) (hk : key∈FP)
variable (hS : (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos).Access)
variable (A : FixedWidthTarskiPrincipalBits.Access MF) (hW : UnaryFn MF.width)
variable (hr : read∈FP) (hD : BinaryFn budget) (hH : BinaryFn height)
variable (hfit : ∀c b,budget (pair c b)<2^MF.width (read (pair c b)))

include hrT a hT hk hS A hW hr hD hH hfit in
theorem signs_evaluator :
    SpaceFunction (signs P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass) :=by
  have E:=IntegralFramedScalarTarskiIteratedSign.evaluator P D H L F C hs key hpos O hc MF
    (read∘base) (index MF read) (budget∘base) (height∘base)
    (fun c b=>by simpa only [Function.comp_apply,base,pairFst_pair,pairSnd_pair] using dim c (pairFst b))
    (fun c b=>(congrArg (fun z=>(FixedWidthTarskiPrincipalBits.polynomial MF (read z) (index MF read (pair c b))).totalDegree≤budget z)
      (base_pair c b)).mpr (hdegree c (pairFst b) _))
    (fun c b=>(congrArg (fun z=>MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read z) (index MF read (pair c b)))≤2^height z)
      (base_pair c b)).mpr (hmass c (pairFst b) _)) T hrT a hT hk hS A hW
    (mem_FP_comp base_FP hr) (index_binary MF read hr A.degree) (hD.comp base_FP) (hH.comp base_FP)
    (fun c b=>by simpa only [Function.comp_apply,base,pairFst_pair,pairSnd_pair] using hfit c (pairFst b))
  exact E.precompose query query_FP

include hrT a hT hk hS A hW hr hD hH hfit in
theorem evaluator :
    SpaceFunction (fun u=>SignStatisticBits.integerCode
      (value P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass u)) :=
  CanonicalSignStatisticBits.evaluator
    (signs_evaluator P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass
      T hrT a hT hk hS A hW hr hD hH hfit) (count MF read) (count_binary MF read hr A.degree)

end LeanCanny.Encoding.IntegralFramedScalarTarskiStatistic
