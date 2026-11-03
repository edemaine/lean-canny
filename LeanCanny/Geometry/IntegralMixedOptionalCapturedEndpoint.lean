/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCapturedEndpointFrame
public import LeanCanny.Geometry.IntegralMixedOptionalJointSlab
public import LeanCanny.Geometry.IntegralMixedMatchedSlabBlock
/-! # Optional endpoint references survive the anchor and all captures

The endpoint reference comes from the actual optional-pair result. It is
shifted once for the physical anchor and once per coordinate capture.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {a b : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

def PairResult.endpointIndex (R : PairResult x F z φ values a b hn hcap)
    (q : ℕ) (right : Bool) : Fin (m+R.commands.length+1+q):=
  capturedReference q (if right then R.right.succ else R.left.succ)

theorem PairResult.endpointIndex_val (R : PairResult x F z φ values a b hn hcap)
    (q : ℕ) (right : Bool) :
    (R.endpointIndex q right).val=q+1+(if right then R.right.val else R.left.val):=by
  cases right <;> simp only [PairResult.endpointIndex,capturedReference_val,
    Bool.false_eq_true,ite_false,ite_true,Fin.val_succ] <;> omega

noncomputable def PairResult.capturedFrame (R : PairResult x F z φ values a b hn hcap)
    (q : ℕ) : Frame n:=capturedBaseFrame R.atomic.retained q

theorem PairResult.capturedFrame_slice (R : PairResult x F z φ values a b hn hcap)
    {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (anchor : ℝ)
    (js : List (IntegralMixedPointCompanion.Free frozen)) :
    slice P (R.capturedFrame js.length)
      (IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js)=slice P F values:=by
  rw [PairResult.capturedFrame,capturedBaseFrame_slice,slice_retained,R.slice_eq]

theorem PairResult.capturedFrame_atomic (R : PairResult x F z φ values a b hn hcap) (q : ℕ) :
    AtomicRows (R.capturedFrame q) (m+R.commands.length+1+q):=
  capturedBaseFrame_atomic R.atomic.retained q

theorem PairResult.endpoint_value (R : PairResult x F z φ values a b hn hcap)
    {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (anchor : ℝ)
    (js : List (IntegralMixedPointCompanion.Free frozen)) (right : Bool) :
    IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js
      (R.endpointIndex js.length right)=(if right then b else a):=by
  unfold PairResult.endpointIndex
  rw [capturedReference_value]
  cases right
  · exact R.left_value
  · exact R.right_value

noncomputable def PairResult.endpointFrame (R : PairResult x F z φ values a b hn hcap)
    (h : Fin (n+1)) (q : ℕ) (right : Bool) : Frame n:=
  referencedEndpointFrame (R.capturedFrame_atomic q) h (R.endpointIndex q right)

theorem PairResult.endpointFrame_slice (R : PairResult x F z φ values a b hn hcap)
    (h : Fin (n+1)) (hh : h∉F.frozen)
    {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (anchor : ℝ)
    (js : List (IntegralMixedPointCompanion.Free frozen)) (right : Bool) :
    slice P (R.endpointFrame h js.length right)
      (IntegralMixedPointCompanion.values p (Fin.cons anchor R.nextValues) js)=
      slice P F values∩{y | y h=(if right then b else a)}:=by
  have hh' : h∉(R.capturedFrame js.length).frozen:=by
    change h∉R.frame.frozen
    rw [R.frozen]
    exact hh
  rw [PairResult.endpointFrame,referencedEndpointFrame_slice _ h hh',
    R.capturedFrame_slice,R.endpoint_value]

theorem PairResult.endpointFrame_prefix (R : PairResult x F z φ values a b hn hcap)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (q : ℕ) (right : Bool) : PrefixFrozen (R.endpointFrame h q right):=by
  have HP : PrefixFrozen (R.capturedFrame q):=
    R.prefixFrozen.retained.capturedBaseFrame R.atomic.retained q
  apply HP.referencedEndpointFrame (R.capturedFrame_atomic q) h
  · change h.val=R.frame.frozen.card
    rw [R.frozen]
    exact hfirst
  · change h∉R.frame.frozen
    rw [R.frozen]
    exact hh

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
