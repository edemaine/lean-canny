/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionReadback
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointFrame
/-! # Endpoint references after an anchor and coordinate captures

The midpoint frame used by the captures may contain a doubled row. The
endpoint child instead retains the original atomic rows and reads its
endpoint from the shifted old bank.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {F : Frame n}

def capturedReference (q : ℕ) (u : Fin m) : Fin (m+q):=
  ⟨q+u.val,by omega⟩

@[simp] theorem capturedReference_val (q : ℕ) (u : Fin m) :
    (capturedReference q u).val=q+u.val:=rfl

noncomputable def capturedBaseFrame (HA : AtomicRows F m) (q : ℕ) : Frame n:=
  IntegralMixedPointCompanion.frame F.frozen (fun _=>false) (fun i=>.single (HA.atom i)) q

theorem capturedBaseFrame_zero (HA : AtomicRows F m) : capturedBaseFrame HA 0=F:=HA.frame_eq.symm

theorem capturedBaseFrame_succ (HA : AtomicRows F m) (q : ℕ) :
    capturedBaseFrame HA (q+1)=retained (capturedBaseFrame HA q):=
  IntegralMixedPointCompanion.frame_succ _ _ _ _

theorem capturedBaseFrame_atomic (HA : AtomicRows F m) (q : ℕ) :
    AtomicRows (capturedBaseFrame HA q) (m+q):=by
  induction q with
  | zero=>simpa only [capturedBaseFrame_zero,Nat.add_zero] using HA
  | succ q ih=>rw [capturedBaseFrame_succ]; exact ih.retained

theorem PrefixFrozen.capturedBaseFrame (HP : PrefixFrozen F) (HA : AtomicRows F m) (q : ℕ) :
    PrefixFrozen (capturedBaseFrame HA q):=HP

theorem FreeNormal.capturedBaseFrame (HF : FreeNormal F) (HA : AtomicRows F m) (q : ℕ) :
    FreeNormal (capturedBaseFrame HA q):=by
  induction q with
  | zero=>simpa only [capturedBaseFrame_zero] using HF
  | succ q ih=>rw [capturedBaseFrame_succ]; exact ih.retained

theorem capturedBaseFrame_slice {P : SpatialSource n} (HA : AtomicRows F m)
    {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (old : Fin m→ℝ)
    (js : List (IntegralMixedPointCompanion.Free frozen)) :
    slice P (capturedBaseFrame HA js.length) (IntegralMixedPointCompanion.values p old js)=
      slice P F old:=by
  induction js with
  | nil=>change slice P (capturedBaseFrame HA 0) old=slice P F old
         rw [capturedBaseFrame_zero]
  | cons j js ih=>
    change slice P (capturedBaseFrame HA (js.length+1))
      (Fin.cons (p j.val) (IntegralMixedPointCompanion.values p old js))=_
    rw [capturedBaseFrame_succ,slice_retained,ih]

theorem capturedReference_value {frozen : Finset (Fin (n+1))}
    (p : Fin (n+1)→ℝ) (old : Fin m→ℝ)
    (js : List (IntegralMixedPointCompanion.Free frozen)) (u : Fin m) :
    IntegralMixedPointCompanion.values p old js (capturedReference js.length u)=old u:=
  IntegralMixedPointCompanion.values_old p old js u

end LeanCanny.Geometry.IntegralMixedFrozenFrame
