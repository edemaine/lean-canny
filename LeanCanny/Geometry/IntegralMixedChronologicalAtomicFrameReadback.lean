/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalOptionalPairSweep
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointActual
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointActual
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointRealization
public import LeanCanny.Geometry.IntegralMixedCapturedEndpointFrame

/-! # Literal frame equality determines the actual atomic rows

The atomic row witness is not assumed to choose a particular code. Its
zero/reference expression determines its bounded retained atom uniquely.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem atom_value_injective : Function.Injective (Atom.value (birth:=m)) :=by
  intro a b H
  cases a with
  | none=>
    cases b with
    | none=>rfl
    | some b=>cases H
  | some a=>
    cases b with
    | none=>cases H
    | some b=>
      apply congrArg some
      apply Fin.ext
      exact AffineExpr.reference.inj H

theorem atomic_atom (d : Descriptor n m) (F : Frame n) (HA : AtomicRows F m)
    (HE : F=d.frame) (i : Fin (n+1)) : HA.atom i=d.atom i :=by
  subst F
  apply atom_value_injective
  exact (HA.atom_value i).symm

theorem midpoint_rows (d : Descriptor n m) (hk : d.labels.length<n+1)
    (HA : AtomicRows d.frame m) (a b : Fin m) :
    referencedMidpointRows HA (IntegralMixedChronologicalMidpoint.next d hk)
      (IntegralMixedChronologicalMidpoint.reference a) (IntegralMixedChronologicalMidpoint.reference b)=
      IntegralMixedChronologicalMidpoint.rows d hk a b :=by
  funext i
  unfold referencedMidpointRows IntegralMixedChronologicalMidpoint.rows
  split_ifs
  · rfl
  · exact congrArg Row.single (atomic_atom d d.frame HA rfl i)

theorem midpoint_data_code (d : Descriptor n m) (hk : d.labels.length<n+1)
    (HA : AtomicRows d.frame m) (a b : Fin m) (g j : Fin (n+1))
    (hg : g∉insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen)
    (hj : j∉insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen) :
    (referencedMidpointData HA (IntegralMixedChronologicalMidpoint.next d hk)
      (IntegralMixedChronologicalMidpoint.reference a) (IntegralMixedChronologicalMidpoint.reference b) g j hg hj).code=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        a.val b.val g.val j.val :=by
  rw [←IntegralMixedChronologicalMidpointCode.data_code d hk a b g j hg hj]
  unfold referencedMidpointData IntegralMixedChronologicalMidpointCode.data
  rw [midpoint_rows]
  rfl

theorem captured_frame (d : Descriptor n m) (F : Frame n) (HA : AtomicRows F m)
    (HE : F=d.frame) (q : ℕ) : capturedBaseFrame HA q=(retainMany d q).frame :=by
  induction q with
  | zero=>exact (capturedBaseFrame_zero HA).trans HE
  | succ q ih=>
    rw [capturedBaseFrame_succ,ih]
    exact (retainMany d q).frame_retain.symm

theorem freeze_frozen (d : Descriptor n m) (a : Fin m) (hk : d.labels.length<n+1) :
    (d.freeze a hk).frame.frozen=insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen :=by
  ext i
  rw [(d.freeze a hk).frozen_mem,d.freeze_length,Finset.mem_insert,d.frozen_mem,Fin.ext_iff]
  change i.val<d.labels.length+1 ↔ i.val=d.labels.length ∨ i.val<d.labels.length
  omega

theorem freeze_atom (d : Descriptor n m) (a : Fin m) (hk : d.labels.length<n+1) (i : Fin (n+1)) :
    (d.freeze a hk).atom i=if i=IntegralMixedChronologicalMidpoint.next d hk then
      some (IntegralMixedChronologicalMidpoint.reference a) else d.atom i :=by
  by_cases hi : i.val<d.labels.length
  · have HN : i≠IntegralMixedChronologicalMidpoint.next d hk:=by
      intro HE
      have HH:=congrArg Fin.val HE
      change i.val=d.labels.length at HH
      omega
    have HI : i.val<(d.freeze a hk).labels.length:=by rw [d.freeze_length];omega
    rw [ite_eq_right HN,Descriptor.atom,dite_eq_left HI,Descriptor.atom,dite_eq_left hi]
    exact congrArg some (d.freeze_reference_old a hk ⟨i.val,hi⟩)
  · by_cases he : i.val=d.labels.length
    · have HE : i=IntegralMixedChronologicalMidpoint.next d hk:=Fin.ext he
      have HI : i.val<(d.freeze a hk).labels.length:=by rw [d.freeze_length];omega
      rw [ite_eq_left HE,Descriptor.atom,dite_eq_left HI]
      apply congrArg some
      have HJ : (⟨i.val,HI⟩ : Fin (d.freeze a hk).labels.length)=
          ⟨d.labels.length,by rw [d.freeze_length];omega⟩:=Fin.ext he
      rw [HJ]
      exact d.freeze_reference_last a hk
    · have HN : i≠IntegralMixedChronologicalMidpoint.next d hk:=fun HE=>he (congrArg Fin.val HE)
      have HI : ¬i.val<(d.freeze a hk).labels.length:=by rw [d.freeze_length];omega
      rw [ite_eq_right HN,Descriptor.atom,dite_eq_right HI,Descriptor.atom,dite_eq_right hi]

theorem endpoint_rows (d : Descriptor n m) (hk : d.labels.length<n+1)
    (HA : AtomicRows d.frame m) (a : Fin m) :
    referencedEndpointRows HA (IntegralMixedChronologicalMidpoint.next d hk)
      (IntegralMixedChronologicalMidpoint.reference a)=fun i=>Row.single ((d.freeze a hk).atom i) :=by
  funext i
  rw [freeze_atom]
  unfold referencedEndpointRows
  split_ifs
  · rfl
  · exact congrArg Row.single (atomic_atom d d.frame HA rfl i)

theorem original_data_congr (s t : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows otherRows : Fin (n+1)→Row m) (g j : Fin (n+1))
    (hg : g∉s) (hj : j∉s) (hg' : g∉t) (hj' : j∉t) (HS : s=t) (HR : rows=otherRows) :
    originalPointData s double rows g j hg hj=originalPointData t double otherRows g j hg' hj' :=by
  subst t
  subst otherRows
  rfl

theorem endpoint_data_code (d : Descriptor n m) (hk : d.labels.length<n+1)
    (HA : AtomicRows d.frame m) (a : Fin m) (g j : Fin (n+1))
    (hg : g∉insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen)
    (hj : j∉insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen) :
    (originalPointData (insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen) (fun _=>false)
      (referencedEndpointRows HA (IntegralMixedChronologicalMidpoint.next d hk)
        (IntegralMixedChronologicalMidpoint.reference a)) g j hg hj).code=
      IntegralMixedChronologicalEndpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        a.val g.val j.val :=by
  have HG : g∉(d.freeze a hk).frame.frozen:=by rw [freeze_frozen];exact hg
  have HJ : j∉(d.freeze a hk).frame.frozen:=by rw [freeze_frozen];exact hj
  rw [←IntegralMixedChronologicalEndpointCode.data_code d a hk g j HG HJ]
  apply congrArg IntegralMixedCriticalRecordConstructor.Data.code
  exact original_data_congr _ _ _ _ _ g j hg hj HG HJ (freeze_frozen d a hk).symm
    (endpoint_rows d hk HA a)

theorem midpoint_code_of_eq (d : Descriptor n m) (hk : d.labels.length<n+1)
    (F : Frame n) (HA : AtomicRows F m) (HE : F=d.frame)
    (h : Fin (n+1)) (HH : h=IntegralMixedChronologicalMidpoint.next d hk)
    (u v a b : Fin m) (HU : u=IntegralMixedChronologicalMidpoint.reference a)
    (HV : v=IntegralMixedChronologicalMidpoint.reference b) (g j : Fin (n+1))
    (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen) :
    (referencedMidpointData HA h u v g j hg hj).code=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        a.val b.val g.val j.val :=by
  subst F
  subst h
  subst u
  subst v
  exact midpoint_data_code d hk HA a b g j hg hj

theorem endpoint_code_of_eq (d : Descriptor n m) (hk : d.labels.length<n+1)
    (F : Frame n) (HA : AtomicRows F m) (HE : F=d.frame)
    (h : Fin (n+1)) (HH : h=IntegralMixedChronologicalMidpoint.next d hk)
    (u a : Fin m) (HU : u=IntegralMixedChronologicalMidpoint.reference a) (g j : Fin (n+1))
    (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen) :
    (originalPointData (insert h F.frozen) (fun _=>false) (referencedEndpointRows HA h u) g j hg hj).code=
      IntegralMixedChronologicalEndpointCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        a.val g.val j.val :=by
  subst F
  subst h
  subst u
  exact endpoint_data_code d hk HA a g j hg hj

theorem endpoint_frame (d : Descriptor n m) (hk : d.labels.length<n+1)
    (HA : AtomicRows d.frame m) (a : Fin m) :
    referencedEndpointFrame HA (IntegralMixedChronologicalMidpoint.next d hk)
      (IntegralMixedChronologicalMidpoint.reference a)=(d.freeze a hk).frame :=by
  have HS:=freeze_frozen d a hk
  unfold referencedEndpointFrame
  rw [endpoint_rows]
  change originalFrame (insert (IntegralMixedChronologicalMidpoint.next d hk) d.frame.frozen)
    (fun _=>false) (fun i=>Row.single ((d.freeze a hk).atom i))=
      originalFrame (d.freeze a hk).frame.frozen (fun _=>false) (fun i=>Row.single ((d.freeze a hk).atom i))
  rw [HS]

theorem endpoint_frame_of_eq (d : Descriptor n m) (hk : d.labels.length<n+1)
    (F : Frame n) (HA : AtomicRows F m) (HE : F=d.frame)
    (h : Fin (n+1)) (HH : h=IntegralMixedChronologicalMidpoint.next d hk)
    (u a : Fin m) (HU : u=IntegralMixedChronologicalMidpoint.reference a) :
    referencedEndpointFrame HA h u=(d.freeze a hk).frame :=by
  subst F
  subst h
  subst u
  exact endpoint_frame d hk HA a

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
