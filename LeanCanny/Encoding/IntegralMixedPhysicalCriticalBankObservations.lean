/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalIntervalEndpoints
public import LeanCanny.Encoding.IntegralFramedPhysicalBankNaturalPoint
/-! # The native old-bank scan reads carrier-free observations of one joint tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank
local notation "B" => bank hn ht ha hR outer

theorem bank_point_observation (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer child) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key n outer child q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key n outer child) (positive hn ht ha hR outer child) q w hv j=z j.val)
    (i : ℕ) (hi : i<birth n outer false q) :
    IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR outer child q w hv i=
      (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key n outer child q)).point
        z (i+if child then 1 else 0) :=by
  have HE:=IntegralFramedPhysicalSquare.bank_observation_of_joint (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (key n outer child) (positive hn ht ha hR outer child)
    q w hv z hz (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR outer child q
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)))
  exact HE.symm.trans (congrArg (fun j=>(IntegralMixedFullBankObservation.atFamily
    (B).parameters (B).plan (B).data (key n outer child q)).point z j)
      (IntegralMixedPhysicalCriticalBankEquality.coordinate_val hn ht ha hR outer child q i 0 hi))

theorem newest_observation (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key n outer true q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key n outer true) (positive hn ht ha hR outer true) q w hv j=z j.val) :
    newestPoint hn ht ha hR outer q w hv=
      (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key n outer true q)).point z 0 :=
  (IntegralFramedPhysicalSquare.bank_observation_of_joint (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (key n outer true) (positive hn ht ha hR outer true)
    q w hv z hz ⟨0,positive hn ht ha hR outer true q⟩).symm

theorem agrees_iff_observations (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q w)
    (z : ℕ→ℝ)
    (hz : ∀j : Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan (key n outer true q)),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (key n outer true) (positive hn ht ha hR outer true) q w hv j=z j.val) :
    IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR outer (pair q w) ↔
      ∀i<birth n outer false q,
        IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR outer false q
          (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
        (IntegralMixedFullBankObservation.atFamily (B).parameters (B).plan (B).data (key n outer true q)).point z (i+1) :=by
  rw [IntegralMixedPhysicalCriticalBankEquality.agrees_iff hn ht ha hR outer q w hp hv]
  constructor
  · intro HE i hi
    exact (HE i hi).trans (bank_point_observation hn ht ha hR outer true q w hv z hz i hi)
  · intro HE i hi
    exact (HE i hi).trans (bank_point_observation hn ht ha hR outer true q w hv z hz i hi).symm

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
