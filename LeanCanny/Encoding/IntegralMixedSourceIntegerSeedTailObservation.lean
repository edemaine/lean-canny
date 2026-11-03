/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
/-! # Actual seed-tail completion preserves every old physical column -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_congr {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd:=by cases he;rfl

variable (P :Parameters) (R :(root :List Bool)→SpatialSource (P.ambient root))
  (hn :∀root,0<P.ambient root) (hd :∀root,(R root).degree=P.degree root)
  (hcap :∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N :List Bool→ℕ) (T :IntegerPolynomialRootQueriesBits.Source) (hz :∀q,T.polynomial q≠0)
  (hT :∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom :∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn
  (fun root _=>hd root) hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
variable (H :IntegralMixedFramedHistoryFamilyBits.Data P
  (IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn
    (fun root _=>hd root) hcap N T hz hT hroom))

include H in
theorem full_observation (root aux :List Bool) (codes :List (List Bool)) (k :ℕ)
    (ht :IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)))
    (charge :ℕ) (hcharge :(R root).degree=BoundedZeroSource.powerDegree charge)
    (z :ℕ→ℝ)
    (hroot :(IntegralFramedPhysicalPrefixObservation.atRoot P D root (N root+codes.length)
      (before_bound P N hroom root codes k ht)).Roots z)
    (p :Fin (P.ambient root+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃y :ℕ→ℝ,
      (ofCommands (initial P D root) ((D).rules root) (by have HH:=(D).room root;omega)).Roots y ∧
      (∀i,i<(IntegralFramedPhysicalPrefixObservation.atRoot P D root (N root+codes.length)
        (before_bound P N hroom root codes k ht)).arity→y i=z i) ∧
      ∀i,i<((D).rules root).length→
        (ofCommands (initial P D root) ((D).rules root) (by have HH:=(D).room root;omega)).point y i=
          IntegralMixedCanonicalPadding.values (p 0)
            ((IntegralFramedPhysicalPrefixObservation.atRoot P D root (N root+codes.length)
              (before_bound P N hroom root codes k ht)).point z) k i :=by
  let cs:=paddedPast (defaultInstruction P D root) ((D).rules root) (N root+codes.length)
  have HB :cs.length≤(P.cap root+1)+1:=by
    rw [paddedPast_length]
    exact (before_bound P N hroom root codes k ht).trans (Nat.le_succ _)
  have HE:=full_seed_tail P R hn hd hcap N T hz hT hroom H root aux codes k ht
  have HC :IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (R root).degree≤2^P.width root:=by
    rw [hd]
    exact hcap root
  let seed:=IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root
  have HA :(List.replicate k seed++cs).length≤(P.cap root+1)+1:=by
    rw [←HE]
    have HH:=(D).room root
    omega
  have HR:=IntegralMixedCanonicalPadding.run_observation (initial P D root) cs HB (R root)
    (IntegralMixedCausalUnitRecordBits.record (R root) (hn root) 0
      (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0) HC).source_cap
    (hn root) charge hcharge HC z hroot p hp hg k HA
  obtain ⟨y,hy,hold,hpoint⟩:=HR
  have HO:=observation_congr (initial P D root) ((D).rules root) (List.replicate k seed++cs)
    (by have HH:=(D).room root;omega) HA HE
  refine ⟨y,(congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots y) HO).mpr hy,hold,?_⟩
  intro i hi
  have HI :i<(List.replicate k seed++cs).length:=by rw [←HE];exact hi
  exact (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point y i) HO).trans
    (hpoint ⟨i,HI⟩)

end LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
