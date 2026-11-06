/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredAssociation
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderPreludePhaseGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociationGeometry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedTargetAttachment
/-! # Native anchored association joins actual marked preludes

The converse requires genuine paths from the two seeds to their own preludes.
These paths are not consequences of native validity alone.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry IntegralMixedHistory
open FormulaSignSlotRadialProviderGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_point_heq {n m:ℕ} (h:n=m) (p:Fin m→ℝ) :
    HEq (FormulaSignSlotRadialProviderPairGeometry.castPoint h p) p:=by cases h;rfl

private theorem polynomial_heq {n m:ℕ} (P:SpatialSource n) (Q:SpatialSource m)
    (hd:n=m) (hp:HEq P Q) :
    HEq (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree):=by
  cases hd
  cases eq_of_heq hp
  rfl

private theorem joined_transport {n m:ℕ} (P:MvPolynomial (Fin n) ℤ) (Q:MvPolynomial (Fin m) ℤ)
    (hd:n=m) (hp:HEq P Q) (x y:Fin n→ℝ) (u v:Fin m→ℝ) (hx:HEq x u) (hy:HEq y v)
    (HJ:JoinedIn {z |P.eval₂ (Int.castRingHom ℝ) z=0} x y) :
    JoinedIn {z |Q.eval₂ (Int.castRingHom ℝ) z=0} u v:=by
  cases hd
  cases eq_of_heq hp
  cases eq_of_heq hx
  cases eq_of_heq hy
  exact HJ

local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider"=>FormulaSignSlotRadialProviderAtomic.provider
local notation "depth"=>FormulaSignSlotRadialProviderAtomic.depth
local notation "num"=>FormulaSignSlotRadialProviderMarkedGeometry.number
local notation "Geo"=>FormulaSignSlotRadialProviderMarkedGeometry.zeroSet
local notation "Poly"=>FormulaSignSlotRadialProviderMarkedGeometry.polynomial
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.point
  FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint pointAt preludeAt
  FormulaSignSlotRadialProviderPairGeometry.externalPoint FormulaSignSlotRadialProviderAtomicGeometry.point
  FormulaSignSlotRadialProviderAtomicGeometry.source

noncomputable def externalPrelude (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext) :
    Fin (num (provider a)+4)→ℝ:=
  FormulaSignSlotRadialProviderPairGeometry.castPoint
    (congrArg (·+4) (FormulaSignSlotRadialProviderPairGeometry.number_pair a ext hp))
    (preludeAt (provider ext) ext he rfl)

theorem externalPrelude_heq (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext) :
    HEq (externalPrelude a ext hp he) (preludeAt (provider ext) ext he rfl):=cast_point_heq _ _

private theorem pair_polynomial_heq (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) :
    HEq (Poly (provider a)) (Poly (provider ext)):=by
  exact polynomial_heq _ _ (congrArg (·+3) (FormulaSignSlotRadialProviderPairGeometry.number_pair a ext hp))
    ((FormulaSignSlotRadialProviderAtomicGeometry.source_heq _).symm.trans
      ((FormulaSignSlotRadialProviderPairGeometry.source_pair a ext hp).trans
        (FormulaSignSlotRadialProviderAtomicGeometry.source_heq _)))

theorem external_path (a ext:List Bool)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext)) (he:A ext)
    (HJ:JoinedIn (Geo (provider ext)) (pointAt (provider ext) ext he rfl)
      (preludeAt (provider ext) ext he rfl)) :
    JoinedIn (Geo (provider a)) (FormulaSignSlotRadialProviderPairGeometry.externalPoint a ext hp he)
      (externalPrelude a ext hp he):=by
  exact joined_transport _ _ (congrArg (·+4) (FormulaSignSlotRadialProviderPairGeometry.number_pair a ext hp)).symm
    (pair_polynomial_heq a ext hp).symm _ _ _ _
    ((pointAt_heq _ ext he rfl).symm.trans
      (FormulaSignSlotRadialProviderPairGeometry.externalPoint_heq a ext hp he).symm)
    (externalPrelude_heq a ext hp he).symm HJ

theorem attached_of_reachable_marker (c a m:List Bool) (ha:A a) (hm:A m)
    (hca:provider a=c) (hcm:provider m=c) (HR:RawReachable c a m)
    (HM:m∈FormulaSignSlotRadialProviderMarkedAnchor.language) :
    JoinedIn (Geo c) (pointAt c a ha hca) (preludeAt c a ha hca):=by
  have HE:= (FormulaSignSlotRadialProviderMarkedAnchor.language_native_iff m hm).mp HM
  have HP:pointAt c m hm hcm=preludeAt c m hm hcm:=
    eq_of_heq ((native_pointAt_heq c m hm hcm).symm.trans (HE.trans (preludeAt_heq c m hm hcm)))
  have HJ:=raw_reachable_joined c a m HR
  change JoinedIn (Geo c) (pointAt c a ha hca) (pointAt c m hm hcm) at HJ
  rw [HP] at HJ
  exact HJ.trans (FormulaSignSlotRadialProviderPreludePhaseGeometry.prelude_joined_same_provider c m a hm ha hcm hca)

theorem language_joined_preludes (a ext:List Bool) (ha:A a) (he:A ext)
    (hda:depth a=0) (hde:depth ext=0)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext))
    (hx:FormulaSignSlotRadialExternalContext.external (provider ext))
    (HL:pair a ext∈FormulaSignSlotRadialProviderAnchoredAssociation.language) :
    JoinedIn (Geo (provider a)) (preludeAt (provider a) a ha rfl) (externalPrelude a ext hp he):=by
  obtain ⟨HAssoc,mOld,mExt,HO,HE,MO,ME⟩:=
    (FormulaSignSlotRadialProviderAnchoredAssociation.language_iff a ext).mp HL
  have HA:=attached_of_reachable_marker (provider a) a mOld ha HO.2.1 rfl HO.2.2.2.1 HO MO
  have HB:=attached_of_reachable_marker (provider ext) ext mExt he HE.2.1 rfl HE.2.2.2.1 HE ME
  have HC:=(FormulaSignSlotRadialProviderAssociation.language_joined_iff a ext ha he hda hde hp hx).mp
    ((FormulaSignSlotRadialProviderAssociation.language_iff a ext).mpr HAssoc)
  exact HA.symm.trans (HC.trans (external_path a ext hp he HB))

theorem language_of_joined_preludes (a ext:List Bool) (ha:A a) (he:A ext)
    (hda:depth a=0) (hde:depth ext=0)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext))
    (hx:FormulaSignSlotRadialExternalContext.external (provider ext))
    (HA:JoinedIn (Geo (provider a)) (pointAt (provider a) a ha rfl) (preludeAt (provider a) a ha rfl))
    (HE:JoinedIn (Geo (provider ext)) (pointAt (provider ext) ext he rfl) (preludeAt (provider ext) ext he rfl))
    (HJ:JoinedIn (Geo (provider a)) (preludeAt (provider a) a ha rfl) (externalPrelude a ext hp he)) :
    pair a ext∈FormulaSignSlotRadialProviderAnchoredAssociation.language:=by
  have HC:=HA.trans (HJ.trans (external_path a ext hp he HE).symm)
  have HAssoc:=(FormulaSignSlotRadialProviderAssociation.language_iff a ext).mp
    ((FormulaSignSlotRadialProviderAssociation.language_joined_iff a ext ha he hda hde hp hx).mpr HC)
  obtain ⟨mOld,hmOld,_,_,HO,MO,_⟩:=
    FormulaSignSlotRadialProviderProperAppend.exists_reachable_marked_anchor_of_source_path
      (provider a) a ha rfl hda HA
  obtain ⟨mExt,hmExt,_,_,HExt,ME,_⟩:=
    FormulaSignSlotRadialProviderProperAppend.exists_reachable_marked_anchor_of_source_path
      (provider ext) ext he rfl hde HE
  exact (FormulaSignSlotRadialProviderAnchoredAssociation.language_iff a ext).mpr
    ⟨HAssoc,mOld,mExt,HO,HExt,MO,ME⟩

theorem language_iff_joined_preludes_of_attachments (a ext:List Bool) (ha:A a) (he:A ext)
    (hda:depth a=0) (hde:depth ext=0)
    (hp:provider a=FormulaSignSlotRadialProviderPair.oldOf (provider ext))
    (hx:FormulaSignSlotRadialExternalContext.external (provider ext))
    (HA:JoinedIn (Geo (provider a)) (pointAt (provider a) a ha rfl) (preludeAt (provider a) a ha rfl))
    (HE:JoinedIn (Geo (provider ext)) (pointAt (provider ext) ext he rfl) (preludeAt (provider ext) ext he rfl)) :
    pair a ext∈FormulaSignSlotRadialProviderAnchoredAssociation.language↔
      JoinedIn (Geo (provider a)) (preludeAt (provider a) a ha rfl) (externalPrelude a ext hp he):=
  ⟨language_joined_preludes a ext ha he hda hde hp hx,
    language_of_joined_preludes a ext ha he hda hde hp hx HA HE⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredGeometry
