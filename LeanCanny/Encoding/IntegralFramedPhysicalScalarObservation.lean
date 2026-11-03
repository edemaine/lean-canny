/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
public import LeanCanny.Encoding.IntegralFramedPhysicalNaturalPoint
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixRealization
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
/-! # Scalar suffix powers recover actual prefix observation quotients -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem slotNumber_drop {n B : ℕ} (cs : List (Instruction n B)) (k i : ℕ)
    (hi : i<(cs.drop k).length) :slotNumber cs (k+i)=slotNumber (cs.drop k) i:=by
 induction k generalizing cs with
 | zero=>simp only [Nat.zero_add,List.drop_zero]
 | succ k ih=>
   cases cs with
   | nil=>simp only [List.drop_nil,List.length_nil] at hi;omega
   | cons c cs=>
     simp only [List.drop_succ_cons] at hi ⊢
     change (if k+1+i=0 then arity (c::cs)-1 else slotNumber cs (k+1+i-1))=slotNumber (cs.drop k) i
     rw [ite_eq_right (by omega : k+1+i≠0)]
     have HE :k+1+i-1=k+i:=by omega
     rw [HE]
     exact ih cs hi

theorem scalarTuple_natural (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c)) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w)
    (i : Fin ((family P D H).birth (key c))) :
    IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hp c w hv i=
      IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv
        (slotNumber (commands P D (key c)) i.val):=by
 have HE :(IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) i).val=
     slotNumber (commands P D (key c)) i.val:=by
   unfold IntegralMixedFramedScalarEmbedding.scalarMap
   simp only [Function.comp_apply]
   rw [family_scalar]
   exact enumerate_scalar _ _
 exact (IntegralFramedPhysicalSquare.scalarTuple_map P D H L F C hs key hp c w hv i).trans
   ((IntegralFramedPhysicalSquare.naturalPoint_at P D H L F C hs key hp c w hv
     (IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) i)).symm.trans
       (congrArg (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv) HE))

theorem quotient_observation {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1)
    (φ : (run x cs hc).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : ℕ→ℝ)
    (hφ : ∀i,φ ((run x cs hc).sampler.scalarPrefix.basis.generator i)=
      z (slotNumber cs i.val)^UniformIntegralPowerSchedule.weights S (2^B) cs.length i) :
    ∀i,φ ((run x cs hc).bank.numerator i)/
      ((run x cs hc).bank.denominator i:ℝ)=
        (IntegralMixedFramedRunObservation.ofCommands x cs hc).point z i.val:=by
 intro i
 have HC:=run_canonical x (fun j=>Fin.elim0 j) cs hc
 rw [HC i,hφ i,IntegralMixedFramedRunObservation.point_actual x cs hc z i]
 change z (slotNumber cs i.val)^UniformIntegralPowerSchedule.weights S (2^B) cs.length i /
     ((run x cs hc).bank.denominator i:ℝ)=
   z (enumerate cs ((run x cs hc).sampler.scalar i)).val^
     UniformIntegralPowerSchedule.weights S (2^B) cs.length i /((run x cs hc).bank.denominator i:ℝ)
 rw [run_scalar_number]

theorem quotient_family_observation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool)
    (φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ℕ→ℝ)
    (hφ : ∀i : Fin (commands P D key).length,
      φ (((family P D H).state key).sampler.scalarPrefix.basis.generator i)=
        z (slotNumber (commands P D key) i.val)^
          UniformIntegralPowerSchedule.weights (P.cap (pairFst key)+1) (2^P.width (pairFst key))
            (commands P D key).length i) :
    ∀i : Fin (commands P D key).length,
      φ (((family P D H).state key).bank.numerator i)/(((family P D H).state key).bank.denominator i:ℝ)=
        (IntegralMixedFramedRunObservation.ofCommands
          (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key)) (commands P D key)
          (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))).point z i.val:=
 quotient_observation _ _ _ φ z hφ

theorem prefix_fit (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (c : List Bool) (m : ℕ)
    (hm : m≤IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)) (aux : List Bool) :
    (family P D H).birth (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)≤
      (family P D H).birth (key c):=by
 rw [IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _
   (hm.trans (min_le_right _ _)),IntegralMixedFramedHistoryFamilyBits.family_birth]
 exact hm

private theorem past_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (hr : r=s) (hb : a=b) :
    HEq (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D r) (D.rules r) a)
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D s) (D.rules s) b):=by
 cases hr
 cases hb
 rfl

private theorem root_slots_congr (P : Parameters) (r s : List Bool)
    (cs : List (Instruction (P.ambient r) (P.width r)))
    (ds : List (Instruction (P.ambient s) (P.width s))) (hr : r=s) (hc : HEq cs ds) :
    cs.length=ds.length ∧ ∀i,slotNumber cs i=slotNumber ds i:=by
 cases hr
 cases eq_of_heq hc
 exact ⟨rfl,fun _=>rfl⟩

theorem quotient_prefix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c)) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w)
    (m : ℕ) (hm : m≤IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)) (aux : List Bool)
    (φ : ((family P D H).state (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hp c w hv
        (UniformIntegralPowerSchedule.embed (prefix_fit P D H key c m hm aux) i)^
          UniformIntegralPowerSchedule.weights
            ((family P D H).cap (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux))
            (2^(family P D H).width (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux))
            ((family P D H).birth (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)) i) :
    ∀i : Fin (commands P D (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)).length,
      φ (((family P D H).state (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)).bank.numerator i)/
        (((family P D H).state (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)).bank.denominator i:ℝ)=
      (IntegralMixedFramedRunObservation.ofCommands
        (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)))
        (commands P D (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux))
        (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))).point
          (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv) i.val:=by
 let old:=IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux
 have HB :(family P D H).birth old=m:=
   (IntegralMixedFramedHistoryFamilyBits.family_birth P D H old).trans
     (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (hm.trans (min_le_right _ _)))
 have HO :HEq (commands P D old) (IntegralFramedPhysicalPrefixRealization.past P D key c m):=
   past_congr P D _ _ _ _ (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
     (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (hm.trans (min_le_right _ _)))
 have H0 :(commands P D (key c)).drop ((family P D H).birth (key c)-(family P D H).birth old)=
     IntegralFramedPhysicalPrefixRealization.past P D key c m:=by
   rw [HB,IntegralMixedFramedHistoryFamilyBits.family_birth]
   exact IntegralFramedPhysicalPrefixRealization.drop_eq P D key c m hm
 have HD :HEq ((commands P D (key c)).drop ((family P D H).birth (key c)-(family P D H).birth old))
     (commands P D old):=(heq_of_eq H0).trans HO.symm
 have HSlots:=root_slots_congr P (pairFst (key c)) (pairFst old) _ _
   (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _).symm HD
 apply quotient_family_observation P D H old φ _
 intro i
 have HS :=slotNumber_drop (commands P D (key c)) ((family P D H).birth (key c)-(family P D H).birth old) i.val
   ((congrArg (fun l : ℕ=>i.val<l) HSlots.1).mpr i.isLt)
 have HX :IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hp c w hv
     (UniformIntegralPowerSchedule.embed (prefix_fit P D H key c m hm aux) i)=
     IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv (slotNumber (commands P D old) i.val):=by
   rw [scalarTuple_natural]
   change IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv
     (slotNumber (commands P D (key c)) ((family P D H).birth (key c)-(family P D H).birth old+i.val))=_
   exact congrArg (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv)
     (HS.trans (HSlots.2 i.val))
 exact (hφ i).trans (congrArg (fun v : ℝ=>v^UniformIntegralPowerSchedule.weights
   ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i) HX)

noncomputable def atKeyObservation (P : Parameters) (D : Plan P) (key : List Bool) :=
 IntegralMixedFramedRunObservation.ofCommands
   (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key)) (commands P D key)
   (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))

theorem observation_keyAt (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ) (aux : List Bool)
    (hm : m≤P.cap root+1) :
    atKeyObservation P D (IntegralMixedFramedHistoryFamilyBits.keyAt root m aux)=
      IntegralFramedPhysicalPrefixObservation.atRoot P D root m hm:=by
 let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root m aux
 have HE :atKeyObservation P D key=IntegralFramedPhysicalPrefixObservation.atRoot P D (pairFst key)
     (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _):=rfl
 exact HE.trans (IntegralFramedPhysicalPrefixObservation.at_congr P D _ root _ m _ hm
   (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
   (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ hm))

theorem quotient_prefix_at (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c)) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w)
    (old : List Bool) (m : ℕ) (hm : m≤IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)) (aux : List Bool)
    (he : old=IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key c)) m aux)
    (hfit : (family P D H).birth old≤(family P D H).birth (key c))
    (φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hp c w hv
        (UniformIntegralPowerSchedule.embed hfit i)^UniformIntegralPowerSchedule.weights
          ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i) :
    ∀i : Fin (commands P D old).length,
      φ (((family P D H).state old).bank.numerator i)/(((family P D H).state old).bank.denominator i:ℝ)=
        (atKeyObservation P D old).point (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv) i.val:=by
 subst old
 exact quotient_prefix P D H L F C hs key hp c w hv m hm aux φ hφ

end LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation
