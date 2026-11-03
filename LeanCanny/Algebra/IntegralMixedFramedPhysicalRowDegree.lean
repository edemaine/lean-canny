/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence

/-! # Original-header degree metadata for the full physical sampler -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowDegree
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedHistoryFamilyBits (prefixLength)
open UniformIntegralPowerSchedule
open IntegralMixedHistory IntegralHistorySampler
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def header (P : Parameters) (T : Tables) (q : List Bool) :=
  IntegralMixedCommandHeaderBits.lookup (T.commands (pairFst (pairFst q))) (rowBirth P T q)

theorem header_readers (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    IntegralMixedCommandHeaderBits.Readers (header P T) :=
  IntegralMixedCommandHeaderBits.lookup_readers _ _
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) h.commands)
    (BinaryFn.ofUnary (rowBirth_unary P a T h))

def scalarDegree (P : Parameters) (T : Tables) (q : List Bool) :=
  2^P.width (pairFst (pairFst q))*
    birth (P.cap (pairFst (pairFst q))+1) (2^P.width (pairFst (pairFst q))) (rowBirth P T q)
def physicalPower (P : Parameters) (T : Tables) (q : List Bool) :=
  physical (P.cap (pairFst (pairFst q))+1) (2^P.width (pairFst (pairFst q))) (rowBirth P T q)

theorem scalarDegree_binary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    BinaryFn (scalarDegree P T) := by
  have HR:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HN:=(BinaryFn.const 2).powUnary (a.width.comp HR)
  exact HN.mul (birth_binary ((a.cap.comp HR).add (UnaryFn.const 1)) HN (rowBirth_unary P a T h))

theorem physicalPower_binary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    BinaryFn (physicalPower P T) :=
  physical_binary ((a.cap.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))) (rowBirth_unary P a T h)

def Frozen (P : Parameters) (T : Tables) (q : List Bool) : Prop :=
  P.ambient (pairFst (pairFst q))+2≤localRow P T q ∧
    localRow P T q-(P.ambient (pairFst (pairFst q))+2)<(header P T q).offset

theorem frozen_fppred (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    FPPred (Frozen P T) := by
  have HN:=(a.ambient.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 2)
  have HL:=localRow_unary P a T h
  exact (FPPred.le HN HL).and ((BinaryFn.ofUnary (HL.sub HN)).lt (header_readers P a T h).offset)

noncomputable def degree (P : Parameters) (T : Tables) (q : List Bool) :=
  if Nat.fromBitsLE (pairSnd q)<fullArity P T q then
    if IsScalar P T q then scalarDegree P T q
    else if localRow P T q=P.ambient (pairFst (pairFst q))+1 then
      P.degree (pairFst (pairFst q))*physicalPower P T q
    else if Frozen P T q then physicalPower P T q
    else (P.degree (pairFst (pairFst q))-1)*physicalPower P T q
  else 1

theorem degree_binary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    BinaryFn (degree P T) := by
  have HR:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HP:=physicalPower_binary P a T h
  have HD : BinaryFn (fun q=>P.degree (pairFst (pairFst q))) :=a.degree.comp HR
  have HL:=localRow_unary P a T h
  have HN:=(a.ambient.comp HR).add (UnaryFn.const 1)
  exact BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.ofUnary (fullArity_unary P a T h)))
    (BinaryFn.ite (isScalar_fppred P a T h) (scalarDegree_binary P a T h)
      (BinaryFn.ite (FPPred.eq HL HN) (HD.mul HP)
        (BinaryFn.ite (frozen_fppred P a T h) HP ((HD.sub (BinaryFn.const 1)).mul HP)))) (BinaryFn.const 1)

theorem fresh_scalar_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.degrees (IntegralMixedFramedPhysicalIndex.fresh c)=
      2^B*birth S (2^B) m := by
  cases c <;> rfl

theorem critical_ambient_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (i : Fin (n+1)) :
    (IntegralMixedHistory.criticalStep x hm r).sampler.degrees (Sum.inl (Sum.inr (Sum.inl i)))=
      (P.degree-1)*physical S (2^B) m := rfl

theorem critical_source_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) :
    (IntegralMixedHistory.criticalStep x hm r).sampler.degrees (Sum.inl (Sum.inr (Sum.inr 0)))=
      P.degree*physical S (2^B) m := rfl

theorem critical_height_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (i : Fin (n+1)) :
    (IntegralMixedHistory.criticalStep x hm r).sampler.degrees (Sum.inl (Sum.inr (Sum.inr i.succ)))=
      if i.val<r.offset.val then physical S (2^B) m else (P.degree-1)*physical S (2^B) m := by
  change (if i∈Finset.univ.filter (fun j : Fin (n+1)=>j.val<r.offset.val) then physical S (2^B) m
    else (P.degree-1)*physical S (2^B) m)=_
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]


theorem rowBirth_le (P : Parameters) (T : Tables) (q : List Bool) :
    rowBirth P T q≤prefixLength P (pairFst q) := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

def upper (P : Parameters) (root : List Bool) :=
  (2^P.width root+P.degree root+1)*
    ((2*cap (P.cap root+1) (2^P.width root)+1)*
      birth (P.cap root+1) (2^P.width root) (P.cap root+1))

theorem upper_binary (P : Parameters) (a : Access P) : BinaryFn (upper P) := by
  have HN:=(BinaryFn.const 2).powUnary a.width
  have HS:=a.cap.add (UnaryFn.const 1)
  have HC:=(BinaryFn.ofUnary HS).mul (HN.sub (BinaryFn.const 1))
  exact ((HN.add a.degree).add (BinaryFn.const 1)).mul
    (((BinaryFn.const 2).mul HC).add (BinaryFn.const 1) |>.mul (birth_binary HS HN HS))

theorem upper_pos (P : Parameters) (root : List Bool) : 0<upper P root := by
  unfold upper
  exact Nat.mul_pos (Nat.succ_pos _)
    (Nat.mul_pos (Nat.succ_pos _) (birth_pos _ _ _))

theorem degree_le_upper (P : Parameters) (T : Tables) (q : List Bool) :
    degree P T q≤upper P (pairFst (pairFst q)) := by
  let root:=pairFst (pairFst q)
  let S:=P.cap root+1
  let N:=2^P.width root
  let D:=P.degree root
  let C:=2*cap S N+1
  let W:=birth S N S
  have HB : rowBirth P T q≤S :=
    (rowBirth_le P T q).trans (min_le_right _ _)
  have HS : birth S N (rowBirth P T q)≤W:=birth_le S N _ HB
  have HP : physicalPower P T q≤C*W :=
    Nat.mul_le_mul_left C (birth_le S N _ ((Nat.sub_le _ _).trans HB))
  have HW : W≤C*W := by dsimp only [C]; nlinarith
  have HU : upper P root=(N+D+1)*(C*W):=rfl
  have Hscalar : scalarDegree P T q≤upper P root := by
    change N*birth S N (rowBirth P T q)≤_
    rw [HU]
    exact (Nat.mul_le_mul_left N (HS.trans HW)).trans
      (Nat.mul_le_mul_right _ ((Nat.le_add_right N D).trans (Nat.le_succ _)))
  have HD : D*physicalPower P T q≤upper P root := by
    rw [HU]
    exact (Nat.mul_le_mul_left D HP).trans
      (Nat.mul_le_mul_right _ ((Nat.le_add_left D N).trans (Nat.le_succ _)))
  have HD1 : (D-1)*physicalPower P T q≤upper P root :=
    (Nat.mul_le_mul_right _ (Nat.sub_le D 1)).trans HD
  have Hphysical : physicalPower P T q≤upper P root := by
    rw [HU]
    exact HP.trans (by
      have HB : 1≤N+D+1:=Nat.succ_pos _
      simpa only [one_mul] using Nat.mul_le_mul_right (C*W) HB)
  unfold degree
  split_ifs
  · exact Hscalar
  · exact HD
  · exact Hphysical
  · exact HD1
  · exact (upper_pos P root)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowDegree
