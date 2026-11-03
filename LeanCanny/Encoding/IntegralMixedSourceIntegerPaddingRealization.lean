/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingPrefix
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingRealization
/-! # The actual pre-probe prefix has an honest canonical seed realization -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingRealization
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedIntegerRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realizes_list_iff {n S B : ℕ} {Q : SpatialSource n}
    (initial : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (v : ℕ→ℝ) :
    Realizes (run initial cs hc) v ↔ Realizes (run initial ds hd) v:=by
  cases he
  rfl

private theorem realizes_runAt_congr (P : Parameters) (D : Plan P) (a b : List Bool) (i j : ℕ)
    (ha : i≤P.cap a+1) (hb : j≤P.cap b+1) (hab : a=b) (hij : i=j) (v : ℕ→ℝ) :
    Realizes (IntegralMixedFramedFamilyRunView.runAt P D a i ha) v ↔
      Realizes (IntegralMixedFramedFamilyRunView.runAt P D b j hb) v:=by
  cases hab
  cases hij
  rfl

theorem realizes_at_key_iff (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root aux : List Bool) (b : ℕ) (hb : b≤P.cap root+1) (v : ℕ→ℝ) :
    Realizes (IntegralMixedFramedFamilyRunView.stateView P D H (keyAt root b aux)) v ↔
      Realizes (IntegralMixedFramedFamilyRunView.runAt P D root b hb) v :=by
  change Realizes (IntegralMixedFramedFamilyRunView.runAt P D
    (pairFst (keyAt root b aux)) (prefixLength P (keyAt root b aux)) (min_le_right _ _)) v ↔ _
  exact realizes_runAt_congr P D _ root _ b _ hb (pairFst_pair _ _) (keyAt_prefix P root b aux hb) v

variable (P : Parameters) (R : (root : List Bool)→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root,(R root).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
 (IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom))

include H in
theorem runAt_realizes (root aux : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)++[probe]))
    (charge : ℕ) (hcharge : (R root).degree=BoundedZeroSource.powerDegree charge)
    (v : ℕ→ℝ)
    (hv : Realizes (IntegralMixedFramedFamilyRunView.runAt P D root (N root+oldCodes.length)
      (IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht 0 (Nat.zero_le _))) v)
    (p : Fin (P.ambient root+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree)).eval₂
      (Int.castRingHom ℝ) p=0) :
    Realizes (IntegralMixedFramedFamilyRunView.runAt P D root (N root+(oldCodes.length+k))
      (IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht k le_rfl))
      (IntegralMixedCanonicalPadding.values (p 0) v k) :=by
  let cs:=paddedPast (defaultInstruction P D root) ((D).rules root) (N root+oldCodes.length)
  have Hbefore : cs.length≤(P.cap root+1)+1:=by
    rw [paddedPast_length]
    exact (IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht 0 (Nat.zero_le _)).trans (Nat.le_succ _)
  have HE:=IntegralMixedSourceIntegerPaddingPrefix.past_padding P R hn hd hcap N T hz hT hroom H root aux oldCodes k probe ht
  have HA : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (R root).degree≤2^P.width root:=by
    rw [hd]
    exact hcap root
  have Hafter : (List.replicate k (IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root)++cs).length≤(P.cap root+1)+1:=by
    rw [←HE,paddedPast_length]
    exact (IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht k le_rfl).trans (Nat.le_succ _)
  have HR:=IntegralMixedCanonicalPadding.run_realizes (initial P D root) cs Hbefore (R root)
    (IntegralMixedCausalUnitRecordBits.record (R root) (hn root) 0
      (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0) HA).source_cap
    (hn root) charge hcharge HA v hv p hp hg k Hafter
  exact (realizes_list_iff (initial P D root) _ _ _ Hafter HE (IntegralMixedCanonicalPadding.values (p 0) v k)).mpr HR

include H in
theorem canonical_realizes (root aux : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)++[probe]))
    (charge : ℕ) (hcharge : (R root).degree=BoundedZeroSource.powerDegree charge)
    (v : ℕ→ℝ)
    (hv : Realizes (IntegralMixedFramedFamilyRunView.stateView P D H
      (keyAt root (N root+oldCodes.length) aux)) v)
    (p : Fin (P.ambient root+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree)).eval₂
      (Int.castRingHom ℝ) p=0) :
    Realizes (IntegralMixedFramedFamilyRunView.stateView P D H
      (keyAt root (N root+(oldCodes.length+k)) aux)) (IntegralMixedCanonicalPadding.values (p 0) v k) :=by
  have HB:=IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht 0 (Nat.zero_le _)
  have HA:=IntegralMixedSourceIntegerPaddingPrefix.prefix_bound P N hroom root oldCodes k probe ht k le_rfl
  have HV:=(realizes_at_key_iff P D H root aux (N root+oldCodes.length) HB v).mp hv
  have HR:=runAt_realizes P R hn hd hcap N T hz hT hroom H root aux oldCodes k probe ht charge hcharge v HV p hp hg
  exact (realizes_at_key_iff P D H root aux (N root+(oldCodes.length+k)) HA
    (IntegralMixedCanonicalPadding.values (p 0) v k)).mpr HR

end LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingRealization
