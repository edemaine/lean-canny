/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecision
/-! # Streamed decisions read the literal source interval

The reusable packet contract concerns individual signs. Exact head/seed
degrees and both Tarski statistics are checked by the native decision.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecisionReadback
open LeanCanny.Algebra LeanCanny.Computation Polynomial PrincipalSubresultant Set
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
  (D:List Bool→ℕ) (atom:List Bool→List Bool) (z c:List Bool) (b:ℝ) (a:Fin (N c)→ℝ)
  (hD:D z=S.degree c)
noncomputable def Packet:Prop:=∀d s m r j,IntegralPolynomialWindowTarskiDecision.At atom (IntegralPolynomialWindowTarskiDecision.control z d s m) r j=
  InfinitesimalSign.encode (SignType.sign ((IntegralPolynomialWindowTarski.entryPolynomial S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m) r j).eval₂
    (Int.castRingHom ℝ) (IntegralPolynomialWindowTarski.values N c d s m b a)))

private theorem control_base (d s:ℕ) (m:Bool):IntegralPolynomialWindowTarskiDecision.base (IntegralPolynomialWindowTarskiDecision.control z d s m)=z:=by
  simp only [IntegralPolynomialWindowTarskiDecision.base,IntegralPolynomialWindowTarskiDecision.control,IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair]
include hD in
private theorem degree (d s:ℕ) (m:Bool):IntegralPolynomialWindowTarskiDecision.degree D (IntegralPolynomialWindowTarskiDecision.control z d s m)=IntegralPolynomialWindowTarski.degree S (IntegralPolynomialWindowTarski.intervalControl c d s m):=by
  rw [IntegralPolynomialWindowTarski.interval_control_degree]
  simp only [IntegralPolynomialWindowTarskiDecision.degree,IntegralPolynomialWindowTarskiDecision.dword,IntegralPolynomialWindowTarskiDecision.base,IntegralPolynomialWindowTarskiDecision.control,IntegralPolynomialWindowTarskiCatalogue.control,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,hD]
include hD in
private theorem seedDegree (d s:ℕ) (m:Bool):IntegralPolynomialWindowTarskiDecision.seedDegree D (IntegralPolynomialWindowTarskiDecision.control z d s m)=IntegralPolynomialWindowTarski.seedDegree S (IntegralPolynomialWindowTarski.intervalControl c d s m):=by
  rw [IntegralPolynomialWindowTarski.interval_control_seed]
  simp only [IntegralPolynomialWindowTarskiDecision.seedDegree,IntegralPolynomialWindowTarskiDecision.sword,IntegralPolynomialWindowTarskiDecision.base,IntegralPolynomialWindowTarskiDecision.control,IntegralPolynomialWindowTarskiCatalogue.control,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,hD]

variable (HA:Packet S N hd atom z c b a)
include HA in
private theorem at_zero (d s:ℕ) (m:Bool) (r j:ℕ):IntegralPolynomialWindowTarskiDecision.atZero atom (IntegralPolynomialWindowTarskiDecision.control z d s m) r j ↔
    (IntegralPolynomialWindowTarski.entryPolynomial S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m) r j).eval₂
      (Int.castRingHom ℝ) (IntegralPolynomialWindowTarski.values N c d s m b a)=0:=by
  rw [IntegralPolynomialWindowTarskiDecision.atZero,HA]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
private theorem zero (d s:ℕ) (m:Bool) (r j:ℕ):IntegralPolynomialWindowTarskiDecision.Zero atom r (pair (IntegralPolynomialWindowTarskiDecision.control z d s m) (BinaryNatCode.encode j)) ↔
    IntegralPolynomialWindowTarskiDecision.atZero atom (IntegralPolynomialWindowTarskiDecision.control z d s m) r j:=by
  simp only [IntegralPolynomialWindowTarskiDecision.Zero,IntegralPolynomialWindowTarskiDecision.atZero,IntegralPolynomialWindowTarskiDecision.At,IntegralPolynomialWindowTarskiDecision.query,pairFst_pair,pairSnd_pair]
include HA in
private theorem head_zero (d s:ℕ) (m:Bool) (j:ℕ):IntegralPolynomialWindowTarskiDecision.atZero atom (IntegralPolynomialWindowTarskiDecision.control z d s m) 1 j ↔
    (IntegralPolynomialWindowTarski.realHead S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m) (IntegralPolynomialWindowTarski.values N c d s m b a)).coeff j=0:=by
  rw [at_zero S N hd atom z c b a HA]
  simp only [IntegralPolynomialWindowTarski.entryPolynomial,one_ne_zero,ite_false,ite_true,IntegralPolynomialWindowTarski.head_value]
include HA in
private theorem seed_zero (d s:ℕ) (m:Bool) (j:ℕ):IntegralPolynomialWindowTarskiDecision.atZero atom (IntegralPolynomialWindowTarskiDecision.control z d s m) 2 j ↔
    (IntegralPolynomialWindowTarski.realSeed S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m) (IntegralPolynomialWindowTarski.values N c d s m b a)).coeff j=0:=by
  rw [at_zero S N hd atom z c b a HA]
  simp only [IntegralPolynomialWindowTarski.entryPolynomial,show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,ite_false,IntegralPolynomialWindowTarski.seed_value]

include hD HA in
theorem selected (d s:ℕ) (m:Bool):IntegralPolynomialWindowTarskiDecision.Selected D atom (IntegralPolynomialWindowTarskiDecision.control z d s m) ↔
    IntegralPolynomialWindowTarski.Selected S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m) (IntegralPolynomialWindowTarski.values N c d s m b a):=by
  have HD:=degree S D z c hD d s m
  have HS:=seedDegree S D z c hD d s m
  have HC:IntegralPolynomialWindowTarskiDecision.cap D (IntegralPolynomialWindowTarskiDecision.control z d s m)=IntegralPolynomialWindowTarski.inputBound S (IntegralPolynomialWindowTarski.intervalControl c d s m):=by
    simp only [IntegralPolynomialWindowTarskiDecision.cap,control_base,hD,IntegralPolynomialWindowTarski.inputBound,IntegralPolynomialWindowTarski.interval_control_original]
  unfold IntegralPolynomialWindowTarskiDecision.Selected IntegralPolynomialWindowTarskiDecision.HeadSelected IntegralPolynomialWindowTarskiDecision.SeedSelected IntegralPolynomialWindowTarskiDecision.Higher IntegralPolynomialWindowTarski.Selected IntegralPolynomialWindowTarski.HeadSelected IntegralPolynomialWindowTarski.SeedSelected
  simp only [HD,HS,HC]
  simp_rw [zero atom z,head_zero S N hd atom z c b a HA,seed_zero S N hd atom z c b a HA]
  have HI:IntegralPolynomialWindowTarski.inputBound S (IntegralPolynomialWindowTarski.intervalControl c d s m)=S.degree c:=by
    unfold IntegralPolynomialWindowTarski.inputBound;rw [IntegralPolynomialWindowTarski.interval_control_original]
  simp only [Nat.lt_succ_iff]
  apply and_congr
  · apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    exact ⟨fun H hi hcap=>H hcap hi,fun H hcap hi=>H hi hcap⟩
  · apply or_congr
    · rfl
    · apply and_congr_right
      intro _
      apply forall_congr'
      intro i
      exact ⟨fun H hi hcap=>H hcap hi,fun H hcap hi=>H hi hcap⟩

private theorem reverse_range (d:ℕ):(List.range (d+1)).reverse=(List.range (d+1)).map (fun i=>d-i):=by
  have H:=List.reverse_range' (s:=0) (n:=d+1)
  simpa only [Nat.zero_add,Nat.add_sub_cancel,←List.range_eq_range'] using H

include hD HA in
theorem statistic (d s:ℕ) (m:Bool):
    IntegralPolynomialWindowTarskiDecision.statistic D atom (IntegralPolynomialWindowTarskiDecision.control z d s m)=
    IntegralPolynomialWindowTarski.statistic S N hd (IntegralPolynomialWindowTarski.intervalControl c d s m)
      (IntegralPolynomialWindowTarski.values N c d s m b a):=by
  unfold IntegralPolynomialWindowTarskiDecision.statistic
  rw [CanonicalSignStatisticBits.value_at _ _ _
    (fun i=>(FixedWidthTarskiPrincipalBits.polynomial (IntegralPolynomialWindowTarski.family S N hd)
      (IntegralPolynomialWindowTarski.intervalControl c d s m)
      (IntegralPolynomialWindowTarski.degree S (IntegralPolynomialWindowTarski.intervalControl c d s m)-i)).eval₂
        (Int.castRingHom ℝ) (IntegralPolynomialWindowTarski.values N c d s m b a))]
  · rw [degree S D z c hD]
    unfold IntegralPolynomialWindowTarski.statistic
    rw [reverse_range,List.map_map]
    rfl
  · intro i _
    unfold IntegralPolynomialWindowTarskiDecision.statisticSigns
    simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [degree S D z c hD,HA]
    simp only [IntegralPolynomialWindowTarski.entryPolynomial,ite_true]

include hD HA in
theorem constant:IntegralPolynomialWindowTarskiDecision.Constant D atom z ↔
    IntegralPolynomialWindowTarski.ConstantSelected S N hd c a:=by
  unfold IntegralPolynomialWindowTarskiDecision.Constant IntegralPolynomialWindowTarskiDecision.Higher
  simp_rw [zero atom z,head_zero S N hd atom z c b a HA]
  simp only [IntegralPolynomialWindowTarski.canonical_head,hD,Nat.lt_succ_iff,
    IntegralPolynomialWindowTarski.ConstantSelected]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  exact ⟨fun H hi hcap=>H hcap hi,fun H hcap hi=>H hi hcap⟩

include hD HA in
theorem allZero:IntegralPolynomialWindowTarskiDecision.AllZero D atom z ↔
    IntegralPolynomialWindowTarski.Zero S N hd c a:=by
  unfold IntegralPolynomialWindowTarskiDecision.AllZero
  simp_rw [zero atom z,head_zero S N hd atom z c b a HA]
  simp only [IntegralPolynomialWindowTarski.canonical_head,hD,Nat.lt_succ_iff,
    IntegralPolynomialWindowTarski.Zero]

include hD HA in
theorem empty:IntegralPolynomialWindowTarskiDecision.Empty D atom z ↔
    IntegralPolynomialWindowTarski.Empty S N hd c b a:=by
  unfold IntegralPolynomialWindowTarskiDecision.Empty IntegralPolynomialWindowTarski.Empty
  rw [constant S N hd D atom z c b a hD HA]
  apply or_congr_right
  simp only [hD,IntegralPolynomialWindowTarskiCatalogue.limit]
  apply exists_congr
  intro d1
  apply and_congr_right
  intro _
  apply exists_congr
  intro s1
  apply and_congr_right
  intro _
  apply exists_congr
  intro d2
  apply and_congr_right
  intro _
  apply exists_congr
  intro s2
  apply and_congr_right
  intro _
  unfold IntegralPolynomialWindowTarskiDecision.Witness IntegralPolynomialWindowTarskiDecision.SumZero
  simp only [IntegralPolynomialWindowTarskiDecision.witnessControl,IntegralPolynomialWindowTarskiDecision.witnessBase,
    Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [selected S N hd D atom z c b a hD HA,selected S N hd D atom z c b a hD HA,
    statistic S N hd D atom z c b a hD HA,statistic S N hd D atom z c b a hD HA]

include hD HA in
theorem interval (HB:0<b):IntegralPolynomialWindowTarskiDecision.Empty D atom z ↔
    ∀r:ℝ,(IntegralPolynomialWindowTarski.baseHead S N hd c a).eval r=0 → r ∉ Ioo 0 b:=
  (empty S N hd D atom z c b a hD HA).trans (IntegralPolynomialWindowTarski.empty_iff S N hd c b a HB)
end LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecisionReadback
