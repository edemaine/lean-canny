/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowNatural
/-! # Native fresh-row queries identify the literal saved creating polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSemantics
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength keyAt instruction)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedFramedPhysicalRowTransport
open IntegralMixedFramedPhysicalFreshRowBits (base localIndex prepared smallCount largeCount polynomial)
open IntegralMixedFramedPhysicalIndex (arity criticalEquiv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family
  IntegralMixedFramedPhysicalBirthQueryBits.base IntegralMixedFramedPhysicalBirthQueryBits.packet
  IntegralMixedFramedPhysicalBlockBits.oldCount IntegralMixedFramedPhysicalBlockBits.fullCount
  IntegralMixedFramedPhysicalBlockBits.prepared IntegralMixedFramedPhysicalBlockBits.poweredRowPolynomial
  localRow rowBirth fullArity IntegralMixedFramedPhysicalIndex.prefixArity

variable (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
  (key : List Bool) (r : ℕ)
  (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
  (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) (M : List Bool)

include hT hr hs in
theorem prepared_saved :
    IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M))=
      keyAt (pairFst key) (rowBirth P T (pair key (BinaryNatCode.encode r))) (BinaryNatCode.encode 1) :=by
  have HB:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_below_cap P D J T hT key r hr hs
  unfold prepared IntegralMixedFramedPhysicalBlockBits.prepared
  rw [IntegralMixedFramedPhysicalBlockBits.sourceTask_saved]
  unfold IntegralMixedPhysicalTaskBits.saved
  rw [IntegralMixedFramedPhysicalBirthQueryBits.base_root,
    IntegralMixedFramedPhysicalBirthQueryBits.base_birth P D T _ (by simp only [pairFst_pair];omega),
    IntegralMixedFramedPhysicalBirthQueryBits.base_context P D J T hT key r hr hs M]
  simp only [pairFst_pair]

include hT hr hs in
theorem prepared_prefix :
    prefixLength P (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)))=
      rowBirth P T (pair key (BinaryNatCode.encode r)) :=by
  rw [prepared_saved P D J T hT key r hr hs M]
  apply IntegralMixedFramedHistoryFamilyBits.keyAt_prefix
  have HB:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_below_cap P D J T hT key r hr hs
  omega

include hT hr hs in
theorem prepared_root :
    pairFst (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)))=
      pairFst key :=by
  rw [prepared_saved P D J T hT key r hr hs M]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

include hT hr hs in
theorem prepared_critical :
    (instruction P D (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)))).command=
      .critical (IntegralMixedFramedPhysicalBits.rule P D
        (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)))) :=by
  have HC:=IntegralMixedFramedPhysicalBirthQueryBits.base_actual_context P D T (pair (pair key (BinaryNatCode.encode r)) M)
  have H1:=IntegralMixedFramedPhysicalBirthQueryBits.base_context P D J T hT key r hr hs M
  have HE : IntegralMixedVirtualTaskBits.saved P (base P D T (pair (pair key (BinaryNatCode.encode r)) M))=
      IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)) :=by
    unfold prepared IntegralMixedFramedPhysicalBlockBits.prepared
    rw [IntegralMixedFramedPhysicalBlockBits.sourceTask_saved]
    rfl
  rw [HE] at HC
  have HH:=IntegralMixedFramedPhysicalRowOrigin.command_of_context
    (instruction P D (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M)))).command
    ((IntegralMixedCommandHeaderBits.command_context _).trans (HC.symm.trans H1))
  obtain ⟨v,hv⟩:=HH
  rw [IntegralMixedFramedPhysicalBits.rule_critical P D _ v hv]
  exact hv


include hT hr hs in
theorem prepared_oldCount :
    IntegralMixedFramedPhysicalBlockBits.oldCount P D (prepared P D J T)
      (pair (pair key (BinaryNatCode.encode r)) M)=
      IntegralMixedFramedPhysicalIndex.prefixArity P T
        (pair key (List.replicate (rowBirth P T (pair key (BinaryNatCode.encode r))) true)) :=by
  unfold IntegralMixedFramedPhysicalBlockBits.oldCount IntegralMixedFramedFullScalarRowBits.fullCount
  change arity (commands P D (IntegralMixedPhysicalTaskBits.saved P
    (prepared P D J T (pair (pair key (BinaryNatCode.encode r)) M))))=_
  rw [count_view,prepared_root P D J T hT key r hr hs M,prepared_prefix P D J T hT key r hr hs M]
  exact (IntegralMixedFramedPhysicalIndex.prefixArity_packet P D J T hT key _).symm

theorem prepared_spatialCount :
    IntegralMixedFramedPhysicalBlockBits.spatialCount P D J (prepared P D J T)
      (pair (pair key (BinaryNatCode.encode r)) M)=P.ambient (pairFst key)+1 :=by
  unfold prepared
  rw [IntegralMixedFramedPhysicalBlockBits.prepared_spatialCount,
    IntegralMixedFramedPhysicalBlockBits.spatialCount_eq,
    IntegralMixedFramedPhysicalBirthQueryBits.base_root]
  simp only [pairFst_pair]

include hr hs in
theorem creator_span :
    IntegralMixedFramedPhysicalIndex.span P T (birthPacket P T (pair key (BinaryNatCode.encode r)))=
      (P.ambient (pairFst key)+1)+(P.ambient (pairFst key)+2)+1 :=by
  have HC:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_context P T key r hr hs
  simp only [IntegralMixedFramedPhysicalRowDegree.header,pairFst_pair] at HC
  simp only [IntegralMixedFramedPhysicalIndex.span,birthPacket,pairFst_pair,pairSnd_pair,
    List.length_replicate,HC,ite_true,IntegralMixedFramedPhysicalIndex.block]

include hT hr hs in
theorem smallCount_creating :
    smallCount P D J T (pair (pair key (BinaryNatCode.encode r)) M)=
      arity (commands P D (creatingAt P T key r (BinaryNatCode.encode 1))) :=by
  have HN:=hr.trans_eq (native_full_count P D J T hT key r)
  rw [creatingAt_count P D J T hT key r _ HN,prefix_succ]
  unfold smallCount IntegralMixedFramedPhysicalBlockBits.fullCount
  rw [prepared_oldCount P D J T hT key r hr hs M,prepared_spatialCount]
  have HS:=creator_span P T key r hr hs
  simpa only [birthPacket,pairFst_pair] using
    congrArg (fun n=>IntegralMixedFramedPhysicalIndex.prefixArity P T
      (pair key (List.replicate (rowBirth P T (pair key (BinaryNatCode.encode r))) true))+n) HS.symm

theorem largeCount_packet :
    largeCount P D (pair (pair key (BinaryNatCode.encode r)) M)=arity (commands P D key) :=by
  have HK : (pairFst∘pairFst) (pair (pair key (BinaryNatCode.encode r)) M)=key :=by
    simp only [Function.comp_apply,pairFst_pair]
  exact congrArg (fun k=>arity (commands P D k)) HK

include hT hr hs in
theorem count_le :
    smallCount P D J T (pair (pair key (BinaryNatCode.encode r)) M)≤
      largeCount P D (pair (pair key (BinaryNatCode.encode r)) M) :=by
  rw [smallCount_creating P D J T hT key r hr hs M]
  rw [largeCount_packet P D key r M]
  exact creatingAt_le P D J T hT key r (BinaryNatCode.encode 1) (hr.trans_eq (native_full_count P D J T hT key r))

include hT hr hs in
theorem localRow_index :
    IntegralMixedFramedPhysicalBlockBits.oldCount P D (prepared P D J T)
      (pair (pair key (BinaryNatCode.encode r)) M)+
        localIndex P T (pair (pair key (BinaryNatCode.encode r)) M)=r :=by
  obtain ⟨hb,hl,hu⟩:=rowBirth_interval P T key r hr
  rw [prepared_oldCount P D J T hT key r hr hs M]
  have HI : localIndex P T (pair (pair key (BinaryNatCode.encode r)) M)=
      localRow P T (pair key (BinaryNatCode.encode r)):=
    congrArg (localRow P T) (pairFst_pair _ _)
  rw [HI,localRow_packet P T key r _ hb hl hu]
  omega

include hr hs in
theorem localRow_lt :
    localIndex P T (pair (pair key (BinaryNatCode.encode r)) M)<
      IntegralMixedFramedPhysicalIndex.block (P.ambient (pairFst key)) :=by
  have HL:=localRow_lt_span P T key r hr
  rw [creator_span P T key r hr hs] at HL
  have HN : localRow P T (pair key (BinaryNatCode.encode r))+1≠
      (P.ambient (pairFst key)+1)+(P.ambient (pairFst key)+2)+1 :=by
    intro HH
    apply hs
    refine ⟨?_,?_⟩
    · simpa only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hr
    · rw [creator_span P T key r hr hs]
      exact HH
  have HI : localIndex P T (pair (pair key (BinaryNatCode.encode r)) M)=
      localRow P T (pair key (BinaryNatCode.encode r)):=
    congrArg (localRow P T) (pairFst_pair _ _)
  rw [HI]
  unfold IntegralMixedFramedPhysicalIndex.block
  omega


attribute [local semireducible] IntegralMixedFramedPhysicalBits.family

include hT hr hs in
theorem polynomial_creating :
    rename Fin.val (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))=
      keyRow P D (creatingAt P T key r (BinaryNatCode.encode 1)) r :=by
  let q:=pair (pair key (BinaryNatCode.encode r)) M
  let source:=IntegralMixedPhysicalTaskBits.saved P (prepared P D J T q)
  have HB:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_below_cap P D J T hT key r hr hs
  have HL : localIndex P T q<IntegralMixedFramedPhysicalIndex.block (P.ambient (pairFst source)) :=by
    have HE:=congrArg (fun root=>IntegralMixedFramedPhysicalIndex.block (P.ambient root))
      (prepared_root P D J T hT key r hr hs M)
    exact (localRow_lt P T key r hr hs M).trans_eq HE.symm
  let j : FlatAffineCriticalStage.Variables (P.ambient (pairFst source)+1):=
    criticalEquiv.symm ⟨localIndex P T q,HL⟩
  have HJ : localIndex P T q=(criticalEquiv j).val :=
    (congrArg Fin.val (criticalEquiv.apply_symm_apply ⟨localIndex P T q,HL⟩)).symm
  have HA:=IntegralMixedFramedPhysicalBirthQueryBits.base_active P D J T hT key r hr hs M
  have HP : polynomial P D J T hT q=IntegralMixedFramedPhysicalBlockBits.poweredExact P D J (prepared P D J T) q j :=
    IntegralMixedFramedPhysicalBlockBits.prepared_powered_exact P D J T hT (base P D T) (localIndex P T) q HA j HJ
  have HC:=IntegralMixedFramedPhysicalFreshRowNatural.powered_row P D J (prepared P D J T) q
    (BinaryNatCode.encode 1)
    (by rw [prepared_prefix P D J T hT key r hr hs M,prepared_root P D J T hT key r hr hs M];omega)
    (prepared_critical P D J T hT key r hr hs M) j
  have HK : keyAt (pairFst source) (prefixLength P source+1) (BinaryNatCode.encode 1)=
      creatingAt P T key r (BinaryNatCode.encode 1) :=by
    change keyAt (pairFst (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T q)))
      (prefixLength P (IntegralMixedPhysicalTaskBits.saved P (prepared P D J T q))+1) _=_
    rw [prepared_root P D J T hT key r hr hs M,prepared_prefix P D J T hT key r hr hs M]
    rfl
  have HI : arity (commands P D source)+(criticalEquiv j).val=r :=by
    have HO : IntegralMixedFramedPhysicalBlockBits.oldCount P D (prepared P D J T) q=
        arity (commands P D source) :=by
      unfold IntegralMixedFramedPhysicalBlockBits.oldCount IntegralMixedFramedFullScalarRowBits.fullCount
      rfl
    rw [←HO,←HJ]
    exact localRow_index P D J T hT key r hr hs M
  have HE:=(congrArg (rename Fin.val) HP).trans HC
  exact HE.trans (congrArg₂ (fun k i=>keyRow P D k i) HK HI)

include hT hr hs in
theorem polynomial_terminal :
    rename Fin.val (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))=keyRow P D key r :=by
  have HN:=hr.trans_eq (native_full_count P D J T hT key r)
  exact (polynomial_creating P D J T hT key r hr hs M).trans
    (key_rows P D (creatingAt P T key r (BinaryNatCode.encode 1)) key
      (creatingAt_root P T key r (BinaryNatCode.encode 1))
      (creatingAt_fits P D J T hT key r (BinaryNatCode.encode 1) HN) r
      (creatingAt_valid P D J T hT key r (BinaryNatCode.encode 1) HN)).symm

include hT hr hs in
theorem polynomial_indexed :
    rename (Fin.castLE ((count_le P D J T hT key r hr hs M).trans_eq (largeCount_packet P D key r M)))
      (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))=
      indexedRow P D J key ⟨r,hr.trans_eq (native_full_count P D J T hT key r)⟩ :=by
  apply (MvPolynomial.rename_injective (f:=Fin.val) Fin.val_injective)
  rw [rename_rename]
  change rename Fin.val (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))=_
  exact (polynomial_terminal P D J T hT key r hr hs M).trans
    (keyRow_family P D J key r (hr.trans_eq (native_full_count P D J T hT key r)))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSemantics
