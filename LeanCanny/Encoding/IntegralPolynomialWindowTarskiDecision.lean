/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiIntervalSigns
public import LeanCanny.Algebra.CanonicalSignStatisticSpace
public import LeanCanny.Algebra.SignedIntegerArithmeticFP
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
/-! # Native finite window decisions from streamed signs

The atom reader receives one unchanged point context and finite window
controls. All degree tests and principal statistics are computed internally.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecision
open LeanCanny.Algebra LeanCanny.Computation Brackets
open scoped Classical
attribute [local instance 2000] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem flag_not (P:List Bool→Prop) (E:SpaceFunction (fun z=>[decide (P z)])):
    SpaceFunction (fun z=>[decide (¬P z)]):=by
  have H:=E.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact H.congr (funext fun z=>by simp only [Function.comp_apply,id_eq,List.cons.injEq,and_true,decide_eq_true_eq])
theorem flag_and (P Q:List Bool→Prop) (E:SpaceFunction (fun z=>[decide (P z)]))
    (F:SpaceFunction (fun z=>[decide (Q z)])):SpaceFunction (fun z=>[decide (P z∧Q z)]):=
  (E.andFlags F).congr (funext fun z=>by simp only [List.cons.injEq,and_true,decide_eq_true_eq])
theorem flag_or (P Q:List Bool→Prop) (E:SpaceFunction (fun z=>[decide (P z)]))
    (F:SpaceFunction (fun z=>[decide (Q z)])):SpaceFunction (fun z=>[decide (P z∨Q z)]):=by
  have H:=flag_not _ (flag_and _ _ (flag_not P E) (flag_not Q F))
  exact H.congr (funext fun z=>by rw [not_and_or,not_not,not_not])
theorem flag_all (P:List Bool→Prop) (B:List Bool→ℕ) (E:SpaceFunction (fun z=>[decide (P z)]))
    (hB:BinaryFn B):SpaceFunction (fun z=>[decide (∀i<B z,P (pair z (BinaryNatCode.encode i)))]):=
  (E.forall_binary hB).congr (funext fun z=>by simp only [List.cons.injEq,and_true,decide_eq_true_eq])
theorem flag_exists (P:List Bool→Prop) (B:List Bool→ℕ) (E:SpaceFunction (fun z=>[decide (P z)]))
    (hB:BinaryFn B):SpaceFunction (fun z=>[decide (∃i,i<B z∧P (pair z (BinaryNatCode.encode i)))]):=by
  have H:=flag_not _ (flag_all _ B (flag_not P E) hB)
  exact H.congr (funext fun z=>by simp only [not_forall,not_not,exists_prop])
theorem flag_imp (P Q:List Bool→Prop) (hP:FPPred P)
    (E:SpaceFunction (fun z=>[decide (Q z)])):SpaceFunction (fun z=>[decide (P z→Q z)]):=by
  have H:=SpaceFunction.branch (fun z=>decide (P z)) hP.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  exact H.congr (funext fun z=>by by_cases HP:P z <;>simp only [HP,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,true_implies,false_implies])

variable (D:List Bool→ℕ) (atom:List Bool→List Bool)
def base (q:List Bool):=pairFst q
def dword (q:List Bool):=pairFst (pairSnd q)
def sword (q:List Bool):=pairFst (pairSnd (pairSnd q))
noncomputable def degree (q:List Bool):=min (Nat.fromBitsLE (dword q)) (D (base q))+1
noncomputable def seedDegree (q:List Bool):=min (Nat.fromBitsLE (sword q)) (D (base q))
noncomputable def cap (q:List Bool):=D (base q)
def query (q:List Bool) (r j:ℕ):=pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j))
noncomputable def At (q:List Bool) (r j:ℕ):=atom (query q r j)
noncomputable def Zero (r:ℕ) (q:List Bool):Prop:=atom (pair (pairFst q) (pair (BinaryNatCode.encode r) (pairSnd q)))=InfinitesimalSign.encode 0
noncomputable def atZero (q:List Bool) (r j:ℕ):Prop:=At atom q r j=InfinitesimalSign.encode 0

private theorem binary_min {f g:List Bool→ℕ} (hf:BinaryFn f) (hg:BinaryFn g):BinaryFn (fun z=>min (f z) (g z)):=
  (BinaryFn.ite (hf.le hg) hf hg).of_eq (fun z=>by
    split_ifs with H
    · exact (Nat.min_eq_left H).symm
    · exact (Nat.min_eq_right (Nat.le_of_not_ge H)).symm)
theorem degree_binary (hD:BinaryFn D):BinaryFn (degree D):=
  (binary_min (BinaryFn.fromBits (show dword∈FP by polytime [dword])) (hD.comp pairFst_mem_FP)).add (BinaryFn.const 1)
theorem seedDegree_binary (hD:BinaryFn D):BinaryFn (seedDegree D):=
  binary_min (BinaryFn.fromBits (show sword∈FP by polytime [sword])) (hD.comp pairFst_mem_FP)
theorem cap_binary (hD:BinaryFn D):BinaryFn (cap D):=hD.comp pairFst_mem_FP

theorem zero_evaluator (E:SpaceFunction atom) (r:ℕ):SpaceFunction (fun z=>[decide (Zero atom r z)]):=
  (E.precompose (fun z=>pair (pairFst z) (pair (BinaryNatCode.encode r) (pairSnd z)))
    (mem_FP_pair pairFst_mem_FP (mem_FP_pair (constFn_mem_FP _) pairSnd_mem_FP))).postcompose _
      (stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).flag_mem_FP
private theorem chosen_evaluator (E:SpaceFunction atom) (r:ℕ) (j:List Bool→ℕ) (hj:BinaryFn j):
    SpaceFunction (fun q=>[decide (atZero atom q r (j q))]):=by
  have H:=(zero_evaluator atom E r).precompose (fun q=>pair q (BinaryNatCode.encode (j q))) (mem_FP_pair id_mem_FP hj.bits_mem_FP)
  exact H.congr (funext fun q=>by simp only [Function.comp_apply,Zero,atZero,At,query,pairFst_pair,pairSnd_pair])

noncomputable def Higher (r:ℕ) (cut count:List Bool→ℕ) (q:List Bool):Prop:=
  ∀j<count q,cut q<j→Zero atom r (pair q (BinaryNatCode.encode j))
theorem higher_evaluator (E:SpaceFunction atom) (r:ℕ) (cut count:List Bool→ℕ)
    (hcut:BinaryFn cut) (hcount:BinaryFn count):SpaceFunction (fun q=>[decide (Higher atom r cut count q)]):=by
  have H:=flag_imp (fun z=>cut (pairFst z)<Nat.fromBitsLE (pairSnd z)) (Zero atom r)
    ((show BinaryFn (fun z=>cut (pairFst z)) from hcut.comp pairFst_mem_FP).lt (BinaryFn.fromBits pairSnd_mem_FP)) (zero_evaluator atom E r)
  exact (flag_all _ count H hcount).congr (funext fun q=>by
    simp only [Higher,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])
noncomputable def HeadSelected (q:List Bool):Prop:=¬atZero atom q 1 (degree D q) ∧
  Higher atom 1 (degree D) (fun q=>cap D q+1) q
noncomputable def SeedSelected (q:List Bool):Prop:=
  (seedDegree D q=0 ∧∀j<degree D q,Zero atom 2 (pair q (BinaryNatCode.encode j))) ∨
  (¬atZero atom q 2 (seedDegree D q) ∧Higher atom 2 (seedDegree D) (degree D) q)
noncomputable def Selected (q:List Bool):Prop:=HeadSelected D atom q∧SeedSelected D atom q

theorem selected_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun q=>[decide (Selected D atom q)]):=by
  have HD:=degree_binary D hD
  have HS:=seedDegree_binary D hD
  have HH:=flag_and _ _ (flag_not _ (chosen_evaluator atom E 1 _ HD))
    (higher_evaluator atom E 1 _ _ HD ((cap_binary D hD).add (BinaryFn.const 1)))
  have HZ:=flag_and _ _ (SpaceFunction.ofFP _ (HS.eq (BinaryFn.const 0)).flag_mem_FP)
    (flag_all _ _ (zero_evaluator atom E 2) HD)
  have HNZ:=flag_and _ _ (flag_not _ (chosen_evaluator atom E 2 _ HS))
    (higher_evaluator atom E 2 _ _ HS HD)
  exact flag_and _ _ HH (flag_or _ _ HZ HNZ)

def statisticQuery (q:List Bool):=pair (pairFst q)
  (pair (BinaryNatCode.encode 0) (BinaryNatCode.encode (0)))
noncomputable def statisticSigns (q:List Bool):=At atom (pairFst q) 0 (degree D (pairFst q)-Nat.fromBitsLE (pairSnd q))
noncomputable def statistic (q:List Bool):ℤ:=CanonicalSignStatisticBits.value (statisticSigns D atom) (fun q=>degree D q+1) q

theorem statistic_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun q=>SignStatisticBits.integerCode (statistic D atom q)):=by
  have HP:BinaryFn (fun z=>degree D (pairFst z)):=(degree_binary D hD).comp pairFst_mem_FP
  have HI:=HP.sub (BinaryFn.fromBits pairSnd_mem_FP)
  have EQ:=mem_FP_pair pairFst_mem_FP (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 0)) HI.bits_mem_FP)
  exact CanonicalSignStatisticBits.evaluator (E.precompose _ EQ) _ ((degree_binary D hD).add (BinaryFn.const 1))

noncomputable def control:=IntegralPolynomialWindowTarskiCatalogue.control
noncomputable def Constant (z:List Bool):Prop:=¬atZero atom (control z 0 0 false) 1 0 ∧
  Higher atom 1 (fun _=>0) (fun _=>D z+1) (control z 0 0 false)
noncomputable def AllZero (z:List Bool):Prop:=∀j<D z+1,Zero atom 1 (pair (control z 0 0 false) (BinaryNatCode.encode j))

theorem control_FP (d s:ℕ) (m:Bool):(fun z=>control z d s m)∈FP:=by
  unfold control IntegralPolynomialWindowTarskiCatalogue.control
  exact mem_FP_pair id_mem_FP (constFn_mem_FP _)
private theorem control_base (z:List Bool) (d s:ℕ) (m:Bool):base (control z d s m)=z:=by
  simp only [base,control,IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair]
theorem constant_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun z=>[decide (Constant D atom z)]):=by
  have HC:=
    control_FP 0 0 false
  have H0:=(flag_not _ (chosen_evaluator atom E 1 _ (BinaryFn.const 0))).precompose _ HC
  have HH:=(higher_evaluator atom E 1 (fun _=>0) (fun q=>cap D q+1)
    (BinaryFn.const 0) ((cap_binary D hD).add (BinaryFn.const 1))).precompose _ HC
  have H:=flag_and _ _ H0 HH
  exact H.congr (funext fun z=>by simp only [Constant,Higher,cap,control_base])
theorem allZero_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun z=>[decide (AllZero D atom z)]):=by
  have EQ:=(zero_evaluator atom E 1).precompose
    (fun q=>pair (control (pairFst q) 0 0 false) (pairSnd q))
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP (control_FP 0 0 false)) pairSnd_mem_FP)
  exact (flag_all _ _ EQ (hD.add (BinaryFn.const 1))).congr (funext fun z=>by
    simp only [AllZero,pairFst_pair,pairSnd_pair])

def witnessBase (q:List Bool):=pairFst (pairFst (pairFst (pairFst q)))
noncomputable def witnessControl (m:Bool) (q:List Bool):=control (witnessBase q)
  (Nat.fromBitsLE (if m then pairSnd (pairFst q) else pairSnd (pairFst (pairFst (pairFst q)))))
  (Nat.fromBitsLE (if m then pairSnd q else pairSnd (pairFst (pairFst q)))) m
theorem witnessControl_FP (m:Bool):witnessControl m∈FP:=by
  unfold witnessControl control IntegralPolynomialWindowTarskiCatalogue.control
  apply mem_FP_pair (show witnessBase∈FP by polytime [witnessBase])
  cases m <;>simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact mem_FP_pair (BinaryFn.fromBits (by polytime)).bits_mem_FP
      (mem_FP_pair (BinaryFn.fromBits (by polytime)).bits_mem_FP (constFn_mem_FP []))
  · exact mem_FP_pair (BinaryFn.fromBits (by polytime)).bits_mem_FP
      (mem_FP_pair (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP (constFn_mem_FP [true]))
noncomputable def SumZero (q:List Bool):Prop:=
  statistic D atom (witnessControl true q)+statistic D atom (witnessControl false q)=0
noncomputable def Witness (q:List Bool):Prop:=Selected D atom (witnessControl false q) ∧
  Selected D atom (witnessControl true q) ∧SumZero D atom q

def negateCode (q:List Bool):=pair (pairSnd q) (pairFst q)
private theorem negateCode_packet (z:ℤ):negateCode (SignStatisticBits.integerCode z)=SignStatisticBits.integerCode (-z):=by
  simp only [negateCode,SignStatisticBits.integerCode,pairFst_pair,pairSnd_pair,neg_neg]
private theorem integerCode_inj (x y:ℤ):SignStatisticBits.integerCode x=SignStatisticBits.integerCode y ↔x=y:=by
  constructor
  · intro H
    exact (SignedIntegerArithmetic.value_packet x).symm.trans
      ((congrArg SignedIntegerArithmetic.value H).trans (SignedIntegerArithmetic.value_packet y))
  · exact congrArg SignStatisticBits.integerCode

theorem sumZero_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun q=>[decide (SumZero D atom q)]):=by
  have ES:=statistic_evaluator D atom hD E
  have E1:=(ES.precompose _ (witnessControl_FP true))
  have E2:=(ES.precompose _ (witnessControl_FP false)).postcompose negateCode
    (mem_FP_pair pairSnd_mem_FP pairFst_mem_FP)
  have EH:=(E1.pairOutputs E2).postcompose _ (stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  exact EH.congr (funext fun q=>by
    simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,negateCode_packet]
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,integerCode_inj,SumZero]
    exact eq_neg_iff_add_eq_zero)

theorem witness_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun q=>[decide (Witness D atom q)]):=
  flag_and _ _ ((selected_evaluator D atom hD E).precompose _ (witnessControl_FP false))
    (flag_and _ _ ((selected_evaluator D atom hD E).precompose _ (witnessControl_FP true)) (sumZero_evaluator D atom hD E))

noncomputable def Empty (z:List Bool):Prop:=Constant D atom z ∨
  ∃d1,d1<D z+2 ∧∃s1,s1<D z+2 ∧∃d2,d2<D z+2 ∧∃s2,s2<D z+2 ∧
    Witness D atom (pair (pair (pair (pair z (BinaryNatCode.encode d1)) (BinaryNatCode.encode s1))
      (BinaryNatCode.encode d2)) (BinaryNatCode.encode s2))
theorem empty_evaluator (hD:BinaryFn D) (E:SpaceFunction atom):
    SpaceFunction (fun z=>[decide (Empty D atom z)]):=by
  have H3:BinaryFn (fun z=>D (pairFst (pairFst (pairFst z)))+2):=
    (show BinaryFn (fun z=>D (pairFst (pairFst (pairFst z)))) from hD.comp (show (fun z=>pairFst (pairFst (pairFst z)))∈FP by polytime)).add (BinaryFn.const 2)
  have H2:BinaryFn (fun z=>D (pairFst (pairFst z))+2):=
    (show BinaryFn (fun z=>D (pairFst (pairFst z))) from hD.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (BinaryFn.const 2)
  have H1:BinaryFn (fun z=>D (pairFst z)+2):=(show BinaryFn (fun z=>D (pairFst z)) from hD.comp pairFst_mem_FP).add (BinaryFn.const 2)
  have E3:=flag_exists _ _ (witness_evaluator D atom hD E) H3
  have E2:=flag_exists _ _ E3 H2
  have E1:=flag_exists _ _ E2 H1
  have E0:=flag_exists _ _ E1 (hD.add (BinaryFn.const 2))
  have EW:SpaceFunction (fun z=>[decide (∃d1,d1<D z+2 ∧∃s1,s1<D z+2 ∧∃d2,d2<D z+2 ∧∃s2,s2<D z+2 ∧
    Witness D atom (pair (pair (pair (pair z (BinaryNatCode.encode d1)) (BinaryNatCode.encode s1))
      (BinaryNatCode.encode d2)) (BinaryNatCode.encode s2)))]) :=
    E0.congr (funext fun z=>by simp only [pairFst_pair])
  exact flag_or _ _ (constant_evaluator D atom hD E) EW
end LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecision
