/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutHead
public import LeanCanny.Algebra.IntegralCoordinatePullSpace
public import LeanCanny.Algebra.IntegralMixedCoefficientQuery
/-! # Native full relative cut heads from original CurrentQ arithmetic

A coefficient query changes only the coefficient field. The saved parent,
its context, and the arbitrary caller modulus are preserved. No sign,
algebraic-coefficient or matrix evaluator is an input to this factory.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

def query (parent : List Bool→List Bool) (k : List Bool→ℕ) (c : List Bool) :=
  IntegralMixedCoefficientQueryBits.writer P .rawFactor .originalCoefficient
    (pair (parent c) (pair (BinaryNatCode.encode (k c)) (pair [] [])))

theorem query_FP (a : Access P) (parent : List Bool→List Bool) (hp : parent∈FP)
    (k : List Bool→ℕ) (hk : BinaryFn k) : query P parent k∈FP :=
  mem_FP_comp (mem_FP_pair hp (mem_FP_pair hk.bits_mem_FP (constFn_mem_FP (pair [] []))))
    (IntegralMixedCoefficientQueryBits.writer_FP P a .rawFactor .originalCoefficient)

theorem query_saved (parent : List Bool→List Bool) (k : List Bool→ℕ) (c : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P parent k c)=saved P parent c :=by
  simp only [query,IntegralMixedCoefficientQueryBits.writer_saved,pairFst_pair,saved]

theorem query_active (parent : List Bool→List Bool) (k : List Bool→ℕ) (c : List Bool) :
    IntegralMixedFramedFullCutProbeBits.Active P (query P parent k c)↔IntegralMixedFramedFullCutProbeBits.Active P (parent c) :=by
  simp only [query,IntegralMixedFramedFullCutProbeBits.Active,IntegralMixedVirtualCaps.valid,
    IntegralMixedCoefficientQueryBits.writer_birth,IntegralMixedCoefficientQueryBits.writer_root,
    IntegralMixedVirtualContextBits.context,IntegralMixedCoefficientQueryBits.writer_get,pairFst_pair,
    reduceCtorEq,ite_false]

theorem query_coefficient (parent : List Bool→List Bool) (k : List Bool→ℕ) (c : List Bool) :
    get P .coefficient (query P parent k c)=min (k c) (numericCap P (RankedHistoryTask.root (parent c))) :=by
  simp only [query,IntegralMixedCoefficientQueryBits.writer_get,reduceCtorEq,ite_false,ite_true,
    IntegralPowerProductBits.factorWord,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

private theorem powered_at (q old : List Bool) (k S : ℕ)
    (hkey : IntegralMixedVirtualTaskBits.saved P q=old) (hk : get P .coefficient q=k)
    (hS : S=P.cap (pairFst old)+1) :
    HEq ((IntegralMixedFramedCutProbeSourceBits.source P D H).poweredPolynomial (fun _=>S) q)
      (if IntegralMixedFramedFullCutProbeBits.Active P q then coefficientAt P D H old k else 0) :=by
  subst old
  subst k
  subst S
  unfold IntegralCoordinateCoefficientBits.Family.poweredPolynomial IntegralCoordinateCoefficientBits.Family.polynomial
  by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P q
  · simp only [IntegralMixedFramedCutProbeSourceBits.source,ite_eq_left ha]
    rfl
  · simp only [IntegralMixedFramedCutProbeSourceBits.source,ite_eq_right ha,
      IntegralCoordinateBasis.representative_zero]
    apply heq_of_eq
    exact map_zero _

private theorem value_congr {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (h : a=b) (hp : HEq p q) (V : ℕ) (r mw : List Bool) :
    residueBits (((p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V (Nat.fromBitsLE r))) : ℤ) : ZMod (Nat.fromBitsLE mw+1))=
      residueBits (((q.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V (Nat.fromBitsLE r))) : ℤ) : ZMod (Nat.fromBitsLE mw+1)) :=by
  cases h
  cases hp
  rfl

theorem degree_binary (a : Access P) (parent : List Bool→List Bool) (hp : parent∈FP)
    (d : List Bool→ℕ) (hd : BinaryFn d) : BinaryFn (degree P parent d) :=by
  have HC:=(numericCap_binary P a).comp (mem_FP_comp hp RankedHistoryTask.root_FP)
  exact (BinaryFn.ite (hd.le HC) hd HC).of_eq (fun c=>by simp only [degree,Nat.min_def,Function.comp_apply])

private theorem pull_powered (Q : IntegralCoordinateCoefficientBits.Family)
    (f : List Bool→List Bool) (S : List Bool→ℕ) (c : List Bool) :
    (Q.pull f).poweredPolynomial S c=Q.poweredPolynomial (fun _=>S c) (f c) :=rfl

attribute [local irreducible] coefficientAt head IntegralCoordinateCoefficientBits.Family.poweredPolynomial

theorem coefficient_evaluator (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d k V : List Bool→ℕ)
    (hd : BinaryFn d) (hk : BinaryFn k) (hV : UnaryFn V)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D H parent) V
      (fun c=>(head P D H parent d c).coeff (k c)) target modulus) :=by
  let f:=query P parent k
  have hq : f∈FP:=query_FP P a parent hp k hk
  let S:=fun c=>P.cap (pairFst (saved P parent c))+1
  have hS : UnaryFn S:=((a.cap.comp (mem_FP_comp (mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP P a)) pairFst_mem_FP)).add (UnaryFn.const 1))
  have E:=IntegralCoordinateCoefficientBits.pulled_powered_evaluator (IntegralMixedFramedCutProbeSourceBits.source P D H)
    f hq S V target modulus (IntegralMixedFramedCutProbePacketBits.value P D H) hS
    (IntegralMixedFramedCutProbeSourceBits.arity_unary P a D H) (IntegralMixedFramedCutProbeSourceBits.width_unary P a D H)
    hV ht hm (IntegralMixedFramedCutProbePacketBits.evaluator P a D H L F C hL hF hC h hb)
    (IntegralMixedFramedCutProbePacketBits.packet P D H)
  have HG:=hk.le (degree_binary P a parent hp d hd)
  have EB:=SpaceFunction.branch (fun c=>decide (k c≤degree P parent d c)) HG.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply EB.congr
  funext c
  simp only [FixedWidthRowBits.value,decide_eq_true_eq]
  by_cases hf : k c≤degree P parent d c
  · rw [ite_eq_left hf,head_coefficient]
    have HK : k c≤numericCap P (RankedHistoryTask.root (parent c)):=hf.trans (min_le_right _ _)
    have Hk : get P .coefficient (f c)=k c:=(query_coefficient P parent k c).trans (min_eq_left HK)
    have HP:=powered_at P D H (f c) (saved P parent c) (k c) (S c) (query_saved P parent k c) Hk rfl
    have HPP:= (heq_of_eq (pull_powered (IntegralMixedFramedCutProbeSourceBits.source P D H) f S c)).trans HP
    have HA : (IntegralMixedFramedCutProbeSourceBits.source P D H).arity (f c)=arity P D H parent c:=
      congrArg (fun key=>(family P D H).birth key) (query_saved P parent k c)
    by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P (parent c)
    · have hqa : IntegralMixedFramedFullCutProbeBits.Active P (f c):=(query_active P parent k c).mpr ha
      rw [ite_eq_left hqa] at HPP
      rw [ite_eq_left ⟨ha,hf⟩]
      exact value_congr (((IntegralMixedFramedCutProbeSourceBits.source P D H).pull f).poweredPolynomial S c)
        (coefficientAt P D H (saved P parent c) (k c)) HA HPP (V c) (target c) (modulus c)
    · have hqa : ¬IntegralMixedFramedFullCutProbeBits.Active P (f c):=fun Hq=>ha ((query_active P parent k c).mp Hq)
      rw [ite_eq_right hqa] at HPP
      rw [ite_eq_right (fun Hq=>ha Hq.1)]
      exact value_congr (((IntegralMixedFramedCutProbeSourceBits.source P D H).pull f).poweredPolynomial S c)
        (0 : MvPolynomial (Fin (arity P D H parent c)) ℤ) HA HPP (V c) (target c) (modulus c)
  · rw [ite_eq_right hf,head_coefficient,ite_eq_right (fun Hq=>hf Hq.2)]
    change []=residueBits ((0:ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))
    rw [Int.cast_zero]
    rfl

end LeanCanny.Algebra.IntegralMixedFramedFullCutHead
