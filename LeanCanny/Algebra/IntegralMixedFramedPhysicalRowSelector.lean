/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn

/-! # Native creating blocks for full physical rows

Oldest-first physical indices retain their column through every later birth.
A row request keeps its full saved key and a binary physical index. Original
header prefix arities identify the unique birth block and its local row.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowSelector
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (prefixLength)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedPhysicalIndex (span prefixArity)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem span_pos (P : Parameters) (T : Tables) (q : List Bool) : 0<span P T q := by
  unfold span
  split_ifs <;> omega

theorem prefix_succ (P : Parameters) (T : Tables) (key : List Bool) (b : ℕ) :
    prefixArity P T (pair key (List.replicate (b+1) true))=
      prefixArity P T (pair key (List.replicate b true))+
        span P T (pair key (List.replicate b true)) := by
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate,Finset.sum_range_succ]

theorem prefix_strictMono (P : Parameters) (T : Tables) (key : List Bool) :
    StrictMono (fun b=>prefixArity P T (pair key (List.replicate b true))) := by
  apply strictMono_nat_of_lt_succ
  intro b
  rw [prefix_succ]
  exact Nat.lt_add_of_pos_right (span_pos P T _)

def endPacket (q : List Bool) := pair (pairFst (pairFst q)) (List.replicate ((pairSnd q).length+1) true)
theorem endPacket_FP : endPacket∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  ((UnaryFn.length pairSnd_mem_FP).add (UnaryFn.const 1)).mem_FP

def rowBirth (P : Parameters) (T : Tables) (q : List Bool) :=
  ((Finset.range (prefixLength P (pairFst q))).filter fun b=>
    prefixArity P T (pair (pairFst q) (List.replicate (b+1) true))≤Nat.fromBitsLE (pairSnd q)).card

theorem rowBirth_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (rowBirth P T) := by
  have HE:=((IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T h).comp endPacket_FP)
  have HR:=BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have HC:=UnaryFn.count ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP)
    ((BinaryFn.ofUnary HE).le HR)
  exact HC.of_eq (fun q=>by
    simp only [rowBirth,endPacket,Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate])

def birthPacket (P : Parameters) (T : Tables) (q : List Bool) :=
  pair (pairFst q) (List.replicate (rowBirth P T q) true)
theorem birthPacket_FP (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    birthPacket P T∈FP := mem_FP_pair pairFst_mem_FP (rowBirth_unary P a T h).mem_FP

def fullArity (P : Parameters) (T : Tables) (q : List Bool) :=
  prefixArity P T (pair (pairFst q) (List.replicate (prefixLength P (pairFst q)) true))
theorem fullArity_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (fullArity P T) :=
  (IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T h).comp
    (mem_FP_pair pairFst_mem_FP ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP).mem_FP)

def localRow (P : Parameters) (T : Tables) (q : List Bool) :=
  min (Nat.fromBitsLE (pairSnd q)) (fullArity P T q)-prefixArity P T (birthPacket P T q)
theorem localRow_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (localRow P T) :=
  (UnaryFn.fromBitsLE_min pairSnd_mem_FP (fullArity_unary P a T h)).sub
    ((IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T h).comp (birthPacket_FP P a T h))

def previousKey (P : Parameters) (T : Tables) (q : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (pairFst q)) (rowBirth P T q)
    (pairSnd (pairSnd (pairFst q)))
def creatingKey (P : Parameters) (T : Tables) (q : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (pairFst q)) (rowBirth P T q+1)
    (pairSnd (pairSnd (pairFst q)))
theorem previousKey_FP (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    previousKey P T∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
      (mem_FP_pair (BinaryFn.ofUnary (rowBirth_unary P a T h)).bits_mem_FP
        (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP))
theorem creatingKey_FP (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    creatingKey P T∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
      (mem_FP_pair (BinaryFn.ofUnary ((rowBirth_unary P a T h).add (UnaryFn.const 1))).bits_mem_FP
        (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP))

theorem rowBirth_packet (P : Parameters) (T : Tables) (key : List Bool) (r b : ℕ)
    (hb : b<prefixLength P key)
    (hl : prefixArity P T (pair key (List.replicate b true))≤r)
    (hu : r<prefixArity P T (pair key (List.replicate (b+1) true))) :
    rowBirth P T (pair key (BinaryNatCode.encode r))=b := by
  have HM:=(prefix_strictMono P T key).monotone
  have HE : (Finset.range (prefixLength P key)).filter
      (fun j=>prefixArity P T (pair key (List.replicate (j+1) true))≤r)=Finset.range b := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨_,hj⟩
      by_contra H
      have HH:=HM (Nat.succ_le_succ (Nat.le_of_not_gt H))
      change prefixArity P T (pair key (List.replicate (b+1) true))≤
        prefixArity P T (pair key (List.replicate (j+1) true)) at HH
      omega
    · intro hj
      exact ⟨hj.trans hb,(HM (by omega : j+1≤b)).trans hl⟩
  simp only [rowBirth,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HE,Finset.card_range]

theorem localRow_packet (P : Parameters) (T : Tables) (key : List Bool) (r b : ℕ)
    (hb : b<prefixLength P key)
    (hl : prefixArity P T (pair key (List.replicate b true))≤r)
    (hu : r<prefixArity P T (pair key (List.replicate (b+1) true))) :
    localRow P T (pair key (BinaryNatCode.encode r))=
      r-prefixArity P T (pair key (List.replicate b true)) := by
  have HM:=(prefix_strictMono P T key).monotone
  have HR : r≤fullArity P T (pair key (BinaryNatCode.encode r)) := by
    exact hu.le.trans (by
      simpa only [fullArity,pairFst_pair] using HM (by omega : b+1≤prefixLength P key))
  have HC : Nat.fromBitsLE (pairSnd (pair key (BinaryNatCode.encode r)))≤
      fullArity P T (pair key (BinaryNatCode.encode r)) := by
    simpa only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HR
  unfold localRow birthPacket
  rw [rowBirth_packet P T key r b hb hl hu,min_eq_left HC]
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem exists_interval (P : Parameters) (T : Tables) (key : List Bool) (r m : ℕ)
    (hr : r<prefixArity P T (pair key (List.replicate m true))) :
    ∃b<m,prefixArity P T (pair key (List.replicate b true))≤r ∧
      r<prefixArity P T (pair key (List.replicate (b+1) true)) := by
  induction m with
  | zero=>simp only [prefixArity,pairSnd_pair,List.length_replicate,Finset.range_zero,
      Finset.sum_empty,Nat.not_lt_zero] at hr
  | succ m ih=>
    by_cases H : r<prefixArity P T (pair key (List.replicate m true))
    · obtain ⟨b,hb,hl,hu⟩:=ih H
      exact ⟨b,Nat.lt_succ_of_lt hb,hl,hu⟩
    · exact ⟨m,Nat.lt_succ_self m,Nat.le_of_not_gt H,hr⟩

theorem rowBirth_interval (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r))) :
    let b:=rowBirth P T (pair key (BinaryNatCode.encode r))
    b<prefixLength P key ∧ prefixArity P T (pair key (List.replicate b true))≤r ∧
      r<prefixArity P T (pair key (List.replicate (b+1) true)) := by
  have HR : r<prefixArity P T (pair key (List.replicate (prefixLength P key) true)) := by
    simpa only [fullArity,pairFst_pair] using hr
  obtain ⟨b,hb,hl,hu⟩:=exists_interval P T key r (prefixLength P key) HR
  have HB:=rowBirth_packet P T key r b hb hl hu
  dsimp only
  rw [HB]
  exact ⟨hb,hl,hu⟩

theorem localRow_lt_span (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r))) :
    localRow P T (pair key (BinaryNatCode.encode r))<
      span P T (birthPacket P T (pair key (BinaryNatCode.encode r))) := by
  obtain ⟨hb,hl,hu⟩:=rowBirth_interval P T key r hr
  rw [localRow_packet P T key r _ hb hl hu]
  rw [prefix_succ] at hu
  simp only [birthPacket,pairFst_pair]
  omega

theorem previousKey_packet (P : Parameters) (T : Tables) (key : List Bool) (r b : ℕ)
    (hb : b<prefixLength P key)
    (hl : prefixArity P T (pair key (List.replicate b true))≤r)
    (hu : r<prefixArity P T (pair key (List.replicate (b+1) true))) :
    previousKey P T (pair key (BinaryNatCode.encode r))=
      IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key) b (pairSnd (pairSnd key)) := by
  unfold previousKey
  rw [rowBirth_packet P T key r b hb hl hu,pairFst_pair]

theorem creatingKey_packet (P : Parameters) (T : Tables) (key : List Bool) (r b : ℕ)
    (hb : b<prefixLength P key)
    (hl : prefixArity P T (pair key (List.replicate b true))≤r)
    (hu : r<prefixArity P T (pair key (List.replicate (b+1) true))) :
    creatingKey P T (pair key (BinaryNatCode.encode r))=
      IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key) (b+1) (pairSnd (pairSnd key)) := by
  unfold creatingKey
  rw [rowBirth_packet P T key r b hb hl hu,pairFst_pair]

def IsScalar (P : Parameters) (T : Tables) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd q)<fullArity P T q ∧
    localRow P T q+1=span P T (birthPacket P T q)

theorem isScalar_fppred (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    FPPred (IsScalar P T) :=
  ((BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.ofUnary (fullArity_unary P a T h))).and
    (FPPred.eq ((localRow_unary P a T h).add (UnaryFn.const 1))
      ((IntegralMixedFramedPhysicalIndex.span_unary P a T h).comp (birthPacket_FP P a T h)))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowSelector
