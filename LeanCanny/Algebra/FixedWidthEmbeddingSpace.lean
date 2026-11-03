/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthPermutationSpace
public import LeanCanny.Algebra.EmbeddedCoefficient
/-! # Native fixed-width coefficients under an explicit injective embedding

A native column reader selects the old variables. Queries with a nonzero
exponent outside that image vanish; all remaining exponents are repacked.
This permits scalar slots interspersed among retained physical variables.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthEmbeddingBits
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial MatrixPower RationalSubstitution.Indexed
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (A N W : List Bool→ℕ) (target index : List Bool→List Bool)

def read (p : List Bool) := FixedWidthQuery.read N W target (pair (pairFst p) (index p))
def coordinate (c : List Bool) (i : ℕ) :=
  FixedWidthQuery.entry N W target c (Nat.fromBitsLE (index (pair c (BinaryNatCode.encode i))))
def word (c : List Bool) := FixedWidthNatVector.encode (A c) (W c) (coordinate N W target index c)

theorem read_FP (hN : UnaryFn N) (hW : UnaryFn W) (ht : target∈FP) (hi : index∈FP) : read N W target index∈FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP hi) (FixedWidthQuery.read_mem_FP hN hW ht)

theorem read_packet (c : List Bool) (i : ℕ) : read N W target index (pair c (BinaryNatCode.encode i))=
    BinaryNatCode.encode (coordinate N W target index c i) := by
  have H:=FixedWidthQuery.read_packet N W target c (Nat.fromBitsLE (index (pair c (BinaryNatCode.encode i))))
  simp only [read,coordinate,FixedWidthQuery.read,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at H ⊢
  exact H

theorem word_FP (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (ht : target∈FP) (hi : index∈FP) : word A N W target index∈FP :=
  FixedWidthNatVector.encode_mem_FP A W _ hA hW _ (read_FP N W target index hN hW ht hi) (read_packet N W target index)

def Member (q : List Bool) := ∃i<A (pairFst q),Nat.fromBitsLE (index (pair (pairFst q) (BinaryNatCode.encode i)))=Nat.fromBitsLE (pairSnd q)

theorem member_FP (hA : UnaryFn A) (hi : index∈FP) : FPPred (Member A index) := by
  let loop:=fun p=>pair (pairFst (pairFst p)) (BinaryNatCode.encode (pairSnd p).length)
  have HL:loop∈FP:=mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (bits_mem_FP UnaryFn.index)
  have HE: FPPred (fun p=>Nat.fromBitsLE (index (loop p))=Nat.fromBitsLE (pairSnd (pairFst p))) :=
    BinaryNat.eq_fppred (mem_FP_comp HL hi) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  exact (HE.exists_lt (hA.comp pairFst_mem_FP)).of_iff (fun q=>by
    simp only [Member,loop,pairFst_pair,pairSnd_pair,List.length_replicate])

def Guard (c : List Bool) := ∀j<N c,FixedWidthQuery.entry N W target c j=0 ∨ Member A index (pair c (BinaryNatCode.encode j))

private theorem targetRead_bits (c : List Bool) (i : ℕ) :
    Nat.fromBitsLE (FixedWidthQuery.read N W target (pair c i.bits))=FixedWidthQuery.entry N W target c i := by
  change Nat.fromBitsLE (FixedWidthQuery.read N W target (pair c (BinaryNatCode.encode i)))=_
  rw [FixedWidthQuery.read_packet,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem guard_FP (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (ht : target∈FP) (hi : index∈FP) : FPPred (Guard A N W target index) := by
  let packet:=fun p=>pair (pairFst p) (BinaryNatCode.encode (pairSnd p).length)
  have HP:packet∈FP:=mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)
  have HZ: FPPred (fun p=>Nat.fromBitsLE (FixedWidthQuery.read N W target (packet p))=0) :=
    BinaryNat.eq_const_fppred (mem_FP_comp HP (FixedWidthQuery.read_mem_FP hN hW ht)) 0
  have HM: FPPred (fun p=>Member A index (packet p)) := (member_FP A index hA hi).comp HP
  exact ((HZ.or HM).forall_lt hN).of_iff (fun c=>by
    simp only [Guard,packet,pairFst_pair,pairSnd_pair,List.length_replicate]
    constructor
    · intro h j hj
      rcases h j hj with hz|hm
      · exact Or.inl ((targetRead_bits N W target c j).symm.trans hz)
      · exact Or.inr hm
    · intro h j hj
      rcases h j hj with hz|hm
      · exact Or.inl ((targetRead_bits N W target c j).trans hz)
      · exact Or.inr hm)

theorem word_coordinate (c : List Bool) (i : ℕ) (hi : i<A c) :
    FixedWidthQuery.coordinate W (word A N W target index) c i=coordinate N W target index c i := by
  apply FixedWidthNatVector.decode_block _ _ _ i hi
  unfold coordinate FixedWidthQuery.entry FixedWidthQuery.coordinate
  split_ifs
  · exact (Nat.fromBitsLE_lt_pow_length _).trans_le (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  · exact Nat.two_pow_pos _

theorem support_guard (c : List Bool) (f : Fin (A c)→Fin (N c))
    (hindex : ∀i,index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f i).val) :
    (↑(exponentVector (N c) (FixedWidthQuery.coordinate W target c)).support : Set (Fin (N c)))⊆Set.range f ↔
      Guard A N W target index c := by
  constructor
  · intro h j hj
    by_cases hz : FixedWidthQuery.entry N W target c j=0
    · exact Or.inl hz
    · apply Or.inr
      have HE: (exponentVector (N c) (FixedWidthQuery.coordinate W target c)) ⟨j,hj⟩≠0 := by
        simpa only [exponentVector,Finsupp.coe_equivFunOnFinite_symm,FixedWidthQuery.entry,ite_eq_left hj] using hz
      obtain ⟨i,he⟩:=h (Finsupp.mem_support_iff.mpr HE)
      simp only [Member,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
      refine ⟨i.val,i.isLt,?_⟩
      have HI : index (pair c i.val.bits)=(f i).val.bits := by
        simpa only [BinaryNatCode.encode] using hindex i
      rw [HI,Nat.fromBitsLE_bits]
      exact congrArg Fin.val he
  · intro h j hj
    have HJ:=h j.val j.isLt
    have HE : FixedWidthQuery.entry N W target c j.val≠0 := by
      simpa only [exponentVector,Finsupp.coe_equivFunOnFinite_symm,FixedWidthQuery.entry,ite_eq_left j.isLt] using Finsupp.mem_support_iff.mp hj
    have HM:=HJ.resolve_left HE
    simp only [Member,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HM
    obtain ⟨i,hi,he⟩:=HM
    refine ⟨⟨i,hi⟩,Fin.ext ?_⟩
    have HI : index (pair c i.bits)=(f ⟨i,hi⟩).val.bits := by
      simpa only [BinaryNatCode.encode] using hindex ⟨i,hi⟩
    rwa [HI,Nat.fromBitsLE_bits] at he

theorem exponent_word (c : List Bool) (f : Fin (A c)→Fin (N c)) (hf : Function.Injective f)
    (hindex : ∀i,index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f i).val) :
    exponentVector (A c) (FixedWidthQuery.coordinate W (word A N W target index) c)=
      (exponentVector (N c) (FixedWidthQuery.coordinate W target c)).comapDomain f hf.injOn := by
  ext i
  simp only [exponentVector,Finsupp.coe_equivFunOnFinite_symm,Finsupp.comapDomain_apply]
  rw [word_coordinate A N W target index c i.val i.isLt]
  unfold coordinate
  rw [hindex i]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,FixedWidthQuery.entry,ite_eq_left (f i).isLt]

theorem coefficient (c : List Bool) (f : Fin (A c)→Fin (N c)) (hf : Function.Injective f)
    (hindex : ∀i,index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f i).val)
    (p : MvPolynomial (Fin (A c)) ℤ) :
    (rename f p).coeff (exponentVector (N c) (FixedWidthQuery.coordinate W target c))=
      if Guard A N W target index c then p.coeff
        (exponentVector (A c) (FixedWidthQuery.coordinate W (word A N W target index) c)) else 0 := by
  rw [EmbeddedCoefficient.coeff_rename f hf]
  simp only [EmbeddedCoefficient.value,support_guard A N W target index c f hindex,←exponent_word A N W target index c f hf hindex]

private theorem queryExponent (N W : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :
    FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (N c))) (W c) (Nat.fromBitsLE (target c))=
      exponentVector (N c) (FixedWidthQuery.coordinate W target c) := by
  ext i
  exact FixedWidthBlockRenameBits.entry_bits _ _ _

theorem evaluator (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (f : (c : List Bool)→Fin (A c)→Fin (N c)) (hf : ∀c,Function.Injective (f c))
    (hindex : ∀c i,index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f c i).val)
    (modulus : List Bool→List Bool) (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W)
    (ht : target∈FP) (hi : index∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p (word A N W target index) modulus)) :
    SpaceFunction (FixedWidthRowBits.value N W (fun c=>rename (f c) (p c)) target modulus) := by
  have H:=SpaceFunction.branch (fun c=>decide (Guard A N W target index c))
    (guard_FP A N W target index hA hN hW ht hi).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c=>?_)
  simp only [FixedWidthRowBits.value,queryExponent]
  rw [coefficient A N W target index c (f c) (hf c) (hindex c) (p c)]
  by_cases hc : Guard A N W target index c
  · simp only [hc,decide_eq_true_eq,ite_true]
  · simp only [hc,decide_eq_true_eq,ite_false,Int.cast_zero,MatrixPower.residueBits,ZMod.val_zero,BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.FixedWidthEmbeddingBits
