/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegree
public import LeanCanny.Computation.PolyTimeBinaryRange
/-! # Native full-square metadata from original header tables

Every row degree is bound to the actual full sampler. A bounded binary sum
computes the advertised degree. The only remaining cost boundary is the
literal full row coefficient reader, which the physical-row backend supplies.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands prefixLength)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)

include a ht hr in
theorem count_unary (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (fun c=>count P D (key c)) := by
  have HP:UnaryFn (fun c=>prefixLength P (key c)) :=(IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk
  have HB:=((IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T ht).comp (mem_FP_pair hk HP.mem_FP))
  exact HB.of_eq (fun c=>IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T hr (key c) _)

include hr in
theorem rowDegree_eq_native (key : List Bool) (j : ℕ) : rowDegree P D H key j=
    IntegralMixedFramedPhysicalRowDegree.degree P T (pair key (BinaryNatCode.encode j)) := by
  by_cases hj : j<count P D key
  · rw [rowDegree,dite_eq_left hj]
    exact (IntegralMixedFramedPhysicalDegree.degree_eq P D H T hr key ⟨j,hj⟩).symm
  · rw [rowDegree,dite_eq_right hj]
    have HA : IntegralMixedFramedPhysicalRowSelector.fullArity P T (pair key (BinaryNatCode.encode j))=count P D key := by
      simp only [IntegralMixedFramedPhysicalRowSelector.fullArity,pairFst_pair]
      exact IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T hr key _
    unfold IntegralMixedFramedPhysicalRowDegree.degree
    rw [HA]
    simp only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,ite_eq_right hj]

include a ht hr in
theorem rowDegree_binary (key : List Bool→List Bool) (hk : key∈FP) :
    BinaryFn (fun q=>rowDegree P D H (key (pairFst q)) (Nat.fromBitsLE (pairSnd q))) := by
  have HN : BinaryFn (fun q=>IntegralMixedFramedPhysicalRowDegree.degree P T
      (pair (key (pairFst q)) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))))) :=(IntegralMixedFramedPhysicalRowDegree.degree_binary P a T ht).comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP)
  exact HN.of_eq (fun q=>by
    simpa only [pairFst_pair,pairSnd_pair] using (rowDegree_eq_native P D H T hr (key (pairFst q)) (Nat.fromBitsLE (pairSnd q))).symm)

include a ht hr in
theorem degree_binary (key : List Bool→List Bool) (hk : key∈FP) : BinaryFn (fun c=>degree P D H (key c)) := by
  have HN:BinaryFn (fun z=>IntegralMixedFramedPhysicalRowDegree.degree P T
      (pair (key (pairFst z)) (BinaryNatCode.encode (pairSnd z).length))) :=
    (IntegralMixedFramedPhysicalRowDegree.degree_binary P a T ht).comp
      (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP)
  have HS:=BinaryFn.sum (count_unary P a D H T ht hr key hk) HN
  exact (HS.add (BinaryFn.const 1)).of_eq (fun c=>by
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
    rw [Finset.sum_range]
    unfold degree
    apply congrArg (fun v : ℕ=>v+1)
    exact Finset.sum_congr rfl (fun i _=>
      (rowDegree_eq_native P D H T hr (key c) i.val).symm.trans (rowDegree_at P D H (key c) i)))

include a ht hr in
theorem finite_access (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀c,0<(family P D H).birth (key c))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input P D H L F C hs key hpos))) :
    NoInfinitySquareSample.Access (finite P D H L F C hs key hpos) where
  count:=count_unary P a D H T ht hr key hk
  degree:=degree_binary P a D H T ht hr key hk
  mass:=(IntegralMixedPhysicalRowBudget.familyMass_binary P a hL hF hC).comp (mem_FP_comp hk pairFst_mem_FP)
  rowDegree:=rowDegree_binary P a D H T ht hr key hk
  row:=ER

include a ht hr in
theorem access (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀c,0<(family P D H).birth (key c))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input P D H L F C hs key hpos))) :
    (input P D H L F C hs key hpos).Access :=
  NoInfinitySquareSample.access (finite_access P a D H T ht hr L F C hs hL hF hC key hk hpos ER)
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
