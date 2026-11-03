/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalIntegerLeaves
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
public import LeanCanny.Encoding.IntegralMixedMarkedLeafPowers
/-! # Original marked and signed-outer leaf tables for full physical tests

All n+8 or n+10 original integer polynomials are preserved, including the
large power and signed cutoff leaves. The source and vertex stay fixed;
only the chronological leaf number is carried by the test datum.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalLeafSources
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegerPolynomialSourceChoice
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def query (z : List Bool) :=pair (pairFst (pairFst z)) (pairSnd z)
theorem query_FP : query∈FP :=mem_FP_pair
  (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
noncomputable def source (Q : IntegerPolynomialRootQueriesBits.Source) :=reindex Q query

theorem source_access (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    IntegerPolynomialRootQueriesBits.Access (source Q) :=reindex_access Q hQ query_FP

theorem source_packet (Q : IntegerPolynomialRootQueriesBits.Source) (ctx : List Bool) (i : ℕ) :
    (source Q).polynomial (pair (pair ctx []) (BinaryNatCode.encode i))=
      Q.polynomial (pair ctx (BinaryNatCode.encode i)) :=by
  simp only [source,reindex,Function.comp_apply,query,pairFst_pair,pairSnd_pair]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (R : List Bool→ℕ)
noncomputable def marked :=source (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
noncomputable def outer :=source (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R)
def markedCount (n : List Bool→ℕ) (c : List Bool) :=number n (pairFst c)+8
def outerCount (n : List Bool→ℕ) (c : List Bool) :=number n (pairFst c)+10

include hn in
theorem markedCount_unary : UnaryFn (markedCount n) :=
  ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp pairFst_mem_FP).add (UnaryFn.const 8)
include hn in
theorem outerCount_unary : UnaryFn (outerCount n) :=
  ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp pairFst_mem_FP).add (UnaryFn.const 10)

theorem marked_access (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (marked hn ht ha R) :=
  source_access _ (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
theorem outer_access (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (outer hn ht ha R) :=
  source_access _ (IntegralMixedAuxiliaryOuterIntegerSource.access hn ht ha hR)

theorem positive_power_root (E : ℕ) (v : ℝ) :
    (PowerIntegerPolynomial.polynomial False E).eval₂ (Int.castRingHom ℝ) v=0 ↔ v=(2:ℝ)^E :=by
  rw [PowerIntegerPolynomial.root_iff]
  simp only [PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]
theorem negative_power_root (E : ℕ) (v : ℝ) :
    (PowerIntegerPolynomial.polynomial True E).eval₂ (Int.castRingHom ℝ) v=0 ↔ v=-(2:ℝ)^E :=by
  rw [PowerIntegerPolynomial.root_iff]
  simp only [PowerIntegerPolynomial.value,ite_true,Int.cast_neg,Int.cast_pow,Int.cast_ofNat]

theorem radius (ctx : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number n ctx+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    v (number n ctx+4)=(2:ℝ)^(R ctx) :=by
  have E:=h (number n ctx+4) (by omega)
  rw [IntegralMixedMarkedLeafPowers.polynomial_radius] at E
  exact (positive_power_root _ _).mp E

theorem parameters (ctx : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number n ctx+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    v (number n ctx+5)=(2:ℝ)^(IntegralMixedAuxiliaryParametricSlackSource.regularizationAt n t
      (R∘IntegralMixedAuxiliaryMarkedIntegerSource.tail) (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey n t ctx)) ∧
    v (number n ctx+6)=(2:ℝ)^(IntegralMixedAuxiliaryMarkedIntegerSource.beta n t
      (R∘IntegralMixedAuxiliaryMarkedIntegerSource.tail) (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey n t ctx)) ∧
    v (number n ctx+7)=(2:ℝ)^(IntegralMixedAuxiliaryParametricSlackSource.penaltyAt n t
      (R∘IntegralMixedAuxiliaryMarkedIntegerSource.tail) (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey n t ctx)) :=by
  have E5:=h (number n ctx+5) (by omega)
  have E6:=h (number n ctx+6) (by omega)
  have E7:=h (number n ctx+7) (by omega)
  rw [IntegralMixedMarkedLeafPowers.polynomial_regularization] at E5
  rw [IntegralMixedMarkedLeafPowers.polynomial_perturbation] at E6
  rw [IntegralMixedMarkedLeafPowers.polynomial_penalty] at E7
  exact ⟨(positive_power_root _ _).mp E5,(positive_power_root _ _).mp E6,(positive_power_root _ _).mp E7⟩

theorem outer_marked_roots (ctx : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number n ctx+10,((IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    ∀i<number n ctx+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0 :=by
  intro i hi
  have E:=h i (by omega)
  rw [IntegralMixedAuxiliaryOuterIntegerSource.agree_before hn ht ha R _ (by
    simpa only [IntegralMixedAuxiliaryMarkedIntegerSource.tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hi)] at E
  exact E

theorem positive_cutoff (ctx : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number n ctx+10,((IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    v (number n ctx+8)=(2:ℝ)^(IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R ctx) :=by
  have E:=h (number n ctx+8) (by omega)
  rw [IntegralMixedAuxiliaryOuterIntegerSource.positive_polynomial hn ht ha R _ (by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])] at E
  simp only [pairFst_pair] at E
  exact (positive_power_root _ _).mp E

theorem negative_cutoff (ctx : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number n ctx+10,((IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R).polynomial
      (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    v (number n ctx+9)=-(2:ℝ)^(IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R ctx) :=by
  have E:=h (number n ctx+9) (by omega)
  rw [IntegralMixedAuxiliaryOuterIntegerSource.negative_polynomial hn ht ha R _ (by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])] at E
  simp only [pairFst_pair] at E
  exact (negative_power_root _ _).mp E
end LeanCanny.Encoding.IntegralFramedPhysicalLeafSources
