/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGrid
/-! # One bounded Gram table and its own component-hitting grid word

The selected heads share one encoded table and one sampled tuple. The
source equation is retained at that tuple; no second source is resampled.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGridWords
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CoerciveBoxGramEliminant.polynomial

def tableWord {n : ℕ} (tau witness : Fin n → ℕ) : List Bool :=
  WordList.encode (List.ofFn fun i => pair (BinaryNatCode.encode (tau i)) (BinaryNatCode.encode (witness i)))

theorem table_row {n : ℕ} (tau witness : Fin n → ℕ) (i : Fin n) :
    WordList.get (tableWord tau witness) i.val=
      pair (BinaryNatCode.encode (tau i)) (BinaryNatCode.encode (witness i)) := by
  simp [tableWord,WordList.get_encode]

theorem slice_packet {n : ℕ} (u : List Bool) (tau witness : Fin n → ℕ) (i : Fin n) :
    ImplicitSourceGramGrid.slice (pair u (tableWord tau witness)) i.val=tau i := by
  rw [ImplicitSourceGramGrid.slice,ImplicitSourceGramGrid.table,pairSnd_pair,table_row,pairFst_pair]
  exact Nat.fromBitsLE_bits _

theorem witness_packet {n : ℕ} (u : List Bool) (tau witness : Fin n → ℕ) (i : Fin n) :
    ImplicitSourceGramGrid.witness (pair u (tableWord tau witness)) i.val=witness i := by
  rw [ImplicitSourceGramGrid.witness,ImplicitSourceGramGrid.table,pairSnd_pair,table_row,pairSnd_pair]
  exact Nat.fromBitsLE_bits _

theorem table_length {n : ℕ} (tau witness : Fin n → ℕ) (L : ℕ)
    (hb : ∀ i, tau i≤L ∧ witness i≤L) :
    (tableWord tau witness).length≤(6*(L+1).size+6)*n := by
  have HT (i : Fin n) : (BinaryNatCode.encode (tau i)).length≤(L+1).size := by
    rw [BinaryNatCode.length_encode]
    exact Nat.size_le_size ((hb i).1.trans (Nat.le_succ _))
  have HW (i : Fin n) : (BinaryNatCode.encode (witness i)).length≤(L+1).size := by
    rw [BinaryNatCode.length_encode]
    exact Nat.size_le_size ((hb i).2.trans (Nat.le_succ _))
  have HL := WordList.length_le
    (List.ofFn fun i : Fin n => pair (BinaryNatCode.encode (tau i)) (BinaryNatCode.encode (witness i)))
    (3*(L+1).size+2) (by
      intro v hv
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      rw [pair_length]
      have := HT i
      have := HW i
      omega)
  have HE : 2*(3*(L+1).size+2)+2=6*(L+1).size+6 := by omega
  simpa only [tableWord,List.length_ofFn,HE] using HL

/-- Eliminate the header equality before forming any dependent root tuple. -/
theorem at_context (S : Source) (hp : ∀ u, 0<S.arity u) (u c : List Bool)
    (hc : ImplicitSourceGramGrid.header c=u) (tau witness : Fin (S.arity u) → ℕ)
    (ht : ∀ i, ImplicitSourceGramGrid.slice c i.val=tau i)
    (hr : ∀ i, ImplicitSourceGramGrid.witness c i.val=witness i)
    (a : Zeros ((S.polynomial u).map (Int.castRingHom ℝ)))
    (ha : ∀ i, (CoerciveGramWitnessGrid.polynomial (S.polynomial u) (S.degree u) tau witness i).eval₂
      (Int.castRingHom ℝ) (a.val i)=0) :
    ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w),
      w.length=SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) c ∧
        HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val a.val := by
  cases hc
  have HT : (fun i : Fin (S.arity (ImplicitSourceGramGrid.header c)) =>
      ImplicitSourceGramGrid.slice c i.val)=tau := funext ht
  have HR : (fun i : Fin (S.arity (ImplicitSourceGramGrid.header c)) =>
      ImplicitSourceGramGrid.witness c i.val)=witness := funext hr
  have hz (i : Fin (S.arity (ImplicitSourceGramGrid.header c))) :
      (ImplicitSourceGramGrid.polynomial S c i).eval₂ (Int.castRingHom ℝ) (a.val i)=0 := by
    change (CoerciveGramWitnessGrid.polynomial (S.polynomial (ImplicitSourceGramGrid.header c))
      (S.degree (ImplicitSourceGramGrid.header c)) _ _ i).eval₂ (Int.castRingHom ℝ) (a.val i)=0
    rw [HT,HR]
    exact ha i
  let z : SquareSampleComplete.Roots (ImplicitSourceGramGrid.input S hp) c :=
    ⟨a.val,fun i => (DiagonalUnivariateSystem.eval (ImplicitSourceGramGrid.polynomial S c i) i
      (Int.castRingHom ℝ) a.val).trans (hz i)⟩
  let w := SquareSampleCompleteVertices.word (ImplicitSourceGramGrid.input S hp)
    (ImplicitSourceGramGrid.complete S hp) c z
  have hw := SquareSampleCompleteVertices.word_valid (ImplicitSourceGramGrid.input S hp)
    (ImplicitSourceGramGrid.complete S hp) c z
  refine ⟨w,hw,(Classical.choose hw).1,?_⟩
  exact heq_of_eq (congrArg Subtype.val (SquareSampleCompleteVertices.candidate_word
    (ImplicitSourceGramGrid.input S hp) (ImplicitSourceGramGrid.complete S hp) c z))

/-- Every original component has a point on one bounded witnessed grid,
named by that grid's own exact-width word. -/
theorem exists_word (S : Source) (hp : ∀ u, 0<S.arity u) (u : List Bool)
    (x : Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) :
    ∃ Gamma : List Bool,
      Gamma.length≤(6*(ImplicitSourceCoerciveBoxGram.degreeBound S u+1).size+6)*S.arity u ∧
      (∀ i : Fin (S.arity u),
        ImplicitSourceGramGrid.slice (pair u Gamma) i.val≤ImplicitSourceCoerciveBoxGram.degreeBound S u ∧
        ImplicitSourceGramGrid.witness (pair u Gamma) i.val≤ImplicitSourceCoerciveBoxGram.degreeBound S u) ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid
          (ImplicitSourceGramGrid.input S hp) (pair u Gamma) w),
        w.length=SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) (pair u Gamma) ∧
        ∃ a : Zeros ((S.polynomial u).map (Int.castRingHom ℝ)),
          JoinedIn (Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) x.val a.val ∧
            HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp)
              (pair u Gamma) w hw).val a.val := by
  obtain ⟨tau,witness,hb,a,HJ,ha⟩ := CoerciveGramWitnessGrid.joined_sample
    (S.polynomial u) (S.degree u) (S.polynomial_degree u) x
  obtain ⟨w,hw,hlen,hpoint⟩ := at_context S hp u (pair u (tableWord tau witness))
    (pairFst_pair _ _) tau witness (slice_packet u tau witness) (witness_packet u tau witness) a ha
  refine ⟨tableWord tau witness,table_length tau witness _ hb,?_,w,hw,hlen,a,HJ,hpoint⟩
  intro i
  rw [slice_packet,witness_packet]
  exact hb i

end LeanCanny.Encoding.ImplicitSourceGramGridWords
