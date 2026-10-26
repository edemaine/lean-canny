/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionCoefficient
public import LeanCanny.Encoding.BoundedCriticalLabels
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native counting of the distinct real projection roots

The concrete projection polynomial may contain extraneous roots. The count
includes those roots, as do the ordered labels. Its coefficient-mass bound and
all modular coefficient queries come from the actual selected source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRootCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalProjection.polynomial

theorem polynomial_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedCriticalProjection.polynomial (P.comp f) c = BoundedCriticalProjection.polynomial P (f c) := by
  exact (BoundedProjectionMacaulay.lowest_eq (P.comp f) c).symm.trans
    ((congrArg (fun A : Matrix (Fin (BoundedProjectionMacaulay.dimension P (f c)))
      (Fin (BoundedProjectionMacaulay.dimension P (f c))) (Polynomial ℤ) =>
        CharacteristicLowestBounds.lowest A) (BoundedProjectionMacaulay.matrix_comp P f c)).trans
          (BoundedProjectionMacaulay.lowest_eq P (f c)))

theorem rootSet_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedCriticalLabels.rootSet (P.comp f) c = BoundedCriticalLabels.rootSet P (f c) := by
  simp only [BoundedCriticalLabels.rootSet, polynomial_comp]

noncomputable def degree (P : Readers) (c : List Bool) : ℕ :=
  2 ^ BoundedCriticalProjection.labelWidth P c

noncomputable def massExponent (P : Readers) (c : List Bool) : ℕ :=
  BoundedCriticalProjection.coefficientBits P c + (degree P c + 1).size

theorem degree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degree P) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp
    (BoundedCriticalProjection.labelWidth_unary h)

theorem massExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (massExponent P) :=
  (BoundedCriticalProjection.coefficientBits_binary h).add (((degree_binary h).add (BinaryFn.const 1)).size)

theorem mass_bound (P : Readers) (c : List Bool) :
    coefficientMass (BoundedCriticalProjection.polynomial P c) ≤ 2 ^ massExponent P c := by
  apply coefficientMass_le_pow_of_degree_coeff _ (degree P c) (BoundedCriticalProjection.coefficientBits P c)
    (BoundedCriticalProjection.polynomial_degree P c)
  intro k
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (BoundedCriticalProjection.polynomial_coefficient_bits P c k))

/-- Move the modulus before the coefficient index for the projection reader. -/
def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def coefficient (P : Readers) : List Bool → List Bool :=
  BoundedProjectionCoefficient.value P ∘ coefficientQuery

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P) :=
  (BoundedProjectionCoefficient.evaluator h ha).precompose coefficientQuery coefficientQuery_FP

theorem coefficient_packet (P : Readers) (c : List Bool) (k m : ℕ) (hm : 0 < m) :
    coefficient P (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((BoundedCriticalProjection.polynomial P c).coeff k) m := by
  unfold coefficient
  simp only [Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair]
  generalize hw : BinaryNatCode.encode (m - 1) = w
  have hmod : Nat.fromBitsLE w + 1 = m := by rw [← hw]; simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  subst m
  exact BoundedProjectionCoefficient.value_packet P c w k

noncomputable def family (P : Readers) : SignPatternBits.Family where
  root := BoundedCriticalProjection.polynomial P
  polynomial _ _ := 0
  pattern _ _ := 0
  count _ := []
  rootDegree c := BinaryNatCode.encode (degree P c)
  degree _ := []
  rootMass c := BinaryNatCode.encode (massExponent P c)
  mass _ := []
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact pow_pos (by decide) _
  root_degree c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact BoundedCriticalProjection.polynomial_degree P c
  root_mass c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact mass_bound P c
  polynomial_degree _ i hi := by change i < 0 at hi; omega
  polynomial_mass _ i hi := by change i < 0 at hi; omega

theorem family_polyTime {P : Readers} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (family P) := by
  refine ⟨constFn_mem_FP [], ?_, (degree_binary h).bits_mem_FP,
    constFn_mem_FP [], (massExponent_binary h).bits_mem_FP, constFn_mem_FP []⟩
  exact UnaryFn.const 0

noncomputable def access (P : Readers) : SignPatternBits.Access (family P) where
  rootCoefficient := coefficient P
  polynomialCoefficient _ := []
  pattern _ := []
  root_eq := coefficient_packet P
  polynomial_eq _ i hi := by change i < 0 at hi; omega
  pattern_eq _ _ := rfl

noncomputable def count (P : Readers) (c : List Bool) : ℕ := (BoundedCriticalLabels.rootSet P c).card

theorem family_count (P : Readers) (c : List Bool) : SignPatternBits.rootCount (family P) c = count P c := by
  simp [SignPatternBits.rootCount, family, RootSignQueries.signCount, count, BoundedCriticalLabels.rootSet]

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (count P c)) := by
  have E := SignPatternBits.rootCountEvaluator (access P) (family_polyTime h)
    (constFn_mem_FP []) (coefficient_evaluator h ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (family_count P c))

theorem rank_lt_count (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalLabels.rank P c x < count P c :=
  (((BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl).symm (BoundedCriticalLabels.projectedRoot P c x)).isLt

private theorem ordered_rank_eq_card {α : Type*} [LinearOrder α] (s : Finset α) (x : {a // a ∈ s}) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun a => a < x.val)).card := by
  let e := (s.orderIsoOfFin rfl).symm
  rw [← Finset.card_range (e x).val]
  symm
  apply Finset.card_bij (fun y hy => (e ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
  · intro y hy
    rw [Finset.mem_range]
    exact e.lt_iff_lt.mpr (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact congrArg Subtype.val (e.injective (Fin.ext hab))
  · intro n hn
    have hn' : n < (e x).val := Finset.mem_range.mp hn
    let j : Fin s.card := ⟨n, hn'.trans (e x).isLt⟩
    refine ⟨(e.symm j).val, Finset.mem_filter.mpr ⟨(e.symm j).property, ?_⟩, ?_⟩
    · change e.symm j < x
      have h := e.symm.strictMono (show j < e x from hn')
      rw [e.symm_apply_apply] at h
      exact h
    · simp only [e.apply_symm_apply]
      rfl

/-- A label rank counts precisely the projection roots strictly below its sample. -/
theorem rank_eq_card_below (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalLabels.rank P c x =
      ((BoundedCriticalLabels.rootSet P c).filter (fun t => t <
        BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val)).card :=
  ordered_rank_eq_card (BoundedCriticalLabels.rootSet P c) (BoundedCriticalLabels.projectedRoot P c x)

end LeanCanny.Encoding.BoundedProjectionRootCount
