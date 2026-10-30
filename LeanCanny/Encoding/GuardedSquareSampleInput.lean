/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.FixedWidthRowArithmetic
public import LeanCanny.Computation.SpaceFunctionSpaceBranch
public import LeanCanny.Computation.PSPACEClosure

/-! # Total native all-root sampling under a checked source promise

Prepared degree records need only satisfy their algebraic properties after
validation. Outside the checked language, a diagonal identity system supplies
a total native sampler. Numeric controls are enlarged uniformly, so no
polynomial-time promise decider is assumed. Valid records retain every root,
including singular roots, and can use the complete native vertex interface.
-/

@[expose] public section
namespace LeanCanny.Encoding.GuardedSquareSampleInput
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

structure Data where
  count : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  system : (u : List Bool) → Fin (count u) → MvPolynomial (Fin (count u)) ℤ
  annihilator : (u : List Bool) → Fin (count u) → Polynomial ℤ
  annDegree : List Bool → ℕ
  annHeight : List Bool → ℕ
  good : Language
  count_pos : ∀ u, 0 < count u
  system_degree : ∀ u, u ∈ good → ∀ i, (system u i).totalDegree ≤ degree u
  system_mass : ∀ u, u ∈ good → ∀ i, MvMass.mass (system u i) ≤ 2 ^ mass u
  ann_nonzero : ∀ u, u ∈ good → ∀ i, annihilator u i ≠ 0
  ann_degree : ∀ u, u ∈ good → ∀ i, (annihilator u i).natDegree ≤ annDegree u
  ann_height : ∀ u, u ∈ good → ∀ i j, ((annihilator u i).coeff j).natAbs.size ≤ annHeight u
  ann_root : ∀ u, u ∈ good → ∀ (z : Fin (count u) → ℝ),
    (∀ i, (system u i).eval₂ (Int.castRingHom ℝ) z = 0) →
    ∀ i, (annihilator u i).eval₂ (Int.castRingHom ℝ) (z i) = 0

noncomputable def input (F : Data) : SquareSampleInput.Inputs where
  count := F.count
  degree u := F.degree u + 1
  mass u := F.mass u + 1
  system u i := if u ∈ F.good then F.system u i else MvPolynomial.X i
  count_pos := F.count_pos
  degree_pos _ := Nat.zero_lt_succ _
  system_degree u i := by
    split_ifs with hu
    · exact (F.system_degree u hu i).trans (Nat.le_succ _)
    · simp only [MvPolynomial.totalDegree_X]
      omega
  system_mass u i := by
    split_ifs with hu
    · exact (F.system_mass u hu i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    · simpa only [MvMass.X] using Nat.one_le_pow (F.mass u + 1) 2 (by decide)
  annihilator u i := if u ∈ F.good then F.annihilator u i else Polynomial.X
  annDegree u := F.annDegree u + 1
  annHeight u := F.annHeight u + 1
  ann_nonzero u i := by
    split_ifs with hu
    · exact F.ann_nonzero u hu i
    · exact Polynomial.X_ne_zero
  ann_degree u i := by
    split_ifs with hu
    · exact (F.ann_degree u hu i).trans (Nat.le_succ _)
    · simp only [Polynomial.natDegree_X]
      omega
  ann_height u i j := by
    split_ifs with hu
    · exact (F.ann_height u hu i j).trans (Nat.le_succ _)
    · by_cases hj : j = 1
      · simp [Polynomial.coeff_X, hj]
      · simp [Polynomial.coeff_X, Ne.symm hj]
  ann_root u z hz _ i := by
    by_cases hu : u ∈ F.good
    · simp only [hu, ite_true] at hz ⊢
      exact F.ann_root u hu z hz i
    · simpa only [hu, ite_false, Polynomial.eval₂_X, MvPolynomial.eval₂_X] using hz i

theorem complete (F : Data) : SquareSampleComplete.Complete (input F) := by
  intro u z hz i
  by_cases hu : u ∈ F.good
  · change (if u ∈ F.good then F.annihilator u i else Polynomial.X).eval₂ _ (z i) = 0
    rw [ite_eq_left hu]
    apply F.ann_root u hu z ?_ i
    simpa only [input, hu, ite_true] using hz
  · simpa only [input, hu, ite_false, Polynomial.eval₂_X, MvPolynomial.eval₂_X] using hz i

def selected (F : Data) (u i : List Bool) : Fin (F.count u) :=
  ⟨min (Nat.fromBitsLE i) (F.count u - 1), by have := F.count_pos u; omega⟩

noncomputable def rowCoefficient (F : Data) (q : List Bool) : List Bool :=
  residueBits (((F.system (SquareSampleInput.source q)
    (selected F (SquareSampleInput.source q) (SquareSampleInput.indexWord q))).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (SquareSampleInput.widthWord q).length
      (Nat.fromBitsLE (SquareSampleInput.rankWord q)))) : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1))

noncomputable def annCoefficient (F : Data) (q : List Bool) : List Bool :=
  residueBits (((F.annihilator (SquareSampleInput.source q)
    (selected F (SquareSampleInput.source q) (SquareSampleInput.indexWord q))).coeff
      (Nat.fromBitsLE (SquareSampleInput.rankWord q))) : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1))

structure Data.Access (F : Data) : Prop where
  count : UnaryFn F.count
  degree : BinaryFn F.degree
  mass : BinaryFn F.mass
  annDegree : BinaryFn F.annDegree
  annHeight : BinaryFn F.annHeight
  good : SpaceDecider F.good
  row : SpaceFunction (rowCoefficient F)
  annihilator : SpaceFunction (annCoefficient F)

noncomputable def rowAt (F : Data) (q : List Bool) : Fin (F.count (SquareSampleInput.source q)) :=
  selected F (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem rowAt_unary {F : Data} (h : F.Access) : UnaryFn (fun q => (rowAt F q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    ((h.count.comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

theorem identityRowEvaluator {F : Data} (h : F.Access) : SpaceFunction
    (FixedWidthRowBits.value (F.count ∘ SquareSampleInput.source)
      (fun q => (SquareSampleInput.widthWord q).length) (fun q => MvPolynomial.X (rowAt F q))
      SquareSampleInput.rankWord SquareSampleInput.modulusWord) :=
  FixedWidthRowBits.variable_evaluator _ _ _ _ _ (h.count.comp SquareSampleInput.source_FP)
    (UnaryFn.length SquareSampleInput.widthWord_FP) (rowAt_unary h) SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP

theorem rowEvaluator {F : Data} (h : F.Access) : SpaceFunction (SquareSampleInput.rowCoefficient (input F)) := by
  have E := SpaceFunction.branchDecider (h.good.precompose SquareSampleInput.source SquareSampleInput.source_FP)
    h.row (identityRowEvaluator h)
  refine E.congr (funext fun q => ?_)
  change (if SquareSampleInput.source q ∈ F.good then rowCoefficient F q else _) = _
  by_cases hu : SquareSampleInput.source q ∈ F.good <;>
    simp only [hu, ite_true, ite_false, rowCoefficient, FixedWidthRowBits.value,
      SquareSampleInput.rowCoefficient, SquareSampleInput.rowValue, input, rowAt, selected, SquareSampleInput.selected]; rfl

theorem identityAnnEvaluator : SpaceFunction (fun q => residueBits
    (((Polynomial.X : Polynomial ℤ).coeff (Nat.fromBitsLE (SquareSampleInput.rankWord q))) :
      ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1))) := by
  have hk := (BinaryFn.fromBits SquareSampleInput.rankWord_FP).eq (BinaryFn.const 1)
  have hm := mem_FP_comp SquareSampleInput.modulusWord_FP BinaryNat.succ_mem_FP
  have E := SpaceFunction.branch _ hk.flag_mem_FP
    (SpaceFunction.ofFP _ (mem_FP_comp hm ArithmeticBits.one_mem_FP)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  change (if decide (Nat.fromBitsLE (SquareSampleInput.rankWord q) = 1) then
    ArithmeticBits.one (BinaryNat.succ (SquareSampleInput.modulusWord q)) else []) = _
  by_cases hk : Nat.fromBitsLE (SquareSampleInput.rankWord q) = 1
  · simp only [hk, decide_true, ite_true, Polynomial.coeff_X, BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits _
  · simp [hk, Ne.symm hk, Polynomial.coeff_X, residueBits, BinaryNatCode.encode]

theorem annEvaluator {F : Data} (h : F.Access) : SpaceFunction (SquareSampleInput.annCoefficient (input F)) := by
  have E := SpaceFunction.branchDecider (h.good.precompose SquareSampleInput.source SquareSampleInput.source_FP)
    h.annihilator identityAnnEvaluator
  refine E.congr (funext fun q => ?_)
  change (if SquareSampleInput.source q ∈ F.good then annCoefficient F q else _) = _
  by_cases hu : SquareSampleInput.source q ∈ F.good <;>
    simp only [hu, ite_true, ite_false, annCoefficient, SquareSampleInput.annCoefficient,
      SquareSampleInput.annValue, input, selected, SquareSampleInput.selected]

theorem access {F : Data} (h : F.Access) : (input F).Access :=
  ⟨h.count, h.degree.add (BinaryFn.const 1), h.mass.add (BinaryFn.const 1),
    h.annDegree.add (BinaryFn.const 1), h.annHeight.add (BinaryFn.const 1), rowEvaluator h, annEvaluator h⟩

theorem roots_iff (F : Data) (u : List Bool) (hu : u ∈ F.good) (z : Fin (F.count u) → ℝ) :
    (∀ i, ((input F).system u i).eval₂ (Int.castRingHom ℝ) z = 0) ↔
      ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0 := by
  simp only [input, hu, ite_true]

theorem vertex_mem_PSPACE {F : Data} (h : F.Access) :
    SquareSampleCompleteVertices.language (input F) ∈ PSPACE :=
  SquareSampleCompleteVertices.mem_PSPACE (access h)

theorem width_unary {F : Data} (h : F.Access) : UnaryFn (SquareSampleCompleteVertices.width (input F)) :=
  SquareSampleCompleteVertices.width_unary (access h)

noncomputable def language (F : Data) : Language :=
  {q | pairFst q ∈ F.good ∧ SquareSampleCompleteVertices.Valid (input F) (pairFst q) (pairSnd q)}

theorem decider {F : Data} (h : F.Access) : SpaceDecider (language F) := by
  have G := (h.good.precompose pairFst pairFst_mem_FP).flagEvaluator
  have V := (SquareSampleCompleteVertices.decider (access h)).flagEvaluator
  have E := G.andFlags V
  apply E.decider (fun w => decide (w = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, SquareSampleCompleteVertices.language, Set.mem_preimage, Set.mem_ofPred_eq,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Data} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

theorem rejects_invalid (F : Data) (q : List Bool) (hq : pairFst q ∉ F.good) : q ∉ language F :=
  fun h => hq h.1

end LeanCanny.Encoding.GuardedSquareSampleInput
