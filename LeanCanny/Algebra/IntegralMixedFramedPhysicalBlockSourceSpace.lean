/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtDerivativeSpace
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightCoefficientSpace
/-! # Exact source and gradient terms occupy the actual ambient block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family IntegralCriticalHistoryTask.modulus residueBits
  FixedWidthRowBits.value MvPolynomial.pderiv MvPolynomial.rename IntegralMixedPhysicalOriginalSourceBits.polynomial

noncomputable def sourcePolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :=
  MvPolynomial.rename (ambientIndex P D J base q)
    (IntegralMixedPhysicalOriginalSourceBits.polynomial (IntegralMixedFramedPhysicalSourceAtBits.family P D J base) q)

noncomputable def derivativePolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :
    MvPolynomial (Fin (fullCount P D J base q)) ℤ := by
  let p : MvPolynomial (Fin (spatialCount P D J base q)) ℤ:=
    IntegralMixedPhysicalOriginalSourceBits.polynomial (IntegralMixedFramedPhysicalSourceAtBits.family P D J base) q
  exact MvPolynomial.rename (ambientIndex P D J base q) (MvPolynomial.pderiv ⟨selected q,hs q⟩ p)

attribute [local irreducible] sourcePolynomial derivativePolynomial

theorem sourceModulus_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) :
    IntegralMixedPhysicalOriginalSourceBits.modulusWord (IntegralMixedFramedPhysicalSourceAtBits.family P D J base)
      (IntegralMixedFramedPhysicalSourceAtBits.indices P D J base)=IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base := by
  funext q
  dsimp only [IntegralMixedPhysicalOriginalSourceBits.modulusWord,IntegralMixedFramedPhysicalHeightBits.modulusWord,
    IntegralMixedFramedPhysicalSourceAtBits.indices,IntegralMixedPhysicalOriginalPullBits.indices,
    IntegralMixedFramedPhysicalLowBits.indices,IntegralMixedPhysicalTaskBits.indices,IntegralMixedPhysicalQueryBits.indices,
    IntegralMixedPhysicalTaskBits.queries,IntegralMixedPhysicalQueryBits.taskQueries,Function.comp_apply]

theorem source_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V (sourcePolynomial P D J base) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  rw [←sourceModulus_eq P D J base]
  unfold sourcePolynomial
  have HA:=spatialCount_unary P a D J c base hb
  have HN:=fullCount_unary P a D J c base hb
  have HI:=ambientReader_FP P a D J c base hb
  exact FixedWidthEmbeddingBits.evaluator (spatialCount P D J base) (fullCount P D J base) V target (ambientReader P D base)
    (IntegralMixedPhysicalOriginalSourceBits.polynomial (IntegralMixedFramedPhysicalSourceAtBits.family P D J base))
    (ambientIndex P D J base) (ambientIndex_injective P D J base) (ambientReader_packet P D J base)
    _ HA HN hV ht HI (IntegralMixedFramedPhysicalSourceAtBits.evaluator P a D J c base hb V hV _
      (FixedWidthEmbeddingBits.word_FP _ _ _ _ _ HA HN hV ht HI))

theorem derivative_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V (derivativePolynomial P D J base selected hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  rw [←sourceModulus_eq P D J base]
  unfold derivativePolynomial
  have HA:=spatialCount_unary P a D J c base hb
  have HN:=fullCount_unary P a D J c base hb
  have HI:=ambientReader_FP P a D J c base hb
  exact FixedWidthEmbeddingBits.evaluator (spatialCount P D J base) (fullCount P D J base) V target (ambientReader P D base)
    (fun q=>MvPolynomial.pderiv ⟨selected q,hs q⟩
      (IntegralMixedPhysicalOriginalSourceBits.polynomial (IntegralMixedFramedPhysicalSourceAtBits.family P D J base) q))
    (ambientIndex P D J base) (ambientIndex_injective P D J base) (ambientReader_packet P D J base)
    _ HA HN hV ht HI (IntegralMixedFramedPhysicalSourceAtBits.derivative_evaluator P a D J c base hb selected hs hselected V hV _
      (FixedWidthEmbeddingBits.word_FP _ _ _ _ _ HA HN hV ht HI))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
