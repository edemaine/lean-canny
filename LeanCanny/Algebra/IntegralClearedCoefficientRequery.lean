/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientSpace

/-! # Requerying a fixed original cleared-coefficient family

A child record selects its saved original source separately from its spatial
exponent and old basis indices. All polynomial, height, denominator, and
layout data come from that saved source. The original readers are charged
through explicit query writers, so changing a target cannot change the source.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.requery (S : Source) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c))) : Source where
  arity c := S.arity (original c)
  free c := S.free (original c)
  offset c := S.offset (original c)
  fit c := S.fit (original c)
  sourceWidth c := S.sourceWidth (original c)
  targetWidth c := S.targetWidth (original c)
  rank c := S.rank (original c)
  carrier c := S.carrier (original c)
  ring c := S.ring (original c)
  basis c := S.basis (original c)
  polynomial c := S.polynomial (original c)
  support c := S.support (original c)
  denominator c := S.denominator (original c)
  height c := S.height (original c)
  allowance c := S.allowance (original c)
  target := target
  row := row
  col := col
  modulus c := S.modulus (original c)
  modulus_ne_zero c := S.modulus_ne_zero (original c)

def coefficientRequery (original : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (original (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

theorem coefficientRequery_FP (original : List Bool → List Bool) (h : original ∈ FP) :
    coefficientRequery original ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) h)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def heightRequery (original : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (original (pairFst q)) (pairSnd q)

theorem heightRequery_FP (original : List Bool → List Bool) (h : original ∈ FP) :
    heightRequery original ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP h) pairSnd_mem_FP

noncomputable def Access.requery (S : Source) (a : Access S) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c)))
    (h : original ∈ FP) (ht : BinaryFn target) (hr : BinaryFn (fun c => (row c).val))
    (hc : BinaryFn (fun c => (col c).val)) : Access (S.requery original target row col) where
  arity := a.arity.comp h
  free := a.free.comp h
  offset := a.offset.comp h
  sourceWidth := a.sourceWidth.comp h
  targetWidth := a.targetWidth.comp h
  rank := a.rank.comp h
  allowance := a.allowance.comp h
  target := ht
  row := hr
  col := hc
  modulus := a.modulus.comp h
  coefficient := a.coefficient ∘ coefficientRequery original
  height := a.height ∘ heightRequery original
  denominator := a.denominator ∘ original
  coefficient_eq c k r t := by
    simp only [Function.comp_apply, coefficientRequery, context, pairFst_pair, pairSnd_pair]
    exact a.coefficient_eq (original c) k r t
  height_eq c i r t := by
    simp only [Function.comp_apply, heightRequery, pairFst_pair, pairSnd_pair]
    exact a.height_eq (original c) i r t
  denominator_eq c := a.denominator_eq (original c)

theorem requery_evaluator (S : Source) (a : Access S) (original : List Bool → List Bool)
    (target : List Bool → ℕ) (row col : ∀ c, Fin (S.rank (original c)))
    (h : original ∈ FP) (ht : BinaryFn target) (hr : BinaryFn (fun c => (row c).val))
    (hc : BinaryFn (fun c => (col c).val)) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) :
    SpaceFunction (S.requery original target row col).value :=
  evaluator (S.requery original target row col) (a.requery S original target row col h ht hr hc)
    (EC.precompose (coefficientRequery original) (coefficientRequery_FP original h))
    (EH.precompose (heightRequery original) (heightRequery_FP original h)) (EQ.precompose original h)

end LeanCanny.Algebra.IntegralClearedCoefficientBits
