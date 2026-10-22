/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.EtaleDerivation
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.Perfect

/-! # Derivations detecting transcendental elements in characteristic zero

A coordinate derivation on an algebraically independent polynomial subalgebra
extends through its fraction field and a separable algebraic extension. A
transcendence basis containing a chosen transcendental element therefore gives
a derivation taking that element to one.
-/

@[expose] public section

namespace LeanCanny.Algebra.TranscendentalDerivation
open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  {v : ι → L}

noncomputable def onAdjoin (hv : AlgebraicIndependent K v) (j : ι) :
    Derivation K (Algebra.adjoin K (Set.range v)) L where
  toLinearMap := (MvPolynomial.aeval v).toLinearMap.comp
    ((pderiv j).toLinearMap.comp hv.repr.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change MvPolynomial.aeval v (pderiv j (hv.repr (a * b))) =
      a • MvPolynomial.aeval v (pderiv j (hv.repr b)) +
        b • MvPolynomial.aeval v (pderiv j (hv.repr a))
    simp only [map_mul, pderiv_mul, map_add, hv.aeval_repr, Algebra.smul_def]
    ac_rfl

theorem onAdjoin_generator (hv : AlgebraicIndependent K v) (j : ι) :
    onAdjoin hv j (hv.aevalEquiv (X j)) = 1 := by
  change MvPolynomial.aeval v (pderiv j (hv.repr (hv.aevalEquiv (X j)))) = 1
  simp [AlgebraicIndependent.repr]

variable [CharZero K]

theorem exists_of_basis (hv : IsTranscendenceBasis K v) (j : ι) :
    ∃ δ : Derivation K L L, δ (v j) = 1 := by
  let A := Algebra.adjoin K (Set.range v)
  let B := IntermediateField.adjoin K (Set.range v)
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  let : Algebra.IsAlgebraic B L := hv.isAlgebraic_field
  let : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.comp A B L
  refine ⟨EtaleDerivation.extend (onAdjoin hv.1 j), ?_⟩
  have h := EtaleDerivation.extend_algebraMap (onAdjoin hv.1 j) (hv.1.aevalEquiv (X j))
  simpa only [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X, onAdjoin_generator] using h

theorem exists_of_transcendental {x : L} (hx : Transcendental K x) :
    ∃ δ : Derivation K L L, δ x = 1 := by
  have hi : AlgebraicIndepOn K id ({x} : Set L) :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun y : ({x} : Set L) => (y : L))
      ⟨x, Set.mem_singleton x⟩).mpr hx
  obtain ⟨s, hs, hb⟩ := exists_isTranscendenceBasis_superset hi
  exact exists_of_basis hb ⟨x, hs (Set.mem_singleton x)⟩

theorem algebraic_of_all_derivations_vanish {x : L} (hx : ∀ δ : Derivation K L L, δ x = 0) :
    IsAlgebraic K x := by
  by_contra hn
  obtain ⟨δ, hδ⟩ := exists_of_transcendental hn
  exact one_ne_zero (hδ.symm.trans (hx δ))

end LeanCanny.Algebra.TranscendentalDerivation
