/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceCoercivePreparation
public import LeanCanny.Geometry.CoerciveGramWitnessGrid
public import LeanCanny.Encoding.SquareSampleCompleteVertices
/-! # A total diagonal sampler from witnessed implicit Gram slices

The context stores the original source packet and a table of coefficient
witnesses. Every table gives nonzero annihilators, including malformed ones.
The original source equation is a separate own-point filter.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGrid
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CoerciveBoxGramEliminant.polynomial

def header (c : List Bool) := pairFst c
def table (c : List Bool) := pairSnd c
def slice (c : List Bool) (i : ℕ) := Nat.fromBitsLE (pairFst (WordList.get (table c) i))
def witness (c : List Bool) (i : ℕ) := Nat.fromBitsLE (pairSnd (WordList.get (table c) i))
abbrev count (S : Source) (c : List Bool) := S.arity (header c)
noncomputable def polynomial (S : Source) (c : List Bool) (i : Fin (count S c)) : Polynomial ℤ :=
  CoerciveGramWitnessGrid.polynomial (S.polynomial (header c)) (S.degree (header c))
    (fun j => slice c j.val) (fun j => witness c j.val) i
noncomputable def degree (S : Source) (c : List Bool) := ImplicitSourceCoerciveBoxGram.degreeBound S (header c)
noncomputable def mass (S : Source) (c : List Bool) := ImplicitSourceCoerciveBoxGram.massExponent S (header c)

theorem nonzero (S : Source) (c : List Bool) (i : Fin (count S c)) : polynomial S c i ≠ 0 :=
  CoerciveGramWitnessGrid.nonzero _ _ _ _ _

theorem polynomial_degree (S : Source) (c : List Bool) (i : Fin (count S c)) :
    (polynomial S c i).natDegree ≤ degree S c := by
  dsimp only [polynomial, CoerciveGramWitnessGrid.polynomial]
  split_ifs
  · simp only [Polynomial.natDegree_one]; exact Nat.zero_le _
  · exact CoerciveBoxGramEliminant.inner_degree _ _ (S.polynomial_degree (header c)) i _

theorem polynomial_mass (S : Source) (c : List Bool) (i : Fin (count S c)) :
    coefficientMass (polynomial S c i) ≤ 2 ^ mass S c := by
  dsimp only [polynomial, CoerciveGramWitnessGrid.polynomial]
  split_ifs
  · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ _
    rw [coefficientMass_C]
    exact Nat.one_le_two_pow
  · exact (NestedMass.coeff_le _ _).trans
      (CoerciveBoxGramEliminant.mass_le_pow _ _ _ (S.polynomial_degree (header c)) (S.polynomial_mass (header c)) i)

theorem coefficient_height (S : Source) (c : List Bool) (i : Fin (count S c)) (j : ℕ) :
    ((polynomial S c i).coeff j).natAbs.size ≤ mass S c + 1 := by
  have h := (coeff_natAbs_le_coefficientMass (polynomial S c i) j).trans (polynomial_mass S c i)
  simpa only [Nat.size_pow] using Nat.size_le_size h

noncomputable def input (S : Source) (hp : ∀ u, 0 < S.arity u) : SquareSampleInput.Inputs where
  count := count S
  degree c := degree S c + 1
  mass := mass S
  system c := DiagonalUnivariateSystem.system (polynomial S c)
  count_pos c := hp (header c)
  degree_pos _ := Nat.zero_lt_succ _
  system_degree c i := (DiagonalUnivariateSystem.degree_le _ _).trans ((polynomial_degree S c i).trans (Nat.le_succ _))
  system_mass c i := (DiagonalUnivariateSystem.mass_le _ _).trans (polynomial_mass S c i)
  annihilator := polynomial S
  annDegree := degree S
  annHeight c := mass S c + 1
  ann_nonzero := nonzero S
  ann_degree := polynomial_degree S
  ann_height := coefficient_height S
  ann_root _c _z hz _ i := by
    simpa only [DiagonalUnivariateSystem.system, DiagonalUnivariateSystem.eval] using hz i

theorem complete (S : Source) (hp : ∀ u, 0 < S.arity u) : SquareSampleComplete.Complete (input S hp) := by
  intro c z hz i
  simpa only [input, DiagonalUnivariateSystem.system, DiagonalUnivariateSystem.eval] using hz i

end LeanCanny.Encoding.ImplicitSourceGramGrid
