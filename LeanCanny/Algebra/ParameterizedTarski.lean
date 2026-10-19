/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.EffectiveInfinitesimalSign
public import LeanCanny.Algebra.PseudoRemainderQuery

/-! # Polynomial tests controlling a small-parameter Tarski query

The leading coefficients of the head and its symbolic pseudo-seed control their
degrees. Fixed-bound signed principal coefficients then control the complete
query. A finite sum of their coefficient masses gives a common dyadic interval.
The budget here is a mathematical expression in the symbolic polynomials; an FP
bound derived from the original source bounds is a separate resource obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.ParameterTarski
open Polynomial PrincipalSubresultant

noncomputable def evalHom (x : ℝ) : ℤ[X] →+* ℝ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) x

noncomputable def seed (p f : (ℤ[X])[X]) : (ℤ[X])[X] :=
  PseudoRemainder.seed p f p.natDegree (p.natDegree + f.natDegree)

noncomputable def principal (p f : (ℤ[X])[X]) (j : ℕ) : ℤ[X] :=
  signedPsc p (seed p f) p.natDegree (seed p f).natDegree j

noncomputable def tests (p f : (ℤ[X])[X]) : List ℤ[X] :=
  p.leadingCoeff :: (seed p f).leadingCoeff :: (List.range (p.natDegree + 1)).map (principal p f)

noncomputable def budget (p f : (ℤ[X])[X]) : ℕ := ((tests p f).map coefficientMass).sum.size

structure Bounded (p f : (ℤ[X])[X]) (b : ℕ) : Prop where
  head : coefficientMass p.leadingCoeff ≤ 2 ^ b
  seed : coefficientMass (seed p f).leadingCoeff ≤ 2 ^ b
  principal : ∀ j, j ≤ p.natDegree → coefficientMass (principal p f j) ≤ 2 ^ b

theorem Bounded.mono {p f : (ℤ[X])[X]} {b c : ℕ} (h : Bounded p f b) (hbc : b ≤ c) : Bounded p f c := by
  have hpow : 2 ^ b ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hbc
  exact ⟨h.head.trans hpow, h.seed.trans hpow, fun j hj => (h.principal j hj).trans hpow⟩

theorem mass_le_tests (p f : (ℤ[X])[X]) (t : ℤ[X]) (ht : t ∈ tests p f) :
    coefficientMass t ≤ 2 ^ budget p f := by
  have hm : coefficientMass t ∈ (tests p f).map coefficientMass := List.mem_map.mpr ⟨t, ht, rfl⟩
  exact (List.le_sum_of_mem hm).trans (Nat.lt_size_self _).le

theorem budget_bounded (p f : (ℤ[X])[X]) : Bounded p f (budget p f) := by
  constructor
  · exact mass_le_tests p f _ List.mem_cons_self
  · exact mass_le_tests p f _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro j hj
    apply mass_le_tests p f
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩

theorem natDegree_eval (p : (ℤ[X])[X]) (b s : ℕ)
    (hm : coefficientMass p.leadingCoeff ≤ 2 ^ b) (hs : b < s)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic s) :
    (p.map (evalHom x)).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have ht : p.leadingCoeff.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hl
    have he := InfinitesimalSign.integer_sign_eval_le_dyadic p.leadingCoeff b s hm hs x hx hxs
    have hn : evalHom x p.leadingCoeff ≠ 0 := by
      intro hz
      change SignType.sign (evalHom x p.leadingCoeff) = _ at he
      rw [hz, sign_zero] at he
      exact ht (sign_eq_zero_iff.mp he.symm)
    have hc : (p.map (evalHom x)).coeff p.natDegree ≠ 0 := by
      rw [coeff_map, coeff_natDegree]
      exact hn
    exact le_antisymm natDegree_map_le (le_natDegree_of_ne_zero hc)

noncomputable def value (p f : (ℤ[X])[X]) : ℤ :=
  if p.natDegree = 0 then 0 else permanencesMinusVariations
    ((List.range (p.natDegree + 1)).reverse.map fun j => (principal p f j).trailingCoeff)

theorem query_eq_value (p f : (ℤ[X])[X]) (b s : ℕ) (h : Bounded p f b) (hs : b < s)
    (x : ℝ) (hx : 0 < x) (hxs : x ≤ InfinitesimalSign.dyadic s) :
    RootSignQueries.tarskiQuery (p.map (evalHom x)) (f.map (evalHom x)) = value p f := by
  by_cases hp : p.natDegree = 0
  · have hz : (p.map (evalHom x)).natDegree = 0 := by
      have hd : (p.map (evalHom x)).natDegree ≤ p.natDegree := natDegree_map_le
      omega
    rw [value, ite_eq_left hp, eq_C_of_natDegree_eq_zero hz]
    simp only [RootSignQueries.tarskiQuery, roots_C, RootSignQueries.signSum,
      Multiset.toFinset_zero, Finset.sum_empty]
  · have hd := natDegree_eval p b s h.head hs x hx hxs
    have hn := natDegree_eval (seed p f) b s h.seed hs x hx hxs
    have hD : (f.map (evalHom x) * (p.map (evalHom x)).derivative).natDegree ≤ p.natDegree + f.natDegree := by
      have hf : (f.map (evalHom x)).natDegree ≤ f.natDegree := natDegree_map_le
      have hp' := (natDegree_derivative_le (p.map (evalHom x))).trans (Nat.sub_le _ _)
      exact natDegree_mul_le.trans (by omega)
    rw [RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ _ _ hd (by omega) hD,
      PseudoRemainder.principalQuery, PseudoRemainder.seed_map]
    change permanencesMinusVariations ((List.range (p.natDegree + 1)).reverse.map
      (signedPsc (p.map (evalHom x)) ((seed p f).map (evalHom x)) p.natDegree
        ((seed p f).map (evalHom x)).natDegree)) = _
    rw [hn, value, ite_eq_right hp]
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j ≤ p.natDegree := by
      have := List.mem_range.mp (List.mem_reverse.mp hj)
      omega
    change SignType.sign (signedPsc (p.map (evalHom x)) ((seed p f).map (evalHom x))
      p.natDegree (seed p f).natDegree j) = SignType.sign (principal p f j).trailingCoeff
    rw [signedPsc_map_map]
    exact InfinitesimalSign.integer_sign_eval_le_dyadic (principal p f j) b s (h.principal j hj') hs x hx hxs

/-- The displayed budget is obtained from the finite polynomial tests, including
zero tests. It is not an assumed interval of constancy. -/
theorem query_eq_value_on_interval (p f : (ℤ[X])[X]) (x : ℝ) (hx : 0 < x)
    (hxs : x ≤ InfinitesimalSign.dyadic (budget p f + 1)) :
    RootSignQueries.tarskiQuery (p.map (evalHom x)) (f.map (evalHom x)) = value p f :=
  query_eq_value p f _ _ (budget_bounded p f) (Nat.lt_succ_self _) x hx hxs

theorem query_stable (p f : (ℤ[X])[X]) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxs : x ≤ InfinitesimalSign.dyadic (budget p f + 1))
    (hys : y ≤ InfinitesimalSign.dyadic (budget p f + 1)) :
    RootSignQueries.tarskiQuery (p.map (evalHom x)) (f.map (evalHom x)) =
      RootSignQueries.tarskiQuery (p.map (evalHom y)) (f.map (evalHom y)) :=
  (query_eq_value_on_interval p f x hx hxs).trans (query_eq_value_on_interval p f y hy hys).symm

end LeanCanny.Algebra.ParameterTarski
