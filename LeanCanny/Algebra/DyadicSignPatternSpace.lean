/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicSignPatternSource

/-! # Exact root-sign counts at a selected dyadic parameter in polynomial space

A polynomially bounded query family is evaluated at the same beta as the root
polynomial. Positive denominator clearing preserves all requested signs and
distinct roots, so the integer evaluator returns the real specialized count.
This statement does not assume or establish eventual stability as beta tends
to zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial

theorem root_signCount_C_mul {J : Type*} (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b) :
    signCount (C a * p).roots.toFinset (fun i => C b * Q i) σ = signCount p.roots.toFinset Q σ := by
  classical
  simp only [signCount, roots_C_mul p ha, eval_mul, eval_C, sign_mul, sign_pos hb, one_mul]

end LeanCanny.Algebra.RootSignQueries

namespace LeanCanny.Algebra.DyadicSignPatternBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

noncomputable def rootPolynomial (F : Family) (c : List Bool) : ℝ[X] :=
  (F.root.polynomial c).map (DyadicPolynomial.evalHom (Nat.fromBitsLE (F.root.exponent c)))

noncomputable def queryPolynomial (F : Family) (c : List Bool) (i : ℕ) : ℝ[X] :=
  (F.polynomial c i).map (DyadicPolynomial.evalHom (Nat.fromBitsLE (F.root.exponent c)))

noncomputable def rootCount (F : Family) (c : List Bool) : ℕ := RootSignQueries.signCount
  (rootPolynomial F c).roots.toFinset
  (fun i : Fin (Nat.fromBitsLE (F.count c)) => queryPolynomial F c i.val)
  (fun i => F.pattern c i.val)

theorem root_specialized_map (F : Family) (c : List Bool) :
    (F.root.specialized c).map (algebraMap ℤ ℝ) =
      C ((2 : ℝ) ^ (Nat.fromBitsLE (F.root.exponent c) * Nat.fromBitsLE (F.root.parameterDegree c))) *
        rootPolynomial F c :=
  DyadicPolynomial.map_specialize _ _ _ (F.root.coefficient_degree c)

theorem query_specialized_map (F : Family) (c : List Bool) (i : ℕ) :
    ((queryFamily F).specialized (pair c (BinaryNatCode.encode i))).map (algebraMap ℤ ℝ) =
      C ((2 : ℝ) ^ (Nat.fromBitsLE (F.root.exponent c) * Nat.fromBitsLE (F.parameterDegree c))) *
        queryPolynomial F c i := by
  simp only [DyadicPolynomialBits.Family.specialized, queryFamily, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact DyadicPolynomial.map_specialize _ _ _ (F.coefficient_degree c i)

theorem family_rootCount (F : Family) (c : List Bool) : SignPatternBits.rootCount (family F) c = rootCount F c := by
  change RootSignQueries.signCount ((F.root.specialized c).map (algebraMap ℤ ℝ)).roots.toFinset
    (fun i : Fin (Nat.fromBitsLE (F.count c)) =>
      ((queryFamily F).specialized (pair c (BinaryNatCode.encode i.val))).map (algebraMap ℤ ℝ))
    (fun i => F.pattern c i.val) = _
  simp_rw [root_specialized_map, query_specialized_map]
  exact RootSignQueries.root_signCount_C_mul _ _ _ _ _
    (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) (pow_pos (by norm_num : (0 : ℝ) < 2) _)

/-- All specialized coefficient readers are constructed from original bivariate
coefficient routines. The family size has the same unary FP bound as the integer
sign-pattern evaluator. -/
theorem rootCountEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (rootCount F c)) := by
  let E := SignPatternBits.rootCountEvaluator (access a) (controls F hF) hs
    (DyadicPolynomialBits.residueEvaluator a.root hF.root H) (queryEvaluator a hF P)
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (family_rootCount F c))

def positiveLanguage (F : Family) : Language := {c | 0 < rootCount F c}

theorem positiveDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    SpaceDecider (positiveLanguage F) := by
  have hflag := (stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (rootCountEvaluator a hF hs H P).decider (fun v => decide (v ≠ [])) hflag
  intro c
  simp only [positiveLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, BinaryNatCode.encode,
    ne_eq, BinaryNat.bits_eq_nil_iff]
  omega

theorem positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    positiveLanguage F ∈ PSPACE := (positiveDecider a hF hs H P).mem_PSPACE

def realizableLanguage (F : Family) : Language := {c | ∃ x : ℝ,
  (rootPolynomial F c).eval x = 0 ∧ ∀ i : Fin (Nat.fromBitsLE (F.count c)),
    SignType.sign ((queryPolynomial F c i.val).eval x) = F.pattern c i.val}

def guardedRealizableLanguage (F : Family) : Language :=
  {c | rootPolynomial F c ≠ 0 ∧ c ∈ realizableLanguage F}

theorem positive_iff_realizable (F : Family) (c : List Bool) (hp : rootPolynomial F c ≠ 0) :
    c ∈ positiveLanguage F ↔ c ∈ realizableLanguage F :=
  RootSignQueries.root_signCount_pos _ hp _ _

theorem positiveLanguage_eq_guarded (F : Family) : positiveLanguage F = guardedRealizableLanguage F := by
  ext c
  by_cases hp : rootPolynomial F c = 0
  · simp only [positiveLanguage, guardedRealizableLanguage, Set.mem_ofPred_eq, rootCount, hp,
      Polynomial.roots_zero, Multiset.toFinset_zero, RootSignQueries.signCount, Finset.filter_empty,
      Finset.card_empty, lt_self_iff_false, ne_eq, not_true_eq_false, false_and]
  · simp only [guardedRealizableLanguage, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hp, (positive_iff_realizable F c hp).mp h⟩,
      fun h => (positive_iff_realizable F c hp).mpr h.2⟩

theorem guardedRealizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    guardedRealizableLanguage F ∈ PSPACE := by
  rw [← positiveLanguage_eq_guarded]
  exact positiveLanguage_mem_PSPACE a hF hs H P

theorem realizableLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient)
    (hp : ∀ c, rootPolynomial F c ≠ 0) : realizableLanguage F ∈ PSPACE := by
  have he : guardedRealizableLanguage F = realizableLanguage F := by
    ext c
    change (rootPolynomial F c ≠ 0 ∧ c ∈ realizableLanguage F) ↔ c ∈ realizableLanguage F
    exact ⟨fun h => h.2, fun h => ⟨hp c, h⟩⟩
  rw [← he]
  exact guardedRealizableLanguage_mem_PSPACE a hF hs H P

theorem rootPolynomial_ne_zero_of_small (F : Family) (c : List Bool)
    (hp : F.root.polynomial c ≠ 0)
    (hs : Nat.fromBitsLE (F.root.mass c) < Nat.fromBitsLE (F.root.exponent c)) :
    rootPolynomial F c ≠ 0 := by
  have hn : F.root.specialized c ≠ 0 :=
    (DyadicPolynomial.specialize_eq_zero_iff _ _ _ _
      (F.root.coefficient_degree c) (F.root.coefficient_mass c) hs).not.mpr hp
  have hi : Function.Injective (algebraMap ℤ ℝ) := by
    intro x y h
    exact Int.cast_injective h
  have hm := (Polynomial.map_ne_zero_iff hi).mpr hn
  rw [root_specialized_map] at hm
  intro hz
  rw [hz, mul_zero] at hm
  exact hm rfl

/-- A nonzero original root polynomial remains nonzero at the effectively small
parameter; no separate specialized-nonvanishing hypothesis is needed. -/
theorem realizableLanguage_mem_PSPACE_of_small {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient)
    (hp : ∀ c, F.root.polynomial c ≠ 0)
    (hsmall : ∀ c, Nat.fromBitsLE (F.root.mass c) < Nat.fromBitsLE (F.root.exponent c)) :
    realizableLanguage F ∈ PSPACE :=
  realizableLanguage_mem_PSPACE a hF hs H P (fun c => rootPolynomial_ne_zero_of_small F c (hp c) (hsmall c))

end LeanCanny.Algebra.DyadicSignPatternBits
