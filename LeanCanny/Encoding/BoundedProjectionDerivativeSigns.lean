/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionThom

/-! # Native sign queries for selected projection derivatives

The number of queried features is polynomially bounded, while every derivative
order is binary and may exceed the degree. Counts include extraneous projection
roots. This does not enumerate the full, potentially exponential Thom signature.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionDerivativeSigns
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial

noncomputable def family (P : Readers) (count : List Bool → ℕ)
    (orders : List Bool → List Bool) (pattern : List Bool → ℕ → SignType) : SignPatternBits.Family where
  root := BoundedCriticalProjection.polynomial P
  polynomial c i := BoundedProjectionThom.polynomial P c (Nat.fromBitsLE (orders (pair c (BinaryNatCode.encode i))))
  pattern := pattern
  count c := BinaryNatCode.encode (count c)
  rootDegree c := BinaryNatCode.encode (BoundedProjectionRootCount.degree P c)
  degree c := BinaryNatCode.encode (BoundedProjectionRootCount.degree P c)
  rootMass c := BinaryNatCode.encode (BoundedProjectionRootCount.massExponent P c)
  mass c := BinaryNatCode.encode (BoundedProjectionThom.massExponent P c)
  rootDegree_pos c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact pow_pos (by decide) _
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedCriticalProjection.polynomial_degree P c
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionRootCount.mass_bound P c
  polynomial_degree c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionThom.degree P c _
  polynomial_mass c _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionThom.mass_bound P c _

theorem family_polyTime {P : Readers} {count : List Bool → ℕ}
    (h : P.PolyTime) (hc : UnaryFn count) (orders : List Bool → List Bool)
    (pattern : List Bool → ℕ → SignType) : SignPatternBits.ControlsPolyTime (family P count orders pattern) := by
  refine ⟨bits_mem_FP hc, ?_,
    (BoundedProjectionRootCount.degree_binary h).bits_mem_FP,
    (BoundedProjectionRootCount.degree_binary h).bits_mem_FP,
    (BoundedProjectionRootCount.massExponent_binary h).bits_mem_FP,
    (BoundedProjectionThom.massExponent_binary h).bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hc

/-- Replace the feature index by its selected, canonically encoded derivative order. -/
def query (orders : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (BoundedProjectionThom.original q)
    (pair (BinaryNatCode.encode (Nat.fromBitsLE (orders
      (pair (BoundedProjectionThom.original q) (BoundedProjectionThom.order q)))))
      (BoundedProjectionThom.index q))) (pairSnd q)

theorem query_FP {orders : List Bool → List Bool} (ho : orders ∈ FP) : query orders ∈ FP := by
  have hi := mem_FP_comp (mem_FP_pair BoundedProjectionThom.original_FP BoundedProjectionThom.order_FP) ho
  have hn := (BinaryFn.fromBits hi).bits_mem_FP
  have h := mem_FP_pair (mem_FP_pair BoundedProjectionThom.original_FP
    (mem_FP_pair hn BoundedProjectionThom.index_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [query, Function.comp_apply])

noncomputable def access (P : Readers) (count : List Bool → ℕ)
    (orders : List Bool → List Bool) (pattern : List Bool → ℕ → SignType)
    (patternBits : List Bool → List Bool)
    (hs : ∀ c i, patternBits (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (pattern c i)) :
    SignPatternBits.Access (family P count orders pattern) where
  rootCoefficient := BoundedProjectionRootCount.coefficient P
  polynomialCoefficient := BoundedProjectionThom.value P ∘ query orders
  pattern := patternBits
  root_eq := BoundedProjectionRootCount.coefficient_packet P
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, query, BoundedProjectionThom.original, BoundedProjectionThom.order,
      BoundedProjectionThom.index, pairFst_pair, pairSnd_pair]
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact BoundedProjectionThom.value_packet P c _ k w
  pattern_eq := hs

noncomputable def count (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) (pattern : List Bool → ℕ → SignType) (c : List Bool) : ℕ :=
  SignPatternBits.rootCount (family P features orders pattern) c

attribute [local irreducible] BoundedProjectionThom.value BoundedProjectionRootCount.coefficient query

theorem evaluator {P : Readers} {features : List Bool → ℕ} {orders patternBits : List Bool → List Bool}
    {pattern : List Bool → ℕ → SignType} (h : P.PolyTime) (hc : UnaryFn features)
    (ho : orders ∈ FP) (hp : patternBits ∈ FP)
    (hs : ∀ c i, patternBits (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (pattern c i))
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (count P features orders pattern c)) := by
  have H := BoundedProjectionRootCount.coefficient_evaluator h ha
  have Q := (BoundedProjectionThom.evaluator h ha).precompose (query orders) (query_FP ho)
  have E := SignPatternBits.rootCountEvaluator (access P features orders pattern patternBits hs)
    (family_polyTime h hc orders pattern) hp H Q
  exact E

/-- A root realizing these derivative signs exists. No sample-validity claim
is made for an extraneous root of the projection polynomial. -/
noncomputable def language (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) (pattern : List Bool → ℕ → SignType) : Language :=
  SignPatternBits.realizableLanguage (family P features orders pattern)

theorem language_iff (P : Readers) (features : List Bool → ℕ)
    (orders : List Bool → List Bool) (pattern : List Bool → ℕ → SignType) (c : List Bool) :
    c ∈ language P features orders pattern ↔ ∃ x : ℝ,
      (BoundedCriticalProjection.polynomial P c).eval₂ (Int.castRingHom ℝ) x = 0 ∧
      ∀ i : Fin (features c), SignType.sign ((BoundedProjectionThom.polynomial P c
        (Nat.fromBitsLE (orders (pair c (BinaryNatCode.encode i.val))))).eval₂ (Int.castRingHom ℝ) x) =
          pattern c i.val := by
  dsimp only [language, SignPatternBits.realizableLanguage, family, Set.mem_ofPred_eq]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (features c)) = features c from Nat.fromBitsLE_bits _]
  simp only [BinaryNatCode.encode, Polynomial.eval_map, algebraMap_int_eq]

theorem decider {P : Readers} {features : List Bool → ℕ} {orders patternBits : List Bool → List Bool}
    {pattern : List Bool → ℕ → SignType} (h : P.PolyTime) (hc : UnaryFn features)
    (ho : orders ∈ FP) (hp : patternBits ∈ FP)
    (hs : ∀ c i, patternBits (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (pattern c i))
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (language P features orders pattern) := by
  have H := BoundedProjectionRootCount.coefficient_evaluator h ha
  have Q := (BoundedProjectionThom.evaluator h ha).precompose (query orders) (query_FP ho)
  have E := SignPatternBits.positiveDecider (access P features orders pattern patternBits hs)
    (family_polyTime h hc orders pattern) hp H Q
  have he : SignPatternBits.positiveLanguage (family P features orders pattern) =
      language P features orders pattern := by
    ext c
    exact SignPatternBits.positive_iff_realizable _ c (BoundedCriticalProjection.polynomial_ne_zero P c)
  rw [← he]
  exact E

end LeanCanny.Encoding.BoundedProjectionDerivativeSigns
