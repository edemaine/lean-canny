/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayPolynomialSpace
public import LeanCanny.Algebra.MacaulayBivariateBounds
public import LeanCanny.Algebra.MacaulayFullBoxSpace

/-! # Macaulay coefficients with independent projection and perturbation variables

The inner variable is the perturbation parameter; the outer variable is the
projection parameter. A radix exceeding the entire determinant's inner degree
allows the univariate backend to recover their coefficients independently.
Entry access decodes the requested univariate degree by quotient and remainder.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBivariate
open LeanCanny.Encoding LeanCanny.Computation
open MacaulayBits MatrixPower
open scoped BigOperators

structure Family where
  layout : Layout
  modulus : List Bool → ℕ
  inner : List Bool → ℕ
  outer : List Bool → ℕ
  bound : List Bool → ℕ
  polynomial : (c : List Bool) → Fin (layout.arity c) →
    MvPolynomial (Fin (layout.arity c)) (Polynomial (Polynomial (ZMod (modulus c))))
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  inner_bound : ∀ c i e j, (((polynomial c i).coeff e).coeff j).natDegree ≤ bound c

def Family.dimension (F : Family) (c : List Bool) : ℕ := FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c)
noncomputable def Family.matrix (F : Family) (c : List Bool) :
    Matrix (Fin (F.dimension c)) (Fin (F.dimension c)) (Polynomial (Polynomial (ZMod (F.modulus c)))) :=
  Macaulay.matrix (F.polynomial c) (Degrees F.layout c) (F.layout.width c)

/-- The common backend supplies the radix, Kronecker routing and zero branch. -/
noncomputable def Family.determinant (F : Family) : BivariateDeterminantBits.Family where
  dimension := F.dimension
  dimension_pos c := by unfold Family.dimension FixedWidthPolynomial.count; positivity
  modulus := F.modulus
  inner := F.inner
  outer := F.outer
  bound := F.bound
  matrix := F.matrix
  modulus_ne_zero := F.modulus_ne_zero
  inner_bound c := Macaulay.matrix_inner_degree (F.polynomial c) (Degrees F.layout c)
    (F.layout.width c) (F.bound c) (F.inner_bound c)

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c))

structure Access (F : Family) where
  modulus : List Bool → List Bool
  inner : List Bool → List Bool
  outer : List Bool → List Bool
  bound : List Bool → List Bool
  coefficient : List Bool → List Bool
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  inner_eq : ∀ c, inner c = BinaryNatCode.encode (F.inner c)
  outer_eq : ∀ c, outer c = BinaryNatCode.encode (F.outer c)
  bound_eq : ∀ c, bound c = BinaryNatCode.encode (F.bound c)
  coefficient_eq : ∀ c (i : Fin (F.layout.arity c)) k u v,
    coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
        residueBits ((((F.polynomial c i).coeff (RationalSubstitution.Indexed.exponentVector (F.layout.arity c)
          (FixedWidthPolynomial.entry (F.layout.width c) k))).coeff v).coeff u)

/-- Identity padding contributes only at inner and outer degree zero. -/
def constantEntry (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairFst (pairSnd (pairFst p))) = 0 ∧
      Nat.fromBitsLE (pairSnd (pairSnd (pairFst p))) = 0 ∧ sameIndex p then
    ArithmeticBits.one (modulus (context p)) else []

theorem constantEntry_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    constantEntry modulus ∈ FP := by
  have huv := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hz (f : List Bool → List Bool) (hf : f ∈ FP) : FPPred (fun p => Nat.fromBitsLE (f p) = 0) :=
    (BinaryFn.fromBits hf).eq (BinaryFn.const 0)
  have ho := mem_FP_comp (mem_FP_comp context_mem_FP hm) ArithmeticBits.one_mem_FP
  have hf := ((hz _ (mem_FP_comp huv pairFst_mem_FP)).and
    ((hz _ (mem_FP_comp huv pairSnd_mem_FP)).and sameIndex_fppred)).ite_mem_FP
      ho (constFn_mem_FP [])
  exact mem_FP_of_eq hf (fun _ => rfl)

theorem constantEntry_packet (modulus : List Bool → List Bool) (c : List Bool) (m u v r s : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) :
    constantEntry modulus (packet (pair c (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) r s) =
      residueBits (((((if r = s then 1 else 0) : Polynomial (Polynomial (ZMod m))).coeff v).coeff u)) := by
  simp only [constantEntry, sameIndex, context, row, col, packet, pairFst_pair,
    pairSnd_pair, fromBits_encode, hm]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> by_cases hrs : r = s <;>
    simp [hu, hv, hrs, Polynomial.coeff_one, residueBits, BinaryNatCode.encode]
  simpa only [residueBits, BinaryNatCode.encode] using ArithmeticBits.one_residueBits m

def Access.entry {F : Family} (a : Access F) : List Bool → List Bool :=
  entryWithIdentity F.layout (a.coefficient ∘ MacaulayPolynomial.sourceInput) (constantEntry a.modulus) ∘
    PolynomialMoment.augmentedInput

theorem Access.entryEvaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction a.entry :=
  (entryWithIdentityEvaluator h (E.precompose MacaulayPolynomial.sourceInput MacaulayPolynomial.sourceInput_mem_FP)
    (constantEntry_mem_FP hm)).precompose PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

theorem Access.entry_correct {F : Family} (a : Access F) (c : List Bool)
    (i j : Fin (F.dimension c)) (u v : ℕ) :
    a.entry (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      residueBits (((F.matrix c i j).coeff v).coeff u) := by
  simp only [Access.entry, Function.comp_apply, PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair]
  change entryWithIdentity F.layout (a.coefficient ∘ MacaulayPolynomial.sourceInput) (constantEntry a.modulus)
    (packet (pair c (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) i.val j.val) = _
  have H := entryWithIdentity_packet (R := Polynomial (Polynomial (ZMod (F.modulus c)))) F.layout
    (a.coefficient ∘ MacaulayPolynomial.sourceInput) (constantEntry a.modulus)
    (pair c (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))
  dsimp only [Indices] at H
  rw [pairFst_pair] at H
  refine H (F.polynomial c) (fun p => residueBits ((p.coeff v).coeff u)) ?_ ?_ i j ?_
  · simp [residueBits, BinaryNatCode.encode]
  · intro k r
    simpa only [Function.comp_apply, MacaulayPolynomial.sourceInput, context, row, col,
      packet, pairFst_pair, pairSnd_pair] using a.coefficient_eq c k r u v
  · exact constantEntry_packet a.modulus c (F.modulus c) u v i.val j.val (a.modulus_eq c)

theorem Access.evaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP)
    (E : SpaceFunction a.coefficient) : SpaceFunction F.value :=
  F.determinant.evaluator a.entry a.entry_correct
    (BinaryFn.of_bits (mem_FP_of_eq (dimensionCode_mem_FP h) (FixedWidthPolynomial.countCode_code _ _)))
    (BinaryFn.of_bits (mem_FP_of_eq hm a.modulus_eq)) (BinaryFn.of_bits (mem_FP_of_eq hb a.bound_eq))
    (BinaryFn.of_bits (mem_FP_of_eq hi a.inner_eq)) (BinaryFn.of_bits (mem_FP_of_eq ho a.outer_eq))
    (a.entryEvaluator h hm E)

def Family.zeroLanguage (F : Family) : LeanCanny.Language :=
  {c | ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0}

theorem Access.zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP)
    (E : SpaceFunction a.coefficient) : F.zeroLanguage ∈ PSPACE := by
  have ES := a.evaluator h hm hb hi ho E
  have EA := (Encoding.Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply SpaceDecider.mem_PSPACE
  refine ES.decider (fun z => decide (z = [])) EA ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0 ↔
    decide (residueBits (((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c)) = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

end LeanCanny.Algebra.MacaulayBivariate
