/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateInfinity
public import LeanCanny.Algebra.HomogenizationParameterSpace
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Native coordinate-grid rows with polynomial coefficients

A coordinate polynomial occupies one spatial variable. Its native bivariate
reader supplies one coefficient; FP guards reject exponents in other variables
and invalid coordinate indices. Empty coordinate families are supported.
-/

@[expose] public section
namespace LeanCanny.Algebra.DiagonalParameterBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma coefficient {R ι : Type*} [CommRing R] (p : Polynomial R) (i : ι) (e : ι →₀ ℕ) :
    (p.toMvPolynomial i).coeff e = if ∀ j, j ≠ i → e j = 0 then p.coeff (e i) else 0 := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def, map_sum]
  simp only [UnivariateInfinity.monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases h : ∀ j, j ≠ i → e j = 0
  · rw [ite_eq_left h]
    have he (k : ℕ) : Finsupp.single i k = e ↔ k = e i := by
      constructor
      · intro hk
        simpa only [Finsupp.single_eq_same] using congrArg (fun u : ι →₀ ℕ => u i) hk
      · intro hk
        ext j
        by_cases hj : j = i
        · subst j; simpa only [Finsupp.single_eq_same] using hk
        · simp [hj, h j hj]
    simp only [he, Finset.sum_ite_eq']
    by_cases hs : e i ∈ p.support
    · simp only [hs, ite_true]
    · simp only [hs, ite_false, Polynomial.notMem_support_iff.mp hs]
  · rw [ite_eq_right h]
    have he (k : ℕ) : Finsupp.single i k ≠ e := by
      intro hk
      apply h
      intro j hj
      rw [← hk]
      simp [hj]
    simp only [he, ite_false, Finset.sum_const_zero]

noncomputable def selectedAt (N : List Bool → ℕ)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ)) (c : List Bool) (i : ℕ) : Polynomial (Polynomial ℤ) :=
  if hi : i < N c then p c ⟨i, hi⟩ else 0

noncomputable def selected (N : List Bool → ℕ)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ)) (q : List Bool) : Polynomial (Polynomial ℤ) :=
  selectedAt N p (pairFst q) (Nat.fromBitsLE (pairSnd q))

noncomputable def polynomial (N : List Bool → ℕ)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ)) (row : List Bool → ℕ)
    (c : List Bool) : MvPolynomial (Fin (N c)) (Polynomial ℤ) :=
  if hi : row c < N c then (p c ⟨row c, hi⟩).toMvPolynomial ⟨row c, hi⟩ else 0

def exponentAt (N W : List Bool → ℕ) (q : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (N ∘ pairFst) (W ∘ pairFst) pairSnd q i

def read (N W : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read (N ∘ pairFst) (W ∘ pairFst) pairSnd

lemma read_FP {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) : read N W ∈ FP :=
  FixedWidthQuery.read_mem_FP (hN.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP

def outsideZero (N W row : List Bool → ℕ) (q : List Bool) : Prop :=
  ∀ i < N (pairFst q), i ≠ row (pairFst q) → exponentAt N W q i = 0

instance (N W row : List Bool → ℕ) : DecidablePred (outsideZero N W row) :=
  fun _ => inferInstanceAs (Decidable (∀ i < _, _))

lemma outsideZero_FP {N W row : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hr : BinaryFn row) :
    FPPred (outsideZero N W row) := by
  have he := BinaryFn.fromBits (mem_FP_comp MacaulayBits.loopQuery_mem_FP (read_FP hN hW))
  have hi := BinaryFn.ofUnary UnaryFn.index
  have hr' : BinaryFn (fun z => row (pairFst (pairFst z))) := (hr.comp pairFst_mem_FP).comp pairFst_mem_FP
  have hg := ((hi.eq hr').or (he.eq (BinaryFn.const 0))).forall_lt (hN.comp pairFst_mem_FP)
  apply hg.of_iff
  intro q
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, read, FixedWidthQuery.read_packet, MacaulayBits.fromBits_encode]
  constructor
  · intro h i hi hne
    exact (h i hi).resolve_left hne
  · intro h i hi
    by_cases heq : i = row (pairFst q)
    · exact Or.inl heq
    · exact Or.inr (h i hi heq)

lemma exponent_at (N W : List Bool → ℕ) (q : List Bool) (i : Fin (N (pairFst q))) :
    FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i = exponentAt N W q i.val := by
  simp only [FixedWidthPolynomial.nativeExponent_refl, RationalSubstitution.Indexed.exponentVector,
    Finsupp.coe_equivFunOnFinite_symm, exponentAt, FixedWidthQuery.entry, Function.comp_apply,
    i.isLt, ite_true, FixedWidthQuery.coordinate, FixedWidthPolynomial.entry_eq_digit,
    BinaryNat.value_take, FixedWidthPolynomial.drop_value]

def query (N W row : List Bool → ℕ) (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (pair (pairFst q) (BinaryNatCode.encode (row (pairFst q)))) (modulus (pairFst q)))
    (pair (parameter (pairFst q)) (read N W (pair q (BinaryNatCode.encode (row (pairFst q))))))

lemma query_FP {N W row : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hr : BinaryFn row)
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    query N W row parameter modulus ∈ FP := by
  have hi := mem_FP_comp pairFst_mem_FP hr.bits_mem_FP
  have he := mem_FP_comp (mem_FP_pair id_mem_FP hi) (read_FP hN hW)
  exact mem_FP_of_eq (mem_FP_pair
    (mem_FP_pair (mem_FP_pair pairFst_mem_FP hi) (mem_FP_comp pairFst_mem_FP hm))
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) he)) (fun _ => rfl)

theorem evaluator {N W row : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hr : BinaryFn row)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (hk : parameter ∈ FP) (hm : modulus ∈ FP)
    (E : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (selected N p))) :
    SpaceFunction (HomogenizationParameterBits.source N W (polynomial N p row) parameter modulus) := by
  have hvalid := (hr.lt (BinaryFn.ofUnary hN)).comp pairFst_mem_FP
  have hmask := hvalid.and (outsideZero_FP hN hW hr)
  have R := SpaceFunction.branch (fun q => decide (row (pairFst q) < N (pairFst q) ∧ outsideZero N W row q))
    hmask.flag_mem_FP (E.precompose (query N W row parameter modulus) (query_FP hN hW hr hk hm))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply]
  by_cases hi : row (pairFst q) < N (pairFst q)
  · have hzero : outsideZero N W row q ↔ ∀ j : Fin (N (pairFst q)),
        j ≠ ⟨row (pairFst q), hi⟩ →
          FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)) j = 0 := by
      simp only [exponent_at]
      constructor
      · intro h j hj
        exact h j.val j.isLt (fun he => hj (Fin.ext he))
      · intro h j hj hne
        exact h ⟨j, hj⟩ (fun he => hne (congrArg Fin.val he))
    simp only [HomogenizationParameterBits.source, polynomial, dite_eq_left hi, coefficient]
    by_cases hz : outsideZero N W row q
    · rw [ite_eq_left (hzero.mp hz), ite_eq_left ⟨hi, hz⟩]
      simp only [SymbolicFixedTableEntryBits.coefficient, query, selected,
        pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
        read, FixedWidthQuery.read_packet, exponent_at]
      rw [selectedAt, dite_eq_left hi]
      rfl
    · rw [ite_eq_right (fun h => hz (hzero.mpr h)), ite_eq_right (by simp [hi, hz])]
      simp [residueBits, BinaryNatCode.encode]
  · simp [HomogenizationParameterBits.source, polynomial, hi, residueBits, BinaryNatCode.encode]

lemma selected_comp (N : List Bool → ℕ)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ)) (f : List Bool → List Bool) (z : List Bool) :
    selected (N ∘ f) (fun c => p (f c)) z = selected N p (pair (f (pairFst z)) (pairSnd z)) := by
  simp only [selected, pairFst_pair, pairSnd_pair]
  rfl

def reindexQuery (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (pair (f (pairFst (pairFst (pairFst z)))) (pairSnd (pairFst (pairFst z))))
    (pairSnd (pairFst z))) (pairSnd z)

lemma reindexQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : reindexQuery f ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) hf
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc hi) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem coefficient_comp_evaluator (N : List Bool → ℕ)
    (p : (c : List Bool) → Fin (N c) → Polynomial (Polynomial ℤ))
    (f : List Bool → List Bool) (hf : f ∈ FP)
    (E : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (selected N p))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (selected (N ∘ f) (fun c => p (f c)))) := by
  refine (E.precompose (reindexQuery f) (reindexQuery_FP f hf)).congr (funext fun z => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient,
    reindexQuery, pairFst_pair, pairSnd_pair]
  rw [← selected_comp]

end LeanCanny.Algebra.DiagonalParameterBits
