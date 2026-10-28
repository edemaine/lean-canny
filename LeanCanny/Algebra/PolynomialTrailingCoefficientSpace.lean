/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Algebra.LowestCoefficientSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native coefficients of the lowest nonzero polynomial row

A certified bivariate reader and binary degree/height allowances suffice.
The inner zero test and outer lowest-index scan account for every child
call. The zero polynomial uses the usual natural trailing-degree convention.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialTrailingCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def base (q : List Bool) : List Bool := pairFst (pairFst q)
def outer (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem outer_FP : outer ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def scalar (p : List Bool → Polynomial (Polynomial ℤ)) (q : List Bool) : ℤ :=
  ((p (base q)).coeff (Nat.fromBitsLE (outer q))).coeff (Nat.fromBitsLE (pairSnd q))

def residueQuery (q : List Bool) : List Bool :=
  pair (pair (base (pairFst q)) (pairSnd q))
    (pair (BinaryNat.normalize (pairSnd (pairFst q))) (BinaryNat.normalize (outer (pairFst q))))

theorem residueQuery_FP : residueQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := base) pairFst_mem_FP base_FP) pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
      (mem_FP_comp (mem_FP_comp (f := pairFst) (g := outer) pairFst_mem_FP outer_FP) BinaryNat.normalize_mem_FP))

theorem scalarZeroDecider (p : List Bool → Polynomial (Polynomial ℤ)) (R : CertifiedPolynomial.BivariateReader p)
    {B : List Bool → ℕ} (hB : BinaryFn B)
    (hb : ∀ c i j, (((p c).coeff i).coeff j).natAbs.size ≤ B c) :
    SpaceDecider {q | scalar p q = 0} := by
  apply IntegerZeroBits.zeroDecider (R.evaluator.precompose residueQuery residueQuery_FP)
    (fun q => BinaryNatCode.encode (B (base q))) (BinaryFn.bits_mem_FP (hB.comp base_FP)) (scalar p)
  · intro q
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact hb (base q) _ _
  · intro q m hm
    change R.coefficient (residueQuery (pair q (BinaryNatCode.encode (m - 1)))) = _
    simp only [residueQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    change R.coefficient (pair (pair (base q) (BinaryNatCode.encode (m - 1)))
      (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))
        (BinaryNatCode.encode (Nat.fromBitsLE (outer q))))) = _
    generalize hz : pair (base q) (BinaryNatCode.encode (m - 1)) = z
    have hc : pairFst z = base q := by rw [← hz, pairFst_pair]
    have hmod : Nat.fromBitsLE (pairSnd z) + 1 = m := by
      rw [← hz, pairSnd_pair]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    rw [R.coefficient_eq, hc]
    rfl

def zeroLanguage (p : List Bool → Polynomial (Polynomial ℤ)) : Language :=
  {q | (p (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0}

theorem zeroLanguage_eq_scan (p : List Bool → Polynomial (Polynomial ℤ)) (E : List Bool → ℕ)
    (hE : ∀ c i, ((p c).coeff i).natDegree ≤ E c) :
    zeroLanguage p = BoundedScan.language {q | scalar p q = 0} (fun q => E (pairFst q) + 1) := by
  ext q
  change _ = 0 ↔ ∀ i < E (pairFst q) + 1, scalar p (pair q (BinaryNatCode.encode i)) = 0
  simp only [scalar, base, outer, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · intro hz i _
    rw [hz, Polynomial.coeff_zero]
  · intro hz
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < E (pairFst q) + 1
    · exact hz i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hE (pairFst q) (Nat.fromBitsLE (pairSnd q)); omega)

theorem zeroDecider (p : List Bool → Polynomial (Polynomial ℤ)) (R : CertifiedPolynomial.BivariateReader p)
    {E B : List Bool → ℕ} (hE : BinaryFn E) (hB : BinaryFn B)
    (he : ∀ c i, ((p c).coeff i).natDegree ≤ E c)
    (hb : ∀ c i j, (((p c).coeff i).coeff j).natAbs.size ≤ B c) : SpaceDecider (zeroLanguage p) := by
  have hn : BinaryFn (fun q => E (pairFst q) + 1) :=
    (hE.add (BinaryFn.const 1)).comp pairFst_mem_FP
  have D := BoundedScan.decider (scalarZeroDecider p R hB hb)
    (fun q => BinaryNatCode.encode (E (pairFst q) + 1)) hn.bits_mem_FP
    (fun q => E (pairFst q) + 1) (fun _ => rfl)
  exact D.congr (zeroLanguage_eq_scan p E he).symm

noncomputable def index (p : List Bool → Polynomial (Polynomial ℤ)) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (p c).natTrailingDegree

theorem index_evaluator (p : List Bool → Polynomial (Polynomial ℤ)) (R : CertifiedPolynomial.BivariateReader p)
    {D E B : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) (hB : BinaryFn B)
    (hd : ∀ c, (p c).natDegree ≤ D c) (he : ∀ c i, ((p c).coeff i).natDegree ≤ E c)
    (hb : ∀ c i j, (((p c).coeff i).coeff j).natAbs.size ≤ B c) : SpaceFunction (index p) := by
  apply LowestCoefficientBits.evaluator (zeroDecider p R hE hB he hb).flagEvaluator
    (fun c => BinaryNatCode.encode (D c)) hD.bits_mem_FP p
  · intro c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hd c
  · intro c i
    simp only [zeroLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    by_cases hz : (p c).coeff i = 0 <;> simp [hz]

noncomputable def value (p : List Bool → Polynomial (Polynomial ℤ)) (q : List Bool) : List Bool :=
  residueBits ((((p (pairFst (pairFst q))).trailingCoeff).coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))

def query (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (BinaryNat.normalize (pairSnd (pairFst z))) (pairSnd z))
theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP) pairSnd_mem_FP)

theorem evaluator (p : List Bool → Polynomial (Polynomial ℤ)) (R : CertifiedPolynomial.BivariateReader p)
    {D E B : List Bool → ℕ} (hD : BinaryFn D) (hE : BinaryFn E) (hB : BinaryFn B)
    (hd : ∀ c, (p c).natDegree ≤ D c) (he : ∀ c i, ((p c).coeff i).natDegree ≤ E c)
    (hb : ∀ c i j, (((p c).coeff i).coeff j).natAbs.size ≤ B c) : SpaceFunction (value p) := by
  have EI := (index_evaluator p R hD hE hB hd he hb).precompose
    (fun q => pairFst (pairFst q)) (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  refine (EI.withInput.chain (R.evaluator.precompose query query_FP)).congr (funext fun q => ?_)
  change R.coefficient (query (pair q (index p (pairFst (pairFst q))))) = _
  simp only [query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, index]
  change R.coefficient (pair (pairFst q) (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))
    (BinaryNatCode.encode (p (pairFst (pairFst q))).natTrailingDegree))) = _
  rw [R.coefficient_eq]
  rfl

end LeanCanny.Algebra.PolynomialTrailingCoefficientBits
