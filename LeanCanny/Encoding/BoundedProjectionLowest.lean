/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionCharacteristic
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Algebra.LowestCoefficientSpace

/-! # Native selection of the first nonzero projection characteristic coefficient

Both the retained-variable scan and the integer residue scan use binary bounds.
The selected directions and separating weights are charged by the underlying
certified determinant reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionLowest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets BoundedProjectionMacaulay
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedProjectionCharacteristic.polynomial

def base (q : List Bool) : List Bool := pairFst (pairFst q)
def outer (q : List Bool) : List Bool := pairSnd (pairFst q)
def inner (q : List Bool) : List Bool := pairSnd q

theorem base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem outer_FP : outer ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def scalar (P : Readers) (q : List Bool) : ℤ :=
  ((BoundedProjectionCharacteristic.polynomial P (base q)).coeff
    (Nat.fromBitsLE (outer q))).coeff (Nat.fromBitsLE (inner q))

/-- Reorder a scalar/modulus packet for the certified bivariate reader. -/
def residueQuery (q : List Bool) : List Bool :=
  pair (pair (base (pairFst q)) (pairSnd q))
    (pair (BinaryNat.normalize (inner (pairFst q))) (BinaryNat.normalize (outer (pairFst q))))

theorem residueQuery_FP : residueQuery ∈ FP := by
  have hb := mem_FP_comp pairFst_mem_FP base_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP outer_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hb pairSnd_mem_FP) (mem_FP_pair hi ho)

theorem scalarZeroDecider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider {q | scalar P q = 0} := by
  let R := BoundedProjectionCharacteristic.reader h ha
  have hb : BinaryFn (fun q => BoundedCriticalProjection.coefficientBits P (base q)) :=
    (BoundedCriticalProjection.coefficientBits_binary h).comp base_FP
  apply IntegerZeroBits.zeroDecider (R.evaluator.precompose residueQuery residueQuery_FP)
    (fun q => BinaryNatCode.encode (BoundedCriticalProjection.coefficientBits P (base q)))
    hb.bits_mem_FP (scalar P)
  · intro q
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionCharacteristic.coefficient_bits P (base q) _ _
  · intro q m hm
    change R.coefficient (residueQuery (pair q (BinaryNatCode.encode (m - 1)))) = _
    simp only [residueQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    change R.coefficient (pair (pair (base q) (BinaryNatCode.encode (m - 1)))
      (pair (BinaryNatCode.encode (Nat.fromBitsLE (inner q)))
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

def zeroLanguage (P : Readers) : Language :=
  {q | (BoundedProjectionCharacteristic.polynomial P (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0}

theorem zeroLanguage_eq_scan (P : Readers) :
    zeroLanguage P = BoundedScan.language {q | scalar P q = 0}
      (fun q => dimension P (pairFst q) + 1) := by
  ext q
  change _ = 0 ↔ ∀ i < dimension P (pairFst q) + 1,
    scalar P (pair q (BinaryNatCode.encode i)) = 0
  simp only [scalar, base, inner, outer, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · intro hz i _
    rw [hz, Polynomial.coeff_zero]
  · intro hz
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < dimension P (pairFst q) + 1
    · exact hz i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
        have := BoundedProjectionCharacteristic.coefficient_degree P (pairFst q)
          (Nat.fromBitsLE (pairSnd q))
        omega)

theorem zeroDecider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (zeroLanguage P) := by
  have hn0 : BinaryFn (fun q => dimension P (pairFst q)) := (dimension_binary h).comp pairFst_mem_FP
  have hn := hn0.add (BinaryFn.const 1)
  have D := BoundedScan.decider (scalarZeroDecider h ha)
    (fun q => BinaryNatCode.encode (dimension P (pairFst q) + 1)) hn.bits_mem_FP
    (fun q => dimension P (pairFst q) + 1) (fun _ => rfl)
  exact D.congr (zeroLanguage_eq_scan P).symm

noncomputable def index (P : Readers) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (BoundedProjectionCharacteristic.polynomial P c).natTrailingDegree

theorem index_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (index P) := by
  apply LowestCoefficientBits.evaluator (zeroDecider h ha).flagEvaluator
    (fun c => BinaryNatCode.encode (dimension P c)) (dimension_binary h).bits_mem_FP
    (BoundedProjectionCharacteristic.polynomial P)
  · intro c
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedProjectionCharacteristic.degree P c).le
  · intro c i
    simp only [zeroLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    by_cases hz : (BoundedProjectionCharacteristic.polynomial P c).coeff i = 0 <;> simp [hz]

end LeanCanny.Encoding.BoundedProjectionLowest
