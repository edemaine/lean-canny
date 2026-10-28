/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointRows
public import LeanCanny.Algebra.MacaulayIntegerPolynomialSpace

/-! # Native Macaulay matrices for regular child coordinate equations -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointMacaulay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open FixedWidthPolynomial
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleJointSource.system
  BoundedCriticalSampleJointSource.degree BoundedCriticalSampleJointCoordinate.width

noncomputable def layout (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) : MacaulayBits.Layout where
  arity u := k u + 2
  width := BoundedCriticalSampleJointCoordinate.width P read k
  degree u i := if i = 0 then 1 else BoundedCriticalSampleJointSource.degree P read u

theorem layout_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : (layout P read k).BinaryPolyTime :=
  ⟨hk.add (UnaryFn.const 2), BoundedCriticalSampleJointCoordinate.width_unary h read hr hk,
    BinaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (BinaryFn.const 1)
      ((BoundedCriticalSampleJointSource.degree_binary h read hr).comp pairFst_mem_FP)⟩

noncomputable def system (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) :=
  AffineCoordinateSystem.rows (BoundedCriticalSampleJointSource.system P read o k w bits u (pivot u))
    (fun _ => BoundedCriticalSampleJointSource.degree P read u) (coordinate u)

theorem degrees_eq (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) :
    MacaulayBits.Degrees (layout P read k) u =
      AffineCoordinateSystem.degrees (fun _ : Fin (k u + 1) => BoundedCriticalSampleJointSource.degree P read u) := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> simp [MacaulayBits.Degrees, layout, AffineCoordinateSystem.degrees]

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def index (q : List Bool) : List Bool := pairFst (pairSnd q)
def rank (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def parameter (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rank_FP : rank ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem parameter_FP : parameter ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def selectedRow (k : List Bool → ℕ) (q : List Bool) : Fin (k (origin q) + 2) :=
  ⟨min (Nat.fromBitsLE (index q)) (k (origin q) + 1), by omega⟩
theorem selectedRow_unary {k : List Bool → ℕ} (hk : UnaryFn k) : UnaryFn (fun q => (selectedRow k q).val) :=
  UnaryFn.fromBitsLE_min index_FP ((hk.comp origin_FP).add (UnaryFn.const 1))

noncomputable def coefficientData (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) (i r j : ℕ) : ℤ :=
  (((system P read o k w bits pivot coordinate u ⟨min i (k u + 1), by omega⟩).coeff
    (RationalSubstitution.Indexed.exponentVector (k u + 2)
      (entry (BoundedCriticalSampleJointCoordinate.width P read k u) r))).coeff j)

theorem coefficientData_valid (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (u : List Bool) (i : Fin (k u + 2)) (r j : ℕ) :
    coefficientData P read o k w bits pivot coordinate u i.val r j =
      ((system P read o k w bits pivot coordinate u i).coeff
        (RationalSubstitution.Indexed.exponentVector (k u + 2)
          (entry (BoundedCriticalSampleJointCoordinate.width P read k u) r))).coeff j := by
  unfold coefficientData
  have hi : (⟨min i.val (k u + 1), by omega⟩ : Fin (k u + 2)) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ k u + 1 by have := i.isLt; omega)
  rw [hi]

noncomputable def coefficient (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (q : List Bool) : List Bool :=
  residueBits ((coefficientData P read o k w bits pivot coordinate (origin q) (Nat.fromBitsLE (index q))
    (Nat.fromBitsLE (rank q)) (Nat.fromBitsLE (parameter q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (pivot : (u : List Bool) → Fin (k u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (coefficient P read o k w bits pivot coordinate) := by
  have E := BoundedCriticalSampleJointRows.evaluator h read hr ho hk hw hbits origin_FP pivot hp
    (fun q => coordinate (origin q)) (hc.comp origin_FP) (selectedRow k) (selectedRow_unary hk) parameter_FP modulus_FP ha
  have EQ := E.precompose (fun q => pair q (BinaryNat.normalize (rank q)))
    (mem_FP_pair id_mem_FP (mem_FP_comp rank_FP BinaryNat.normalize_mem_FP))
  refine EQ.congr (funext fun q => ?_)
  have H := AffineCoordinateRowsBits.value_packet (fun q => k (origin q) + 1)
    (BoundedCriticalSampleJointCoordinate.width P read k ∘ origin)
    (BoundedCriticalSampleJointSource.degree P read ∘ origin)
    (fun q => BoundedCriticalSampleJointSource.system P read o k w bits (origin q) (pivot (origin q)))
    (fun q => coordinate (origin q)) (selectedRow k) parameter modulus q (Nat.fromBitsLE (rank q))
  simpa only [Function.comp_apply, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, nativeExponent_refl,
    BoundedCriticalSampleJointRows.value, coefficient, coefficientData, system, selectedRow] using H

theorem coefficient_packet (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (pivot : (u : List Bool) → Fin (k u))
    (coordinate : (u : List Bool) → Fin (k u + 1)) (z : List Bool)
    (i : Fin (k (pairFst z) + 2)) (r j : ℕ) :
    coefficient P read o k w bits pivot coordinate
      (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j)))) =
        residueBits ((((system P read o k w bits pivot coordinate (pairFst z) i).coeff
          (RationalSubstitution.Indexed.exponentVector (k (pairFst z) + 2)
            (entry (BoundedCriticalSampleJointCoordinate.width P read k (pairFst z)) r))).coeff j : ℤ) :
              ZMod (Nat.fromBitsLE (pairSnd z) + 1)) := by
  generalize hq : pair z (pair (BinaryNatCode.encode i.val)
    (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j))) = q
  have hm : pairSnd z = modulus q := by rw [← hq]; simp only [modulus, pairFst_pair]
  have hu : origin q = pairFst z := by rw [← hq]; simp only [origin, pairFst_pair]
  have hi : Nat.fromBitsLE (index q) = i.val := by
    rw [← hq]; simp only [index, pairSnd_pair, pairFst_pair, MacaulayBits.fromBits_encode]
  have hr : Nat.fromBitsLE (rank q) = r := by
    rw [← hq]; simp only [rank, pairSnd_pair, pairFst_pair, MacaulayBits.fromBits_encode]
  have hj : Nat.fromBitsLE (parameter q) = j := by
    rw [← hq]; simp only [parameter, pairSnd_pair, MacaulayBits.fromBits_encode]
  rw [hm, coefficient, hu, hi, hr, hj, coefficientData_valid]

end LeanCanny.Encoding.BoundedCriticalSampleJointMacaulay
