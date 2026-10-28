/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleJointRows
public import LeanCanny.Algebra.MacaulayIntegerPolynomialSpace

/-! # Native Macaulay matrices for regular child coordinate equations -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointMacaulay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open FixedWidthPolynomial
open BoundedFullSampleBlock
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleJointSource.system
  BoundedFullSampleJointSource.degree BoundedFullSampleJointCoordinate.width

noncomputable def layout (F : Inputs) (pull : List Bool → List Bool) : MacaulayBits.Layout where
  arity u := F.dim (pull u) + 2
  width := BoundedFullSampleJointCoordinate.width F ∘ pull
  degree u i := if i = 0 then 1 else BoundedFullSampleJointSource.degree F (pull u)

theorem layout_binary {F : Inputs} (h : F.PolyTime)
    {pull : List Bool → List Bool} (hpull : pull ∈ FP) : (layout F pull).BinaryPolyTime :=
  ⟨(h.dim.comp hpull).add (UnaryFn.const 2), (BoundedFullSampleJointCoordinate.width_unary h).comp hpull,
    BinaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (BinaryFn.const 1)
      ((BoundedFullSampleJointSource.degree_binary h).comp (mem_FP_comp pairFst_mem_FP hpull))⟩

noncomputable def system (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) :=
  AffineCoordinateSystem.rows (BoundedFullSampleJointSource.system F w bits (pull u) (pivot (pull u)))
    (fun _ => BoundedFullSampleJointSource.degree F (pull u)) (coordinate u)

theorem degrees_eq (F : Inputs) (pull : List Bool → List Bool) (u : List Bool) :
    MacaulayBits.Degrees (layout F pull) u =
      AffineCoordinateSystem.degrees (fun _ : Fin (F.dim (pull u) + 1) => BoundedFullSampleJointSource.degree F (pull u)) := by
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

noncomputable def coefficientData (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) (i r j : ℕ) : ℤ :=
  (((system F w bits pull pivot coordinate u ⟨min i (F.dim (pull u) + 1), by omega⟩).coeff
    (RationalSubstitution.Indexed.exponentVector (F.dim (pull u) + 2)
      (entry (BoundedFullSampleJointCoordinate.width F (pull u)) r))).coeff j)

theorem coefficientData_valid (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (u : List Bool) (i : Fin (F.dim (pull u) + 2)) (r j : ℕ) :
    coefficientData F w bits pull pivot coordinate u i.val r j =
      ((system F w bits pull pivot coordinate u i).coeff
        (RationalSubstitution.Indexed.exponentVector (F.dim (pull u) + 2)
          (entry (BoundedFullSampleJointCoordinate.width F (pull u)) r))).coeff j := by
  unfold coefficientData
  have hi : (⟨min i.val (F.dim (pull u) + 1), by omega⟩ : Fin (F.dim (pull u) + 2)) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ F.dim (pull u) + 1 by have := i.isLt; omega)
  rw [hi]

noncomputable def coefficient (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (q : List Bool) : List Bool :=
  residueBits ((coefficientData F w bits pull pivot coordinate (origin q) (Nat.fromBitsLE (index q))
    (Nat.fromBitsLE (rank q)) (Nat.fromBitsLE (parameter q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem coefficient_evaluator {F : Inputs} (h : F.PolyTime)
    {w : List Bool → ℕ} (hw : UnaryFn w)
    {bits pull : List Bool → List Bool} (EB : SpaceFunction bits) (hpull : pull ∈ FP)
    (pivot : (u : List Bool) → Fin (F.dim u)) (hp : BinaryFn (fun u => (pivot u).val))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (hc : UnaryFn (fun u => (coordinate u).val))
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) :
    SpaceFunction (coefficient F w bits pull pivot coordinate) := by
  have E := BoundedFullSampleJointRows.evaluator h hw EB (mem_FP_comp origin_FP hpull) pivot hp
    (fun q => coordinate (origin q)) (hc.comp origin_FP) (selectedRow (F.dim ∘ pull))
    (selectedRow_unary (h.dim.comp hpull)) parameter_FP modulus_FP htP htS
  have EQ := E.precompose (fun q => pair q (BinaryNat.normalize (rank q)))
    (mem_FP_pair id_mem_FP (mem_FP_comp rank_FP BinaryNat.normalize_mem_FP))
  refine EQ.congr (funext fun q => ?_)
  have H := AffineCoordinateRowsBits.value_packet (fun q => F.dim (pull (origin q)) + 1)
    (BoundedFullSampleJointCoordinate.width F ∘ pull ∘ origin)
    (BoundedFullSampleJointSource.degree F ∘ pull ∘ origin)
    (fun q => BoundedFullSampleJointSource.system F w bits (pull (origin q)) (pivot (pull (origin q))))
    (fun q => coordinate (origin q)) (selectedRow (F.dim ∘ pull)) parameter modulus q (Nat.fromBitsLE (rank q))
  simpa only [Function.comp_def, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, nativeExponent_refl,
    BoundedFullSampleJointRows.value, coefficient, coefficientData, system, selectedRow] using H

theorem coefficient_packet (F : Inputs) (w : List Bool → ℕ)
    (bits pull : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.dim u))
    (coordinate : (u : List Bool) → Fin (F.dim (pull u) + 1)) (z : List Bool)
    (i : Fin (F.dim (pull (pairFst z)) + 2)) (r j : ℕ) :
    coefficient F w bits pull pivot coordinate
      (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j)))) =
        residueBits ((((system F w bits pull pivot coordinate (pairFst z) i).coeff
          (RationalSubstitution.Indexed.exponentVector (F.dim (pull (pairFst z)) + 2)
            (entry (BoundedFullSampleJointCoordinate.width F (pull (pairFst z))) r))).coeff j : ℤ) :
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

end LeanCanny.Encoding.BoundedFullSampleJointMacaulay
