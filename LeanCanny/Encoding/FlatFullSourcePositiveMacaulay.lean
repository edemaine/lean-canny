/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositiveRows
public import LeanCanny.Encoding.FlatFullSourcePositiveCoordinate
public import LeanCanny.Algebra.MacaulayIntegerPolynomialSpace

/-! # Native Macaulay matrices for complete flat coordinate equations -/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveMacaulay
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MatrixPower
open FixedWidthPolynomial
open FlatFullSourceTower (Inputs)
open FlatFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourcePositive.system
  FlatFullSourceTower.degree FlatFullSourcePositiveCoordinate.width

noncomputable def layout (F : Inputs) : MacaulayBits.Layout where
  arity u := count F u + 1
  width := FlatFullSourcePositiveCoordinate.width F
  degree u i := if i = 0 then 1 else FlatFullSourceTower.degree F u

theorem layout_binary {F : Inputs} (h : F.Access) : (layout F).BinaryPolyTime :=
  ⟨(FlatFullSourcePositive.count_unary h).add (UnaryFn.const 1), FlatFullSourcePositiveCoordinate.width_unary h,
    BinaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (BinaryFn.const 1)
      ((FlatFullSourceTower.degree_binary h).comp pairFst_mem_FP)⟩

noncomputable def system (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u)) (u : List Bool) :=
  AffineCoordinateSystem.rows (FlatFullSourcePositive.system F u)
    (fun _ => FlatFullSourceTower.degree F u) (coordinate u)

theorem degrees_eq (F : Inputs) (u : List Bool) :
    MacaulayBits.Degrees (layout F) u =
      AffineCoordinateSystem.degrees (fun _ : Fin (count F u) => FlatFullSourceTower.degree F u) := by
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

def selectedRow (F : Inputs) (q : List Bool) : Fin (count F (origin q) + 1) :=
  ⟨min (Nat.fromBitsLE (index q)) (count F (origin q)), by omega⟩
theorem selectedRow_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (selectedRow F q).val) :=
  UnaryFn.fromBitsLE_min index_FP ((FlatFullSourcePositive.count_unary h).comp origin_FP)

noncomputable def coefficientData (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i r j : ℕ) : ℤ :=
  (((system F coordinate u ⟨min i (count F u), by omega⟩).coeff
    (RationalSubstitution.Indexed.exponentVector (count F u + 1)
      (entry (FlatFullSourcePositiveCoordinate.width F u) r))).coeff j)

theorem coefficientData_valid (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u + 1)) (r j : ℕ) :
    coefficientData F coordinate u i.val r j =
      ((system F coordinate u i).coeff
        (RationalSubstitution.Indexed.exponentVector (count F u + 1)
          (entry (FlatFullSourcePositiveCoordinate.width F u) r))).coeff j := by
  unfold coefficientData
  have hi : (⟨min i.val (count F u), by omega⟩ : Fin (count F u + 1)) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ count F u by have := i.isLt; omega)
  rw [hi]

noncomputable def coefficient (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u))
    (q : List Bool) : List Bool :=
  residueBits ((coefficientData F coordinate (origin q) (Nat.fromBitsLE (index q))
    (Nat.fromBitsLE (rank q)) (Nat.fromBitsLE (parameter q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem coefficient_evaluator {F : Inputs} (h : F.Access)
    (coordinate : (u : List Bool) → Fin (count F u)) (hc : UnaryFn (fun u => (coordinate u).val)) :
    SpaceFunction (coefficient F coordinate) := by
  have E0 := FlatFullSourcePositiveRows.evaluator (FlatFullSourceContext.access h origin_FP)
    ((FlatFullSourcePositiveCoordinate.width_unary h).comp origin_FP)
    (fun q => by rw [FlatFullSourceContext.degree_comp]; exact FlatFullSourcePositiveCoordinate.degree_lt_width F (origin q))
    (fun q => FlatFullSourcePositiveCoordinate.width_pos F (origin q))
    (fun q => coordinate (origin q)) (hc.comp origin_FP) (selectedRow F) (selectedRow_unary h) parameter_FP modulus_FP
  have E : SpaceFunction (AffineCoordinateRowsBits.value (count F ∘ origin)
      (FlatFullSourcePositiveCoordinate.width F ∘ origin) (FlatFullSourceTower.degree F ∘ origin)
      (fun q => FlatFullSourcePositive.system F (origin q))
      (fun q => coordinate (origin q)) (selectedRow F) parameter modulus) := by
    refine E0.congr (funext fun q => ?_)
    unfold AffineCoordinateRowsBits.value
    have hs : FlatFullSourcePositive.system (FlatFullSourceContext.comp F origin) (pairFst q) =
        FlatFullSourcePositive.system F (origin (pairFst q)) :=
      funext (FlatFullSourcePositiveRows.system_comp F origin (pairFst q))
    rw [hs, FlatFullSourceContext.degree_comp]
    dsimp only [Function.comp_def, FlatFullSourcePositive.count, FlatFullSourceTower.count, FlatFullSourceTower.arity,
      FlatFullSourceContext.comp, BoundedFullWriter.Readers.comp]
  have EQ := E.precompose (fun q => pair q (BinaryNat.normalize (rank q)))
    (mem_FP_pair id_mem_FP (mem_FP_comp rank_FP BinaryNat.normalize_mem_FP))
  refine EQ.congr (funext fun q => ?_)
  have H := AffineCoordinateRowsBits.value_packet (count F ∘ origin)
    (FlatFullSourcePositiveCoordinate.width F ∘ origin) (FlatFullSourceTower.degree F ∘ origin)
    (fun q => FlatFullSourcePositive.system F (origin q))
    (fun q => coordinate (origin q)) (selectedRow F) parameter modulus q (Nat.fromBitsLE (rank q))
  simpa only [Function.comp_def, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, nativeExponent_refl,
    coefficient, coefficientData, system, selectedRow] using H

theorem coefficient_packet (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u)) (z : List Bool)
    (i : Fin (count F (pairFst z) + 1)) (r j : ℕ) :
    coefficient F coordinate
      (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j)))) =
        residueBits ((((system F coordinate (pairFst z) i).coeff
          (RationalSubstitution.Indexed.exponentVector (count F (pairFst z) + 1)
            (entry (FlatFullSourcePositiveCoordinate.width F (pairFst z)) r))).coeff j : ℤ) :
              ZMod (Nat.fromBitsLE (pairSnd z) + 1)) := by
  generalize hq : pair z (pair (BinaryNatCode.encode i.val)
    (pair (BinaryNatCode.encode r) (BinaryNatCode.encode j))) = q
  have hm : pairSnd z = modulus q := by rw [← hq]; simp only [modulus, pairFst_pair]
  have hu : origin q = pairFst z := by rw [← hq]; simp only [origin, pairFst_pair]
  have hi : Nat.fromBitsLE (index q) = i.val := by
    rw [← hq]; simp only [index, pairSnd_pair, pairFst_pair, MacaulayBits.fromBits_encode]
  have hr : Nat.fromBitsLE (rank q) = r := by
    rw [← hq]; simp only [rank, pairSnd_pair, pairSnd_pair, pairFst_pair, MacaulayBits.fromBits_encode]
  have hj : Nat.fromBitsLE (parameter q) = j := by
    rw [← hq]; simp only [parameter, pairSnd_pair, MacaulayBits.fromBits_encode]
  rw [hm, coefficient, hu, hi, hr, hj, coefficientData_valid]

end LeanCanny.Encoding.FlatFullSourcePositiveMacaulay
