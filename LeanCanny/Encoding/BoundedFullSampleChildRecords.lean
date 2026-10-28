/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildThom
public import LeanCanny.Algebra.FilteredSignProducts
public import LeanCanny.Encoding.SparseFeatureRecords

/-! # Native moments of short regular-child sign records

Candidate records contain twice the label width in factors. A zero slot denotes one;
other slots denote a derivative sign, with large codes clamped to the final
feature. Both the record length and every slot reader have native FP bounds.
Product queries charge the native parameter coefficients and joint-equation and regularity filters.
The evaluator scans all complete blocks, also allowing concatenated records.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildRecords
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedFullSampleChildSource (Inputs)
open Brackets MatrixPower
open scoped Classical BigOperators
attribute [local irreducible] BoundedFullSampleChildCoordinates.parameter
  BoundedFullSampleChildThom.value PrimitivePairBits.coefficient
set_option backward.isDefEq.respectTransparency false

noncomputable def slots (P : Inputs) (c : List Bool) : ℕ := 2 * BoundedFullSampleChildThom.labelWidth P c
noncomputable def width (P : Inputs) (c : List Bool) : ℕ :=
  (BoundedFullSampleChildCoordinates.parameterDegree P c).size + 2
noncomputable def length (P : Inputs) (c : List Bool) : ℕ := slots P c * width P c

theorem slots_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (slots P) :=
  (UnaryFn.const 2).mul (BoundedFullSampleChildThom.labelWidth_unary h)
theorem width_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (width P) := by
  have hs : UnaryFn (fun c => (BoundedFullSampleChildCoordinates.parameterDegree P c).size) :=
    (UnaryFn.length (BoundedFullSampleChildCoordinates.parameterDegree_binary h).bits_mem_FP).of_eq
      (fun c => BinaryNatCode.length_encode _)
  exact hs.add (UnaryFn.const 2)
theorem length_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (length P) := (slots_unary h).mul (width_unary h)

noncomputable def recordSlots (P : Inputs) (z : List Bool) : ℕ := (pairSnd z).length / width P (pairFst z)
theorem recordSlots_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (recordSlots P) :=
  (UnaryFn.length pairSnd_mem_FP).div ((width_unary h).comp pairFst_mem_FP)
theorem width_pos (P : Inputs) (c : List Bool) : 0 < width P c := by unfold width; omega
theorem recordSlots_packet (P : Inputs) (c r : List Bool) (hr : r.length = length P c) :
    recordSlots P (pair c r) = slots P c := by
  simp only [recordSlots, pairFst_pair, pairSnd_pair, hr, length]
  exact Nat.mul_div_cancel _ (width_pos P c)

noncomputable def slot (P : Inputs) (z : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (recordSlots P) (width P ∘ pairFst) pairSnd z i
noncomputable def read (P : Inputs) : List Bool → List Bool :=
  FixedWidthQuery.read (recordSlots P) (width P ∘ pairFst) pairSnd

theorem read_FP {P : Inputs} (h : P.PolyTime) : read P ∈ FP :=
  FixedWidthQuery.read_mem_FP (recordSlots_unary h)
    ((width_unary h).comp pairFst_mem_FP) pairSnd_mem_FP
theorem read_packet (P : Inputs) (z : List Bool) (i : ℕ) :
    read P (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (slot P z i) :=
  FixedWidthQuery.read_packet _ _ _ z i

noncomputable def order (P : Inputs) (z : List Bool) (i : ℕ) : ℕ :=
  min (slot P z i - 1) (BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z))
noncomputable def orderRead (P : Inputs) (t : List Bool) : List Bool :=
  BinaryNatCode.encode (min (Nat.fromBitsLE (read P t) - 1)
    (BoundedFullSampleChildCoordinates.parameterDegree P (pairFst (pairFst t))))

theorem orderRead_FP {P : Inputs} (h : P.PolyTime) : orderRead P ∈ FP := by
  have hx := (BinaryFn.fromBits (read_FP h)).sub (BinaryFn.const 1)
  have hd := (BoundedFullSampleChildCoordinates.parameterDegree_binary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hi := BinaryFn.ite (hx.le hd) hx hd
  have hm : BinaryFn (fun t => min (Nat.fromBitsLE (read P t) - 1)
      (BoundedFullSampleChildCoordinates.parameterDegree P (pairFst (pairFst t)))) :=
    BinaryFn.of_eq hi (fun _ => by simp only [min_def, Function.comp_apply])
  exact hm.bits_mem_FP

theorem orderRead_packet (P : Inputs) (z : List Bool) (i : ℕ) :
    orderRead P (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (order P z i) := by
  rw [orderRead, read_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair, order]

noncomputable def polynomial (P : Inputs) (z : List Bool) (i : ℕ) : Polynomial ℤ :=
  if slot P z i = 0 then 1 else BoundedFullSampleChildThom.polynomial P (pairFst z) (order P z i)

noncomputable def filter (P : Inputs) : SignPatternBits.Family :=
  (BoundedFullSampleChildEquationCount.family P).comp pairFst

noncomputable def family (P : Inputs) : SignPatternBits.Family :=
  { filter P with
    polynomial := polynomial P
    pattern := fun _ _ => 0
    count := fun z => BinaryNatCode.encode (recordSlots P z)
    degree := fun z => BinaryNatCode.encode (BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z))
    mass := fun z => BinaryNatCode.encode (BoundedFullSampleChildThom.massExponent P (pairFst z))
    polynomial_degree := fun z _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      unfold polynomial
      split_ifs
      · simp only [Polynomial.natDegree_one]; exact Nat.zero_le _
      · exact BoundedFullSampleChildThom.degree P (pairFst z) _
    polynomial_mass := fun z _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      unfold polynomial
      split_ifs
      · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
          (Nat.one_le_pow (BoundedFullSampleChildThom.massExponent P (pairFst z)) 2 (by decide))
      · exact BoundedFullSampleChildThom.mass_bound P (pairFst z) _ }

attribute [local irreducible] BoundedFullSampleChildCoordinates.parameterDegree
  BoundedFullSampleChildCoordinates.baseHeight BoundedFullSampleChildThom.massExponent

theorem filter_controls {P : Inputs} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (filter P) :=
  SignPatternBits.comp_controls (BoundedFullSampleChildEquationCount.controls h) pairFst_mem_FP

theorem controls {P : Inputs} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (family P) := by
  have hd : BinaryFn (fun z => BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z)) :=
    (BoundedFullSampleChildCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (fun z => BoundedFullSampleChildThom.massExponent P (pairFst z)) :=
    (BoundedFullSampleChildThom.massExponent_binary h).comp pairFst_mem_FP
  refine ⟨bits_mem_FP (recordSlots_unary h), ?_, (filter_controls h).rootDegree,
    hd.bits_mem_FP, (filter_controls h).rootMass, hm.bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using recordSlots_unary h

def slotQuery (q : List Bool) : List Bool := pair (BoundedFullSampleChildThom.original q) (BoundedFullSampleChildThom.order q)
theorem slotQuery_FP : slotQuery ∈ FP := mem_FP_pair BoundedFullSampleChildThom.original_FP BoundedFullSampleChildThom.order_FP

noncomputable def derivativeQuery (P : Inputs) (q : List Bool) : List Bool :=
  pair (pair (pairFst (BoundedFullSampleChildThom.original q))
    (pair (orderRead P (slotQuery q)) (BoundedFullSampleChildThom.index q))) (pairSnd q)
theorem derivativeQuery_FP {P : Inputs} (h : P.PolyTime) : derivativeQuery P ∈ FP := by
  have H := mem_FP_pair (mem_FP_pair (mem_FP_comp BoundedFullSampleChildThom.original_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp slotQuery_FP (orderRead_FP h)) BoundedFullSampleChildThom.index_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [derivativeQuery, Function.comp_apply])

def unitQuery (q : List Bool) : List Bool := pair q (pair [] (BoundedFullSampleChildThom.index q))
theorem unitQuery_FP : unitQuery ∈ FP := mem_FP_pair id_mem_FP (mem_FP_pair (constFn_mem_FP []) BoundedFullSampleChildThom.index_FP)
def unit : List Bool → List Bool := RootSignQueries.unitCoefficient pairSnd ∘ unitQuery
theorem unit_FP : unit ∈ FP := mem_FP_comp unitQuery_FP (RootSignQueries.unitCoefficient_mem_FP pairSnd_mem_FP)

theorem unit_value (q : List Bool) (k : ℕ) (hi : BoundedFullSampleChildThom.index q = BinaryNatCode.encode k) :
    unit q = residueBits ((((1 : Polynomial ℤ).coeff k : ℤ)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  unfold unit unitQuery
  simp only [Function.comp_apply]
  rw [hi]
  have hu := RootSignQueries.unitCoefficient_packet pairSnd q 0 k
  apply hu.trans
  by_cases hk : k = 0 <;> simp [Polynomial.coeff_one, hk]

theorem unit_packet (z : List Bool) (i k : ℕ) (m : List Bool) :
    unit (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m) =
      residueBits ((((1 : Polynomial ℤ).coeff k : ℤ)) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hq : pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m = q
  have hi : BoundedFullSampleChildThom.index q = BinaryNatCode.encode k := by
    rw [BoundedFullSampleChildThom.index, ← hq, pairFst_pair, pairSnd_pair, pairSnd_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst m
  exact unit_value q k hi

noncomputable def coefficient (P : Inputs) (q : List Bool) : List Bool :=
  if read P (slotQuery q) = [] then unit q else BoundedFullSampleChildThom.value P (derivativeQuery P q)

theorem coefficient_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (coefficient P) := by
  have hp := stringEq_fppred (mem_FP_comp slotQuery_FP (read_FP h)) (constFn_mem_FP [])
  have E := SpaceFunction.branch _ hp.flag_mem_FP (SpaceFunction.ofFP _ unit_FP)
    ((BoundedFullSampleChildThom.evaluator h).precompose (derivativeQuery P) (derivativeQuery_FP h))
  exact E.congr (funext fun _ => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

theorem coefficient_packet (P : Inputs) (z : List Bool) (i k : ℕ) (m : List Bool) :
    coefficient P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m) =
      residueBits (((polynomial P z i).coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  have hslot : slotQuery (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m) =
      pair z (BinaryNatCode.encode i) := by
    simp only [slotQuery, BoundedFullSampleChildThom.original, BoundedFullSampleChildThom.order, pairFst_pair, pairSnd_pair]
  unfold coefficient
  rw [hslot, read_packet]
  by_cases hz : slot P z i = 0
  · rw [ite_eq_left (by rw [hz]; rfl), polynomial, ite_eq_left hz]
    exact unit_packet z i k m
  · have hne : BinaryNatCode.encode (slot P z i) ≠ [] := by
      intro he
      apply hz
      have he' := congrArg Nat.fromBitsLE he
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [] = 0 from rfl] using he'
    rw [ite_eq_right hne, polynomial, ite_eq_right hz]
    simp only [derivativeQuery, hslot, orderRead_packet, BoundedFullSampleChildThom.original,
      BoundedFullSampleChildThom.index, pairFst_pair, pairSnd_pair]
    exact BoundedFullSampleChildThom.value_packet P (pairFst z) (order P z i) k m

noncomputable def filterAccess (P : Inputs) : SignPatternBits.Access (filter P) :=
  (BoundedFullSampleChildEquationCount.access P).comp pairFst

noncomputable def access (P : Inputs) : SignPatternBits.Access (family P) where
  rootCoefficient := (filterAccess P).rootCoefficient
  polynomialCoefficient := coefficient P
  pattern _ := []
  root_eq := (filterAccess P).root_eq
  polynomial_eq z i _ k m hm := by
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact coefficient_packet P z i k w
  pattern_eq _ _ := rfl

noncomputable def moment (P : Inputs) (z : List Bool) : ℤ :=
  BoundedFullSampleChildReindexedQueries.moment P pairFst (family P) z

theorem moment_bound (P : Inputs) (z : List Bool) :
    (moment P z).natAbs ≤ 2 ^ BoundedFullSampleChildThom.labelWidth P (pairFst z) :=
  (BoundedFullSampleChildReindexedQueries.moment_bound P pairFst (family P) z).trans
    (BoundedFullSampleChildRegularCount.count_le P (pairFst z))

attribute [local irreducible] coefficient

theorem evaluator {P : Inputs} (h : P.PolyTime) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (moment P z)) :=
  BoundedFullSampleChildReindexedQueries.evaluator h pairFst_mem_FP (access P) (controls h) (coefficient_evaluator h)

end LeanCanny.Encoding.BoundedFullSampleChildRecords
