/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionMoments
public import LeanCanny.Encoding.SparseFeatureRecords

/-! # Native moments of fixed-width projection-sign records

Candidate records contain twice the label width in factors. A zero slot denotes one;
other slots denote a derivative sign, with large codes clamped to the final
feature. Both the record length and every slot reader have native FP bounds.
Product queries charge the actual projection coefficient and record searches.
The evaluator scans all complete blocks, also allowing concatenated records.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRecords
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical BigOperators
attribute [local irreducible] BoundedCriticalProjection.polynomial
attribute [local irreducible] BoundedProjectionThom.value BoundedProjectionRootCount.coefficient

noncomputable def slots (P : Readers) (c : List Bool) : ℕ := 2 * BoundedCriticalProjection.labelWidth P c
noncomputable def width (P : Readers) (c : List Bool) : ℕ := BoundedCriticalProjection.labelWidth P c + 2
noncomputable def length (P : Readers) (c : List Bool) : ℕ := slots P c * width P c

theorem slots_unary {P : Readers} (h : P.PolyTime) : UnaryFn (slots P) :=
  (UnaryFn.const 2).mul (BoundedCriticalProjection.labelWidth_unary h)
theorem width_unary {P : Readers} (h : P.PolyTime) : UnaryFn (width P) :=
  (BoundedCriticalProjection.labelWidth_unary h).add (UnaryFn.const 2)
theorem length_unary {P : Readers} (h : P.PolyTime) : UnaryFn (length P) := (slots_unary h).mul (width_unary h)

noncomputable def recordSlots (P : Readers) (z : List Bool) : ℕ := (pairSnd z).length / width P (pairFst z)
theorem recordSlots_unary {P : Readers} (h : P.PolyTime) : UnaryFn (recordSlots P) :=
  (UnaryFn.length pairSnd_mem_FP).div ((width_unary h).comp pairFst_mem_FP)
theorem width_pos (P : Readers) (c : List Bool) : 0 < width P c := by unfold width; omega
theorem recordSlots_packet (P : Readers) (c r : List Bool) (hr : r.length = length P c) :
    recordSlots P (pair c r) = slots P c := by
  simp only [recordSlots, pairFst_pair, pairSnd_pair, hr, length]
  exact Nat.mul_div_cancel _ (width_pos P c)

noncomputable def slot (P : Readers) (z : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (recordSlots P) (width P ∘ pairFst) pairSnd z i
noncomputable def read (P : Readers) : List Bool → List Bool :=
  FixedWidthQuery.read (recordSlots P) (width P ∘ pairFst) pairSnd

theorem read_FP {P : Readers} (h : P.PolyTime) : read P ∈ FP :=
  FixedWidthQuery.read_mem_FP (recordSlots_unary h)
    ((width_unary h).comp pairFst_mem_FP) pairSnd_mem_FP
theorem read_packet (P : Readers) (z : List Bool) (i : ℕ) :
    read P (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (slot P z i) :=
  FixedWidthQuery.read_packet _ _ _ z i

noncomputable def order (P : Readers) (z : List Bool) (i : ℕ) : ℕ :=
  min (slot P z i - 1) (BoundedProjectionRootCount.degree P (pairFst z))
noncomputable def orderRead (P : Readers) (t : List Bool) : List Bool :=
  BinaryNatCode.encode (min (Nat.fromBitsLE (read P t) - 1)
    (BoundedProjectionRootCount.degree P (pairFst (pairFst t))))

theorem orderRead_FP {P : Readers} (h : P.PolyTime) : orderRead P ∈ FP := by
  have hx := (BinaryFn.fromBits (read_FP h)).sub (BinaryFn.const 1)
  have hd := (BoundedProjectionRootCount.degree_binary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hi := BinaryFn.ite (hx.le hd) hx hd
  have hm : BinaryFn (fun t => min (Nat.fromBitsLE (read P t) - 1)
      (BoundedProjectionRootCount.degree P (pairFst (pairFst t)))) :=
    BinaryFn.of_eq hi (fun _ => by simp only [min_def, Function.comp_apply])
  exact hm.bits_mem_FP

theorem orderRead_packet (P : Readers) (z : List Bool) (i : ℕ) :
    orderRead P (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (order P z i) := by
  rw [orderRead, read_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair, order]

noncomputable def polynomial (P : Readers) (z : List Bool) (i : ℕ) : Polynomial ℤ :=
  if slot P z i = 0 then 1 else BoundedProjectionThom.polynomial P (pairFst z) (order P z i)

noncomputable def family (P : Readers) : SignQueryBits.Family where
  root z := BoundedCriticalProjection.polynomial P (pairFst z)
  polynomial := polynomial P
  exponent _ _ := 1
  count z := BinaryNatCode.encode (recordSlots P z)
  rootDegree z := BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z))
  degree z := BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z))
  rootMass z := BinaryNatCode.encode (BoundedProjectionRootCount.massExponent P (pairFst z))
  mass z := BinaryNatCode.encode (BoundedProjectionThom.massExponent P (pairFst z))
  rootDegree_pos z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact pow_pos (by decide) _
  root_degree z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedCriticalProjection.polynomial_degree P (pairFst z)
  root_mass z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionRootCount.mass_bound P (pairFst z)
  polynomial_degree z i _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold polynomial
    split_ifs
    · simp only [Polynomial.natDegree_one]; exact Nat.zero_le _
    · exact BoundedProjectionThom.degree P (pairFst z) _
  polynomial_mass z i _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold polynomial
    split_ifs
    · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
        (Nat.one_le_pow (BoundedProjectionThom.massExponent P (pairFst z)) 2 (by decide))
    · exact BoundedProjectionThom.mass_bound P (pairFst z) _

attribute [local irreducible] BoundedProjectionRootCount.degree BoundedProjectionRootCount.massExponent
  BoundedProjectionThom.massExponent

theorem controls {P : Readers} (h : P.PolyTime) : SignQueryBits.ControlsPolyTime (family P) := by
  have hC := bits_mem_FP (recordSlots_unary h)
  have hD := BinaryFn.bits_mem_FP ((BoundedProjectionRootCount.degree_binary h).comp pairFst_mem_FP)
  have hR := BinaryFn.bits_mem_FP ((BoundedProjectionRootCount.massExponent_binary h).comp pairFst_mem_FP)
  have hB := BinaryFn.bits_mem_FP ((BoundedProjectionThom.massExponent_binary h).comp pairFst_mem_FP)
  constructor
  · change (fun z => BinaryNatCode.encode (recordSlots P z)) ∈ FP
    exact hC
  · change (fun z => BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z))) ∈ FP
    exact hD
  · change (fun z => BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z))) ∈ FP
    exact hD
  · change (fun z => BinaryNatCode.encode (BoundedProjectionRootCount.massExponent P (pairFst z))) ∈ FP
    exact hR
  · change (fun z => BinaryNatCode.encode (BoundedProjectionThom.massExponent P (pairFst z))) ∈ FP
    exact hB

def slotQuery (q : List Bool) : List Bool := pair (BoundedProjectionThom.original q) (BoundedProjectionThom.order q)
theorem slotQuery_FP : slotQuery ∈ FP := mem_FP_pair BoundedProjectionThom.original_FP BoundedProjectionThom.order_FP

noncomputable def derivativeQuery (P : Readers) (q : List Bool) : List Bool :=
  pair (pair (pairFst (BoundedProjectionThom.original q))
    (pair (orderRead P (slotQuery q)) (BoundedProjectionThom.index q))) (pairSnd q)
theorem derivativeQuery_FP {P : Readers} (h : P.PolyTime) : derivativeQuery P ∈ FP := by
  have H := mem_FP_pair (mem_FP_pair (mem_FP_comp BoundedProjectionThom.original_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp slotQuery_FP (orderRead_FP h)) BoundedProjectionThom.index_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [derivativeQuery, Function.comp_apply])

def unitQuery (q : List Bool) : List Bool := pair q (pair [] (BoundedProjectionThom.index q))
theorem unitQuery_FP : unitQuery ∈ FP := mem_FP_pair id_mem_FP (mem_FP_pair (constFn_mem_FP []) BoundedProjectionThom.index_FP)
def unit : List Bool → List Bool := RootSignQueries.unitCoefficient pairSnd ∘ unitQuery
theorem unit_FP : unit ∈ FP := mem_FP_comp unitQuery_FP (RootSignQueries.unitCoefficient_mem_FP pairSnd_mem_FP)

theorem unit_value (q : List Bool) (k : ℕ) (hi : BoundedProjectionThom.index q = BinaryNatCode.encode k) :
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
  have hi : BoundedProjectionThom.index q = BinaryNatCode.encode k := by
    rw [BoundedProjectionThom.index, ← hq, pairFst_pair, pairSnd_pair, pairSnd_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst m
  exact unit_value q k hi

noncomputable def coefficient (P : Readers) (q : List Bool) : List Bool :=
  if read P (slotQuery q) = [] then unit q else BoundedProjectionThom.value P (derivativeQuery P q)

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P) := by
  have hp := stringEq_fppred (mem_FP_comp slotQuery_FP (read_FP h)) (constFn_mem_FP [])
  have E := SpaceFunction.branch _ hp.flag_mem_FP (SpaceFunction.ofFP _ unit_FP)
    ((BoundedProjectionThom.evaluator h ha).precompose (derivativeQuery P) (derivativeQuery_FP h))
  exact E.congr (funext fun _ => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

theorem coefficient_packet (P : Readers) (z : List Bool) (i k : ℕ) (m : List Bool) :
    coefficient P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m) =
      residueBits (((polynomial P z i).coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  have hslot : slotQuery (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) m) =
      pair z (BinaryNatCode.encode i) := by
    simp only [slotQuery, BoundedProjectionThom.original, BoundedProjectionThom.order, pairFst_pair, pairSnd_pair]
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
    simp only [derivativeQuery, hslot, orderRead_packet, BoundedProjectionThom.original,
      BoundedProjectionThom.index, pairFst_pair, pairSnd_pair]
    exact BoundedProjectionThom.value_packet P (pairFst z) (order P z i) k m

noncomputable def access (P : Readers) : SignQueryBits.Access (family P) where
  rootCoefficient := BoundedProjectionRootCount.coefficient P ∘ SignPatternBits.sourceQuery
  polynomialCoefficient := coefficient P
  exponent _ := [true]
  root_eq z k m hm := by
    simp only [Function.comp_apply, SignPatternBits.sourceQuery, pairFst_pair, pairSnd_pair]
    exact BoundedProjectionRootCount.coefficient_packet P (pairFst z) k m hm
  polynomial_eq z i _ k m hm := by
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact coefficient_packet P z i k w
  exponent_eq _ _ _ := rfl

noncomputable def moment (P : Readers) (z : List Bool) : ℤ := (family P).value z

attribute [local irreducible] coefficient

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (moment P z)) := by
  have H := (BoundedProjectionRootCount.coefficient_evaluator h ha).precompose _ SignPatternBits.sourceQuery_mem_FP
  have Q := coefficient_evaluator h ha
  have E := SignQueryBits.evaluator (access P) (controls h) (constFn_mem_FP [true]) H Q
  exact E

end LeanCanny.Encoding.BoundedProjectionRecords
