/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterInverse
public import LeanCanny.Algebra.IntegerMatrixTrailingSpace
public import LeanCanny.Algebra.CharacteristicIntegerBounds
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native coefficients for constant-denominator parameter inverses

The trailing-index scan and every characteristic-coefficient query use the
original modular matrix reader. The denominator and inverse coefficients
remain streamed residues, with binary dimension and height allowances.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterInverseBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Berkowitz
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.negate Matrix.charpoly IntegralParameterInverse.inverse IntegralParameterInverse.tail

def base (q : List Bool) : List Bool := LeanCanny.pairFst (LeanCanny.pairFst q)
def modulus (q : List Bool) : List Bool := LeanCanny.pairSnd (LeanCanny.pairFst q)

theorem base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def rawQuery (q : List Bool) : List Bool :=
  LeanCanny.pair (LeanCanny.pair (base q) (LeanCanny.pairSnd q)) (modulus q)

theorem rawQuery_FP : rawQuery ∈ FP := mem_FP_pair (mem_FP_pair base_FP pairSnd_mem_FP) modulus_FP

noncomputable def raw (F : IntegerFamily) (q : List Bool) : List Bool :=
  residueBits ((((F.matrix (base q)).charpoly.coeff (Nat.fromBitsLE (LeanCanny.pairSnd q))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem primitive_packet (F : IntegerFamily) (c m k : List Bool) :
    IntegerCharacteristicBits.value (IntegerMatrixTrailingBits.indexed F) LeanCanny.pairSnd
      (LeanCanny.pair (LeanCanny.pair c k) m) =
        residueBits ((((F.matrix c).charpoly.coeff (Nat.fromBitsLE k)) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : LeanCanny.pair c k = z
  have hc : LeanCanny.pairFst z = c := by rw [← hz, LeanCanny.pairFst_pair]
  have hk : LeanCanny.pairSnd z = k := by rw [← hz, LeanCanny.pairSnd_pair]
  subst c
  subst k
  exact IntegerCharacteristicBits.packet (IntegerMatrixTrailingBits.indexed F) LeanCanny.pairSnd z m

theorem raw_packet (F : IntegerFamily) (q k : List Bool) :
    raw F (LeanCanny.pair q k) =
      residueBits ((((F.matrix (LeanCanny.pairFst q)).charpoly.coeff (Nat.fromBitsLE k)) : ℤ) :
        ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1)) := by
  generalize hz : LeanCanny.pair q k = z
  have hq : LeanCanny.pairFst z = q := by rw [← hz, LeanCanny.pairFst_pair]
  have hk : LeanCanny.pairSnd z = k := by rw [← hz, LeanCanny.pairSnd_pair]
  subst q
  subst k
  rfl

theorem raw_evaluator {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceFunction (raw F) := by
  have H := IntegerCharacteristicBits.evaluator (IntegerMatrixTrailingBits.access a) (IntegerMatrixTrailingBits.controls a ha)
    (E.precompose _ IntegerMatrixTrailingBits.sourceQuery_FP) pairSnd_mem_FP
  exact (H.precompose rawQuery rawQuery_FP).congr
    (funext fun q => primitive_packet F (base q) (modulus q) (LeanCanny.pairSnd q))

def inverseQuery (r : List Bool) : List Bool :=
  LeanCanny.pair (LeanCanny.pairFst (LeanCanny.pairFst r))
    (BinaryNatCode.encode (Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst r)) +
      Nat.fromBitsLE (LeanCanny.pairSnd r) + 1))

theorem inverseQuery_FP : inverseQuery ∈ FP := by
  have hi : BinaryFn (fun r => Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst r))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  have hj := BinaryFn.fromBits pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    ((hi.add hj).add (BinaryFn.const 1)).bits_mem_FP

def negateFinish (r : List Bool) : List Bool :=
  ArithmeticBits.negate (LeanCanny.pair
    (BinaryNatCode.encode (Nat.fromBitsLE (modulus (LeanCanny.pairFst r)) + 1)) (LeanCanny.pairSnd r))

theorem negateFinish_FP : negateFinish ∈ FP := by
  have hm : BinaryFn (fun r => Nat.fromBitsLE (modulus (LeanCanny.pairFst r))) :=
    (BinaryFn.fromBits modulus_FP).comp pairFst_mem_FP
  exact mem_FP_comp
    (f := fun r => LeanCanny.pair (BinaryNatCode.encode (Nat.fromBitsLE (modulus (LeanCanny.pairFst r)) + 1)) (LeanCanny.pairSnd r))
    (g := ArithmeticBits.negate) (mem_FP_pair (hm.add (BinaryFn.const 1)).bits_mem_FP pairSnd_mem_FP)
    ArithmeticBits.negate_mem_FP

noncomputable def value (F : IntegerFamily) (q : List Bool) : List Bool :=
  residueBits (((IntegralParameterInverse.inverse (F.matrix (base q)).charpoly).coeff
    (Nat.fromBitsLE (LeanCanny.pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem evaluator {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {budget : List Bool → ℕ} (hb : BinaryFn budget)
    (hbudget : ∀ c k, ((F.matrix c).charpoly.coeff k).natAbs.size ≤ budget c) : SpaceFunction (value F) := by
  have S := (IntegerMatrixTrailingBits.evaluator a ha E hb hbudget).precompose base base_FP
  have Q := S.withInput.postcompose inverseQuery inverseQuery_FP
  have C := Q.chain (raw_evaluator a ha E)
  apply (C.withInput.postcompose negateFinish negateFinish_FP).congr
  funext q
  let bits := BinaryNatCode.encode (IntegerMatrixTrailingBits.polynomial F (base q)).natTrailingDegree
  change negateFinish (LeanCanny.pair q (raw F (inverseQuery (LeanCanny.pair q bits)))) = value F q
  have HQ : inverseQuery (LeanCanny.pair q bits) = LeanCanny.pair (LeanCanny.pairFst q)
      (BinaryNatCode.encode (Nat.fromBitsLE (LeanCanny.pairSnd q) + (F.matrix (base q)).charpoly.natTrailingDegree + 1)) := by
    simp only [inverseQuery, bits, IntegerMatrixTrailingBits.polynomial,
      LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HQ, raw_packet]
  simp only [negateFinish, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair]
  rw [ArithmeticBits.negate_residueBits]
  simp only [value, IntegralParameterInverse.coeff_inverse, Int.cast_neg, base, modulus,
    Nat.add_right_comm, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def denominatorValue (F : IntegerFamily) (q : List Bool) : List Bool :=
  residueBits ((IntegralParameterInverse.denominator (F.matrix (LeanCanny.pairFst q)).charpoly : ℤ) :
    ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1))

theorem denominator_evaluator {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {budget : List Bool → ℕ} (hb : BinaryFn budget)
    (hbudget : ∀ c k, ((F.matrix c).charpoly.coeff k).natAbs.size ≤ budget c) :
    SpaceFunction (denominatorValue F) := by
  have S := (IntegerMatrixTrailingBits.evaluator a ha E hb hbudget).precompose LeanCanny.pairFst pairFst_mem_FP
  apply (S.withInput.chain (raw_evaluator a ha E)).congr
  funext q
  change raw F (LeanCanny.pair q (BinaryNatCode.encode (F.matrix (LeanCanny.pairFst q)).charpoly.natTrailingDegree)) = _
  rw [raw_packet]
  simp only [denominatorValue, IntegralParameterInverse.denominator, Polynomial.trailingCoeff,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem evaluator_of_entry_bounds {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {height : List Bool → ℕ} (hh : BinaryFn height)
    (hentries : ∀ c i j, (F.matrix c i j).natAbs ≤ 2 ^ height c) : SpaceFunction (value F) := by
  have hN : BinaryFn F.dimension :=
    BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))
  exact evaluator a ha E (CharacteristicIntegerBounds.budget_binary hN hh)
    (fun c k => CharacteristicIntegerBounds.coefficient_bits (F.matrix c) (height c) (hentries c) k)

theorem denominator_evaluator_of_entry_bounds {F : IntegerFamily} (a : IntegerAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) {height : List Bool → ℕ} (hh : BinaryFn height)
    (hentries : ∀ c i j, (F.matrix c i j).natAbs ≤ 2 ^ height c) :
    SpaceFunction (denominatorValue F) := by
  have hN : BinaryFn F.dimension :=
    BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))
  exact denominator_evaluator a ha E (CharacteristicIntegerBounds.budget_binary hN hh)
    (fun c k => CharacteristicIntegerBounds.coefficient_bits (F.matrix c) (height c) (hentries c) k)

end LeanCanny.Algebra.IntegralParameterInverseBits
