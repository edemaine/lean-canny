/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCausalLevelSchedule
public import LeanCanny.Algebra.ImplicitPowerResidueFP
public import LeanCanny.Encoding.LevelLiftCoefficient
/-! # Native residues of a causal next-frame level coefficient

Only the old bank rank and old entry-height bound enter the exponent. The
integer coefficient is never serialized, and composite query moduli are valid.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalLevelCoefficient
open LeanCanny.Algebra LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
open LeanCanny.Algebra.MatrixPower

def read (n D m B G : List Bool → ℕ) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  LevelLiftCoefficient.read n D
    (fun q => IntegralMixedRetainedRealBound.height (FixedWidthPolynomial.count (m q) (B q)) (G q)) modulus

theorem rank_binary {m B : List Bool → ℕ} (hm : UnaryFn m) (hB : UnaryFn B) :
    BinaryFn (fun q => FixedWidthPolynomial.count (m q) (B q)) :=
  ((BinaryFn.const 2).powUnary hB).powUnary hm

theorem height_binary {m B G : List Bool → ℕ} (hm : UnaryFn m) (hB : UnaryFn B) (hG : BinaryFn G) :
    BinaryFn (fun q => IntegralMixedRetainedRealBound.height (FixedWidthPolynomial.count (m q) (B q)) (G q)) :=
  IntegralMixedRetainedRealBound.height_binary (rank_binary hm hB) hG

theorem read_FP {n D m B G : List Bool → ℕ} {modulus : List Bool → List Bool}
    (hn : UnaryFn n) (hD : UnaryFn D) (hm : UnaryFn m) (hB : UnaryFn B) (hG : BinaryFn G)
    (hmod : modulus ∈ FP) : read n D m B G modulus ∈ FP :=
  LevelLiftCoefficient.read_FP hn hD (height_binary hm hB hG) hmod

theorem read_value (n D m B G : List Bool → ℕ) (modulus : List Bool → List Bool) (q : List Bool) :
    read n D m B G modulus q=residueBits
      ((coefficient (n q) (D q) (FixedWidthPolynomial.count (m q) (B q)) (G q):ℤ):
        ZMod (Nat.fromBitsLE (modulus q)+1)) :=
  LevelLiftCoefficient.read_value n D _ modulus q

def scheduledExponent (n D R b C j : List Bool → ℕ) (q : List Bool) : ℕ :=
  LeanCanny.Geometry.IntegralMixedCausalLevelSchedule.cfactor (n q) (D q) (R q)*
    LeanCanny.Geometry.IntegralMixedCausalLevelSchedule.schedule (b q) (C q) (j q)

theorem scheduledExponent_binary {n D R b C j : List Bool → ℕ}
    (hn : UnaryFn n) (hD : BinaryFn D) (hR : BinaryFn R) (hb : BinaryFn b) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (scheduledExponent n D R b C j) :=
  (LeanCanny.Geometry.IntegralMixedCausalLevelSchedule.cfactor_binary hn hD hR).mul
    (LeanCanny.Geometry.IntegralMixedCausalLevelSchedule.schedule_binary hb hC hj)

def scheduledRead (n D R b C j : List Bool → ℕ) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  ImplicitPowerResidue.value (fun _ => BinaryNatCode.encode 2)
    (fun q => BinaryNatCode.encode (scheduledExponent n D R b C j q)) modulus

theorem scheduledRead_FP {n D R b C j : List Bool → ℕ} {modulus : List Bool → List Bool}
    (hn : UnaryFn n) (hD : BinaryFn D) (hR : BinaryFn R) (hb : BinaryFn b) (hC : BinaryFn C) (hj : UnaryFn j)
    (hmod : modulus ∈ FP) : scheduledRead n D R b C j modulus ∈ FP :=
  ImplicitPowerResidue.value_mem_FP _ _ _ (constFn_mem_FP _)
    (scheduledExponent_binary hn hD hR hb hC hj).bits_mem_FP hmod

theorem scheduledRead_value (n D R b C j : List Bool → ℕ) (modulus : List Bool → List Bool) (q : List Bool) :
    scheduledRead n D R b C j modulus q=residueBits
      (((2:ℤ)^scheduledExponent n D R b C j q:ℤ):ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  rw [scheduledRead,ImplicitPowerResidue.value_eq]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,Int.cast_pow,Int.cast_ofNat,Nat.cast_ofNat]

end LeanCanny.Encoding.IntegralMixedCausalLevelCoefficient
