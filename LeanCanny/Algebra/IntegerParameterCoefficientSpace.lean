/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerParameterCoefficient
public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.ModularNatMulFP
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native coefficient access for integer parameter substitution

The first fixed-width block is the parameter exponent. Dropping that block
gives the original spatial query. Both are retained in binary, so one source
coefficient call evaluates the represented integer polynomial in native space.
The writer is total on arbitrary target words, including width zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerParameterCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegerParameterFlatten
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (W : List Bool → ℕ) (source target : List Bool → List Bool)

def parameter (c : List Bool) : List Bool := BinaryNat.normalize ((target c).take (W c))
def spatial (c : List Bool) : List Bool := BinaryNat.normalize ((target c).drop (W c))

theorem parameter_mem_FP (hW : UnaryFn W) (ht : target ∈ FP) : parameter W target ∈ FP :=
  mem_FP_comp (take_mem_FP ht hW) BinaryNat.normalize_mem_FP

theorem spatial_mem_FP (hW : UnaryFn W) (ht : target ∈ FP) : spatial W target ∈ FP :=
  mem_FP_comp (drop_mem_FP ht hW) BinaryNat.normalize_mem_FP

def query (c : List Bool) : List Bool := pair (source c) (pair (parameter W target c) (spatial W target c))

theorem query_mem_FP (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) :
    query W source target ∈ FP :=
  mem_FP_pair hs (mem_FP_pair (parameter_mem_FP W target hW ht) (spatial_mem_FP W target hW ht))

def value (coefficient : List Bool → List Bool) (c : List Bool) : List Bool :=
  coefficient (query W source target c)

theorem evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) :
    SpaceFunction (value W source target coefficient) :=
  E.precompose (query W source target) (query_mem_FP W source target hW hs ht)

private theorem entry_fromBits (w : ℕ) (bits : List Bool) (i : ℕ) :
    entry w (Nat.fromBitsLE bits) i = Nat.fromBitsLE ((bits.drop (i * w)).take w) := by
  rw [entry_eq_digit, BinaryNat.value_take, drop_value]

theorem tail_nativeExponent (n : ℕ) (c : List Bool) :
    tailExponent (nativeExponent (Equiv.refl (Fin (n + 1))) (W c) (Nat.fromBitsLE (target c))) =
      nativeExponent (Equiv.refl (Fin n)) (W c) (Nat.fromBitsLE (spatial W target c)) := by
  ext i
  simp only [tailExponent_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    Equiv.refl_apply, spatial, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  rw [entry_fromBits, entry_fromBits, List.drop_drop]
  congr 2
  simp only [Fin.val_succ, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem parameter_nativeExponent (n : ℕ) (c : List Bool) :
    nativeExponent (Equiv.refl (Fin (n + 1))) (W c) (Nat.fromBitsLE (target c)) 0 =
      Nat.fromBitsLE (parameter W target c) := by
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    Fin.val_zero, entry_fromBits, Nat.zero_mul, List.drop_zero, parameter,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]

theorem coefficient (n : ℕ) (q : MvPolynomial (Fin n) (Polynomial ℤ)) (c : List Bool) :
    (flatten q).coeff (nativeExponent (Equiv.refl (Fin (n + 1))) (W c) (Nat.fromBitsLE (target c))) =
      (q.coeff (nativeExponent (Equiv.refl (Fin n)) (W c)
        (Nat.fromBitsLE (spatial W target c)))).coeff (Nat.fromBitsLE (parameter W target c)) := by
  rw [coeff_flatten, tail_nativeExponent, parameter_nativeExponent]

/-- Any native source reader for the parameter-ring coefficients gives the
actual modular coefficient of the integer polynomial after one FP query. -/
theorem packet {n : ℕ} (q : MvPolynomial (Fin n) (Polynomial ℤ))
    (reader : List Bool → List Bool) (c : List Bool) (m : ℕ)
    (hreader : ∀ k r, reader (pair (source c) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode r))) =
      residueBits (((q.coeff (nativeExponent (Equiv.refl (Fin n)) (W c) r)).coeff k : ℤ) : ZMod (m + 1))) :
    value W source target reader c =
      residueBits (((flatten q).coeff (nativeExponent (Equiv.refl (Fin (n + 1)))
        (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod (m + 1)) := by
  rw [coefficient W target n q c]
  change reader (pair (source c) (pair (parameter W target c) (spatial W target c))) = _
  have hp : parameter W target c = BinaryNatCode.encode (Nat.fromBitsLE (parameter W target c)) := by
    simp only [parameter, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, BinaryNatCode.encode]
  have hs : spatial W target c = BinaryNatCode.encode (Nat.fromBitsLE (spatial W target c)) := by
    simp only [spatial, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, BinaryNatCode.encode]
  conv_lhs => rw [hp, hs]
  exact hreader _ _

/-- Adapt the source protocol `(context, parameter exponent, spatial rank)`
to the ordinary integer coefficient protocol `(context, rank)`. -/
def liftReader (reader : List Bool → List Bool) (z : List Bool) : List Bool :=
  value (W ∘ pairFst) pairFst pairSnd reader z

theorem liftReader_evaluator {reader : List Bool → List Bool} (E : SpaceFunction reader)
    (hW : UnaryFn W) : SpaceFunction (liftReader W reader) :=
  evaluator (W ∘ pairFst) pairFst pairSnd E (hW.comp pairFst_mem_FP) pairFst_mem_FP pairSnd_mem_FP

theorem liftReader_packet {n : ℕ} (q : MvPolynomial (Fin n) (Polynomial ℤ))
    (reader : List Bool → List Bool) (c : List Bool) (m r : ℕ)
    (hreader : ∀ k s, reader (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode s))) =
      residueBits (((q.coeff (nativeExponent (Equiv.refl (Fin n)) (W c) s)).coeff k : ℤ) : ZMod (m + 1))) :
    liftReader W reader (pair c (BinaryNatCode.encode r)) =
      residueBits (((flatten q).coeff (nativeExponent (Equiv.refl (Fin (n + 1))) (W c) r) : ℤ) : ZMod (m + 1)) := by
  have h := packet (W ∘ pairFst) pairFst pairSnd q reader (pair c (BinaryNatCode.encode r)) m
    (by simpa only [Function.comp_apply, pairFst_pair] using hreader)
  simpa only [liftReader, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

end LeanCanny.Algebra.IntegerParameterCoefficientBits
