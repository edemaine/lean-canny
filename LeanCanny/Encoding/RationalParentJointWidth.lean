/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentJointCoefficient
public import LeanCanny.Algebra.HomogenizationPolynomialSpace

/-! # Joint rows in arbitrary polynomially bounded exponent widths

Valid selected pivots and rows use the existing complete joint reader. A
binary degree guard precedes width conversion. Moduli and monomial ranks are
normalized without changing the original source context.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentJointWidth
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open RationalParentJointSource (system degree width)
open RationalParentJointSource (Inputs)
open scoped Classical
attribute [local irreducible] RationalParentJointCoefficient.value
  RationalParentJointSource.system RationalParentJointSource.degree
  RationalParentJointSource.width CoefficientWidthBits.value

def query (context row modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (context (pairFst q)) (pair (row (pairFst q)) (BinaryNat.normalize (pairSnd q))))
    (BinaryNat.normalize (modulus (pairFst q)))

theorem query_FP {context row modulus : List Bool → List Bool} (hc : context ∈ FP)
    (hr : row ∈ FP) (hm : modulus ∈ FP) : query context row modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP hc) (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr)
    (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)))
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.normalize_mem_FP)

def normalize (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.normalize (pairSnd q))
theorem normalize_FP : normalize ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def value (F : Inputs) (w W : List Bool → ℕ)
    (bits context : List Bool → List Bool) (pivot : (u : List Bool) → Fin (F.block.dim u))
    (row : (u : List Bool) → Fin (F.block.dim (context u) + 1)) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  HomogenizationPolynomialBits.integerValue (fun u => F.block.dim (context u) + 1) W
    (fun u => system F w bits (context u) (pivot (context u)) (row u)) modulus

theorem evaluator {F : Inputs} (h : F.Access)
    {w W : List Bool → ℕ} (hw : UnaryFn w) (hW : UnaryFn W)
    {bits : List Bool → List Bool} (E : SpaceFunction bits) (pivot : (u : List Bool) → Fin (F.block.dim u))
    (hp : BinaryFn (fun u => (pivot u).val)) {context : List Bool → List Bool} (hc : context ∈ FP)
    (row : (u : List Bool) → Fin (F.block.dim (context u) + 1))
    (hi : UnaryFn (fun u => (row u).val)) {modulus : List Bool → List Bool} (hm : modulus ∈ FP)
    (htS : ∀ u, (TermView.term (F.block.source.source u)).arity ≤ F.block.source.dim u) :
    SpaceFunction (value F w W bits context pivot row modulus) := by
  let old := value F w (RationalParentJointSource.width F ∘ context) bits context pivot row modulus
  have ES := (RationalParentJointCoefficient.evaluator h hw hp E htS).precompose
    (query context (fun u => BinaryNatCode.encode (row u).val) modulus) (query_FP hc (bits_mem_FP hi) hm)
  have EO : SpaceFunction old := ES.congr (funext fun q => by
    have H := RationalParentJointCoefficient.packet F w (fun u => (pivot u).val) bits
      (context (pairFst q)) (pivot (context (pairFst q))) rfl (row (pairFst q)) (Nat.fromBitsLE (pairSnd q))
      (Nat.fromBitsLE (modulus (pairFst q)))
    simpa only [query, BinaryNat.normalize_eq_bits, Function.comp_apply, old, value,
      HomogenizationPolynomialBits.integerValue, BinaryNatCode.encode] using H)
  have EC := CoefficientWidthBits.evaluator_binary_degree ((h.block.dim.comp hc).add (UnaryFn.const 1)) hW
    ((RationalParentJointSource.width_unary h).comp hc)
    ((RationalParentJointSource.degree_binary h).comp hc) EO
  refine (EC.precompose normalize normalize_FP).congr (funext fun q => ?_)
  have H := CoefficientWidthBits.value_packet (fun u => F.block.dim (context u) + 1) W
    (RationalParentJointSource.width F ∘ context) (degree F ∘ context) old
    (pairFst q) (Equiv.refl _) (system F w bits (context (pairFst q)) (pivot (context (pairFst q))) (row (pairFst q)))
    (fun a : ℤ => MatrixPower.residueBits (a : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [MatrixPower.residueBits, BinaryNatCode.encode])
    (RationalParentJointSource.degree_lt_width F (context (pairFst q)))
    (fun m hm i => (MvPolynomial.monomial_le_degreeOf i hm).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
        (RationalParentJointSource.polynomial_degree F w bits (context (pairFst q))
          (pivot (context (pairFst q))) (row (pairFst q)))) )
    (fun r => HomogenizationPolynomialBits.integer_packet _ _ _ _ (pairFst q) r) (Nat.fromBitsLE (pairSnd q))
  simpa only [Function.comp_def, normalize, BinaryNat.normalize_eq_bits, value,
    HomogenizationPolynomialBits.integerValue, BinaryNatCode.encode] using H

end LeanCanny.Encoding.RationalParentJointWidth
