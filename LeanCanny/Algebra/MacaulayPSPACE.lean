/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryCorrect
public import LeanCanny.Algebra.IntegerDeterminantSpaceEntries

/-! # Polynomial-space zero testing for padded Macaulay determinants

The dimension is exponential and never written in unary. Polynomially bounded
arity, block width and degrees, an FP binary coefficient budget, and certified
source coefficient residues suffice. Homogeneity is needed for the common-root
theorem, but not for computing this determinant. This does not identify a
resultant, decide homogeneous feasibility, or extract Canny's eliminant.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits

open LeanCanny.Encoding LeanCanny.Computation

structure Family where
  layout : Layout
  polynomial : (c : List Bool) → Fin (layout.arity c) → MvPolynomial (Fin (layout.arity c)) ℤ
  coefficientBits : List Bool → ℕ
  bound : ∀ c i e, ((polynomial c i).coeff e).natAbs ≤ 2 ^ coefficientBits c

def dimensionCode (L : Layout) : List Bool → List Bool := FixedWidthPolynomial.countCode L.arity L.width

def budgetCode (L : Layout) (bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair
    (BinaryNat.mul (pair (BinaryNatCode.encode (dimensionCode L c).length) (dimensionCode L c)))
    (BinaryNat.mul (pair (dimensionCode L c) (bits c)))))

theorem dimensionCode_mem_FP {L : Layout} (h : L.PolyTime) : dimensionCode L ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP h.arity h.width

theorem budgetCode_mem_FP {L : Layout} (h : L.PolyTime) {bits : List Bool → List Bool}
    (hb : bits ∈ FP) : budgetCode L bits ∈ FP := by
  have hd := dimensionCode_mem_FP h
  have hs := bits_mem_FP (UnaryFn.length hd)
  have hleft := mem_FP_comp (mem_FP_pair hs hd) BinaryNat.mul_mem_FP
  have hright := mem_FP_comp (mem_FP_pair hd hb) BinaryNat.mul_mem_FP
  have hsum := mem_FP_comp (mem_FP_pair hleft hright) BinaryNat.add_mem_FP
  have hout := mem_FP_comp hsum BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := budgetCode L bits) hout ?_
  intro c
  simp only [Function.comp_apply, budgetCode]
  rfl

theorem budgetCode_code (L : Layout) (bits : List Bool → List Bool) (B : List Bool → ℕ)
    (hb : ∀ c, bits c = BinaryNatCode.encode (B c)) (c : List Bool) :
    budgetCode L bits c = BinaryNatCode.encode
      ((FixedWidthPolynomial.count (L.arity c) (L.width c)).size *
        FixedWidthPolynomial.count (L.arity c) (L.width c) +
        FixedWidthPolynomial.count (L.arity c) (L.width c) * B c + 1) := by
  simp only [budgetCode, dimensionCode, FixedWidthPolynomial.countCode_code,
    BinaryNatCode.length_encode, hb, BinaryNat.succ_eq_bits, BinaryNat.add_pair,
    BinaryNat.mul_pair, fromBits_encode, Nat.fromBitsLE_bits]
  rfl

theorem matrix_entry_bound (F : Family) (c : List Bool)
    (r s : Macaulay.Index (F.layout.arity c) (F.layout.width c)) :
    (Macaulay.matrix (F.polynomial c) (Degrees F.layout c) (F.layout.width c) r s).natAbs ≤
      2 ^ F.coefficientBits c := by
  by_cases hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees F.layout c)
  · rw [Macaulay.entry_active _ _ _ r s hr]
    split_ifs
    · exact F.bound c _ _
    · exact Nat.zero_le _
  · simp only [Macaulay.matrix, dite_eq_right hr, Matrix.one_apply]
    split_ifs
    · exact Nat.one_le_two_pow
    · exact Nat.zero_le _

noncomputable def Family.integer (F : Family) : Berkowitz.IntegerFamily where
  dimension := fun c => FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c)
  matrix := fun c => Macaulay.matrix (F.polynomial c) (Degrees F.layout c) (F.layout.width c)
  budget := fun c => (FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c)).size *
    FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c) +
    FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c) * F.coefficientBits c + 1
  determinant_bits := fun c => IntegerModular.det_natAbs_size_le_uniform _ _ (matrix_entry_bound F c)

def Family.zeroLanguage (F : Family) : Language := {c | c ∈ F.integer.zeroLanguage}

structure Access (F : Family) where
  bits : List Bool → List Bool
  bits_eq : ∀ c, bits c = BinaryNatCode.encode (F.coefficientBits c)
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ q (i : Fin (F.layout.arity (pairFst q))) (k : ℕ),
    coefficient (packet q i.val k) = MatrixPower.residueBits
      ((F.polynomial (pairFst q) i).coeff (RationalSubstitution.Indexed.exponentVector (F.layout.arity (pairFst q))
        (FixedWidthPolynomial.entry (F.layout.width (pairFst q)) k)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

noncomputable def Access.integer {F : Family} (a : Access F) : Berkowitz.IntegerAccess F.integer where
  dimension := dimensionCode F.layout
  budget := budgetCode F.layout a.bits
  entry := entry F.layout a.coefficient
  dimension_eq := FixedWidthPolynomial.countCode_code F.layout.arity F.layout.width
  budget_eq := budgetCode_code F.layout a.bits F.coefficientBits a.bits_eq
  entry_eq := fun q i j => entry_packet F.layout a.coefficient q (F.polynomial (pairFst q))
    (a.coefficient_eq q) i j

theorem Access.integer_controls {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hb : a.bits ∈ FP) : a.integer.ControlsPolyTime := by
  constructor
  · simpa only [Access.integer] using dimensionCode_mem_FP h
  · simpa only [Access.integer] using budgetCode_mem_FP h hb

theorem Access.integer_entryEvaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (E : SpaceFunction a.coefficient) : SpaceFunction a.integer.entry := by
  have EC := entryEvaluator h E
  simpa only [Access.integer] using EC

theorem Access.decider {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hb : a.bits ∈ FP) (E : SpaceFunction a.coefficient) : SpaceDecider F.zeroLanguage :=
  Berkowitz.IntegerAccess.deciderWithEntry a.integer (a.integer_controls h hb) (a.integer_entryEvaluator h E)

theorem Access.zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hb : a.bits ∈ FP) (E : SpaceFunction a.coefficient) : F.zeroLanguage ∈ PSPACE :=
  (a.decider h hb E).mem_PSPACE

end LeanCanny.Algebra.MacaulayBits
