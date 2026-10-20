/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryEncoding
public import LeanCanny.Algebra.MacaulayPSPACE
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Polynomial-space coefficients of symbolic Macaulay determinants

A context carries a polynomial system, positive modulus and requested output
degree. Each child query selects a source polynomial, monomial rank and parameter
degree. The scalar selector retains that degree in its context. Identity padding
contributes only at degree zero. The polynomial determinant evaluator includes
all source-coefficient child costs.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayPolynomial
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open MacaulayBits

structure Family where
  layout : Layout
  modulus : List Bool → ℕ
  degree : List Bool → ℕ
  polynomial : (c : List Bool) → Fin (layout.arity c) →
    MvPolynomial (Fin (layout.arity c)) (Polynomial (ZMod (modulus c)))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.determinant (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension := fun c => FixedWidthPolynomial.count (F.layout.arity c) (F.layout.width c)
  modulus := F.modulus
  degree := F.degree
  matrix := fun c => Macaulay.matrix (F.polynomial c) (Degrees F.layout c) (F.layout.width c)
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def Family.value (F : Family) : List Bool → List Bool := F.determinant.value

def sourceInput (p : List Bool) : List Bool :=
  pair (context p) (pair (row p) (pair (col p) (pairSnd (pairFst p))))

theorem sourceInput_mem_FP : sourceInput ∈ FP :=
  mem_FP_pair context_mem_FP (mem_FP_pair row_mem_FP (mem_FP_pair col_mem_FP
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)))

theorem sourceInput_packet (c : List Bool) (D i k : ℕ) :
    sourceInput (packet (pair c (BinaryNatCode.encode D)) i k) =
      pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode D))) := by
  simp only [sourceInput, context_packet, row_packet, col_packet]
  simp only [packet, pairFst_pair, pairSnd_pair]

def constantEntry (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd (pairFst p)) = 0 ∧ sameIndex p then
    MatrixPower.ArithmeticBits.one (modulus (context p)) else []

theorem constantEntry_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    constantEntry modulus ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hz : FPPred (fun p => Nat.fromBitsLE (pairSnd (pairFst p)) = 0) :=
    (BinaryNat.le_fppred ht (constFn_mem_FP [])).of_iff (fun p => by change Nat.fromBitsLE (pairSnd (pairFst p)) ≤ 0 ↔ _; omega)
  have ho := mem_FP_comp (mem_FP_comp context_mem_FP hm) MatrixPower.ArithmeticBits.one_mem_FP
  have hf := (hz.and sameIndex_fppred).ite_mem_FP ho (constFn_mem_FP [])
  refine mem_FP_of_eq (g := constantEntry modulus) hf ?_
  intro p
  rfl

theorem constantEntry_packet (modulus : List Bool → List Bool) (c : List Bool) (m D r s : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) :
    constantEntry modulus (packet (pair c (BinaryNatCode.encode D)) r s) =
      MatrixPower.residueBits (((if r = s then 1 else 0) : Polynomial (ZMod m)).coeff D) := by
  simp only [constantEntry, context_packet, sameIndex, row_packet, col_packet, fromBits_encode]
  simp only [packet, pairFst_pair, pairSnd_pair, fromBits_encode, hm]
  by_cases hD : D = 0 <;> by_cases hrs : r = s
  · subst D
    simp only [hrs, ite_true, Polynomial.coeff_one_zero]
    exact MatrixPower.ArithmeticBits.one_residueBits m
  · simp only [hD, hrs, ite_false, and_false, Polynomial.coeff_zero]
    simp [MatrixPower.residueBits, BinaryNatCode.encode]
  · simp only [hD, hrs, ite_true, ite_false, false_and, Polynomial.coeff_one]
    simp [MatrixPower.residueBits, BinaryNatCode.encode]
  · simp only [hD, hrs, ite_false, false_and, Polynomial.coeff_zero]
    simp [MatrixPower.residueBits, BinaryNatCode.encode]

structure Access (F : Family) where
  modulus : List Bool → List Bool
  degree : List Bool → List Bool
  coefficient : List Bool → List Bool
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  coefficient_eq : ∀ c (i : Fin (F.layout.arity c)) k D,
    coefficient (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode D)))) =
      MatrixPower.residueBits (((F.polynomial c i).coeff
        (RationalSubstitution.Indexed.exponentVector (F.layout.arity c)
          (FixedWidthPolynomial.entry (F.layout.width c) k))).coeff D)

def Access.entry {F : Family} (a : Access F) : List Bool → List Bool :=
  entryWithIdentity F.layout (a.coefficient ∘ sourceInput) (constantEntry a.modulus) ∘ PolynomialMoment.augmentedInput

noncomputable def Access.entryEvaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction a.entry := by
  have EC := E.precompose sourceInput sourceInput_mem_FP
  have ES := entryWithIdentityEvaluator h EC (constantEntry_mem_FP hm)
  exact ES.precompose PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

theorem Access.entry_correct {F : Family} (a : Access F) (c : List Bool)
    (i j : Macaulay.Index (F.layout.arity c) (F.layout.width c)) (D : ℕ) :
    a.entry (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode D)))) =
      MatrixPower.residueBits ((Macaulay.matrix (F.polynomial c) (Degrees F.layout c) (F.layout.width c) i j).coeff D) := by
  simp only [Access.entry, Function.comp_apply, PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair]
  change entryWithIdentity F.layout (a.coefficient ∘ sourceInput) (constantEntry a.modulus)
    (packet (pair c (BinaryNatCode.encode D)) i.val j.val) = _
  have H := entryWithIdentity_packet (R := Polynomial (ZMod (F.modulus c))) F.layout (a.coefficient ∘ sourceInput) (constantEntry a.modulus)
    (pair c (BinaryNatCode.encode D))
  dsimp only [Indices] at H
  rw [pairFst_pair] at H
  refine H (F.polynomial c) (fun p => MatrixPower.residueBits (p.coeff D)) ?_ ?_ i j ?_
  · simp [MatrixPower.residueBits, BinaryNatCode.encode]
  · intro k r
    change a.coefficient (sourceInput (packet (pair c (BinaryNatCode.encode D)) k.val r)) = _
    rw [sourceInput_packet]
    exact a.coefficient_eq c k r D
  · exact constantEntry_packet a.modulus c (F.modulus c) D i.val j.val (a.modulus_eq c)

noncomputable def Access.determinant {F : Family} (a : Access F) : BerkowitzPolynomial.ModularAccess F.determinant where
  dimension := dimensionCode F.layout
  modulus := a.modulus
  degree := a.degree
  entry := a.entry
  dimension_eq := FixedWidthPolynomial.countCode_code F.layout.arity F.layout.width
  modulus_eq := a.modulus_eq
  degree_eq := a.degree_eq
  entry_eq := a.entry_correct

theorem Access.determinant_controls {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (hd : a.degree ∈ FP) : a.determinant.ControlsPolyTime :=
  ⟨dimensionCode_mem_FP h, hm, hd⟩

noncomputable def Access.determinantEntryEvaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction a.determinant.entry := by
  have ES := a.entryEvaluator h hm E
  simpa only [Access.determinant] using ES

noncomputable def Access.evaluator {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (hd : a.degree ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction F.value :=
  BerkowitzPolynomial.ModularAccess.evaluator a.determinant (a.determinant_controls h hm hd)
    (a.determinantEntryEvaluator h hm E)

theorem Access.zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.layout.PolyTime)
    (hm : a.modulus ∈ FP) (hd : a.degree ∈ FP) (E : SpaceFunction a.coefficient) : F.determinant.zeroLanguage ∈ PSPACE :=
  BerkowitzPolynomial.ModularAccess.zeroLanguage_mem_PSPACE_of_evaluator a.determinant
    (a.determinant_controls h hm hd) (a.determinantEntryEvaluator h hm E)

end LeanCanny.Algebra.MacaulayPolynomial
