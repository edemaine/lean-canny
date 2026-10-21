/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialMomentSpace
public import LeanCanny.Algebra.BerkowitzFactorChildCorrect

/-!
# Trailing-block polynomial moment coefficients

A moment context pairs an ordinary layered-entry request with a requested
polynomial degree. Offset writers retain each coefficient query's degree
while selecting the border vectors and trailing block in the original matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Polynomial Matrix
open Berkowitz

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  degree : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))[X]
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits ((F.matrix c).det.coeff (F.degree c))

def ModularFamily.zeroLanguage (F : ModularFamily) : Complexity.Language :=
  {c | (F.matrix c).det.coeff (F.degree c) = 0}

structure ModularAccess (F : ModularFamily) where
  dimension : List Bool → List Bool
  modulus : List Bool → List Bool
  degree : List Bool → List Bool
  entry : List Bool → List Bool
  dimension_eq : ∀ c, dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  entry_eq : ∀ c i j d, entry (pair c (pair (BinaryNatCode.encode i.val)
    (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) = residueBits ((F.matrix c i j).coeff d)

structure ModularAccess.ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  degree : a.degree ∈ FP

def stage (F : ModularFamily) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (QueryBits.rowIndex q) / (F.dimension (pairFst q) + 1)
def trailingDimension (F : ModularFamily) (q : List Bool) : ℕ := F.dimension (pairFst q) - stage F q - 1
def momentExponent (F : ModularFamily) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (QueryBits.colIndex q) % (F.dimension (pairFst q) + 1) -
    (Nat.fromBitsLE (QueryBits.rowIndex q) % (F.dimension (pairFst q) + 1) + 1)

def momentFamily (F : ModularFamily) : PolynomialMoment.ModularFamily where
  dimension := fun p => trailingDimension F (pairFst p)
  modulus := fun p => F.modulus (pairFst (pairFst p))
  exponent := fun p => momentExponent F (pairFst p)
  degree := fun p => Nat.fromBitsLE (pairSnd p)
  row := fun p j => F.matrix (pairFst (pairFst p))
    ⟨stage F (pairFst p), by have h := j.isLt; dsimp only [trailingDimension] at h; omega⟩
    ⟨stage F (pairFst p) + 1 + j.val, by have h := j.isLt; dsimp only [trailingDimension] at h; omega⟩
  column := fun p i => F.matrix (pairFst (pairFst p))
    ⟨stage F (pairFst p) + 1 + i.val, by have h := i.isLt; dsimp only [trailingDimension] at h; omega⟩
    ⟨stage F (pairFst p), by have h := i.isLt; dsimp only [trailingDimension] at h; omega⟩
  matrix := fun p i j => F.matrix (pairFst (pairFst p))
    ⟨stage F (pairFst p) + 1 + i.val, by have h := i.isLt; dsimp only [trailingDimension] at h; omega⟩
    ⟨stage F (pairFst p) + 1 + j.val, by have h := j.isLt; dsimp only [trailingDimension] at h; omega⟩
  modulus_ne_zero := fun p => F.modulus_ne_zero (pairFst (pairFst p))

def attachDegree (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (pairFst (pairSnd (pairFst p)))
    (pair (pairSnd (pairSnd (pairFst p))) (pairSnd p)))

def vectorBase (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairFst (pairSnd p))
def matrixBase (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (pairFst (pairSnd p)) (pairFst (pairSnd (pairSnd p))))

def rowInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  attachDegree (pair (EntryAccess.rowInput dim (vectorBase p)) (pairSnd (pairSnd p)))
def columnInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  attachDegree (pair (EntryAccess.columnInput dim (vectorBase p)) (pairSnd (pairSnd p)))
def matrixInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  attachDegree (pair (EntryAccess.matrixInput dim (matrixBase p)) (pairSnd (pairSnd (pairSnd p))))

theorem attachDegree_mem_FP : attachDegree ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  have hj := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hi (mem_FP_pair hj pairSnd_mem_FP))
  refine mem_FP_of_eq (g := attachDegree) h ?_
  intro p
  simp only [Function.comp_apply, attachDegree]

theorem vectorBase_mem_FP : vectorBase ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  exact mem_FP_pair hc hi

theorem matrixBase_mem_FP : matrixBase ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  exact mem_FP_pair hc (mem_FP_pair hi hj)

theorem rowInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : rowInput dim ∈ FP := by
  have hq := mem_FP_comp vectorBase_mem_FP (EntryAccess.rowInput_mem_FP hd)
  have hk := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hq hk) attachDegree_mem_FP
  refine mem_FP_of_eq (g := rowInput dim) h ?_
  intro p
  simp only [Function.comp_apply, rowInput]

theorem columnInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : columnInput dim ∈ FP := by
  have hq := mem_FP_comp vectorBase_mem_FP (EntryAccess.columnInput_mem_FP hd)
  have hk := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hq hk) attachDegree_mem_FP
  refine mem_FP_of_eq (g := columnInput dim) h ?_
  intro p
  simp only [Function.comp_apply, columnInput]

theorem matrixInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : matrixInput dim ∈ FP := by
  have hq := mem_FP_comp matrixBase_mem_FP (EntryAccess.matrixInput_mem_FP hd)
  have hk := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hq hk) attachDegree_mem_FP
  refine mem_FP_of_eq (g := matrixInput dim) h ?_
  intro p
  simp only [Function.comp_apply, matrixInput]

namespace ModularAccess

theorem stage_code {F : ModularFamily} (a : ModularAccess F) (q : List Bool) :
    QueryBits.sourceLayer a.dimension q = BinaryNatCode.encode (stage F q) := by
  rw [QueryBits.sourceLayer_eq_code]
  simp only [QueryBits.inputDimension, a.dimension_eq, QueryBits.code_value, stage]

theorem trailingDimension_code {F : ModularFamily} (a : ModularAccess F) (q : List Bool) :
    QueryBits.remaining a.dimension q = BinaryNatCode.encode (trailingDimension F q) := by
  rw [QueryBits.remaining_eq_code]
  simp only [QueryBits.inputDimension, a.dimension_eq, QueryBits.code_value, trailingDimension, stage]

theorem momentExponent_code {F : ModularFamily} (a : ModularAccess F) (q : List Bool) :
    QueryBits.momentExponent a.dimension q = BinaryNatCode.encode (momentExponent F q) := by
  rw [QueryBits.momentExponent_eq_code]
  simp only [QueryBits.inputDimension, a.dimension_eq, QueryBits.code_value, momentExponent]

set_option backward.isDefEq.respectTransparency false in
def momentAccess {F : ModularFamily} (a : ModularAccess F) : PolynomialMoment.ModularAccess (momentFamily F) where
  bits := {
    dimension := QueryBits.remaining a.dimension ∘ pairFst
    row := a.entry ∘ rowInput a.dimension
    column := a.entry ∘ columnInput a.dimension
    entry := a.entry ∘ matrixInput a.dimension }
  modulus := a.modulus ∘ pairFst ∘ pairFst
  exponent := QueryBits.momentExponent a.dimension ∘ pairFst
  degree := BinaryNat.normalize ∘ pairSnd
  dimension_eq := by
    intro p
    simpa only [Function.comp_apply, momentFamily] using trailingDimension_code a (pairFst p)
  modulus_eq := by
    intro p
    simpa only [Function.comp_apply, momentFamily] using a.modulus_eq (pairFst (pairFst p))
  exponent_eq := by
    intro p
    simpa only [Function.comp_apply, momentFamily] using momentExponent_code a (pairFst p)
  degree_eq := by
    intro p
    simpa only [Function.comp_apply, momentFamily, BinaryNatCode.encode] using BinaryNat.normalize_eq_bits (pairSnd p)
  row_eq := by
    intro p j d
    change Fin (trailingDimension F (pairFst p)) at j
    have hj := j.isLt
    have hs : stage F (pairFst p) < F.dimension (pairFst (pairFst p)) := by
      dsimp only [trailingDimension] at hj; omega
    have hv : stage F (pairFst p) + 1 + j.val < F.dimension (pairFst (pairFst p)) := by
      dsimp only [trailingDimension] at hj; omega
    simp only [Function.comp_apply, rowInput, vectorBase, pairFst_pair, pairSnd_pair,
      EntryAccess.rowInput_code a.dimension (pairFst p) (stage F (pairFst p)) j.val (stage_code a (pairFst p)),
      attachDegree]
    have h := a.entry_eq (pairFst (pairFst p)) ⟨stage F (pairFst p), hs⟩
      ⟨stage F (pairFst p) + 1 + j.val, hv⟩ d
    simpa only [momentFamily] using h
  column_eq := by
    intro p i d
    change Fin (trailingDimension F (pairFst p)) at i
    have hi := i.isLt
    have hs : stage F (pairFst p) < F.dimension (pairFst (pairFst p)) := by
      dsimp only [trailingDimension] at hi; omega
    have hv : stage F (pairFst p) + 1 + i.val < F.dimension (pairFst (pairFst p)) := by
      dsimp only [trailingDimension] at hi; omega
    simp only [Function.comp_apply, columnInput, vectorBase, pairFst_pair, pairSnd_pair,
      EntryAccess.columnInput_code a.dimension (pairFst p) (stage F (pairFst p)) i.val (stage_code a (pairFst p)),
      attachDegree]
    have h := a.entry_eq (pairFst (pairFst p))
      ⟨stage F (pairFst p) + 1 + i.val, hv⟩ ⟨stage F (pairFst p), hs⟩ d
    simpa only [momentFamily] using h
  entry_eq := by
    intro p i j d
    change Fin (trailingDimension F (pairFst p)) at i j
    have hi : stage F (pairFst p) + 1 + i.val < F.dimension (pairFst (pairFst p)) := by
      have h := i.isLt; dsimp only [trailingDimension] at h; omega
    have hj : stage F (pairFst p) + 1 + j.val < F.dimension (pairFst (pairFst p)) := by
      have h := j.isLt; dsimp only [trailingDimension] at h; omega
    simp only [Function.comp_apply, matrixInput, matrixBase, pairFst_pair, pairSnd_pair,
      EntryAccess.matrixInput_code a.dimension (pairFst p) (stage F (pairFst p)) i.val j.val (stage_code a (pairFst p)),
      attachDegree]
    have h := a.entry_eq (pairFst (pairFst p))
      ⟨stage F (pairFst p) + 1 + i.val, hi⟩ ⟨stage F (pairFst p) + 1 + j.val, hj⟩ d
    simpa only [momentFamily] using h

theorem moment_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.momentAccess.ControlsPolyTime := by
  have hd := mem_FP_comp pairFst_mem_FP (QueryBits.remaining_mem_FP ha.dimension)
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) ha.modulus
  have he := mem_FP_comp pairFst_mem_FP (QueryBits.momentExponent_mem_FP ha.dimension)
  have hk := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  constructor
  · simpa only [momentAccess] using hd
  · simpa only [momentAccess, Function.comp_def] using hm
  · simpa only [momentAccess] using he
  · simpa only [momentAccess] using hk

theorem momentEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceFunction (momentFamily F).value := by
  have R := E.precompose (rowInput a.dimension) (rowInput_mem_FP ha.dimension)
  have C := E.precompose (columnInput a.dimension) (columnInput_mem_FP ha.dimension)
  have A := E.precompose (matrixInput a.dimension) (matrixInput_mem_FP ha.dimension)
  exact PolynomialMoment.ModularAccess.evaluator a.momentAccess (moment_controls a ha) R C A

end ModularAccess
end LeanCanny.Algebra.BerkowitzPolynomial
