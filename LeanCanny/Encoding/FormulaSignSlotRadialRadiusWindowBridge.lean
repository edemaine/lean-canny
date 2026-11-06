/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiIntervalSigns
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadSource
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiOrdinal
/-! # The installed coordinate-head windows have the actual-source formal kernels -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowBridge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev source := FormulaSignSlotRadialRadiusHeadSource.source
noncomputable abbrev centers := FormulaSignSlotRadialRadiusHeadReader.arity
theorem dimension (c : List Bool) : source.arity c = centers c + 1 := rfl

attribute [local irreducible] FormulaSignSlotRadialRadiusHead.polynomial
  FormulaSignSlotRadialEliminantPacked.resultDegree FormulaSignSlotRadialEliminantFormalMass.budget

theorem radius_polynomial (c : List Bool) : IntegralPolynomialRadiusReader.polynomial source centers dimension c =
    FormulaSignSlotRadialRadiusHeadReader.polynomial c := by
  unfold IntegralPolynomialRadiusReader.polynomial IntegralPolynomialRadiusReader.castPolynomial
  have HC : Fin.cast (dimension c) = id := by funext i; exact Fin.ext rfl
  rw [HC, MvPolynomial.rename_id]
  rfl

theorem head_eq (c : List Bool) : IntegralPolynomialWindowTarski.head source centers dimension c =
    FormulaSignSlotRadialRadiusTarskiFamily.head c := by
  unfold IntegralPolynomialWindowTarski.head FormulaSignSlotRadialRadiusTarskiFamily.head
  rw [radius_polynomial]
theorem query_eq (c : List Bool) : IntegralPolynomialWindowTarski.query centers c =
    FormulaSignSlotRadialRadiusTarskiFamily.query c := rfl
theorem degree_eq (c : List Bool) : IntegralPolynomialWindowTarski.degree source c =
    FormulaSignSlotRadialRadiusTarskiFamily.degree c := rfl
theorem bound_eq (c : List Bool) : IntegralPolynomialWindowTarski.bound source c =
    FormulaSignSlotRadialRadiusTarskiFamily.bound c := rfl
theorem seed_degree_eq (c : List Bool) : IntegralPolynomialWindowTarski.seedDegree source c =
    FormulaSignSlotRadialRadiusTarskiFamily.seedDegree c := rfl

theorem seed_eq (c : List Bool) : IntegralPolynomialWindowTarski.seed source centers dimension c =
    FormulaSignSlotRadialRadiusTarskiFamily.seed c := by
  unfold IntegralPolynomialWindowTarski.seed FormulaSignSlotRadialRadiusTarskiFamily.seed
  rw [head_eq, query_eq, degree_eq, bound_eq]

theorem principal_eq (c : List Bool) (j : ℕ) :
    FixedWidthTarskiPrincipalBits.polynomial (IntegralPolynomialWindowTarski.family source centers dimension) c j =
      FixedWidthTarskiPrincipalBits.polynomial FormulaSignSlotRadialRadiusTarskiFamily.family c j := by
  unfold FixedWidthTarskiPrincipalBits.polynomial
  change PrincipalSubresultant.signedPsc (IntegralPolynomialWindowTarski.head source centers dimension c)
    (PseudoRemainder.seed (IntegralPolynomialWindowTarski.head source centers dimension c)
      (IntegralPolynomialWindowTarski.query centers c) (IntegralPolynomialWindowTarski.degree source c)
      (IntegralPolynomialWindowTarski.bound source c)) (IntegralPolynomialWindowTarski.degree source c)
      (IntegralPolynomialWindowTarski.seedDegree source c) j = _
  rw [head_eq, query_eq, degree_eq, bound_eq, seed_degree_eq]
  rfl

noncomputable def oldEntry (q : List Bool) (r j : ℕ) :
    MvPolynomial (Fin (FormulaSignSlotRadialRadiusTarskiFamily.arity q)) ℤ :=
  if r=0 then FixedWidthTarskiPrincipalBits.polynomial FormulaSignSlotRadialRadiusTarskiFamily.family q j
  else if r=1 then (FormulaSignSlotRadialRadiusTarskiFamily.head q).coeff j
  else (FormulaSignSlotRadialRadiusTarskiFamily.seed q).coeff j

theorem entry_eq (q : List Bool) (r j : ℕ) :
    IntegralPolynomialWindowTarski.entryPolynomial source centers dimension q r j = oldEntry q r j := by
  unfold IntegralPolynomialWindowTarski.entryPolynomial oldEntry
  rw [principal_eq, head_eq, seed_eq]
  rfl

def roleWord (r : ℕ) : List Bool := if r=0 then [] else if r=1 then [false] else [true]

theorem kernel_arity (q : List Bool) (r j : ℕ) :
    FormulaSignSlotRadialRadiusTarskiKernelSource.source.arity
      (pair (roleWord r) (pair q (BinaryNatCode.encode j))) = IntegralPolynomialWindowTarski.arity centers q := by
  simp only [FormulaSignSlotRadialRadiusTarskiKernelSource.source,
    FormulaSignSlotRadialRadiusTarskiKernelSource.payload, FormulaSignSlotRadialRadiusTarskiSource.arity,
    FormulaSignSlotRadialRadiusTarskiSource.original, pairSnd_pair, pairFst_pair]
  rfl

attribute [local irreducible] IntegralPolynomialWindowTarski.head IntegralPolynomialWindowTarski.seed
  FormulaSignSlotRadialRadiusTarskiFamily.head FormulaSignSlotRadialRadiusTarskiFamily.seed
  FixedWidthTarskiPrincipalBits.polynomial FormulaSignSlotSource.dimension

private theorem principal_context_heq (F : FixedWidthTarskiPrincipalBits.Family) (q e : List Bool) (h : q=e) (j : ℕ) :
    HEq (FixedWidthTarskiPrincipalBits.polynomial F q j) (FixedWidthTarskiPrincipalBits.polynomial F e j) := by cases h; rfl
private theorem coefficient_context_heq {n : List Bool → ℕ} (F : (q : List Bool) → Polynomial (MvPolynomial (Fin (n q)) ℤ))
    (q e : List Bool) (h : q=e) (j : ℕ) : HEq ((F q).coeff j) ((F e).coeff j) := by cases h; rfl

theorem kernel_packet (q : List Bool) (r j : ℕ) :
    HEq (FormulaSignSlotRadialRadiusTarskiKernelSource.polynomial
      (pair (roleWord r) (pair q (BinaryNatCode.encode j))))
      (IntegralPolynomialWindowTarski.entryPolynomial source centers dimension q r j) := by
  rw [entry_eq]
  unfold FormulaSignSlotRadialRadiusTarskiKernelSource.polynomial
  simp only [FormulaSignSlotRadialRadiusTarskiKernelSource.principal,
    FormulaSignSlotRadialRadiusTarskiKernelSource.headOnly, FormulaSignSlotRadialRadiusTarskiKernelSource.payload,
    FormulaSignSlotRadialRadiusTarskiSource.polynomial, FormulaSignSlotRadialRadiusTarskiSource.original,
    FormulaSignSlotRadialRadiusTarskiSource.order, FormulaSignSlotRadialRadiusTarskiSelectionSource.polynomial,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases h0 : r=0
  · subst r
    simp [roleWord, oldEntry]
    exact principal_context_heq _ _ q (by rw [pairSnd_pair, pairFst_pair]) j
  · by_cases h1 : r=1
    · subst r
      simp [roleWord, oldEntry]
      exact coefficient_context_heq FormulaSignSlotRadialRadiusTarskiFamily.head _ q (by rw [pairSnd_pair, pairFst_pair]) j
    · simp [roleWord, oldEntry, h0, h1]
      exact coefficient_context_heq FormulaSignSlotRadialRadiusTarskiFamily.seed _ q (by rw [pairSnd_pair, pairFst_pair]) j

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowBridge
