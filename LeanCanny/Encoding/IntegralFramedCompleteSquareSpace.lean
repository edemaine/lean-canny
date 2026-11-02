/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.IntegralMixedFramedRowSpace

/-! # Actual complete-square row access from creating-companion space

The reader selects the actual newest-first prefix row and preserves its
literal original creating source. Whole-system heterogeneous snapshots
transport only variable counts and row indices, with no row agreement input.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCompleteSquare
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedStepHeight IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem system_apply_heq {a b : ℕ} (hab : a=b)
    (f : Fin a→MvPolynomial (Fin a) ℤ) (g : Fin b→MvPolynomial (Fin b) ℤ) (hfg : HEq f g)
    (i : Fin a) (j : Fin b) (hij : i.val=j.val) : HEq (f i) (g j) := by
  cases hab
  cases hfg
  have HI : i=j := Fin.ext hij
  cases HI
  rfl

private theorem coefficient_heq {a b : ℕ} (hab : a=b)
    (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ) (hpq : HEq p q) (V r M : ℕ) :
    residueBits ((p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin a)) V r) : ℤ) : ZMod M)=
    residueBits ((q.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin b)) V r) : ℤ) : ZMod M) := by
  cases hab
  cases hpq
  rfl

theorem row_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u))
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H))) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input P D H L F C h key hpos)) := by
  let Q := input P D H L F C h key hpos
  let keyQ := key ∘ SquareSampleInput.source
  have HK : keyQ∈FP := mem_FP_comp SquareSampleInput.source_FP hk
  have HQpos : ∀ q,0<IntegralMixedFramedRowBits.count P keyQ q := fun q=>
    (hpos (SquareSampleInput.source q)).trans_eq (family_birth P D H (key (SquareSampleInput.source q)))
  have HE := IntegralMixedFramedRowBits.polynomial_evaluator P a D H keyQ SquareSampleInput.indexWord
    SquareSampleInput.rankWord SquareSampleInput.modulusWord HQpos
    (fun q=>(SquareSampleInput.widthWord q).length) HK SquareSampleInput.indexWord_FP
    (UnaryFn.length SquareSampleInput.widthWord_FP) SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP E
  apply HE.congr
  funext q
  let u := SquareSampleInput.source q
  let i := IntegralMixedFramedRowBits.selectedIndex P D H keyQ SquareSampleInput.indexWord HQpos q
  have HC : IntegralMixedFramedRowBits.count P keyQ q=Q.count u := (family_birth P D H (key u)).symm
  have HC' : Q.count u=(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key u) := rfl
  have HI : (SquareSampleInput.selected Q u (SquareSampleInput.indexWord q)).val=i.val := by
    change min (Nat.fromBitsLE (SquareSampleInput.indexWord q)) (Q.count u-1)=
      IntegralMixedFramedRowBits.selected P keyQ SquareSampleInput.indexWord q
    rw [←HC]
    rfl
  have HS := system_apply_heq HC' (Q.system u)
    (((IntegralMixedFramedHistoryFamilyBits.family P D H).state (key u)).sampler.scalarPrefix.rows)
    (rows_heq P D H L F C h key hpos u) (SquareSampleInput.selected Q u (SquareSampleInput.indexWord q)) i HI
  have HP := IntegralMixedFramedRowBits.polynomial_actual P D H keyQ SquareSampleInput.indexWord HQpos q
  have HV := coefficient_heq HC _ _ (HP.trans HS.symm) (SquareSampleInput.widthWord q).length
    (Nat.fromBitsLE (SquareSampleInput.rankWord q)) (Nat.fromBitsLE (SquareSampleInput.modulusWord q)+1)
  exact HV

end LeanCanny.Encoding.IntegralFramedCompleteSquare
