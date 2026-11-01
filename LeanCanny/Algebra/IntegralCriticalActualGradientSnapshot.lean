/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualScalarModels
public import LeanCanny.Algebra.IntegralCriticalActualCaps
/-! # Canonical original and derivative coefficient queries

The creating family fixes the algebra and polynomial. Natural target and
matrix selectors are applied afterward; no abstract source equality is
assumed by the transport lemmas.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualGradientSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

noncomputable def queried (A : IntegralHistoryCriticalBits.Family) (e r t m : ℕ) (hm : m ≠ 0) :=
  IntegralCriticalTotalSnapshotBits.queryAt A 0 e r t m hm
noncomputable def gradient (A : IntegralHistoryCriticalBits.Family) (j e r t m : ℕ) (hm : m ≠ 0) : List Bool := by
  let S := IntegralCriticalActualScalarModels.eulerAt (queried A 0 r t m hm)
  let := S.ring []
  exact residueBits ((Algebra.leftMulMatrix (S.basis [])
    ((IntegralCriticalGradientBits.polynomial S.toGradient []
      (IntegralCriticalActualScalarModels.selectedAt (queried A 0 r t m hm) j [])).coeff
        (RationalSubstitution.Indexed.exponentVector (S.free [])
          (FixedWidthPolynomial.entry (S.targetWidth []) e))) (S.row []) (S.col []) : ℤ) : ZMod m)
noncomputable def original (A : IntegralHistoryCriticalBits.Family) (e r t m : ℕ) (hm : m ≠ 0) :=
  (IntegralCriticalActualScalarModels.eulerAt (queried A e r t m hm)).toGradient.toFrozen.toSource.value []

theorem original_snapshot (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatGridSourceBits.original (IntegralCriticalTotalCreatingBits.euler F)).value q =
      original (IntegralCriticalTotalCreatingBits.atFamily F q)
        (IntegralCriticalHistoryTask.get F.toParameters .target q)
        (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := rfl

theorem gradient_snapshot (F : Scripts) (q : List Bool)
    (j : Fin ((IntegralCriticalTotalCreatingBits.euler F).free q)) (e : ℕ) :
    (IntegralCriticalGradientBits.family (IntegralCriticalTotalCreatingBits.euler F).toGradient).value
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) =
      gradient (IntegralCriticalTotalCreatingBits.atFamily F q) j.val e
        (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  rw [IntegralCriticalGradientBits.packet]
  unfold gradient
  let := (IntegralCriticalTotalCreatingBits.euler F).ring q
  have H : j.val % (IntegralCriticalTotalCreatingBits.euler F).free q = j.val := Nat.mod_eq_of_lt j.isLt
  change _ = residueBits ((Algebra.leftMulMatrix ((IntegralCriticalTotalCreatingBits.euler F).basis q)
    ((IntegralCriticalGradientBits.polynomial (IntegralCriticalTotalCreatingBits.euler F).toGradient q
      ⟨j.val % (IntegralCriticalTotalCreatingBits.euler F).free q, _⟩).coeff
        (RationalSubstitution.Indexed.exponentVector ((IntegralCriticalTotalCreatingBits.euler F).free q)
          (FixedWidthPolynomial.entry ((IntegralCriticalTotalCreatingBits.euler F).targetWidth q) e)))
      ((IntegralCriticalTotalCreatingBits.euler F).row q) ((IntegralCriticalTotalCreatingBits.euler F).col q) : ℤ) :
      ZMod ((IntegralCriticalTotalCreatingBits.euler F).modulus q))
  simp only [H]

theorem gradient_congr (A B : IntegralHistoryCriticalBits.Family) (j e r t m j' e' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hj : j = j') (he : e = e')
    (hr : r = r') (ht : t = t') (hmod : m = m') :
    gradient A j e r t m hm = gradient B j' e' r' t' m' hm' := by
  subst B; subst j'; subst e'; subst r'; subst t'; subst m'
  rfl

theorem original_congr (A B : IntegralHistoryCriticalBits.Family) (e r t m e' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (he : e = e')
    (hr : r = r') (ht : t = t') (hmod : m = m') :
    original A e r t m hm = original B e' r' t' m' hm' := by
  subst B; subst e'; subst r'; subst t'; subst m'
  rfl

end LeanCanny.Algebra.IntegralCriticalActualGradientSnapshot
