/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueFactorNative
/-! # Natural old-basis coefficient entries of the actual relative value factor

One formal digit recovers the coefficient of the same relative value cut.
Both finite address guards are retained, independently of scalar choice
validation. No coefficient evaluator is an argument to these identities.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueCoefficientSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedValueDoubleNilpotent IntegralCoordinateBasis
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedCutNilpotent.value

def scalarChoice (F : Family) (key : List Bool) (c : ℕ) :
    Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial key) (F.rule key)) :=
  ⟨c % IntegralMixedValueTrailing.ChoiceBound (F.spatial key) (F.rule key), Nat.mod_lt _ (by change 0 < _ + 2; omega)⟩
noncomputable def kind (F : Family) (key : List Bool) (j c : ℕ) :=
  IntegralMixedRelativeCuts.Kind.value ((IntegralMixedValueHomogeneousSnapshot.pointIndices F j).coordinate key)
    (scalarChoice F key c)

def index (F : Family) (key : List Bool) (r : ℕ) : Fin (count (F.birth key + 1) (F.width key)) :=
  ⟨r % count (F.birth key + 1) (F.width key), Nat.mod_lt _ (Nat.pow_pos (Nat.two_pow_pos _))⟩
noncomputable def first (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state key)).finBasis
    (IntegralMixedCutNilpotent.value (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c))
    (index F key r) (index F key t)
noncomputable def coefficient (F : Family) (key : List Bool) (j c k r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k) r t

theorem first_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueFactorValue.value P F q = residueBits
      (first F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := rfl

theorem first_coefficient (F : Family) (key : List Bool) (j c : ℕ)
    (i t : Fin (count (F.birth key) (F.width key))) (k : Fin (2 ^ F.width key)) :
    first F key j c (k.val + 2 ^ F.width key * i.val) (2 ^ F.width key * t.val) =
      coefficient F key j c k.val i.val t.val := by
  let r := pairIndex (F.birth key) (F.width key) (i, k)
  let s := pairIndex (F.birth key) (F.width key) (t, 0)
  have HI : index F key r.val = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have HT : index F key s.val = s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have HE : first F key j c r.val s.val =
      IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key)
        (kind F key j c) k.val i t := by
    unfold first
    rw [HI, HT]
    exact IntegralMixedCutNilpotent.coefficient (F.state key) (F.birth_bound key) (F.rule key)
      (kind F key j c) (F.scalar_cap key) k i t
  have HB := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (kind F key j c) k.val) i t
  simpa only [r, s, IntegralMixedCutNilpotent.pairIndex_value, Fin.val_zero, Nat.zero_add, coefficient] using HE.trans HB.symm

theorem coefficient_zero (F : Family) (key : List Bool) (j c k r t : ℕ)
    (hk : 2 ^ F.width key ≤ k) : coefficient F key j c k r t = 0 := by
  have HZ := IntegralMixedCutNilpotent.coefficient_outside (F.state key) (F.birth_bound key)
    (F.rule key) (kind F key j c) (F.scalar_cap key) k hk
  unfold coefficient
  rw [HZ]
  simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite, ite_self]

end LeanCanny.Algebra.IntegralMixedValueCoefficientSnapshot
