/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.BinaryDerivativeTestEvaluation
public import LeanCanny.CountingHierarchy.RootLabelEvaluation
public import LeanCanny.CountingHierarchy.NativeRootLabelBounds

/-! # Native counting certificates for the actual sparse integer root label -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def sparseRootLabelResidue (p D N b z base : ℕ)
    (c : ℕ → ℕ) (orders : List ℕ) (target : ℕ → ℕ) : ℕ :=
  rootLabelResidue p (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (N + 1)) (N + 1)
    (binaryDerivativeTestResidue p D z base c orders) target

/-- An `F_8` coefficient evaluator gives `F_12` sparse-label values.
The test width is unary; source degrees, precisions and derivative orders
are binary. All numeric bounds are computed from the primary instance. -/
theorem sparseRootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D N b z base : α → ℕ} {orders : α → List ℕ}
    {c target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hN : ComputableInPolyTime N enc encUnary)
    (hb : ComputableInPolyTime b enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hbase : base ∈ CountingFunction (max a 3 + 1) enc encNat)
    (horders : ComputableInPolyTime orders enc (encList encNat))
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat)
    (ht : target ∈ CountingFunction (max a 3 + 4) (encPair enc encNat) encNat) :
    (fun w => sparseRootLabelResidue (p w) (D w) (N w) (b w) (z w) (base w)
      (fun j => c (w, j)) (orders w) (fun j => target (w, j))) ∈
        CountingFunction (max a 3 + 4) enc encNat := by
  have hNb := ComputableInPolyTime.unary_to_binary.comp hN
  have hwidth : ComputableInPolyTime (fun w => N w + 1) enc encUnary := by fun_prop
  have hs : ComputableInPolyTime (fun w => 16 * (N w + 1)) enc encNat := by fun_prop
  have hprecision := algebraicTestPrecision_polyTime hD hD hb
    (derivativeTestMassExponent_polyTime hD hb)
  have hvalue := binaryDerivativeTestResidue_mem E hp hD hz hbase horders hc
  have ht' : target ∈ CountingFunction (max a 3 + 1 + 3) (encPair enc encNat) encNat := by
    simpa only [Nat.add_assoc] using ht
  simpa only [sparseRootLabelResidue, Nat.add_assoc] using
    rootLabelResidue_mem E hp hprecision hs hwidth hvalue ht'

/-- Equality with the integer label used in the finite feasibility criterion.
There is no assumption of access to expanded polynomial coefficients. -/
theorem sparseRootLabelResidue_cast {p D N : ℕ} [Fact p.Prime]
    (q b₀ : Polynomial ℤ) (b z base : ℕ) (c target : ℕ → ℕ)
    (L : List (Fin D × SignType)) (hD : q.natDegree ≤ D) (hprime : D < p)
    (hc : ∀ j ≤ D, (c j : ZMod p) = (q.map (Int.castRingHom (ZMod p))).coeff j)
    (hbase : (base : ZMod p) = b₀.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p))
    (ht : ∀ i : Fin (N + 1), (target i.val : ZMod p) =
      ((derivativeLabelTargets N L i : ℤ) : ZMod p)) :
    (sparseRootLabelResidue p D N b z base c (L.map (fun t => t.1.val + 1)) target : ZMod p) =
      (sparseIntegerRootLabel q b₀ N b L).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  exact rootLabelResidue_cast _ _ (derivativeLabelTests q b₀ N L)
    (derivativeLabelTargets N L) (z : ZMod p) _ target
    (fun i => binaryDerivativeTestResidue_cast q b₀ z base c L hD hprime hc hbase i) ht

end LeanCanny.CountingHierarchy
