/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FullDerivativeTests
public import LeanCanny.CountingHierarchy.FingerprintRootLabelEvaluation
public import LeanCanny.CountingHierarchy.NativeRootLabelBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv

/-! # Native prescribed-root labels from implicitly addressed coefficients -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def prescribedRootLabelResidue (p D b mu gamma z : ℕ) (target : ℤ)
    (c : ℕ → ℕ) : ℕ :=
  fingerprintLabelResidue p (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (1 + D * mu)) D mu gamma (target % (p : ℤ)).toNat
    (fullDerivativeTestResidue p D z c)

theorem prescribedRootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D b mu gamma z : α → ℕ} {target : α → ℤ} {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hmu : ComputableInPolyTime mu enc encNat)
    (hgamma : ComputableInPolyTime gamma enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (ht : ComputableInPolyTime target enc encIntBin)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => prescribedRootLabelResidue (p w) (D w) (b w) (mu w) (gamma w) (z w) (target w)
      (fun j => c (w, j))) ∈ CountingFunction (max a 3 + 8) enc encNat := by
  have hB := algebraicTestPrecision_polyTime hD hD hb (derivativeTestMassExponent_polyTime hD hb)
  have hs := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 16)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.const 1)
      (ComputableInPolyTime.binary_mul' hD hmu))
  have htarget := ComputableInPolyTime.intBin_emodNat' ht hp
  have hvalues := fullDerivativeTestResidue_mem E hp hD hz hc
  have h := fingerprintLabelResidue_mem E hp hB hs hD hmu hgamma htarget hvalues
  simpa only [prescribedRootLabelResidue, Nat.add_assoc] using h

/-- The modular value is that of the constructed integer label, with no
assumed oracle for a derivative, expanded label, or root sign. -/
theorem prescribedRootLabelResidue_cast {p D : ℕ} [Fact p.Prime] (q : Polynomial ℤ)
    (hD : q.natDegree ≤ D) (hDp : D < p) (b mu gamma z : ℕ) (hmu : mu ≠ 0)
    (target : ℤ) (c : ℕ → ℕ) (hc : ∀ j ≤ D, (c j : ZMod p) = (q.coeff j : ZMod p)) :
    (prescribedRootLabelResidue p D b mu gamma z target c : ZMod p) =
      (fingerprintIntegerRootLabel q 1 D b mu gamma target).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have htarget : ((target % (p : ℤ)).toNat : ZMod p) = (target : ZMod p) := by
    have he : (target % (p : ℤ)).toNat = (target : ZMod p).val := by
      simpa only [Int.toNat_natCast] using (congrArg Int.toNat (ZMod.val_intCast (n := p) target)).symm
    rw [he, ZMod.natCast_zmod_val]
  exact fingerprintLabelResidue_cast _ _ mu gamma hmu (fingerprintTests q 1 D) target _ (z : ZMod p) _
    (fullDerivativeTestResidue_cast q hD hDp z c hc) htarget

end LeanCanny.CountingHierarchy
