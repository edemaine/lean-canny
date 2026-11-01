/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalStateEntry
public import LeanCanny.Algebra.IntegralCriticalScriptHeightBridge

/-! # Height entries with their actual carrier and basis packaged together -/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false

noncomputable def Prefix.elementEntry {S B m : ℕ} (P : Prefix S (2 ^ B) m) (x : P.carrier)
    (r t : Fin (count m B)) (modulus : ℕ) : List Bool :=
  residueBits ((Algebra.leftMulMatrix P.basis.finBasis x r t : ℤ) : ZMod modulus)

end LeanCanny.Algebra.UniformIntegralPrefix

namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def State.clearedEntry {S B n W D C m : ℕ} (x : State S B n W D C m) (select : ℕ → ℕ)
    (i r t modulus : ℕ) : List Bool :=
  let pick (j : ℕ) : Option (Fin m) := if hj : select j < m then some ⟨select j, hj⟩ else none
  x.scalarPrefix.elementEntry
    (CoordinateFrozenCriticalElimination.numerators
      (fun j : Fin (n + 1) => x.bank.selectedDenominator (pick j.val))
      (fun j => x.bank.selectedNumerator (pick j.val)) i)
    ⟨r % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ modulus

end LeanCanny.Algebra.IntegralCriticalScript

namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
set_option backward.isDefEq.respectTransparency false

noncomputable def heightValue (F : Family) (i r t modulus : ℕ) : List Bool :=
  (F.scalarPrefix []).elementEntry ((original F).height [] i)
    ⟨r % count (F.birth []) (F.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count (F.birth []) (F.width []), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ modulus

end LeanCanny.Algebra.IntegralHistoryCriticalBits

namespace LeanCanny.Algebra.IntegralCriticalScriptHeightBits
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript
set_option backward.isDefEq.respectTransparency false

theorem sourceValue_entry (F : Queries) (c : List Bool) :
    (source F).value c = (state F c).scalarPrefix.elementEntry (cleared F c) (F.row c) (F.col c) (F.modulus c) := by
  unfold CommonHeightBits.Source.value
  dsimp only [source]
  rw [← cleared_eq]
  rfl

theorem sourceValue_clearedEntry (F : Queries) (c : List Bool) :
    (source F).value c = (state F c).clearedEntry (F.selector c) (F.coordinate c)
      (F.row c).val (F.col c).val (F.modulus c) := by
  rw [sourceValue_entry]
  unfold State.clearedEntry
  simp only [Nat.mod_eq_of_lt (F.row c).isLt, Nat.mod_eq_of_lt (F.col c).isLt]
  rfl

end LeanCanny.Algebra.IntegralCriticalScriptHeightBits

namespace LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript
set_option backward.isDefEq.respectTransparency false

theorem heightValue_entry (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) (i r t modulus : ℕ) :
    (IntegralCriticalScriptHeightBits.state (queries F) c).clearedEntry (selector F c) i r t modulus =
      IntegralHistoryCriticalBits.heightValue (atSource F c) i r t modulus := by
  unfold State.clearedEntry IntegralHistoryCriticalBits.heightValue
  apply congrArg (fun H => (IntegralCriticalScriptHeightBits.state (queries F) c).scalarPrefix.elementEntry H _ _ modulus)
  exact cleared_height_eq F c i

end LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
