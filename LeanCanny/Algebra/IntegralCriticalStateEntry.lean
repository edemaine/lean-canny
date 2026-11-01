/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalCreatingValue
public import LeanCanny.Algebra.IntegralCriticalScriptHeight

/-! # Retained matrix entries with an abstract actual script state

The state packages its dependent carrier and basis. Callers can transport
state inputs without elaborating the entire interpreted polynomial history.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def State.entry {S B n W D C m : ℕ} (x : State S B n W D C m) (i : Option (Fin m))
    (r t : Fin (count m B)) (modulus : ℕ) : List Bool :=
  residueBits ((Algebra.leftMulMatrix x.scalarPrefix.basis.finBasis (x.bank.selectedNumerator i) r t : ℤ) : ZMod modulus)

theorem State.entry_none {S B n W D C m : ℕ} (x : State S B n W D C m)
    (r t : Fin (count m B)) (modulus : ℕ) : x.entry none r t modulus = [] := by
  simp [State.entry, HeightBank.selectedNumerator, map_zero, residueBits, BinaryNatCode.encode]

theorem run_entry {S B n W D C : ℕ} (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length)
    (r t : Fin (count rules.length B)) (modulus : ℕ) :
    (run rules h hN).entry (some i) r t modulus =
      if r.val % count i.val B = t.val % count i.val B then
        IntegralCriticalCreatingBits.value (birthFamily rules h hN i)
          (r.val / count i.val B) (t.val / count i.val B) modulus else [] :=
  IntegralCriticalCreatingBits.retained_value rules h hN i r t modulus

end LeanCanny.Algebra.IntegralCriticalScript

namespace LeanCanny.Algebra.IntegralCriticalScriptHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript
set_option backward.isDefEq.respectTransparency false

theorem rawValue_entry (F : Queries) (c : List Bool) (hc : F.coordinate c < F.ambient c + 1) :
    (source F).rawValue c = (state F c).entry (select F c (F.coordinate c)) (F.row c) (F.col c) (F.modulus c) :=
  rawValue_eq F c hc

end LeanCanny.Algebra.IntegralCriticalScriptHeightBits
