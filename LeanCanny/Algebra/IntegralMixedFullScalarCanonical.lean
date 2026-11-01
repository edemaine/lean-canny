/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarCurrent
/-! # Canonical residue outputs of the full scalar dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

private theorem choose_canonical (M N : Machine) (m : ℕ) (q : List Bool)
    (hm : ∃ z : ZMod m, residueBits z = M.model q) (hn : ∃ z : ZMod m, residueBits z = N.model q) :
    ∃ z : ZMod m, residueBits z = (M.choose N).model q := by
  change ∃ z : ZMod m, residueBits z = if M.selected q then M.model q else N.model q
  split_ifs <;> assumption

theorem denominator_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (denominator P a D h).model q :=
  choose_canonical _ _ _ q ⟨_, rfl⟩ ⟨_, rfl⟩

theorem scalar_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (k : Kind) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (scalar P a D h k).model q :=
  choose_canonical _ _ _ q (IntegralMixedPhysicalNativeScalarBits.value_canonical P (physicalFamily P D) k q)
    (IntegralMixedVirtualContextScalarBits.value_canonical P (virtualFamily P D) (virtualKind k) q)

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    ((leading P a D h).choose ((denominator P a D h).choose ((oldHeight P a D h).choose
      ((scalar P a D h .commonLeading).choose ((height P a D h).choose ((scalar P a D h .originalScale).choose zero)))))).model q
  apply choose_canonical _ _ _ q (IntegralMixedFullScalarLeadingBits.canonical P D q)
  apply choose_canonical _ _ _ q (denominator_canonical P a D h q)
  apply choose_canonical _ _ _ q (IntegralMixedOldHeightBits.value_canonical P D q)
  apply choose_canonical _ _ _ q (scalar_canonical P a D h .commonLeading q)
  apply choose_canonical _ _ _ q (IntegralMixedNativeHeightBits.model_canonical P D q)
  exact choose_canonical _ _ _ q (scalar_canonical P a D h .originalScale q) ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedFullScalarBits
