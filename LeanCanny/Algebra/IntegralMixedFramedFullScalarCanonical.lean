/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarCurrent
public import LeanCanny.Algebra.IntegralMixedDenominatorCanonical
/-! # Canonical residue outputs of the full scalar dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

private theorem choose_canonical (M N : Machine) (m : ℕ) (q : List Bool)
    (hm : ∃ z : ZMod m, residueBits z = M.model q) (hn : ∃ z : ZMod m, residueBits z = N.model q) :
    ∃ z : ZMod m, residueBits z = (M.choose N).model q := by
  change ∃ z : ZMod m, residueBits z = if M.selected q then M.model q else N.model q
  split_ifs <;> assumption

theorem denominator_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (denominator P a D J h).model q :=
  choose_canonical _ _ _ q
    (IntegralMixedDenominatorCanonicalBits.physical P a (physicalFamily P D J) (physicalInput P a D J h)
      (IntegralMixedFramedPhysicalBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
      (routingAccess P a D J h) h.physicalScales q)
    (IntegralMixedDenominatorCanonicalBits.virtual P a (virtualFamily P D J) (virtualInput P a D J h)
      (IntegralMixedFramedHistoryFamilyBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
      (routingAccess P a D J h) h.virtualScales q)

theorem scalar_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (k : Kind) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (scalar P a D J h k).model q :=
  choose_canonical _ _ _ q (IntegralMixedPhysicalNativeScalarBits.value_canonical P (physicalFamily P D J) k q)
    (IntegralMixedVirtualContextScalarBits.value_canonical P (virtualFamily P D J) (virtualKind k) q)

attribute [local irreducible] IntegralMixedFramedScalarLeadingBits.value
  IntegralMixedFramedOldHeightBits.value IntegralMixedFramedNativeHeightBits.model

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D J h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    ((leading P a D J h).choose ((denominator P a D J h).choose ((oldHeight P a D J h).choose
      ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))))).model q
  exact choose_canonical (leading P a D J h)
    ((denominator P a D J h).choose ((oldHeight P a D J h).choose
      ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))))
    (modulus P q) q (IntegralMixedFramedScalarLeadingBits.canonical P D J q)
    (choose_canonical (denominator P a D J h)
      ((oldHeight P a D J h).choose ((scalar P a D J h .commonLeading).choose
        ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero))))
      (modulus P q) q (denominator_canonical P a D J h q)
      (choose_canonical (oldHeight P a D J h)
        ((scalar P a D J h .commonLeading).choose ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero)))
        (modulus P q) q (IntegralMixedFramedOldHeightBits.value_canonical P D J q)
        (choose_canonical (scalar P a D J h .commonLeading)
          ((height P a D J h).choose ((scalar P a D J h .originalScale).choose zero))
          (modulus P q) q (scalar_canonical P a D J h .commonLeading q)
          (choose_canonical (height P a D J h) ((scalar P a D J h .originalScale).choose zero)
            (modulus P q) q (IntegralMixedFramedNativeHeightBits.model_canonical P D J q)
            (choose_canonical (scalar P a D J h .originalScale) zero (modulus P q) q
              (scalar_canonical P a D J h .originalScale q) ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩)))))
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
