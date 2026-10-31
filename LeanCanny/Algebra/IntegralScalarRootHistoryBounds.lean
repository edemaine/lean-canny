/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryGlobalHeightBounds
public import LeanCanny.Algebra.IntegralScalarRootHeightBank
public import LeanCanny.Algebra.IntegralClearedCriticalLeadingCoefficient

/-! # Uniform bounds for histories of scalar-root height representations

Every new numerator is the actual monic scalar generator; its denominator
is the constructed critical polynomial's nonzero integer top coefficient.
The same global height budget controls these banks, and all retained
numerators are exactly the current prefix's canonical generators.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarRootHistoryBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralHistoryCriticalBits IntegralHistoryGlobalHeightBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def degree (F : Family) (c : List Bool) : ℕ := PurePowerReductionBounds.dimension (F.free c + 1) (F.data c).degree

inductive History (n W D C : ℕ) : {S B m : ℕ} → (P : Prefix S (2 ^ B) m) → HeightBank P → Prop
  | base (S B : ℕ) : History n W D C (UniformIntegralPrefix.base S (2 ^ B)) (HeightBank.base S B)
  | step (F : Family) (c : List Bool) (bank : HeightBank (F.scalarPrefix c))
      (previous : History n W D C (F.scalarPrefix c) bank)
      (select : Fin (F.ambient c + 1) → Option (Fin (F.birth c)))
      (heights : ∀ i, (F.data c).heights i = bank.selectedNumerator (select i))
      (scales : ∀ i, (F.data c).scales i = bank.selectedDenominator (select i))
      (hC : ∀ e, ((F.data c).low.coeff e).natAbs ≤ 2 ^ C)
      (hP : ((F.data c).leading).natAbs ≤ 2 ^ C)
      (hn : F.ambient c + 1 ≤ n) (hW : F.sourceWidth c ≤ W) (hD : (F.data c).degree ≤ D)
      (hdegree : degree F c ≤ 2 ^ F.width c) :
      History n W D C
        (UniformIntegralPrefix.step (F.scalarPrefix c) (F.data c).birth_bound (Nat.two_pow_pos (F.width c))
          (show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c) (degree F c))
        (bank.rootStep (F.data c).birth_bound
          (show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c) (degree F c)
          (IntegralClearedCriticalLeadingBits.integer (source F) c))

theorem History.bounds {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) : bank.Bounds (height n (count S B) W D (2 ^ B) C m) := by
  induction history with
  | base S B => exact HeightBank.base_bounds S B _
  | step F c bank previous select heights scales hC hP hn hW hD hdegree ih =>
    let M := count (F.cap c) (F.width c)
    let T := height n M W D (2 ^ F.width c) C (F.birth c)
    have HT : 1 ≤ T := height_pos _ _ _ _ _ _ _
    have HC : C ≤ T := source_le_height _ _ _ _ _ _ _
    let H : Bounds (freeze F c) := bankBounds (freeze F c) (fun _ => bank) (fun _ => T)
      (fun _ => C) (fun _ => C) (fun _ => ih) (fun _ => select)
      (fun _ => heights) (fun _ => scales) (fun _ => hC) (fun _ => hP)
    have HR : count (F.birth c) (F.width c) ≤ M := rank_cap (F.data c).birth_bound
    have HK : heightFactor (freeze F c) [] ≤ criticalFactor n M W D :=
      heightFactor_le (freeze F c) [] n M W D hn HR hW hD
    have HB : budget (freeze F c) H [] ≤ criticalFactor n M W D * T :=
      (budget_scaled (freeze F c) H [] T HT HC (by exact le_rfl) (by exact le_rfl) HC).trans
        (Nat.mul_le_mul_right T HK)
    have HP (k : ℕ) (r t : Fin (count (F.birth c) (F.width c))) :
        (Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis
          ((show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c).coeff k) r t).natAbs ≤
            2 ^ budget (freeze F c) H [] := by
      have HE := coefficient_height (freeze F c) H [] k r t
      rw [freeze_annihilator] at HE
      exact HE
    have HZ := IntegralClearedCriticalLeadingBits.integer_height (source F) c (budget (freeze F c) H []) HP
    rw [height_step]
    exact bank.rootStep_scaled_bounds (F.data c).birth_bound _ (degree F c) (budget (freeze F c) H []) T M
      (criticalFactor n M W D) _ ih HT HR HB HP HZ

theorem History.generators {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) (i : Fin m) : bank.numerator i = P.basis.generator i := by
  induction history with
  | base S B => exact Fin.elim0 i
  | step F c bank previous select heights scales hC hP hn hW hD hdegree ih =>
    exact bank.rootStep_generators (F.data c).birth_bound _ (degree F c) _ ih i

theorem integer_nonzero (F : Family) (c : List Bool) : IntegralClearedCriticalLeadingBits.integer (source F) c ≠ 0 := by
  apply IntegralClearedCriticalLeadingBits.integer_ne_zero
  · exact (F.data c).leading_ne
  · exact CoordinateFrozenCriticalElimination.denominator_ne_zero (F.data c).scales (F.data c).scales_ne
  · have := (F.data c).degree_two
    change (F.data c).degree ≠ 0
    omega

theorem History.denominators_ne_zero {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) (i : Fin m) : bank.denominator i ≠ 0 := by
  induction history with
  | base S B => exact Fin.elim0 i
  | step F c bank previous select heights scales hC hP hn hW hD hdegree ih =>
    exact bank.rootStep_denominator_ne_zero (F.data c).birth_bound _ (degree F c) _ (integer_nonzero F c) ih i

theorem History.birth_bound {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) : m ≤ S + 1 := by
  cases history with
  | base S B => exact Nat.zero_le _
  | step F c bank previous select heights scales hC hP hn hW hD hdegree =>
    exact Nat.add_le_add_right (F.data c).birth_bound 1

theorem History.uniform_bounds {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : History n W D C P bank) : bank.Bounds (height n (count S B) W D (2 ^ B) C (S + 1)) :=
  history.bounds.mono (height_mono _ _ _ _ _ _ history.birth_bound)

end LeanCanny.Algebra.IntegralScalarRootHistoryBounds
