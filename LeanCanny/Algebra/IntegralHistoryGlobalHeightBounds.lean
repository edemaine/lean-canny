/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryCriticalBank
public import LeanCanny.Algebra.IntegralCriticalFactorCeiling

/-! # Uniform height budgets across actual critical births

Fix original spatial metadata and a birth cap. The scalar rank is bounded
by the fixed degree to that cap. One factor controls a complete critical
birth, so iterating it keeps the binary length of every height budget
polynomial. Earlier canonical numerators remain embedded in each bank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryGlobalHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralHistoryCriticalBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def criticalFactor (n M W D : ℕ) : ℕ := IntegralCriticalFactorCeiling.factor n M W D * (n + 1)
def growth (n M W D N : ℕ) : ℕ := bankGrowth M N (criticalFactor n M W D)
def height (n M W D N C m : ℕ) : ℕ := growth n M W D N ^ m * (C + 1)

theorem growth_pos (n M W D N : ℕ) : 1 ≤ growth n M W D N := bankGrowth_pos _ _ _

theorem height_pos (n M W D N C m : ℕ) : 1 ≤ height n M W D N C m :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (Nat.ne_of_gt (growth_pos n M W D N))) (by omega))

theorem source_le_height (n M W D N C m : ℕ) : C ≤ height n M W D N C m := by
  have HG : 1 ≤ growth n M W D N ^ m := Nat.one_le_pow _ _ (growth_pos n M W D N)
  exact (Nat.le_succ C).trans (by simpa only [Nat.one_mul, height] using Nat.mul_le_mul_right (C + 1) HG)

theorem height_step (n M W D N C m : ℕ) :
    height n M W D N C (m + 1) = growth n M W D N * height n M W D N C m := by
  unfold height
  rw [pow_succ']
  exact Nat.mul_assoc _ _ _

theorem height_bits (n M W D N C m : ℕ) :
    (height n M W D N C m).size ≤ (growth n M W D N).size * m + (C + 1).size + 1 := by
  have HG : growth n M W D N ^ m ≤ 2 ^ ((growth n M W D N).size * m) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (Nat.lt_size_self (growth n M W D N)).le m
  have HH : height n M W D N C m ≤ 2 ^ ((growth n M W D N).size * m + (C + 1).size) := by
    exact (Nat.mul_le_mul HG (Nat.lt_size_self (C + 1)).le).trans_eq (pow_add _ _ _).symm
  simpa only [Nat.size_pow] using Nat.size_le_size HH

theorem criticalFactor_binary {n M W D : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) : BinaryFn (fun c => criticalFactor (n c) (M c) (W c) (D c)) :=
  (IntegralCriticalFactorCeiling.factor_binary hn hM hW hD).mul ((BinaryFn.ofUnary hn).add (BinaryFn.const 1))

theorem growth_binary {n M W D N : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hN : BinaryFn N) :
    BinaryFn (fun c => growth (n c) (M c) (W c) (D c) (N c)) :=
  bankGrowth_binary hM hN (criticalFactor_binary hn hM hW hD)

theorem height_binary {n M W D N C m : List Bool → ℕ} (hn : UnaryFn n) (hM : BinaryFn M)
    (hW : UnaryFn W) (hD : BinaryFn D) (hN : BinaryFn N) (hC : BinaryFn C) (hm : UnaryFn m) :
    BinaryFn (fun c => height (n c) (M c) (W c) (D c) (N c) (C c) (m c)) :=
  ((growth_binary hn hM hW hD hN).powUnary hm).mul (hC.add (BinaryFn.const 1))

theorem rank_cap {S B m : ℕ} (hm : m ≤ S) : count m B ≤ count S B :=
  Nat.pow_le_pow_right (Nat.two_pow_pos B) hm

theorem heightFactor_le (F : Family) (c : List Bool) (n M W D : ℕ)
    (hn : F.ambient c + 1 ≤ n) (hM : count (F.birth c) (F.width c) ≤ M)
    (hW : F.sourceWidth c ≤ W) (hD : (F.data c).degree ≤ D) : heightFactor F c ≤ criticalFactor n M W D := by
  have HF : F.free c + 1 ≤ n := by have := F.fit c; omega
  have HL := IntegralCriticalFactorCeiling.dimension_mono HF hD
  have HB := IntegralCriticalFactorCeiling.bound_mono HF hD
  have HC := IntegralCriticalFactorCeiling.dominates (source F) c n M W D hn HF hM hW hD HL HB
  exact Nat.mul_le_mul HC (by omega)

noncomputable def freeze (F : Family) (c : List Bool) : Family where
  cap _ := F.cap c
  width _ := F.width c
  birth _ := F.birth c
  ambient _ := F.ambient c
  free _ := F.free c
  scalarPrefix _ := F.scalarPrefix c
  data _ := F.data c
  offset _ := F.offset c
  fit _ := F.fit c
  sourceWidth _ := F.sourceWidth c
  degree_lt _ := F.degree_lt c
  objective _ := F.objective c
  coordinate _ := F.coordinate c
  coefficientIndex _ := F.coefficientIndex c
  target _ := F.target c
  row _ := F.row c
  col _ := F.col c
  modulus _ := F.modulus c
  modulus_ne_zero _ := F.modulus_ne_zero c

theorem freeze_annihilator (F : Family) (c q : List Bool) :
    (source (freeze F c)).annihilator q = (source F).annihilator c := by rfl

/-- Actual critical births with bounded original spatial metadata. No
coefficient or height-budget oracle is stored in the history. -/
inductive CriticalHistory (n W D C : ℕ) : {S B m : ℕ} →
    (P : Prefix S (2 ^ B) m) → HeightBank P → Prop
  | base (S B : ℕ) : CriticalHistory n W D C (UniformIntegralPrefix.base S (2 ^ B)) (HeightBank.base S B)
  | step (F : Family) (c : List Bool) (bank : HeightBank (F.scalarPrefix c))
      (previous : CriticalHistory n W D C (F.scalarPrefix c) bank)
      (select : Fin (F.ambient c + 1) → Option (Fin (F.birth c)))
      (heights : ∀ i, (F.data c).heights i = bank.selectedNumerator (select i))
      (scales : ∀ i, (F.data c).scales i = bank.selectedDenominator (select i))
      (hC : ∀ e, ((F.data c).low.coeff e).natAbs ≤ 2 ^ C)
      (hP : ((F.data c).leading).natAbs ≤ 2 ^ C)
      (hn : F.ambient c + 1 ≤ n) (hW : F.sourceWidth c ≤ W) (hD : (F.data c).degree ≤ D) (d : ℕ) :
      CriticalHistory n W D C
        (UniformIntegralPrefix.step (F.scalarPrefix c) (F.data c).birth_bound (Nat.two_pow_pos (F.width c))
          (show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c) d)
        (bank.step (F.data c).birth_bound
          (show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c) d)

theorem CriticalHistory.bounds {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : CriticalHistory n W D C P bank) :
    bank.Bounds (height n (count S B) W D (2 ^ B) C m) := by
  induction history with
  | base S B => exact HeightBank.base_bounds S B _
  | step F c bank previous select heights scales hC hP hn hW hD d ih =>
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
    rw [height_step]
    exact bank.step_scaled_bounds (F.data c).birth_bound _ d (budget (freeze F c) H []) T M
      (criticalFactor n M W D) ih HT HR HB HP

theorem CriticalHistory.birth_bound {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : CriticalHistory n W D C P bank) : m ≤ S + 1 := by
  cases history with
  | base S B => exact Nat.zero_le _
  | step F c bank previous select heights scales hC hP hn hW hD d =>
    exact Nat.add_le_add_right (F.data c).birth_bound 1

theorem height_mono (n M W D N C : ℕ) {m s : ℕ} (hm : m ≤ s) :
    height n M W D N C m ≤ height n M W D N C s :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (growth_pos n M W D N) hm)

theorem CriticalHistory.uniform_bounds {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (history : CriticalHistory n W D C P bank) :
    bank.Bounds (height n (count S B) W D (2 ^ B) C (S + 1)) :=
  history.bounds.mono (height_mono _ _ _ _ _ _ history.birth_bound)

theorem uniform_height_binary {n W D C S B : List Bool → ℕ} (hn : UnaryFn n) (hW : UnaryFn W)
    (hD : BinaryFn D) (hC : BinaryFn C) (hS : UnaryFn S) (hB : UnaryFn B) :
    BinaryFn (fun c => height (n c) (count (S c) (B c)) (W c) (D c) (2 ^ B c) (C c) (S c + 1)) := by
  have HN : BinaryFn (fun c => 2 ^ B c) := (BinaryFn.const 2).powUnary hB
  exact height_binary hn (HN.powUnary hS) hW hD HN hC (hS.add (UnaryFn.const 1))

end LeanCanny.Algebra.IntegralHistoryGlobalHeightBounds
