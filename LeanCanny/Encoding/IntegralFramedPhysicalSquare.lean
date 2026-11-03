/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareAccess
public import LeanCanny.Algebra.IntegralMixedFramedFullRowMassControls
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalar
/-! # Complete square sampling of the actual full physical framed history

All scalar, physical and multiplier rows remain in the system. Their
literal degrees and exclusion at infinity come from the actual sampler.
The advertised degree is one plus their sum, so no degree-bound premise
or replacement of the sampler by its scalar prefix is needed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate arity)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def count (P : Parameters) (D : Plan P) (key : List Bool) : ℕ :=arity (commands P D key)
noncomputable def sampler (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : IntegralHistorySampler.Sampler ((family P D H).cap key)
      (2^(family P D H).width key) ((family P D H).birth key) (Fin (count P D key)) :=
  letI : Fintype ((family P D H).physical key):=
    Fintype.ofEquiv (Fin (count P D key)) (enumerate (commands P D key)).symm
  IntegralHistorySampler.reindex ((family P D H).state key).sampler (enumerate (commands P D key))

noncomputable def rowDegree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (j : ℕ) :=if hj : j<count P D key then (sampler P D H key).degrees ⟨j,hj⟩ else 1
noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :=(∑ i : Fin (count P D key),(sampler P D H key).degrees i)+1

theorem rowDegree_at (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin (count P D key)) : rowDegree P D H key i.val=(sampler P D H key).degrees i := by
  unfold rowDegree
  rw [dite_eq_left i.isLt]

theorem degree_pos (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    0<degree P D H key :=Nat.succ_pos _

theorem rowDegree_le (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin (count P D key)) : rowDegree P D H key i.val≤degree P D H key := by
  rw [rowDegree_at]
  exact (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_succ _)

theorem birth_le_count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (family P D H).birth key≤count P D key := by
  change (commands P D key).length≤arity (commands P D key)
  rw [IntegralMixedFramedPhysicalIndex.arity_eq]
  exact Nat.le_add_right _ _

noncomputable def finite (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c)) : NoInfinitySquareSample.Family where
  count c:=count P D (key c)
  degree c:=degree P D H (key c)
  mass c:=IntegralMixedPhysicalRowBudget.familyMass P L F C (pairFst (key c))
  rowDegree c:=rowDegree P D H (key c)
  rows c:=(sampler P D H (key c)).rows
  count_pos c:=(hpos c).trans_le (birth_le_count P D H (key c))
  degree_pos c:=degree_pos P D H (key c)
  row_degree c i:=((sampler P D H (key c)).row_degree i).trans_eq (rowDegree_at P D H (key c) i).symm
  rowDegree_pos c i:=(sampler P D H (key c)).degree_pos i |>.trans_eq (rowDegree_at P D H (key c) i).symm
  rowDegree_le c i:=rowDegree_le P D H (key c) i
  row_mass c i:=by
    change MvMass.mass (MvPolynomial.rename (enumerate (commands P D (key c)))
      (((family P D H).state (key c)).sampler.rows ((enumerate (commands P D (key c))).symm i)))≤_
    exact (MvMass.rename_le _ _).trans (IntegralMixedPhysicalRowBudget.family_mass P D H L F C hs (key c) _)
  noInfinity c:=by
    have HE : (fun i : Fin (count P D (key c))=>rowDegree P D H (key c) i.val)=(sampler P D H (key c)).degrees :=
      funext (rowDegree_at P D H (key c))
    rw [HE]
    exact (sampler P D H (key c)).noInfinity

noncomputable def input (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c)) : SquareSampleInput.Inputs :=
  NoInfinitySquareSample.input (finite P D H L F C hs key hpos)

theorem complete (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c)) :
    SquareSampleComplete.Complete (input P D H L F C hs key hpos) :=NoInfinitySquareSample.complete _

theorem rows_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c)) (c : List Bool) :
    (input P D H L F C hs key hpos).system c=(sampler P D H (key c)).rows :=rfl
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
