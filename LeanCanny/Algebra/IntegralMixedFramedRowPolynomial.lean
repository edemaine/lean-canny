/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedRowQuery

/-! # Every actual prefix row is its original creating row in an old block

The youngest variables outside that block are absent. Exact source-cell
transport identifies the creating monic row, and persistent prefix chains
identify its embedding with the original newest-first row index.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript IntegralMixedFramedCompanionBits
open MvPolynomial BlockRenameCoefficient
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selectedIndex (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (hpos : ∀ q,0<count P key q) (q : List Bool) :
    Fin ((bank P D H).birth (key q)) :=
  ⟨selected P key index q,(selected_lt P key index q (hpos q)).trans_eq
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H (key q)).symm⟩

theorem row_fit (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (hpos : ∀ q,0<count P key q) (q : List Bool) :
    selected P key index q+((source P D H).arity (creatorKey P key index q)+1)≤count P key q := by
  rw [creator_arity]
  unfold birth
  have HI:=selected_lt P key index q (hpos q)
  omega

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (hpos : ∀ q,0<count P key q) (q : List Bool) :
    MvPolynomial (Fin (count P key q)) ℤ :=
  rename (BlockRenameCoefficient.shift ((source P D H).arity (creatorKey P key index q)+1)
    (count P key q) (selected P key index q) (row_fit P D H key index hpos q))
    (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1) (creatorKey P key index q))

private theorem rename_block_heq {a b A B O : ℕ} (ha : a=b) (hA : A=B)
    (hfit : O+a≤A) (hfit' : O+b≤B) (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hp : HEq p q) :
    HEq (rename (BlockRenameCoefficient.shift a A O hfit) p)
      (rename (BlockRenameCoefficient.shift b B O hfit') q) := by
  cases ha
  cases hA
  cases hp
  rfl

attribute [local irreducible] PaddedIntegralRowBits.polynomial

theorem polynomial_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (hpos : ∀ q,0<count P key q) (q : List Bool) :
    HEq (polynomial P D H key index hpos q)
      (((bank P D H).state (key q)).sampler.scalarPrefix.rows (selectedIndex P D H key index hpos q)) := by
  let cs := IntegralMixedFramedHistoryFamilyBits.commands P D (key q)
  let i := selectedIndex P D H key index hpos q
  have hcs : cs.length≤P.cap (pairFst (key q))+1+1 :=
    ((bank P D H).birth_bound (key q)).trans (Nat.le_succ _)
  let o := origin (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (key q))) cs hcs i
  have HM : count P key q=cs.length :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H (key q)).symm
  have HN : (source P D H).arity (creatorKey P key index q)+1=(older cs i).length+1 := by
    rw [creator_arity]
    have HO:=older_length cs i
    change (count P key q-1-selected P key index q)+1=(older cs i).length+1
    change (older cs i).length=cs.length-1-selected P key index q at HO
    omega
  have HF : selected P key index q+((older cs i).length+1)≤cs.length := by
    have HO:=older_length cs i
    have HI:=i.isLt
    change selected P key index q<cs.length at HI
    change (older cs i).length=cs.length-1-selected P key index q at HO
    omega
  have HP := source_creator_row P D H (key q) i []
  have HR := rename_block_heq HN HM (row_fit P D H key index hpos q) HF _ _ HP
  have HE : BlockRenameCoefficient.shift ((older cs i).length+1) cs.length (selected P key index q) HF=
      UniformIntegralPowerSchedule.embed o.chain.le := by
    funext j
    apply Fin.ext
    change selected P key index q+j.val=cs.length-((older cs i).length+1)+j.val
    have HO:=older_length cs i
    have HI:=i.isLt
    change (older cs i).length=cs.length-1-selected P key index q at HO
    change selected P key index q<cs.length at HI
    omega
  rw [HE,←o.row] at HR
  exact HR

end LeanCanny.Algebra.IntegralMixedFramedRowBits
