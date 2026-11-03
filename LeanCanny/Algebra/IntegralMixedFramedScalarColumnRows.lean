/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarRows
/-! # Native scalar columns injectively rename the literal prefix rows -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open IntegralMixedHistory IntegralMixedFullHistoryScript MvPolynomial
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedHeaderTablesBits (Tables)
open LeanCanny.Encoding IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem old_injective {n B : ℕ} {P : SpatialSource n} {ι : Type} (c : Command P B) :
    Function.Injective (old (ι:=ι) c) := by
  cases c with
  | integer=>exact Sum.inl_injective
  | critical=>exact Sum.inl_injective.comp Sum.inl_injective
  | cut=>exact Sum.inl_injective

private theorem fresh_not_old {n B : ℕ} {P : SpatialSource n} {ι : Type} (c : Command P B) (i : ι) :
    old c i≠fresh c := by
  cases c <;> intro h <;> cases h

theorem scalarSlot_injective {n B : ℕ} (cs : List (Instruction n B)) : Function.Injective (scalarSlot cs) := by
  induction cs with
  | nil=>intro i; exact Fin.elim0 i
  | cons c cs ih=>
    change Function.Injective (Fin.cons (fresh c.command) (fun j=>old c.command (scalarSlot cs j)))
    apply Fin.cons_injective_of_injective
    · rintro ⟨i,hi⟩
      exact fresh_not_old c.command _ hi
    · exact (old_injective c.command).comp ih

theorem family_scalar_injective (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Function.Injective ((family P D H).state key).sampler.scalar := by
  rw [family_scalar]
  exact scalarSlot_injective _

noncomputable def nativeScalarColumn (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool)
    (i : Fin (commands P D key).length) : Fin (arity (commands P D key)) :=
  ⟨scalarColumn P T (pair key (BinaryNatCode.encode i.val)),by
    rw [scalarColumn_actual P D H T hr key i]
    exact (enumerate _ _).isLt⟩

theorem nativeScalarColumn_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) :
    nativeScalarColumn P D H T hr key=(enumerate (commands P D key))∘((family P D H).state key).sampler.scalar := by
  funext i
  apply Fin.ext
  exact scalarColumn_actual P D H T hr key i

theorem nativeScalarColumn_injective (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) :
    Function.Injective (nativeScalarColumn P D H T hr key) := by
  rw [nativeScalarColumn_eq]
  exact (enumerate _).injective.comp (family_scalar_injective P D H key)

theorem native_scalar_row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool)
    (i : Fin (commands P D key).length) :
    PolynomialSystemReindex.system (enumerate (commands P D key)) ((family P D H).state key).sampler.rows
      (nativeScalarColumn P D H T hr key i)=
      rename (nativeScalarColumn P D H T hr key) (((family P D H).state key).sampler.scalarPrefix.rows i) := by
  rw [nativeScalarColumn_eq]
  exact indexed_scalar_row P D H key i
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
