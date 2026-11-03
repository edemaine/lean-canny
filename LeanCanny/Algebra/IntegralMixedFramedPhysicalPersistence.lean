/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowSelector

/-! # Full physical rows retain their creating equations and degrees

Later scalar and critical births rename every old physical equation. The
explicit oldest-first enumeration keeps its raw column number unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript (Instruction Index run)
open IntegralMixedFramedPhysicalIndex (old enumerate)
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem step_rows_old {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B) (i : ι) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.rows (old c i)=rename (old c) (x.sampler.rows i) := by
  cases c with
  | integer=>rfl
  | critical r=>
    change rename Sum.inl (rename Sum.inl (x.sampler.rows i))=
      rename (Sum.inl∘Sum.inl) (x.sampler.rows i)
    rw [rename_rename]
  | cut=>rfl

theorem step_degrees_old {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B) (i : ι) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.degrees (old c i)=x.sampler.degrees i := by
  cases c <;> rfl

def embed {n B : ℕ} : (newer older : List (Instruction n B))→Index (Fin 0) older→Index (Fin 0) (newer++older)
  | [],_=>id
  | c::cs,older=>old c.command∘embed cs older

theorem enumerate_embed {n B : ℕ} (newer older : List (Instruction n B)) (i : Index (Fin 0) older) :
    (enumerate (newer++older) (embed newer older i)).val=(enumerate older i).val := by
  induction newer with
  | nil=>rfl
  | cons c cs ih=>
    exact (IntegralMixedFramedPhysicalIndex.step_old c.command (enumerate (cs++older)) _).trans ih

theorem run_rows_embed {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1) (i : Index (Fin 0) older) :
    (run initial (newer++older) h).sampler.rows (embed newer older i)=
      rename (embed newer older) ((run initial older ho).sampler.rows i) := by
  induction newer with
  | nil=>simp only [List.nil_append,embed,rename_id]; rfl
  | cons c cs ih=>
    have HC : (cs++older).length≤S+1 := by simp only [List.cons_append,List.length_cons] at h; omega
    have HM : (cs++older).length≤S := by simp only [List.cons_append,List.length_cons] at h; omega
    have HX:=step_rows_old (reframe (run initial (cs++older) HC) c.source c.source_cap) HM c.command (embed cs older i)
    change (run initial ((c::cs)++older) h).sampler.rows (embed (c::cs) older i)=
      rename (old c.command) ((run initial (cs++older) HC).sampler.rows (embed cs older i)) at HX
    rw [HX,ih HC,rename_rename]
    rfl

theorem run_degrees_embed {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1) (i : Index (Fin 0) older) :
    (run initial (newer++older) h).sampler.degrees (embed newer older i)=
      (run initial older ho).sampler.degrees i := by
  induction newer with
  | nil=>rfl
  | cons c cs ih=>
    have HC : (cs++older).length≤S+1 := by simp only [List.cons_append,List.length_cons] at h; omega
    have HM : (cs++older).length≤S := by simp only [List.cons_append,List.length_cons] at h; omega
    have HX:=step_degrees_old (reframe (run initial (cs++older) HC) c.source c.source_cap) HM c.command (embed cs older i)
    exact HX.trans (ih HC)

theorem run_old_roots {n S B : ℕ} {P : SpatialSource n} {K : Type*} [CommRing K]
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1)
    (z : Index (Fin 0) (newer++older)→K)
    (hz : ∀i,((run initial (newer++older) h).sampler.rows i).eval₂ (Int.castRingHom K) z=0) :
    ∀i,((run initial older ho).sampler.rows i).eval₂ (Int.castRingHom K) (z∘embed newer older)=0 := by
  intro i
  have HI:=hz (embed newer older i)
  rw [run_rows_embed initial newer older h ho i,eval₂_rename] at HI
  exact HI


theorem arity_append {n B : ℕ} (newer older : List (Instruction n B)) :
    IntegralMixedFramedPhysicalIndex.arity (newer++older)=
      IntegralMixedFramedPhysicalIndex.arity older+IntegralMixedFramedPhysicalIndex.arity newer := by
  induction newer with
  | nil=>simp only [List.nil_append,IntegralMixedFramedPhysicalIndex.arity,Nat.add_zero]
  | cons c cs ih=>
    simp only [List.cons_append,IntegralMixedFramedPhysicalIndex.arity,ih]
    omega

theorem arity_le_append {n B : ℕ} (newer older : List (Instruction n B)) :
    IntegralMixedFramedPhysicalIndex.arity older≤IntegralMixedFramedPhysicalIndex.arity (newer++older) := by
  rw [arity_append]
  omega

theorem enumerate_symm_castLE {n B : ℕ} (newer older : List (Instruction n B))
    (i : Fin (IntegralMixedFramedPhysicalIndex.arity older)) :
    (enumerate (newer++older)).symm (Fin.castLE (arity_le_append newer older) i)=
      embed newer older ((enumerate older).symm i) := by
  apply (enumerate (newer++older)).injective
  apply Fin.ext
  simpa only [Equiv.apply_symm_apply,Fin.val_castLE] using
    (enumerate_embed newer older ((enumerate older).symm i)).symm

theorem run_indexed_rows {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1)
    (i : Fin (IntegralMixedFramedPhysicalIndex.arity older)) :
    PolynomialSystemReindex.system (enumerate (newer++older)) (run initial (newer++older) h).sampler.rows
      (Fin.castLE (arity_le_append newer older) i)=
      rename (Fin.castLE (arity_le_append newer older))
        (PolynomialSystemReindex.system (enumerate older) (run initial older ho).sampler.rows i) := by
  unfold PolynomialSystemReindex.system
  rw [enumerate_symm_castLE,run_rows_embed initial newer older h ho _,rename_rename,rename_rename]
  apply congrArg (fun f=>rename f ((run initial older ho).sampler.rows ((enumerate older).symm i)))
  funext j
  apply Fin.ext
  exact enumerate_embed newer older j

theorem run_indexed_degrees {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1)
    (i : Fin (IntegralMixedFramedPhysicalIndex.arity older)) :
    (run initial (newer++older) h).sampler.degrees
      ((enumerate (newer++older)).symm (Fin.castLE (arity_le_append newer older) i))=
      (run initial older ho).sampler.degrees ((enumerate older).symm i) := by
  rw [enumerate_symm_castLE]
  exact run_degrees_embed initial newer older h ho _

end LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
