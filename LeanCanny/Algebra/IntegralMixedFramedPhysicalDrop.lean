/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
/-! # Literal full physical suffix embeddings, including mixed critical blocks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalDrop
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (old enumerate)
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def embedding {n B : ℕ} : (cs : List (Instruction n B))→(k : ℕ)→Index (Fin 0) (cs.drop k)→Index (Fin 0) cs
 | _,0=>id
 | [],_+1=>Fin.elim0
 | c::cs,k+1=>old c.command∘embedding cs k

theorem enumerate_embedding {n B : ℕ} (cs : List (Instruction n B)) (k : ℕ)
    (i : Index (Fin 0) (cs.drop k)) :
    (enumerate cs (embedding cs k i)).val=(enumerate (cs.drop k) i).val :=by
  induction cs generalizing k with
  | nil=>cases k <;> exact Fin.elim0 i
  | cons c cs ih=>
    cases k with
    | zero=>rfl
    | succ k=>exact (IntegralMixedFramedPhysicalIndex.step_old c.command (enumerate cs) _).trans (ih k i)

theorem rows_embedding {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1)
    (k : ℕ) (hk : (cs.drop k).length≤S+1) (i : Index (Fin 0) (cs.drop k)) :
    (run initial cs hc).sampler.rows (embedding cs k i)=
      rename (embedding cs k) ((run initial (cs.drop k) hk).sampler.rows i) :=by
  induction cs generalizing k with
  | nil=>cases k <;> exact Fin.elim0 i
  | cons c cs ih=>
    cases k with
    | zero=>rw [show embedding (c::cs) 0=id from rfl,rename_id];rfl
    | succ k=>
      have HT : cs.length≤S+1:=by simp only [List.length_cons] at hc;omega
      have HM : cs.length≤S:=by simp only [List.length_cons] at hc;omega
      have HR:=IntegralMixedFramedPhysicalPersistence.step_rows_old
        (reframe (run initial cs HT) c.source c.source_cap) HM c.command (embedding cs k i)
      change (run initial (c::cs) hc).sampler.rows (embedding (c::cs) (k+1) i)=
        rename (old c.command) ((run initial cs HT).sampler.rows (embedding cs k i)) at HR
      rw [HR,ih HT k hk i,rename_rename]
      rfl

theorem roots {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1)
    (k : ℕ) (hk : (cs.drop k).length≤S+1) (z : Index (Fin 0) cs→ℝ)
    (hz : ∀i,((run initial cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∀i,((run initial (cs.drop k) hk).sampler.rows i).eval₂ (Int.castRingHom ℝ) (z∘embedding cs k)=0 :=by
  intro i
  have HI:=hz (embedding cs k i)
  rw [rows_embedding initial cs hc k hk i,eval₂_rename] at HI
  exact HI

end LeanCanny.Algebra.IntegralMixedFramedPhysicalDrop
