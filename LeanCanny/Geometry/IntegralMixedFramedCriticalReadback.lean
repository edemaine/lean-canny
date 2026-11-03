/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAncestry
/-! # A retained actual critical block gives a geometric critical point

The entire final tuple is fixed. Older raw columns are unchanged; the
ambient block is raised to the power assigned at its creating birth.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B : ℕ} {P : SpatialSource n}

noncomputable def Roots (initial : State P S B 0 (Fin 0)) (cs : List (Instruction n B))
    (h : cs.length≤S+1) (z : ℕ→ℝ) : Prop :=
  ∀i,((run initial cs h).sampler.rows i).eval₂ (Int.castRingHom ℝ)
    (fun j=>z (enumerate cs j).val)=0

noncomputable def point (older : List (Instruction n B)) (z : ℕ→ℝ) (i : Fin (n+1)) : ℝ :=
  z (arity older+i.val)^physical S (2^B) older.length

theorem roots_congr (initial : State P S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (z : ℕ→ℝ) :
    Roots initial cs hc z↔Roots initial ds hd z :=by cases he;rfl

theorem run_critical (initial : State P S B 0 (Fin 0)) (Q : SpatialSource n)
    (hQ : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (r : CriticalRule n)
    (newer older : List (Instruction n B))
    (h : (newer++⟨Q,hQ,.critical r⟩::older).length≤S+1)
    (ho : older.length≤S+1) (hm : older.length≤S) (z : ℕ→ℝ)
    (hz : Roots initial (newer++⟨Q,hQ,.critical r⟩::older) h z) :
    let x:=reframe (run initial older ho) Q hQ
    ∃φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        z (enumerate older (x.sampler.scalar i)).val^weights S (2^B) older.length i) ∧
      IntegralMixedCriticalReadback.CriticalPoint x hm r φ (point (S:=S) older z) :=by
  let c : Instruction n B:=⟨Q,hQ,.critical r⟩
  let x:=reframe (run initial older ho) Q hQ
  have hs : (c::older).length≤S+1:=by
    simp only [List.length_cons]
    omega
  let w : Index (Fin 0) (c::older)→ℝ:=
    fun j=>z (enumerate (newer++c::older) (IntegralMixedFramedPhysicalPersistence.embed newer (c::older) j)).val
  have HR:=IntegralMixedFramedPhysicalPersistence.run_old_roots initial newer (c::older) h hs
    (fun j=>z (enumerate (newer++c::older) j).val) hz
  obtain ⟨φ,_,hφ,HP⟩:=IntegralMixedCriticalReadback.roots_interpret x hm r w HR
  refine ⟨φ,fun i=>(hφ i).trans ?_,?_⟩
  · apply congrArg (fun a : ℝ=>a^weights S (2^B) older.length i)
    unfold w
    rw [IntegralMixedFramedPhysicalPersistence.enumerate_embed]
    exact congrArg z (step_old (.critical r) (enumerate older) (x.sampler.scalar i))
  · have HE : IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=older.length) w=point (S:=S) older z :=by
      funext i
      apply congrArg (fun a : ℝ=>a^physical S (2^B) older.length)
      exact congrArg z (retained_creating_ambient Q hQ r newer older i)
    exact HE ▸ HP

end LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
