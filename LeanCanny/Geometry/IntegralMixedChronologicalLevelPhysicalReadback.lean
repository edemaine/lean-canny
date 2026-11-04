/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelPhysicalColumns
/-! # One natural readback identifies every physical block of a proper level -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript IntegralMixedFramedFixedContinuation
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n}
  (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
noncomputable local instance levelPhysicalReadbackIndexFintype :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) older):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) older
variable {x :State P S B m (IntegralMixedFramedHistoryScript.Index (Fin 0) older)}
  {d :Descriptor n m} {z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {left right :Endpoint m}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
  (R :NativePair x d z φ values left right hn hcap) (hk :d.labels.length<n+1)
  (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
local notation "K"=>List.length (NativePair.orderedFree R hk)
variable (hp :m+R.result.commands.length≤S)
  (room :m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
  (hroom :m+R.result.commands.length+1+(R.orderedFree hk).length≤S)
  (side :Bool) (childRoom :m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1)
  (pMID pChild :Fin (n+1)→ℝ)
  (A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
    pMID (R.orderedFree hk) room)
  (E :R.LevelChildCaptures hk g hg hp pMID room A hroom side pChild childRoom)
  {L :ℕ} {u :ℕ→ℝ} {e :R.levelIndex hk g hg side≃Fin L} {bank :ℕ→ℝ}
  (N :R.NaturalReadback hk g hg hp room hroom side childRoom pMID pChild A E u e bank)
  (he :HEq (enumerate ((R.levelCommands hk g hg side).map (wrap P hP)++older)) e)
local notation "L0"=>arity (R.result.commands.map (wrap P hP)++older)
local notation "a"=>m+R.result.commands.length
local notation "span"=>2*n+4

include N he in
/-- The midpoint anchor/captures and child anchor/captures use the same point
within each block, and the same natural tuple and ordinal map throughout. -/
theorem NativePair.NaturalReadback.powered_block (b :ℕ) (hb0 :a≤b) (hb1 :b<a+2+2*K)
    (i :Fin (n+1)):
    u (L0+span*(b-a)+i.val)^UniformIntegralPowerSchedule.physical S (2^B) b=
      if b<a+1+K then pMID i else pChild i:=by
  by_cases hA :b=a
  · have H:=NativePair.NaturalReadback.mid_anchor R hk g hg hp room hroom side childRoom pMID pChild A E N i
    rw [R.level_mid_anchor_number hP older hk g hg side e he i] at H
    rw [ite_eq_left (by omega)]
    simpa only [hA,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using H
  by_cases hM :b<a+1+K
  · let k :Fin K:=⟨K-1-(b-a-1),by omega⟩
    have HK :K-1-k.val=b-a-1:=by dsimp only [k];omega
    have HB :a+1+(K-1-k.val)=b:=by omega
    have HC :L0+span+span*(K-1-k.val)+i.val=L0+span*(b-a)+i.val:=by
      have HD :b-a=1+(K-1-k.val):=by omega
      rw [HD]
      ring
    have H:=NativePair.NaturalReadback.mid_block R hk g hg hp room hroom side childRoom pMID pChild A E N k i
    rw [R.level_mid_number hP older hk g hg side e he k i,HC,HB] at H
    rw [ite_eq_left hM]
    exact H
  by_cases hC :b=a+1+K
  · have H:=NativePair.NaturalReadback.child_anchor R hk g hg hp room hroom side childRoom pMID pChild A E N i
    have HC :L0+span*(1+K)+i.val=L0+span*(b-a)+i.val:=by
      have HD :b-a=1+K:=by omega
      rw [HD]
    rw [R.level_child_anchor_number hP older hk g hg side e he i,HC,←hC] at H
    rw [ite_eq_right hM]
    exact H
  · let k :Fin K:=⟨K-1-(b-a-2-K),by omega⟩
    have HK :K-1-k.val=b-a-2-K:=by dsimp only [k];omega
    have HB :a+1+K+1+(K-1-k.val)=b:=by omega
    have HC :L0+span*(2+K)+span*(K-1-k.val)+i.val=L0+span*(b-a)+i.val:=by
      have HD :b-a=2+K+(K-1-k.val):=by omega
      rw [HD]
      ring
    have H:=NativePair.NaturalReadback.child_block R hk g hg hp room hroom side childRoom pMID pChild A E N k i
    rw [R.level_child_number hP older hk g hg side e he k i,HC,HB] at H
    rw [ite_eq_right hM]
    exact H

theorem level_block_rooms (a0 a1 a2 a3 :ℕ) (h :a0+a1+2+2*a2≤a3+1):
    a0+a1≤a3 ∧a0+a1+1+a2≤a3+1 ∧a0+a1+1+a2≤a3 ∧a0+a1+1+a2+1+a2≤a3+1:=by omega

/-- Exactly the existing A/E/e/he/N witness. This is propositional packaging,
so its data need only be unpacked while proving physical or scalar equalities. -/
def NativePair.PhysicalReadback
    (horizon :m+R.result.commands.length+2+2*K≤S+1)
    (totalColumns :ℕ) (rawTuple :ℕ→ℝ) (midPoint childPoint :Fin (n+1)→ℝ)
    (valuesAt :ℕ→ℝ):Prop:=
  ∃A :R.result.MidpointCaptures (level_block_rooms _ _ _ _ horizon).1
      (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg midPoint (R.orderedFree hk)
      (level_block_rooms _ _ _ _ horizon).2.1,
    ∃E :R.LevelChildCaptures hk g hg (level_block_rooms _ _ _ _ horizon).1 midPoint
      (level_block_rooms _ _ _ _ horizon).2.1 A (level_block_rooms _ _ _ _ horizon).2.2.1
      side childPoint (level_block_rooms _ _ _ _ horizon).2.2.2,
    ∃ordinal :R.levelIndex hk g hg side≃Fin totalColumns,
      HEq (enumerate ((R.levelCommands hk g hg side).map (wrap P hP)++older)) ordinal ∧
        R.NaturalReadback hk g hg (level_block_rooms _ _ _ _ horizon).1
          (level_block_rooms _ _ _ _ horizon).2.1 (level_block_rooms _ _ _ _ horizon).2.2.1
          side (level_block_rooms _ _ _ _ horizon).2.2.2
          midPoint childPoint A E rawTuple ordinal valuesAt

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
