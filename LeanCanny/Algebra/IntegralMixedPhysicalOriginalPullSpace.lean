/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLowSpace
/-! # Original physical coefficient packets retain an external query datum

Only the saved physical-source word is transformed. Exponent and modulus
queries remain outside the bounded flat task payload until the original leaf.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOriginalPullBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedPhysicalCriticalBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def indices (F : Family) (I : Indices F) (base : List Bool→List Bool) :
    Indices (IntegralMixedPhysicalQueryBits.pull F base) where
  coordinate q:=I.coordinate (base q)
  coefficientIndex:=I.coefficientIndex∘base
  target:=I.target∘base
  row q:=I.row (base q)
  col q:=I.col (base q)
  modulus:=I.modulus∘base
  modulus_ne_zero q:=I.modulus_ne_zero (base q)

theorem metadata (F : Family) (I : Indices F) (h : Metadata F I)
    (base : List Bool→List Bool) (hb : base∈FP) :
    Metadata (IntegralMixedPhysicalQueryBits.pull F base) (indices F I base) where
  ambient:=h.ambient.comp hb
  birth:=h.birth.comp hb
  width:=h.width.comp hb
  offset:=h.offset.comp hb
  degree:=h.degree.comp hb
  objective:=h.objective.comp hb
  target:=h.target.comp hb
  row:=h.row.comp hb
  col:=h.col.comp hb
  modulus:=h.modulus.comp hb
  coordinate:=h.coordinate.comp hb
  coefficientIndex:=h.coefficientIndex.comp hb

theorem coefficient (F : Family) (I : Indices F) (base : List Bool→List Bool) (q : List Bool) (k : ℕ) :
    IntegralMixedPhysicalOriginalBits.coefficient (IntegralMixedPhysicalQueryBits.pull F base) (indices F I base) q k=
      IntegralMixedPhysicalOriginalBits.coefficient F I (base q) k := by
  rw [IntegralMixedOriginalSpatialTermBits.physical_coefficient,IntegralMixedOriginalSpatialTermBits.physical_coefficient]
  rfl

def packet (base : List Bool→List Bool) (p : List Bool) := pair (base (pairFst p)) (pairSnd p)
theorem packet_FP (base : List Bool→List Bool) (hb : base∈FP) : packet base∈FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hb) pairSnd_mem_FP

theorem scalar (F : Family) (I : Indices F) (base : List Bool→List Bool) (p : List Bool) :
    IntegralMixedPhysicalOriginalBits.scalar (IntegralMixedPhysicalQueryBits.pull F base) (indices F I base) p=
      IntegralMixedPhysicalOriginalBits.scalar F I (packet base p) := by
  have HC : IntegralMixedPhysicalOriginalBits.coefficient (IntegralMixedPhysicalQueryBits.pull F base) (indices F I base)
      (pairFst p) (Nat.fromBitsLE (pairSnd p))=
      IntegralMixedPhysicalOriginalBits.coefficient F I (pairFst (packet base p)) (Nat.fromBitsLE (pairSnd (packet base p))) := by
    rw [coefficient]
    simp only [packet,pairFst_pair,pairSnd_pair]
  have HM : (indices F I base).modulus (pairFst p)=I.modulus (pairFst (packet base p)) := by
    change I.modulus (base (pairFst p))=I.modulus (pairFst (packet base p))
    rw [packet,pairFst_pair]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) HC HM

theorem original_space (F : Family) (I : Indices F) (E : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (base : List Bool→List Bool) (hb : base∈FP) :
    SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar (IntegralMixedPhysicalQueryBits.pull F base) (indices F I base)) :=
  (E.precompose (packet base) (packet_FP base hb)).congr (funext fun p=>(scalar F I base p).symm)

end LeanCanny.Algebra.IntegralMixedPhysicalOriginalPullBits
