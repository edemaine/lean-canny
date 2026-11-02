/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBounds
public import LeanCanny.Geometry.BoundedZeroPerturbation

/-! # One original-only binary radius contains every decoded candidate

The certified packed-height reader is bounded over all short prepared roots.
The word allowance depends only on the original input, even for malformed
advice. This radius is chosen before introducing the later regular source.
It bounds the sample coordinates; it does not assert stabilization of every
connection in an unbounded original zero set.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateRadius
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.Geometry
open IntegralMixedAuxiliaryCandidateBounds
open scoped Classical

theorem coordinate_exponent {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ E : List Bool→ℕ,BinaryFn E ∧ ∀ original label,
      ∀ hv : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label),∀ i : Fin (n original),
        |IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv i|≤(2:ℝ)^E original := by
  obtain ⟨r,hr⟩:=IntegralMixedAuxiliaryCandidate.source_length_polynomial hn ht
  have HB : UnaryFn (fun original : List Bool=>r.eval original.length) :=
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval r).comp (UnaryFn.length id_mem_FP)
  obtain ⟨E,hE,HE⟩:=(packedHeight_binary hn ht ha).wordEnvelope HB
  refine ⟨E,hE,fun original label hv i=>?_⟩
  have HS : (IntegralMixedAuxiliaryCandidate.source n t (pair original label)).length≤r.eval original.length := by
    simpa only [pairFst_pair] using hr (pair original label)
  exact (pointAt_bound hn ht ha original label hv i).trans
    (pow_le_pow_right₀ (by norm_num) (HE original _ HS))

theorem exists_radius {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ R : List Bool→ℕ,BinaryFn R ∧ ∀ original label,
      ∀ hv : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label),
        BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv)≤
          (BoundedZeroSource.radiusSquared (R original):ℝ) := by
  obtain ⟨E,hE,HE⟩:=coordinate_exponent hn ht ha
  refine ⟨fun original=>E original+(n original).size,hE.add (BinaryFn.ofUnary hn).size,?_⟩
  intro original label hv
  have HR:=BoundedPositivePerturbation.penalty_bound 2 (E original)
    (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv) (HE original label hv)
  have HP : (2:ℝ)^(E original*2+(n original).size)≤(2:ℝ)^(2*(E original+(n original).size)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  simpa only [BoundedZeroSource.radial,BoundedZeroSource.radiusSquared,Int.cast_pow,Int.cast_ofNat]
    using HR.trans HP

noncomputable def radius {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : List Bool→ℕ :=
  Classical.choose (exists_radius hn ht ha)

theorem radius_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    BinaryFn (radius hn ht ha) := (Classical.choose_spec (exists_radius hn ht ha)).1

theorem point_radial_le {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) (hv : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label)) :
    BoundedZeroSource.radial (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv)≤
      (BoundedZeroSource.radiusSquared (radius hn ht ha original):ℝ) :=
  (Classical.choose_spec (exists_radius hn ht ha)).2 original label hv

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateRadius
