/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryPieceTruth
/-! # Endpoint subformulas select existing samples of the original cover -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliarySampleEndpoints
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- If both endpoint formulas occur in the original formula, their singleton
points are already samples of any nonempty piece containing them. -/
theorem point_iff_samples (q : PointQuery) (hd : q.space.WellFormed)
    (preL suffixL preR suffixR : List Bool)
    (hL : FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original q.space)) =
      preL ++ q.source.encode ++ suffixL)
    (hR : FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original q.space)) =
      preR ++ q.target.encode ++ suffixR)
    (hs : q.source.arity ≤ ClosedFormulaGateMetadata.dimension (CanonicalSignRefinement.original q.space))
    (ht : q.target.arity ≤ ClosedFormulaGateMetadata.dimension (CanonicalSignRefinement.original q.space)) :
    (Input.point q).encode ∈ pointLanguage ↔
      ∃ i j : CanonicalAuxiliaryCandidateCover.Index q.space,
      ∃ hi : CanonicalAuxiliaryProjectedSamples.Good q.space i,
      ∃ hj : CanonicalAuxiliaryProjectedSamples.Good q.space j,
        Denotes q.space.dimension q.source (CanonicalAuxiliaryCandidateCover.rawSample q.space i hi) ∧
        Denotes q.space.dimension q.target (CanonicalAuxiliaryCandidateCover.rawSample q.space j hj) ∧
        CanonicalAuxiliaryCandidateCover.walk q.space i j := by
  rw [CanonicalAuxiliaryCandidateCover.point_language_iff q hd]
  constructor
  · rintro ⟨x,y,HX,HY,i,j,HI,HJ,HW⟩
    have hi := CanonicalAuxiliaryProjectedSamples.good_of_raw_nonempty q.space i ⟨x.val,HI⟩
    have hj := CanonicalAuxiliaryProjectedSamples.good_of_raw_nonempty q.space j ⟨y.val,HJ⟩
    have HEi := CanonicalAuxiliaryPieceTruth.sample_eq_of_denotes q.space i hi q.source
      preL suffixL hL hs x.val HX HI
    have HEj := CanonicalAuxiliaryPieceTruth.sample_eq_of_denotes q.space j hj q.target
      preR suffixR hR ht y.val HY HJ
    exact ⟨i,j,hi,hj,HEi.symm ▸ HX,HEj.symm ▸ HY,HW⟩
  · rintro ⟨i,j,hi,hj,HX,HY,HW⟩
    exact ⟨CanonicalAuxiliaryCandidateCover.sample q.space hd i hi,
      CanonicalAuxiliaryCandidateCover.sample q.space hd j hj,HX,HY,i,j,
      CanonicalAuxiliaryCandidateCover.sample_mem q.space hd i hi,
      CanonicalAuxiliaryCandidateCover.sample_mem q.space hd j hj,HW⟩

/-- Tautologies expose both endpoint formulas to the finite sign refinement. -/
def expose (q : PointQuery) : PointQuery :=
  {q with space := ⟨q.space.dimension,
    .and q.space.formula (.and (.or q.source (.not q.source)) (.or q.target (.not q.target)))⟩}

theorem expose_realization (q : PointQuery) : (expose q).space.realization = q.space.realization := by
  ext x
  simp only [expose,Description.realization,mem_ofPred_eq,Formula.Holds]
  tauto

theorem expose_wellFormed (q : PointQuery) (hd : q.space.WellFormed)
    (hs : q.source.arity ≤ q.space.dimension) (ht : q.target.arity ≤ q.space.dimension) :
    (expose q).space.WellFormed := by
  change max q.space.formula.arity (max (max q.source.arity q.source.arity)
    (max q.target.arity q.target.arity)) ≤ q.space.dimension
  exact max_le hd (max_le (max_le hs hs) (max_le ht ht))

theorem expose_language_iff (q : PointQuery) (hd : q.space.WellFormed)
    (hs : q.source.arity ≤ q.space.dimension) (ht : q.target.arity ≤ q.space.dimension) :
    (Input.point (expose q)).encode ∈ pointLanguage ↔ (Input.point q).encode ∈ pointLanguage := by
  rw [point_encode_mem_iff,point_encode_mem_iff]
  change ((expose q).space.WellFormed ∧ ∃ x y : Fin q.space.dimension → ℝ,
    Denotes _ q.source x ∧ Denotes _ q.target y ∧ JoinedIn (expose q).space.realization x y) ↔ _
  rw [expose_realization]
  exact and_congr (iff_of_true (expose_wellFormed q hd hs ht) hd) Iff.rfl


private theorem encode_and (p r : Formula) :
    (Formula.and p r).encode = FormulaBooleanCircuitSource.header 4 ++ p.encode ++ r.encode ++ [true] :=
  FormulaBooleanCircuitSource.encode_binary false p r
private theorem encode_or (p r : Formula) :
    (Formula.or p r).encode = FormulaBooleanCircuitSource.header 5 ++ p.encode ++ r.encode ++ [true] :=
  FormulaBooleanCircuitSource.encode_binary true p r

def sourcePrefix (q : PointQuery) := FormulaBooleanCircuitSource.header 4 ++ q.space.formula.encode ++
  FormulaBooleanCircuitSource.header 4 ++ FormulaBooleanCircuitSource.header 5
def sourceSuffix (q : PointQuery) := (Formula.not q.source).encode ++ [true] ++
  (Formula.or q.target (.not q.target)).encode ++ [true] ++ [true]
def targetPrefix (q : PointQuery) := FormulaBooleanCircuitSource.header 4 ++ q.space.formula.encode ++
  FormulaBooleanCircuitSource.header 4 ++ (Formula.or q.source (.not q.source)).encode ++
  FormulaBooleanCircuitSource.header 5
def targetSuffix (q : PointQuery) := (Formula.not q.target).encode ++ [true] ++ [true] ++ [true]

theorem source_occurs (q : PointQuery) :
    FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original (expose q).space)) =
      sourcePrefix q ++ q.source.encode ++ sourceSuffix q := by
  rw [CanonicalSignRefinement.original,Input.field_whole_space,FormulaView.normalize_encode]
  change (Formula.and q.space.formula (.and (.or q.source (.not q.source))
    (.or q.target (.not q.target)))).encode = _
  rw [encode_and,encode_and,encode_or]
  simp only [sourcePrefix,sourceSuffix,List.append_assoc]

theorem target_occurs (q : PointQuery) :
    FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original (expose q).space)) =
      targetPrefix q ++ q.target.encode ++ targetSuffix q := by
  rw [CanonicalSignRefinement.original,Input.field_whole_space,FormulaView.normalize_encode]
  change (Formula.and q.space.formula (.and (.or q.source (.not q.source))
    (.or q.target (.not q.target)))).encode = _
  rw [encode_and,encode_and,encode_or q.target]
  simp only [targetPrefix,targetSuffix,List.append_assoc]

/-- The original point language reduces to reachability between its actual
accepted auxiliary samples, with both singleton tests still checked. -/
theorem original_point_iff_samples (q : PointQuery) (hd : q.space.WellFormed)
    (hs : q.source.arity ≤ q.space.dimension) (ht : q.target.arity ≤ q.space.dimension) :
    (Input.point q).encode ∈ pointLanguage ↔
      ∃ i j : CanonicalAuxiliaryCandidateCover.Index (expose q).space,
      ∃ hi : CanonicalAuxiliaryProjectedSamples.Good (expose q).space i,
      ∃ hj : CanonicalAuxiliaryProjectedSamples.Good (expose q).space j,
        Denotes q.space.dimension q.source (CanonicalAuxiliaryCandidateCover.rawSample (expose q).space i hi) ∧
        Denotes q.space.dimension q.target (CanonicalAuxiliaryCandidateCover.rawSample (expose q).space j hj) ∧
        CanonicalAuxiliaryCandidateCover.walk (expose q).space i j := by
  rw [←expose_language_iff q hd hs ht]
  apply point_iff_samples (expose q) (expose_wellFormed q hd hs ht)
    (sourcePrefix q) (sourceSuffix q) (targetPrefix q) (targetSuffix q)
    (source_occurs q) (target_occurs q)
  · change q.source.arity ≤ ClosedFormulaGateTruth.F.dimension (Input.whole (expose q).space).encode
    rw [ClosedFormulaGateTruth.dimension_whole]
    exact hs
  · change q.target.arity ≤ ClosedFormulaGateTruth.F.dimension (Input.whole (expose q).space).encode
    rw [ClosedFormulaGateTruth.dimension_whole]
    exact ht

end LeanCanny.Connectivity.CanonicalAuxiliarySampleEndpoints
