/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullCriticalSamples
public import LeanCanny.ETR.ComplexCriticalSampleCircuit

/-! # Native constrained queries for the actual critical samples

The original readers and a direction record generate the full shared source
and derivative circuit. Formula witnesses are independent of every circuit
auxiliary. Selection of the direction composes with the resulting native
space procedure; it is not assumed to be a polynomial-time reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open BoundedFullWriter MvPolynomial RealQuery.Interleaved
open scoped Classical

noncomputable def frame (P : Readers) (c : List Bool) : ℕ := CriticalKernel.zeroWire (start P c) (P.dim c + 4)

noncomputable def program (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Operation :=
  CriticalKernel.program (start P c) (P.dim c + 4) (BoundedFullWriter.program P c) (output P c)
    (BoundedFullDirectionQueries.direction P record c)

noncomputable def equations (P : Readers) (record : List Bool → List Bool) (c : List Bool) :=
  CriticalKernel.finiteRows (BoundedFullCriticalSamples.polynomial P c)
    (fun j => BoundedFullDirectionQueries.direction P record c j.val)

noncomputable def models (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    List (ℕ × MvPolynomial (Fin (P.dim c + 4)) ℤ) :=
  List.ofFn (fun j : Fin (P.dim c + 4) =>
    (CriticalSamples.output (start P c) (P.dim c + 4) (BoundedFullWriter.program P c) j.val,
      equations P record c j))

noncomputable def query (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Gate :=
  CriticalSamples.query (start P c) (P.dim c + 4) (BoundedFullWriter.program P c) (output P c)
    (BoundedFullDirectionQueries.direction P record c)

theorem frame_unary {P : Readers} (h : P.PolyTime) : UnaryFn (frame P) :=
  (start_unary h).add (h.dim.add (UnaryFn.const 4))

theorem length_unary {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) :
    UnaryFn (fun c => (program P record c).length) :=
  CriticalSamples.length_unary (start_unary h) (h.dim.add (UnaryFn.const 4)) (BoundedFullWriter.length_unary h)

theorem wellFormed (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    StraightLine.WellFormed (frame P c) (program P record c) :=
  CriticalKernel.wellFormed _ _ _ _ _ (BoundedFullWriter.wellFormed P c) (output_lt P c)

theorem models_bound (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    ∀ z ∈ models P record c, z.1 < frame P c + (program P record c).length := by
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  exact CriticalSamples.output_lt _ _ _ _ _ j.val j.isLt

theorem models_identity (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    ∀ z ∈ models P record c, Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ))
      (frame P c) (program P record c) z.1 = rename Fin.val z.2 := by
  let W := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ))
    (start P c) (BoundedFullWriter.program P c)
  have hw := BoundedFullWriter.wellFormed P c
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ))
    (start P c) (BoundedFullWriter.program P c) hw
  have hin : ∀ i < start P c, W i = X i :=
    fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  rw [show Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (frame P c) (program P record c)
      (CriticalSamples.output (start P c) (P.dim c + 4) (BoundedFullWriter.program P c) j.val) =
      CriticalSamples.criticalPolynomial (W (output P c)) (BoundedFullDirectionQueries.direction P record c) j.val from
        CriticalSamples.symbolic_output W _ _ _ _ _ hw hr hin (output_lt P c) j.val j.isLt]
  rw [show W (output P c) = rename Fin.val (BoundedFullCriticalSamples.polynomial P c) from
    BoundedFullGeometry.source_identity P c ht, CriticalSamples.finite_polynomial]
  rfl

theorem query_eq_models (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    query P record c = zeroGates (frame P c) (program P record c) (models P record c) := by
  unfold query CriticalSamples.query zeroGates
  apply congrArg (StraightLine.gates (frame P c) (program P record c) ++ ·)
  apply List.ext_getElem
  · simp only [CriticalSamples.outputs, models, List.length_map, List.length_range, List.length_ofFn]
  · intro i hi hj
    simp only [CriticalSamples.outputs, models, List.getElem_map, List.getElem_ofFn, List.getElem_range]

theorem query_encode_mem_FP {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP) :
    (fun c => encode (query P record c)) ∈ FP :=
  CriticalSamples.query_encode_mem_FP (start_unary h) (h.dim.add (UnaryFn.const 4)) (output_unary h)
    (BoundedFullWriter.length_unary h) (BoundedFullWriter.encode_mem_FP h) (BoundedFullDirectionQueries.literal_mem_FP h hr)

/-- The scalar interface keeps reader composition independent of finite-tuple
transport while retaining the exact finite critical equations. -/
noncomputable def conditionData (source : List Bool) (dim radius : ℕ) (r : List Bool) (x : ℕ → ℝ) : Prop :=
  let P : Readers := ⟨fun _ => source, fun _ => dim, fun _ => radius⟩
  ∀ j, (equations P (fun _ => r) [] j).eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0

noncomputable def Condition (P : Readers) (record : List Bool → List Bool) (c : List Bool) (x : ℕ → ℝ) : Prop :=
  conditionData (P.source c) (P.dim c) (P.radius c) (record c) x

theorem condition_iff (P : Readers) (record : List Bool → List Bool) (c : List Bool) (x : ℕ → ℝ) :
    Condition P record c x ↔ ∀ j, (equations P record c j).eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0 := Iff.rfl

theorem correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    InputSatisfiable (P.dim c + 4) (frame P c) (query P record c) p ↔
      ∃ x : ℕ → ℝ, Condition P record c x ∧ p.Holds x := by
  rw [query_eq_models, finite_correct _ _ _ p (by unfold frame CriticalKernel.zeroWire; omega)
    (wellFormed P record c) (models_bound P record c) (models_identity P record c ht)]
  apply exists_congr
  intro x
  apply and_congr ?_ Iff.rfl
  rw [condition_iff]
  constructor
  · intro h j
    exact h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro h z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact h j

theorem evaluator {P : Readers} {record : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hr : record ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ, Condition P record c x ∧ (p c).Holds x)]) := by
  have ha : ∀ c g, g ∈ query P record c → g.arity ≤ frame P c + (program P record c).length := by
    intro c g hg
    rw [query_eq_models] at hg
    exact zeroGates_arity _ _ _ (wellFormed P record c) (models_bound P record c) g hg
  have he := RealQuery.Interleaved.evaluator (h.dim.add (UnaryFn.const 4)) (frame_unary h)
    ((frame_unary h).add (length_unary (record := record) h)) (query_encode_mem_FP h hr) hp
    (fun c => by unfold frame CriticalKernel.zeroWire; omega) (fun _ => Nat.le_add_right ..) ha
  apply he.congr
  funext c
  rw [correct P record c (p c) (ht c)]

theorem selected_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      Condition P (BoundedFullDirectionChoice.record P) c x ∧ (p c).Holds x)]) := by
  have hc := evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hp)
    (fun z => ht (pairFst z))
  have he : SpaceFunction _ := ⟨hc.computable.comp (BoundedFullDirectionChoice.evaluator h ht).withInput.computable⟩
  apply he.congr
  funext c
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Condition, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]
  exact (Iff.of_eq (@decide_eq_true_eq _ _)).symm

theorem selected_condition (P : Readers) (c : List Bool) (x : ℕ → ℝ) :
    Condition P (BoundedFullDirectionChoice.record P) c x ↔
      ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0 := Iff.rfl

def Matches (P : Readers) (c : List Bool) (p : Formula) (y : BoundedFullCriticalSamples.Samples P c) : Prop :=
  ∃ x : ℕ → ℝ, (∀ i : Fin (P.dim c + 4), x i.val = y.val i) ∧ p.Holds x

theorem selected_iff_samples (P : Readers) (c : List Bool) (p : Formula) :
    (∃ x : ℕ → ℝ, Condition P (BoundedFullDirectionChoice.record P) c x ∧ p.Holds x) ↔
      ∃ y : BoundedFullCriticalSamples.Samples P c, Matches P c p y := by
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨fun i => x i.val, (selected_condition P c x).mp hx⟩, x, fun _ => rfl, hp⟩
  · rintro ⟨y, x, hx, hp⟩
    refine ⟨x, (selected_condition P c x).mpr ?_, hp⟩
    rw [funext hx]
    exact y.property

theorem samples_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ y : BoundedFullCriticalSamples.Samples P c, Matches P c (p c) y)]) := by
  apply (selected_evaluator h hp ht).congr
  funext c
  rw [selected_iff_samples]

private noncomputable def encodeData (source : List Bool) (dim radius : ℕ) (r : List Bool) : List Bool :=
  encode (query ⟨fun _ => source, fun _ => dim, fun _ => radius⟩ (fun _ => r) [])

/-- The actual selected sample circuit can be serialized in native space,
without materializing its source polynomials or a polynomial-time selector. -/
theorem selected_encode_evaluator {P : Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => encode (query P (BoundedFullDirectionChoice.record P) c)) := by
  have he := (BoundedFullDirectionChoice.evaluator h ht).withInput.postcompose
    (fun z => encode (query (P.comp pairFst) pairSnd z))
    (query_encode_mem_FP (h.comp pairFst_mem_FP) pairSnd_mem_FP)
  apply he.congr
  funext c
  change encodeData (P.source (pairFst (pair c (BoundedFullDirectionChoice.record P c))))
      (P.dim (pairFst (pair c (BoundedFullDirectionChoice.record P c))))
      (P.radius (pairFst (pair c (BoundedFullDirectionChoice.record P c))))
      (pairSnd (pair c (BoundedFullDirectionChoice.record P c))) =
    encodeData (P.source c) (P.dim c) (P.radius c) (BoundedFullDirectionChoice.record P c)
  simp only [pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.BoundedCriticalSampleQuery
