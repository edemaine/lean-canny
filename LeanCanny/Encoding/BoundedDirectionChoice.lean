/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedValidity

/-! # Native bounded selection for the component-preserving regular source

The search runs the actual bounded-source validator on candidate records.
Existence follows from the constructed source's derived degree and mass
bounds, with no supplied validity algorithm or generic direction.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedDirectionChoice
open LeanCanny.ETR LeanCanny.Computation LeanCanny.Geometry LeanCanny.Algebra
open BoundedSourceWriter FermatSweepCertificate MvPolynomial Turing.MultiTapeTM LeanCanny.Encoding.Brackets
open scoped Classical

def packet (P : Readers) : Readers :=
  ⟨P.source ∘ pairFst, pairSnd, P.dim ∘ pairFst, P.radius ∘ pairFst⟩

theorem packet_polyTime {P : Readers} (h : P.PolyTime) : (packet P).PolyTime := by
  refine ⟨?_, pairSnd_mem_FP, ?_, h.radius.comp (FP.computable pairFst_mem_FP)⟩
  · exact mem_FP_comp (f := pairFst) (g := P.source) pairFst_mem_FP h.source
  · exact UnaryFn.comp (f := P.dim) (g := pairFst) h.dim pairFst_mem_FP

noncomputable def test (P : Readers) (p : List Bool × List Bool) : Bool :=
  decide (BoundedValidity.check (packet P) (pair p.1 p.2) = [true])

noncomputable def record (P : Readers) : List Bool → List Bool :=
  ImplicitGraph.findWord (test P) (fun c => (P.dim c + 3) * width (P.dim c + 2) (degree P c))

theorem test_computable {P : Readers} (h : P.PolyTime) :
    ComputableInPolySpace (test P) (encPair encBits encBits) encBool := by
  have hc := BoundedValidity.evaluator (packet_polyTime h)
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have he := (ComputableInPolySpace.of_tidyPolyTime heq).comp (hc.computable.comp (.of_tidyPolyTime hp))
  apply he.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq]

theorem evaluator {P : Readers} (h : P.PolyTime) : SpaceFunction (record P) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h) (recordLength_unary (h.dim.add (UnaryFn.const 2)) (degree_binary h))⟩

theorem record_length (P : Readers) (c : List Bool) :
    (record P c).length = (P.dim c + 3) * width (P.dim c + 2) (degree P c) :=
  ImplicitGraph.findWord_length _ _ _

private noncomputable def validData (source : List Bool) (dim radius : ℕ) (r : List Bool) : Prop :=
  let P : Readers := ⟨fun _ => source, fun _ => r, fun _ => dim, fun _ => radius⟩
  Valid ((lower P []).map (Int.castRingHom ℚ)) (leading P [] : ℚ) (degree P []) r

theorem test_correct (P : Readers) (c r : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    test P (c, r) = true ↔
      Valid ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) r := by
  have ht' : (TermView.term ((packet P).source (pair c r))).arity ≤ (packet P).dim (pair c r) := by
    simpa only [packet, Function.comp_apply, pairFst_pair] using ht
  have hv := BoundedValidity.correct (packet P) (pair c r) ht'
  simp only [test, hv, List.cons.injEq, and_true, decide_eq_true_eq]
  change validData ((packet P).source (pair c r)) ((packet P).dim (pair c r)) ((packet P).radius (pair c r))
    ((packet P).record (pair c r)) ↔ validData (P.source c) (P.dim c) (P.radius c) r
  simp only [packet, Function.comp_apply, pairFst_pair, pairSnd_pair]

theorem record_valid (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Valid ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (record P c) := by
  apply (test_correct P c _ ht).mp
  apply ImplicitGraph.findWord_correct
  have hex := IntegerRegularSweepCertificate.exists_valid_record
    (BoundedRegularSource.lower (original P c) (size P c) (size P c) (P.radius c)) 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c))
    (BoundedRegularSource.lower_degree _ _ _ _ (original_degree P c)) (by decide)
    (BoundedRegularSource.powerDegree_gt_one (size P c))
    (BoundedRegularSource.source_mass _ _ _ _ (original_mass P c))
  obtain ⟨r, hr, hv⟩ := hex
  exact ⟨r, hr, (test_correct P c r ht).mpr hv⟩

noncomputable def selected (P : Readers) : Readers := ⟨P.source, record P, P.dim, P.radius⟩

theorem selected_valid (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Valid ((lower (selected P) c).map (Int.castRingHom ℚ)) (leading (selected P) c : ℚ)
      (degree (selected P) c) ((selected P).record c) := record_valid P c ht

private noncomputable def encodeData (source : List Bool) (dim radius : ℕ) (r : List Bool) : List Bool :=
  let P : Readers := ⟨fun _ => source, fun _ => r, fun _ => dim, fun _ => radius⟩
  ComplexCircuit.encode (ComplexCircuit.StraightLine.gates (start P []) (program P []))

/-- Selection and source serialization compose in native polynomial space.
The selected record need not be a polynomial-time reader. -/
theorem selected_encode_evaluator {P : Readers} (h : P.PolyTime) :
    SpaceFunction (fun c => ComplexCircuit.encode (ComplexCircuit.StraightLine.gates
      (start (selected P) c) (program (selected P) c))) := by
  have he := (evaluator h).withInput.postcompose
    (fun p => ComplexCircuit.encode (ComplexCircuit.StraightLine.gates (start (packet P) p) (program (packet P) p)))
      (BoundedSourceWriter.encode_mem_FP (packet_polyTime h))
  apply he.congr
  funext c
  change encodeData (P.source (pairFst (pair c (record P c)))) (P.dim (pairFst (pair c (record P c))))
    (P.radius (pairFst (pair c (record P c)))) (pairSnd (pair c (record P c))) =
      encodeData (P.source c) (P.dim c) (P.radius c) (record P c)
  simp only [pairFst_pair, pairSnd_pair]

def fromSource (source : List Bool → List Bool) (dim radius : List Bool → ℕ) : Readers :=
  ⟨source, fun _ => [], dim, radius⟩

theorem fromSource_polyTime {source : List Bool → List Bool} {dim radius : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) (hR : BinaryFn radius) : (fromSource source dim radius).PolyTime :=
  ⟨ht, constFn_mem_FP [], hd, hR⟩

theorem fromSource_evaluator {source : List Bool → List Bool} {dim radius : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) (hR : BinaryFn radius) :
    SpaceFunction (record (fromSource source dim radius)) := evaluator (fromSource_polyTime ht hd hR)

end LeanCanny.Encoding.BoundedDirectionChoice
