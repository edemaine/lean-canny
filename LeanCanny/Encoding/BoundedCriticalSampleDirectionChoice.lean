/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockData
public import LeanCanny.Encoding.FermatCommonCriticalDirection
public import LeanCanny.Geometry.FermatCriticalRegularity
public import LeanCanny.ETR.NumericLiteralFP

/-! # Native common-direction search over actual parent samples

The native block validator tests every critical root over every selected
parent sample. Its bounded record search uses the parent sample-count bit
allowance. Pure-power shape and regularity over coefficient-field extensions
imply that the search succeeds; no successful-record oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleDirectionChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit BoundedFullWriter MvPolynomial Turing.MultiTapeTM
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd

structure Inputs where
  parent : Readers
  source : List Bool → List Bool
  offset : List Bool → ℕ
  free : List Bool → ℕ
  degree : List Bool → ℕ

structure Inputs.PolyTime (F : Inputs) : Prop where
  parent : F.parent.PolyTime
  source : F.source ∈ FP
  offset : BinaryFn F.offset
  free : UnaryFn F.free
  degree : BinaryFn F.degree

noncomputable def width (F : Inputs) (c : List Bool) : ℕ :=
  Algebra.FermatCommonCriticalDirection.binaryWidth (F.free c) (F.degree c)
    (BoundedFullCriticalSamples.labelWidth F.parent c)

noncomputable def recordLength (F : Inputs) (c : List Bool) : ℕ := F.free c * width F c

theorem width_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (width F) :=
  FermatCommonCriticalDirection.binaryWidth_unary h.free h.degree
    (BoundedFullCriticalSamples.labelWidth_unary h.parent)

theorem width_pos (F : Inputs) (c : List Bool) : 0 < width F c := by
  unfold width Algebra.FermatCommonCriticalDirection.binaryWidth Algebra.FermatBoundedCriticalDirection.binaryWidth
  omega

theorem recordLength_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (recordLength F) :=
  h.free.mul (width_unary h)

noncomputable def direction (F : Inputs) (c r : List Bool) (i : ℕ) : ℤ :=
  FixedWidthQuery.coordinate (width F) (fun _ => r) c i

noncomputable def family (F : Inputs) : BlockKernel.Inputs where
  source := F.source ∘ pairFst
  offset := F.offset ∘ pairFst
  free := F.free ∘ pairFst
  direction q i := FixedWidthQuery.coordinate (width F ∘ pairFst) pairSnd q i
  condition _ := .falsum

theorem family_polyTime {F : Inputs} (h : F.PolyTime) : (family F).PolyTime := by
  refine ⟨mem_FP_comp (f := pairFst) (g := F.source) pairFst_mem_FP h.source, h.offset.comp pairFst_mem_FP,
    h.free.comp pairFst_mem_FP, ?_, constFn_mem_FP Formula.falsum.encode⟩
  have hw := ((width_unary h).comp pairFst_mem_FP).comp pairFst_mem_FP
  have hb := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    ((UnaryFn.length pairSnd_mem_FP).mul hw)) hw
  exact mem_FP_of_eq (Term.negNat_toBits_mem_FP (BinaryFn.fromBits hb)) (fun _ => rfl)

def Good (F : Inputs) (c r : List Bool) : Prop :=
  BoundedCriticalSampleBlockData.Good F.parent c (F.source c) (F.offset c) (F.free c) (direction F c r)

noncomputable def test (F : Inputs) (p : List Bool × List Bool) : Bool :=
  decide (BoundedCriticalSampleBlockRegularity.Good (F.parent.comp pairFst) (family F) (pair p.1 p.2))

theorem test_correct (F : Inputs) (c r : List Bool) : test F (c, r) = true ↔ Good F c r := by
  simp only [test, decide_eq_true_eq, BoundedCriticalSampleBlockData.data_comp_iff]
  have hd : (family F).direction (pair c r) = direction F c r := by
    funext i
    simp only [family, direction, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [hd]
  simp only [Good, family, Function.comp_apply, pairFst_pair]

theorem test_computable {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c) :
    ComputableTidilyInPolySpace (test F) (encPair encBits encBits) encBool := by
  have hc := BoundedCriticalSampleBlockRegularity.evaluator (h.parent.comp pairFst_mem_FP)
    (family_polyTime h) (fun q => ht (pairFst q))
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have he := (ComputableTidilyInPolySpace.of_polyTime heq).comp (hc.computable.comp (.of_polyTime hp))
  apply he.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq, List.cons.injEq, and_true]

noncomputable def record (F : Inputs) : List Bool → List Bool :=
  ImplicitGraph.findWord (test F) (recordLength F)

theorem evaluator {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c) : SpaceFunction (record F) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h ht) (recordLength_unary h)⟩

theorem record_length (F : Inputs) (c : List Bool) : (record F c).length = recordLength F c :=
  ImplicitGraph.findWord_length _ _ _

/-- The selected block uses the actual space-computed record. -/
noncomputable def selected (F : Inputs) : BlockKernel.Inputs where
  source := F.source
  offset := F.offset
  free := F.free
  direction c := direction F c (record F c)
  condition _ := .falsum

theorem selected_good_iff (F : Inputs) (c : List Bool) :
    BoundedCriticalSampleBlockRegularity.Good F.parent (selected F) c ↔ Good F c (record F c) :=
  BoundedCriticalSampleBlockData.data_iff F.parent (selected F) c

private def queryPacket (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))

private theorem queryPacket_FP : queryPacket ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def read (F : Inputs) (q : List Bool) : List Bool :=
  FermatCommonCriticalDirection.read F.free F.degree (BoundedFullCriticalSamples.labelWidth F.parent)
    (pair (pair (pairFst q) (record F (pairFst q))) (pairSnd q))

theorem read_evaluator {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c) : SpaceFunction (read F) := by
  have hr := FermatCommonCriticalDirection.read_FP h.free h.degree
    (BoundedFullCriticalSamples.labelWidth_unary h.parent)
  have H := (evaluator h ht).call pairFst
    (FermatCommonCriticalDirection.read F.free F.degree (BoundedFullCriticalSamples.labelWidth F.parent) ∘ queryPacket)
    pairFst_mem_FP (mem_FP_comp queryPacket_FP hr)
  exact H.congr (funext fun q => by simp only [Function.comp_apply, queryPacket, pairFst_pair, pairSnd_pair, read])

theorem read_packet (F : Inputs) (c : List Bool) (i : ℕ) (hi : i < F.free c) :
    read F (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.coordinate (width F) (record F) c i) := by
  simp only [read, pairFst_pair, pairSnd_pair,
    FermatCommonCriticalDirection.read_packet _ _ _ _ _ i hi]
  rfl

theorem record_good_of_exists (F : Inputs) (c : List Bool)
    (hex : ∃ r : List Bool, r.length = recordLength F c ∧ Good F c r) : Good F c (record F c) := by
  apply (test_correct F c _).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hg⟩ := hex
  exact ⟨r, hr, (test_correct F c r).mpr hg⟩

theorem exists_record (F : Inputs) (c : List Bool)
    (low : BoundedFullCriticalSamples.Samples F.parent c → MvPolynomial (Fin (F.free c + 1)) ℝ)
    (a : BoundedFullCriticalSamples.Samples F.parent c → ℝ) (ha : ∀ p, a p ≠ 0)
    (hshape : ∀ p, BoundedCriticalSampleBlockScaling.original (TermView.term (F.source c)) p.val
      (F.offset c) (F.free c + 1) = FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c))
    (hlow : ∀ p, (low p).totalDegree < F.degree c) (hN : 1 < F.degree c)
    (hregular : ∀ p, ∀ (L : Type) [Field L] [Algebra ℝ L] (x : Fin (F.free c + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c)) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c))) ≠ 0) :
    ∃ r : List Bool, r.length = recordLength F c ∧ Good F c r := by
  obtain ⟨r, hr, hg⟩ := FermatCommonCriticalDirection.exists_parent_record F.parent c low a ha (F.degree c)
    hlow hN hregular
  refine ⟨r, hr, ?_⟩
  intro p y hy
  let v := fun i : Fin (F.free c) =>
    (FermatCommonCriticalDirection.assignment (F.free c) (F.degree c)
      (BoundedFullCriticalSamples.labelWidth F.parent c) r i : ℝ)
  have he : BoundedCriticalSampleBlockData.rows (F.source c) (F.offset c) (F.free c) (direction F c r) p.val =
      CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c)) v := by
    unfold BoundedCriticalSampleBlockData.rows
    rw [hshape p]
    congr 1
  change (∀ i, (BoundedCriticalSampleBlockData.rows (F.source c) (F.offset c) (F.free c)
    (direction F c r) p.val i).eval y = 0) at hy
  change (fderiv ℝ (fun z => fun i => (BoundedCriticalSampleBlockData.rows (F.source c) (F.offset c)
    (F.free c) (direction F c r) p.val i).eval z) y).IsInvertible
  rw [he] at hy ⊢
  apply FermatCriticalRegularity.regular_of_certificate
  apply hg p ℝ y
  intro i
  change (FermatCriticalBadSystem.equations (low p) (a p) (F.degree c) i).eval₂ (eval₂Hom (RingHom.id ℝ) v) y = 0
  rw [← eval_map, FermatCriticalRegularity.equations_map]
  exact hy i

theorem record_good (F : Inputs) (c : List Bool)
    (low : BoundedFullCriticalSamples.Samples F.parent c → MvPolynomial (Fin (F.free c + 1)) ℝ)
    (a : BoundedFullCriticalSamples.Samples F.parent c → ℝ) (ha : ∀ p, a p ≠ 0)
    (hshape : ∀ p, BoundedCriticalSampleBlockScaling.original (TermView.term (F.source c)) p.val
      (F.offset c) (F.free c + 1) = FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c))
    (hlow : ∀ p, (low p).totalDegree < F.degree c) (hN : 1 < F.degree c)
    (hregular : ∀ p, ∀ (L : Type) [Field L] [Algebra ℝ L] (x : Fin (F.free c + 1) → L),
      aeval x (FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c)) = 0 →
        ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (low p) (a p) (F.degree c))) ≠ 0) :
    Good F c (record F c) :=
  record_good_of_exists F c (exists_record F c low a ha hshape hlow hN hregular)

end LeanCanny.Encoding.BoundedCriticalSampleDirectionChoice
