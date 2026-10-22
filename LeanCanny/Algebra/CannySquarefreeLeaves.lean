/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SquarefreeLeafMatrix
public import LeanCanny.Algebra.BerkowitzPolynomialBranch
public import LeanCanny.Algebra.CannyResultantRecursiveStage
public import LeanCanny.Algebra.BerkowitzSingleCallSource
public import LeanCanny.Computation.SingleCallLeaf

/-! # A mixed square-free-leaf and resultant-node coefficient source

Leaves use a one-by-one matrix containing the scaled square-free polynomial;
internal nodes use the actual Canny Sylvester matrix. The same one-request
state handles both cases. Native leaf computation needs no recursive child or
execution clock. The concrete balanced-tree contexts and graph bounds remain
parameters of the uniform evaluation theorem.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.WithSquarefreeLeaves
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open BerkowitzPolynomial.TaskDispatch

variable (L : SeparableBits.Family) {F : Family} (a : Access F) (select : List Bool → Bool)

noncomputable def leafAccess : BerkowitzPolynomial.ModularAccess (SeparableBits.LeafMatrix.family L F.degree) :=
  SeparableBits.LeafMatrix.access L F.degree a.degree a.degree_eq

noncomputable def family : BerkowitzPolynomial.ModularFamily :=
  BerkowitzPolynomial.ModularFamily.branch select (SeparableBits.LeafMatrix.family L F.degree) F.modular.determinant

noncomputable def access : BerkowitzPolynomial.ModularAccess (family L (F := F) select) :=
  BerkowitzPolynomial.ModularAccess.branch select (leafAccess L a) a.modular.determinant

def entrySelect (p : List Bool) : Bool := select (pairFst p)

noncomputable def program (leftTask rightTask : List Bool → List Bool) : SingleCall.Program :=
  (RecursiveStage.program a leftTask rightTask).withLeaf (entrySelect select) (leafAccess L a).entry

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul BinaryNat.mulMod
  BinaryNat.powMod SeparableBits.squarefreeValue RecursiveStage.selectRight RecursiveStage.request
  RecursiveStage.leftQuery RecursiveStage.rightQuery

theorem controls (ha : a.ControlsPolyTime) (hs : (fun c => [select c]) ∈ FP) :
    (access L a select).ControlsPolyTime :=
  BerkowitzPolynomial.ModularAccess.branch_controls select (leafAccess L a) a.modular.determinant hs
    (SeparableBits.LeafMatrix.controls L F.degree a.degree a.degree_eq ha.degree)
    (a.modular.determinant_controls (a.modular_controlsWithCoefficients ha))

theorem certificates (A : SeparableBits.Readers L) (ha : a.ControlsPolyTime)
    (hs : (fun c => [select c]) ∈ FP) (leftTask rightTask : List Bool → List Bool)
    (hl : leftTask ∈ FP) (hr : rightTask ∈ FP) : (program L a select leftTask rightTask).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) := by
  have hselect := mem_FP_comp pairFst_mem_FP hs
  have hquery := (flag_computable (RecursiveStage.selectRight_FP a ha)).ite'
    (mem_FP_comp RecursiveStage.rightQuery_FP hr) (mem_FP_comp (RecursiveStage.leftQuery_FP a ha) hl)
  exact (RecursiveStage.program a leftTask rightTask).withLeaf_certificates (entrySelect select) (leafAccess L a).entry
    hselect (RecursiveStage.request_FP a ha) hquery (SpaceFunction.ofFP _ (constFn_mem_FP []))
    (RecursiveStage.finish_space a ha) (SeparableBits.LeafMatrix.entry_space L A F.degree a.degree a.degree_eq)

theorem value_eq (leftTask rightTask answer : List Bool → List Bool)
    (hl : ∀ p, answer (leftTask p) = a.leftCoefficient p)
    (hr : ∀ p, answer (rightTask p) = a.rightCoefficient p) (p : List Bool) :
    (program L a select leftTask rightTask).value answer p = (access L a select).entry p := by
  simp only [program, SingleCall.Program.withLeaf_value, RecursiveStage.value_eq a leftTask rightTask answer hl hr p,
    access, BerkowitzPolynomial.ModularAccess.branch, entrySelect]

theorem leaf_needs_false (leftTask rightTask answer : List Bool → List Bool) (p : List Bool) (t : ℕ)
    (hs : select (pairFst p) = true) :
    (program L a select leftTask rightTask).controller.needs
      (((program L a select leftTask rightTask).controller.reference answer)^[t] (SingleCall.Program.initial p)) = false := by
  exact (RecursiveStage.program a leftTask rightTask).withLeaf_needs_iterate (entrySelect select) (leafAccess L a).entry answer p t |>.trans
    (by simp only [entrySelect, hs, ite_true])

theorem source_levels (leftTask rightTask : List Bool → List Bool)
    (tasks : List Bool → List Bool → Prop) (level : List Bool → ℕ)
    (hl : ∀ p, select (pairFst p) = false → RecursiveStage.request a p = true →
      RecursiveStage.selectRight a p = false → isZero (leftTask (RecursiveStage.leftQuery a p)) = false →
      level (origin (leftTask (RecursiveStage.leftQuery a p))) < level (pairFst p))
    (hr : ∀ p, select (pairFst p) = false → RecursiveStage.request a p = true →
      RecursiveStage.selectRight a p = true → isZero (rightTask (RecursiveStage.rightQuery p)) = false →
      level (origin (rightTask (RecursiveStage.rightQuery p))) < level (pairFst p)) :
    SourceLevels (access L a select) (program L a select leftTask rightTask).controller (fun _ => 1) tasks level := by
  apply singleCall_source_levels
  intro p hreq hz
  have hs : select (pairFst p) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    simp only [program, SingleCall.Program.withLeaf, entrySelect, hs, ite_true, Bool.false_eq_true] at hreq
  have hn : RecursiveStage.request a p = true := by
    simpa only [program, SingleCall.Program.withLeaf, entrySelect, hs, Bool.false_eq_true, ite_false,
      RecursiveStage.program] using hreq
  change isZero (if RecursiveStage.selectRight a p then rightTask (RecursiveStage.rightQuery p)
    else leftTask (RecursiveStage.leftQuery a p)) = false at hz
  change level (origin (if RecursiveStage.selectRight a p then rightTask (RecursiveStage.rightQuery p)
    else leftTask (RecursiveStage.leftQuery a p))) < level (pairFst p)
  cases hb : RecursiveStage.selectRight a p with
  | true =>
    simp only [hb, ite_true] at hz ⊢
    exact hr p hs hn hb hz
  | false =>
    simp only [hb, Bool.false_eq_true, ite_false] at hz ⊢
    exact hl p hs hn hb hz

theorem family_value (c : List Bool) :
    (family L (F := F) select).value c = if select c then
      SeparableBits.squarefreeValue L (pair c (BinaryNatCode.encode (F.degree (pairFst c)))) else F.value c := by
  rw [family, BerkowitzPolynomial.ModularFamily.branch_value, SeparableBits.LeafMatrix.value_eq]
  change (if select c then _ else F.modular.value c) = _
  rw [F.modular_value]

/-- One native machine evaluates the mixed leaf/resultant graph. The input
polynomial leaf readers are certified; the internal original-coefficient
answers are supplied solely by child-task semantics and ranked query closure. -/
theorem evaluator (A : SeparableBits.Readers L) (ha : a.ControlsPolyTime)
    (hs : (fun c => [select c]) ∈ FP) (leftTask rightTask : List Bool → List Bool)
    (hlFP : leftTask ∈ FP) (hrFP : rightTask ∈ FP)
    (hl : ∀ p, answer (access L a select) (leftTask p) = a.leftCoefficient p)
    (hr : ∀ p, answer (access L a select) (rightTask p) = a.rightCoefficient p)
    (tasks : List Bool → List Bool → Prop) (level H K M : List Bool → ℕ)
    (hH : UnaryFn H) (hK : UnaryFn K) (hM : UnaryFn M)
    (hroot : ∀ q, tasks q q)
    (hlevels : ∀ root q, tasks root q → level (origin q) ≤ H root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer (access L a select) q).length ≤ K root)
    (hclosed : QueriesClosed (access L a select) (program L a select leftTask rightTask).controller (fun _ => 1) tasks)
    (hlevel : SourceLevels (access L a select) (program L a select leftTask rightTask).controller (fun _ => 1) tasks level)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q →
      determinantFields (F := family L (F := F) select) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q →
      momentFields (F := family L (F := F) select) (payload q) ≤ M root) :
    SpaceFunction (family L (F := F) select).value := by
  have E := singleCall_evaluator (access L a select) (program L a select leftTask rightTask)
    (controls L a select ha hs) (certificates L a select A ha hs leftTask rightTask hlFP hrFP)
    (value_eq L a select leftTask rightTask (answer (access L a select)) hl hr)
    tasks level H K M hH hK hM hroot hlevels hword hanswer hclosed hlevel hdet hmoment
  exact determinant_reader (access L a select) E

end LeanCanny.Algebra.CannyResultantBits.WithSquarefreeLeaves
