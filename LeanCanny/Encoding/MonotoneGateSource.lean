/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.TermArityFP
public import LeanCanny.Computation.PolyTimeRange
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # A native polynomial-size equation writer for unique arithmetic gate values

Each wire has two circular witness variables and one value variable. Values
of earlier wires are referenced by name, so AND squares its child values
without expanding their expressions. The complete source is a single sum of
squares of the gate equations and the root value. There are no selectors.
-/
@[expose] public section
namespace LeanCanny.Encoding.MonotoneGateSource
open LeanCanny.Computation ETR
open scoped Classical

structure Family where
  dimension : List Bool → ℕ
  count : List Bool → ℕ
  kind : List Bool → ℕ
  left : List Bool → ℕ
  right : List Bool → ℕ
  atom : List Bool → Term

structure Access (F : Family) : Prop where
  dimension : UnaryFn F.dimension
  count : UnaryFn F.count
  kind : BinaryFn F.kind
  left : UnaryFn F.left
  right : UnaryFn F.right
  atom : (fun q => (F.atom q).toData.toBits) ∈ FP

def index (q : List Bool) : ℕ := (pairSnd q).length
def dimension (F : Family) (q : List Bool) : ℕ := F.dimension (pairFst q)
def count (F : Family) (q : List Bool) : ℕ := F.count (pairFst q)
def witnessIndex (F : Family) (q : List Bool) (b : Bool) : ℕ := dimension F q+2*index q+b.toNat
def valueIndex (F : Family) (q : List Bool) (i : ℕ) : ℕ := dimension F q+2*count F q+i

def child (F : Family) (side : Bool) (q : List Bool) : Term :=
  let i := if side then F.right q else F.left q
  if i < index q then .var (valueIndex F q i) else .const 1

def atomBody (F : Family) (q : List Bool) : Term :=
  .add (F.atom q) (.mul (.const (-1))
    (.add (.mul (.var (witnessIndex F q false)) (.var (witnessIndex F q false)))
      (.mul (.var (witnessIndex F q true)) (.var (witnessIndex F q true)))))

def body (F : Family) (q : List Bool) : Term :=
  if F.kind q=1 then .const 0 else
  if F.kind q=2 then atomBody F q else
  if F.kind q=4 then .add (.mul (child F false q) (child F false q)) (.mul (child F true q) (child F true q)) else
  if F.kind q=5 then .mul (child F false q) (child F true q) else .const 1

def constraint (F : Family) (q : List Bool) : Term :=
  .add (.var (valueIndex F q (index q))) (.mul (.const (-1)) (body F q))

def root (F : Family) (c : List Bool) : Term :=
  if F.count c=0 then .const 1 else .var (F.dimension c+2*F.count c+(F.count c-1))

def terms (F : Family) (c : List Bool) : List Term :=
  root F c :: (List.range (F.count c)).map (fun i => constraint F (pair c (List.replicate i true)))

def polynomial (F : Family) (c : List Bool) : Term := SumSquares.accumulate (terms F c) (.const 0)

private theorem variable_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun q => (Term.var (n q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Term.variableBits_mem_FP hn) (fun _ => Term.variableBits_eq _)

private theorem add_FP {a b : List Bool → Term}
    (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (Term.add (a q) (b q)).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 ha hb)
  intro q
  exact (Term.add_toBits _ _).symm

private theorem mul_FP {a b : List Bool → Term}
    (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (Term.mul (a q) (b q)).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 ha hb)
  intro q
  exact (Term.mul_toBits _ _).symm

private theorem iteTerm_FP {P : List Bool → Prop} [DecidablePred P]
    (hP : FPPred P) {a b : List Bool → Term}
    (ha : (fun q => (a q).toData.toBits) ∈ FP) (hb : (fun q => (b q).toData.toBits) ∈ FP) :
    (fun q => (if P q then a q else b q).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (hP.ite_mem_FP ha hb)
  intro q
  by_cases H : P q <;> simp only [H,ite_true,ite_false]

theorem dimension_unary (F : Family) (hF : Access F) : UnaryFn (dimension F) := hF.dimension.comp pairFst_mem_FP
theorem count_unary (F : Family) (hF : Access F) : UnaryFn (count F) := hF.count.comp pairFst_mem_FP
theorem index_unary : UnaryFn index := UnaryFn.length pairSnd_mem_FP

theorem child_FP (F : Family) (hF : Access F) (side : Bool) :
    (fun q => (child F side q).toData.toBits) ∈ FP := by
  have HI : UnaryFn (fun q => if side then F.right q else F.left q) := by cases side; exact hF.left; exact hF.right
  have HV := variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul (count_unary F hF))).add HI)
  exact iteTerm_FP (FPPred.lt HI index_unary) HV (constFn_mem_FP (Term.const 1).toData.toBits)

theorem atomBody_FP (F : Family) (hF : Access F) : (fun q => (atomBody F q).toData.toBits) ∈ FP := by
  have H0 := variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const 0))
  have H1 := variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const 1))
  exact add_FP hF.atom (mul_FP (constFn_mem_FP _) (add_FP (mul_FP H0 H0) (mul_FP H1 H1)))

theorem body_FP (F : Family) (hF : Access F) : (fun q => (body F q).toData.toBits) ∈ FP := by
  have HL := child_FP F hF false
  have HR := child_FP F hF true
  exact iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 1)) (constFn_mem_FP (Term.const 0).toData.toBits)
    (iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 2)) (atomBody_FP F hF)
      (iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 4)) (add_FP (mul_FP HL HL) (mul_FP HR HR))
        (iteTerm_FP (BinaryFn.eq hF.kind (BinaryFn.const 5)) (mul_FP HL HR) (constFn_mem_FP (Term.const 1).toData.toBits))))

theorem constraint_FP (F : Family) (hF : Access F) : (fun q => (constraint F q).toData.toBits) ∈ FP :=
  add_FP (variable_FP (((dimension_unary F hF).add ((UnaryFn.const 2).mul (count_unary F hF))).add index_unary))
    (mul_FP (constFn_mem_FP _) (body_FP F hF))

theorem root_FP (F : Family) (hF : Access F) : (fun c => (root F c).toData.toBits) ∈ FP :=
  iteTerm_FP (FPPred.eq hF.count (UnaryFn.const 0)) (constFn_mem_FP (Term.const 1).toData.toBits)
    (variable_FP ((hF.dimension.add ((UnaryFn.const 2).mul hF.count)).add (hF.count.sub (UnaryFn.const 1))))

def termsBits (F : Family) (c : List Bool) : List Bool :=
  Brackets.wrap ((root F c).toData.toBits ++
    (List.range (F.count c)).flatMap (fun i => (constraint F (pair c (List.replicate i true))).toData.toBits))

theorem termsBits_FP (F : Family) (hF : Access F) : termsBits F ∈ FP := by
  have HR := flatMap_range_mem_FP (constraint_FP F hF) hF.count.mem_FP
  have HR' : (fun c => (List.range (F.count c)).flatMap (fun i =>
      (constraint F (pair c (List.replicate i true))).toData.toBits)) ∈ FP := by
    simpa only [List.length_replicate] using HR
  exact mem_FP_comp (appendFn_mem_FP (root_FP F hF) HR') Brackets.wrap_mem_FP

theorem termsBits_eq (F : Family) (c : List Bool) : termsBits F c = SumSquares.listBits (terms F c) := by
  simp only [termsBits,terms,SumSquares.listBits,Data.toBits_l,List.map_cons,List.map_map,
    Brackets.wrap,List.flatten_eq_flatMap,List.flatMap_cons,List.flatMap_map,Function.comp_def,id_eq]

theorem polynomial_FP (F : Family) (hF : Access F) : (fun c => (polynomial F c).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (termsBits_FP F hF) SumSquares.collapse_mem_FP)
  intro c
  rw [Function.comp_apply,termsBits_eq,SumSquares.collapse_listBits]
  rfl

theorem polynomial_zero_iff (F : Family) (c : List Bool) (env : ℕ → ℝ) :
    (polynomial F c).eval env=0 ↔ (root F c).eval env=0 ∧
      ∀ i<F.count c, (constraint F (pair c (List.replicate i true))).eval env=0 := by
  rw [polynomial,SumSquares.accumulate_zero_iff]
  simp only [terms,List.mem_cons,forall_eq_or_imp,List.forall_mem_map,List.mem_range]

end LeanCanny.Encoding.MonotoneGateSource
