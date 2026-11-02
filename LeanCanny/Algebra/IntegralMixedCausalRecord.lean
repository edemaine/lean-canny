/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeaders
public import LeanCanny.Algebra.IntegralMixedAffineCode
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQGrowth
/-! # Original causal records omit the interpreted slope

An original record stores the spatial source, affine rows, scales, frozen
height and cut labels. Instantiation inserts current bank Q only into the
mathematical cut slope; header values are independent of that insertion.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalRecordBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCommandHeaderBits (Header)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

inductive Tag where
  | coordinate | squarefree | value | limitCoordinate
  deriving DecidableEq

structure Cut {n : ℕ} (P : SpatialSource n) (B : ℕ) where
  critical : CriticalRule n
  height : Fin (n+1)
  frozen : height.val<critical.offset.val
  tag : Tag
  coordinate : ℕ
  choice : ℕ
  degree : ℕ
  source_cap : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree
  degree_cap : degree≤2^B
  current : Bool

noncomputable def Cut.rule {n B : ℕ} {P : SpatialSource n} (r : Cut P B) (Q : ℤ) (hQ : Q≠0) : IntegralMixedCriticalSweep.Rule n where
  critical := r.critical
  height := r.height
  height_frozen := r.frozen
  slope := if r.current then Q else 1
  slope_ne_zero := by split_ifs; exact hQ; exact one_ne_zero

noncomputable def Cut.kind {n B : ℕ} {P : SpatialSource n} (r : Cut P B) (Q : ℤ) (hQ : Q≠0) :
    IntegralMixedRelativeCuts.Kind P (r.rule Q hQ) :=
  let j : Fin (n-r.critical.offset.val+1) := ⟨r.coordinate%(n-r.critical.offset.val+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
  match r.tag with
  | .coordinate => .coordinate j ⟨r.choice%IntegralMixedCoordinateTrailing.ChoiceBound P (r.rule Q hQ),Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .squarefree => .squarefree j ⟨r.choice%IntegralMixedCoordinateSquarefree.coordinateDegree P (r.rule Q hQ),Nat.mod_lt _ (by
      unfold IntegralMixedCoordinateSquarefree.coordinateDegree PurePowerReductionBounds.dimension FixedWidthPolynomial.count
      exact pow_pos (Nat.two_pow_pos _) _)⟩
  | .value => .value j ⟨r.choice%IntegralMixedValueTrailing.ChoiceBound P (r.rule Q hQ),Nat.mod_lt _ (by
      unfold IntegralMixedValueTrailing.ChoiceBound
      omega)⟩
  | .limitCoordinate => .limitCoordinate j ⟨r.choice%IntegralMixedLimitCoordinate.ChoiceBound P (r.rule Q hQ),Nat.mod_lt _ (Nat.succ_pos _)⟩

inductive Template {n : ℕ} (P : SpatialSource n) (B : ℕ) where
  | integer (polynomial : Polynomial ℤ) (nonzero : polynomial≠0) (degree_cap : polynomial.natDegree≤2^B)
  | critical (rule : CriticalRule n)
  | cut (rule : Cut P B)

noncomputable def Template.command {n B : ℕ} {P : SpatialSource n} (r : Template P B) (Q : ℤ) (hQ : Q≠0) :
    IntegralMixedFullHistoryScript.Command P B :=
  match r with
  | .integer p hp hd => .integer p hp hd
  | .critical c => .critical c
  | .cut c => .cut (c.rule Q hQ) (c.kind Q hQ) c.degree c.source_cap c.degree_cap

structure Record (n B : ℕ) where
  source : SpatialSource n
  source_cap : PurePowerReductionBounds.dimension (n+1) source.degree≤2^B
  template : Template source B

noncomputable def instantiate {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) : Instruction n B where
  source := r.source
  source_cap := r.source_cap
  command := r.template.command (commonDenominator x) (commonDenominator_ne_zero x)

theorem instantiate_congr {n S T B m k : ℕ} {P Q : SpatialSource n} {ι κ : Type}
    (x : State P S B m ι) (y : State Q T B k κ) (r : Record n B) (h : commonDenominator x=commonDenominator y) :
    instantiate x r=instantiate y r := by
  have HC (a b : ℤ) (ha : a≠0) (hb : b≠0) (hab : a=b) : r.template.command a ha=r.template.command b hb := by
    subst b
    rfl
  exact congrArg (fun cmd => Instruction.mk r.source r.source_cap cmd)
    (HC _ _ _ _ h)

noncomputable def Template.header {n B : ℕ} {P : SpatialSource n} (r : Template P B) : Header :=
  IntegralMixedCommandHeaderBits.command (r.command 1 one_ne_zero)

theorem Template.header_command {n B : ℕ} {P : SpatialSource n} (r : Template P B) (Q : ℤ) (hQ : Q≠0) :
    IntegralMixedCommandHeaderBits.command (r.command Q hQ)=r.header := by
  cases r with
  | integer => rfl
  | critical => rfl
  | cut c =>
    cases ht : c.tag <;> simp only [Template.header,Template.command,IntegralMixedCommandHeaderBits.command,Cut.kind,ht] <;> rfl

theorem instantiate_header {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) :
    IntegralMixedCommandHeaderBits.command (instantiate x r).command=r.template.header :=
  r.template.header_command _ _

/-- Original affine/scales metadata contains no Q field. -/
noncomputable def Template.body {n B : ℕ} {P : SpatialSource n} : Template P B → List Bool
  | .integer .. => []
  | .critical c => WordList.encode [WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode (c.heights i))),
      WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode (c.scales i)))]
  | .cut c => WordList.encode [WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode (c.critical.heights i))),
      WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode (c.critical.scales i))),
      BinaryNatCode.encode c.height.val]

noncomputable def commandBody {n B : ℕ} {P : SpatialSource n} : IntegralMixedFullHistoryScript.Command P B → List Bool
  | .integer .. => []
  | .critical c => WordList.encode [WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode (c.heights i))),
      WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode (c.scales i)))]
  | .cut c _ _ _ _ => WordList.encode [WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode (c.critical.heights i))),
      WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode (c.critical.scales i))),BinaryNatCode.encode c.height.val]

theorem Template.body_command {n B : ℕ} {P : SpatialSource n} (r : Template P B) (Q : ℤ) (hQ : Q≠0) :
    commandBody (r.command Q hQ)=r.body := by cases r <;> rfl

theorem instantiate_body {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) : commandBody (instantiate x r).command=r.template.body :=
  r.template.body_command _ _

end LeanCanny.Algebra.IntegralMixedCausalRecordBits
