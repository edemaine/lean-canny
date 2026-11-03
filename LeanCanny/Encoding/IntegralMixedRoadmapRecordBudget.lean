/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointTrace
/-! # Original bounds for the literal recursive record chain

The cap and code budget are fixed from dimension, initial birth count and
scalar width, before allocating sample words. Both critical and relative-cut
constructors fit this budget. The physical-column estimate applies to actual
mixed scripts, including their auxiliary critical blocks. This does not yet
identify a graph edge relation or bound the complete sampler's word width.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical

def maxBirth (n initial : ℕ) :=initial+recordBound n
def probedRecordBound (n : ℕ) :=recordBound n+1
def fullBirth (n initial : ℕ) :=maxBirth n initial+1
def cap (n initial : ℕ) :=fullBirth n initial+2
def codeBound (n initial B : ℕ) :=IntegralMixedCutRecordConstructor.codeBudget n (maxBirth n initial) B
def wordBound (n initial B : ℕ) :=byteBound n (codeBound n initial B)
def columnBound (n initialColumns : ℕ) :=initialColumns+(2*n+4)*recordBound n

theorem maxBirth_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>maxBirth (n q) (initial q)) :=hi.add (recordBound_unary hn)

theorem cap_unary {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    UnaryFn (fun q=>cap (n q) (initial q)) :=
  ((maxBirth_unary hn hi).add (UnaryFn.const 1)).add (UnaryFn.const 2)

theorem cap_eq_probed (n initial : ℕ) : cap n initial=initial+probedRecordBound n+2 :=by
  unfold cap fullBirth maxBirth probedRecordBound
  omega

theorem codeBound_unary {n initial B : List Bool→ℕ} (hn : UnaryFn n)
    (hi : BinaryFn initial) (hB : UnaryFn B) : UnaryFn (fun q=>codeBound (n q) (initial q) (B q)) :=
  IntegralMixedCutRecordConstructor.codeBudget_unary hn
    (hi.add (BinaryFn.ofUnary (recordBound_unary hn))) hB

theorem wordBound_unary {n initial B : List Bool→ℕ} (hn : UnaryFn n)
    (hi : BinaryFn initial) (hB : UnaryFn B) : UnaryFn (fun q=>wordBound (n q) (initial q) (B q)) :=
  byteBound_unary hn (codeBound_unary hn hi hB)

theorem columnBound_unary {n columns : List Bool→ℕ} (hn : UnaryFn n) (hc : UnaryFn columns) :
    UnaryFn (fun q=>columnBound (n q) (columns q)) :=
  hc.add ((((UnaryFn.const 2).mul hn).add (UnaryFn.const 4)).mul (recordBound_unary hn))

theorem critical_code_length {n initial B birth : ℕ} (hbirth : birth≤maxBirth n initial)
    (d : IntegralMixedCriticalRecordConstructor.Data n birth) : d.code.length≤codeBound n initial B :=
  d.code_length.trans ((IntegralMixedCutRecordConstructor.critical_codeBudget_le n birth B).trans
    (LeanCanny.Geometry.IntegralMixedOptionalEndpoints.codeBudget_mono n B _ _ hbirth))

def criticalWord {n initial B birth : ℕ} (hbirth : birth≤maxBirth n initial)
    (d : IntegralMixedCriticalRecordConstructor.Data n birth) : Word (codeBound n initial B) :=
  ⟨d.code,critical_code_length hbirth d⟩

theorem cut_code_length {n initial B birth : ℕ} (hbirth : birth≤maxBirth n initial)
    (d : IntegralMixedCutRecordConstructor.Data n birth) (tag : IntegralMixedCausalRecordBits.Tag)
    (choice degree : ℕ) (hc : choice≤2^B) (hd : degree≤2^B) :
    (d.code tag choice degree).length≤codeBound n initial B :=
  (d.code_length tag choice degree hc hd).trans
    (LeanCanny.Geometry.IntegralMixedOptionalEndpoints.codeBudget_mono n B _ _ hbirth)

def cutWord {n initial B birth : ℕ} (hbirth : birth≤maxBirth n initial)
    (d : IntegralMixedCutRecordConstructor.Data n birth) (tag : IntegralMixedCausalRecordBits.Tag)
    (choice degree : ℕ) (hc : choice≤2^B) (hd : degree≤2^B) : Word (codeBound n initial B) :=
  ⟨d.code tag choice degree,cut_code_length hbirth d tag choice degree hc hd⟩

theorem raw_point_code_length {n initial B birth : ℕ} (hbirth : birth≤maxBirth n initial)
    (w : List Bool) (g j : ℕ) (H : IntegralMixedChronologicalFrameCode.PointGood n birth w g j) :
    (IntegralMixedChronologicalFrameCode.code n w g j).length≤codeBound n initial B :=by
  rw [←IntegralMixedChronologicalFrameCode.rawData_code n birth w g j H]
  exact critical_code_length hbirth _

theorem Records.original_word_length {n initial B labels : ℕ}
    (R : Records n (codeBound n initial B) labels) : R.word.length≤wordBound n initial B :=
  R.word_length_le

theorem Records.room {n initial B labels : ℕ} (R : Records n (codeBound n initial B) labels) :
    initial+R.codes.length+1<cap n initial :=by
  have HC:=R.codes_length_le
  unfold cap fullBirth maxBirth
  omega

theorem actual_physical_columns {n B initialColumns : ℕ} {P : SpatialSource n} {ι : Type}
    [Fintype ι] (hι : Fintype.card ι≤ initialColumns) (cs : List (Command P B))
    (hlen : cs.length≤recordBound n) : Fintype.card (Index ι cs)≤columnBound n initialColumns :=by
  rw [physical_arity]
  have HC : criticalCount cs≤cs.length:=List.countP_le_length
  have HM:=Nat.mul_le_mul_left (2*n+3) HC
  have HE : cs.length+(2*n+3)*cs.length=(2*n+4)*cs.length:=by ring
  unfold columnBound
  calc
    Fintype.card ι+cs.length+(2*n+3)*criticalCount cs
      ≤ initialColumns+(cs.length+(2*n+3)*cs.length):=by omega
    _=initialColumns+(2*n+4)*cs.length:=by rw [HE]
    _≤ initialColumns+(2*n+4)*recordBound n:=Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _

end LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
