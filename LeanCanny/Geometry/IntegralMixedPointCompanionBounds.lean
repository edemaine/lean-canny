/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionReadback
public import LeanCanny.Geometry.IntegralMixedPointCompanionColumns
public import LeanCanny.Encoding.IntegralMixedJointRecordBudgetNative
/-! # Local count, physical-column and native byte bounds

These bounds charge one fixed-point capture only. They do not charge an
entire recursive incidence witness or permit changing a sampler horizon.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m B : ℕ} {P : SpatialSource n}

def codeBound (n m B q : ℕ):=IntegralMixedCutRecordConstructor.codeBudget n (m+q) B
def byteBound (n m B q : ℕ):=(2*codeBound n m B q+2)*q

theorem code_size (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) :
    ∀code∈codes frozen double rows g js,code.length≤codeBound n m B js.length :=by
  induction js with
  | nil=>simp only [codes,List.not_mem_nil,false_implies,implies_true]
  | cons j js ih=>
    intro code hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact (pointData frozen double rows g js.length j).code_length.trans
        ((IntegralMixedCutRecordConstructor.critical_codeBudget_le n (m+js.length) B).trans
          (IntegralMixedOptionalEndpoints.codeBudget_mono n B _ _ (by simp only [List.length_cons];omega)))
    · exact (ih code hc).trans (IntegralMixedOptionalEndpoints.codeBudget_mono n B _ _
        (by simp only [List.length_cons];omega))

theorem bytes (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) :
    (WordList.encode (codes frozen double rows g js).reverse).length≤byteBound n m B js.length :=by
  have H:=WordList.length_le (codes frozen double rows g js).reverse (codeBound n m B js.length)
    (fun code hc=>code_size frozen double rows g js code (List.mem_reverse.mp hc))
  simpa only [List.length_reverse,codes_length,byteBound] using H

theorem count_all_free (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) :
    (commands (P:=P) (B:=B) frozen double rows g (allFree frozen)).length≤n+1 :=by
  rw [commands_length]
  exact allFree_length frozen

theorem columns_all_free {ι : Type} [Fintype ι] (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) :
    Fintype.card (Index ι (commands (P:=P) (B:=B) frozen double rows g (allFree frozen)))≤
      Fintype.card ι+(2*n+4)*(n+1) :=by
  rw [physical_columns]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (allFree_length frozen)) _

theorem byteBound_mono (n m B a b : ℕ) (hab : a≤b) : byteBound n m B a≤byteBound n m B b :=by
  have HC:=IntegralMixedOptionalEndpoints.codeBudget_mono n B (m+a) (m+b) (Nat.add_le_add_left hab m)
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 HC) 2) hab

theorem bytes_all_free (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) :
    (WordList.encode (codes frozen double rows g (allFree frozen)).reverse).length≤byteBound n m B (n+1) :=
  (bytes frozen double rows g (allFree frozen)).trans (byteBound_mono n m B _ _ (allFree_length frozen))

theorem byteBound_unary {N M W Q : List Bool→ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hW : UnaryFn W) (hQ : UnaryFn Q) : UnaryFn (fun z=>byteBound (N z) (M z) (W z) (Q z)) :=by
  have HB:=IntegralMixedCutRecordConstructor.codeBudget_unary hN
    (hM.add (BinaryFn.ofUnary hQ)) hW
  exact (((UnaryFn.const 2).mul HB).add (UnaryFn.const 2)).mul hQ

theorem allFreeByteBound_unary {N M W : List Bool→ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hW : UnaryFn W) : UnaryFn (fun z=>byteBound (N z) (M z) (W z) (N z+1)) :=
  byteBound_unary hN hM hW (hN.add (UnaryFn.const 1))

end LeanCanny.Geometry.IntegralMixedPointCompanion
