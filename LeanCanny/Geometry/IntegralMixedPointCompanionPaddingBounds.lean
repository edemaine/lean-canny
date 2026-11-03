/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionPadding
/-! # Exact physical padding counts and native original byte ceilings

Only the original seed code is repeated. Its producer-label bytes do not
grow with the padding length, although actual rules and denominators change.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m B : ℕ} {P : SpatialSource n}

def paddingByteBound (n m B k : ℕ):=(2*IntegralMixedCutRecordConstructor.codeBudget n m B+2)*k

theorem padding_bytes (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (k : ℕ) :
    (WordList.encode (codes frozen double rows g (List.replicate k g)).reverse).length≤paddingByteBound n m B k :=by
  rw [codes_replicate,List.reverse_replicate]
  have HC :=(pointData frozen double rows g 0 g).code_length.trans
    (IntegralMixedCutRecordConstructor.critical_codeBudget_le n m B)
  have H:=WordList.length_le (List.replicate k (pointData frozen double rows g 0 g).code)
    (IntegralMixedCutRecordConstructor.codeBudget n m B) (by
      intro w hw
      obtain rfl:=List.eq_of_mem_replicate hw
      exact HC)
  simpa only [List.length_replicate,paddingByteBound] using H

theorem paddingByteBound_unary {N M W K : List Bool→ℕ} (hN : UnaryFn N) (hM : BinaryFn M)
    (hW : UnaryFn W) (hK : UnaryFn K) : UnaryFn (fun z=>paddingByteBound (N z) (M z) (W z) (K z)) :=by
  have HC:=IntegralMixedCutRecordConstructor.codeBudget_unary hN hM hW
  exact (((UnaryFn.const 2).mul HC).add (UnaryFn.const 2)).mul hK

theorem padding_columns {ι : Type} [Fintype ι] (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (k : ℕ) :
    Fintype.card (Index ι (commands (P:=P) (B:=B) frozen double rows g (List.replicate k g)))=
      Fintype.card ι+(2*n+4)*k :=by
  simpa only [List.length_replicate] using physical_columns (P:=P) (B:=B) frozen double rows g (List.replicate k g)

theorem paddingColumnBound_unary {N L K : List Bool→ℕ} (hN : UnaryFn N) (hL : UnaryFn L)
    (hK : UnaryFn K) : UnaryFn (fun z=>L z+(2*N z+4)*K z) :=
  hL.add ((((UnaryFn.const 2).mul hN).add (UnaryFn.const 4)).mul hK)

variable {S : ℕ} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (p : Fin (n+1)→ℝ) (k : ℕ)
    (room : m+(List.replicate k g).length≤S+1)
    (R : Realized x frozen double rows g z φ old p (List.replicate k g) room)

theorem Realized.padding_value (i : Fin k) :
    R.hom ((run x frozen double rows g (List.replicate k g) room).bank.numerator
      ⟨i.val,by simp only [List.length_replicate];have :=i.isLt;omega⟩)/
    ((run x frozen double rows g (List.replicate k g) room).bank.denominator
      ⟨i.val,by simp only [List.length_replicate];have :=i.isLt;omega⟩:ℝ)=p g.val :=
  (R.quotients _).trans (values_replicate frozen g p old k i)

end LeanCanny.Geometry.IntegralMixedPointCompanion
