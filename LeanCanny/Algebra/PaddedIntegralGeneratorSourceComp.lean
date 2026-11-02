/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralGeneratorSource

/-! # Native source-word composition preserves full companion queries

Only the source word is rewritten. The caller modulus and both arbitrary
basis-index words are copied literally, retaining their modular semantics.
The interpreted source copies its entire algebra, basis and polynomial.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Source.comp (S : Source) (f : List Bool→List Bool) : Source where
  arity c := S.arity (f c)
  width c := S.width (f c)
  carrier c := S.carrier (f c)
  ring c := S.ring (f c)
  nontrivial c := S.nontrivial (f c)
  basis c := S.basis (f c)
  polynomial c := S.polynomial (f c)
  degree c := S.degree (f c)

def compQuery (f : List Bool→List Bool) (q : List Bool) :=
  pair (pair (f (base q)) (modulus q)) (pair (row q) (col q))

theorem compQuery_FP {f : List Bool→List Bool} (hf : f∈FP) : compQuery f∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp base_FP hf) modulus_FP) (mem_FP_pair row_FP col_FP)

theorem Source.comp_matrix (S : Source) (f : List Bool→List Bool) (c : List Bool) :
    (S.comp f).matrix c=S.matrix (f c) := rfl

noncomputable def Source.rawEntry (S : Source) (c : List Bool) (r t : ℕ) : ℤ :=
  S.matrix c
    ⟨r % count (S.arity c+1) (S.width c),Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count (S.arity c+1) (S.width c),Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def integerResidue (m : ℕ) (z : ℤ) : List Bool := residueBits (z : ZMod m)

theorem value_raw (S : Source) (q : List Bool) :
    value S q=integerResidue (Nat.fromBitsLE (modulus q)+1)
      (S.rawEntry (base q) (Nat.fromBitsLE (row q)) (Nat.fromBitsLE (col q))) := rfl

theorem Source.comp_rawEntry (S : Source) (f : List Bool→List Bool) (c : List Bool) (r t : ℕ) :
    (S.comp f).rawEntry c r t=S.rawEntry (f c) r t := rfl

attribute [local irreducible] Source.matrix Source.rawEntry integerResidue

theorem value_comp (S : Source) (f : List Bool→List Bool) (q : List Bool) :
    value (S.comp f) q=value S (compQuery f q) := by
  rw [value_raw,value_raw,Source.comp_rawEntry]
  simp only [compQuery,base,modulus,row,col,pairFst_pair,pairSnd_pair]

theorem comp_evaluator (S : Source) (f : List Bool→List Bool) (hf : f∈FP)
    (E : SpaceFunction (value S)) : SpaceFunction (value (S.comp f)) :=
  (E.precompose (compQuery f) (compQuery_FP hf)).congr (funext fun q=>(value_comp S f q).symm)

end LeanCanny.Algebra.PaddedIntegralGeneratorSource
