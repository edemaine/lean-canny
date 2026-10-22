/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationCompilerStateEncoding
public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.Tactic.PolyTime

/-!
# The encoded atomic instruction of the equation compiler

The packet contains an NNF atom and the unary next-variable counter. Its output
is an encoded equation system with the exact witness allocation of `equations`.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationCompiler

open LeanCanny.Encoding.Brackets Turing.MultiTapeTM

def HasTag (tag : ℕ) (bits : List Bool) : Prop := firstChild bits = (Codec.unary tag).toBits

instance (tag : ℕ) (bits : List Bool) : Decidable (HasTag tag bits) := by
  unfold HasTag
  infer_instance

theorem hasTag_fppred (tag : ℕ) : FPPred (HasTag tag) :=
  stringEq_fppred firstChild_mem_FP (constFn_mem_FP (Codec.unary tag).toBits)

def packAtom (next : ℕ) (terms : List Bool) : List Bool := pair (Codec.unary next).toBits terms

def atomBits (packet : List Bool) : List Bool :=
  let p := pairFst packet
  let i := Codec.unaryValue (pairSnd packet)
  let term := NNF.second p
  let singleton := fun t => consNode t (SumSquares.listBits [])
  if HasTag 0 p then packAtom i (SumSquares.listBits [.const 1])
  else if HasTag 1 p then packAtom i (singleton term)
  else if HasTag 2 p then packAtom (i + 1) (singleton (Term.negativeBits term i))
  else if HasTag 0 term then packAtom i (SumSquares.listBits [])
  else if HasTag 1 term then packAtom (i + 1) (singleton (Term.nonzeroBits (NNF.second term) i))
  else packAtom (i + 1) (singleton (Term.nonnegativeBits (NNF.second term) i))

-- Native certificates keep named writers opaque during compositional search.
@[program_certificate]
theorem hasTag_computable {bits : List Bool → List Bool} (tag : ℕ)
    [DecidablePred (fun z => HasTag tag (bits z))]
    (hb : ComputableTidilyInPolyTime bits encBits encBits) :
    ComputableTidilyInPolyTime (fun z => decide (HasTag tag (bits z))) encBits encBool :=
  ((hasTag_fppred tag).comp hb).computable

@[program_certificate]
theorem packAtom_computable {next : List Bool → ℕ} {terms : List Bool → List Bool}
    (hn : ComputableTidilyInPolyTime next encBits encUnary)
    (ht : ComputableTidilyInPolyTime terms encBits encBits) :
    ComputableTidilyInPolyTime (fun z => packAtom (next z) (terms z)) encBits encBits :=
  pair_computable (Codec.unary_toBits_mem_FP hn) ht

@[program_certificate]
theorem atomBits_mem_FP :
    ComputableTidilyInPolyTime atomBits encBits encBits := by
  polytime [atomBits]

def Atomic : SignedFormula → Prop
  | .and _ _ | .or _ _ => False
  | _ => True

theorem atomBits_encode (p : SignedFormula) (start : ℕ) (hp : Atomic p) :
    atomBits (pair p.toFormula.encode (Codec.unary start).toBits) = (p.equations start).encode := by
  cases p <;>
    simp_all [Atomic, atomBits, packAtom, HasTag, SignedFormula.toFormula,
      Formula.encode, Formula.toData, NNF.second, remainingChildren_toBits, firstChild_toBits,
      Codec.unary_toBits_injective.eq_iff, EquationSystem.encode, SignedFormula.equations,
      SumSquares.listBits, consNode_toBits]

end LeanCanny.ETR.EquationCompiler
