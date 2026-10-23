/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionComposition
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Algebra.ModularNegFP

/-! # Compositional raw residue readers

Space certificates compose arbitrary binary readers. Pointwise correctness only
requires canonical residues at the query being interpreted; no global invariant
on malformed queries is imposed. Moduli use binary predecessor words.
-/

@[expose] public section
namespace LeanCanny.Algebra.ModularResidueSpace
open LeanCanny.Encoding

variable (modulus : List Bool → List Bool)
abbrev m (c : List Bool) : ℕ := Nat.fromBitsLE (modulus c) + 1

def prepare (q : List Bool) : List Bool :=
  pair (BinaryNat.succ (modulus (pairFst q))) (pairSnd q)

theorem prepare_mem_FP (hm : modulus ∈ FP) : prepare modulus ∈ FP := by
  have h := mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

end LeanCanny.Algebra.ModularResidueSpace

namespace LeanCanny.Algebra.ModularResidueReaders
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def addValue (modulus f g : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNat.succ (modulus c)) (pair (f c) (g c)))
def negValue (modulus f : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (modulus c)) (f c))
noncomputable def maskValue (p : List Bool → Prop) (f : List Bool → List Bool)
    (c : List Bool) : List Bool := if p c then f c else []

theorem addEvaluator {modulus f g : List Bool → List Bool} (hm : modulus ∈ FP)
    (F : SpaceFunction f) (G : SpaceFunction g) : SpaceFunction (addValue modulus f g) := by
  have E := (F.pairOutputs G).withInput.postcompose _
    (mem_FP_comp (ModularResidueSpace.prepare_mem_FP modulus hm) ArithmeticBits.addMod_mem_FP)
  exact E.congr (funext fun c => by simp only [Function.comp_apply, ModularResidueSpace.prepare,
    pairFst_pair, pairSnd_pair, addValue])

theorem negEvaluator {modulus f : List Bool → List Bool} (hm : modulus ∈ FP)
    (F : SpaceFunction f) : SpaceFunction (negValue modulus f) := by
  have E := F.withInput.postcompose _
    (mem_FP_comp (ModularResidueSpace.prepare_mem_FP modulus hm) ArithmeticBits.negate_mem_FP)
  exact E.congr (funext fun c => by simp only [Function.comp_apply, ModularResidueSpace.prepare,
    pairFst_pair, pairSnd_pair, negValue])

theorem maskEvaluator {p : List Bool → Prop} {f : List Bool → List Bool}
    (hp : FPPred p) (F : SpaceFunction f) : SpaceFunction (maskValue p f) := by
  have E := SpaceFunction.branch (fun c => decide (p c)) hp.flag_mem_FP F
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun c => by simp only [maskValue, decide_eq_true_eq])

theorem addValue_eq (modulus f g : List Bool → List Bool) (c : List Bool)
    (a b : ZMod (ModularResidueSpace.m modulus c))
    (hf : f c = residueBits a) (hg : g c = residueBits b) :
    addValue modulus f g c = residueBits (a + b) := by
  let : NeZero (ModularResidueSpace.m modulus c) := ⟨by unfold ModularResidueSpace.m; omega⟩
  rw [addValue, hf, hg, BinaryNat.succ_eq_bits]
  exact ArithmeticBits.addMod_residueBits _ _ _

theorem negValue_eq (modulus f : List Bool → List Bool) (c : List Bool)
    (a : ZMod (ModularResidueSpace.m modulus c)) (hf : f c = residueBits a) :
    negValue modulus f c = residueBits (-a) := by
  let : NeZero (ModularResidueSpace.m modulus c) := ⟨by unfold ModularResidueSpace.m; omega⟩
  rw [negValue, hf, BinaryNat.succ_eq_bits]
  exact ArithmeticBits.negate_residueBits _ _

theorem maskValue_eq (p : List Bool → Prop) (f : List Bool → List Bool) (c : List Bool)
    {m : ℕ} (a : ZMod m) (hf : f c = residueBits a) :
    maskValue p f c = residueBits (if p c then a else 0) := by
  by_cases h : p c
  · simpa only [maskValue, h, ite_true] using hf
  · simp [maskValue, h, residueBits, BinaryNatCode.encode]

/-- A native reader with canonical residue semantics on its declared domain.
The domain permits partially prepared contexts without imposing any new
invariant on malformed packets. -/
structure Reader (modulus : List Bool → List Bool)
    (meaning : (c : List Bool) → ZMod (ModularResidueSpace.m modulus c))
    (valid : List Bool → Prop := fun _ => True) where
  value : List Bool → List Bool
  evaluator : SpaceFunction value
  correct : ∀ c, valid c → value c = residueBits (meaning c)

namespace Reader
variable {modulus : List Bool → List Bool}
variable {a b : (c : List Bool) → ZMod (ModularResidueSpace.m modulus c)}
variable {valid : List Bool → Prop}

def add (A : Reader modulus a valid) (B : Reader modulus b valid) (hm : modulus ∈ FP) :
    Reader modulus (fun c => a c + b c) valid where
  value := addValue modulus A.value B.value
  evaluator := addEvaluator hm A.evaluator B.evaluator
  correct c hc := addValue_eq modulus _ _ c _ _ (A.correct c hc) (B.correct c hc)

def neg (A : Reader modulus a valid) (hm : modulus ∈ FP) :
    Reader modulus (fun c => -a c) valid where
  value := negValue modulus A.value
  evaluator := negEvaluator hm A.evaluator
  correct c hc := negValue_eq modulus _ c _ (A.correct c hc)

noncomputable def mask (A : Reader modulus a valid) (p : List Bool → Prop) (hp : FPPred p) :
    Reader modulus (fun c => if p c then a c else 0) valid where
  value := maskValue p A.value
  evaluator := maskEvaluator hp A.evaluator
  correct c hc := maskValue_eq p _ c _ (A.correct c hc)

/-- Semantic replacement preserves the native function definitionally. -/
def congr (A : Reader modulus a valid) (h : ∀ c, valid c → a c = b c) : Reader modulus b valid where
  value := A.value
  evaluator := A.evaluator
  correct c hc := by rw [← h c hc]; exact A.correct c hc

def precompose (A : Reader modulus a valid) (input : List Bool → List Bool) (hi : input ∈ FP) :
    Reader (modulus ∘ input) (fun c => a (input c)) (valid ∘ input) where
  value := A.value ∘ input
  evaluator := A.evaluator.precompose input hi
  correct c hc := A.correct (input c) hc

end Reader

end LeanCanny.Algebra.ModularResidueReaders
