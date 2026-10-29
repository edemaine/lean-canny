/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceBlockCoefficient
public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Native critical-row coefficients in a flat stage block

Two native partial-derivative calls and modular arithmetic construct the
critical difference of the embedded original source. The source, block,
modulus, and all controls are charged. Copy constraints are separate rows.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceCriticalCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs arity count degree)
open FlatFullSourceBlockCoefficient (reader reader_evaluator reader_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

def flattenQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem flattenQuery_FP : flattenQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def indexedReader (F : Inputs) (O W : List Bool → ℕ)
    (modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F ∘ pairFst) (count F ∘ pairFst) (O ∘ pairFst) (W ∘ pairFst)
    pairSnd ((reader F W modulus) ∘ flattenQuery)

theorem indexedReader_evaluator {F : Inputs} (h : F.Access) {O W : List Bool → ℕ}
    (hO : UnaryFn O) (hW : UnaryFn W) {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (indexedReader F O W modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _
    ((reader_evaluator h hW hm).precompose flattenQuery flattenQuery_FP)
    ((FlatFullSourceTower.arity_unary h).comp pairFst_mem_FP)
    ((FlatFullSourceTower.count_unary h).comp pairFst_mem_FP)
    (hO.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP

theorem indexedReader_packet (F : Inputs) (O W : List Bool → ℕ) (modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ count F c) (r : ℕ) :
    indexedReader F O W modulus (pair c (BinaryNatCode.encode r)) = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit)
        (BoundedFullCriticalSamples.polynomial F.source c)).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c) r) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  apply FixedWidthBlockRenameBits.packet _ _ _ _ _ _ hfit _ z _ rfl rfl rfl
  intro k
  simp only [Function.comp_apply, flattenQuery, pairFst_pair, pairSnd_pair]
  exact reader_packet F W modulus (pairFst z) k

def modulusCode (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (modulus c) [true])
theorem modulusCode_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : modulusCode modulus ∈ FP :=
  mem_FP_comp (g := BinaryNat.add) (mem_FP_pair hm (constFn_mem_FP [true])) BinaryNat.add_mem_FP

theorem modulusCode_eq (modulus : List Bool → List Bool) (c : List Bool) :
    modulusCode modulus c = BinaryNatCode.encode (Nat.fromBitsLE (modulus c) + 1) := by
  rw [modulusCode, BinaryNat.add_pair]
  rfl

noncomputable def value (F : Inputs) (O W base selected : List Bool → ℕ)
    (target modulus direction : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthCriticalBits.value (count F) W (degree F) base selected target (modulusCode modulus) direction
    (indexedReader F O W modulus)

theorem evaluator {F : Inputs} (h : F.Access) {O W base selected : List Bool → ℕ}
    (hO : UnaryFn O) (hW : UnaryFn W) (hb : UnaryFn base) (hs : UnaryFn selected)
    {target modulus direction : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) (hv : direction ∈ FP) :
    SpaceFunction (value F O W base selected target modulus direction) :=
  FixedWidthCriticalBits.evaluator _ _ _ _ _ _ _ _ (indexedReader_evaluator h hO hW hm)
    (FlatFullSourceTower.count_unary h) hW (FlatFullSourceTower.degree_binary h) hb hs ht (modulusCode_FP hm) hv

theorem packet (F : Inputs) (O W base selected : List Bool → ℕ)
    (target modulus direction : List Bool → List Bool) (c : List Bool)
    (hfit : O c + arity F c ≤ count F c) (b i : Fin (arity F c)) (v : ℕ)
    (hb : base c = O c + b.val) (hi : selected c = O c + i.val)
    (hW : degree F c < 2 ^ W c) (hv : direction c = BinaryNatCode.encode v) :
    value F O W base selected target modulus direction c = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit)
        (ProjectionCriticalFamily.spatialEquation (BoundedFullCriticalSamples.polynomial F.source c) b
          (fun _ => (v : ℤ)) i)).coeff
            (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c)
              (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let f := BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit
  let p := BoundedFullCriticalSamples.polynomial F.source c
  have hf : Function.Injective f := BlockRenameCoefficient.shift_injective _ _ _ _
  have H := FixedWidthCriticalBits.packet (count F) W (degree F) base selected target
    (modulusCode modulus) direction (Equiv.refl (Fin (count F c))) (rename f p) (f b) (f i) v
      (Nat.fromBitsLE (modulus c)) (indexedReader F O W modulus) c rfl hb hi
      (FlatFullSourceTower.degree_pos F c)
      ((totalDegree_rename_le _ _).trans ((BoundedFullCriticalSamples.source_degree F.source c).trans (Nat.le_succ _)))
      hW (modulusCode_eq modulus c) hv (indexedReader_packet F O W modulus c hfit)
  have he : (if f i = f b then rename f p else pderiv (f i) (rename f p) - C (v : ℤ) * pderiv (f b) (rename f p)) =
      rename f (ProjectionCriticalFamily.spatialEquation p b (fun _ => (v : ℤ)) i) := by
    by_cases hib : i = b
    · simp only [hib, ite_true, ProjectionCriticalFamily.spatialEquation]
    · simp only [hf.ne hib, ite_false, ProjectionCriticalFamily.spatialEquation, hib,
        pderiv_rename hf, map_sub, map_mul, rename_C]
  rw [he] at H
  exact H

end LeanCanny.Encoding.FlatFullSourceCriticalCoefficient
