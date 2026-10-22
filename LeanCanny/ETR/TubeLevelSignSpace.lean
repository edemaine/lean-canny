/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSignQueries
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native space certificates for the actual tube sample sign stage

A family supplies rational-level coordinate representations of the compiled
systems. Binary degree/mass budgets and native space coefficient readers for
their integer parameter and sign-query polynomials suffice to count samples
and decide sample existence. Constructing these representations and readers
with bounds in the original input remains a separate obligation.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelSign
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open TubeLevelPacket TubeEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

structure Source where
  packet : List Bool → List Bool
  mask : List Bool → List Bool
  projection : List Bool → ℕ → ℤ
  level : List Bool → ℚ
  finite : ∀ c, FiniteCompiledFibers.{0} (packet c) (level c : ℝ)
  representation : ∀ c, FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ)
    (rationalSystem (packet c) (mask c) (projection c) (level c))
  coordinates : ∀ c, IntegerCoordinatePolynomials.IntegerData (representation c)

structure Budget (S : Source) where
  rootDegree : List Bool → List Bool
  degree : List Bool → List Bool
  rootMass : List Bool → List Bool
  mass : List Bool → List Bool
  rootDegree_pos : ∀ c, 0 < Nat.fromBitsLE (rootDegree c)
  root_degree : ∀ c, (S.coordinates c).polynomial.natDegree ≤ Nat.fromBitsLE (rootDegree c)
  root_mass : ∀ c, coefficientMass (S.coordinates c).polynomial ≤ 2 ^ Nat.fromBitsLE (rootMass c)
  query_degree : ∀ c i, i < constraintCount (TubeIndexed.arity (pairFst (S.packet c))) →
    (indexedSignQuery (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c) i).natDegree ≤
      Nat.fromBitsLE (degree c)
  query_mass : ∀ c i, i < constraintCount (TubeIndexed.arity (pairFst (S.packet c))) →
    coefficientMass (indexedSignQuery (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c) i) ≤
      2 ^ Nat.fromBitsLE (mass c)

noncomputable def family (S : Source) (B : Budget S) : SignPatternBits.Family where
  root c := (S.coordinates c).polynomial
  polynomial c := indexedSignQuery (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c)
  pattern _ _ := .pos
  count c := BinaryNatCode.encode (constraintCount (TubeIndexed.arity (pairFst (S.packet c))))
  rootDegree := B.rootDegree
  degree := B.degree
  rootMass := B.rootMass
  mass := B.mass
  rootDegree_pos := B.rootDegree_pos
  root_degree := B.root_degree
  root_mass := B.root_mass
  polynomial_degree := by
    intro c i hi
    exact B.query_degree c i (by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
  polynomial_mass := by
    intro c i hi
    exact B.query_mass c i (by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)

theorem controls (S : Source) (B : Budget S) (hp : S.packet ∈ FP)
    (hr : B.rootDegree ∈ FP) (hd : B.degree ∈ FP) (hb : B.rootMass ∈ FP) (hm : B.mass ∈ FP) :
    SignPatternBits.ControlsPolyTime (family S B) := by
  have hu := TubeZero.constraintCount_unary
    (TubeIndexed.arity_unary.comp (mem_FP_comp hp pairFst_mem_FP))
  refine ⟨bits_mem_FP hu, ?_, hr, hd, hb, hm⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply] using hu

noncomputable def sampleCount (S : Source) (c : List Bool) : ℕ :=
  sampleRootCount (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c)

def sampleLanguage (S : Source) : Language :=
  {c | ∃ z, CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c : ℝ) z}

theorem family_rootCount (S : Source) (B : Budget S) (c : List Bool) :
    SignPatternBits.rootCount (family S B) c = sampleCount S c := by
  exact congrArg (fun k : ℕ => RootSignQueries.signCount
    (((S.coordinates c).polynomial.map (algebraMap ℤ ℝ)).roots.toFinset)
    (fun i : Fin k => (indexedSignQuery (S.packet c) (S.mask c) (S.projection c)
      (S.level c) (S.coordinates c) i.val).map (algebraMap ℤ ℝ)) (fun _ => .pos))
    (Nat.fromBitsLE_bits _)

def positiveAccess {S : Source} {B : Budget S} (a : SignPatternBits.Access (family S B)) :
    SignPatternBits.Access (family S B) :=
  { a with pattern := fun _ => InfinitesimalSign.encode .pos, pattern_eq := fun _ _ => rfl }

theorem countEvaluator {S : Source} {B : Budget S} (a : SignPatternBits.Access (family S B))
    (hF : SignPatternBits.ControlsPolyTime (family S B))
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (sampleCount S c)) := by
  let E := SignPatternBits.rootCountEvaluator (positiveAccess a) hF (constFn_mem_FP _) H P
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (family_rootCount S B c))

theorem sampleDecider {S : Source} {B : Budget S} (a : SignPatternBits.Access (family S B))
    (hF : SignPatternBits.ControlsPolyTime (family S B))
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceDecider (sampleLanguage S) := by
  have hflag : (fun w : List Bool => [decide (w ≠ [])]) ∈ FP :=
    (LeanCanny.Encoding.Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (countEvaluator a hF H P).decider (fun w => decide (w ≠ [])) hflag
  intro c
  have hz : BinaryNatCode.encode (sampleCount S c) = [] ↔ sampleCount S c = 0 := by
    change BinaryNatCode.encode (sampleCount S c) = BinaryNatCode.encode 0 ↔ _
    exact BinaryNatCode.encode_injective.eq_iff
  simp only [sampleLanguage, Set.mem_ofPred_eq, decide_eq_true_eq]
  exact (sampleRootCount_pos_iff (S.packet c) (S.mask c) (S.projection c) (S.level c)
    (S.finite c) (S.coordinates c)).symm.trans (Nat.pos_iff_ne_zero.trans (not_congr hz).symm)

theorem sampleLanguage_mem_PSPACE {S : Source} {B : Budget S} (a : SignPatternBits.Access (family S B))
    (hF : SignPatternBits.ControlsPolyTime (family S B))
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    sampleLanguage S ∈ PSPACE := (sampleDecider a hF H P).mem_PSPACE

end LeanCanny.ETR.TubeLevelSign
