/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralDenominatorPassCorrect
public import LeanCanny.Algebra.ModularHistoryPassSpace
public import LeanCanny.Algebra.ModularScalarSpace
/-! # Forward denominators with charged original leading readers

The selected-scale product and all metadata are native. Original integer
leading coefficients may require polynomial space. The forward table
retains canonical residues only and uses no modular inverse.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralDenominatorPassSpace
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralDenominatorPass
set_option backward.isDefEq.respectTransparency false

structure Native (F : Family) : Prop where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  arity : UnaryFn (fun p => F.arity (pairFst p) (cursor p))
  degree : BinaryFn (fun p => F.degree (pairFst p) (cursor p))
  exponent : BinaryFn (fun p => F.exponent (pairFst p) (cursor p))
  index : BinaryFn (fun z => F.index (pairFst (pairFst z)) (cursor (pairFst z)) (Nat.fromBitsLE (pairSnd z)))

structure Access (F : Family) extends Native F where
  leading : SpaceFunction (fun p => residueBits (F.leading (pairFst p) (cursor p) : ZMod (F.modulus (pairFst p))))

-- Only scale-product arithmetic uses this record. Its leading field is
-- unused by factor/rawProduct, and no FP claim is made for F.leading.
def productFamily (F : Family) : Family := { F with leading := fun _ _ => 0 }

theorem productAccess (F : Family) (a : Native F) : IntegralDenominatorPass.Access (productFamily F) where
  count := a.count
  modulus := a.modulus
  arity := a.arity
  leading := mem_FP_of_eq (constFn_mem_FP []) (fun p => by
    change [] = residueBits ((0 : ℤ) : ZMod (F.modulus (pairFst p)))
    simp [residueBits, BinaryNatCode.encode])
  degree := a.degree
  exponent := a.exponent
  index := a.index

theorem rawProduct_FP (F : Family) (a : Native F) : (fun p => residueBits (IntegralDenominatorPass.rawProduct F p)) ∈ FP :=
  mem_FP_of_eq (IntegralDenominatorPass.rawProduct_FP (productFamily F) (productAccess F a)) (fun _ => rfl)

theorem rawNext_evaluator (F : Family) (a : Access F) : SpaceFunction (fun p => residueBits (rawNext F p)) := by
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  have H0 := fun p => F.modulus_ne_zero (pairFst p)
  have HQ := ModularScalarFP.pow HM H0 _ a.degree (rawProduct F) (rawProduct_FP F a.toNative)
  have HA := ModularScalarSpace.mul HM _ _ a.leading (SpaceFunction.ofFP _ HQ)
  have HD := ModularScalarFP.natCast HM _ a.degree
  have HB := ModularScalarSpace.mul HM _ _ HA (SpaceFunction.ofFP _ HD)
  exact ModularScalarSpace.pow HM H0 _ a.exponent _ HB

noncomputable def access (F : Family) (a : Access F) : ModularHistoryPassSpace.Access (pass F) where
  count := a.count
  modulus := a.modulus
  step p := residueBits (rawNext F p)
  step_space := rawNext_evaluator F a
  step_eq := by
    intro c i v hv
    change residueBits (rawNext F (BoundedFold.packet c i (WordList.encode (v.map residueBits)))) = residueBits (next F c i v)
    simp only [rawNext, cursor, BoundedFold.counter_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedFold.accumulator_packet]
    exact (congrArg (fun u => residueBits (stepValue F u i (WordList.encode (v.map residueBits))))
      (BoundedFold.context_packet c i _)).trans (congrArg residueBits (stepValue_encoded F c i v hv))

theorem table_evaluator (F : Family) (a : Access F) : SpaceFunction (ModularHistoryPassSpace.run (pass F) (access F a)) :=
  ModularHistoryPassSpace.run_evaluator (pass F) (access F a)

theorem reader_evaluator (F : Family) (a : Access F) (j : List Bool → ℕ) (hj : BinaryFn j) :
    SpaceFunction (ModularHistoryPassSpace.read (pass F) (access F a) j) :=
  ModularHistoryPassSpace.read_evaluator (pass F) (access F a) j hj

theorem reader_eq (F : Family) (a : Access F) (j : List Bool → ℕ) (c : List Bool) :
    ModularHistoryPassSpace.read (pass F) (access F a) j c =
      residueBits (((integers F c (F.count c))[j c]?).getD 0 : ZMod (F.modulus c)) := by
  rw [ModularHistoryPassSpace.read_eq, values_cast, List.map_map, List.getElem?_map]
  change (Option.map (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) ((integers F c (F.count c))[j c]?)).getD [] = _
  cases (integers F c (F.count c))[j c]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _
  | some z => rfl

theorem integer_reader_evaluator (F : Family) (a : Access F) (j : List Bool → ℕ) (hj : BinaryFn j) :
    SpaceFunction (fun c => residueBits (((integers F c (F.count c))[j c]?).getD 0 : ZMod (F.modulus c))) :=
  (reader_evaluator F a j hj).congr (funext (reader_eq F a j))
end LeanCanny.Algebra.IntegralDenominatorPassSpace
