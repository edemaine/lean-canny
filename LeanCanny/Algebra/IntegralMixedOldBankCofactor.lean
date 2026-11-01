/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedBankCofactor
public import LeanCanny.Algebra.IntegralMixedRoutineContextQuery
public import LeanCanny.Algebra.IntegralMixedVirtualCaps
public import LeanCanny.Algebra.IntegralMixedVirtualNativeObjective
/-! # Native old-bank cofactors requesting actual earlier scalar producers

The saved source is ROOT, scalar-prefix birth, and producer context. The
producer query resets coordinate/context, uses routine6/phase0, and stores
its birth once. Only selector metadata is native; retained integer leading
values remain current recursive replies. This bank product is distinct
from the virtual spatial clearing denominator, which also includes the
immutable affine rule scales.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldBankCofactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Routing where
  coordinate : List Bool → ℕ
  context : List Bool → ℕ
structure RoutingAccess (R : Routing) : Prop where
  coordinate : BinaryFn R.coordinate
  context : BinaryFn R.context

def producerBirth (z : List Bool) := Nat.fromBitsLE (pairFst (pairSnd z))
def retainedIndex (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
theorem producerBirth_binary : BinaryFn producerBirth := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem retainedIndex_binary : BinaryFn retainedIndex := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def writer (P : Parameters) (R : Routing) := IntegralMixedRoutineContextQuery.query P pairFst producerBirth .companion .originalCoefficient R.coordinate R.context

theorem writer_FP (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) : writer P R ∈ FP :=
  IntegralMixedRoutineContextQuery.query_FP P a pairFst pairFst_mem_FP producerBirth producerBirth_binary .companion .originalCoefficient
    R.coordinate R.context hr.coordinate hr.context

noncomputable def count (P : Parameters) (F : Family) (q : List Bool) := F.birth (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def scalars (P : Parameters) (F : Family) (selected : List Bool → ℕ) :=
  IntegralMixedBankCofactor.scalars (IntegralMixedVirtualTaskBits.family P F) (modulus P) (modulus_ne_zero P) selected

theorem count_eq (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) : count P F q = birth P q := g.birth q

theorem count_unary (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) : UnaryFn (count P F) :=
  (RankedHistoryTask.birth_unary _ (birthCap_unary P a)).of_eq (fun q => (g.birth q).symm)

theorem controls (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (selected : List Bool → ℕ) (hs : BinaryFn selected) : CommonHeightRecursivePass.Controls (scalars P F selected) :=
  ⟨count_unary P a F g, modulus_binary P a, hs⟩

noncomputable def packet (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) :=
  pair q (pair (BinaryNatCode.encode (count P F q - 1 - i)) (BinaryNatCode.encode i))

noncomputable def program (P : Parameters) (F : Family) (selected : List Bool → ℕ) (R : Routing) :=
  CommonHeightRecursivePass.program (scalars P F selected) (writer P R)

theorem certificates (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (selected : List Bool → ℕ) (hs : BinaryFn selected) (R : Routing) (hr : RoutingAccess R) :
    (program P F selected R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  CommonHeightRecursivePass.certificates _ (controls P a F g selected hs) _ (writer_FP P a R hr)

theorem writer_root (P : Parameters) (R : Routing) (z : List Bool) :
    RankedHistoryTask.root (writer P R z) = RankedHistoryTask.root (pairFst z) :=
  IntegralMixedRoutineContextQuery.query_root P pairFst producerBirth .companion .originalCoefficient R.coordinate R.context z

theorem writer_phase (P : Parameters) (R : Routing) (z : List Bool) : phase (writer P R z) = 0 :=
  IntegralMixedRoutineContextQuery.query_phase P pairFst producerBirth .companion .originalCoefficient R.coordinate R.context z

theorem writer_routine (P : Parameters) (R : Routing) (z : List Bool) : IntegralMixedRoutineTaskBits.routine P (writer P R z) = 6 :=
  IntegralMixedRoutineContextQuery.query_routine P pairFst producerBirth .companion .originalCoefficient R.coordinate R.context z

theorem writer_modulus (P : Parameters) (R : Routing) (z : List Bool) : modulus P (writer P R z) = modulus P (pairFst z) :=
  IntegralMixedRoutineContextQuery.query_modulus P pairFst producerBirth .companion .originalCoefficient R.coordinate R.context z

theorem writer_packet_birth (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < count P F q) :
    birth P (writer P R (packet P F q i)) = count P F q - 1 - i := by
  rw [writer, IntegralMixedRoutineContextQuery.query_birth]
  · simp only [producerBirth, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · simp only [producerBirth, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [count_eq P F g q] at hi ⊢
    exact (by omega : birth P q - 1 - i ≤ birth P q).trans (min_le_right _ _)

theorem writer_packet_frame (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < count P F q) :
    IntegralMixedRoutineTaskBits.Frame P q (writer P R (packet P F q i)) := by
  have HB : producerBirth (packet P F q i) < birth P (pairFst (packet P F q i)) := by
    simp only [producerBirth, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [← count_eq P F g q]
    omega
  simpa only [writer, packet, pairFst_pair] using IntegralMixedRoutineContextQuery.query_frame_birth P pairFst producerBirth
    .companion .originalCoefficient R.coordinate R.context (packet P F q i) HB

abbrev RepliesAt (P : Parameters) (F : Family) (R : Routing) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i : Fin (count P F q), reply (writer P R (packet P F q i.val)) =
    residueBits ((F.state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator i : ZMod (modulus P q))

noncomputable def value (P : Parameters) (F : Family) (selected : List Bool → ℕ) (q : List Bool) :=
  residueBits ((scalars P F selected).cofactor q : ZMod (modulus P q))

theorem value_at (P : Parameters) (F : Family) (selected : List Bool → ℕ) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F R reply q) :
    (program P F selected R).value reply q = value P F selected q :=
  IntegralMixedBankCofactor.program_value (IntegralMixedVirtualTaskBits.family P F) (modulus P) (modulus_ne_zero P) selected
    (writer P R) reply q he

theorem replies_scale (P : Parameters) (F : Family) (selected : List Bool → ℕ) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F R reply q) :
    ∀ i < (scalars P F selected).count q,
      reply (writer P R (pair q (pair (BinaryNatCode.encode ((scalars P F selected).count q - 1 - i)) (BinaryNatCode.encode i)))) =
        residueBits ((scalars P F selected).scale q i : ZMod ((scalars P F selected).modulus q)) := by
  intro i hi
  change _ = residueBits (IntegralMixedBankCofactor.scale (IntegralMixedVirtualTaskBits.family P F) q i : ZMod (modulus P q))
  have HI : i < (IntegralMixedVirtualTaskBits.family P F).birth q := hi
  rw [IntegralMixedBankCofactor.scale, dite_eq_left HI]
  exact he ⟨i, hi⟩

noncomputable def stateBound (P : Parameters) (F : Family) (q : List Bool) :=
  2 * q.length + 2 * (count P F q).size + (modulus P q).size + 2

theorem stateBound_unary (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) : UnaryFn (stateBound P F) := by
  have HC : UnaryFn (fun q => (count P F q).size) := (UnaryFn.length (BinaryFn.ofUnary (count_unary P a F g)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun q => (modulus P q).size) := (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HC)).add HM).add (UnaryFn.const 2)

theorem state_length_at (P : Parameters) (F : Family) (selected : List Bool → ℕ) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F R reply q) (t : ℕ) :
    (RecursiveFold.encState (((program P F selected R).controller.reference reply)^[t] ((program P F selected R).initial q))).length ≤ stateBound P F q := by
  have H := CommonHeightRecursivePass.orbit_length (scalars P F selected) (writer P R) reply q
    (replies_scale P F selected R reply q he) t
  change (RecursiveFold.encState (((program P F selected R).controller.reference reply)^[t]
    ((program P F selected R).initial q))).length ≤
      2 * q.length + 2 * (Turing.MultiTapeTM.encNat (count P F q)).length + (BinaryNatCode.encode (modulus P q)).length + 2 at H
  simpa only [stateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (selected : List Bool → ℕ) (hs : BinaryFn selected) (R : Routing) (hr : RoutingAccess R) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (program P F selected R).controller
  certificates := certificates P a F g selected hs R hr
  selected q := decide (IntegralMixedVirtualCaps.valid P q)
  selected_FP := (IntegralMixedVirtualCaps.valid_FP P a).flag_mem_FP
  model := value P F selected
  clock := count P F
  clock_binary := BinaryFn.ofUnary (count_unary P a F g)
  stateBound := stateBound P F
  stateBound_unary := stateBound_unary P a F g

theorem requests_frame (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (selected : List Bool → ℕ) (R : Routing) (reply : List Bool → List Bool)
    (q c : List Bool) (budget : List Bool → ℕ)
    (hc : (program P F selected R).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  have HC := IntegralMixedVirtualNativeLowerBits.fold_requests_bound (program P F selected R) reply budget q c hc
  obtain ⟨i, hi, rfl⟩ := (CommonHeightRecursivePass.requests_iff (scalars P F selected) (writer P R) reply q c).mp HC
  exact writer_packet_frame P F g R q i hi

theorem correct (P : Parameters) (a : Access P) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (selected : List Bool → ℕ) (hs : BinaryFn selected) (R : Routing) (hr : RoutingAccess R)
    (reply : List Bool → List Bool) (he : ∀ q, IntegralMixedVirtualCaps.valid P q → RepliesAt P F R reply q) :
    Correct (machine P a F g selected hs R hr) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (program P F selected R).halted_after reply q
  · intro q t hq hh
    simp only [machine] at hh ⊢
    exact ((program P F selected R).output_when_halted reply q t hh).trans (value_at P F selected R reply q (he q (of_decide_eq_true hq)))
  · intro q t hq
    exact state_length_at P F selected R reply q (he q (of_decide_eq_true hq)) t
  · intro q c budget _ hc
    exact requests_frame P F g selected R reply q c budget hc

theorem value_full (P : Parameters) (F : Family) (q : List Bool) : value P F (count P F) q =
    residueBits (IntegralMixedHistory.commonDenominator (F.state (IntegralMixedVirtualTaskBits.saved P q)) : ZMod (modulus P q)) := by
  have H := IntegralMixedBankCofactor.cofactor_outside (IntegralMixedVirtualTaskBits.family P F)
    (modulus P) (modulus_ne_zero P) (count P F) q (Nat.le_refl _)
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H
end LeanCanny.Algebra.IntegralMixedOldBankCofactorBits
