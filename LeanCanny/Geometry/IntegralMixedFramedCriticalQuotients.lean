/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
/-! # Creating-bank quotient values persist in the same full raw tuple -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (enumerate)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem point_append {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (newer older :List (Instruction n B))
    (hc :(newer++older).length≤S+1) (ho :older.length≤S+1) (z :ℕ→ℝ) (i :Fin older.length) :
    (ofCommands x (newer++older) hc).point z (newer.length+i.val)=
      (ofCommands x older ho).point z i.val :=by
  induction newer with
  | nil=>simp only [List.nil_append,List.length_nil,Nat.zero_add]
  | cons c cs ih=>
    have HT :(cs++older).length≤S+1:=by simp only [List.length_append,List.length_cons] at hc ⊢;omega
    have HI :cs.length+i.val<(cs++older).length:=by simp only [List.length_append];omega
    have HE:=IntegralFramedPhysicalPrefixPoint.point_cons x c (cs++older) hc HT z ⟨cs.length+i.val,HI⟩
    exact (show (ofCommands x ((c::cs)++older) hc).point z ((c::cs).length+i.val)=
      (ofCommands x (cs++older) HT).point z (cs.length+i.val) from by
        simpa only [List.cons_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using HE).trans (ih HT)

theorem quotient_of_generators {n S B :ℕ} {P Q :SpatialSource n}
    (initial :State P S B 0 (Fin 0))
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1) (z :ℕ→ℝ)
    (φ :(reframe (run initial older ho) Q hQ).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((reframe (run initial older ho) Q hQ).sampler.scalarPrefix.basis.generator i)=
      z (enumerate older ((reframe (run initial older ho) Q hQ).sampler.scalar i)).val^
        UniformIntegralPowerSchedule.weights S (2^B) older.length i) (i :Fin older.length) :
    φ ((reframe (run initial older ho) Q hQ).bank.numerator i)/
        ((reframe (run initial older ho) Q hQ).bank.denominator i:ℝ)=
      (ofCommands initial older ho).point z i.val :=by
  have HC :Canonical initial:=by intro j;exact Fin.elim0 j
  have Hcan:=reframe_canonical (run initial older ho) (run_canonical initial HC older ho) Q hQ
  have HE:=IntegralMixedCanonicalBankPoint.quotient_eq (reframe (run initial older ho) Q hQ) Hcan
    (fun i=>z (enumerate older ((reframe (run initial older ho) Q hQ).sampler.scalar i)).val) φ hφ i
  exact HE.trans (IntegralMixedFramedRunObservation.point_actual initial older ho z i).symm

end LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
