/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
public import LeanCanny.Computation.SpaceFunction

/-! # Native Savitch evaluation with polynomial-space adjacency and preprocessing

The edge routine may take arbitrary time. Its workspace is charged together
with the midpoint stack, the parameter and the encoded endpoints. Preparing
the call may also take arbitrary time. This extends the upstream
polynomial-time edge and input interface to polynomial-space routines.
-/

@[expose] public section

namespace LeanCanny.Computation
open Turing.MultiTapeTM Cslib.Reachability Cslib.BitString

theorem savitch_computable_polySpace {π γ : Type} {encP : π ↪ List Bool}
    {encIn : γ ↪ List Bool} {edge : π → List Bool → List Bool → Bool}
    (hedge : ComputableTidilyInPolySpace
      (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool}
    (hin : ComputableTidilyInPolySpace (fun x => (par x, width x, depth x, src x, dst x))
      encIn (encArgs encP))
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ComputableTidilyInPolySpace
      (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x)) encIn encBool := by
  obtain ⟨te, se, hse, he⟩ := hedge
  have hlength := hin.polyBounded_length
  obtain ⟨ti, si, hsi, hi⟩ := hin
  have H := computableTidilyInO_savitch he hi hsrc hdst
  obtain ⟨cs, ds, hcs⟩ := hse.exists_le
  let L := fun x => (encArgs encP (par x, width x, depth x, src x, dst x)).length
  have hlen : PolyBounded (fun x => (encIn x).length) L := hlength
  have hL (x : γ) : depth x ≤ L x ∧ width x ≤ L x ∧ (encP (par x)).length ≤ L x := by
    simp only [L, encArgs, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hE (x : γ) : edgeMax se (par x) (width x) ≤ cs * (5 * L x + 3) ^ ds :=
    listMax_le fun u hu => listMax_le fun v hv => by
      refine (hcs _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
      have := hL x
      simp only [length_encPair, encBits_apply, mem_enumList.mp hu, mem_enumList.mp hv]
      omega
  have hpoly : Cslib.PolynomiallyBounded
      (fun n => (n + 1) * (2 * n + 1) + n + cs * (5 * n + 3) ^ ds + 1) := by
    fun_prop
  have hg : PolyBounded (fun x => (encIn x).length)
      (fun x => (L x + 1) * (2 * L x + 1) + L x + cs * (5 * L x + 3) ^ ds + 1) :=
    PolyBounded.comp (size' := id) (g := L) (PolyBounded.of_polynomiallyBounded id hpoly) hlen
  refine ⟨_, _, (hsi.add hg).mono (fun x => ?_), H⟩
  obtain ⟨hd, hw, hp⟩ := hL x
  have hs := Nat.mul_le_mul (show depth x + 1 ≤ L x + 1 by omega)
    (show depth x + width x + 1 ≤ 2 * L x + 1 by omega)
  have := hE x
  omega

end LeanCanny.Computation
