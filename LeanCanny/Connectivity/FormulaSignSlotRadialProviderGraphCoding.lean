/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphReachability
/-! # Fixed-width graph paths faithfully represent the raw native vertices

Padding introduces no additional point relation. Every native vertex has a
literal label, and decoding every guarded graph step yields native adjacency.
The equivalence here concerns the actual native graph, before geometry.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def label (c q : List Bool):=IntegralMixedRoadmapWordLabel.encode
  (FormulaSignSlotRadialProviderAtomic.providerVertexBudget c) q

theorem label_decode (c q : List Bool) : IntegralMixedRoadmapWordLabel.decode (label c q)=q:=
  IntegralMixedRoadmapWordLabel.decode_encode _ _

theorem label_valid (c q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q=c) :Valid c (label c q) :=by
  simpa only [Valid,label_decode] using And.intro hc hq

theorem label_length (c q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q=c) : (label c q).length=width c :=by
  have HB : q.length≤FormulaSignSlotRadialProviderAtomic.providerVertexBudget c:=by
    simpa only [hc] using FormulaSignSlotRadialProviderAtomic.vertex_length_provider q hq
  exact IntegralMixedRoadmapWordLabel.encode_length _ q HB

theorem decode_step (c u v : List Bool)
    (h : ImplicitGraph.Step (ImplicitGraph.guard (edges c) (vertices c))
      (width c) u v) :
    FormulaSignSlotRadialProviderEdge.Adjacent (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v) :=by
  have H : vertices c u=true∧vertices c v=true∧edges c u v=true:=by
    simpa only [ImplicitGraph.guard,Bool.and_eq_true,and_assoc] using h.2.2
  exact of_decide_eq_true H.2.2

theorem labels_step (c u v : List Bool) (hu : u.length=width c) (hv : v.length=width c)
    (hU : Valid c u) (hV : Valid c v)
    (hE : FormulaSignSlotRadialProviderEdge.Adjacent (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v)) :
    ImplicitGraph.Step (ImplicitGraph.guard (edges c) (vertices c))
      (width c) u v :=by
  refine ⟨hu,hv,?_⟩
  simp only [ImplicitGraph.guard,vertices,edges,hU,hV,hE,decide_true,Bool.true_and]

theorem decode_path (c u v : List Bool)
    (h : Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard (edges c) (vertices c))
      (width c)) u v) :
    Relation.ReflTransGen (FormulaSignSlotRadialProviderEdge.Adjacent)
      (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v) :=
  Relation.ReflTransGen.lift IntegralMixedRoadmapWordLabel.decode (fun a b H=>decode_step c a b H) _ _ h

theorem path_provider_eq (a b : List Bool)
    (h : Relation.ReflTransGen (FormulaSignSlotRadialProviderEdge.Adjacent) a b) :
    FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b :=
  Relation.reflTransGen_le_of_equivalence_of_le (Setoid.ker FormulaSignSlotRadialProviderAtomic.provider).iseqv
    (fun _ _ => FormulaSignSlotRadialProviderEdge.provider_eq _ _) _ _ h

theorem encode_path (c a b : List Bool)
    (hc : FormulaSignSlotRadialProviderAtomic.provider a=c)
    (h : Relation.ReflTransGen (FormulaSignSlotRadialProviderEdge.Adjacent) a b) :
    Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard (edges c) (vertices c))
      (width c)) (label c a) (label c b) :=by
  induction h with
  | refl=>exact .refl
  | @tail b d Hab Hbd IH=>
    obtain ⟨HB,HD⟩:=FormulaSignSlotRadialProviderEdge.valid b d Hbd
    have HC : FormulaSignSlotRadialProviderAtomic.provider b=c:=(path_provider_eq a b Hab).symm.trans hc
    have HCd : FormulaSignSlotRadialProviderAtomic.provider d=c:=(FormulaSignSlotRadialProviderEdge.provider_eq b d Hbd).symm.trans HC
    exact IH.tail (labels_step c _ _ (label_length c b HB HC)
      (label_length c d HD HCd) (label_valid c b HB HC)
      (label_valid c d HD HCd) (by simpa only [label_decode] using Hbd))

noncomputable def NativeConnected (c : List Bool):=∀a b : List Bool,
  FormulaSignSlotRadialProviderAtomic.Valid a→FormulaSignSlotRadialProviderAtomic.Valid b→
  FormulaSignSlotRadialProviderAtomic.provider a=c→FormulaSignSlotRadialProviderAtomic.provider b=c→
    Relation.ReflTransGen (FormulaSignSlotRadialProviderEdge.Adjacent) a b

theorem connected_iff_native (c : List Bool) : c∈connectedLanguage↔NativeConnected c :=by
  constructor
  · intro H a b hA hB hc hd
    have HU:=label_valid c a hA hc
    have HV:=label_valid c b hB hd
    have HP:=H _ (label_length c a hA hc) _ (label_length c b hB hd)
      (by simpa only [vertices,decide_eq_true_eq] using HU)
      (by simpa only [vertices,decide_eq_true_eq] using HV)
    simpa only [label_decode] using decode_path c _ _ HP
  · intro H u hu v hv hU hV
    have HU : Valid c u:=of_decide_eq_true hU
    have HV : Valid c v:=of_decide_eq_true hV
    let a:=IntegralMixedRoadmapWordLabel.decode u
    let b:=IntegralMixedRoadmapWordLabel.decode v
    have HP:=H a b HU.2 HV.2 HU.1 HV.1
    have HE:=encode_path c a b HU.1 HP
    have H1:=labels_step c u (label c a) hu
      (label_length c a HU.2 HU.1) HU (label_valid c a HU.2 HU.1)
      (by rw [label_decode];exact FormulaSignSlotRadialProviderEdge.refl a HU.2)
    have H2:=labels_step c (label c b) v
      (label_length c b HV.2 HV.1) hv (label_valid c b HV.2 HV.1) HV
      (by rw [label_decode];exact FormulaSignSlotRadialProviderEdge.refl b HV.2)
    exact (Relation.ReflTransGen.head H1 HE).tail H2

noncomputable def nativeConnectedLanguage : Language:={c |NativeConnected c}

theorem native_connected_decider : SpaceDecider (nativeConnectedLanguage):=by
  apply (connected_decider).congr
  ext c
  exact connected_iff_native c

theorem native_connected_mem_PSPACE : nativeConnectedLanguage∈PSPACE:=
  (native_connected_decider).mem_PSPACE

noncomputable def RawReachable (c a b : List Bool):=FormulaSignSlotRadialProviderAtomic.Valid a∧
  FormulaSignSlotRadialProviderAtomic.Valid b∧FormulaSignSlotRadialProviderAtomic.provider a=c∧
  FormulaSignSlotRadialProviderAtomic.provider b=c∧Relation.ReflTransGen (FormulaSignSlotRadialProviderEdge.Adjacent) a b

theorem label_reachable_iff (c a b : List Bool) :
    ImplicitGraph.Reachable (edges c) (vertices c) (width c)
      (label c a) (label c b)↔RawReachable c a b :=by
  constructor
  · intro H
    have HU : FormulaSignSlotRadialProviderAtomic.provider a=c∧FormulaSignSlotRadialProviderAtomic.Valid a:=by
      simpa only [Valid,label_decode] using (show Valid c (label c a) from of_decide_eq_true H.1)
    have HV : FormulaSignSlotRadialProviderAtomic.provider b=c∧FormulaSignSlotRadialProviderAtomic.Valid b:=by
      simpa only [Valid,label_decode] using (show Valid c (label c b) from of_decide_eq_true H.2.1)
    exact ⟨HU.2,HV.2,HU.1,HV.1,by simpa only [label_decode] using decode_path c _ _ H.2.2⟩
  · rintro ⟨HA,HB,HC,HD,HP⟩
    exact ⟨by simpa only [vertices,decide_eq_true_eq] using label_valid c a HA HC,
      by simpa only [vertices,decide_eq_true_eq] using label_valid c b HB HD,
      encode_path c a b HC HP⟩

noncomputable def rawPacket (z : List Bool):=pair (pairFst z)
  (pair (label (pairFst z) (leftLabel z)) (label (pairFst z) (rightLabel z)))

theorem rawPacket_FP : rawPacket∈FP:=by
  have HW:=(FormulaSignSlotRadialProviderAtomic.providerVertexBudget_unary).comp
    pairFst_mem_FP
  have HL : leftLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HR : rightLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (IntegralMixedRoadmapWordLabel.encode_FP HW HL) (IntegralMixedRoadmapWordLabel.encode_FP HW HR))

noncomputable def nativeReachLanguage : Language:={z |RawReachable (pairFst z) (leftLabel z) (rightLabel z)}

theorem native_reach_decider : SpaceDecider (nativeReachLanguage):=by
  apply ((reach_decider).precompose _ (rawPacket_FP)).congr
  ext z
  simp only [Set.mem_preimage, reachLanguage, nativeReachLanguage, Set.mem_ofPred_eq,
    rawPacket, leftLabel, rightLabel, pairFst_pair, pairSnd_pair]
  change ((label (pairFst z) (leftLabel z)).length=width (pairFst z)∧
    (label (pairFst z) (rightLabel z)).length=width (pairFst z)∧
    ImplicitGraph.Reachable (edges (pairFst z)) (vertices (pairFst z))
      (width (pairFst z)) (label (pairFst z) (leftLabel z))
        (label (pairFst z) (rightLabel z)))↔RawReachable (pairFst z) (leftLabel z) (rightLabel z)
  rw [label_reachable_iff]
  constructor
  · intro H
    exact H.2.2
  · intro H
    exact ⟨label_length _ _ H.1 H.2.2.1,
      label_length _ _ H.2.1 H.2.2.2.1,H⟩

theorem native_reach_mem_PSPACE : nativeReachLanguage∈PSPACE:=
  (native_reach_decider).mem_PSPACE

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
