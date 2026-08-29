/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every
nonempty compact metric space is a continuous image of the Cantor set.

## Main theorems

* `exists_nat_bool_continuous_surjective_of_compact`: Hausdorff–Alexandroff Theorem.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`cantorSetHomeomorphNatToBool`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `exists_closed_embedding_to_hilbert_cube`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

@[expose] public section

namespace Real

/--
Definition of `fromBinary` / `fromBinary` 的定义

English:
definition fromBinary
  signature: : (Nat -> Bool) -> unitInterval
  body: let φ : (Nat -> Bool) ≃ₜ (Nat -> Fin 2) := Homeomorph.piCongrRight
    (fun _ => finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ => ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)

中文:
定义 fromBinary
  签名: : (自然数 -> 布尔值) -> unit整数erval
  定义体: let φ : (Nat -> Bool) ≃ₜ (Nat -> Fin 2) := Homeomorph.piCongrRight
    (fun _ => finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ => ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)

Depends on / 依赖: Homeomorph, Homeomorph.piCongrRight, Subtype, Subtype.coind, finTwoEquiv, finTwoEquiv.toHomeomorphOfDiscrete.symm, ofDigits, ofDigits_le_one, ofDigits_nonneg, piCongrRight, toHomeomorphOfDiscrete
-/
noncomputable def fromBinary : (Nat -> Bool) -> unitInterval :=
  let φ : (Nat -> Bool) ≃ₜ (Nat -> Fin 2) := Homeomorph.piCongrRight
    (fun _ => finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ => ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)

/--
theorem `fromBinary_continuous` / 定理 `fromBinary_continuous`

English:
theorem fromBinary_continuous
  statement: Continuous fromBinary
  proof: Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _

中文:
定理 fromBinary_continuous
  结论: 连续 fromBinary
  证明: Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _

Depends on / 依赖: Continuous, Continuous.subtype_mk, Homeomorph, Homeomorph.continuous, continuous, continuous_ofDigits, continuous_ofDigits.comp, subtype_mk
-/
theorem fromBinary_continuous : Continuous fromBinary :=
  Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _

/--
theorem `fromBinary_surjective` / 定理 `fromBinary_surjective`

English:
theorem fromBinary_surjective
  statement: fromBinary.Surjective
  proof: by
  refine Subtype.coind_surjective _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
  simp only [Set.surjOn_univ, Homeomorph.surjective _]

中文:
定理 fromBinary_surjective
  结论: fromBinary.满射
  证明: by
  refine Subtype.coind_surjective _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
  simp only [Set.surjOn_univ, Homeomorph.surjective _]

Depends on / 依赖: Homeomorph, Homeomorph.surjective, Set.surjOn_univ, Subtype, Subtype.coind_surjective, coind_surjective, ofDigits_SurjOn, surjOn_univ, surjective
-/
theorem fromBinary_surjective : fromBinary.Surjective := by
  refine Subtype.coind_surjective _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
  simp only [Set.surjOn_univ, Homeomorph.surjective _]

end Real

open Real

/--
Definition of `cantorToHilbert` / `cantorToHilbert` 的定义

English:
definition cantorToHilbert
  signature: (x : Nat -> Bool)
  body: Pi.map (fun _ b => fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)

中文:
定义 cantorToHilbert
  签名: (x : 自然数 -> 布尔值)
  定义体: Pi.map (fun _ b => fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)

Depends on / 依赖: Pi.map, cantorSpaceHomeomorphNatToCantorSpace, fromBinary
-/
noncomputable def cantorToHilbert (x : Nat -> Bool) : Nat -> unitInterval :=
  Pi.map (fun _ b => fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)

/--
theorem `cantorToHilbert_continuous` / 定理 `cantorToHilbert_continuous`

English:
theorem cantorToHilbert_continuous
  statement: Continuous cantorToHilbert
  proof: continuous_pi (fun _ => fromBinary_continuous.comp (by fun_prop))

中文:
定理 cantorToHilbert_continuous
  结论: 连续 cantorToHilbert
  证明: continuous_pi (fun _ => fromBinary_continuous.comp (by fun_prop))

Depends on / 依赖: continuous_pi, fromBinary_continuous, fromBinary_continuous.comp, fun_prop
-/
theorem cantorToHilbert_continuous : Continuous cantorToHilbert :=
  continuous_pi (fun _ => fromBinary_continuous.comp (by fun_prop))

/--
theorem `cantorToHilbert_surjective` / 定理 `cantorToHilbert_surjective`

English:
theorem cantorToHilbert_surjective
  statement: cantorToHilbert.Surjective
  proof: (Function.Surjective.piMap (fun _ => fromBinary_surjective)).comp
    cantorSpaceHomeomorphNatToCantorSpace.surjective

中文:
定理 cantorToHilbert_surjective
  结论: cantorToHilbert.满射
  证明: (Function.Surjective.piMap (fun _ => fromBinary_surjective)).comp
    cantorSpaceHomeomorphNatToCantorSpace.surjective

Depends on / 依赖: Function, Function.Surjective.piMap, Surjective, cantorSpaceHomeomorphNatToCantorSpace, cantorSpaceHomeomorphNatToCantorSpace.surjective, fromBinary_surjective, surjective
-/
theorem cantorToHilbert_surjective : cantorToHilbert.Surjective :=
  (Function.Surjective.piMap (fun _ => fromBinary_surjective)).comp
    cantorSpaceHomeomorphNatToCantorSpace.surjective

attribute [local instance] PiNat.metricSpace in
/--
theorem `exists_retractionCantorSet` / 定理 `exists_retractionCantorSet`

English:
theorem exists_retractionCantorSet
  statement: {X : Set (Nat -> Bool)} (h_closed : IsClosed X)
  proof: by
  obtain ⟨f, fs, frange, hf⟩ := PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty
  exact ⟨f, hf.continuous, frange⟩

中文:
定理 存在_retractionCantorSet
  结论: {X : 集合 (自然数 -> 布尔值)} (h_closed : 是闭集 X)
  证明: by
  obtain ⟨f, fs, frange, hf⟩ := PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty
  exact ⟨f, hf.continuous, frange⟩

Depends on / 依赖: PiNat.exists_lipschitz_retraction_of_isClosed, continuous, exists_lipschitz_retraction_of_isClosed, frange, h_closed, h_nonempty, hf.continuous
-/
theorem exists_retractionCantorSet {X : Set (Nat -> Bool)} (h_closed : IsClosed X)
    (h_nonempty : X.Nonempty) : exists f : (Nat -> Bool) -> (Nat -> Bool), Continuous f ∧ Set.range f = X := by
  obtain ⟨f, fs, frange, hf⟩ := PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty
  exact ⟨f, hf.continuous, frange⟩

/--
theorem `exists_nat_bool_continuous_surjective_of_compact` / 定理 `exists_nat_bool_continuous_surjective_of_compact`

English:
theorem exists_nat_bool_continuous_surjective_of_compact
  statement: (X : Type*) [Nonempty X] [MetricSpace X]
  proof: by
  -- `X` is homeomorphic to a closed subset `KH` of the Hilbert cube.
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨emb, h_emb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let KH : Set (Nat -> unitInterva

中文:
定理 存在_nat_bool_continuous_surjective_of_compact
  结论: (X : 类型) [非空 X] [度量空间 X]
  证明: by
  -- `X` is homeomorphic to a closed subset `KH` of the Hilbert cube.
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨emb, h_emb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let KH : Set (Nat -> unitInterva
-/
theorem exists_nat_bool_continuous_surjective_of_compact (X : Type*) [Nonempty X] [MetricSpace X]
    [CompactSpace X] : exists f : (Nat -> Bool) -> X, Continuous f ∧ Function.Surjective f := by
  -- `X` is homeomorphic to a closed subset `KH` of the Hilbert cube.
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨emb, h_emb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let KH : Set (Nat -> unitInterval) := Set.range emb
  let g : X ≃ₜ KH := h_emb.toHomeomorph
  -- `KC` is the closed preimage of `KH` under the continuous surjection `cantorToHilbert`.
  let KC : Set (Nat -> Bool) := cantorToHilbert ⁻¹' KH
  have hKC_closed : IsClosed KC :=
    IsClosed.preimage cantorToHilbert_continuous (Topology.IsClosedEmbedding.isClosed_range
 Continuous.isClosedEmbedding (Topology.IsEmbedding.continuous h_emb) h_emb.injective)
  -- Take a retraction `f'` from the Cantor space to `KC`.
  obtain ⟨f, hf_continuous, hf_surjective⟩ := exists_retractionCantorSet hKC_closed
 Set.Nonempty.preimage (Set.range_nonempty emb) cantorToHilbert_surjective
  let f' : (Nat -> Bool) -> KC := Subtype.coind f (by simp [← hf_surjective])
  have hf'_surjective : Function.Surjective f' := Subtype.coind_surjective _ (by grind [Set.SurjOn])
  -- Let `h` be the restriction of `cantorToHilbert` to `KC → KH`.
  let h : KC -> KH := KH.restrictPreimage cantorToHilbert
  have hh_continuous : Continuous h := Continuous.restrictPreimage cantorToHilbert_continuous
  have hh_surjective : Function.Surjective h :=
    Set.restrictPreimage_surjective _ cantorToHilbert_surjective
  -- Take the composition `g.symm ∘ h ∘ f'` as the desired continuous surjection from the Cantor
  -- space to `X`.
exact ⟨g.symm ∘ h ∘ f', by fun_prop, g.symm.surjective.comp hh_surjective.comp hf'_surjective⟩
