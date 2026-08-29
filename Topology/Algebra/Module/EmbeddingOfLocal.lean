/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A linear map which is locally an embedding is an embedding

Fix `𝕜` a `NontriviallyNormedField`, `E`, `F` two topological vector spaces over `𝕜`, and
`f : E → F` a `𝕜`-linear map. We show that, if there is a neighborhood `V` of `0 : E`
such that the restriction `V → F` is an embedding, then `f` itself is an embedding.

Note that this result is false for topological groups, as shown by the following counterexamples:
* first, in the group setting, there are local embeddings (even local homeomorphisms) which
  are not globally injective; an example is the quotient map `ℝ → 𝕋 := ℝ ⧸ ℤ`;
* even if assume that `f` is globally injective, the theorem still fails. Consider for example
  `f : ℝ → 𝕋 × 𝕋` given by `x ↦ ([x], [α * x])`, with `α` irrational. `f` is injective, and locally
  an embedding by the inverse function theorem, yet it is not globally an embedding: any
  neighborhood of `f(0) = (0, 0)` contains infinitely many points `f(n)`, `n ∈ ℤ`, since
  `α * n` gets arbitrarily close to being an integer infinitely many times.

## Main results

* `ContinuousSMul.topology_eq_of_induced_eq`: let `t₁`, `t₂` be two vector space
  topologies on `E`, and assume that there is a `t₁`-neighborhood of 0 `V` in restriction to
  which the two topologies coincide. Then `t₁ = t₂`.
* `LinearMap.isInducing_of_restrict_nhds_zero`: consider a linear map `f : E → F`, and assume
  there is a neighborhood of 0 `V` in `E` such that `V.domRestrict f : V → F` satisfies
  `Topology.IsInducing`. Then `f` satisfies `Topology.IsInducing`.
* `LinearMap.isEmbedding_of_restrict_nhds_zero`: consider a linear map `f : E → F`, and assume
  there is a neighborhood of 0 `V` in `E` such that `V.domRestrict f : V → F` is a topological
  embedding. Then `f` is a topological embedding.

## TODO

We will also need the fact that if the restriction `V → F` is a *closed* embedding, then
`f : E → F` is a *closed* embedding. This will follow from the fact that a subgroup which is
locally closed at `0` is in fact closed, which we don't have yet

## Implementation details

The content of this file is essentially (variations of)
[N. Bourbaki, *Théories Spectrales*, Chapitre III, § 5, n° 1, lemme 1][bourbaki2023], except
Bourbaki's proof is very specific to `𝕜 = ℝ` or `𝕜 = ℂ`, since it relies crucially on balanced
sets being connected.

Nevertheless, we are able to adapt their proof to arbitrary nontrivially normed fields.
The key argument, replacing the fact that a connected set cannot be covered nontrivially by
disjoint open sets, is that a balanced set `W` cannot intersect nontrivially both `c • V`
and `Vᶜ`, when `V` is a neighborhood of `0` and `0 < ‖c‖ < 1`. We refer to the (highly commented!)
proof for more details.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 5, n° 1, lemme 1][bourbaki2023]

-/

@[expose] public section

open Topology Filter Bornology Set
open scoped Pointwise Set.Notation

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ ->+* 𝕜₂} {f : E ->ₛₗ[σ] F}

variable (𝕜₁) in
/--
lemma `ContinuousSMul.topology_eq_of_nhds_inf_principal_eq` / 引理 `ContinuousSMul.topology_eq_of_nhds_inf_principal_eq`

English:
lemma ContinuousSMul.topology_eq_of_nhds_inf_principal_eq
  statement: (t₁ t₂ : TopologicalSpace E)
  proof: by
  classical
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Note that, because `V ∈ 𝓕₁`, `H` may be rewritten as `𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  replace H : 𝓕₁ = 𝓕₂ ⊓ 𝓟 V := by simpa [← H]
  -- Because both `t

中文:
引理 连续标量乘法.topology_eq_of_nhds_inf_principal_eq
  结论: (t₁ t₂ : 拓扑空间 E)
  证明: by
  classical
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Note that, because `V ∈ 𝓕₁`, `H` may be rewritten as `𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  replace H : 𝓕₁ = 𝓕₂ ⊓ 𝓟 V := by simpa [← H]
  -- Because both `t

Depends on / 依赖: classical
-/
lemma ContinuousSMul.topology_eq_of_nhds_inf_principal_eq (t₁ t₂ : TopologicalSpace E)
    [@IsTopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _]
    [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V in @nhds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) :
    t₁ = t₂ := by
  classical
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Note that, because `V ∈ 𝓕₁`, `H` may be rewritten as `𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  replace H : 𝓕₁ = 𝓕₂ ⊓ 𝓟 V := by simpa [← H]
  -- Because both `t₁` and `t₂` are additive group topologies, it is enough to show `𝓕₁ = 𝓕₂`.
  suffices 𝓕₁ = 𝓕₂ by rwa [IsTopologicalAddGroup.ext_iff] <;> infer_instance
  -- If we can show that `V ∈ 𝓕₂` we are done, because then `𝓕₁ = 𝓕₂ ⊓ 𝓟 V = 𝓕₂`.
  suffices V in 𝓕₂ by simpa [H]
  -- Hence, let us show that `V ∈ 𝓕₂`. Fix a scalar `c` with `0 < ‖c‖ < 1`.
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c != 0 := norm_pos_iff.mp hc₀
  -- We know that `c • V ∈ 𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  have cV_mem : c • V in 𝓕₂ ⊓ 𝓟 V := by
    simpa [← H, 𝓕₁, set_smul_mem_nhds_zero_iff c_ne]
  -- Furthermore, we know that `𝓕₂` has a basis of balanced sets
  have basis_𝓕₂ : HasBasis 𝓕₂ (fun (s : Set E) => s in 𝓕₂ ∧ Balanced 𝕜₁ s) id :=
    let := t₂; nhds_basis_balanced 𝕜₁ E
  -- Hence, we get a balanced set `W ∈ 𝓕₂` such that `W ∩ V ⊆ c • V`.
.mem_iff.mp cV_mem obtain ⟨W, ⟨W_mem_𝓕₂, W_bal⟩, hW⟩ := basis_𝓕₂.inf_principal V
  -- We claim that `W ⊆ V`. This will conclude the proof, since `W ∈ 𝓕₂`.
  suffices W subseteq V from mem_of_superset W_mem_𝓕₂ this
  -- Let `w ∈ W` be arbitrary.
  intro w w_in_W
  -- Because `V` is a `t₁`-neighborhood of `0`, we have `c ^ n • w ∈ V` for some natural number `n`.
  obtain ⟨n, hn⟩ : exists n : Nat, c ^ n • w in V :=
    let := t₁
.zero_smul_const w tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁
.exists .eventually_mem V_mem
  -- We will conclude by reducing `c ^ n • w ∈ V` to `w = c ^ 0 • w ∈ V` inductively.
  suffices c ^ 0 • w in V by simpa
  apply Nat.decreasingInduction (motive := fun (k : Nat) _ => c^k • w in V) ?_ hn n.zero_le
  -- To do so, we show that if `k : ℕ` is such that `c ^ (k + 1) • w ∈ V` then `c ^ k • w ∈ V`.
  intro k _ (hk : c ^ (k + 1) • w in V)
  -- Indeed, because `W` is balanced, we have `c ^ (k + 1) • w ∈ W ∩ V ⊆ c • V`
  have : c ^ (k + 1) • w in c • V :=
    hW ⟨W_bal.smul_mem (by grw [norm_pow, hc₁.le, one_pow]) w_in_W, hk⟩
  -- Cancelling `c`, we get `c ^ k • w ∈ V` as we claimed.
  rwa [pow_add, pow_one, mul_comm, mul_smul, smul_mem_smul_set_iff₀ c_ne V] at this

variable (𝕜₁) in
/--
lemma `ContinuousSMul.topology_eq_of_induced_eq` / 引理 `ContinuousSMul.topology_eq_of_induced_eq`

English:
lemma ContinuousSMul.topology_eq_of_induced_eq
  statement: (t₁ t₂ : TopologicalSpace E)
  proof: by
  apply topology_eq_of_nhds_inf_principal_eq 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  rw [H]

中文:
引理 连续标量乘法.topology_eq_of_induced_eq
  结论: (t₁ t₂ : 拓扑空间 E)
  证明: by
  apply topology_eq_of_nhds_inf_principal_eq 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  rw [H]

Depends on / 依赖: V_mem, map_comap_setCoe_val, mem_of_mem_nhds, nhds_induced, simp_rw, topology_eq_of_nhds_inf_principal_eq
-/
lemma ContinuousSMul.topology_eq_of_induced_eq (t₁ t₂ : TopologicalSpace E)
    [@IsTopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _]
    [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V in @nhds E t₁ 0)
    (H : t₁.induced ((↑) : V -> E) = t₂.induced ((↑) : V -> E)) :
    t₁ = t₂ := by
  apply topology_eq_of_nhds_inf_principal_eq 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  rw [H]

variable [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] [RingHomIsometric σ]

/--
lemma `LinearMap.isInducing_of_restrict_nhds_zero` / 引理 `LinearMap.isInducing_of_restrict_nhds_zero`

English:
lemma LinearMap.isInducing_of_restrict_nhds_zero
  statement: {V : Set E}
  proof: by
  rw [isInducing_iff]
  -- Call `t₁` the original topology on `E`, and `t₂` the topology induced by `f`. Because
  -- `f` is linear, `t₂` is also a vector space topology.
  have := topologicalAddGroup_induced f
  have := continuousSMul_inducedₛₗ f σ.isometry.continuous
  -- Because `Set.domRestri

中文:
引理 线性映射.isInducing_of_restrict_nhds_zero
  结论: {V : 集合 E}
  证明: by
  rw [isInducing_iff]
  -- Call `t₁` the original topology on `E`, and `t₂` the topology induced by `f`. Because
  -- `f` is linear, `t₂` is also a vector space topology.
  have := topologicalAddGroup_induced f
  have := continuousSMul_inducedₛₗ f σ.isometry.continuous
  -- Because `Set.domRestri

Depends on / 依赖: isInducing_iff
-/
lemma LinearMap.isInducing_of_restrict_nhds_zero {V : Set E}
    (V_mem : V in 𝓝 0) (H : IsInducing (Set.domRestrict V f)) : IsInducing f := by
  rw [isInducing_iff]
  -- Call `t₁` the original topology on `E`, and `t₂` the topology induced by `f`. Because
  -- `f` is linear, `t₂` is also a vector space topology.
  have := topologicalAddGroup_induced f
  have := continuousSMul_inducedₛₗ f σ.isometry.continuous
  -- Because `Set.domRestrict V f` is an inducing, `t₁` and `t₂` induce the same topology
  -- on `V`, so we get `t₁ = t₂` from the lemmas above.
  apply ContinuousSMul.topology_eq_of_induced_eq 𝕜₁ _ (.induced f _) V_mem
  rw [induced_compose]; rw [← domRestrict_eq]; rw [← H.eq_induced]; rw [← IsInducing.subtypeVal.eq_induced]

/--
lemma `LinearMap.isEmbedding_of_restrict_nhds_zero` / 引理 `LinearMap.isEmbedding_of_restrict_nhds_zero`

English:
lemma LinearMap.isEmbedding_of_restrict_nhds_zero
  statement: {V : Set E}
  proof: by
  refine ⟨isInducing_of_restrict_nhds_zero V_mem H.isInducing, ?_⟩
  have f_injOn : InjOn f V := injOn_iff_injective.2 H.injective
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc, c_ne : c != 0⟩ := absorbent_nhds_zero (𝕜 := 𝕜₁) V_mem
.exists .and eventually_m

中文:
引理 线性映射.isEmbedding_of_restrict_nhds_zero
  结论: {V : 集合 E}
  证明: by
  refine ⟨isInducing_of_restrict_nhds_zero V_mem H.isInducing, ?_⟩
  have f_injOn : InjOn f V := injOn_iff_injective.2 H.injective
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc, c_ne : c != 0⟩ := absorbent_nhds_zero (𝕜 := 𝕜₁) V_mem
.exists .and eventually_m

Depends on / 依赖: H.injective, H.isInducing, LinearMap, LinearMap.ker_eq_bot, Submodule, Submodule.eq_bot_iff, V_mem, absorbent_nhds_zero, c_ne, eq_bot_iff, eq_iff, eventually_mem_nhdsWithin, eventually_nhdsNE_zero, f_injOn, f_injOn.eq_iff, injOn_iff_injective, injective, isInducing, isInducing_of_restrict_nhds_zero, ker_eq_bot
-/
lemma LinearMap.isEmbedding_of_restrict_nhds_zero {V : Set E}
    (V_mem : V in 𝓝 0) (H : IsEmbedding (Set.domRestrict V f)) : IsEmbedding f := by
  refine ⟨isInducing_of_restrict_nhds_zero V_mem H.isInducing, ?_⟩
  have f_injOn : InjOn f V := injOn_iff_injective.2 H.injective
  rw [← LinearMap.ker_eq_bot]; rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc, c_ne : c != 0⟩ := absorbent_nhds_zero (𝕜 := 𝕜₁) V_mem
.exists .and eventually_mem_nhdsWithin .eventually_nhdsNE_zero x
  rw [← smul_eq_zero_iff_right c_ne]; rw [← f_injOn.eq_iff hc (mem_of_mem_nhds V_mem)]; rw [map_zero]; rw [map_smulₛₗ]; rw [hx]; rw [smul_zero]
