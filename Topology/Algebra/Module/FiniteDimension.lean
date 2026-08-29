/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.Simple
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Finite-dimensional topological vector spaces over complete fields

Let `𝕜` be a complete nontrivially normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]`
and `[ContinuousSMul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `LinearMap.continuous_iff_isClosed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `LinearMap.continuous_of_finiteDimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equivFun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live in the same universe. So we start by doing that as a private
lemma, then we deduce `LinearMap.continuous_of_finiteDimensional` from it, and then the general
result follows as `continuous_equivFun_basis`.

-/

@[expose] public section

open Filter Module Set TopologicalSpace Topology

universe u v w x

noncomputable section

section FiniteDimensional

variable {𝕜 E F : Type*}
  [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]

-- Note: ideally this would be in `Mathlib.Topology.Algebra.Module.Basic`, but `CoFG` imports
-- too much at the moment for this to be allowed.
/--
Instance `Submodule.CoFG.topologicalClosure` / 实例 `Submodule.CoFG.topologicalClosure`

English:
instance Submodule.CoFG.topologicalClosure
  signature: [Ring 𝕜] [Module 𝕜 E] [ContinuousAdd E]
  body: ‹s.CoFG›.of_le s.le_topologicalClosure

中文:
实例 子模.CoFG.topologicalClosure
  签名: [环 𝕜] [模 𝕜 E] [连续加法 E]
  定义体: ‹s.CoFG›.of_le s.le_topologicalClosure

Depends on / 依赖: le_topologicalClosure, of_le, s.CoFG, s.le_topologicalClosure
-/
instance Submodule.CoFG.topologicalClosure [Ring 𝕜] [Module 𝕜 E] [ContinuousAdd E]
    [ContinuousConstSMul 𝕜 E] (s : Submodule 𝕜 E) [s.CoFG] : s.topologicalClosure.CoFG :=
  ‹s.CoFG›.of_le s.le_topologicalClosure

/--
Instance `ContinuousLinearMap.instModuleFinite` / 实例 `ContinuousLinearMap.instModuleFinite`

English:
instance ContinuousLinearMap.instModuleFinite
  signature: [CommRing 𝕜] [Module 𝕜 E] [Module.Finite 𝕜 E]
  body: .of_injective (ContinuousLinearMap.coeLM 𝕜 : (E ->L[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

中文:
实例 连续线性映射.instModuleFinite
  签名: [交换环 𝕜] [模 𝕜 E] [模.有限 𝕜 E]
  定义体: .of_injective (ContinuousLinearMap.coeLM 𝕜 : (E ->L[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM, ContinuousLinearMap.coe_injective, coe_injective, of_injective
-/
instance ContinuousLinearMap.instModuleFinite [CommRing 𝕜] [Module 𝕜 E] [Module.Finite 𝕜 E]
    [Module 𝕜 F] [IsNoetherian 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    Module.Finite 𝕜 (E ->L[𝕜] F) :=
  .of_injective (ContinuousLinearMap.coeLM 𝕜 : (E ->L[𝕜] F) ->ₗ[𝕜] E ->ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

/--
theorem `ContinuousLinearMap.finiteDimensional` / 定理 `ContinuousLinearMap.finiteDimensional`

English:
theorem ContinuousLinearMap.finiteDimensional
  statement: [Field 𝕜] [Module 𝕜 E]
  proof: inferInstance

中文:
定理 连续线性映射.finiteDimensional
  结论: [域 𝕜] [模 𝕜 E]
  证明: inferInstance
-/
protected theorem ContinuousLinearMap.finiteDimensional [Field 𝕜] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [Module 𝕜 F] [FiniteDimensional 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    FiniteDimensional 𝕜 (E ->L[𝕜] F) :=
  inferInstance

end FiniteDimensional

section NormedField

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [IsTopologicalAddGroup F']
  [ContinuousSMul 𝕜 F']

/--
theorem `unique_topology_of_t2` / 定理 `unique_topology_of_t2`

English:
theorem unique_topology_of_t2
  statement: {t : TopologicalSpace 𝕜} (h₁ : @IsTopologicalAddGroup 𝕜 t _)
  proof: by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine IsTopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`,

中文:
定理 unique_topology_of_t2
  结论: {t : 拓扑空间 𝕜} (h₁ : @是拓扑加群 𝕜 t _)
  证明: by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine IsTopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`,
-/
theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @IsTopologicalAddGroup 𝕜 t _)
    (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine IsTopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [Metric.nhds_basis_closedBall.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
have : {ξ₀}ᶜ in @nhds 𝕜 t 0 := IsOpen.mem_nhds isOpen_compl_singleton
mem_compl_singleton_iff.mpr Ne.symm norm_ne_zero_iff.mp hξ₀.ne.symm
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 {ξ₀}ᶜ in @nhds 𝕜 t 0 := balancedCore_mem_nhds_zero this
    refine mem_of_superset this fun ξ hξ => ?_
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closedBall_self hε.le
    · rw [mem_closedBall_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra! h
      suffices (ξ₀ * ξ⁻¹) • ξ in balancedCore 𝕜 {ξ₀}ᶜ by
        rw [smul_eq_mul]; rw [mul_assoc]; rw [inv_mul_cancel₀ hξ0]; rw [mul_one] at this
        exact notMem_compl_iff.mpr (mem_singleton ξ₀) ((balancedCore_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine (balancedCore_balanced _).smul_mem ?_ hξ
      rw [norm_mul]; rw [norm_inv]; rw [mul_inv_le_iff₀ (norm_pos_iff.mpr hξ0)]; rw [one_mul]
      exact (hξ₀ε.trans h).le
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (fun x ↦ x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0 =
          map id (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) :=
        map_id.symm
      _ = map (fun x => id x • (1 : 𝕜)) (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) := by
        simp
      _ <= @nhds 𝕜 t ((0 : 𝕜) • (1 : 𝕜)) :=
        (@Tendsto.smul_const _ _ _ hnorm.toUniformSpace.toTopologicalSpace t _ _ _ _ _
          tendsto_id (1 : 𝕜))
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]

/--
theorem `LinearMap.continuous_of_isClosed_ker` / 定理 `LinearMap.continuous_of_isClosed_ker`

English:
theorem LinearMap.continuous_of_isClosed_ker
  statement: (l : E ->ₗ[𝕜] 𝕜)
  proof: by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ

中文:
定理 线性映射.continuous_of_isClosed_ker
  结论: (l : E ->ₗ[𝕜] 𝕜)
  证明: by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ
-/
theorem LinearMap.continuous_of_isClosed_ker (l : E ->ₗ[𝕜] 𝕜)
    (hl : IsClosed (LinearMap.ker l : Set E)) :
    Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 (LinearMap.range l) = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range l).finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.range_eq_top]; rw [Submodule.range_liftQ]
      exact Submodule.eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ LinearMap.ker l) ≃ₗ[𝕜] 𝕜 :=
      LinearEquiv.ofBijective ((LinearMap.ker l).liftQ l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E -> 𝕜) = φ ∘ (LinearMap.ker l).mkQ := by ext; rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.toEquiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.toEquiv.symm inferInstance = hnorm.toUniformSpace.toTopologicalSpace := by
      refine unique_topology_of_t2 (topologicalAddGroup_induced φ.symm.toLinearMap)
        (continuousSMul_induced φ.symm.toMulActionHom) ?_
      rw [t2Space_iff]
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.toEquiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    simp_rw +instances [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng

/--
theorem `LinearMap.continuous_iff_isClosed_ker` / 定理 `LinearMap.continuous_iff_isClosed_ker`

English:
theorem LinearMap.continuous_iff_isClosed_ker
  given: (l : E ->ₗ[𝕜] 𝕜)
  proof: ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

中文:
定理 线性映射.continuous_iff_isClosed_ker
  条件: (l : E ->ₗ[𝕜] 𝕜)
  证明: ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

Depends on / 依赖: continuous_of_isClosed_ker, isClosed_singleton, isClosed_singleton.preimage, l.continuous_of_isClosed_ker, preimage
-/
theorem LinearMap.continuous_iff_isClosed_ker (l : E ->ₗ[𝕜] 𝕜) :
    Continuous l ↔ IsClosed (LinearMap.ker l : Set E) :=
  ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

/--
theorem `LinearMap.continuous_of_nonzero_on_open` / 定理 `LinearMap.continuous_of_nonzero_on_open`

English:
theorem LinearMap.continuous_of_nonzero_on_open
  statement: (l : E ->ₗ[𝕜] 𝕜) (s : Set E) (hs₁ : IsOpen s)
  proof: by
  refine l.continuous_of_isClosed_ker (l.isClosed_or_dense_ker.resolve_right fun hl => ?_)
  rcases hs₂ with ⟨x, hx⟩
  have : x in interior (LinearMap.ker l : Set E)ᶜ := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this

中文:
定理 线性映射.continuous_of_nonzero_on_open
  结论: (l : E ->ₗ[𝕜] 𝕜) (s : 集合 E) (hs₁ : 是开集 s)
  证明: by
  refine l.continuous_of_isClosed_ker (l.isClosed_or_dense_ker.resolve_right fun hl => ?_)
  rcases hs₂ with ⟨x, hx⟩
  have : x in interior (LinearMap.ker l : Set E)ᶜ := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this

Depends on / 依赖: LinearMap, LinearMap.ker, continuous_of_isClosed_ker, hl.interior_compl, interior, interior_compl, isClosed_or_dense_ker, l.continuous_of_isClosed_ker, l.isClosed_or_dense_ker.resolve_right, mem_interior_iff_mem_nhds, mem_nhds, mem_of_superset, resolve_right
-/
theorem LinearMap.continuous_of_nonzero_on_open (l : E ->ₗ[𝕜] 𝕜) (s : Set E) (hs₁ : IsOpen s)
    (hs₂ : s.Nonempty) (hs₃ : forall x in s, l x != 0) : Continuous l := by
  refine l.continuous_of_isClosed_ker (l.isClosed_or_dense_ker.resolve_right fun hl => ?_)
  rcases hs₂ with ⟨x, hx⟩
  have : x in interior (LinearMap.ker l : Set E)ᶜ := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this

variable [CompleteSpace 𝕜]

/--
theorem `continuous_equivFun_basis_aux` / 定理 `continuous_equivFun_basis_aux`

English:
theorem continuous_equivFun_basis_aux
  statement: [T2Space E] {ι : Type v} [Finite ι]
  proof: by
  have := Fintype.ofFinite ι
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices forall n, Fintype.card ι = n -> Continuous ξ.equivFun by exact this _ rfl
  intro n hn
  induction n generalizing ι E with
 

中文:
定理 continuous_equivFun_basis_aux
  结论: [T2空间 E] {ι : 类型v} [有限 ι]
  证明: by
  have := Fintype.ofFinite ι
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices forall n, Fintype.card ι = n -> Continuous ξ.equivFun by exact this _ rfl
  intro n hn
  induction n generalizing ι E with
 
-/
private theorem continuous_equivFun_basis_aux [T2Space E] {ι : Type v} [Finite ι]
    (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun := by
  have := Fintype.ofFinite ι
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices forall n, Fintype.card ι = n -> Continuous ξ.equivFun by exact this _ rfl
  intro n hn
  induction n generalizing ι E with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
  | succ n IH =>
    have : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : forall s : Submodule 𝕜 E, finrank 𝕜 s = n -> IsClosed (s : Set E) := by
      intro s s_dim
      let : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
      let b := Basis.ofVectorSpace 𝕜 s
      have U : IsUniformEmbedding b.equivFun.symm.toEquiv := by
        have : Fintype.card (Basis.ofVectorSpaceIndex 𝕜 s) = n := by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equivFun := IH b inferInstance this
        exact
          b.equivFun.symm.isUniformEmbedding b.equivFun.symm.toLinearMap.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        completeSpace_coe_iff_isComplete.1 ((completeSpace_congr U).1 inferInstance)
      exact this.isClosed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : forall f : E ->ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases H : finrank 𝕜 (LinearMap.range f) = 0
      · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
      · have : finrank 𝕜 (LinearMap.ker f) = n := by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ]; rw [hn] at Z
          have : finrank 𝕜 (LinearMap.range f) = 1 :=
            le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range f).finrank_le) (zero_lt_iff.mpr H)
          rw [this]; rw [add_comm]; rw [Nat.add_one] at Z
          exact Nat.succ.inj Z
        have : IsClosed (LinearMap.ker f : Set E) := H₁ _ this
        exact LinearMap.continuous_of_isClosed_ker f this
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)

/-- A finite-dimensional t2 vector space over a complete field must carry the module topology.

Not declared as a global instance only for performance reasons. -/
@[local instance]
/--
lemma `isModuleTopologyOfFiniteDimensional` / 引理 `isModuleTopologyOfFiniteDimensional`

English:
lemma isModuleTopologyOfFiniteDimensional
  given: [T2Space E] [FiniteDimensional 𝕜 E]
  proof: -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- use that it has the module topology
  let b := Basis.ofVectorSpace 𝕜 E
  have continuousEquiv : E ≃L[𝕜] (Basis.ofVectorSpaceIndex 𝕜 E) -> 𝕜 :=
    { __ := b.equivFun
      continuous_toFun := continu

中文:
引理 isModuleTopologyOfFiniteDimensional
  条件: [T2空间 E] [有限维 𝕜 E]
  证明: -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- use that it has the module topology
  let b := Basis.ofVectorSpace 𝕜 E
  have continuousEquiv : E ≃L[𝕜] (Basis.ofVectorSpaceIndex 𝕜 E) -> 𝕜 :=
    { __ := b.equivFun
      continuous_toFun := continu
-/
lemma isModuleTopologyOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    IsModuleTopology 𝕜 E :=
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- use that it has the module topology
  let b := Basis.ofVectorSpace 𝕜 E
  have continuousEquiv : E ≃L[𝕜] (Basis.ofVectorSpaceIndex 𝕜 E) -> 𝕜 :=
    { __ := b.equivFun
      continuous_toFun := continuous_equivFun_basis_aux b
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := 𝕜)
        (A := (Basis.ofVectorSpaceIndex 𝕜 E) -> 𝕜) (B := E) b.equivFun.symm }
  IsModuleTopology.iso continuousEquiv.symm

/--
theorem `LinearMap.continuous_of_finiteDimensional` / 定理 `LinearMap.continuous_of_finiteDimensional`

English:
theorem LinearMap.continuous_of_finiteDimensional
  statement: [T2Space E] [FiniteDimensional 𝕜 E]
  proof: IsModuleTopology.continuous_of_linearMap f

中文:
定理 线性映射.continuous_of_finiteDimensional
  结论: [T2空间 E] [有限维 𝕜 E]
  证明: IsModuleTopology.continuous_of_linearMap f

Depends on / 依赖: IsModuleTopology, IsModuleTopology.continuous_of_linearMap, continuous_of_linearMap
-/
theorem LinearMap.continuous_of_finiteDimensional [T2Space E] [FiniteDimensional 𝕜 E]
    (f : E ->ₗ[𝕜] F') : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

/--
Instance `LinearMap.continuousLinearMapClassOfFiniteDimensional` / 实例 `LinearMap.continuousLinearMapClassOfFiniteDimensional`

English:
instance LinearMap.continuousLinearMapClassOfFiniteDimensional
  signature: [T2Space E] [FiniteDimensional 𝕜 E]
  body: { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

中文:
实例 线性映射.continuousLinearMapClassOfFiniteDimensional
  签名: [T2空间 E] [有限维 𝕜 E]
  定义体: { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

Depends on / 依赖: LinearMap, LinearMap.semilinearMapClass, continuous_of_finiteDimensional, f.continuous_of_finiteDimensional, map_continuous, semilinearMapClass
-/
instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E ->ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

/--
theorem `continuous_equivFun_basis` / 定理 `continuous_equivFun_basis`

English:
theorem continuous_equivFun_basis
  given: [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 𝕜 E)
  proof: haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

中文:
定理 continuous_equivFun_basis
  条件: [T2空间 E] {ι : 类型} [有限 ι] (ξ : 基 ι 𝕜 E)
  证明: haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

Depends on / 依赖: FiniteDimensional, continuous_of_finiteDimensional, equivFun, equivFun.toLinearMap.continuous_of_finiteDimensional, finiteDimensional_of_finite, toLinearMap
-/
theorem continuous_equivFun_basis [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun :=
  haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where
  body: ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

中文:
定义 toContinuousLinearMap
  签名: : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where
  定义体: ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

Depends on / 依赖: continuous_of_finiteDimensional, f.continuous_of_finiteDimensional
-/
def toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where
  toFun f := ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

/--
Definition of `_root_.Module.End.toContinuousLinearMap` / `_root_.Module.End.toContinuousLinearMap` 的定义

English:
definition _root_.Module.End.toContinuousLinearMap
  signature: (E : Type v) [NormedAddCommGroup E]
  body: { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]

中文:
定义 _root_.模.End.toContinuousLinearMap
  签名: (E : 类型v) [赋范交换加群 E]
  定义体: { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toContinuousLinearMap, commutes, map_mul, toContinuousLinearMap
-/
def _root_.Module.End.toContinuousLinearMap (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : (E ->ₗ[𝕜] E) ≃ₐ[𝕜] (E ->L[𝕜] E) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]
/--
theorem `coe_toContinuousLinearMap'` / 定理 `coe_toContinuousLinearMap'`

English:
theorem coe_toContinuousLinearMap'
  given: (f : E ->ₗ[𝕜] F')
  statement: ⇑(LinearMap.toContinuousLinearMap f) = f
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearMap'
  条件: (f : E ->ₗ[𝕜] F')
  结论: ⇑(线性映射.toContinuousLinearMap f) = f
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearMap' (f : E ->ₗ[𝕜] F') : ⇑(LinearMap.toContinuousLinearMap f) = f :=
  rfl

@[simp]
/--
theorem `coe_toContinuousLinearMap` / 定理 `coe_toContinuousLinearMap`

English:
theorem coe_toContinuousLinearMap
  given: (f : E ->ₗ[𝕜] F')
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearMap
  条件: (f : E ->ₗ[𝕜] F')
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearMap (f : E ->ₗ[𝕜] F') :
    ((LinearMap.toContinuousLinearMap f) : E ->ₗ[𝕜] F') = f :=
  rfl

@[simp]
/--
theorem `coe_toContinuousLinearMap_symm` / 定理 `coe_toContinuousLinearMap_symm`

English:
theorem coe_toContinuousLinearMap_symm
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearMap_symm
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearMap_symm :
    ⇑(toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F').symm =
      ((↑) : (E ->L[𝕜] F') -> E ->ₗ[𝕜] F') :=
  rfl

@[simp]
/--
theorem `det_toContinuousLinearMap` / 定理 `det_toContinuousLinearMap`

English:
theorem det_toContinuousLinearMap
  given: (f : E ->ₗ[𝕜] E)
  proof: rfl

中文:
定理 det_toContinuousLinearMap
  条件: (f : E ->ₗ[𝕜] E)
  证明: rfl
-/
theorem det_toContinuousLinearMap (f : E ->ₗ[𝕜] E) :
    (LinearMap.toContinuousLinearMap f).det = LinearMap.det f :=
  rfl

/--
theorem `isOpenMap_of_finiteDimensional` / 定理 `isOpenMap_of_finiteDimensional`

English:
theorem isOpenMap_of_finiteDimensional
  given: (f : F ->ₗ[𝕜] E) (hf : Function.Surjective f)
  proof: IsModuleTopology.isOpenMap_of_surjective hf

中文:
定理 isOpenMap_of_finiteDimensional
  条件: (f : F ->ₗ[𝕜] E) (hf : 函数.满射 f)
  证明: IsModuleTopology.isOpenMap_of_surjective hf

Depends on / 依赖: IsModuleTopology, IsModuleTopology.isOpenMap_of_surjective, isOpenMap_of_surjective
-/
theorem isOpenMap_of_finiteDimensional (f : F ->ₗ[𝕜] E) (hf : Function.Surjective f) :
    IsOpenMap f :=
  IsModuleTopology.isOpenMap_of_surjective hf

/--
Instance `canLiftContinuousLinearMap` / 实例 `canLiftContinuousLinearMap`

English:
instance canLiftContinuousLinearMap
  signature: : CanLift (E ->ₗ[𝕜] F) (E ->L[𝕜] F) (↑) fun _ => True
  body: ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩

中文:
实例 canLiftContinuousLinearMap
  签名: : CanLift (E ->ₗ[𝕜] F) (E ->L[𝕜] F) (↑) fun _ => 真
  定义体: ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩

Depends on / 依赖: LinearMap, LinearMap.toContinuousLinearMap, toContinuousLinearMap
-/
instance canLiftContinuousLinearMap : CanLift (E ->ₗ[𝕜] F) (E ->L[𝕜] F) (↑) fun _ => True :=
  ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩

/--
lemma `toContinuousLinearMap_eq_iff_eq_toLinearMap` / 引理 `toContinuousLinearMap_eq_iff_eq_toLinearMap`

English:
lemma toContinuousLinearMap_eq_iff_eq_toLinearMap
  given: (f : E ->ₗ[𝕜] E) (g : E ->L[𝕜] E)
  proof: by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

中文:
引理 toContinuousLinearMap_eq_iff_eq_toLinearMap
  条件: (f : E ->ₗ[𝕜] E) (g : E ->L[𝕜] E)
  证明: by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, LinearMap, LinearMap.ext_iff, ext_iff
-/
lemma toContinuousLinearMap_eq_iff_eq_toLinearMap (f : E ->ₗ[𝕜] E) (g : E ->L[𝕜] E) :
    f.toContinuousLinearMap = g ↔ f = g.toLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

/--
lemma `_root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap` / 引理 `_root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap`

English:
lemma _root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap
  statement: (g : E ->L[𝕜] E)
  proof: by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

中文:
引理 _root_.连续线性映射.toLinearMap_eq_iff_eq_toContinuousLinearMap
  结论: (g : E ->L[𝕜] E)
  证明: by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, LinearMap, LinearMap.ext_iff, ext_iff
-/
lemma _root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap (g : E ->L[𝕜] E)
    (f : E ->ₗ[𝕜] E) : g.toLinearMap = f ↔ g = f.toContinuousLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

end LinearMap

section

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

namespace LinearEquiv

/--
Definition of `toContinuousLinearEquiv` / `toContinuousLinearEquiv` 的定义

English:
definition toContinuousLinearEquiv
  signature: (e : E ≃ₗ[𝕜] F)
  body: { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]

中文:
定义 toContinuousLinearEquiv
  签名: (e : E ≃ₗ[𝕜] F)
  定义体: { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]

Depends on / 依赖: FiniteDimensional, continuous_invFun, continuous_of_finiteDimensional, continuous_toFun, e.finiteDimensional, e.symm.toLinearMap.continuous_of_finiteDimensional, e.toLinearMap.continuous_of_finiteDimensional, finiteDimensional, toLinearMap
-/
def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
/--
theorem `coe_toContinuousLinearEquiv` / 定理 `coe_toContinuousLinearEquiv`

English:
theorem coe_toContinuousLinearEquiv
  given: (e : E ≃ₗ[𝕜] F)
  statement: (e.toContinuousLinearEquiv : E ->ₗ[𝕜] F) = e
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearEquiv
  条件: (e : E ≃ₗ[𝕜] F)
  结论: (e.toContinuousLinearEquiv : E ->ₗ[𝕜] F) = e
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E ->ₗ[𝕜] F) = e :=
  rfl

@[simp]
/--
theorem `coe_toContinuousLinearEquiv'` / 定理 `coe_toContinuousLinearEquiv'`

English:
theorem coe_toContinuousLinearEquiv'
  given: (e : E ≃ₗ[𝕜] F)
  statement: (e.toContinuousLinearEquiv : E -> F) = e
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearEquiv'
  条件: (e : E ≃ₗ[𝕜] F)
  结论: (e.toContinuousLinearEquiv : E -> F) = e
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearEquiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E -> F) = e :=
  rfl

@[simp]
/--
theorem `coe_toContinuousLinearEquiv_symm` / 定理 `coe_toContinuousLinearEquiv_symm`

English:
theorem coe_toContinuousLinearEquiv_symm
  given: (e : E ≃ₗ[𝕜] F)
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearEquiv_symm
  条件: (e : E ≃ₗ[𝕜] F)
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.toLinearEquiv.symm : F ->ₗ[𝕜] E) = e.symm := rfl

@[simp]
/--
theorem `coe_toContinuousLinearEquiv_symm'` / 定理 `coe_toContinuousLinearEquiv_symm'`

English:
theorem coe_toContinuousLinearEquiv_symm'
  given: (e : E ≃ₗ[𝕜] F)
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearEquiv_symm'
  条件: (e : E ≃ₗ[𝕜] F)
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearEquiv_symm' (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F -> E) = e.symm :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_toContinuousLinearEquiv` / 定理 `toLinearEquiv_toContinuousLinearEquiv`

English:
theorem toLinearEquiv_toContinuousLinearEquiv
  given: (e : E ≃ₗ[𝕜] F)
  proof: by
  ext x
  rfl

中文:
定理 toLinearEquiv_toContinuousLinearEquiv
  条件: (e : E ≃ₗ[𝕜] F)
  证明: by
  ext x
  rfl
-/
theorem toLinearEquiv_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.toLinearEquiv = e := by
  ext x
  rfl

/--
theorem `toLinearEquiv_toContinuousLinearEquiv_symm` / 定理 `toLinearEquiv_toContinuousLinearEquiv_symm`

English:
theorem toLinearEquiv_toContinuousLinearEquiv_symm
  given: (e : E ≃ₗ[𝕜] F)
  proof: by
  ext x
  rfl

中文:
定理 toLinearEquiv_toContinuousLinearEquiv_symm
  条件: (e : E ≃ₗ[𝕜] F)
  证明: by
  ext x
  rfl
-/
theorem toLinearEquiv_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm := by
  ext x
  rfl

/--
Instance `canLiftContinuousLinearEquiv` / 实例 `canLiftContinuousLinearEquiv`

English:
instance canLiftContinuousLinearEquiv
  signature: :
  body: ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

中文:
实例 canLiftContinuousLinearEquiv
  签名: :
  定义体: ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

Depends on / 依赖: f.toLinearEquiv_toContinuousLinearEquiv, toLinearEquiv_toContinuousLinearEquiv
-/
instance canLiftContinuousLinearEquiv :
    CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousLinearEquiv.toLinearEquiv fun _ => True :=
  ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

end LinearEquiv

variable [FiniteDimensional 𝕜 F]

/--
theorem `FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq` / 定理 `FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq`

English:
theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
  proof: (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

中文:
定理 有限维.nonempty_continuousLinearEquiv_of_finrank_eq
  证明: (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

Depends on / 依赖: LinearEquiv, LinearEquiv.toContinuousLinearEquiv, nonempty_linearEquiv_of_finrank_eq, toContinuousLinearEquiv
-/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/--
theorem `FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq` / 定理 `FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq`

English:
theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq
  proof: ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

中文:
定理 有限维.nonempty_continuousLinearEquiv_iff_finrank_eq
  证明: ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

Depends on / 依赖: FiniteDimensional, FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq, finrank_eq, h.toLinearEquiv.finrank_eq, nonempty_continuousLinearEquiv_of_finrank_eq, toLinearEquiv
-/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq :
    Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

/--
Definition of `ContinuousLinearEquiv.ofFinrankEq` / `ContinuousLinearEquiv.ofFinrankEq` 的定义

English:
definition ContinuousLinearEquiv.ofFinrankEq
  signature: (cond : finrank 𝕜 E = finrank 𝕜 F)
  body: (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

中文:
定义 连续线性等价.ofFinrankEq
  签名: (cond : finrank 𝕜 E = finrank 𝕜 F)
  定义体: (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

Depends on / 依赖: LinearEquiv, LinearEquiv.ofFinrankEq, ofFinrankEq, toContinuousLinearEquiv
-/
def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

end

namespace Module.Basis
variable {ι : Type*} [Finite ι] [T2Space E]

/--
Definition of `constrL` / `constrL` 的定义

English:
definition constrL
  signature: (v : Basis ι 𝕜 E) (f : ι -> F)
  body: haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp]

中文:
定义 constrL
  签名: (v : 基 ι 𝕜 E) (f : ι -> F)
  定义体: haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp]

Depends on / 依赖: FiniteDimensional, LinearMap, LinearMap.toContinuousLinearMap, constr, finiteDimensional_of_finite, toContinuousLinearMap, v.constr, v.finiteDimensional_of_finite
-/
def constrL (v : Basis ι 𝕜 E) (f : ι -> F) : E ->L[𝕜] F :=
  haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp]
/--
theorem `coe_constrL` / 定理 `coe_constrL`

English:
theorem coe_constrL
  given: (v : Basis ι 𝕜 E) (f : ι -> F)
  statement: (v.constrL f : E ->ₗ[𝕜] F) = v.constr 𝕜 f
  proof: rfl

中文:
定理 coe_constrL
  条件: (v : 基 ι 𝕜 E) (f : ι -> F)
  结论: (v.constrL f : E ->ₗ[𝕜] F) = v.constr 𝕜 f
  证明: rfl
-/
theorem coe_constrL (v : Basis ι 𝕜 E) (f : ι -> F) : (v.constrL f : E ->ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
@[simps! apply]
/--
Definition of `equivFunL` / `equivFunL` 的定义

English:
definition equivFunL
  signature: (v : Basis ι 𝕜 E)
  body: { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_

中文:
定义 equivFunL
  签名: (v : 基 ι 𝕜 E)
  定义体: { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_

Depends on / 依赖: Continuous, FiniteDimensional, continuous_invFun, continuous_of_finiteDimensional, continuous_toFun, equivFun, finiteDimensional_of_finite, toLinearMap, v.equivFun, v.equivFun.symm.toFun, v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional, v.equivFun.toLinearMap.continuous_of_finiteDimensional, v.finiteDimensional_of_finite
-/
def equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι -> 𝕜 :=
  { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
/--
lemma `equivFunL_symm_apply_repr` / 引理 `equivFunL_symm_apply_repr`

English:
lemma equivFunL_symm_apply_repr
  given: (v : Basis ι 𝕜 E) (x : E)
  proof: v.equivFunL.symm_apply_apply x

@[simp]

中文:
引理 equivFunL_symm_apply_repr
  条件: (v : 基 ι 𝕜 E) (x : E)
  证明: v.equivFunL.symm_apply_apply x

@[simp]

Depends on / 依赖: equivFunL, symm_apply_apply, v.equivFunL.symm_apply_apply
-/
lemma equivFunL_symm_apply_repr (v : Basis ι 𝕜 E) (x : E) :
    v.equivFunL.symm (v.repr x) = x :=
  v.equivFunL.symm_apply_apply x

@[simp]
/--
theorem `constrL_apply` / 定理 `constrL_apply`

English:
theorem constrL_apply
  given: {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι -> F) (e : E)
  proof: v.constr_apply_fintype 𝕜 _ _

@[simp 1100]

中文:
定理 constrL_apply
  条件: {ι : 类型} [有限类型 ι] (v : 基 ι 𝕜 E) (f : ι -> F) (e : E)
  证明: v.constr_apply_fintype 𝕜 _ _

@[simp 1100]

Depends on / 依赖: constr_apply_fintype, v.constr_apply_fintype
-/
theorem constrL_apply {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι -> F) (e : E) :
    v.constrL f e = ∑ i, v.equivFun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp 1100]
/--
theorem `constrL_basis` / 定理 `constrL_basis`

English:
theorem constrL_basis
  given: (v : Basis ι 𝕜 E) (f : ι -> F) (i : ι)
  statement: v.constrL f (v i) = f i
  proof: v.constr_basis 𝕜 _ _

中文:
定理 constrL_basis
  条件: (v : 基 ι 𝕜 E) (f : ι -> F) (i : ι)
  结论: v.constrL f (v i) = f i
  证明: v.constr_basis 𝕜 _ _

Depends on / 依赖: constr_basis, v.constr_basis
-/
theorem constrL_basis (v : Basis ι 𝕜 E) (f : ι -> F) (i : ι) : v.constrL f (v i) = f i :=
  v.constr_basis 𝕜 _ _

end Module.Basis

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/--
Definition of `toContinuousLinearEquivOfDetNeZero` / `toContinuousLinearEquivOfDetNeZero` 的定义

English:
definition toContinuousLinearEquivOfDetNeZero
  signature: (f : E ->L[𝕜] E) (hf : f.det != 0)
  body: ((f : E ->ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]

中文:
定义 toContinuousLinearEquivOfDetNeZero
  签名: (f : E ->L[𝕜] E) (hf : f.det != 0)
  定义体: ((f : E ->ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]

Depends on / 依赖: equivOfDetNeZero, toContinuousLinearEquiv
-/
def toContinuousLinearEquivOfDetNeZero (f : E ->L[𝕜] E) (hf : f.det != 0) : E ≃L[𝕜] E :=
  ((f : E ->ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]
/--
theorem `coe_toContinuousLinearEquivOfDetNeZero` / 定理 `coe_toContinuousLinearEquivOfDetNeZero`

English:
theorem coe_toContinuousLinearEquivOfDetNeZero
  given: (f : E ->L[𝕜] E) (hf : f.det != 0)
  proof: by
  ext x
  rfl

@[simp]

中文:
定理 coe_toContinuousLinearEquivOfDetNeZero
  条件: (f : E ->L[𝕜] E) (hf : f.det != 0)
  证明: by
  ext x
  rfl

@[simp]
-/
theorem coe_toContinuousLinearEquivOfDetNeZero (f : E ->L[𝕜] E) (hf : f.det != 0) :
    (f.toContinuousLinearEquivOfDetNeZero hf : E ->L[𝕜] E) = f := by
  ext x
  rfl

@[simp]
/--
theorem `toContinuousLinearEquivOfDetNeZero_apply` / 定理 `toContinuousLinearEquivOfDetNeZero_apply`

English:
theorem toContinuousLinearEquivOfDetNeZero_apply
  given: (f : E ->L[𝕜] E) (hf : f.det != 0) (x : E)
  proof: rfl

中文:
定理 toContinuousLinearEquivOfDetNeZero_apply
  条件: (f : E ->L[𝕜] E) (hf : f.det != 0) (x : E)
  证明: rfl
-/
theorem toContinuousLinearEquivOfDetNeZero_apply (f : E ->L[𝕜] E) (hf : f.det != 0) (x : E) :
    f.toContinuousLinearEquivOfDetNeZero hf x = f x :=
  rfl

/--
theorem `_root_.Matrix.toLin_finTwoProd_toContinuousLinearMap` / 定理 `_root_.Matrix.toLin_finTwoProd_toContinuousLinearMap`

English:
theorem _root_.Matrix.toLin_finTwoProd_toContinuousLinearMap
  given: (a b c d : 𝕜)
  proof: ContinuousLinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

中文:
定理 _root_.矩阵.toLin_finTwoProd_toContinuousLinearMap
  条件: (a b c d : 𝕜)
  证明: ContinuousLinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, Matrix, Matrix.toLin_finTwoProd_apply, toLin_finTwoProd_apply
-/
theorem _root_.Matrix.toLin_finTwoProd_toContinuousLinearMap (a b c d : 𝕜) :
    LinearMap.toContinuousLinearMap
      (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜) !![a, b; c, d]) =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
ContinuousLinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

end ContinuousLinearMap

end NormedField

section IsUniformAddGroup

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

include 𝕜 in
/--
theorem `FiniteDimensional.complete` / 定理 `FiniteDimensional.complete`

English:
theorem FiniteDimensional.complete
  given: [FiniteDimensional 𝕜 E]
  statement: CompleteSpace E
  proof: by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

中文:
定理 有限维.complete
  条件: [有限维 𝕜 E]
  结论: 完备空间 E
  证明: by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, IsUniformEmbedding, completeSpace_congr, e.symm.isUniformEmbedding, e.toEquiv.symm, finrank, finrank_fin_fun, isUniformEmbedding, ofFinrankEq, toEquiv
-/
theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

variable {𝕜 E}

/--
theorem `Submodule.complete_of_finiteDimensional` / 定理 `Submodule.complete_of_finiteDimensional`

English:
theorem Submodule.complete_of_finiteDimensional
  given: (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s]
  proof: haveI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

中文:
定理 子模.complete_of_finiteDimensional
  条件: (s : 子模 𝕜 E) [有限维 𝕜 s]
  证明: haveI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, IsUniformAddGroup, complete, completeSpace_coe_iff_isComplete, isUniformAddGroup, s.toAddSubgroup.isUniformAddGroup, toAddSubgroup
-/
theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  haveI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

end IsUniformAddGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F]

/--
theorem `Submodule.closed_of_finiteDimensional` / 定理 `Submodule.closed_of_finiteDimensional`

English:
theorem Submodule.closed_of_finiteDimensional
  proof: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  s.complete_of_finiteDimensional.isClosed

中文:
定理 子模.closed_of_finiteDimensional
  证明: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  s.complete_of_finiteDimensional.isClosed

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, complete_of_finiteDimensional, isClosed, isUniformAddGroup_of_addCommGroup, rightUniformSpace, s.complete_of_finiteDimensional.isClosed
-/
theorem Submodule.closed_of_finiteDimensional
    [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  s.complete_of_finiteDimensional.isClosed

/--
theorem `Submodule.isClosed_mono_of_finiteDimensional_quotient` / 定理 `Submodule.isClosed_mono_of_finiteDimensional_quotient`

English:
theorem Submodule.isClosed_mono_of_finiteDimensional_quotient
  proof: by
  rw [show t = comap s.mkQ (map s.mkQ t) by simpa]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

中文:
定理 子模.isClosed_mono_of_finiteDimensional_quotient
  证明: by
  rw [show t = comap s.mkQ (map s.mkQ t) by simpa]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

Depends on / 依赖: closed_of_finiteDimensional, closed_of_finiteDimensional.preimage, continuous_quot_mk, preimage, s.mkQ
-/
theorem Submodule.isClosed_mono_of_finiteDimensional_quotient
    {s t : Submodule 𝕜 E} [FiniteDimensional 𝕜 (E ⧸ s)] (s_closed : IsClosed (s : Set E))
    (s_le_t : s <= t) :
    IsClosed (t : Set E) := by
  rw [show t = comap s.mkQ (map s.mkQ t) by simpa]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

/--
theorem `Submodule.isClosed_sup_finiteDimensional` / 定理 `Submodule.isClosed_sup_finiteDimensional`

English:
theorem Submodule.isClosed_sup_finiteDimensional
  proof: by
  rw [← comap_map_mkQ]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

中文:
定理 子模.isClosed_sup_finiteDimensional
  证明: by
  rw [← comap_map_mkQ]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

Depends on / 依赖: closed_of_finiteDimensional, closed_of_finiteDimensional.preimage, comap_map_mkQ, continuous_quot_mk, preimage, s.mkQ
-/
theorem Submodule.isClosed_sup_finiteDimensional
    (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [ht : FiniteDimensional 𝕜 t] :
    IsClosed ((s ⊔ t : Submodule 𝕜 E) : Set E) := by
  rw [← comap_map_mkQ]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

/--
theorem `LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient` / 定理 `LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient`

English:
theorem LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
  proof: by
  obtain ⟨t, s_compl_t⟩ := Submodule.exists_isCompl s
have : FiniteDimensional 𝕜 t := .of_fg Submodule.CoFG.fg_of_isCompl s_compl_t inferInstance
  rw [← Submodule.map_top]; rw [← s_compl_t.sup_eq_top]; rw [Submodule.map_sup]
  exact Submodule.isClosed_sup_finiteDimensional _ _ h

中文:
定理 线性映射.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
  证明: by
  obtain ⟨t, s_compl_t⟩ := Submodule.exists_isCompl s
have : FiniteDimensional 𝕜 t := .of_fg Submodule.CoFG.fg_of_isCompl s_compl_t inferInstance
  rw [← Submodule.map_top]; rw [← s_compl_t.sup_eq_top]; rw [Submodule.map_sup]
  exact Submodule.isClosed_sup_finiteDimensional _ _ h

Depends on / 依赖: FiniteDimensional, Submodule, Submodule.CoFG.fg_of_isCompl, Submodule.exists_isCompl, Submodule.isClosed_sup_finiteDimensional, Submodule.map_sup, Submodule.map_top, exists_isCompl, fg_of_isCompl, isClosed_sup_finiteDimensional, map_sup, map_top, of_fg, s_compl_t, s_compl_t.sup_eq_top, sup_eq_top
-/
theorem LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E ->ₗ[𝕜] F} {s : Submodule 𝕜 E}
    [s.CoFG] (h : IsClosed (s.map f : Set F)) :
    IsClosed (f.range : Set F) := by
  obtain ⟨t, s_compl_t⟩ := Submodule.exists_isCompl s
have : FiniteDimensional 𝕜 t := .of_fg Submodule.CoFG.fg_of_isCompl s_compl_t inferInstance
  rw [← Submodule.map_top]; rw [← s_compl_t.sup_eq_top]; rw [Submodule.map_sup]
  exact Submodule.isClosed_sup_finiteDimensional _ _ h

/--
theorem `LinearMap.isClosedEmbedding_of_injective` / 定理 `LinearMap.isClosedEmbedding_of_injective`

English:
theorem LinearMap.isClosedEmbedding_of_injective
  statement: [T2Space E] [FiniteDimensional 𝕜 E] [T2Space F]
  proof: let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      simpa [LinearMap.coe_range f] using (LinearMap.range f).closed_of_finiteDimensional }

中文:
定理 线性映射.isClosedEmbedding_of_injective
  结论: [T2空间 E] [有限维 𝕜 E] [T2空间 F]
  证明: let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      simpa [LinearMap.coe_range f] using (LinearMap.range f).closed_of_finiteDimensional }

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.comp, LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.coe_range, LinearMap.ker_eq_bot.mp, LinearMap.range, closed_of_finiteDimensional, coe_range, g.toContinuousLinearEquiv.toHomeomorph.isEmbedding, isClosed_range, isEmbedding, ker_eq_bot, ofInjective, subtypeVal, toContinuousLinearEquiv, toHomeomorph
-/
theorem LinearMap.isClosedEmbedding_of_injective [T2Space E] [FiniteDimensional 𝕜 E] [T2Space F]
    {f : E ->ₗ[𝕜] F} (hf : LinearMap.ker f = ⊥) : IsClosedEmbedding f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      simpa [LinearMap.coe_range f] using (LinearMap.range f).closed_of_finiteDimensional }

/--
theorem `isClosedEmbedding_smul_left` / 定理 `isClosedEmbedding_smul_left`

English:
theorem isClosedEmbedding_smul_left
  given: [T2Space E] {c : E} (hc : c != 0)
  proof: LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 hc)

中文:
定理 isClosedEmbedding_smul_left
  条件: [T2空间 E] {c : E} (hc : c != 0)
  证明: LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 hc)

Depends on / 依赖: LinearMap, LinearMap.isClosedEmbedding_of_injective, LinearMap.ker_toSpanSingleton, isClosedEmbedding_of_injective, ker_toSpanSingleton
-/
theorem isClosedEmbedding_smul_left [T2Space E] {c : E} (hc : c != 0) :
    IsClosedEmbedding fun x : 𝕜 => x • c :=
  LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 hc)

-- `smul` is a closed map in the first argument.
/--
theorem `isClosedMap_smul_left` / 定理 `isClosedMap_smul_left`

English:
theorem isClosedMap_smul_left
  given: [T2Space E] (c : E)
  statement: IsClosedMap fun x : 𝕜 => x • c
  proof: by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap

中文:
定理 isClosedMap_smul_left
  条件: [T2空间 E] (c : E)
  结论: 是闭映射 fun x : 𝕜 => x • c
  证明: by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap

Depends on / 依赖: isClosedEmbedding_smul_left, isClosedMap, isClosedMap_const, simp_rw, smul_zero
-/
theorem isClosedMap_smul_left [T2Space E] (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap

/--
theorem `ContinuousLinearMap.exists_rightInverse_of_surjective` / 定理 `ContinuousLinearMap.exists_rightInverse_of_surjective`

English:
theorem ContinuousLinearMap.exists_rightInverse_of_surjective
  statement: [T2Space F] [FiniteDimensional 𝕜 F]
  proof: let ⟨g, hg⟩ := (f : E ->ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩

@[deprecated (since := "2026-04-24")]
alias ContinuousLinearMap.exists_right_inverse_of_surjective :=
  ContinuousLinearMap.exists_rightInverse_of_surjective

中文:
定理 连续线性映射.存在_rightInverse_of_surjective
  结论: [T2空间 F] [有限维 𝕜 F]
  证明: let ⟨g, hg⟩ := (f : E ->ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩

@[deprecated (since := "2026-04-24")]
alias ContinuousLinearMap.exists_right_inverse_of_surjective :=
  ContinuousLinearMap.exists_rightInverse_of_surjective

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_inj, LinearMap, LinearMap.toContinuousLinearMap, coe_inj, exists_rightInverse_of_surjective, toContinuousLinearMap
-/
theorem ContinuousLinearMap.exists_rightInverse_of_surjective [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E ->L[𝕜] F) (hf : f.range = ⊤) : exists g : F ->L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E ->ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩

@[deprecated (since := "2026-04-24")]
alias ContinuousLinearMap.exists_right_inverse_of_surjective :=
  ContinuousLinearMap.exists_rightInverse_of_surjective

/--
theorem `ContinuousLinearMap.isQuotientMap_of_finiteDimensional` / 定理 `ContinuousLinearMap.isQuotientMap_of_finiteDimensional`

English:
theorem ContinuousLinearMap.isQuotientMap_of_finiteDimensional
  statement: [T2Space F] [FiniteDimensional 𝕜 F]
  proof: let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  .of_inverse g.continuous f.continuous (fun _ => congr($hg _))

中文:
定理 连续线性映射.isQuotientMap_of_finiteDimensional
  结论: [T2空间 F] [有限维 𝕜 F]
  证明: let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  .of_inverse g.continuous f.continuous (fun _ => congr($hg _))

Depends on / 依赖: continuous, exists_rightInverse_of_surjective, f.continuous, f.exists_rightInverse_of_surjective, g.continuous, of_inverse
-/
theorem ContinuousLinearMap.isQuotientMap_of_finiteDimensional [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E ->L[𝕜] F) (hf : f.range = ⊤) :
    IsQuotientMap f :=
  let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  .of_inverse g.continuous f.continuous (fun _ => congr($hg _))

/--
theorem `ContinuousLinearMap.isStrictMap_of_finiteDimensional` / 定理 `ContinuousLinearMap.isStrictMap_of_finiteDimensional`

English:
theorem ContinuousLinearMap.isStrictMap_of_finiteDimensional
  statement: [T2Space F] [FiniteDimensional 𝕜 F]
  proof: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact f.rangeRestrict.isQuotientMap_of_finiteDimensional (by simp)

中文:
定理 连续线性映射.isStrictMap_of_finiteDimensional
  结论: [T2空间 F] [有限维 𝕜 F]
  证明: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact f.rangeRestrict.isQuotientMap_of_finiteDimensional (by simp)

Depends on / 依赖: f.rangeRestrict.isQuotientMap_of_finiteDimensional, isQuotientMap_of_finiteDimensional, isStrictMap_iff_isQuotientMap_rangeFactorization, rangeRestrict
-/
theorem ContinuousLinearMap.isStrictMap_of_finiteDimensional [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E ->L[𝕜] F) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact f.rangeRestrict.isQuotientMap_of_finiteDimensional (by simp)

/--
theorem `LocallyCompactSpace.of_finiteDimensional_of_complete` / 定理 `LocallyCompactSpace.of_finiteDimensional_of_complete`

English:
theorem LocallyCompactSpace.of_finiteDimensional_of_complete
  statement: (K V : Type*)
  proof: -- Reduce to `SeparationQuotient V`, which is a `T2Space`.
  suffices LocallyCompactSpace (SeparationQuotient V) from
SeparationQuotient.isInducing_mk.locallyCompactSpace
      SeparationQuotient.range_mk (X := V) ▸ isClosed_univ.isLocallyClosed
  let ⟨_, ⟨b⟩⟩ := Basis.exists_basis K (SeparationQuot

中文:
定理 局部紧空间.of_finiteDimensional_of_complete
  结论: (K V : 类型)
  证明: -- Reduce to `SeparationQuotient V`, which is a `T2Space`.
  suffices LocallyCompactSpace (SeparationQuotient V) from
SeparationQuotient.isInducing_mk.locallyCompactSpace
      SeparationQuotient.range_mk (X := V) ▸ isClosed_univ.isLocallyClosed
  let ⟨_, ⟨b⟩⟩ := Basis.exists_basis K (SeparationQuot
-/
theorem LocallyCompactSpace.of_finiteDimensional_of_complete (K V : Type*)
    [NontriviallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [Module K V] [ContinuousSMul K V] [FiniteDimensional K V] :
    LocallyCompactSpace V :=
  -- Reduce to `SeparationQuotient V`, which is a `T2Space`.
  suffices LocallyCompactSpace (SeparationQuotient V) from
SeparationQuotient.isInducing_mk.locallyCompactSpace
      SeparationQuotient.range_mk (X := V) ▸ isClosed_univ.isLocallyClosed
  let ⟨_, ⟨b⟩⟩ := Basis.exists_basis K (SeparationQuotient V)
  have := FiniteDimensional.fintypeBasisIndex b
  b.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace

section Riesz

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E Eᵤ : Type*} [AddCommGroup E] [AddCommGroup Eᵤ] [Module 𝕜 E] [Module 𝕜 Eᵤ]
  [TopologicalSpace E] [UniformSpace Eᵤ] [T2Space E] [T2Space Eᵤ]
  [IsTopologicalAddGroup E] [IsUniformAddGroup Eᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 Eᵤ]

open scoped Pointwise in
/--
theorem `FiniteDimensional.of_totallyBounded_nhds_zero` / 定理 `FiniteDimensional.of_totallyBounded_nhds_zero`

English:
theorem FiniteDimensional.of_totallyBounded_nhds_zero
  statement: {U : Set Eᵤ} (hU_nhds : U in 𝓝 (0 : Eᵤ))
  proof: by
  obtain ⟨c, hc0, hc1⟩ : exists c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < 1 := NormedField.exists_norm_lt 𝕜 zero_lt_one
  have hc_ne : c != 0 := norm_pos_iff.mp hc0
  obtain ⟨F, hF_finite, hF_cover⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hU_tb
    (c • U) ((set_smul_mem_nhds_zero_iff hc_ne).mpr hU_

中文:
定理 有限维.of_totallyBounded_nhds_zero
  结论: {U : 集合 Eᵤ} (hU_nhds : U in 𝓝 (0 : Eᵤ))
  证明: by
  obtain ⟨c, hc0, hc1⟩ : exists c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < 1 := NormedField.exists_norm_lt 𝕜 zero_lt_one
  have hc_ne : c != 0 := norm_pos_iff.mp hc0
  obtain ⟨F, hF_finite, hF_cover⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hU_tb
    (c • U) ((set_smul_mem_nhds_zero_iff hc_ne).mpr hU_

Depends on / 依赖: Finite, Finite.span_of_finite, FiniteDimensional, NormedField, NormedField.exists_norm_lt, Set.mem_iU, Submodule, Submodule.span, exists_norm_lt, hF_cover, hF_finite, hU_nhds, hU_tb, h_cover, hc_ne, mem_iU, norm_pos_iff, norm_pos_iff.mp, set_smul_mem_nhds_zero_iff, span_of_finite
-/
theorem FiniteDimensional.of_totallyBounded_nhds_zero {U : Set Eᵤ} (hU_nhds : U in 𝓝 (0 : Eᵤ))
    (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  obtain ⟨c, hc0, hc1⟩ : exists c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < 1 := NormedField.exists_norm_lt 𝕜 zero_lt_one
  have hc_ne : c != 0 := norm_pos_iff.mp hc0
  obtain ⟨F, hF_finite, hF_cover⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hU_tb
    (c • U) ((set_smul_mem_nhds_zero_iff hc_ne).mpr hU_nhds)
  let M : Submodule 𝕜 Eᵤ := Submodule.span 𝕜 F
  let : FiniteDimensional 𝕜 M := Finite.span_of_finite 𝕜 hF_finite
  have h_cover : U subseteq M + c • U := fun x hx => by
obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hF_cover hx
    exact ⟨f, Submodule.subset_span hf, y, hy, rfl⟩
  have h_ind (n : Nat) : U subseteq M + c ^ n • U := by
    induction n with
    | zero => simpa using! fun x hx => ⟨0, M.zero_mem, x, hx, zero_add x⟩
    | succ n ih =>
      calc
        U subseteq M + c ^ n • U := ih
        _ subseteq M + c ^ n • (M + c • U) := by gcongr
        _ subseteq M + c ^ (n + 1) • U := by
          rw [smul_add]; rw [smul_smul]; rw [pow_succ]; rw [← add_assoc]
          congr!
          lift c to 𝕜ˣ using isUnit_iff_ne_zero.mpr hc_ne
          simp [← Units.val_pow_eq_pow_val, ← Units.smul_def]
  have h_small : Tendsto (fun n => c ^ n • U) atTop (𝓝 0).smallSets :=
    (TotallyBounded.isVonNBounded 𝕜 hU_tb).tendsto_smallSets_nhds.comp
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)
  have hU_sub_M : U subseteq M := by
    intro x hx
    choose m hm u hu h_eq using fun n => h_ind n hx
    have hu_tendsto : Tendsto u atTop (𝓝 0) := by
      intro W hW
      exact (tendsto_smallSets_iff.mp h_small W hW).mono fun n hn => hn (hu n)
    have hm_tendsto : Tendsto m atTop (𝓝 x) := by
      simpa [show m = fun n => x - u n by grind] using! tendsto_const_nhds.sub hu_tendsto
    exact M.closed_of_finiteDimensional.mem_of_tendsto hm_tendsto (Eventually.of_forall hm)
.submodule_eq_top .mono hU_sub_M have hM_top : M = ⊤ := absorbent_nhds_zero (𝕜 := 𝕜) hU_nhds
  exact FiniteDimensional.of_surjective M.subtype fun x => ⟨⟨x, by simp [hM_top]⟩, rfl⟩

open scoped Pointwise in
/--
theorem `FiniteDimensional.of_totallyBounded_nhds` / 定理 `FiniteDimensional.of_totallyBounded_nhds`

English:
theorem FiniteDimensional.of_totallyBounded_nhds
  statement: {x : Eᵤ} {U : Set Eᵤ} (hU_nhds : U in 𝓝 x)
  proof: by
  replace hU_nhds : x +ᵥ (-x) +ᵥ U in 𝓝 x := by simpa
  rw [vadd_mem_nhds_self] at hU_nhds
  refine .of_totallyBounded_nhds_zero _ hU_nhds ?_
  have : -x +ᵥ U = (· - x) '' U := by simp [← Set.image_vadd, neg_add_eq_sub]
  exact this ▸ hU_tb.image (uniformContinuous_id.sub uniformContinuous_const)

中文:
定理 有限维.of_totallyBounded_nhds
  结论: {x : Eᵤ} {U : 集合 Eᵤ} (hU_nhds : U in 𝓝 x)
  证明: by
  replace hU_nhds : x +ᵥ (-x) +ᵥ U in 𝓝 x := by simpa
  rw [vadd_mem_nhds_self] at hU_nhds
  refine .of_totallyBounded_nhds_zero _ hU_nhds ?_
  have : -x +ᵥ U = (· - x) '' U := by simp [← Set.image_vadd, neg_add_eq_sub]
  exact this ▸ hU_tb.image (uniformContinuous_id.sub uniformContinuous_const)

Depends on / 依赖: Set.image_vadd, hU_nhds, hU_tb, hU_tb.image, image_vadd, neg_add_eq_sub, of_totallyBounded_nhds_zero, replace, uniformContinuous_const, uniformContinuous_id, uniformContinuous_id.sub, vadd_mem_nhds_self
-/
theorem FiniteDimensional.of_totallyBounded_nhds {x : Eᵤ} {U : Set Eᵤ} (hU_nhds : U in 𝓝 x)
    (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  replace hU_nhds : x +ᵥ (-x) +ᵥ U in 𝓝 x := by simpa
  rw [vadd_mem_nhds_self] at hU_nhds
  refine .of_totallyBounded_nhds_zero _ hU_nhds ?_
  have : -x +ᵥ U = (· - x) '' U := by simp [← Set.image_vadd, neg_add_eq_sub]
  exact this ▸ hU_tb.image (uniformContinuous_id.sub uniformContinuous_const)

/--
theorem `FiniteDimensional.of_exists_totallyBounded_nhds` / 定理 `FiniteDimensional.of_exists_totallyBounded_nhds`

English:
theorem FiniteDimensional.of_exists_totallyBounded_nhds
  proof: by
  rcases h with ⟨x, U, hU_nhds, hU_tb⟩
  exact FiniteDimensional.of_totallyBounded_nhds (𝕜 := 𝕜) hU_nhds hU_tb

中文:
定理 有限维.of_存在_totallyBounded_nhds
  证明: by
  rcases h with ⟨x, U, hU_nhds, hU_tb⟩
  exact FiniteDimensional.of_totallyBounded_nhds (𝕜 := 𝕜) hU_nhds hU_tb

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_totallyBounded_nhds, hU_nhds, hU_tb, of_totallyBounded_nhds
-/
theorem FiniteDimensional.of_exists_totallyBounded_nhds
    (h : exists x : Eᵤ, exists U in 𝓝 x, TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  rcases h with ⟨x, U, hU_nhds, hU_tb⟩
  exact FiniteDimensional.of_totallyBounded_nhds (𝕜 := 𝕜) hU_nhds hU_tb

/--
theorem `FiniteDimensional.of_locallyCompactSpace` / 定理 `FiniteDimensional.of_locallyCompactSpace`

English:
theorem FiniteDimensional.of_locallyCompactSpace
  given: [WeaklyLocallyCompactSpace E]
  proof: let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let ⟨_, hU_compact, hU_nhds⟩ := exists_compact_mem_nhds (0 : E)
  .of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_compact.totallyBounded

中文:
定理 有限维.of_locallyCompactSpace
  条件: [WeaklyLocallyCompact空间 E]
  证明: let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let ⟨_, hU_compact, hU_nhds⟩ := exists_compact_mem_nhds (0 : E)
  .of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_compact.totallyBounded

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, UniformSpace, exists_compact_mem_nhds, hU_compact, hU_compact.totallyBounded, hU_nhds, isUniformAddGroup_of_addCommGroup, of_totallyBounded_nhds_zero, rightUniformSpace, totallyBounded
-/
theorem FiniteDimensional.of_locallyCompactSpace [WeaklyLocallyCompactSpace E] :
    FiniteDimensional 𝕜 E :=
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let ⟨_, hU_compact, hU_nhds⟩ := exists_compact_mem_nhds (0 : E)
  .of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_compact.totallyBounded

/--
theorem `HasCompactSupport.eq_zero_or_finiteDimensional` / 定理 `HasCompactSupport.eq_zero_or_finiteDimensional`

English:
theorem HasCompactSupport.eq_zero_or_finiteDimensional
  statement: {X : Type*} [TopologicalSpace X] [Zero X]
  proof: (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h =>
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

中文:
定理 HasCompactSupport.eq_zero_or_finiteDimensional
  结论: {X : 类型} [拓扑空间 X] [零 X]
  证明: (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h =>
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

Depends on / 依赖: HasCompactSupport, HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup, LocallyCompactSpace, eq_zero_or_locallyCompactSpace_of_addGroup, imp_right, of_locallyCompactSpace
-/
theorem HasCompactSupport.eq_zero_or_finiteDimensional {X : Type*} [TopologicalSpace X] [Zero X]
    [T1Space X] {f : E -> X} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ FiniteDimensional 𝕜 E :=
  (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h =>
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

/--
theorem `HasCompactMulSupport.eq_one_or_finiteDimensional` / 定理 `HasCompactMulSupport.eq_one_or_finiteDimensional`

English:
theorem HasCompactMulSupport.eq_one_or_finiteDimensional
  statement: {X : Type*} [TopologicalSpace X] [One X]
  proof: have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional 𝕜 (X := Additive X) hf h'f

中文:
定理 HasCompactMulSupport.eq_one_or_finiteDimensional
  结论: {X : 类型} [拓扑空间 X] [幺 X]
  证明: have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional 𝕜 (X := Additive X) hf h'f

Depends on / 依赖: Additive, HasCompactSupport, HasCompactSupport.eq_zero_or_finiteDimensional, T1Space, eq_zero_or_finiteDimensional
-/
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*} [TopologicalSpace X] [One X]
    [T1Space X] {f : E -> X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E :=
  have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional 𝕜 (X := Additive X) hf h'f

end Riesz

section Compl

open Submodule

/--
theorem `Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient` / 定理 `Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`

English:
theorem Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient
  statement: {p q : Submodule 𝕜 E}
  proof: by
  let φ : E ⧸ p ->L[𝕜] q := (p.quotientEquivOfIsCompl q h).toLinearMap.toContinuousLinearMap
  have := (φ ∘L p.mkQL).isTopCompl_of_proj fun x => by simp [φ]
  simpa [φ] using this.symm

中文:
定理 子模.是补集.isTopCompl_of_finiteDimensional_quotient
  结论: {p q : 子模 𝕜 E}
  证明: by
  let φ : E ⧸ p ->L[𝕜] q := (p.quotientEquivOfIsCompl q h).toLinearMap.toContinuousLinearMap
  have := (φ ∘L p.mkQL).isTopCompl_of_proj fun x => by simp [φ]
  simpa [φ] using this.symm

Depends on / 依赖: isTopCompl_of_proj, p.mkQL, p.quotientEquivOfIsCompl, quotientEquivOfIsCompl, this.symm, toContinuousLinearMap, toLinearMap, toLinearMap.toContinuousLinearMap
-/
theorem Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient {p q : Submodule 𝕜 E}
    (h : IsCompl p q) (hp : IsClosed (p : Set E)) [FiniteDimensional 𝕜 (E ⧸ p)] :
    IsTopCompl p q := by
  let φ : E ⧸ p ->L[𝕜] q := (p.quotientEquivOfIsCompl q h).toLinearMap.toContinuousLinearMap
  have := (φ ∘L p.mkQL).isTopCompl_of_proj fun x => by simp [φ]
  simpa [φ] using this.symm

/--
theorem `Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional` / 定理 `Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional`

English:
theorem Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional
  statement: {p q : Submodule 𝕜 E}
  proof: by
  suffices FiniteDimensional 𝕜 (E ⧸ p) from h.isTopCompl_of_finiteDimensional_quotient hp
  exact (p.quotientEquivOfIsCompl q h).symm.finiteDimensional

中文:
定理 子模.是补集.isTopCompl_of_isClosed_of_finiteDimensional
  结论: {p q : 子模 𝕜 E}
  证明: by
  suffices FiniteDimensional 𝕜 (E ⧸ p) from h.isTopCompl_of_finiteDimensional_quotient hp
  exact (p.quotientEquivOfIsCompl q h).symm.finiteDimensional

Depends on / 依赖: FiniteDimensional, finiteDimensional, h.isTopCompl_of_finiteDimensional_quotient, isTopCompl_of_finiteDimensional_quotient, p.quotientEquivOfIsCompl, quotientEquivOfIsCompl, symm.finiteDimensional
-/
theorem Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional {p q : Submodule 𝕜 E}
    (h : IsCompl p q) (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 𝕜 q] :
    IsTopCompl p q := by
  suffices FiniteDimensional 𝕜 (E ⧸ p) from h.isTopCompl_of_finiteDimensional_quotient hp
  exact (p.quotientEquivOfIsCompl q h).symm.finiteDimensional

/--
theorem `Submodule.ClosedComplemented.of_finiteDimensional_quotient` / 定理 `Submodule.ClosedComplemented.of_finiteDimensional_quotient`

English:
theorem Submodule.ClosedComplemented.of_finiteDimensional_quotient
  statement: {p : Submodule 𝕜 E}
  proof: by
  obtain ⟨q, hq⟩ : exists q, IsCompl p q := p.exists_isCompl
.closedComplemented exact hq.isTopCompl_of_finiteDimensional_quotient hp

@[deprecated (since := "2026-05-09")]
alias Submodule.ClosedComplemented.of_quotient_finiteDimensional :=
  Submodule.ClosedComplemented.of_finiteDimensional_quot

中文:
定理 子模.ClosedComplemented.of_finiteDimensional_quotient
  结论: {p : 子模 𝕜 E}
  证明: by
  obtain ⟨q, hq⟩ : exists q, IsCompl p q := p.exists_isCompl
.closedComplemented exact hq.isTopCompl_of_finiteDimensional_quotient hp

@[deprecated (since := "2026-05-09")]
alias Submodule.ClosedComplemented.of_quotient_finiteDimensional :=
  Submodule.ClosedComplemented.of_finiteDimensional_quot

Depends on / 依赖: IsCompl, closedComplemented, exists_isCompl, hq.isTopCompl_of_finiteDimensional_quotient, isTopCompl_of_finiteDimensional_quotient, p.exists_isCompl
-/
theorem Submodule.ClosedComplemented.of_finiteDimensional_quotient {p : Submodule 𝕜 E}
    (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 𝕜 (E ⧸ p)] : p.ClosedComplemented := by
  obtain ⟨q, hq⟩ : exists q, IsCompl p q := p.exists_isCompl
.closedComplemented exact hq.isTopCompl_of_finiteDimensional_quotient hp

@[deprecated (since := "2026-05-09")]
alias Submodule.ClosedComplemented.of_quotient_finiteDimensional :=
  Submodule.ClosedComplemented.of_finiteDimensional_quotient

/--
theorem `Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient` / 定理 `Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient`

English:
theorem Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient
  proof: by
  obtain ⟨C, B_le_C, C_compl_A⟩ := hAB.symm.exists_isCompl
  have C_cofg : FiniteDimensional 𝕜 (E ⧸ C) := CoFG.of_le B_le_C B_cofg
  have hC : IsClosed (C : Set E) := isClosed_mono_of_finiteDimensional_quotient hB B_le_C
.symm.closedComplemented exact C_compl_A.isTopCompl_of_finiteDimensional_quo

中文:
定理 子模.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient
  证明: by
  obtain ⟨C, B_le_C, C_compl_A⟩ := hAB.symm.exists_isCompl
  have C_cofg : FiniteDimensional 𝕜 (E ⧸ C) := CoFG.of_le B_le_C B_cofg
  have hC : IsClosed (C : Set E) := isClosed_mono_of_finiteDimensional_quotient hB B_le_C
.symm.closedComplemented exact C_compl_A.isTopCompl_of_finiteDimensional_quo

Depends on / 依赖: B_cofg, B_le_C, C_cofg, C_compl_A, C_compl_A.isTopCompl_of_finiteDimensional_quotient, CoFG.of_le, FiniteDimensional, IsClosed, closedComplemented, exists_isCompl, hAB.symm.exists_isCompl, isClosed_mono_of_finiteDimensional_quotient, isTopCompl_of_finiteDimensional_quotient, of_le, symm.closedComplemented
-/
theorem Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient
    {A B : Submodule 𝕜 E} [B_cofg : FiniteDimensional 𝕜 (E ⧸ B)] (hB : IsClosed (B : Set E))
    (hAB : Disjoint A B) : A.ClosedComplemented := by
  obtain ⟨C, B_le_C, C_compl_A⟩ := hAB.symm.exists_isCompl
  have C_cofg : FiniteDimensional 𝕜 (E ⧸ C) := CoFG.of_le B_le_C B_cofg
  have hC : IsClosed (C : Set E) := isClosed_mono_of_finiteDimensional_quotient hB B_le_C
.symm.closedComplemented exact C_compl_A.isTopCompl_of_finiteDimensional_quotient hC

/--
lemma `Submodule.ClosedComplemented.of_finiteDimensional_of_le` / 引理 `Submodule.ClosedComplemented.of_finiteDimensional_of_le`

English:
lemma Submodule.ClosedComplemented.of_finiteDimensional_of_le
  proof: by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨C, hBC⟩ := B.exists_isCompl
  refine ⟨((projectionOnto B C hBC).domRestrict A).toContinuousLinearMap ∘SL p, fun x => ?_⟩
  simp [hp ⟨x, hB x.2⟩]

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in

中文:
引理 子模.ClosedComplemented.of_finiteDimensional_of_le
  证明: by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨C, hBC⟩ := B.exists_isCompl
  refine ⟨((projectionOnto B C hBC).domRestrict A).toContinuousLinearMap ∘SL p, fun x => ?_⟩
  simp [hp ⟨x, hB x.2⟩]

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in

Depends on / 依赖: B.exists_isCompl, domRestrict, exists_isCompl, projectionOnto, toContinuousLinearMap
-/
lemma Submodule.ClosedComplemented.of_finiteDimensional_of_le
    {A B : Submodule 𝕜 E} [FiniteDimensional 𝕜 A] (hA : A.ClosedComplemented) [T2Space A]
    (hB : B <= A) : B.ClosedComplemented := by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨C, hBC⟩ := B.exists_isCompl
  refine ⟨((projectionOnto B C hBC).domRestrict A).toContinuousLinearMap ∘SL p, fun x => ?_⟩
  simp [hp ⟨x, hB x.2⟩]

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/--
theorem `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range` / 定理 `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`

English:
theorem ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range
  statement: [T2Space F]
  proof: by
  suffices FiniteDimensional 𝕜 (E ⧸ f.ker) from .of_finiteDimensional_quotient f.isClosed_ker
  exact f.toLinearMap.quotKerEquivRange.symm.finiteDimensional

中文:
定理 连续线性映射.ker_closedComplemented_of_finiteDimensional_range
  结论: [T2空间 F]
  证明: by
  suffices FiniteDimensional 𝕜 (E ⧸ f.ker) from .of_finiteDimensional_quotient f.isClosed_ker
  exact f.toLinearMap.quotKerEquivRange.symm.finiteDimensional

Depends on / 依赖: FiniteDimensional, f.isClosed_ker, f.ker, f.toLinearMap.quotKerEquivRange.symm.finiteDimensional, finiteDimensional, isClosed_ker, of_finiteDimensional_quotient, quotKerEquivRange, toLinearMap
-/
theorem ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range [T2Space F]
    (f : E ->L[𝕜] F) [FiniteDimensional 𝕜 f.range] : f.ker.ClosedComplemented := by
  suffices FiniteDimensional 𝕜 (E ⧸ f.ker) from .of_finiteDimensional_quotient f.isClosed_ker
  exact f.toLinearMap.quotKerEquivRange.symm.finiteDimensional

end Compl
