/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`ContinuousMap.equivBoundedOfCompact` to move functions back and forth.
-/

@[expose] public section

noncomputable section

open NNReal BoundedContinuousFunction Set Metric

namespace ContinuousMap

variable {α β E : Type*}
variable [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β] [SeminormedAddCommGroup E]

section

variable (α β)

/-- When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps -fullyApplied]
/--
Definition of `equivBoundedOfCompact` / `equivBoundedOfCompact` 的定义

English:
definition equivBoundedOfCompact
  signature: : C(α, β) ≃ (α ->ᵇ β)
  body: ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

中文:
定义 equivBoundedOfCompact
  签名: : C(α, β) ≃ (α ->ᵇ β)
  定义体: ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.toContinuousMap, mkOfCompact, toContinuousMap
-/
def equivBoundedOfCompact : C(α, β) ≃ (α ->ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

/--
theorem `isUniformInducing_equivBoundedOfCompact` / 定理 `isUniformInducing_equivBoundedOfCompact`

English:
theorem isUniformInducing_equivBoundedOfCompact
  statement: IsUniformInducing (equivBoundedOfCompact α β)
  proof: IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | forall x, (p.1 x, p.2 x) in b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
   

中文:
定理 isUniformInducing_equivBoundedOfCompact
  结论: IsUniformInducing (equivBoundedOfCompact α β)
  证明: IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | forall x, (p.1 x, p.2 x) in b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
   

Depends on / 依赖: IsUniformInducing, IsUniformInducing.mk, Set.univ, dist_le, hasBasis_compactConvergenceUniformity, hasBasis_compactConvergenceUniformity.mem_iff, isCompact_univ, mem_iff, mem_univ, uniformity_basis_dist_le, uniformity_basis_dist_le.mem_iff
-/
theorem isUniformInducing_equivBoundedOfCompact : IsUniformInducing (equivBoundedOfCompact α β) :=
  IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | forall x, (p.1 x, p.2 x) in b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
            fun f g h => hs fun x _ => h x⟩,
          fun ⟨_, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.univ, { p | dist p.1 p.2 <= ε }⟩, ⟨isCompact_univ, ⟨ε, hε, fun _ h => h⟩⟩,
            fun ⟨f, g⟩ h => hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)

/--
theorem `isUniformEmbedding_equivBoundedOfCompact` / 定理 `isUniformEmbedding_equivBoundedOfCompact`

English:
theorem isUniformEmbedding_equivBoundedOfCompact
  statement: IsUniformEmbedding (equivBoundedOfCompact α β)
  proof: { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

#adaptation_note

中文:
定理 isUniformEmbedding_equivBoundedOfCompact
  结论: IsUniformEmbedding (equivBoundedOfCompact α β)
  证明: { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

#adaptation_note

Depends on / 依赖: equivBoundedOfCompact, injective, isUniformInducing_equivBoundedOfCompact
-/
theorem isUniformEmbedding_equivBoundedOfCompact : IsUniformEmbedding (equivBoundedOfCompact α β) :=
  { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps! -fullyApplied apply symm_apply]
/--
Definition of `addEquivBoundedOfCompact` / `addEquivBoundedOfCompact` 的定义

English:
definition addEquivBoundedOfCompact
  signature: [AddMonoid β] [LipschitzAdd β]
  body: ({ toContinuousMapAddMonoidHom α β, (equivBoundedOfCompact α β).symm with } :
    (α ->ᵇ β) ≃+ C(α, β)).symm

中文:
定义 addEquivBoundedOfCompact
  签名: [AddMonoid β] [LipschitzAdd β]
  定义体: ({ toContinuousMapAddMonoidHom α β, (equivBoundedOfCompact α β).symm with } :
    (α ->ᵇ β) ≃+ C(α, β)).symm

Depends on / 依赖: equivBoundedOfCompact, toContinuousMapAddMonoidHom
-/
def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α ->ᵇ β) :=
  ({ toContinuousMapAddMonoidHom α β, (equivBoundedOfCompact α β).symm with } :
    (α ->ᵇ β) ≃+ C(α, β)).symm

/--
Instance `instPseudoMetricSpace` / 实例 `instPseudoMetricSpace`

English:
instance instPseudoMetricSpace
  signature: : PseudoMetricSpace C(α, β)
  body: (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _

中文:
实例 instPseudoMetricSpace
  签名: : PseudoMetricSpace C(α, β)
  定义体: (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _

Depends on / 依赖: comapPseudoMetricSpace, isUniformEmbedding_equivBoundedOfCompact
-/
instance instPseudoMetricSpace : PseudoMetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: {β : Type*} [MetricSpace β]
  body: (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _

中文:
实例 instMetricSpace
  签名: {β : 类型} [MetricSpace β]
  定义体: (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _

Depends on / 依赖: comapMetricSpace, isUniformEmbedding_equivBoundedOfCompact
-/
instance instMetricSpace {β : Type*} [MetricSpace β] :
    MetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _


/-- When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
/--
Definition of `isometryEquivBoundedOfCompact` / `isometryEquivBoundedOfCompact` 的定义

English:
definition isometryEquivBoundedOfCompact
  signature: : C(α, β) ≃ᵢ (α ->ᵇ β) where
  body: rfl
  toEquiv := equivBoundedOfCompact α β

中文:
定义 isometryEquivBoundedOfCompact
  签名: : C(α, β) ≃ᵢ (α ->ᵇ β) where
  定义体: rfl
  toEquiv := equivBoundedOfCompact α β
-/
def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α ->ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β

end

@[simp]
/--
theorem `_root_.BoundedContinuousFunction.dist_mkOfCompact` / 定理 `_root_.BoundedContinuousFunction.dist_mkOfCompact`

English:
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact
  given: (f g : C(α, β))
  proof: rfl

@[simp]

中文:
定理 _root_.BoundedContinuousFunction.dist_mkOfCompact
  条件: (f g : C(α, β))
  证明: rfl

@[simp]
-/
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl

@[simp]
/--
theorem `_root_.BoundedContinuousFunction.dist_toContinuousMap` / 定理 `_root_.BoundedContinuousFunction.dist_toContinuousMap`

English:
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap
  given: (f g : α ->ᵇ β)
  proof: rfl

中文:
定理 _root_.BoundedContinuousFunction.dist_toContinuousMap
  条件: (f g : α ->ᵇ β)
  证明: rfl
-/
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap (f g : α ->ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl

open BoundedContinuousFunction

section

variable {f g : C(α, β)} {C : Real}

/--
theorem `dist_apply_le_dist` / 定理 `dist_apply_le_dist`

English:
theorem dist_apply_le_dist
  given: (x : α)
  statement: dist (f x) (g x) <= dist f g
  proof: by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

中文:
定理 dist_apply_le_dist
  条件: (x : α)
  结论: dist (f x) (g x) <= dist f g
  证明: by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

Depends on / 依赖: dist_coe_le_dist, dist_mkOfCompact, mkOfCompact_apply
-/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) <= dist f g := by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

/--
theorem `dist_le` / 定理 `dist_le`

English:
theorem dist_le
  given: (C0 : (0 : Real) <= C)
  statement: dist f g <= C ↔ forall x : α, dist (f x) (g x) <= C
  proof: by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]

中文:
定理 dist_le
  条件: (C0 : (0 : 实数) <= C)
  结论: dist f g <= C ↔ 对任意 x : α, dist (f x) (g x) <= C
  证明: by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.dist_le, dist_le, dist_mkOfCompact, mkOfCompact_apply
-/
theorem dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ forall x : α, dist (f x) (g x) <= C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]

/--
theorem `dist_le_iff_of_nonempty` / 定理 `dist_le_iff_of_nonempty`

English:
theorem dist_le_iff_of_nonempty
  given: [Nonempty α]
  statement: dist f g <= C ↔ forall x, dist (f x) (g x) <= C
  proof: by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]

中文:
定理 dist_le_iff_of_nonempty
  条件: [Nonempty α]
  结论: dist f g <= C ↔ 对任意 x, dist (f x) (g x) <= C
  证明: by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.dist_le_iff_of_nonempty, dist_le_iff_of_nonempty, dist_mkOfCompact, mkOfCompact_apply
-/
theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x) (g x) <= C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]

/--
theorem `dist_lt_iff_of_nonempty` / 定理 `dist_lt_iff_of_nonempty`

English:
theorem dist_lt_iff_of_nonempty
  given: [Nonempty α]
  statement: dist f g < C ↔ forall x : α, dist (f x) (g x) < C
  proof: by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]

中文:
定理 dist_lt_iff_of_nonempty
  条件: [Nonempty α]
  结论: dist f g < C ↔ 对任意 x : α, dist (f x) (g x) < C
  证明: by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]

Depends on / 依赖: dist_lt_iff_of_nonempty_compact, dist_mkOfCompact, mkOfCompact_apply
-/
theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ forall x : α, dist (f x) (g x) < C := by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]

/--
theorem `dist_lt_of_nonempty` / 定理 `dist_lt_of_nonempty`

English:
theorem dist_lt_of_nonempty
  given: [Nonempty α] (w : forall x : α, dist (f x) (g x) < C)
  statement: dist f g < C
  proof: dist_lt_iff_of_nonempty.2 w

中文:
定理 dist_lt_of_nonempty
  条件: [Nonempty α] (w : 对任意 x : α, dist (f x) (g x) < C)
  结论: dist f g < C
  证明: dist_lt_iff_of_nonempty.2 w

Depends on / 依赖: dist_lt_iff_of_nonempty
-/
theorem dist_lt_of_nonempty [Nonempty α] (w : forall x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w

/--
theorem `dist_lt_iff` / 定理 `dist_lt_iff`

English:
theorem dist_lt_iff
  given: (C0 : (0 : Real) < C)
  statement: dist f g < C ↔ forall x : α, dist (f x) (g x) < C
  proof: by
  rw [← dist_mkOfCompact]; rw [dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]

中文:
定理 dist_lt_iff
  条件: (C0 : (0 : 实数) < C)
  结论: dist f g < C ↔ 对任意 x : α, dist (f x) (g x) < C
  证明: by
  rw [← dist_mkOfCompact]; rw [dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]

Depends on / 依赖: dist_lt_iff_of_compact, dist_mkOfCompact, mkOfCompact_apply
-/
theorem dist_lt_iff (C0 : (0 : Real) < C) : dist f g < C ↔ forall x : α, dist (f x) (g x) < C := by
  rw [← dist_mkOfCompact]; rw [dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]

/--
theorem `dist_eq_iSup` / 定理 `dist_eq_iSup`

English:
theorem dist_eq_iSup
  statement: dist f g = ⨆ x, dist (f x) (g x)
  proof: by
  simp [← isometryEquivBoundedOfCompact α β |>.dist_eq f g,
    BoundedContinuousFunction.dist_eq_iSup]

中文:
定理 dist_eq_iSup
  结论: dist f g = ⨆ x, dist (f x) (g x)
  证明: by
  simp [← isometryEquivBoundedOfCompact α β |>.dist_eq f g,
    BoundedContinuousFunction.dist_eq_iSup]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.dist_eq_iSup, dist_eq, dist_eq_iSup, isometryEquivBoundedOfCompact
-/
theorem dist_eq_iSup : dist f g = ⨆ x, dist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.dist_eq f g,
    BoundedContinuousFunction.dist_eq_iSup]

/--
theorem `nndist_eq_iSup` / 定理 `nndist_eq_iSup`

English:
theorem nndist_eq_iSup
  statement: nndist f g = ⨆ x, nndist (f x) (g x)
  proof: by
  simp [← isometryEquivBoundedOfCompact α β |>.nndist_eq f g,
    BoundedContinuousFunction.nndist_eq_iSup]

中文:
定理 nndist_eq_iSup
  结论: nndist f g = ⨆ x, nndist (f x) (g x)
  证明: by
  simp [← isometryEquivBoundedOfCompact α β |>.nndist_eq f g,
    BoundedContinuousFunction.nndist_eq_iSup]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.nndist_eq_iSup, isometryEquivBoundedOfCompact, nndist_eq, nndist_eq_iSup
-/
theorem nndist_eq_iSup : nndist f g = ⨆ x, nndist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.nndist_eq f g,
    BoundedContinuousFunction.nndist_eq_iSup]

/--
theorem `edist_eq_iSup` / 定理 `edist_eq_iSup`

English:
theorem edist_eq_iSup
  statement: edist f g = ⨆ (x : α), edist (f x) (g x)
  proof: by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]

中文:
定理 edist_eq_iSup
  结论: edist f g = ⨆ (x : α), edist (f x) (g x)
  证明: by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.edist_eq_iSup, edist_eq, edist_eq_iSup, isometryEquivBoundedOfCompact
-/
theorem edist_eq_iSup : edist f g = ⨆ (x : α), edist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]

instance {R} [Zero R] [Zero β] [PseudoMetricSpace R] [SMul R β] [IsBoundedSMul R β] :
    IsBoundedSMul R C(α, β) where
  dist_smul_pair' r f g := by
    simpa only [← dist_mkOfCompact] using! dist_smul_pair r (mkOfCompact f) (mkOfCompact g)
  dist_pair_smul' r₁ r₂ f := by
    simpa only [← dist_mkOfCompact] using! dist_pair_smul r₁ r₂ (mkOfCompact f)

end

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm C(α, E)
  body: dist x 0

@[simp]

中文:
实例 :
  签名: Norm C(α, E)
  定义体: dist x 0

@[simp]
-/
instance : Norm C(α, E) where norm x := dist x 0

@[simp]
/--
theorem `_root_.BoundedContinuousFunction.norm_mkOfCompact` / 定理 `_root_.BoundedContinuousFunction.norm_mkOfCompact`

English:
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact
  given: (f : C(α, E))
  statement: ‖mkOfCompact f‖ = ‖f‖
  proof: rfl

@[simp]

中文:
定理 _root_.BoundedContinuousFunction.norm_mkOfCompact
  条件: (f : C(α, E))
  结论: ‖mkOfCompact f‖ = ‖f‖
  证明: rfl

@[simp]
-/
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact (f : C(α, E)) : ‖mkOfCompact f‖ = ‖f‖ :=
  rfl

@[simp]
/--
theorem `_root_.BoundedContinuousFunction.norm_toContinuousMap_eq` / 定理 `_root_.BoundedContinuousFunction.norm_toContinuousMap_eq`

English:
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq
  given: (f : α ->ᵇ E)
  proof: rfl

中文:
定理 _root_.BoundedContinuousFunction.norm_toContinuousMap_eq
  条件: (f : α ->ᵇ E)
  证明: rfl
-/
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq (f : α ->ᵇ E) :
    ‖f.toContinuousMap‖ = ‖f‖ :=
  rfl

open BoundedContinuousFunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeminormedAddCommGroup C(α, E)
  body: ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm_neg_add,
    mkOfCompact_add, mkOfCompact_neg]
  dist := dist
  norm := norm

中文:
实例 :
  签名: SeminormedAddCommGroup C(α, E)
  定义体: ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm_neg_add,
    mkOfCompact_add, mkOfCompact_neg]
  dist := dist
  norm := norm

Depends on / 依赖: ContinuousMap, ContinuousMap.instPseudoMetricSpace, instPseudoMetricSpace
-/
instance : SeminormedAddCommGroup C(α, E) where
  __ := ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm_neg_add,
    mkOfCompact_add, mkOfCompact_neg]
  dist := dist
  norm := norm

instance {E : Type*} [NormedAddCommGroup E] : NormedAddCommGroup C(α, E) where
  __ : SeminormedAddCommGroup C(α, E) := inferInstance
  __ : MetricSpace C(α, E) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] {E
  body: by
  simpa [nontrivialTopology_iff_exists_norm_ne_zero] using exists_ne (0 : C(α, E))

中文:
实例 [Nonempty
  签名: α] {E
  定义体: by
  simpa [nontrivialTopology_iff_exists_norm_ne_zero] using exists_ne (0 : C(α, E))

Depends on / 依赖: exists_ne, nontrivialTopology_iff_exists_norm_ne_zero
-/
instance [Nonempty α] {E : Type*} [NormedAddCommGroup E] [Nontrivial E] :
    NontrivialTopology C(α, E) := by
  simpa [nontrivialTopology_iff_exists_norm_ne_zero] using exists_ne (0 : C(α, E))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  body: by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

中文:
实例 [Nonempty
  签名: α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  定义体: by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

Depends on / 依赖: mkOfCompact_one, norm_mkOfCompact, norm_one
-/
instance [Nonempty α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  norm_one := by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

section

variable (f : C(α, E))

-- The corresponding lemmas for `BoundedContinuousFunction` are stated with `{f}`,
-- and so cannot be used in dot notation.
/--
theorem `norm_coe_le_norm` / 定理 `norm_coe_le_norm`

English:
theorem norm_coe_le_norm
  given: (x : α)
  statement: ‖f x‖ <= ‖f‖
  proof: (mkOfCompact f).norm_coe_le_norm x

中文:
定理 norm_coe_le_norm
  条件: (x : α)
  结论: ‖f x‖ <= ‖f‖
  证明: (mkOfCompact f).norm_coe_le_norm x

Depends on / 依赖: mkOfCompact, norm_coe_le_norm
-/
theorem norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖ :=
  (mkOfCompact f).norm_coe_le_norm x

/--
theorem `dist_le_two_norm` / 定理 `dist_le_two_norm`

English:
theorem dist_le_two_norm
  given: (x y : α)
  statement: dist (f x) (f y) <= 2 * ‖f‖
  proof: (mkOfCompact f).dist_le_two_norm x y

中文:
定理 dist_le_two_norm
  条件: (x y : α)
  结论: dist (f x) (f y) <= 2 * ‖f‖
  证明: (mkOfCompact f).dist_le_two_norm x y

Depends on / 依赖: dist_le_two_norm, mkOfCompact
-/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) <= 2 * ‖f‖ :=
  (mkOfCompact f).dist_le_two_norm x y

/--
theorem `norm_le` / 定理 `norm_le`

English:
theorem norm_le
  given: {C : Real} (C0 : (0 : Real) <= C)
  statement: ‖f‖ <= C ↔ forall x : α, ‖f x‖ <= C
  proof: @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

中文:
定理 norm_le
  条件: {C : 实数} (C0 : (0 : 实数) <= C)
  结论: ‖f‖ <= C ↔ 对任意 x : α, ‖f x‖ <= C
  证明: @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_le, mkOfCompact, norm_le
-/
theorem norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <= C ↔ forall x : α, ‖f x‖ <= C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

/--
theorem `norm_le_of_nonempty` / 定理 `norm_le_of_nonempty`

English:
theorem norm_le_of_nonempty
  given: [Nonempty α] {M : Real}
  statement: ‖f‖ <= M ↔ forall x, ‖f x‖ <= M
  proof: @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

中文:
定理 norm_le_of_nonempty
  条件: [Nonempty α] {M : 实数}
  结论: ‖f‖ <= M ↔ 对任意 x, ‖f x‖ <= M
  证明: @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_le_of_nonempty, mkOfCompact, norm_le_of_nonempty
-/
theorem norm_le_of_nonempty [Nonempty α] {M : Real} : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

/--
theorem `norm_lt_iff` / 定理 `norm_lt_iff`

English:
theorem norm_lt_iff
  given: {M : Real} (M0 : 0 < M)
  statement: ‖f‖ < M ↔ forall x, ‖f x‖ < M
  proof: @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

中文:
定理 norm_lt_iff
  条件: {M : 实数} (M0 : 0 < M)
  结论: ‖f‖ < M ↔ 对任意 x, ‖f x‖ < M
  证明: @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_lt_iff_of_compact, mkOfCompact, norm_lt_iff_of_compact
-/
theorem norm_lt_iff {M : Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

/--
theorem `nnnorm_lt_iff` / 定理 `nnnorm_lt_iff`

English:
theorem nnnorm_lt_iff
  given: {M : Real>=0} (M0 : 0 < M)
  statement: ‖f‖₊ < M ↔ forall x : α, ‖f x‖₊ < M
  proof: f.norm_lt_iff M0

中文:
定理 nnnorm_lt_iff
  条件: {M : 实数>=0} (M0 : 0 < M)
  结论: ‖f‖₊ < M ↔ 对任意 x : α, ‖f x‖₊ < M
  证明: f.norm_lt_iff M0

Depends on / 依赖: f.norm_lt_iff, norm_lt_iff
-/
theorem nnnorm_lt_iff {M : Real>=0} (M0 : 0 < M) : ‖f‖₊ < M ↔ forall x : α, ‖f x‖₊ < M :=
  f.norm_lt_iff M0

/--
theorem `norm_lt_iff_of_nonempty` / 定理 `norm_lt_iff_of_nonempty`

English:
theorem norm_lt_iff_of_nonempty
  given: [Nonempty α] {M : Real}
  statement: ‖f‖ < M ↔ forall x, ‖f x‖ < M
  proof: @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

中文:
定理 norm_lt_iff_of_nonempty
  条件: [Nonempty α] {M : 实数}
  结论: ‖f‖ < M ↔ 对任意 x, ‖f x‖ < M
  证明: @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact, mkOfCompact, norm_lt_iff_of_nonempty_compact
-/
theorem norm_lt_iff_of_nonempty [Nonempty α] {M : Real} : ‖f‖ < M ↔ forall x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

/--
theorem `nnnorm_lt_iff_of_nonempty` / 定理 `nnnorm_lt_iff_of_nonempty`

English:
theorem nnnorm_lt_iff_of_nonempty
  given: [Nonempty α] {M : Real>=0}
  statement: ‖f‖₊ < M ↔ forall x, ‖f x‖₊ < M
  proof: f.norm_lt_iff_of_nonempty

中文:
定理 nnnorm_lt_iff_of_nonempty
  条件: [Nonempty α] {M : 实数>=0}
  结论: ‖f‖₊ < M ↔ 对任意 x, ‖f x‖₊ < M
  证明: f.norm_lt_iff_of_nonempty

Depends on / 依赖: f.norm_lt_iff_of_nonempty, norm_lt_iff_of_nonempty
-/
theorem nnnorm_lt_iff_of_nonempty [Nonempty α] {M : Real>=0} : ‖f‖₊ < M ↔ forall x, ‖f x‖₊ < M :=
  f.norm_lt_iff_of_nonempty

/--
theorem `apply_le_norm` / 定理 `apply_le_norm`

English:
theorem apply_le_norm
  given: (f : C(α, Real)) (x : α)
  statement: f x <= ‖f‖
  proof: le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

中文:
定理 apply_le_norm
  条件: (f : C(α, 实数)) (x : α)
  结论: f x <= ‖f‖
  证明: le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

Depends on / 依赖: Or.inl, f.norm_coe_le_norm, le_abs, le_abs.mpr, le_refl, le_trans, norm_coe_le_norm
-/
theorem apply_le_norm (f : C(α, Real)) (x : α) : f x <= ‖f‖ :=
  le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

/--
theorem `neg_norm_le_apply` / 定理 `neg_norm_le_apply`

English:
theorem neg_norm_le_apply
  given: (f : C(α, Real)) (x : α)
  statement: -‖f‖ <= f x
  proof: le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))

中文:
定理 neg_norm_le_apply
  条件: (f : C(α, 实数)) (x : α)
  结论: -‖f‖ <= f x
  证明: le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))

Depends on / 依赖: f.norm_coe_le_norm, le_trans, neg_le, neg_le.mp, neg_le_abs, neg_le_neg, norm_coe_le_norm
-/
theorem neg_norm_le_apply (f : C(α, Real)) (x : α) : -‖f‖ <= f x :=
  le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))

/--
theorem `nnnorm_eq_iSup_nnnorm` / 定理 `nnnorm_eq_iSup_nnnorm`

English:
theorem nnnorm_eq_iSup_nnnorm
  statement: ‖f‖₊ = ⨆ x : α, ‖f x‖₊
  proof: (mkOfCompact f).nnnorm_eq_iSup_nnnorm

中文:
定理 nnnorm_eq_iSup_nnnorm
  结论: ‖f‖₊ = ⨆ x : α, ‖f x‖₊
  证明: (mkOfCompact f).nnnorm_eq_iSup_nnnorm

Depends on / 依赖: mkOfCompact, nnnorm_eq_iSup_nnnorm
-/
theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  (mkOfCompact f).nnnorm_eq_iSup_nnnorm

/--
theorem `norm_eq_iSup_norm` / 定理 `norm_eq_iSup_norm`

English:
theorem norm_eq_iSup_norm
  statement: ‖f‖ = ⨆ x : α, ‖f x‖
  proof: (mkOfCompact f).norm_eq_iSup_norm

中文:
定理 norm_eq_iSup_norm
  结论: ‖f‖ = ⨆ x : α, ‖f x‖
  证明: (mkOfCompact f).norm_eq_iSup_norm

Depends on / 依赖: mkOfCompact, norm_eq_iSup_norm
-/
theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
  (mkOfCompact f).norm_eq_iSup_norm

/--
theorem `enorm_eq_iSup_enorm` / 定理 `enorm_eq_iSup_enorm`

English:
theorem enorm_eq_iSup_enorm
  statement: ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
  proof: (mkOfCompact f).enorm_eq_iSup_enorm

中文:
定理 enorm_eq_iSup_enorm
  结论: ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
  证明: (mkOfCompact f).enorm_eq_iSup_enorm

Depends on / 依赖: enorm_eq_iSup_enorm, mkOfCompact
-/
theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ :=
  (mkOfCompact f).enorm_eq_iSup_enorm

-- A version with better keys
instance {X : Type*} [TopologicalSpace X] (K : TopologicalSpace.Compacts X) :
    CompactSpace (K : Set X) :=
  TopologicalSpace.Compacts.instCompactSpaceSubtypeMem ..

/--
theorem `norm_restrict_mono_set` / 定理 `norm_restrict_mono_set`

English:
theorem norm_restrict_mono_set
  statement: {X : Type*} [TopologicalSpace X] (f : C(X, E))
  proof: (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) Set.inclusion hKL x

中文:
定理 norm_restrict_mono_set
  结论: {X : 类型} [TopologicalSpace X] (f : C(X, E))
  证明: (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) Set.inclusion hKL x

Depends on / 依赖: Set.inclusion, f.restrict, inclusion, norm_coe_le_norm, norm_le, norm_nonneg, restrict
-/
theorem norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E))
    {K L : TopologicalSpace.Compacts X} (hKL : K <= L) : ‖f.restrict K‖ <= ‖f.restrict L‖ :=
(norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) Set.inclusion hKL x

/--
lemma `norm_eq_norm_coeFn` / 引理 `norm_eq_norm_coeFn`

English:
lemma norm_eq_norm_coeFn
  given: [Fintype α]
  statement: ‖f‖ = ‖(f : α -> E)‖
  proof: by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by positivity)]
    exact norm_le_pi_norm _
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    exact f.norm_coe_le_norm

中文:
引理 norm_eq_norm_coeFn
  条件: [Fintype α]
  结论: ‖f‖ = ‖(f : α -> E)‖
  证明: by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by positivity)]
    exact norm_le_pi_norm _
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    exact f.norm_coe_le_norm

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_le, f.norm_coe_le_norm, le_antisymm, norm_coe_le_norm, norm_le, norm_le_pi_norm, pi_norm_le_iff_of_nonneg
-/
lemma norm_eq_norm_coeFn [Fintype α] : ‖f‖ = ‖(f : α -> E)‖ := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by positivity)]
    exact norm_le_pi_norm _
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    exact f.norm_coe_le_norm

end

section

variable {R : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSeminormedRing
  signature: R] : NonUnitalSeminormedRing C(α, R) where
  body: inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul_le f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)

中文:
实例 [NonUnitalSeminormedRing
  签名: R] : NonUnitalSeminormedRing C(α, R) where
  定义体: inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul_le f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)
-/
instance [NonUnitalSeminormedRing R] : NonUnitalSeminormedRing C(α, R) where
  __ : SeminormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul_le f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSeminormedCommRing
  signature: R] : NonUnitalSeminormedCommRing C(α, R) where
  body: inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

中文:
实例 [NonUnitalSeminormedCommRing
  签名: R] : NonUnitalSeminormedCommRing C(α, R) where
  定义体: inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance
-/
instance [NonUnitalSeminormedCommRing R] : NonUnitalSeminormedCommRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedRing
  signature: R] : SeminormedRing C(α, R) where
  body: inferInstance
  __ : Ring C(α, R) := inferInstance

中文:
实例 [SeminormedRing
  签名: R] : SeminormedRing C(α, R) where
  定义体: inferInstance
  __ : Ring C(α, R) := inferInstance
-/
instance [SeminormedRing R] : SeminormedRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : Ring C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedCommRing
  signature: R] : SeminormedCommRing C(α, R) where
  body: inferInstance
  __ : CommRing C(α, R) := inferInstance

中文:
实例 [SeminormedCommRing
  签名: R] : SeminormedCommRing C(α, R) where
  定义体: inferInstance
  __ : CommRing C(α, R) := inferInstance
-/
instance [SeminormedCommRing R] : SeminormedCommRing C(α, R) where
  __ : SeminormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNormedRing
  signature: R] : NonUnitalNormedRing C(α, R) where
  body: inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance

中文:
实例 [NonUnitalNormedRing
  签名: R] : NonUnitalNormedRing C(α, R) where
  定义体: inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
-/
instance [NonUnitalNormedRing R] : NonUnitalNormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNormedCommRing
  signature: R] : NonUnitalNormedCommRing C(α, R) where
  body: inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

中文:
实例 [NonUnitalNormedCommRing
  签名: R] : NonUnitalNormedCommRing C(α, R) where
  定义体: inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance
-/
instance [NonUnitalNormedCommRing R] : NonUnitalNormedCommRing C(α, R) where
  __ : NonUnitalNormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedRing
  signature: R] : NormedRing C(α, R) where
  body: inferInstance
  __ : SeminormedRing C(α, R) := inferInstance

中文:
实例 [NormedRing
  签名: R] : NormedRing C(α, R) where
  定义体: inferInstance
  __ : SeminormedRing C(α, R) := inferInstance
-/
instance [NormedRing R] : NormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : SeminormedRing C(α, R) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedCommRing
  signature: R] : NormedCommRing C(α, R) where
  body: inferInstance
  __ : CommRing C(α, R) := inferInstance

中文:
实例 [NormedCommRing
  签名: R] : NormedCommRing C(α, R) where
  定义体: inferInstance
  __ : CommRing C(α, R) := inferInstance
-/
instance [NormedCommRing R] : NormedCommRing C(α, R) where
  __ : NormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

end

section

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
Instance `normedSpace` / 实例 `normedSpace`

English:
instance normedSpace
  signature: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  body: norm_smul_le

中文:
实例 normedSpace
  签名: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 E]
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance normedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] : NormedSpace 𝕜 C(α, E) where
  norm_smul_le := norm_smul_le

section

variable (α 𝕜 E)

/--
Definition of `linearIsometryBoundedOfCompact` / `linearIsometryBoundedOfCompact` 的定义

English:
definition linearIsometryBoundedOfCompact
  signature: : C(α, E) ≃ₗᵢ[𝕜] α ->ᵇ E
  body: { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun _ => rfl }

中文:
定义 linearIsometryBoundedOfCompact
  签名: : C(α, E) ≃ₗᵢ[𝕜] α ->ᵇ E
  定义体: { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun _ => rfl }

Depends on / 依赖: addEquivBoundedOfCompact, map_smul, norm_map
-/
def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α ->ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun _ => rfl }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equivBoundedOfCompact`, `addEquivBoundedOfCompact`
@[simp]
/--
theorem `linearIsometryBoundedOfCompact_symm_apply` / 定理 `linearIsometryBoundedOfCompact_symm_apply`

English:
theorem linearIsometryBoundedOfCompact_symm_apply
  given: (f : α ->ᵇ E)
  proof: rfl

@[simp]

中文:
定理 linearIsometryBoundedOfCompact_symm_apply
  条件: (f : α ->ᵇ E)
  证明: rfl

@[simp]
-/
theorem linearIsometryBoundedOfCompact_symm_apply (f : α ->ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl

@[simp]
/--
theorem `linearIsometryBoundedOfCompact_apply_apply` / 定理 `linearIsometryBoundedOfCompact_apply_apply`

English:
theorem linearIsometryBoundedOfCompact_apply_apply
  given: (f : C(α, E)) (a : α)
  proof: rfl

@[simp]

中文:
定理 linearIsometryBoundedOfCompact_apply_apply
  条件: (f : C(α, E)) (a : α)
  证明: rfl

@[simp]
-/
theorem linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl

@[simp]
/--
theorem `linearIsometryBoundedOfCompact_toIsometryEquiv` / 定理 `linearIsometryBoundedOfCompact_toIsometryEquiv`

English:
theorem linearIsometryBoundedOfCompact_toIsometryEquiv
  proof: rfl

@[simp]

中文:
定理 linearIsometryBoundedOfCompact_toIsometryEquiv
  证明: rfl

@[simp]
-/
theorem linearIsometryBoundedOfCompact_toIsometryEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E :=
  rfl

@[simp]
/--
theorem `linearIsometryBoundedOfCompact_toAddEquiv` / 定理 `linearIsometryBoundedOfCompact_toAddEquiv`

English:
theorem linearIsometryBoundedOfCompact_toAddEquiv
  proof: rfl

@[simp]

中文:
定理 linearIsometryBoundedOfCompact_toAddEquiv
  证明: rfl

@[simp]
-/
theorem linearIsometryBoundedOfCompact_toAddEquiv :
    ((linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α ->ᵇ E)) =
      addEquivBoundedOfCompact α E :=
  rfl

@[simp]
/--
theorem `linearIsometryBoundedOfCompact_of_compact_toEquiv` / 定理 `linearIsometryBoundedOfCompact_of_compact_toEquiv`

English:
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv
  proof: rfl

中文:
定理 linearIsometryBoundedOfCompact_of_compact_toEquiv
  证明: rfl
-/
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl

end

/--
lemma `nnnorm_smul_const` / 引理 `nnnorm_smul_const`

English:
lemma nnnorm_smul_const
  statement: {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
  proof: by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]

中文:
引理 nnnorm_smul_const
  结论: {R β : 类型} [SeminormedAddCommGroup β] [SeminormedRing R]
  证明: by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]
-/
@[simp] lemma nnnorm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖₊ = ‖f‖₊ * ‖b‖₊ := by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]

/--
lemma `norm_smul_const` / 引理 `norm_smul_const`

English:
lemma norm_smul_const
  statement: {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
  proof: by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]

中文:
引理 norm_smul_const
  结论: {R β : 类型} [SeminormedAddCommGroup β] [SeminormedRing R]
  证明: by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]
-/
@[simp] lemma norm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖ = ‖f‖ * ‖b‖ := by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]

section NormSum

variable {R : Type*} [NonUnitalSeminormedRing R] [IsCancelMulZero R]

open BoundedContinuousFunction

/--
lemma `norm_add_eq_max` / 引理 `norm_add_eq_max`

English:
lemma norm_add_eq_max
  given: {f g : C(α, R)} (h : f * g = 0)
  proof: by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using! congr($h x)
  simpa using! BoundedContinuousFunction.norm_add_eq_max h

中文:
引理 norm_add_eq_max
  条件: {f g : C(α, R)} (h : f * g = 0)
  证明: by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using! congr($h x)
  simpa using! BoundedContinuousFunction.norm_add_eq_max h

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_add_eq_max, mkOfCompact, norm_add_eq_max, replace
-/
lemma norm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using! congr($h x)
  simpa using! BoundedContinuousFunction.norm_add_eq_max h

/--
lemma `nnnorm_add_eq_max` / 引理 `nnnorm_add_eq_max`

English:
lemma nnnorm_add_eq_max
  given: {f g : C(α, R)} (h : f * g = 0)
  proof: NNReal.eq norm_add_eq_max h

中文:
引理 nnnorm_add_eq_max
  条件: {f g : C(α, R)} (h : f * g = 0)
  证明: NNReal.eq norm_add_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_add_eq_max
-/
lemma nnnorm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊ :=
NNReal.eq norm_add_eq_max h

/--
lemma `norm_sub_eq_max` / 引理 `norm_sub_eq_max`

English:
lemma norm_sub_eq_max
  given: {f g : C(α, R)} (h : f * g = 0)
  proof: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

中文:
引理 norm_sub_eq_max
  条件: {f g : C(α, R)} (h : f * g = 0)
  证明: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

Depends on / 依赖: norm_add_eq_max, sub_eq_add_neg
-/
lemma norm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖ = max ‖f‖ ‖g‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)

/--
lemma `nnnorm_sub_eq_max` / 引理 `nnnorm_sub_eq_max`

English:
lemma nnnorm_sub_eq_max
  given: {f g : C(α, R)} (h : f * g = 0)
  proof: NNReal.eq norm_sub_eq_max h

中文:
引理 nnnorm_sub_eq_max
  条件: {f g : C(α, R)} (h : f * g = 0)
  证明: NNReal.eq norm_sub_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_sub_eq_max
-/
lemma nnnorm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖₊ = max ‖f‖₊ ‖g‖₊ :=
NNReal.eq norm_sub_eq_max h

open scoped Function in
/--
lemma `nnnorm_sum_eq_sup` / 引理 `nnnorm_sum_eq_sup`

English:
lemma nnnorm_sum_eq_sup
  statement: {ι : Type*} {f : ι -> C(α, R)} (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

中文:
引理 nnnorm_sum_eq_sup
  结论: {ι : 类型} {f : ι -> C(α, R)} (s : Finset ι)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mul_sum, Finset.sum_eq_zero, classical, induction_on, insert, mul_sum, nnnorm_add_eq_max, sum_eq_zero
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι -> C(α, R)} (s : Finset ι)
    (h : Pairwise ((· * · = 0) on f)) :
    ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h (by grind)

end NormSum

section

variable {𝕜 : Type*} {γ : Type*} [NormedField 𝕜] [SeminormedRing γ] [NormedAlgebra 𝕜 γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAlgebra 𝕜 C(α, γ)
  body: { ContinuousMap.normedSpace, ContinuousMap.algebra with }

中文:
实例 :
  签名: NormedAlgebra 𝕜 C(α, γ)
  定义体: { ContinuousMap.normedSpace, ContinuousMap.algebra with }

Depends on / 依赖: ContinuousMap, ContinuousMap.algebra, ContinuousMap.normedSpace, algebra, normedSpace
-/
instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace, ContinuousMap.algebra with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type*}
variable [PseudoMetricSpace α] [CompactSpace α] [PseudoMetricSpace β]



/--
theorem `uniform_continuity` / 定理 `uniform_continuity`

English:
theorem uniform_continuity
  given: (f : C(α, β)) (ε : Real) (h : 0 < ε)
  proof: Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

中文:
定理 uniform_continuity
  条件: (f : C(α, β)) (ε : 实数) (h : 0 < ε)
  证明: Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

Depends on / 依赖: CompactSpace, CompactSpace.uniformContinuous_of_continuous, Metric, Metric.uniformContinuous_iff.mp, continuous, f.continuous, uniformContinuous_iff, uniformContinuous_of_continuous
-/
theorem uniform_continuity (f : C(α, β)) (ε : Real) (h : 0 < ε) :
    exists δ > 0, forall {x y}, dist x y < δ -> dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
/--
Definition of `modulus` / `modulus` 的定义

English:
definition modulus
  signature: (f : C(α, β)) (ε : Real) (h : 0 < ε)
  body: Classical.choose (uniform_continuity f ε h)

中文:
定义 modulus
  签名: (f : C(α, β)) (ε : 实数) (h : 0 < ε)
  定义体: Classical.choose (uniform_continuity f ε h)

Depends on / 依赖: Classical, Classical.choose, uniform_continuity
-/
def modulus (f : C(α, β)) (ε : Real) (h : 0 < ε) : Real :=
  Classical.choose (uniform_continuity f ε h)

/--
theorem `modulus_pos` / 定理 `modulus_pos`

English:
theorem modulus_pos
  given: (f : C(α, β)) {ε : Real} {h : 0 < ε}
  statement: 0 < f.modulus ε h
  proof: (Classical.choose_spec (uniform_continuity f ε h)).1

中文:
定理 modulus_pos
  条件: (f : C(α, β)) {ε : 实数} {h : 0 < ε}
  结论: 0 < f.modulus ε h
  证明: (Classical.choose_spec (uniform_continuity f ε h)).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, uniform_continuity
-/
theorem modulus_pos (f : C(α, β)) {ε : Real} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.choose_spec (uniform_continuity f ε h)).1

/--
theorem `dist_lt_of_dist_lt_modulus` / 定理 `dist_lt_of_dist_lt_modulus`

English:
theorem dist_lt_of_dist_lt_modulus
  statement: (f : C(α, β)) (ε : Real) (h : 0 < ε) {a b : α}
  proof: (Classical.choose_spec (uniform_continuity f ε h)).2 w

中文:
定理 dist_lt_of_dist_lt_modulus
  结论: (f : C(α, β)) (ε : 实数) (h : 0 < ε) {a b : α}
  证明: (Classical.choose_spec (uniform_continuity f ε h)).2 w

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, uniform_continuity
-/
theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : Real) (h : 0 < ε) {a b : α}
    (w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε :=
  (Classical.choose_spec (uniform_continuity f ε h)).2 w

end UniformContinuity

end ContinuousMap

namespace ContinuousMap

section LocalNormalConvergence

/-! ### Local normal convergence

A sum of continuous functions (on a locally compact space) is "locally normally convergent" if the
sum of its sup-norms on any compact subset is summable. This implies convergence in the topology
of `C(X, E)` (i.e. locally uniform convergence). -/

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/--
theorem `summable_of_locally_summable_norm` / 定理 `summable_of_locally_summable_norm`

English:
theorem summable_of_locally_summable_norm
  statement: {ι : Type*} {F : ι -> C(X, E)}
  proof: by
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : forall s : Finset ι, restrict K (∑ i in s, F i) = ∑ i in s, restrict K (F i) := by
    intro s
    ext1 x
    -- TODO: there is a non-confluence problem in the lemmas here,

中文:
定理 summable_of_locally_summable_norm
  结论: {ι : 类型} {F : ι -> C(X, E)}
  证明: by
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : forall s : Finset ι, restrict K (∑ i in s, F i) = ∑ i in s, restrict K (F i) := by
    intro s
    ext1 x
    -- TODO: there is a non-confluence problem in the lemmas here,

Depends on / 依赖: Compacts, ContinuousMap, ContinuousMap.exists_tendsto_compactOpen_iff_forall, Finset, exists_tendsto_compactOpen_iff_forall, restrict
-/
theorem summable_of_locally_summable_norm {ι : Type*} {F : ι -> C(X, E)}
    (hF : forall K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F := by
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : forall s : Finset ι, restrict K (∑ i in s, F i) = ∑ i in s, restrict K (F i) := by
    intro s
    ext1 x
    -- TODO: there is a non-confluence problem in the lemmas here,
    -- and `SetLike.coe_sort_coe` prevents `restrict_apply` from being used.
    simp [-SetLike.coe_sort_coe]
  simpa only [HasSum, A] using! (hF K).of_norm

end LocalNormalConvergence

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring. -/


section NormedSpace

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

/--
theorem `_root_.BoundedContinuousFunction.mkOfCompact_star` / 定理 `_root_.BoundedContinuousFunction.mkOfCompact_star`

English:
theorem _root_.BoundedContinuousFunction.mkOfCompact_star
  given: [CompactSpace α] (f : C(α, β))
  proof: rfl

中文:
定理 _root_.BoundedContinuousFunction.mkOfCompact_star
  条件: [CompactSpace α] (f : C(α, β))
  证明: rfl
-/
theorem _root_.BoundedContinuousFunction.mkOfCompact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : NormedStarGroup C(α, β) where
  body: by
    rw [← BoundedContinuousFunction.norm_mkOfCompact]; rw [BoundedContinuousFunction.mkOfCompact_star]; rw [norm_star]; rw [BoundedContinuousFunction.norm_mkOfCompact]

中文:
实例 [CompactSpace
  签名: α] : NormedStarGroup C(α, β) where
  定义体: by
    rw [← BoundedContinuousFunction.norm_mkOfCompact]; rw [BoundedContinuousFunction.mkOfCompact_star]; rw [norm_star]; rw [BoundedContinuousFunction.norm_mkOfCompact]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.mkOfCompact_star, BoundedContinuousFunction.norm_mkOfCompact, mkOfCompact_star, norm_mkOfCompact, norm_star
-/
instance [CompactSpace α] : NormedStarGroup C(α, β) where
  norm_star_le f := by
    rw [← BoundedContinuousFunction.norm_mkOfCompact]; rw [BoundedContinuousFunction.mkOfCompact_star]; rw [norm_star]; rw [BoundedContinuousFunction.norm_mkOfCompact]

end NormedSpace

section CStarRing

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [CompactSpace α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNormedRing
  signature: β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  body: by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

中文:
实例 [NonUnitalNormedRing
  签名: β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  定义体: by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, ContinuousMap, ContinuousMap.norm_coe_le_norm, ContinuousMap.norm_le, Real.le_sqrt, Real.sqrt_nonneg, le_sqrt, norm_coe_le_norm, norm_le, norm_nonneg, norm_star_mul_self, sqrt_nonneg
-/
instance [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  norm_mul_self_le f := by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

end CStarRing

end ContinuousMap
