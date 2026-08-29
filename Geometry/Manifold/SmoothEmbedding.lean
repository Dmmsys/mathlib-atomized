/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Diffeomorph -- shake: keep (used in `proof_wanted` only)

/-! # Smooth embeddings

In this file, we define `C^n` embeddings between `C^n` manifolds.
This will be useful to define embedded submanifolds.

## Main definitions and results

* `IsSmoothEmbedding I J n f` means `f : M → N` is a `C^n` embedding:
  it is both a `C^n` immersion and a topological embedding
* `IsSmoothEmbedding.prodMap`: the product of two smooth embeddings is a smooth embedding
* `IsSmoothEmbedding.id`: the identity map is a smooth embedding
* `IsSmoothEmbedding.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth embedding
* `ModelWithCorners.isSmoothEmbedding`: every model with corners is itself a smooth embedding
* `IsSmoothEmbedding.sumInl` and `IsSmoothEmbedding.sumInr`: given `C^n` manifolds `M` and `N`,
  `Sum.inl : M → M ⊕ N` and `Sum.inr : N → M ⊕ N` are `C^n` embeddings
* `IsSmoothEmbedding.contMDiff`: if `f` is a `C^n` embedding, it is automatically `C^n`
  in the sense of `ContMDiff`.

## Implementation notes

* Unlike immersions, being an embedding is a global notion: this is why we have no definition
  `IsSmoothEmbeddingAt`. (Besides, it would be equivalent to being an immersion at `x`.)
* Note that being a smooth embedding is a stronger condition than being a smooth map
  which is a topological embedding. Even being a homeomorphism and a smooth map is not sufficient.
  See e.g. https://math.stackexchange.com/a/2583667 and
  https://math.stackexchange.com/a/3769328 for counterexamples.

## TODO
* `IsSmoothEmbedding.comp`: the composition of smooth embeddings (between Banach manifolds)
  is a smooth embedding
* `IsLocalDiffeomorph.isSmoothEmbedding`, `Diffeomorph.isSmoothEmbedding`:
  a local diffeomorphism (and in particular, a diffeomorphism) is a smooth embedding

-/

open scoped ContDiff
open Topology

public section

noncomputable section

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  {H H' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E₁ H} {I' : ModelWithCorners 𝕜 E₂ H'}
  {J : ModelWithCorners 𝕜 E₃ G} {J' : ModelWithCorners 𝕜 E₄ G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : Nat∞ω}

variable (I J n) in
/-- A `C^n` map `f : M → M'` is a smooth `C^n` embedding if it is a topological embedding
and a `C^n` immersion. -/
@[mk_iff]
/--
Definition of `IsSmoothEmbedding` / `IsSmoothEmbedding` 的定义

English:
structure IsSmoothEmbedding
  parameters: (f : M -> N)
  axioms and operations (2):
    - isImmersion : IsImmersion I J n f
    - isEmbedding : IsEmbedding f

中文:
结构 是光滑嵌入
  参数: (f : M -> N)
  公理与运算 (2 个):
    - isImmersion : 是Immersion I J n f
    - isEmbedding : 是嵌入 f
-/
structure IsSmoothEmbedding (f : M -> N) where
  isImmersion : IsImmersion I J n f
  isEmbedding : IsEmbedding f

namespace IsSmoothEmbedding

variable {f g : M -> N}

/--
lemma `id` / 引理 `id`

English:
lemma id
  given: [IsManifold I n M]
  statement: IsSmoothEmbedding I I n (@id M)
  proof: ⟨.id, .id⟩

中文:
引理 id
  条件: [是流形 I n M]
  结论: 是光滑嵌入 I I n (@id M)
  证明: ⟨.id, .id⟩
-/
protected lemma id [IsManifold I n M] : IsSmoothEmbedding I I n (@id M) := ⟨.id, .id⟩

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {f : M -> N} {g : M' -> N'}
  proof: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

中文:
定理 prodMap
  结论: {f : M -> N} {g : M' -> N'}
  证明: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

Depends on / 依赖: prodMap
-/
theorem prodMap {f : M -> N} {g : M' -> N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSmoothEmbedding I J n f) (hg : IsSmoothEmbedding I' J' n g) :
    IsSmoothEmbedding (I.prod I') (J.prod J') n (Prod.map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

/--
lemma `of_opens` / 引理 `of_opens`

English:
lemma of_opens
  given: [IsManifold I n M] (s : TopologicalSpace.Opens M)
  proof: by
  rw [isSmoothEmbedding_iff]
  exact ⟨IsImmersion.of_opens s, IsEmbedding.subtypeVal⟩

中文:
引理 of_opens
  条件: [是流形 I n M] (s : 拓扑空间.Opens M)
  证明: by
  rw [isSmoothEmbedding_iff]
  exact ⟨IsImmersion.of_opens s, IsEmbedding.subtypeVal⟩

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal, IsImmersion, IsImmersion.of_opens, isSmoothEmbedding_iff, of_opens, subtypeVal
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsSmoothEmbedding I I n (Subtype.val : s -> M) := by
  rw [isSmoothEmbedding_iff]
  exact ⟨IsImmersion.of_opens s, IsEmbedding.subtypeVal⟩

/--
lemma `_root_.ModelWithCorners.isSmoothEmbedding` / 引理 `_root_.ModelWithCorners.isSmoothEmbedding`

English:
lemma _root_.ModelWithCorners.isSmoothEmbedding
  given: {n : Nat}
  proof: ⟨I.isImmersion, I.isClosedEmbedding.isEmbedding⟩

中文:
引理 _root_.带角模型.isSmoothEmbedding
  条件: {n : 自然数}
  证明: ⟨I.isImmersion, I.isClosedEmbedding.isEmbedding⟩
-/
protected lemma _root_.ModelWithCorners.isSmoothEmbedding {n : Nat} :
    IsSmoothEmbedding I (modelWithCornersSelf 𝕜 E₁) n I :=
  ⟨I.isImmersion, I.isClosedEmbedding.isEmbedding⟩

/--
lemma `sumInl` / 引理 `sumInl`

English:
lemma sumInl
  statement: {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  proof: ⟨IsImmersionOfComplement.sumInl.isImmersion, Topology.IsEmbedding.inl⟩

中文:
引理 sumInl
  结论: {M' : 类型} [拓扑空间 M'] [Charted空间 H M']
  证明: ⟨IsImmersionOfComplement.sumInl.isImmersion, Topology.IsEmbedding.inl⟩

Depends on / 依赖: IsEmbedding, IsImmersionOfComplement, IsImmersionOfComplement.sumInl.isImmersion, Topology, Topology.IsEmbedding.inl, isImmersion, sumInl
-/
lemma sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inl M M') :=
  ⟨IsImmersionOfComplement.sumInl.isImmersion, Topology.IsEmbedding.inl⟩

/--
lemma `sumInr` / 引理 `sumInr`

English:
lemma sumInr
  statement: {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  proof: ⟨IsImmersionOfComplement.sumInr.isImmersion, Topology.IsEmbedding.inr⟩

中文:
引理 sumInr
  结论: {M' : 类型} [拓扑空间 M'] [Charted空间 H M']
  证明: ⟨IsImmersionOfComplement.sumInr.isImmersion, Topology.IsEmbedding.inr⟩

Depends on / 依赖: IsEmbedding, IsImmersionOfComplement, IsImmersionOfComplement.sumInr.isImmersion, Topology, Topology.IsEmbedding.inr, isImmersion, sumInr
-/
lemma sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inr M M') :=
  ⟨IsImmersionOfComplement.sumInr.isImmersion, Topology.IsEmbedding.inr⟩

/--
lemma `contMDiff` / 引理 `contMDiff`

English:
lemma contMDiff
  given: (hf : IsSmoothEmbedding I J n f)
  proof: hf.isImmersion.contMDiff

中文:
引理 contMDiff
  条件: (hf : 是光滑嵌入 I J n f)
  证明: hf.isImmersion.contMDiff

Depends on / 依赖: contMDiff, hf.isImmersion.contMDiff, isImmersion
-/
lemma contMDiff (hf : IsSmoothEmbedding I J n f) :
    ContMDiff I J n f :=
  hf.isImmersion.contMDiff

-- use IsImmersion.comp and IsEmbedding.comp
/-- The composition of two smooth embeddings between Banach manifolds is a smooth embedding. -/
proof_wanted comp -- [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
    {g : N -> N'} (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J' n (g ∘ f)

end IsSmoothEmbedding

-- TODO: prove the same result for local diffeomorphisms and deduce it as a corollary
proof_wanted Diffeomorph.isSmoothEmbedding [IsManifold I n M]
    (φ : Diffeomorph I I M M n) : IsSmoothEmbedding I I n φ

end Manifold
