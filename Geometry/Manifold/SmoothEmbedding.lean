/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Diffeomorph  -- shake: keep (used in `proof_wanted` only)

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
  {n : ℕ∞ω}

variable (I J n) in
/-- A `C^n` map `f : M → M'` is a smooth `C^n` embedding if it is a topological embedding
and a `C^n` immersion. -/
@[mk_iff]
/-
**Manifold.IsSmoothEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Manifold`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E₁ : Type u_2
} →       {E₃ : Type u_4} →         [inst_1 : NormedAddCommGroup E₁] →          
 [inst_2 : NormedSpace 𝕜 E₁] →             [inst_3 : NormedAddCommGroup E₃] →   
            [inst_4 : NormedSpace 𝕜 E₃] →                 {H : Type u_6} →      
             {G : Type u_8} →                     [inst_5 : TopologicalSpace H] 
→                       [inst_6 : TopologicalSpace G] →                         
ModelWithCorners 𝕜 E₁ H →                           ModelWithCorners 𝕜 E₃ G →   
                          {M : Type u_10} →                               {N : T
ype u_12} →                                 [inst : TopologicalSpace M] →       
                            [ChartedSpace H M] →                                
     [inst : TopologicalSpace N] → [ChartedSpace G N] → WithTop ℕ∞ → (M → N) → P
rop
参数：M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `C^n` map `f : M → M'` is a smooth `C^n` embedding if it is a topological embe
dding
and a `C^n` immersion.
-/
structure IsSmoothEmbedding (f : M → N) where
  isImmersion : IsImmersion I J n f
  isEmbedding : IsEmbedding f

namespace IsSmoothEmbedding

variable {f g : M → N}

/-
**Manifold.IsSmoothEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSmoothEmbe
dding`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E₁ : Type u_2} [inst_
1 : NormedAddCommGroup E₁]   [inst_2 : NormedSpace 𝕜 E₁] {H : Type u_6} [inst_3 
: TopologicalSpace H] {I : ModelWithCorners 𝕜 E₁ H} {M : Type u_10}   [inst_4 : 
TopologicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n
 M],   Manifold.IsSmoothEmbedding I I n id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersion.id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `Topology.IsEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], T
opology.IsEmbedding id
-/
protected lemma id [IsManifold I n M] : IsSmoothEmbedding I I n (@id M) := ⟨.id, .id⟩

/-- If `f: M → N` and `g: M' × N'` are smooth embeddings, respectively,
then so is `f × g: M × M' → N × N'`. -/
/-
**Manifold.IsSmoothEmbedding.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSmoot
hEmbedding`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} [IsManifold I n M] [IsManifold I' n M'
] [IsManifold J n N] [IsManifold J' n N'] (hf : IsSmoothEmbedding I J n f) (hg :
 IsSmoothEmbedding I' J' n g) : IsSmoothEmbedding (I.prod I') (J.prod J') n (Pro
d.map f g)
参数：hf : IsSmoothEmbedding I J n f；hg : IsSmoothEmbedding I' J' n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersion.prodMap`：prodMap {f : M -> N} {g : M' -> N'} [IsMan
ifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N'] (hf : 
IsImmersion I J n …
· 使用定理 `Manifold.IsSmoothEmbedding.isImmersion`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E₁ : Type u_2} {E₃ : Type u_4} [inst_1 : NormedAddCommGroup
 E₁]   [inst_2 : NormedSpace…
· 使用引理 `Topology.IsEmbedding.prodMap`：Topology.IsEmbedding.prodMap {f : X -> Y} 
{g : Z -> W} (hf : IsEmbedding f) (hg : IsEmbedding g) : IsEmbedding (Prod.map f
 g) where toIsIndu…
· 使用定理 `Manifold.IsSmoothEmbedding.isEmbedding`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E₁ : Type u_2} {E₃ : Type u_4} [inst_1 : NormedAddCommGroup
 E₁]   [inst_2 : NormedSpace…

--- 原说明 ---
If `f: M → N` and `g: M' × N'` are smooth embeddings, respectively,
then so is `f × g: M × M' → N × N'`.
-/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSmoothEmbedding I J n f) (hg : IsSmoothEmbedding I' J' n g) :
    IsSmoothEmbedding (I.prod I') (J.prod J') n (Prod.map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

/- The inclusion of an open subset `s` of a smooth manifold `M` is a smooth embedding. -/
/-
**Manifold.IsSmoothEmbedding.of_opens** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSmoo
thEmbedding`。
形式化陈述：of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) : IsSmoothEmbed
ding I I n (Subtype.val : s -> M)
参数：s : TopologicalSpace.Opens M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.isSmoothEmbedding_iff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E₁ : Type u_2} {E₃ : Type u_4} [inst_1 : NormedAddCommGroup E₁]   [
inst_2 : NormedSpace…
· 使用引理 `Manifold.IsImmersion.of_opens`：of_opens [IsManifold I n M] (s : Topologi
calSpace.Opens M) : IsImmersion I I n (Subtype.val : s -> M)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
The inclusion of an open subset `s` of a smooth manifold `M` is a smooth embeddi
ng.
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsSmoothEmbedding I I n (Subtype.val : s → M) := by
  rw [isSmoothEmbedding_iff]
  exact ⟨IsImmersion.of_opens s, IsEmbedding.subtypeVal⟩

/-- Every `ModelWithCorners 𝕜 E H` is a smooth embedding when viewed as a map `H → E`. -/
/-
**Manifold.IsSmoothEmbedding._root_.ModelWithCorners.isSmoothEmbedding** 是 Mathl
ib 中的一个引理，位于命名空间 `Manifold.IsSmoothEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `ModelWithCorners 𝕜 E H` is a smooth embedding when viewed as a map `H → E
`.
-/
protected lemma _root_.ModelWithCorners.isSmoothEmbedding {n : ℕ} :
    IsSmoothEmbedding I (modelWithCornersSelf 𝕜 E₁) n I :=
  ⟨I.isImmersion, I.isClosedEmbedding.isEmbedding⟩

/-- Given `C^n` manifolds `M` and `N`, `Sum.inl : M → M ⊕ N` is a `C^n` embedding. -/
/-
**Manifold.IsSmoothEmbedding.sumInl** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSmooth
Embedding`。
形式化陈述：sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold 
I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inl M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionOfComplement.isImmersion`：isImmersion (h : IsImmersi
onOfComplement F I J n f) : IsImmersion I J n f
· 使用引理 `Manifold.IsImmersionOfComplement.sumInl`：sumInl {M' : Type*} [Topologica
lSpace M'] [ChartedSpace H M'] [IsManifold I n M] [IsManifold I n M'] : IsImmers
ionOfComplement Unit I I n (@…
· 使用定理 `Topology.IsEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inl

--- 原说明 ---
Given `C^n` manifolds `M` and `N`, `Sum.inl : M → M ⊕ N` is a `C^n` embedding.
-/
lemma sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inl M M') :=
  ⟨IsImmersionOfComplement.sumInl.isImmersion, Topology.IsEmbedding.inl⟩

/-- Given `C^n` manifolds `M` and `N`, `Sum.inr : N → M ⊕ N` is a `C^n` embedding. -/
/-
**Manifold.IsSmoothEmbedding.sumInr** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSmooth
Embedding`。
形式化陈述：sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold 
I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inr M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionOfComplement.isImmersion`：isImmersion (h : IsImmersi
onOfComplement F I J n f) : IsImmersion I J n f
· 使用引理 `Manifold.IsImmersionOfComplement.sumInr`：sumInr {M' : Type*} [Topologica
lSpace M'] [ChartedSpace H M'] [IsManifold I n M] [IsManifold I n M'] : IsImmers
ionOfComplement Unit I I n (@…
· 使用定理 `Topology.IsEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y], Topology.IsEmbedding Sum.inr

--- 原说明 ---
Given `C^n` manifolds `M` and `N`, `Sum.inr : N → M ⊕ N` is a `C^n` embedding.
-/
lemma sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] : IsSmoothEmbedding I I n (@Sum.inr M M') :=
  ⟨IsImmersionOfComplement.sumInr.isImmersion, Topology.IsEmbedding.inr⟩

/-- A smooth embedding is automatically smooth. -/
/-
**Manifold.IsSmoothEmbedding.contMDiff** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSmo
othEmbedding`。
形式化陈述：contMDiff (hf : IsSmoothEmbedding I J n f) : ContMDiff I J n f
参数：hf : IsSmoothEmbedding I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersion.contMDiff`：contMDiff (h : IsImmersion I J n f) : CM
Diff n f
· 使用定理 `Manifold.IsSmoothEmbedding.isImmersion`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E₁ : Type u_2} {E₃ : Type u_4} [inst_1 : NormedAddCommGroup
 E₁]   [inst_2 : NormedSpace…

--- 原说明 ---
A smooth embedding is automatically smooth.
-/
lemma contMDiff (hf : IsSmoothEmbedding I J n f) :
    ContMDiff I J n f :=
  hf.isImmersion.contMDiff

-- use IsImmersion.comp and IsEmbedding.comp
/-- The composition of two smooth embeddings between Banach manifolds is a smooth embedding. -/
proof_wanted comp -- [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
    {g : N → N'} (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J' n (g ∘ f)

end IsSmoothEmbedding

-- TODO: prove the same result for local diffeomorphisms and deduce it as a corollary
proof_wanted Diffeomorph.isSmoothEmbedding [IsManifold I n M]
    (φ : Diffeomorph I I M M n) : IsSmoothEmbedding I I n φ

end Manifold

