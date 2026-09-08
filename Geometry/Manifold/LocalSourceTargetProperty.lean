/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Local properties of smooth functions which depend on both the source and target

In this file, we consider local properties of functions between manifolds, which depend on both the
source and the target: more precisely, properties `P` of functions `f : M → N` such that
`f` has property `P` if and only if there is a suitable pair of charts on `M` and `N`, respectively,
such that `f` read in these charts has a particular form.
The motivating examples of this general description are immersions and submersions:
`f : M → N` is an immersion at `x` iff there are charts `φ` and `ψ` of `M` and `N` around `x` and
`f x`, respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`. Similarly, `f` is a
submersion at `x` iff it looks like a projection `(u, v) ↦ u` in suitable charts near `x` and `f x`.

Studying such local properties allows proving several lemmas about immersions and submersions
only once. In `IsImmersionEmbedding.lean`, we prove that being an immersion at `x` is indeed a
local property of this form.

## Main definitions and results

* `Manifold.LocalSourceTargetPropertyAt` captures a local property of the above form:
  for each `f : M → N`, and pair of charts `φ` of `M` and `ψ` of `N`, the local property is either
  satisfied or not.
  We ask that the property be stable under congruence and under restriction of `φ`.
* `Manifold.LiftSourceTargetPropertyAt f x P`, where `P` is a `LocalSourceTargetPropertyAt`,
  defines a local property of functions of the above shape:
  `f` has this property at `x` if there exist charts `φ` and `ψ` such that `P f φ ψ` holds.
* `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`: if `f` has property `P` at `x`
  and `g` equals `f` near `x`, then `g` also has property `P` at `x`.
* `IsOpen.liftSourceTargetPropertyAt`: the set of points at which `LiftSourceTargetPropertyAt`
  holds is open

-/

public section

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 E E' F F' H H' G G' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

namespace Manifold

/-- Structure recording good behaviour of a property of functions `M → N` w.r.t. compatible
choices of both a chart on `M` and `N`. Currently, we ask for the property to be stable under
restriction of the domain chart, and local in the target.

Motivating examples are immersions and submersions of smooth manifolds. -/
/-
**Manifold.IsLocalSourceTargetProperty** 是 Mathlib 中的一个归纳类型，位于命名空间 `Manifold`。
形式化陈述：{H : Type u_6} →   {G : Type u_8} →     [inst : TopologicalSpace H] →     
  [inst_1 : TopologicalSpace G] →         {M : Type u_10} →           {N : Type 
u_12} →             [inst_2 : TopologicalSpace M] →               [inst_3 : Topo
logicalSpace N] →                 ((M → N) → OpenPartialHomeomorph M H → OpenPar
tialHomeomorph N G → Prop) → Prop
参数：(M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure recording good behaviour of a property of functions `M → N` w.r.t. com
patible
choices of both a chart on `M` and `N`. Currently, we ask for the property to be
 stable under
restriction of the domain chart, and local in the target.

Motivating examples are immersions and submersions of smooth manifolds.
-/
structure IsLocalSourceTargetProperty
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop where
  mono_source : ∀ {f : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    ∀ {s : Set M}, IsOpen s → P f φ ψ → P f (φ.restr s) ψ
  -- Note: the analogous `mono_target` statement is true for both immersions and submersions.
  -- If and when a future lemma requires it, add this here.
  congr : ∀ {f g : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    EqOn f g φ.source → P f φ ψ → P g φ ψ

variable (I J n) in
/-- Data witnessing the fact that `f` has local property `P` at `x` -/
/-
**Manifold.LocalPresentationAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Manifold`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_4} →       {H : Type u
_6} →         {G : Type u_8} →           [inst : NontriviallyNormedField 𝕜] →   
          [inst_1 : NormedAddCommGroup E] →               [inst_2 : NormedSpace 
𝕜 E] →                 [inst_3 : NormedAddCommGroup F] →                   [inst
_4 : NormedSpace 𝕜 F] →                     [inst_5 : TopologicalSpace H] →     
                  [inst_6 : TopologicalSpace G] →                         ModelW
ithCorners 𝕜 E H →                           ModelWithCorners 𝕜 F G →           
                  {M : Type u_10} →                               {N : Type u_12
} →                                 [inst : TopologicalSpace M] →               
                    [ChartedSpace H M] →                                     [in
st_8 : TopologicalSpace N] →                                       [ChartedSpace
 G N] →                                         WithTop ℕ∞ →                    
                       (M → N) →                                             M →
                                               ((M → N) → OpenPartialHomeomorph 
M H → OpenPartialHomeomorph N G → Prop) →                                       
          Type (max (max (max u_10 u_12) u_6) u_8)
参数：M → N；(M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop；
max (max (max u_10 u_12) u_6) u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data witnessing the fact that `f` has local property `P` at `x`
-/
structure LocalPresentationAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) where
  /-- A choice of chart on the domain `M` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `codChart`, `f` has the local property `P` at `x`. -/
  domChart : OpenPartialHomeomorph M H
  /-- A choice of chart on the target `N` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `domChart`, `f` has the local property `P` at `x`. -/
  codChart : OpenPartialHomeomorph N G
  mem_domChart_source : x ∈ domChart.source
  mem_codChart_source : f x ∈ codChart.source
  domChart_mem_maximalAtlas : domChart ∈ IsManifold.maximalAtlas I n M
  codChart_mem_maximalAtlas : codChart ∈ IsManifold.maximalAtlas J n N
  source_subset_preimage_source : domChart.source ⊆ f ⁻¹' codChart.source
  property : P f domChart codChart

variable (I J n) in
/-- The induced property by a local property `P`: it is satisfied for `f` at `x` iff there exist
charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that `f` satisfies `P`
w.r.t. `φ` and `ψ`.

The motivating examples are smooth immersions and submersions: the corresponding condition is that
`f` look like the inclusion `u ↦ (u, 0)` (resp. a projection `(u, v) ↦ u`)
in the charts `φ` and `ψ`.
-/
@[expose]
/-
**Manifold.LiftSourceTargetPropertyAt** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：LiftSourceTargetPropertyAt (f : M -> N) (x : M) (P : (M -> N) -> OpenParti
alHomeomorph M H -> OpenPartialHomeomorph N G -> Prop) : Prop
参数：f : M -> N；x : M；P : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHome
omorph N G -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced property by a local property `P`: it is satisfied for `f` at `x` iff
 there exist
charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that 
`f` satisfies `P`
w.r.t. `φ` and `ψ`.

The motivating examples are smooth immersions and submersions: the corresponding
 condition is that
`f` look like the inclusion `u ↦ (u, 0)` (resp. a projection `(u, v) ↦ u`)
in the charts `φ` and `ψ`.
-/
def LiftSourceTargetPropertyAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop :=
  Nonempty (LocalPresentationAt I J n f x P)

namespace LocalPresentationAt

variable {f g : M → N} {x : M}
  {P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop}

/-
**Manifold.LocalPresentationAt.mapsto_domChart_source_codChart_source** 是 Mathli
b 中的一个引理，位于命名空间 `Manifold.LocalPresentationAt`。
形式化陈述：mapsto_domChart_source_codChart_source (h : LocalPresentationAt I J n f x 
P) : MapsTo f h.domChart.source h.codChart.source
参数：h : LocalPresentationAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.source_subset_preimage_source`：∀ {𝕜 : Type 
u_1} {E : Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : Nontriv
iallyNormedField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma mapsto_domChart_source_codChart_source (h : LocalPresentationAt I J n f x P) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

end LocalPresentationAt

namespace LiftSourceTargetPropertyAt

variable {f g : M → N} {x : M}
  {P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop}

/-- A choice of charts witnessing the local property `P` of `f` at `x`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.localPresentationAt** 是 Mathlib 中的一个定义，位于命
名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：localPresentationAt (h : LiftSourceTargetPropertyAt I J n f x P) : LocalPr
esentationAt I J n f x P
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of charts witnessing the local property `P` of `f` at `x`.
-/
noncomputable def localPresentationAt (h : LiftSourceTargetPropertyAt I J n f x P) :
    LocalPresentationAt I J n f x P :=
  Classical.choice h

/-- A choice of chart on the domain `M` of a local property of `f` at `x`:
w.r.t. this chart and `h.codChart`, `f` has the local property `P` at `x`.
The particular chart is arbitrary, but this choice matches the witness given by `h.codChart`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.domChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifo
ld.LiftSourceTargetPropertyAt`。
形式化陈述：domChart (h : LiftSourceTargetPropertyAt I J n f x P) : OpenPartialHomeomo
rph M H
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the domain `M` of a local property of `f` at `x`:
w.r.t. this chart and `h.codChart`, `f` has the local property `P` at `x`.
The particular chart is arbitrary, but this choice matches the witness given by 
`h.codChart`.
-/
noncomputable def domChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph M H :=
  h.localPresentationAt.domChart

/-- A choice of chart on the co-domain `N` of a local property of `f` at `x`:
w.r.t. this chart and `h.domChart`, `f` has the local property `P` at `x`
The particular chart is arbitrary, but this choice matches the witness given by `h.domChart`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.codChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifo
ld.LiftSourceTargetPropertyAt`。
形式化陈述：codChart (h : LiftSourceTargetPropertyAt I J n f x P) : OpenPartialHomeomo
rph N G
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the co-domain `N` of a local property of `f` at `x`:
w.r.t. this chart and `h.domChart`, `f` has the local property `P` at `x`
The particular chart is arbitrary, but this choice matches the witness given by 
`h.domChart`.
-/
noncomputable def codChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph N G :=
  h.localPresentationAt.codChart
/-
**Manifold.LiftSourceTargetPropertyAt.mem_domChart_source** 是 Mathlib 中的一个引理，位于命
名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：mem_domChart_source (h : LiftSourceTargetPropertyAt I J n f x P) : x in h.
domChart.source
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.mem_domChart_source`：∀ {𝕜 : Type u_1} {E : 
Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : NontriviallyNorme
dField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma mem_domChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    x ∈ h.domChart.source :=
  h.localPresentationAt.mem_domChart_source
/-
**Manifold.LiftSourceTargetPropertyAt.mem_codChart_source** 是 Mathlib 中的一个引理，位于命
名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：mem_codChart_source (h : LiftSourceTargetPropertyAt I J n f x P) : f x in 
h.codChart.source
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.mem_codChart_source`：∀ {𝕜 : Type u_1} {E : 
Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : NontriviallyNorme
dField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma mem_codChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    f x ∈ h.codChart.source :=
  h.localPresentationAt.mem_codChart_source
/-
**Manifold.LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：domChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h
.domChart in IsManifold.maximalAtlas I n M
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.domChart_mem_maximalAtlas`：∀ {𝕜 : Type u_1}
 {E : Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : Nontriviall
yNormedField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma domChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.localPresentationAt.domChart_mem_maximalAtlas
/-
**Manifold.LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：codChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h
.codChart in IsManifold.maximalAtlas J n N
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.codChart_mem_maximalAtlas`：∀ {𝕜 : Type u_1}
 {E : Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : Nontriviall
yNormedField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma codChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.localPresentationAt.codChart_mem_maximalAtlas
/-
**Manifold.LiftSourceTargetPropertyAt.source_subset_preimage_source** 是 Mathlib 
中的一个引理，位于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：source_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P)
 : h.domChart.source subseteq f ⁻¹' h.codChart.source
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.source_subset_preimage_source`：∀ {𝕜 : Type 
u_1} {E : Type u_2} {F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : Nontriv
iallyNormedField 𝕜]   [inst_1 : NormedAddCommGro…
-/
lemma source_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.localPresentationAt.source_subset_preimage_source
/-
**Manifold.LiftSourceTargetPropertyAt.property** 是 Mathlib 中的一个引理，位于命名空间 `Manifo
ld.LiftSourceTargetPropertyAt`。
形式化陈述：property (h : LiftSourceTargetPropertyAt I J n f x P) : P f h.domChart h.c
odChart
参数：h : LiftSourceTargetPropertyAt I J n f x P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.LocalPresentationAt.property`：∀ {𝕜 : Type u_1} {E : Type u_2} {
F : Type u_4} {H : Type u_6} {G : Type u_8} [inst : NontriviallyNormedField 𝕜]  
 [inst_1 : NormedAddCommGro…
-/
lemma property (h : LiftSourceTargetPropertyAt I J n f x P) : P f h.domChart h.codChart :=
  h.localPresentationAt.property

omit [ChartedSpace H M] [ChartedSpace G N] in
/-
**Manifold.LiftSourceTargetPropertyAt.congr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Manif
old.LiftSourceTargetPropertyAt`。
形式化陈述：congr_iff (hP : IsLocalSourceTargetProperty P) {f g : M -> N} {φ : OpenPar
tialHomeomorph M H} {ψ : OpenPartialHomeomorph N G} (hfg : EqOn f g φ.source) : 
P f φ ψ ↔ P g φ ψ
参数：hP : IsLocalSourceTargetProperty P；hfg : EqOn f g φ.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsLocalSourceTargetProperty.congr`：∀ {H : Type u_6} {G : Type u
_8} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace G] {M : Type u_10}   
{N : Type u_12} [inst_2 : Topolo…
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
lemma congr_iff (hP : IsLocalSourceTargetProperty P) {f g : M → N}
    {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G} (hfg : EqOn f g φ.source) :
    P f φ ψ ↔ P g φ ψ :=
  ⟨hP.congr hfg, hP.congr hfg.symm⟩

/-- If `P` is a local property, by monotonicity w.r.t. restricting `domChart`,
if `f` is continuous at `x`, to prove `LiftSourceTargetPropertyAt I I' n f x P`
we need not check the condition `f '' domChart.source ⊆ codChart.source`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.mk_of_continuousAt** 是 Mathlib 中的一个引理，位于命名
空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：mk_of_continuousAt (hf : ContinuousAt f x) (hP : IsLocalSourceTargetProper
ty P) (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N
 G) (hx : x in domChart.source) (hfx : f x in codChart.source) (hdomChart : domC
hart in IsManifold.maximalAtlas I n M) (hcodChart : codChart in IsManifold.maxim
alAtlas J n N) (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I J n 
f x P
参数：hf : ContinuousAt f x；hP : IsLocalSourceTargetProperty P；domChart : OpenParti
alHomeomorph M H；codChart : OpenPartialHomeomorph N G；hx : x in domChart.source；
hfx : f x in codChart.source；hdomChart : domChart in IsManifold.maximalAtlas I n
 M；hcodChart : codChart in IsManifold.maximalAtlas J n N；hfP : P f domChart codC
hart。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `restr_mem_maximalAtlas`：restr_mem_maximalAtlas [ClosedUnderRestriction G
] {e : OpenPartialHomeomorph M H} (he : e in G.maximalAtlas M) {s : Set M} (hs :
 IsOpen s) :…
· 使用定理 `instClosedUnderRestrictionContDiffGroupoid`：∀ {n : WithTop ℕ∞} {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace …
· 使用定理 `Manifold.IsLocalSourceTargetProperty.mono_source`：∀ {H : Type u_6} {G : 
Type u_8} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace G] {M : Type u_
10}   {N : Type u_12} [inst_2 : Topolo…

--- 原说明 ---
If `P` is a local property, by monotonicity w.r.t. restricting `domChart`,
if `f` is continuous at `x`, to prove `LiftSourceTargetPropertyAt I I' n f x P`
we need not check the condition `f '' domChart.source ⊆ codChart.source`.
-/
lemma mk_of_continuousAt (hf : ContinuousAt f x)
    (hP : IsLocalSourceTargetProperty P)
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I J n f x P := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind, hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart, by grind,
    hP.mono_source hsopen hfP⟩

/-- If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
if `f` has property `P` at `x` and `f` and `g` are eventually equal near `x`,
then `g` has property `P` at `x`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位
于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：congr_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (hf : LiftSourc
eTargetPropertyAt I J n f x P) (h' : f =ᶠ[nhds x] g) : LiftSourceTargetPropertyA
t I J n g x P
参数：hP : IsLocalSourceTargetProperty P；hf : LiftSourceTargetPropertyAt I J n f x 
P；h' : f =ᶠ[nhds x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.exists_mem`：∀ {α : Type u} {β : Type v} {l : Filter 
α} {f g : α → β}, f =ᶠ[l] g → ∃ s ∈ l, Set.EqOn f g s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_domChart_source`：mem_domChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : x in h.domChart.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_codChart_source`：mem_codChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : f x in h.codChart.source
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `restr_mem_maximalAtlas`：restr_mem_maximalAtlas [ClosedUnderRestriction G
] {e : OpenPartialHomeomorph M H} (he : e in G.maximalAtlas M) {s : Set M} (hs :
 IsOpen s) :…
· 使用定理 `instClosedUnderRestrictionContDiffGroupoid`：∀ {n : WithTop ℕ∞} {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace …
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.domChart in Is
Manifold.maximalAtlas I n M
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.codChart in Is
Manifold.maximalAtlas J n N
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
· 使用定理 `Set.EqOn.inter_preimage_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{f₁ f₂ : α → β},   Set.EqOn f₁ f₂ s → ∀ (t : Set β), s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Manifold.IsLocalSourceTargetProperty.congr`：∀ {H : Type u_6} {G : Type u
_8} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace G] {M : Type u_10}   
{N : Type u_12} [inst_2 : Topolo…
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Manifold.IsLocalSourceTargetProperty.mono_source`：∀ {H : Type u_6} {G : 
Type u_8} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace G] {M : Type u_
10}   {N : Type u_12} [inst_2 : Topolo…
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.property`：property (h : LiftSourceTa
rgetPropertyAt I J n f x P) : P f h.domChart h.codChart

--- 原说明 ---
If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
if `f` has property `P` at `x` and `f` and `g` are eventually equal near `x`,
then `g` has property `P` at `x`.
-/
lemma congr_of_eventuallyEq (hP : IsLocalSourceTargetProperty P)
    (hf : LiftSourceTargetPropertyAt I J n f x P)
    (h' : f =ᶠ[nhds x] g) : LiftSourceTargetPropertyAt I J n g x P := by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nhds hxs') ▸ mem_codChart_source hf
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hs
  · trans s' ∩ f ⁻¹' hf.codChart.source
    · apply subset_inter
      · exact Subset.trans (by simp [interior_eq_iff_isOpen.mpr hs]) hss'
      · exact Subset.trans (by simp) hf.source_subset_preimage_source
    · rw [hfg.inter_preimage_eq]; exact inter_subset_right
  · exact hP.congr (hfg.mono hss' |>.mono (by grind)) <| hP.mono_source hs hf.property

/-- If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
and `f` and `g` are eventually equal near `x`,
then `f` has property `P` at `x` if and only if `g` has property `P` at `x`. -/
/-
**Manifold.LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
形式化陈述：congr_iff_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[
nhds x] g) : LiftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTargetPropertyAt
 I J n g x P
参数：hP : IsLocalSourceTargetProperty P；h' : f =ᶠ[nhds x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`：congr_of_even
tuallyEq (hP : IsLocalSourceTargetProperty P) (hf : LiftSourceTargetPropertyAt I
 J n f x P) (h' : f =ᶠ[nhds x] g) : LiftSourceT…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
and `f` and `g` are eventually equal near `x`,
then `f` has property `P` at `x` if and only if `g` has property `P` at `x`.
-/
lemma congr_iff_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) :
    LiftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTargetPropertyAt I J n g x P :=
  ⟨fun hf ↦ hf.congr_of_eventuallyEq hP h', fun hg ↦ hg.congr_of_eventuallyEq hP h'.symm⟩

/- The set of points where `LiftSourceTargetPropertyAt` holds is open. -/
/-
**Manifold.LiftSourceTargetPropertyAt._root_.IsOpen.liftSourceTargetPropertyAt**
 是 Mathlib 中的一个引理，位于命名空间 `Manifold.LiftSourceTargetPropertyAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points where `LiftSourceTargetPropertyAt` holds is open.
-/
lemma _root_.IsOpen.liftSourceTargetPropertyAt :
    IsOpen {x | LiftSourceTargetPropertyAt I J n g x P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose the lifted property `P` holds at `x`:
  -- choose slice charts `φ` near `x` and `ψ` near `f x` s.t. `P f φ ψ` holds.
  -- Then the same charts witness that `P f φ ψ` holds at any `y ∈ φ.source`.
  refine ⟨hx.domChart.source, fun y hy ↦ ?_, hx.domChart.open_source, hx.mem_domChart_source⟩
  exact ⟨hx.domChart, hx.codChart, hy, hx.source_subset_preimage_source hy,
    hx.domChart_mem_maximalAtlas, hx.codChart_mem_maximalAtlas, hx.source_subset_preimage_source,
    hx.property⟩
/-
**Manifold.LiftSourceTargetPropertyAt.prodMap** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.LiftSourceTargetPropertyAt`。
形式化陈述：prodMap [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsMani
fold J' n N'] {Q : (M' -> N') -> OpenPartialHomeomorph M' H' -> OpenPartialHomeo
morph N' G' -> Prop} {R : ((M × M') -> (N × N')) -> OpenPartialHomeomorph (M × M
') (H × H') -> OpenPartialHomeomorph (N × N') (G × G') -> Prop} (hf : LiftSource
TargetPropertyAt I J n f x P) {g : M' -> N'} {x' : M'} (hg : LiftSourceTargetPro
pertyAt I' J' n g x' Q) (h : forall {f : M -> N}, forall {φ₁ : OpenPartialHomeom
orph M H}, forall {ψ₁ : Op
参数：M' -> N'；(M × M') -> (N × N')；M × M'；H × H'；N × N'；G × G'；hf : LiftSourceTarg
etPropertyAt I J n f x P；hg : LiftSourceTargetPropertyAt I' J' n g x' Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_domChart_source`：mem_domChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : x in h.domChart.source
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_codChart_source`：mem_codChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : f x in h.codChart.source
· 使用引理 `IsManifold.mem_maximalAtlas_prod`：mem_maximalAtlas_prod [IsManifold I n 
M] [IsManifold I' n M'] {e : OpenPartialHomeomorph M H} (he : e in maximalAtlas 
I n M) {e' : OpenParti…
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.domChart in Is
Manifold.maximalAtlas I n M
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.codChart in Is
Manifold.maximalAtlas J n N
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.property`：property (h : LiftSourceTa
rgetPropertyAt I J n f x P) : P f h.domChart h.codChart
-/
lemma prodMap [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    {Q : (M' → N') → OpenPartialHomeomorph M' H' → OpenPartialHomeomorph N' G' → Prop}
    {R : ((M × M') → (N × N')) → OpenPartialHomeomorph (M × M') (H × H') →
      OpenPartialHomeomorph (N × N') (G × G') → Prop}
    (hf : LiftSourceTargetPropertyAt I J n f x P) {g : M' → N'} {x' : M'}
    (hg : LiftSourceTargetPropertyAt I' J' n g x' Q)
    (h : ∀ {f : M → N}, ∀ {φ₁ : OpenPartialHomeomorph M H}, ∀ {ψ₁ : OpenPartialHomeomorph N G},
      ∀ {g : M' → N'}, ∀ {φ₂ : OpenPartialHomeomorph M' H'}, ∀ {ψ₂ : OpenPartialHomeomorph N' G'},
      P f φ₁ ψ₁ → Q g φ₂ ψ₂ → R (Prod.map f g) (φ₁.prod φ₂) (ψ₁.prod ψ₂)) :
    LiftSourceTargetPropertyAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') R := by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · apply IsManifold.mem_maximalAtlas_prod
      (codChart_mem_maximalAtlas hf) (codChart_mem_maximalAtlas hg)
  · simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph, PartialEquiv.prod_source,
      preimage_prod_map_prod]
    exact prod_mono hf.source_subset_preimage_source hg.source_subset_preimage_source
  · exact h hf.property hg.property

end LiftSourceTargetPropertyAt

end Manifold

