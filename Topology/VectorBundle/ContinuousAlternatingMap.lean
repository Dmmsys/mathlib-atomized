/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The vector bundle of continuous alternating multilinear maps

We define the topological vector bundle of continuous alternating maps
between two vector bundles over the same base.

Consider topological vector bundles with fibers `E₁ x`, `E₂ x`, `x : B`,
with model fibers `F₁` and `F₂`, and a finite index type `ι`.
If `F₁` and `F₂` are normed spaces over a nontrivially normed field `𝕜`,
then we define a vector bundle with fiber `E₁ x [⋀^ι]→L[𝕜] E₂ x`
with model fiber `F₁ [⋀^ι]→L[𝕜] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ [⋀^ι]→L[𝕜] F₂` using the `VectorPrebundle` construction.
-/

@[expose] public section


noncomputable section

open Bundle Set Topology
open scoped Bundle

/-!
### Continuous alternating map between fibers written in coordinates
-/

namespace ContinuousAlternatingMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B₁ : Type*} (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace B₁] [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {B₂ : Type*} (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace B₂] [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- When `ϕ` is a continuous alternating map
between the fibers `E₁ x` and `E₂ y` of two vector bundles `E` and `E'`,
`ContinuousAlternatingMap.inCoordinates F E F' E' x₀ x y₀ y ϕ`
is a coordinate change of this continuous linear map
w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes
given by the vector bundles `E₁` and `E₂`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousAlternatingMap.inCoordinates` is defined everywhere.
See also `ContinuousAlternatingMap.inCoordinates_eq`.

This is the (second component of the) underlying function
of a trivialization of the bundle of continuous alternating maps,
see `FiberBundle.trivializationAt_continuousAlternatingMap_apply`.

However, note that `ContinuousAlternatingMap.inCoordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the bundle of continuous alternating maps
between pulled back bundles.
-/
/-
**ContinuousAlternatingMap.inCoordinates** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：inCoordinates (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y) : F₁ [⋀^
ι]->L[𝕜] F₂
参数：x₀ x : B₁；y₀ y : B₂；ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `ϕ` is a continuous alternating map
between the fibers `E₁ x` and `E₂ y` of two vector bundles `E` and `E'`,
`ContinuousAlternatingMap.inCoordinates F E F' E' x₀ x y₀ y ϕ`
is a coordinate change of this continuous linear map
w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes
given by the vector bundles `E₁` and `E₂`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousAlternatingMap.inCoordinates` is defined everywhere.
See also `ContinuousAlternatingMap.inCoordinates_eq`.

This is the (second component of the) underlying function
of a trivialization of the bundle of continuous alternating maps,
see `FiberBundle.trivializationAt_continuousAlternatingMap_apply`.

However, note that `ContinuousAlternatingMap.inCoordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the bundle of continuous alte
rnating maps
between pulled back bundles.
-/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]→L[𝕜] E₂ y) :
    F₁ [⋀^ι]→L[𝕜] F₂ :=
  trivializationAt F₂ E₂ y₀ |>.continuousLinearMapAt 𝕜 y |>.compContinuousAlternatingMap
    ϕ |>.compContinuousLinearMap <| (trivializationAt F₁ E₁ x₀).symmL 𝕜 x

/-- Rewrite `ContinuousAlternatingMap.inCoordinates` using continuous linear equivalences. -/
/-
**ContinuousAlternatingMap.inCoordinates_eq** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlternatingMap`。
形式化陈述：inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y} (hx :
 x in (trivializationAt F₁ E₁ x₀).baseSet) (hy : y in (trivializationAt F₂ E₂ y₀
).baseSet) : inCoordinates F₁ F₂ x₀ x y₀ y ϕ = (((trivializationAt F₂ E₂ y₀).con
tinuousLinearEquivAt 𝕜 y hy : E₂ y ->L[𝕜] F₂) .compContinuousLinearMap .compCont
inuousAlternatingMap ϕ (((trivializationAt F₁ E₁ x₀).continuousLinearEquivAt 𝕜 x
 hx).symm : F₁ ->L[𝕜] E₁ x))
参数：hx : x in (trivializationAt F₁ E₁ x₀).baseSet；hy : y in (trivializationAt F₂ 
E₂ y₀).baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Rewrite `ContinuousAlternatingMap.inCoordinates` using continuous linear equival
ences.
-/
theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]→L[𝕜] E₂ y}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ =
      (((trivializationAt F₂ E₂ y₀).continuousLinearEquivAt 𝕜 y hy : E₂ y →L[𝕜] F₂)
        |>.compContinuousAlternatingMap ϕ |>.compContinuousLinearMap
          (((trivializationAt F₁ E₁ x₀).continuousLinearEquivAt 𝕜 x hx).symm : F₁ →L[𝕜] E₁ x)) := by
  ext
  simp [inCoordinates, *, Function.comp_def]

end ContinuousAlternatingMap

open ContinuousAlternatingMap (inCoordinates)

/-!
### Pretrivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable (𝕜 ι) in
/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂'`
is the coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂`
and `Pretrivialization.continuousAlternatingMap 𝕜 ι e₁' e₂'`
of the bundle of continuous alternating maps. -/
/-
**Bundle.Pretrivialization.continuousAlternatingMapCoordChange** 是 Mathlib 中的一个定
义，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousAlternatingMapCoordChange (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
 (e₂ e₂' : Trivialization F₂ (π F₂ E₂)) [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsL
inear 𝕜] [e₂'.IsLinear 𝕜] (b : B) : (F₁ [⋀^ι]->L[𝕜] F₂) ->L[𝕜] (F₁ [⋀^ι]->L[𝕜] F
₂)
参数：e₁ e₁' : Trivialization F₁ (π F₁ E₁)；e₂ e₂' : Trivialization F₂ (π F₂ E₂)；b :
 B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with
 fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e
₁ e₁' e₂ e₂'`
is the coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂`
and `Pretrivialization.continuousAlternatingMap 𝕜 ι e₁' e₂'`
of the bundle of continuous alternating maps.
-/
def continuousAlternatingMapCoordChange (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
  (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
/-
**Bundle.Pretrivialization.continuousOn_continuousAlternatingMapCoordChange** 是 
Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousOn_continuousAlternatingMapCoordChange [Finite ι] [VectorBundle 
𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] [MemTrivializationAtlas e₁] [MemTrivializationAt
las e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] : ContinuousOn
 (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂') (e₁.baseSet inter e₂.ba
seSet inter (e₁'.baseSet inter e₂'.baseSet))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `ContinuousOn.clm_comp`：ContinuousOn.clm_comp {g : X -> F ->L[𝕜] G} {f : 
X -> E ->L[𝕜] F} {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) : C
ontinuousOn…
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_coordChange`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3}
 {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → Add
CommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM`：continuo
us_compContinuousLinearMapCLM [Finite ι] : Continuous (compContinuousLinearMapCL
M : (E ->L[𝕜] F) -> (F [⋀^ι]->L[𝕜] G) ->L[𝕜] (E [⋀^ι…
-/
theorem continuousOn_continuousAlternatingMapCoordChange
    [Finite ι]
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  cases nonempty_fintype ι
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · refine map_continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := ι) 𝕜 F₁ F₂ F₂)
      |>.comp_continuousOn ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)
    mfld_set_tac
  · refine ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn ?_
    exact continuousOn_coordChange 𝕜 e₁' e₁ |>.mono (by mfld_set_tac)

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

variable (𝕜 ι e₁ e₁' e₂ e₂') in
/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
/-
**Bundle.Pretrivialization.continuousAlternatingMap** 是 Mathlib 中的一个定义，位于命名空间 `B
undle.Pretrivialization`。
形式化陈述：continuousAlternatingMap : Pretrivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [⋀
^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂` is the induced pretrivial
ization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will la
ter become a
trivialization, after the bundle of continuous semilinear maps is equipped with 
the right
topological vector bundle structure.
-/
def continuousAlternatingMap :
    Pretrivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) where
  toFun p := ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
    p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩
  invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
    p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := by
    rintro ⟨x, L⟩ ⟨h₁, h₂⟩
    simp only [TotalSpace.mk_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  right_inv' := by
    rintro ⟨x, f⟩ ⟨⟨h₁, h₂⟩, -⟩
    simp only [Prod.mk_right_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl
/-
**Bundle.Pretrivialization.continuousAlternatingMap.isLinear** 是 Mathlib 中的一个定理，
位于命名空间 `Bundle.Pretrivialization.continuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u_1} {ι : Type u_2} [inst : NontriviallyNormedField 𝕜] {B : Ty
pe u_3} [inst_1 : TopologicalSpace B]   {F₁ : Type u_4} [inst_2 : NormedAddCommG
roup F₁] [inst_3 : NormedSpace 𝕜 F₁] {E₁ : B → Type u_5}   [inst_4 : (x : B) → A
ddCommGroup (E₁ x)] [inst_5 : (x : B) → _root_.Module 𝕜 (E₁ x)]   [inst_6 : Topo
logicalSpace (Bundle.TotalSpace F₁ E₁)] {F₂ : Type u_6} [inst_7 : NormedAddCommG
roup F₂]   [inst_8 : NormedSpace 𝕜 F₂] {E₂ : B → Type u_7} [inst_9 : (x : B) → A
ddCommGroup (E₂ x)]   [inst_10 : (x : B) → _root_.Module 𝕜 (E₂ x)] [inst_11 : To
pologicalSpace (Bundle.TotalSpace F₂ E₂)]   [inst_12 : (x : B) → TopologicalSpac
e (E₁ x)] [inst_13 : FiberBundle F₁ E₁]   [inst_14 : (x : B) → TopologicalSpace 
(E₂ x)] [inst_15 : FiberBundle F₂ E₂]   {e₁ : Bundle.Trivialization F₁ Bundle.To
talSpace.proj} {e₂ : Bundle.Trivialization F₂ Bundle.TotalSpace.proj}   [inst_16
 : Bundle.Trivialization.IsLinear 𝕜 e₁] [inst_17 : Bundle.Trivialization.IsLinea
r 𝕜 e₂]   [inst_18 : ∀ (x : B), ContinuousAdd (E₂ x)] [inst_19 : ∀ (x : B), Cont
inuousSMul 𝕜 (E₂ x)],   Bundle.Pretrivialization.IsLinear 𝕜 (Bundle.Pretrivializ
ation.continuousAlternatingMap 𝕜 ι e₁ e₂)
参数：x : B；E₁ x；x : B；E₁ x；Bundle.TotalSpace F₁ E₁；x : B；E₂ x；x : B；E₂ x；Bundle.To
talSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；x : B；E₂ x；x : B；E₂ x；Bundle.Pretrivializat
ion.continuousAlternatingMap 𝕜 ι e₁ e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
instance continuousAlternatingMap.isLinear
    [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
    { map_add L L' := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun'] }
/-
**Bundle.Pretrivialization.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命
名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousAlternatingMap_apply (p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) fun x =
> E₁ x [⋀^ι]->L[𝕜] E₂ x) : continuousAlternatingMap 𝕜 ι e₁ e₂ p = ⟨p.1, (e₂.cont
inuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap p.2.compContinuousLinearMa
p e₁.symmL 𝕜 p.1⟩
参数：p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) :
    continuousAlternatingMap 𝕜 ι e₁ e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl
/-
**Bundle.Pretrivialization.continuousAlternatingMap_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]->L[𝕜] F₂)) : (conti
nuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p = ⟨p.1, (e₂.symmL 𝕜 p.1).co
mpContinuousAlternatingMap p.2.compContinuousLinearMap e₁.continuousLinearMapAt 
𝕜 p.1⟩
参数：p : B × (F₁ [⋀^ι]->L[𝕜] F₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl
/-
**Bundle.Pretrivialization.continuousAlternatingMap_symm_apply'** 是 Mathlib 中的一个
定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousAlternatingMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e
₂.baseSet) (L : F₁ [⋀^ι]->L[𝕜] F₂) : (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b
 L = ((e₂.symmL 𝕜 b).compContinuousAlternatingMap <| L.compContinuousLinearMap e
₁.continuousLinearMapAt 𝕜 b)
参数：hb : b in e₁.baseSet inter e₂.baseSet；L : F₁ [⋀^ι]->L[𝕜] F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_coe_proj`：symm_coe_proj {x : B} {y : F} (e
' : Pretrivialization F (π F E)) (h : x in e'.baseSet) : (e'.toPartialEquiv.symm
 (x, y)).1 = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_apply`：symm_apply (e : Pretrivialization F
 (π F E)) {b : B} (hb : b in e.baseSet) (y : F) : e.symm b y = cast (congr_arg E
 (e.symm_coe_proj hb)) (e…
-/
theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L =
      ((e₂.symmL 𝕜 b).compContinuousAlternatingMap <|
        L.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 b) := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb
/-
**Bundle.Pretrivialization.continuousAlternatingMapCoordChange_apply** 是 Mathlib
 中的一个定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousAlternatingMapCoordChange_apply (b : B) (hb : b in e₁.baseSet in
ter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) (L : F₁ [⋀^ι]->L[𝕜] F₂) : 
continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L = (continuousAlternati
ngMap 𝕜 ι e₁' e₂' ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2
参数：b : B；hb : b in e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.base
Set)；L : F₁ [⋀^ι]->L[𝕜] F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.continuousAlternatingMapCongr_apply`：∀ {𝕜 : Type u
_1} {E : Type u_2} {E' : Type u_3} {F : Type u_4} {G : Type u_5} {ι : Type u_6} 
[inst : NormedField 𝕜]   [inst_1 : AddCommGroup…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Bundle.Pretrivialization.continuousAlternatingMap_symm_apply'`：continuou
sAlternatingMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e₂.baseSet) (L :
 F₁ [⋀^ι]->L[𝕜] F₂) : (continuousAlternatingMap 𝕜 ι…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem continuousAlternatingMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
      (continuousAlternatingMap 𝕜 ι e₁' e₂'
        ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousAlternatingMapCoordChange, continuousAlternatingMap_apply,
    Function.comp_def, Trivialization.coordChangeL_apply,
    continuousAlternatingMap_symm_apply' hb.left, hb]

end Bundle.Pretrivialization

/-!
### Vector (pre)bundle structure
-/

namespace Bundle.ContinuousAlternatingMap

open Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable (𝕜 ι F₁ E₁ F₂ E₂) in
/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
/-
**Bundle.ContinuousAlternatingMap.vectorPrebundle** 是 Mathlib 中的一个定义，位于命名空间 `Bun
dle.ContinuousAlternatingMap`。
形式化陈述：vectorPrebundle : VectorPrebundle 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^
ι]->L[𝕜] E₂ x) where pretrivializationAtlas
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no top
ology
on the total space is yet provided).
-/
def vectorPrebundle :
    VectorPrebundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousAlternatingMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousAlternatingMapCoordChange,
      continuousAlternatingMapCoordChange_apply⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, continuousAlternatingMap_apply, isInducing_const_prod]
    let L₁ : E₁ b ≃L[𝕜] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    convert! (L₁.continuousAlternatingMapCongr L₂).toHomeomorph.isInducing
    ext f
    simp [Trivialization.linearMapAt_def_of_mem _ (mem_baseSet_trivializationAt _ _ _), L₁, L₂,
      Function.comp_def, mem_baseSet_trivializationAt]

/-- Topology on the total space of the continuous `σ`-semilinear maps between two "normable" vector
bundles over the same base. -/
/-
**Bundle.ContinuousAlternatingMap.instTopologicalSpaceTotalSpace** 是 Mathlib 中的一
个实例，位于命名空间 `Bundle.ContinuousAlternatingMap`。
形式化陈述：instTopologicalSpaceTotalSpace : TopologicalSpace (TotalSpace (F₁ [⋀^ι]->L
[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on the total space of the continuous `σ`-semilinear maps between two "n
ormable" vector
bundles over the same base.
-/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `σ`-semilinear maps between two vector bundles form a fiber bundle. -/
/-
**Bundle.ContinuousAlternatingMap.instFiberBundle** 是 Mathlib 中的一个实例，位于命名空间 `Bun
dle.ContinuousAlternatingMap`。
形式化陈述：instFiberBundle : FiberBundle (F₁ [⋀^ι]->L[𝕜] F₂) fun x => E₁ x [⋀^ι]->L[𝕜
] E₂ x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `σ`-semilinear maps between two vector bundles form a fiber bundl
e.
-/
instance instFiberBundle :
    FiberBundle (F₁ [⋀^ι]→L[𝕜] F₂) fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous `σ`-semilinear maps between two vector bundles form a vector bundle. -/
/-
**Bundle.ContinuousAlternatingMap.instVectorBundle** 是 Mathlib 中的一个实例，位于命名空间 `Bu
ndle.ContinuousAlternatingMap`。
形式化陈述：instVectorBundle : VectorBundle 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]
->L[𝕜] E₂ x)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.toVectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B)
 → AddCommMonoid (E …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
The continuous `σ`-semilinear maps between two vector bundles form a vector bund
le.
-/
instance instVectorBundle : VectorBundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

end Bundle.ContinuousAlternatingMap

/-!
### Trivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Trivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

variable (𝕜 ι e₁ e₂) in
/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
/-
**Bundle.Trivialization.continuousAlternatingMap** 是 Mathlib 中的一个定义，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：continuousAlternatingMap : Trivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [⋀^ι]
->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over
 a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `
E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`.
-/
def continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩
/-
**Bundle.Trivialization.memTrivializationAtlas_continuousAlternatingMap** 是 Math
lib 中的一个实例，位于命名空间 `Bundle.Trivialization`。
形式化陈述：memTrivializationAtlas_continuousAlternatingMap : MemTrivializationAtlas (
e₁.continuousAlternatingMap 𝕜 ι e₂ : Trivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [
⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
instance memTrivializationAtlas_continuousAlternatingMap :
    MemTrivializationAtlas
      (e₁.continuousAlternatingMap 𝕜 ι e₂ :
        Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x))) :=
  ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]
/-
**Bundle.Trivialization.baseSet_continuousAlternatingMap** 是 Mathlib 中的一个定理，位于命名
空间 `Bundle.Trivialization`。
形式化陈述：baseSet_continuousAlternatingMap : (e₁.continuousAlternatingMap 𝕜 ι e₂).ba
seSet = e₁.baseSet inter e₂.baseSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl
/-
**Bundle.Trivialization.continuousAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间
 `Bundle.Trivialization`。
形式化陈述：continuousAlternatingMap_apply (p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x 
=> E₁ x [⋀^ι]->L[𝕜] E₂ x)) : e₁.continuousAlternatingMap 𝕜 ι e₂ p = .compContinu
ousAlternatingMap p.2 ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1 : _ ->L[𝕜] _) .compC
ontinuousLinearMap (e₁.symmL 𝕜 p.1 : F₁ ->L[𝕜] E₁ p.1)⟩
参数：p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1 : _ →L[𝕜] _) |>.compContinuousAlternatingMap p.2
        |>.compContinuousLinearMap (e₁.symmL 𝕜 p.1 : F₁ →L[𝕜] E₁ p.1)⟩ :=
  rfl

end Bundle.Trivialization

/-!
### Lemmas about `trivializationAt` for the bundle of continuous alternating maps
-/

namespace FiberBundle

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-
**FiberBundle.trivializationAt_continuousAlternatingMap** 是 Mathlib 中的一个定理，位于命名空
间 `FiberBundle`。
形式化陈述：trivializationAt_continuousAlternatingMap (x₀ : B) : trivializationAt (F₁ 
[⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀ = (trivializationAt F₁ E₁ x₀
).continuousAlternatingMap 𝕜 ι (trivializationAt F₂ E₂ x₀)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem trivializationAt_continuousAlternatingMap (x₀ : B) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousAlternatingMap 𝕜 ι (trivializationAt F₂ E₂ x₀) := rfl
/-
**FiberBundle.trivializationAt_continuousAlternatingMap_apply** 是 Mathlib 中的一个定理
，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt_continuousAlternatingMap_apply (x₀ : B) (x : TotalSpace (
F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) : trivializationAt (F₁ [⋀^ι
]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀ x = ⟨x.1, inCoordinates F₁ F₂ x₀
 x.1 x₀ x.1 x.2⟩
参数：x₀ : B；x : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem trivializationAt_continuousAlternatingMap_apply (x₀ : B)
    (x : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ F₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundle.trivializationAt_continuousAlternatingMap_source** 是 Mathlib 中的一个定
理，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt_continuousAlternatingMap_source (x₀ : B) : (trivializatio
nAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).source = π (F₁ [⋀^ι
]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) ⁻¹' ((trivializationAt F₁ E₁ x₀).ba
seSet inter (trivializationAt F₂ E₂ x₀).baseSet)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem trivializationAt_continuousAlternatingMap_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).source =
      π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundle.trivializationAt_continuousAlternatingMap_target** 是 Mathlib 中的一个定
理，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt_continuousAlternatingMap_target (x₀ : B) : (trivializatio
nAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).target = ((triviali
zationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.uni
v
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem trivializationAt_continuousAlternatingMap_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
/-
**FiberBundle.trivializationAt_continuousAlternatingMap_baseSet** 是 Mathlib 中的一个
定理，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt_continuousAlternatingMap_baseSet (x₀ : B) : (trivializati
onAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).baseSet = ((trivia
lizationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem trivializationAt_continuousAlternatingMap_baseSet (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

end FiberBundle

/-!
### Continuity of maps to the total space of the bundle of continuous alternating maps
-/

section Continuity

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x₀ : X}


/-
**continuousWithinAt_continuousAlternatingMap_bundle** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：continuousWithinAt_continuousAlternatingMap_bundle (f : X -> TotalSpace (F
₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) : ContinuousWithinAt f s x₀ 
↔ ContinuousWithinAt (fun x => (f x).1) s x₀ ∧ ContinuousWithinAt (fun x => inCo
ordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀
参数：f : X -> TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuousWithinAt_totalSpace`：continuousWithinAt_totalSpace
 (f : X -> TotalSpace F E) {s : Set X} {x₀ : X} : ContinuousWithinAt f s x₀ ↔ Co
ntinuousWithinAt (fun x => (f x…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousWithinAt_continuousAlternatingMap_bundle
    (f : X → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..
/-
**continuousAt_continuousAlternatingMap_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_continuousAlternatingMap_bundle (f : X -> TotalSpace (F₁ [⋀^ι
]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) : ContinuousAt f x₀ ↔ ContinuousAt
 (fun x => (f x).1) x₀ ∧ ContinuousAt (fun x => inCoordinates F₁ F₂ (f x₀).1 (f 
x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : X -> TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuousAt_totalSpace`：continuousAt_totalSpace (f : X -> T
otalSpace F E) {x₀ : X} : ContinuousAt f x₀ ↔ ContinuousAt (fun x => (f x).proj)
 x₀ ∧ ContinuousAt (fun x…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousAt_continuousAlternatingMap_bundle
    (f : X → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).1) x₀ ∧
        ContinuousAt
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

end Continuity

end

