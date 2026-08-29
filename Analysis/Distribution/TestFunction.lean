/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Continuously differentiable functions with compact support

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with compact support contained in some open set `Ω`. More explicitly, given normed spaces `E`
and `F`, an open set `Ω : Opens E` and `n : ℕ∞`, we are interested in the space `𝓓^{n}(Ω, F)` of
maps `f : E → F` such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` has compact support: `HasCompactSupport f`.
- the support of `f` is inside the open set `Ω`: `tsupport f ⊆ Ω`.

This exists as a bundled type to equip it with the canonical LF topology induced by the inclusions
`𝓓_{K}^{n}(Ω, F) → 𝓓^{n}(Ω, F)` (see `ContDiffMapSupportedIn`). The dual space is then the space of
distributions, or "weak solutions" to PDEs, on `Ω`.

## Main definitions

- `TestFunction Ω F n`: the type of bundled `n`-times continuously differentiable
  functions `E → F` with compact support contained in `Ω`.
- `TestFunction.topologicalSpace`: the canonical LF topology on `𝓓^{n}(Ω, F)`. It is the
  locally convex inductive limit of the topologies on each `𝓓_{K}^{n}(Ω, F)`.

## Main statements

- `TestFunction.continuous_iff_continuous_comp`: a linear map from `𝓓^{n}(E, F)`
  to a locally convex space is continuous iff its restriction to `𝓓^{n}_{K}(E, F)` is
  continuous for each compact set `K`. We will later translate this concretely in terms
  of seminorms.

## Notation

- `𝓓^{n}(Ω, F)`: the space of bundled `n`-times continuously differentiable functions `E → F`
  with compact support contained in `Ω`.
- `𝓓(Ω, F)`: the space of bundled smooth (infinitely differentiable) functions `E → F`
  with compact support contained in `Ω`, i.e. `𝓓^{⊤}(Ω, F)`.

## Tags

distributions, test function
-/

@[expose] public section

open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace
open scoped BoundedContinuousFunction NNReal Topology ContDiff

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {Ω Ω₁ Ω₂ : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace Real F'] [NormedSpace 𝕜 F']
  {n n₁ n₂ k : Nat∞}

variable (Ω F n) in
/--
Definition of `TestFunction` / `TestFunction` 的定义

English:
structure TestFunction
  parameters: : Type _ where
  axioms and operations (4):
    - toFun : E -> F
    - contDiff' : ContDiff Real n toFun
    - hasCompactSupport' : HasCompactSupport toFun
    - tsupport_subset' : tsupport toFun subseteq Ω

中文:
结构 测试函数
  参数: : 类型 _ where
  公理与运算 (4 个):
    - toFun : E -> F
    - contDiff' : 连续可微 实数 n toFun
    - hasCompactSupport' : HasCompactSupport toFun
    - tsupport_subset' : tsupport toFun subseteq Ω
-/
structure TestFunction : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E -> F
  protected contDiff' : ContDiff Real n toFun
  protected hasCompactSupport' : HasCompactSupport toFun
  protected tsupport_subset' : tsupport toFun subseteq Ω

/-- Notation for the space of bundled `n`-times continuously differentiable maps
with compact support. -/
scoped[Distributions] notation "𝓓^{" n "}(" Ω ", " F ")" => TestFunction Ω F n

/-- Notation for the space of "test functions", i.e. bundled smooth (infinitely differentiable) maps
with compact support. -/
scoped[Distributions] notation "𝓓(" Ω ", " F ")" => TestFunction Ω F ⊤

open Distributions

/--
Definition of `TestFunctionClass` / `TestFunctionClass` 的定义

English:
class TestFunctionClass
  parameters: (B : Type*)
  extends: FunLike B E F
  axioms and operations (3):
    - map_contDiff((f : B)) : ContDiff Real n f
    - map_hasCompactSupport((f : B)) : HasCompactSupport f
    - tsupport_map_subset((f : B)) : tsupport f subseteq Ω

中文:
类 测试函数类
  参数: (B : 类型)
  继承: 函数状 B E F
  公理与运算 (3 个):
    - map_contDiff((f : B)) : 连续可微 实数 n f
    - map_hasCompactSupport((f : B)) : HasCompactSupport f
    - tsupport_map_subset((f : B)) : tsupport f subseteq Ω
-/
class TestFunctionClass (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace Real E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace Real F]
    (n : outParam Nat∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff Real n f
  map_hasCompactSupport (f : B) : HasCompactSupport f
  tsupport_map_subset (f : B) : tsupport f subseteq Ω

open TestFunctionClass

namespace TestFunctionClass

instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace Real E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace Real F]
    (n : outParam Nat∞) [TestFunctionClass B Ω F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace Real E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace Real F]
    (n : outParam Nat∞) [TestFunctionClass B Ω F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support (map_hasCompactSupport f)
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end TestFunctionClass

namespace TestFunction

/--
Instance `toTestFunctionClass` / 实例 `toTestFunctionClass`

English:
instance toTestFunctionClass
  signature: : TestFunctionClass 𝓓^{n}(Ω, F) Ω F n where
  body: f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_hasCompactSupport f := f.hasCompactSupport'
  tsupport_map_subset f := f.tsupport_subset'

中文:
实例 toTestFunctionClass
  签名: : 测试函数类 𝓓^{n}(Ω, F) Ω F n where
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_hasCompactSupport f := f.hasCompactSupport'
  tsupport_map_subset f := f.tsupport_subset'

Depends on / 依赖: f.toFun
-/
instance toTestFunctionClass : TestFunctionClass 𝓓^{n}(Ω, F) Ω F n where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_hasCompactSupport f := f.hasCompactSupport'
  tsupport_map_subset f := f.tsupport_subset'

/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: (f : 𝓓^{n}(Ω, F))
  statement: ContDiff Real n f
  proof: map_contDiff f

中文:
定理 contDiff
  条件: (f : 𝓓^{n}(Ω, F))
  结论: 连续可微 实数 n f
  证明: map_contDiff f
-/
protected theorem contDiff (f : 𝓓^{n}(Ω, F)) : ContDiff Real n f := map_contDiff f
/--
theorem `hasCompactSupport` / 定理 `hasCompactSupport`

English:
theorem hasCompactSupport
  given: (f : 𝓓^{n}(Ω, F))
  statement: HasCompactSupport f
  proof: map_hasCompactSupport f

中文:
定理 hasCompactSupport
  条件: (f : 𝓓^{n}(Ω, F))
  结论: HasCompactSupport f
  证明: map_hasCompactSupport f
-/
protected theorem hasCompactSupport (f : 𝓓^{n}(Ω, F)) : HasCompactSupport f :=
  map_hasCompactSupport f
/--
theorem `tsupport_subset` / 定理 `tsupport_subset`

English:
theorem tsupport_subset
  given: (f : 𝓓^{n}(Ω, F))
  statement: tsupport f subseteq Ω
  proof: tsupport_map_subset f

@[fun_prop]

中文:
定理 tsupport_subset
  条件: (f : 𝓓^{n}(Ω, F))
  结论: tsupport f subseteq Ω
  证明: tsupport_map_subset f

@[fun_prop]
-/
protected theorem tsupport_subset (f : 𝓓^{n}(Ω, F)) : tsupport f subseteq Ω := tsupport_map_subset f

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : 𝓓^{n}(Ω, F))
  statement: Continuous f
  proof: f.contDiff.continuous

@[simp]

中文:
定理 continuous
  条件: (f : 𝓓^{n}(Ω, F))
  结论: 连续 f
  证明: f.contDiff.continuous

@[simp]
-/
protected theorem continuous (f : 𝓓^{n}(Ω, F)) : Continuous f :=
  f.contDiff.continuous

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : 𝓓^{n}(Ω, F)}
  statement: f.toFun = (f : E -> F)
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: {f : 𝓓^{n}(Ω, F)}
  结论: f.toFun = (f : E -> F)
  证明: rfl
-/
theorem toFun_eq_coe {f : 𝓓^{n}(Ω, F)} : f.toFun = (f : E -> F) :=
  rfl

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (f : 𝓓^{n}(Ω, F))
  body: f

initialize_simps_projections TestFunction (toFun -> coe, as_prefix coe)

@[ext]

中文:
定义 Simps.coe
  签名: (f : 𝓓^{n}(Ω, F))
  定义体: f

initialize_simps_projections TestFunction (toFun -> coe, as_prefix coe)

@[ext]
-/
def Simps.coe (f : 𝓓^{n}(Ω, F)) : E -> F := f

initialize_simps_projections TestFunction (toFun -> coe, as_prefix coe)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : 𝓓^{n}(Ω, F)} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  body: f'
  contDiff' := h.symm ▸ f.contDiff
  hasCompactSupport' := h.symm ▸ f.hasCompactSupport
  tsupport_subset' := h.symm ▸ f.tsupport_subset

@[simp]

中文:
定义 copy
  签名: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  定义体: f'
  contDiff' := h.symm ▸ f.contDiff
  hasCompactSupport' := h.symm ▸ f.hasCompactSupport
  tsupport_subset' := h.symm ▸ f.tsupport_subset

@[simp]
-/
protected def copy (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f) : 𝓓^{n}(Ω, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  hasCompactSupport' := h.symm ▸ f.hasCompactSupport
  tsupport_subset' := h.symm ▸ f.tsupport_subset

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_toBoundedContinuousFunction` / 定理 `coe_toBoundedContinuousFunction`

English:
theorem coe_toBoundedContinuousFunction
  given: (f : 𝓓^{n}(Ω, F))
  proof: rfl

@[simp]

中文:
定理 coe_toBoundedContinuousFunction
  条件: (f : 𝓓^{n}(Ω, F))
  证明: rfl

@[simp]
-/
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}(Ω, F)) :
    (f : BoundedContinuousFunction E F) = (f : E -> F) := rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  statement: {f : E -> F} {contDiff : ContDiff Real n f} {hasCompactSupport : HasCompactSupport f}
  proof: rfl

中文:
定理 coe_mk
  结论: {f : E -> F} {contDiff : 连续可微 实数 n f} {hasCompactSupport : HasCompactSupport f}
  证明: rfl
-/
theorem coe_mk {f : E -> F} {contDiff : ContDiff Real n f} {hasCompactSupport : HasCompactSupport f}
    {tsupport_subset : tsupport f subseteq Ω} :
    TestFunction.mk f contDiff hasCompactSupport tsupport_subset = f :=
  rfl

section AddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero 𝓓^{n}(Ω, F)
  body: ⟨0, contDiff_zero_fun, .zero, by simp only [tsupport_zero, empty_subset]⟩

中文:
实例 :
  签名: 零 𝓓^{n}(Ω, F)
  定义体: ⟨0, contDiff_zero_fun, .zero, by simp only [tsupport_zero, empty_subset]⟩

Depends on / 依赖: contDiff_zero_fun, empty_subset, tsupport_zero
-/
instance : Zero 𝓓^{n}(Ω, F) where
  zero := ⟨0, contDiff_zero_fun, .zero, by simp only [tsupport_zero, empty_subset]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply 𝓓^{n}(Ω, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero

中文:
实例 :
  签名: 是ZeroApply 𝓓^{n}(Ω, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero
-/
instance : IsZeroApply 𝓓^{n}(Ω, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add 𝓓^{n}(Ω, F)
  body: ⟨f + g, f.contDiff.add g.contDiff, f.hasCompactSupport.add g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_add f g

中文:
实例 :
  签名: 加法 𝓓^{n}(Ω, F)
  定义体: ⟨f + g, f.contDiff.add g.contDiff, f.hasCompactSupport.add g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_add f g

Depends on / 依赖: contDiff, f.contDiff.add, f.hasCompactSupport.add, g.contDiff, g.hasCompactSupport, hasCompactSupport
-/
instance : Add 𝓓^{n}(Ω, F) where
  add f g := ⟨f + g, f.contDiff.add g.contDiff, f.hasCompactSupport.add g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_add f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply 𝓓^{n}(Ω, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add

中文:
实例 :
  签名: 是加法Apply 𝓓^{n}(Ω, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add
-/
instance : IsAddApply 𝓓^{n}(Ω, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg 𝓓^{n}(Ω, F)
  body: ⟨-f, f.contDiff.neg, f.hasCompactSupport.neg, tsupport_neg f ▸ f.tsupport_subset⟩

中文:
实例 :
  签名: 取负 𝓓^{n}(Ω, F)
  定义体: ⟨-f, f.contDiff.neg, f.hasCompactSupport.neg, tsupport_neg f ▸ f.tsupport_subset⟩

Depends on / 依赖: contDiff, f.contDiff.neg, f.hasCompactSupport.neg, f.tsupport_subset, hasCompactSupport, tsupport_neg, tsupport_subset
-/
instance : Neg 𝓓^{n}(Ω, F) where
  neg f := ⟨-f, f.contDiff.neg, f.hasCompactSupport.neg, tsupport_neg f ▸ f.tsupport_subset⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply 𝓓^{n}(Ω, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg

中文:
实例 :
  签名: 是NegApply 𝓓^{n}(Ω, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg
-/
instance : IsNegApply 𝓓^{n}(Ω, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub 𝓓^{n}(Ω, F)
  body: ⟨f - g, f.contDiff.sub g.contDiff, f.hasCompactSupport.sub g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_sub f g

中文:
实例 :
  签名: 减法 𝓓^{n}(Ω, F)
  定义体: ⟨f - g, f.contDiff.sub g.contDiff, f.hasCompactSupport.sub g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_sub f g

Depends on / 依赖: contDiff, f.contDiff.sub, f.hasCompactSupport.sub, g.contDiff, g.hasCompactSupport, hasCompactSupport
-/
instance : Sub 𝓓^{n}(Ω, F) where
  sub f g := ⟨f - g, f.contDiff.sub g.contDiff, f.hasCompactSupport.sub g.hasCompactSupport,
.trans union_subset f.tsupport_subset g.tsupport_subset⟩ tsupport_sub f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply 𝓓^{n}(Ω, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub

中文:
实例 :
  签名: 是SubApply 𝓓^{n}(Ω, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub
-/
instance : IsSubApply 𝓓^{n}(Ω, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub

instance {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}(Ω, F) where
  smul c f := ⟨c • f, f.contDiff.const_smul c, f.hasCompactSupport.smul_left,
.trans f.tsupport_subset⟩ tsupport_smul_subset_right _ _

instance {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    IsSMulApply R 𝓓^{n}(Ω, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_smul := FunLike.coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup 𝓓^{n}(Ω, F)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

中文:
实例 :
  签名: 加法交换群 𝓓^{n}(Ω, F)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup 𝓓^{n}(Ω, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(Ω, F) := fast_instance% FunLike.module

instance {R S} [Semiring R] [Semiring S] [Module R F] [Module S F] [SMulCommClass Real R F]
    [SMulCommClass Real S F] [ContinuousConstSMul R F] [ContinuousConstSMul S F] [SMul R S]
    [IsScalarTower R S F] :
    IsScalarTower R S 𝓓^{n}(Ω, F) := FunLike.isScalarTower

end Module

open ContDiffMapSupportedIn

/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` when `K ⊆ Ω`. -/
@[simps -fullyApplied]
/--
Definition of `ofSupportedIn` / `ofSupportedIn` 的定义

English:
definition ofSupportedIn
  signature: {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω) (f : 𝓓^{n}_{K}(E, F))
  body: ⟨f, f.contDiff, f.compact_supp, f.tsupport_subset.trans K_sub_Ω⟩

中文:
定义 ofSupportedIn
  签名: {K : 余mpacts E} (K_sub_Ω : (K : 集合 E) subseteq Ω) (f : 𝓓^{n}_{K}(E, F))
  定义体: ⟨f, f.contDiff, f.compact_supp, f.tsupport_subset.trans K_sub_Ω⟩

Depends on / 依赖: compact_supp, contDiff, f.compact_supp, f.contDiff, f.tsupport_subset.trans, tsupport_subset
-/
def ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n}(Ω, F) :=
  ⟨f, f.contDiff, f.compact_supp, f.tsupport_subset.trans K_sub_Ω⟩

section Topology

variable {V : Type*} [AddCommGroup V] [Module Real V] [t : TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul Real V] [LocallyConvexSpace Real V]

variable (Ω F n) in
/-- The "original topology" on `𝓓^{n}(Ω, F)`, defined as the supremum over all compacts `K ⊆ Ω` of
the topology on `𝓓^{n}_{K}(E, F)`. In other words, this topology makes `𝓓^{n}(Ω, F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of topological spaces**.

Note that this has no reason to be a locally convex (or even vector space) topology. For this
reason, we actually endow `𝓓^{n}(Ω, F)` with another topology, namely the finest locally convex
topology which is coarser than this original topology. See `TestFunction.topologicalSpace`. -/
@[instance_reducible]
/--
Definition of `originalTop` / `originalTop` 的定义

English:
definition originalTop
  signature: : TopologicalSpace 𝓓^{n}(Ω, F)
  body: ⨆ (K : Compacts E) (K_sub_Ω : (K : Set E) subseteq Ω),
    coinduced (ofSupportedIn K_sub_Ω) ContDiffMapSupportedIn.topologicalSpace

中文:
定义 originalTop
  签名: : 拓扑空间 𝓓^{n}(Ω, F)
  定义体: ⨆ (K : Compacts E) (K_sub_Ω : (K : Set E) subseteq Ω),
    coinduced (ofSupportedIn K_sub_Ω) ContDiffMapSupportedIn.topologicalSpace

Depends on / 依赖: Compacts, ContDiffMapSupportedIn, ContDiffMapSupportedIn.topologicalSpace, coinduced, ofSupportedIn, subseteq, topologicalSpace
-/
noncomputable def originalTop : TopologicalSpace 𝓓^{n}(Ω, F) :=
  ⨆ (K : Compacts E) (K_sub_Ω : (K : Set E) subseteq Ω),
    coinduced (ofSupportedIn K_sub_Ω) ContDiffMapSupportedIn.topologicalSpace

variable (Ω F n) in
/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: : TopologicalSpace 𝓓^{n}(Ω, F)
  body: sInf {t : TopologicalSpace 𝓓^{n}(Ω, F) | originalTop Ω F n <= t ∧
    @IsTopologicalAddGroup 𝓓^{n}(Ω, F) t _ ∧
    @ContinuousSMul Real 𝓓^{n}(Ω, F) _ _ t ∧
    @LocallyConvexSpace Real 𝓓^{n}(Ω, F) _ _ _ _ t}

中文:
实例 topologicalSpace
  签名: : 拓扑空间 𝓓^{n}(Ω, F)
  定义体: sInf {t : TopologicalSpace 𝓓^{n}(Ω, F) | originalTop Ω F n <= t ∧
    @IsTopologicalAddGroup 𝓓^{n}(Ω, F) t _ ∧
    @ContinuousSMul Real 𝓓^{n}(Ω, F) _ _ t ∧
    @LocallyConvexSpace Real 𝓓^{n}(Ω, F) _ _ _ _ t}

Depends on / 依赖: ContinuousSMul, IsTopologicalAddGroup, LocallyConvexSpace, TopologicalSpace, originalTop
-/
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(Ω, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(Ω, F) | originalTop Ω F n <= t ∧
    @IsTopologicalAddGroup 𝓓^{n}(Ω, F) t _ ∧
    @ContinuousSMul Real 𝓓^{n}(Ω, F) _ _ t ∧
    @LocallyConvexSpace Real 𝓓^{n}(Ω, F) _ _ _ _ t}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalAddGroup 𝓓^{n}(Ω, F)
  body: topologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ => ht

中文:
实例 :
  签名: 是拓扑加群 𝓓^{n}(Ω, F)
  定义体: topologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ => ht

Depends on / 依赖: topologicalAddGroup_sInf
-/
noncomputable instance : IsTopologicalAddGroup 𝓓^{n}(Ω, F) :=
  topologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ => ht

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace 𝓓^{n}(Ω, F)
  body: IsTopologicalAddGroup.rightUniformSpace 𝓓^{n}(Ω, F)

中文:
实例 uniformSpace
  签名: : 一致空间 𝓓^{n}(Ω, F)
  定义体: IsTopologicalAddGroup.rightUniformSpace 𝓓^{n}(Ω, F)

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, rightUniformSpace
-/
noncomputable instance uniformSpace : UniformSpace 𝓓^{n}(Ω, F) :=
  IsTopologicalAddGroup.rightUniformSpace 𝓓^{n}(Ω, F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformAddGroup 𝓓^{n}(Ω, F)
  body: isUniformAddGroup_of_addCommGroup

中文:
实例 :
  签名: 是UniformAdd群 𝓓^{n}(Ω, F)
  定义体: isUniformAddGroup_of_addCommGroup

Depends on / 依赖: isUniformAddGroup_of_addCommGroup
-/
noncomputable instance : IsUniformAddGroup 𝓓^{n}(Ω, F) :=
  isUniformAddGroup_of_addCommGroup

-- TODO: deduce for `RCLike` field `𝕂`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul Real 𝓓^{n}(Ω, F)
  body: continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ => ht

中文:
实例 :
  签名: 连续标量乘法 实数 𝓓^{n}(Ω, F)
  定义体: continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ => ht

Depends on / 依赖: continuousSMul_sInf
-/
noncomputable instance : ContinuousSMul Real 𝓓^{n}(Ω, F) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ => ht

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyConvexSpace Real 𝓓^{n}(Ω, F)
  body: .sInf fun _ ⟨_, _, _, ht⟩ => ht

中文:
实例 :
  签名: LocallyConvex空间 实数 𝓓^{n}(Ω, F)
  定义体: .sInf fun _ ⟨_, _, _, ht⟩ => ht
-/
noncomputable instance : LocallyConvexSpace Real 𝓓^{n}(Ω, F) :=
  .sInf fun _ ⟨_, _, _, ht⟩ => ht

/--
theorem `originalTop_le` / 定理 `originalTop_le`

English:
theorem originalTop_le
  statement: originalTop Ω F n <= topologicalSpace Ω F n
  proof: le_sInf fun _t ⟨ht, _⟩ => ht

中文:
定理 originalTop_le
  结论: originalTop Ω F n <= topologicalSpace Ω F n
  证明: le_sInf fun _t ⟨ht, _⟩ => ht

Depends on / 依赖: le_sInf
-/
theorem originalTop_le : originalTop Ω F n <= topologicalSpace Ω F n :=
  le_sInf fun _t ⟨ht, _⟩ => ht

/--
theorem `topologicalSpace_le_iff` / 定理 `topologicalSpace_le_iff`

English:
theorem topologicalSpace_le_iff
  statement: {t : TopologicalSpace 𝓓^{n}(Ω, F)}
  proof: ⟨le_trans originalTop_le, fun H => sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

中文:
定理 topologicalSpace_le_iff
  结论: {t : 拓扑空间 𝓓^{n}(Ω, F)}
  证明: ⟨le_trans originalTop_le, fun H => sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

Depends on / 依赖: le_trans, map_add, originalTop_le, sInf_le
-/
theorem topologicalSpace_le_iff {t : TopologicalSpace 𝓓^{n}(Ω, F)}
    [@IsTopologicalAddGroup _ t _] [@ContinuousSMul Real _ _ _ t]
    [@LocallyConvexSpace Real _ _ _ _ _ t] :
    topologicalSpace Ω F n <= t ↔ originalTop Ω F n <= t :=
  ⟨le_trans originalTop_le, fun H => sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

/-- For every compact `K ⊆ Ω`, the inclusion map `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous. It is in fact a topological embedding, though this fact is not in Mathlib yet. -/
@[fun_prop]
/--
theorem `continuous_ofSupportedIn` / 定理 `continuous_ofSupportedIn`

English:
theorem continuous_ofSupportedIn
  given: {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω)
  proof: by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le

中文:
定理 continuous_ofSupportedIn
  条件: {K : 余mpacts E} (K_sub_Ω : (K : 集合 E) subseteq Ω)
  证明: by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, continuous_iff_coinduced_le, le_rfl, le_trans, originalTop_le
-/
theorem continuous_ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω) :
    Continuous (ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) -> 𝓓^{n}(Ω, F)) := by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le

variable (𝕜) in
/--
Definition of `ofSupportedInCLM` / `ofSupportedInCLM` 的定义

English:
definition ofSupportedInCLM
  signature: [SMulCommClass Real 𝕜 F] {K : Compacts E}
  body: ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 ofSupportedInCLM
  签名: [标量交换类 实数 𝕜 F] {K : 余mpacts E}
  定义体: ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: ofSupportedIn
-/
noncomputable def ofSupportedInCLM [SMulCommClass Real 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) subseteq Ω) :
    𝓓^{n}_{K}(E, F) ->L[𝕜] 𝓓^{n}(Ω, F) where
  toFun f := ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `coe_ofSupportedInCLM` / 定理 `coe_ofSupportedInCLM`

English:
theorem coe_ofSupportedInCLM
  statement: [SMulCommClass Real 𝕜 F] {K : Compacts E}
  proof: rfl

中文:
定理 coe_ofSupportedInCLM
  结论: [标量交换类 实数 𝕜 F] {K : 余mpacts E}
  证明: rfl

Depends on / 依赖: f.hom
-/
@[simp] theorem coe_ofSupportedInCLM [SMulCommClass Real 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) subseteq Ω) :
    (ofSupportedInCLM 𝕜 K_sub_Ω : 𝓓^{n}_{K}(E, F) -> 𝓓^{n}(Ω, F)) = ofSupportedIn K_sub_Ω :=
  rfl

/--
theorem `continuous_iff_continuous_comp` / 定理 `continuous_iff_continuous_comp`

English:
theorem continuous_iff_continuous_comp
  statement: [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]
  proof: by
  simp_rw [← f.coe_restrictScalars Real]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars Real) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul Real _ _ _ (induced (f.restrictScalars Real) t) := continuousSMul_induced _
  have : @Lo

中文:
定理 continuous_iff_continuous_comp
  结论: [代数 实数 𝕜] [标量塔 实数 𝕜 F]
  证明: by
  simp_rw [← f.coe_restrictScalars Real]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars Real) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul Real _ _ _ (induced (f.restrictScalars Real) t) := continuousSMul_induced _
  have : @Lo

Depends on / 依赖: f.hom
-/
protected theorem continuous_iff_continuous_comp [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]
    [Module 𝕜 V] [IsScalarTower Real 𝕜 V] (f : 𝓓^{n}(Ω, F) ->ₗ[𝕜] V) :
    Continuous f ↔ forall (K : Compacts E) (K_sub_Ω : (K : Set E) subseteq Ω),
      Continuous (f ∘ ofSupportedIn K_sub_Ω) := by
  simp_rw [← f.coe_restrictScalars Real]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars Real) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul Real _ _ _ (induced (f.restrictScalars Real) t) := continuousSMul_induced _
  have : @LocallyConvexSpace Real _ _ _ _ _ (induced (f.restrictScalars Real) t) := .induced _
  simp_rw [topologicalSpace_le_iff, originalTop, iSup₂_le_iff, ← continuous_iff_le_induced,
    continuous_coinduced_dom]

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `limitCLM`. -/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mkCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] [Module 𝕜 V]
  body: letI Φ : 𝓓^{n}(Ω, F) ->ₗ[𝕜] V := ⟨⟨toFun, map_add⟩, map_smul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by rwa [TestFunction.continuous_iff_continuous_comp] }

中文:
定义 noncomputable
  签名: def mkCLM [代数 实数 𝕜] [标量塔 实数 𝕜 F] [模 𝕜 V]
  定义体: letI Φ : 𝓓^{n}(Ω, F) ->ₗ[𝕜] V := ⟨⟨toFun, map_add⟩, map_smul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by rwa [TestFunction.continuous_iff_continuous_comp] }
-/
protected noncomputable def mkCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] [Module 𝕜 V]
    [IsScalarTower Real 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) -> V)
    (map_add : forall f g, toFun (f + g) = toFun f + toFun g)
    (map_smul : forall c : 𝕜, forall f, toFun (c • f) = c • toFun f)
    (cont : forall (K : Compacts E) (K_sub_Ω : (K : Set E) subseteq Ω),
      Continuous (toFun ∘ ofSupportedIn K_sub_Ω)) :
    𝓓^{n}(Ω, F) ->L[𝕜] V :=
  letI Φ : 𝓓^{n}(Ω, F) ->ₗ[𝕜] V := ⟨⟨toFun, map_add⟩, map_smul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by rwa [TestFunction.continuous_iff_continuous_comp] }

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `mkCLM`. -/
@[simps!]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def limitCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] [Module 𝕜 V]
  body: haveI toFun_add (f g : 𝓓^{n}(Ω, F)) : toFun (f + g) = toFun f + toFun g := by
    set K : Compacts E := ⟨tsupport f union tsupport g, .union f.hasCompactSupport g.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) subseteq Ω := union_subset f.tsupport_subset g.tsupport_subset
    let f_K : 𝓓^{n}_{K}(

中文:
定义 noncomputable
  签名: def limitCLM [代数 实数 𝕜] [标量塔 实数 𝕜 F] [模 𝕜 V]
  定义体: haveI toFun_add (f g : 𝓓^{n}(Ω, F)) : toFun (f + g) = toFun f + toFun g := by
    set K : Compacts E := ⟨tsupport f union tsupport g, .union f.hasCompactSupport g.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) subseteq Ω := union_subset f.tsupport_subset g.tsupport_subset
    let f_K : 𝓓^{n}_{K}(
-/
protected noncomputable def limitCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] [Module 𝕜 V]
    [IsScalarTower Real 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) -> V)
    (T : Π (K : Compacts E), (K : Set E) subseteq Ω -> 𝓓^{n}_{K}(E, F) ->L[𝕜] V)
    (toFun_eq_T : forall K K_sub_Ω f, toFun (ofSupportedIn K_sub_Ω f) = T K K_sub_Ω f) :
    𝓓^{n}(Ω, F) ->L[𝕜] V :=
  haveI toFun_add (f g : 𝓓^{n}(Ω, F)) : toFun (f + g) = toFun f + toFun g := by
    set K : Compacts E := ⟨tsupport f union tsupport g, .union f.hasCompactSupport g.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) subseteq Ω := union_subset f.tsupport_subset g.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset f.contDiff (subset_closure.trans subset_union_left)
    let g_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset g.contDiff (subset_closure.trans subset_union_right)
    change toFun (ofSupportedIn K_sub_Ω (f_K + g_K)) =
      toFun (ofSupportedIn K_sub_Ω f_K) + toFun (ofSupportedIn K_sub_Ω g_K)
    simp [toFun_eq_T]
  haveI toFun_smul (c : 𝕜) (f : 𝓓^{n}(Ω, F)) : toFun (c • f) = c • toFun f := by
    set K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) subseteq Ω := f.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) := .of_support_subset f.contDiff subset_closure
    change toFun (ofSupportedIn K_sub_Ω (c • f_K)) = c • toFun (ofSupportedIn K_sub_Ω f_K)
    simp [toFun_eq_T]
  TestFunction.mkCLM 𝕜 toFun toFun_add toFun_smul
    (fun K K_sub_Ω => .congr (T K K_sub_Ω).continuous (fun f => (toFun_eq_T K K_sub_Ω f).symm))

end Topology

section ToBoundedContinuousFunctionCLM

variable (𝕜) in
/-- The inclusion of the space `𝓓^{n}(Ω, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
@[simps! apply]
/--
Definition of `toBoundedContinuousFunctionCLM` / `toBoundedContinuousFunctionCLM` 的定义

English:
definition toBoundedContinuousFunctionCLM
  signature: [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]
  body: TestFunction.mkCLM 𝕜 (↑) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous)

中文:
定义 toBoundedContinuousFunctionCLM
  签名: [代数 实数 𝕜] [标量塔 实数 𝕜 F]
  定义体: TestFunction.mkCLM 𝕜 (↑) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous)

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM, TestFunction, TestFunction.mkCLM, continuous, toBoundedContinuousFunctionCLM
-/
noncomputable def toBoundedContinuousFunctionCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] :
    𝓓^{n}(Ω, F) ->L[𝕜] E ->ᵇ F :=
  TestFunction.mkCLM 𝕜 (↑) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous)

/--
lemma `toBoundedContinuousFunctionCLM_eq_of_scalars` / 引理 `toBoundedContinuousFunctionCLM_eq_of_scalars`

English:
lemma toBoundedContinuousFunctionCLM_eq_of_scalars
  statement: [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] (𝕜' : Type*)
  proof: rfl

中文:
引理 toBoundedContinuousFunctionCLM_eq_of_scalars
  结论: [代数 实数 𝕜] [标量塔 实数 𝕜 F] (𝕜' : 类型)
  证明: rfl
-/
lemma toBoundedContinuousFunctionCLM_eq_of_scalars [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) -> _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
/--
theorem `injective_toBoundedContinuousFunctionCLM` / 定理 `injective_toBoundedContinuousFunctionCLM`

English:
theorem injective_toBoundedContinuousFunctionCLM
  given: [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]
  proof: fun f g => by simp [toBoundedContinuousFunctionCLM]

中文:
定理 injective_toBoundedContinuousFunctionCLM
  条件: [代数 实数 𝕜] [标量塔 实数 𝕜 F]
  证明: fun f g => by simp [toBoundedContinuousFunctionCLM]

Depends on / 依赖: toBoundedContinuousFunctionCLM
-/
theorem injective_toBoundedContinuousFunctionCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] :
    Function.Injective (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) ->L[𝕜] E ->ᵇ F) :=
  fun f g => by simp [toBoundedContinuousFunctionCLM]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEval 𝓓^{n}(Ω, F) E F
  body: ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

中文:
实例 :
  签名: 余ntinuousEval 𝓓^{n}(Ω, F) E F
  定义体: ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

Depends on / 依赖: ContinuousEval, ContinuousEval.of_continuous_forget, continuous, of_continuous_forget, toBoundedContinuousFunctionCLM
-/
instance : ContinuousEval 𝓓^{n}(Ω, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T3Space 𝓓^{n}(Ω, F)
  body: suffices T2Space 𝓓^{n}(Ω, F) from inferInstance
  .of_injective_continuous (injective_toBoundedContinuousFunctionCLM Real)
    (ContinuousLinearMap.continuous _)

中文:
实例 :
  签名: T3空间 𝓓^{n}(Ω, F)
  定义体: suffices T2Space 𝓓^{n}(Ω, F) from inferInstance
  .of_injective_continuous (injective_toBoundedContinuousFunctionCLM Real)
    (ContinuousLinearMap.continuous _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous, T2Space, continuous, injective_toBoundedContinuousFunctionCLM, of_injective_continuous
-/
instance : T3Space 𝓓^{n}(Ω, F) :=
  suffices T2Space 𝓓^{n}(Ω, F) from inferInstance
  .of_injective_continuous (injective_toBoundedContinuousFunctionCLM Real)
    (ContinuousLinearMap.continuous _)

end ToBoundedContinuousFunctionCLM

section postcomp

variable [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] [IsScalarTower Real 𝕜 F']

-- Note: generalizing this to a semilinear setting would require a typeclass-way of saying that
-- the `RingHom` is `ℝ`-linear.
/--
Definition of `postcompCLM` / `postcompCLM` 的定义

English:
definition postcompCLM
  signature: (T : F ->L[𝕜] F')
  body: letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{n}(Ω, F') :=
.contDiff.comp f.contDiff, ⟨T ∘ f, T.restrictScalars Real
      f.hasCompactSupport.comp_left (map_zero _),
      (tsupport_comp_subset (map_zero _) f).trans f.tsupport_subset⟩
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupportedInCLM 𝕜 K_sub_Ω ∘L 

中文:
定义 postcompCLM
  签名: (T : F ->L[𝕜] F')
  定义体: letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{n}(Ω, F') :=
.contDiff.comp f.contDiff, ⟨T ∘ f, T.restrictScalars Real
      f.hasCompactSupport.comp_left (map_zero _),
      (tsupport_comp_subset (map_zero _) f).trans f.tsupport_subset⟩
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupportedInCLM 𝕜 K_sub_Ω ∘L 

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.postcompCLM, T.restrictScalars, TestFunction, TestFunction.limitCLM, comp_left, contDiff, contDiff.comp, f.contDiff, f.hasCompactSupport.comp_left, f.tsupport_subset, hasCompactSupport, limitCLM, map_zero, ofSupportedInCLM, postcompCLM, restrictScalars, tsupport_comp_subset, tsupport_subset
-/
noncomputable def postcompCLM (T : F ->L[𝕜] F') :
    𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{n}(Ω, F') :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{n}(Ω, F') :=
.contDiff.comp f.contDiff, ⟨T ∘ f, T.restrictScalars Real
      f.hasCompactSupport.comp_left (map_zero _),
      (tsupport_comp_subset (map_zero _) f).trans f.tsupport_subset⟩
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.postcompCLM T)
    (fun _ _ _ => by ext; simp [Φ])

@[simp]
/--
lemma `postcompCLM_apply` / 引理 `postcompCLM_apply`

English:
lemma postcompCLM_apply
  statement: (T : F ->L[𝕜] F')
  proof: rfl

中文:
引理 postcompCLM_apply
  结论: (T : F ->L[𝕜] F')
  证明: rfl
-/
lemma postcompCLM_apply (T : F ->L[𝕜] F')
    (f : 𝓓^{n}(Ω, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

end postcomp

section Monotone

variable [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
/--
Definition of `monoCLM` / `monoCLM` 的定义

English:
definition monoCLM
  signature: :
  body: open scoped Classical in
  letI Φ (f : 𝓓^{n₁}(Ω₁, F)) : 𝓓^{n₂}(Ω₂, F) :=
    if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂ then
      ⟨f, f.contDiff.of_le (mod_cast h.1), f.hasCompactSupport, f.tsupport_subset.trans h.2⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω₁ => if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂
      the

中文:
定义 monoCLM
  签名: :
  定义体: open scoped Classical in
  letI Φ (f : 𝓓^{n₁}(Ω₁, F)) : 𝓓^{n₂}(Ω₂, F) :=
    if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂ then
      ⟨f, f.contDiff.of_le (mod_cast h.1), f.hasCompactSupport, f.tsupport_subset.trans h.2⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω₁ => if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂
      the

Depends on / 依赖: Classical, ContDiffMapSupportedIn, ContDiffMapSupportedIn.monoCLM, TestFunction, TestFunction.limitCLM, contDiff, f.contDiff.of_le, f.hasCompactSupport, f.tsupport_subset.trans, hasCompactSupport, limitCLM, mod_cast, monoCLM, ofSupportedInCLM, of_le, scoped, split_ifs, tsupport_subset
-/
noncomputable def monoCLM :
    𝓓^{n₁}(Ω₁, F) ->L[𝕜] 𝓓^{n₂}(Ω₂, F) :=
  open scoped Classical in
  letI Φ (f : 𝓓^{n₁}(Ω₁, F)) : 𝓓^{n₂}(Ω₂, F) :=
    if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂ then
      ⟨f, f.contDiff.of_le (mod_cast h.1), f.hasCompactSupport, f.tsupport_subset.trans h.2⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω₁ => if h : n₂ <= n₁ ∧ Ω₁ <= Ω₂
      then ofSupportedInCLM 𝕜 (K_sub_Ω₁.trans h.2) ∘L ContDiffMapSupportedIn.monoCLM 𝕜
      else 0)
    (fun _ _ _ => by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

open scoped Classical in
@[simp]
/--
lemma `monoCLM_apply` / 引理 `monoCLM_apply`

English:
lemma monoCLM_apply
  given: (f : 𝓓^{n₁}(Ω₁, F))
  proof: by
  rw [monoCLM]
  split_ifs <;> rfl

中文:
引理 monoCLM_apply
  条件: (f : 𝓓^{n₁}(Ω₁, F))
  证明: by
  rw [monoCLM]
  split_ifs <;> rfl

Depends on / 依赖: monoCLM, split_ifs
-/
lemma monoCLM_apply (f : 𝓓^{n₁}(Ω₁, F)) :
    ((monoCLM 𝕜 f : 𝓓^{n₂}(Ω₂, F)) : E -> F) = if n₂ <= n₁ ∧ Ω₁ <= Ω₂ then f else 0 := by
  rw [monoCLM]
  split_ifs <;> rfl

/--
lemma `monoCLM_eq_zero` / 引理 `monoCLM_eq_zero`

English:
lemma monoCLM_eq_zero
  given: (H : ¬ (n₂ <= n₁ ∧ Ω₁ <= Ω₂))
  proof: by
  ext; simp [H]

中文:
引理 monoCLM_eq_zero
  条件: (H : ¬ (n₂ <= n₁ ∧ Ω₁ <= Ω₂))
  证明: by
  ext; simp [H]
-/
lemma monoCLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ Ω₁ <= Ω₂)) :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) ->L[𝕜] 𝓓^{n₂}(Ω₂, F)) = 0 := by
  ext; simp [H]

/--
lemma `monoCLM_eq_of_scalars` / 引理 `monoCLM_eq_of_scalars`

English:
lemma monoCLM_eq_of_scalars
  statement: (𝕜' : Type*)
  proof: rfl

中文:
引理 monoCLM_eq_of_scalars
  结论: (𝕜' : 类型)
  证明: rfl
-/
lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) -> 𝓓^{n₂}(Ω₂, F)) = monoCLM 𝕜' :=
  rfl

end Monotone

section FDerivCLM

variable [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜 n k) in
/--
Definition of `fderivCLM` / `fderivCLM` 的定义

English:
definition fderivCLM
  signature: :
  body: letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{k}(Ω, E ->L[Real] F) :=
    if hk : k + 1 <= n then
      ⟨fderiv Real f, f.contDiff.fderiv_right (mod_cast hk),
.trans f.tsupport_subset⟩ f.hasCompactSupport.fderiv Real, tsupport_fderiv_subset Real
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupport

中文:
定义 fderivCLM
  签名: :
  定义体: letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{k}(Ω, E ->L[Real] F) :=
    if hk : k + 1 <= n then
      ⟨fderiv Real f, f.contDiff.fderiv_right (mod_cast hk),
.trans f.tsupport_subset⟩ f.hasCompactSupport.fderiv Real, tsupport_fderiv_subset Real
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupport

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.fderivCLM, M.str, TestFunction, TestFunction.limitCLM, contDiff, f.contDiff.fderiv_right, f.hasCompactSupport.fderiv, f.tsupport_subset, fderiv, fderivCLM, fderiv_right, hasCompactSupport, limitCLM, mod_cast, ofSupportedInCLM, split_ifs, tsupport_fderiv_subset, tsupport_subset
-/
noncomputable def fderivCLM :
    𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, E ->L[Real] F) :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{k}(Ω, E ->L[Real] F) :=
    if hk : k + 1 <= n then
      ⟨fderiv Real f, f.contDiff.fderiv_right (mod_cast hk),
.trans f.tsupport_subset⟩ f.hasCompactSupport.fderiv Real, tsupport_fderiv_subset Real
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω => ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.fderivCLM 𝕜 n k)
    (fun _ _ _ => by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

@[simp]
/--
lemma `fderivCLM_apply` / 引理 `fderivCLM_apply`

English:
lemma fderivCLM_apply
  given: (f : 𝓓^{n}(Ω, F))
  proof: by
  rw [fderivCLM]
  split_ifs <;> rfl

中文:
引理 fderivCLM_apply
  条件: (f : 𝓓^{n}(Ω, F))
  证明: by
  rw [fderivCLM]
  split_ifs <;> rfl

Depends on / 依赖: fderivCLM, split_ifs
-/
lemma fderivCLM_apply (f : 𝓓^{n}(Ω, F)) :
    fderivCLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0 := by
  rw [fderivCLM]
  split_ifs <;> rfl

/--
lemma `fderivCLM_apply_of_le` / 引理 `fderivCLM_apply_of_le`

English:
lemma fderivCLM_apply_of_le
  given: (f : 𝓓^{n}(Ω, F)) (hk : k + 1 <= n)
  proof: by
  simp [hk]

中文:
引理 fderivCLM_apply_of_le
  条件: (f : 𝓓^{n}(Ω, F)) (hk : k + 1 <= n)
  证明: by
  simp [hk]
-/
lemma fderivCLM_apply_of_le (f : 𝓓^{n}(Ω, F)) (hk : k + 1 <= n) :
    fderivCLM 𝕜 n k f = fderiv Real f := by
  simp [hk]

/--
lemma `fderivCLM_apply_of_gt` / 引理 `fderivCLM_apply_of_gt`

English:
lemma fderivCLM_apply_of_gt
  given: (hk : n < k + 1)
  proof: by
  ext : 2
  simp [not_le_of_gt hk]

中文:
引理 fderivCLM_apply_of_gt
  条件: (hk : n < k + 1)
  证明: by
  ext : 2
  simp [not_le_of_gt hk]

Depends on / 依赖: not_le_of_gt
-/
lemma fderivCLM_apply_of_gt (hk : n < k + 1) :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, E ->L[Real] F)) = 0 := by
  ext : 2
  simp [not_le_of_gt hk]

variable (𝕜) in
/--
lemma `fderivCLM_ofSupportedIn` / 引理 `fderivCLM_ofSupportedIn`

English:
lemma fderivCLM_ofSupportedIn
  statement: {K : Compacts E}
  proof: by
  ext
  simp

中文:
引理 fderivCLM_ofSupportedIn
  结论: {K : 余mpacts E}
  证明: by
  ext
  simp
-/
lemma fderivCLM_ofSupportedIn {K : Compacts E}
    (K_sub_Ω : (K : Set E) subseteq Ω) (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k (ofSupportedIn K_sub_Ω f) =
      ofSupportedIn K_sub_Ω (ContDiffMapSupportedIn.fderivCLM 𝕜 n k f) := by
  ext
  simp

variable (𝕜) in
/--
lemma `fderivCLM_eq_of_scalars` / 引理 `fderivCLM_eq_of_scalars`

English:
lemma fderivCLM_eq_of_scalars
  statement: (𝕜' : Type*)
  proof: rfl

中文:
引理 fderivCLM_eq_of_scalars
  结论: (𝕜' : 类型)
  证明: rfl
-/
lemma fderivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) -> _) = fderivCLM 𝕜' n k :=
  rfl

end FDerivCLM

section LineDerivCLM

variable [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F]

variable (𝕜) in
/--
Definition of `lineDerivCLM` / `lineDerivCLM` 的定义

English:
definition lineDerivCLM
  signature: (v : E)
  body: -- Cannot use `ContinuousLinearMap.apply` here because we are mixing `ℝ` and `𝕜`
  letI ev_v : (E ->L[Real] F) ->L[𝕜] F :=
  { toFun f := f v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  postcompCLM ev_v ∘L fderivCLM 𝕜 n k

中文:
定义 lineDerivCLM
  签名: (v : E)
  定义体: -- Cannot use `ContinuousLinearMap.apply` here because we are mixing `ℝ` and `𝕜`
  letI ev_v : (E ->L[Real] F) ->L[𝕜] F :=
  { toFun f := f v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  postcompCLM ev_v ∘L fderivCLM 𝕜 n k
-/
noncomputable def lineDerivCLM (v : E) :
    𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F) :=
  -- Cannot use `ContinuousLinearMap.apply` here because we are mixing `ℝ` and `𝕜`
  letI ev_v : (E ->L[Real] F) ->L[𝕜] F :=
  { toFun f := f v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  postcompCLM ev_v ∘L fderivCLM 𝕜 n k

/--
lemma `lineDerivCLM_eq_fderivCLM` / 引理 `lineDerivCLM_eq_fderivCLM`

English:
lemma lineDerivCLM_eq_fderivCLM
  given: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E}
  proof: rfl

@[simp]

中文:
引理 lineDerivCLM_eq_fderivCLM
  条件: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E}
  证明: rfl

@[simp]

Depends on / 依赖: NormNoninc, NormedAddGroupHom, NormedAddGroupHom.NormNoninc.zero
-/
lemma lineDerivCLM_eq_fderivCLM {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = fderivCLM 𝕜 n k f x v :=
  rfl

@[simp]
/--
lemma `lineDerivCLM_apply` / 引理 `lineDerivCLM_apply`

English:
lemma lineDerivCLM_apply
  given: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E}
  proof: by
  rw [lineDerivCLM_eq_fderivCLM]; rw [fderivCLM_apply]
  split_ifs with hk
  · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    rw [(f.contDiff.differentiable hk'.ne').differentiableAt.lineDeriv_eq_fderiv]
  · rfl

中文:
引理 lineDerivCLM_apply
  条件: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E}
  证明: by
  rw [lineDerivCLM_eq_fderivCLM]; rw [fderivCLM_apply]
  split_ifs with hk
  · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    rw [(f.contDiff.differentiable hk'.ne').differentiableAt.lineDeriv_eq_fderiv]
  · rfl

Depends on / 依赖: add_pos_of_right, contDiff, differentiable, differentiableAt, differentiableAt.lineDeriv_eq_fderiv, f.contDiff.differentiable, fderivCLM_apply, lineDerivCLM_eq_fderivCLM, lineDeriv_eq_fderiv, mod_cast, split_ifs, trans_le, zero_lt_one
-/
lemma lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = if k + 1 <= n then lineDeriv Real f x v else 0 := by
  rw [lineDerivCLM_eq_fderivCLM]; rw [fderivCLM_apply]
  split_ifs with hk
  · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    rw [(f.contDiff.differentiable hk'.ne').differentiableAt.lineDeriv_eq_fderiv]
  · rfl

/--
lemma `lineDerivCLM_apply_of_le` / 引理 `lineDerivCLM_apply_of_le`

English:
lemma lineDerivCLM_apply_of_le
  given: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 <= n)
  proof: by
  simp [hk]

中文:
引理 lineDerivCLM_apply_of_le
  条件: {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 <= n)
  证明: by
  simp [hk]
-/
lemma lineDerivCLM_apply_of_le {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 <= n) :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = lineDeriv Real f x v := by
  simp [hk]

/--
lemma `lineDerivCLM_apply_of_gt` / 引理 `lineDerivCLM_apply_of_gt`

English:
lemma lineDerivCLM_apply_of_gt
  given: {v : E} (hk : n < k + 1)
  proof: by
  ext
  simp [not_le_of_gt hk]

中文:
引理 lineDerivCLM_apply_of_gt
  条件: {v : E} (hk : n < k + 1)
  证明: by
  ext
  simp [not_le_of_gt hk]

Depends on / 依赖: not_le_of_gt
-/
lemma lineDerivCLM_apply_of_gt {v : E} (hk : n < k + 1) :
    (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) = 0 := by
  ext
  simp [not_le_of_gt hk]

variable (𝕜) in
/--
lemma `lineDerivCLM_eq_of_scalars` / 引理 `lineDerivCLM_eq_of_scalars`

English:
lemma lineDerivCLM_eq_of_scalars
  statement: (𝕜' : Type*)
  proof: rfl

中文:
引理 lineDerivCLM_eq_of_scalars
  结论: (𝕜' : 类型)
  证明: rfl
-/
lemma lineDerivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F]
    {v : E} : (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) -> 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜' v :=
  rfl

/--
lemma `lineDerivCLM_add` / 引理 `lineDerivCLM_add`

English:
lemma lineDerivCLM_add
  given: {v₁ v₂ : E}
  proof: by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

中文:
引理 lineDerivCLM_add
  条件: {v₁ v₂ : E}
  证明: by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

Depends on / 依赖: lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM
-/
lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM 𝕜 (v₁ + v₂) : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) =
      lineDerivCLM 𝕜 v₁ + lineDerivCLM 𝕜 v₂ := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

/--
lemma `lineDerivCLM_smul` / 引理 `lineDerivCLM_smul`

English:
lemma lineDerivCLM_smul
  given: {c : Real} {v : E}
  proof: by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

中文:
引理 lineDerivCLM_smul
  条件: {c : 实数} {v : E}
  证明: by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

Depends on / 依赖: NonarchAddGroupSeminormClass, NonarchAddGroupSeminormClass.toAddGroupSeminormClass, lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM, toAddGroupSeminormClass
-/
lemma lineDerivCLM_smul {c : Real} {v : E} :
    (lineDerivCLM 𝕜 (c • v) : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) =
      c • lineDerivCLM 𝕜 v := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

open LineDeriv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDeriv E 𝓓(Ω, F) 𝓓(Ω, F)
  body: lineDerivCLM Real v

中文:
实例 :
  签名: LineDeriv E 𝓓(Ω, F) 𝓓(Ω, F)
  定义体: lineDerivCLM Real v

Depends on / 依赖: NonarchAddGroupNormClass, NonarchAddGroupNormClass.toAddGroupNormClass, lineDerivCLM, toAddGroupNormClass
-/
noncomputable instance : LineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp v := lineDerivCLM Real v

variable (𝕜) in
/--
lemma `lineDerivOp_eq_lineDerivCLM` / 引理 `lineDerivOp_eq_lineDerivCLM`

English:
lemma lineDerivOp_eq_lineDerivCLM
  given: {v : E} {f : 𝓓(Ω, F)}
  proof: rfl

中文:
引理 lineDerivOp_eq_lineDerivCLM
  条件: {v : E} {f : 𝓓(Ω, F)}
  证明: rfl
-/
lemma lineDerivOp_eq_lineDerivCLM {v : E} {f : 𝓓(Ω, F)} :
    ∂_{v} f = lineDerivCLM 𝕜 v f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivAdd E 𝓓(Ω, F) 𝓓(Ω, F)
  body: map_add (lineDerivCLM Real v)
  lineDerivOp_left_add _ _ f := congr($lineDerivCLM_add f)

中文:
实例 :
  签名: LineDerivAdd E 𝓓(Ω, F) 𝓓(Ω, F)
  定义体: map_add (lineDerivCLM Real v)
  lineDerivOp_left_add _ _ f := congr($lineDerivCLM_add f)

Depends on / 依赖: lineDerivCLM, map_add
-/
noncomputable instance : LineDerivAdd E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM Real v)
  lineDerivOp_left_add _ _ f := congr($lineDerivCLM_add f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivSMul 𝕜 E 𝓓(Ω, F) 𝓓(Ω, F)
  body: map_smul (lineDerivCLM 𝕜 v)

中文:
实例 :
  签名: LineDerivSMul 𝕜 E 𝓓(Ω, F) 𝓓(Ω, F)
  定义体: map_smul (lineDerivCLM 𝕜 v)

Depends on / 依赖: lineDerivCLM, map_smul
-/
noncomputable instance : LineDerivSMul 𝕜 E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM 𝕜 v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivLeftSMul Real E 𝓓(Ω, F) 𝓓(Ω, F)
  body: congr($lineDerivCLM_smul f)

中文:
实例 :
  签名: LineDerivLeftSMul 实数 E 𝓓(Ω, F) 𝓓(Ω, F)
  定义体: congr($lineDerivCLM_smul f)

Depends on / 依赖: lineDerivCLM_smul
-/
noncomputable instance : LineDerivLeftSMul Real E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_left_smul _ _ f := congr($lineDerivCLM_smul f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLineDeriv E 𝓓(Ω, F) 𝓓(Ω, F)
  body: (lineDerivCLM Real v).continuous

中文:
实例 :
  签名: 余ntinuousLineDeriv E 𝓓(Ω, F) 𝓓(Ω, F)
  定义体: (lineDerivCLM Real v).continuous

Depends on / 依赖: continuous, lineDerivCLM
-/
noncomputable instance : ContinuousLineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM Real v).continuous

/--
lemma `lineDerivOpCLM_eq_lineDerivCLM` / 引理 `lineDerivOpCLM_eq_lineDerivCLM`

English:
lemma lineDerivOpCLM_eq_lineDerivCLM
  given: {v : E}
  proof: rfl

中文:
引理 lineDerivOpCLM_eq_lineDerivCLM
  条件: {v : E}
  证明: rfl
-/
lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM 𝕜 𝓓(Ω, F) v = lineDerivCLM 𝕜 v :=
  rfl

end LineDerivCLM

section Integral

open MeasureTheory

variable {m : MeasurableSpace E} [OpensMeasurableSpace E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace Real F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (f : 𝓓^{n}(Ω, F))
  proof: by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]

中文:
定理 stronglyMeasurable
  条件: (f : 𝓓^{n}(Ω, F))
  证明: by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
-/
protected theorem stronglyMeasurable (f : 𝓓^{n}(Ω, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: {μ : Measure E} (f : 𝓓^{n}(Ω, F))
  proof: f.stronglyMeasurable.aestronglyMeasurable

中文:
定理 aestronglyMeasurable
  条件: {μ : 测度 E} (f : 𝓓^{n}(Ω, F))
  证明: f.stronglyMeasurable.aestronglyMeasurable
-/
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

/--
theorem `memLp_top` / 定理 `memLp_top`

English:
theorem memLp_top
  given: {μ : Measure E} (f : 𝓓^{n}(Ω, F))
  proof: f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

中文:
定理 memLp_top
  条件: {μ : 测度 E} (f : 𝓓^{n}(Ω, F))
  证明: f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ
-/
protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

/--
theorem `integrable_bilin` / 定理 `integrable_bilin`

English:
theorem integrable_bilin
  statement: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : Measure E} {φ : E -> F₂}
  proof: by
  suffices IntegrableOn (fun x => B (f x) (φ x)) (tsupport f) μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ (subset_tsupport f)
    exact fun x hx hfx => hx (by simp [hfx])
  replace hφ := hφ.integrableOn_compact_subset f.tsupport_subset f.hasComp

中文:
定理 integrable_bilin
  结论: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : 测度 E} {φ : E -> F₂}
  证明: by
  suffices IntegrableOn (fun x => B (f x) (φ x)) (tsupport f) μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ (subset_tsupport f)
    exact fun x hx hfx => hx (by simp [hfx])
  replace hφ := hφ.integrableOn_compact_subset f.tsupport_subset f.hasComp
-/
protected theorem integrable_bilin (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : Measure E} {φ : E -> F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) (f : 𝓓^{n}(Ω, F₁)) :
    Integrable (fun x => B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x => B (f x) (φ x)) (tsupport f) μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ (subset_tsupport f)
    exact fun x hx hfx => hx (by simp [hfx])
  replace hφ := hφ.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  statement: {μ : Measure E}
  proof: by
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport f)]
  replace H := H.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  suffices IntegrableOn ((1 : Real) • f) (tsupport f) μ by simpa
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at H ⊢
  exact f.memL

中文:
定理 integrable
  结论: {μ : 测度 E}
  证明: by
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport f)]
  replace H := H.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  suffices IntegrableOn ((1 : Real) • f) (tsupport f) μ by simpa
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at H ⊢
  exact f.memL
-/
protected theorem integrable {μ : Measure E}
    (H : LocallyIntegrableOn (fun (_ : E) => (1 : Real)) Ω μ)
    (f : 𝓓^{n}(Ω, F)) : Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport f)]
  replace H := H.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  suffices IntegrableOn ((1 : Real) • f) (tsupport f) μ by simpa
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at H ⊢
  exact f.memLp_top.smul H

variable [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F₁] [NormedSpace Real F₃] [IsScalarTower Real 𝕜 F₃]

-- TODO: semilinearize
/--
Definition of `integralAgainstBilinCLM` / `integralAgainstBilinCLM` 的定义

English:
definition integralAgainstBilinCLM
  signature: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂)
  body: open scoped Classical in
  TestFunction.limitCLM 𝕜
    (fun f => if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0)
    (fun K K_sub_Ω =>
      if LocallyIntegrableOn φ Ω μ
      then ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ
      else 0)
    (fun K K_sub_Ω f => by
      spl

中文:
定义 integralAgainstBilinCLM
  签名: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : 测度 E) (φ : E -> F₂)
  定义体: open scoped Classical in
  TestFunction.limitCLM 𝕜
    (fun f => if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0)
    (fun K K_sub_Ω =>
      if LocallyIntegrableOn φ Ω μ
      then ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ
      else 0)
    (fun K K_sub_Ω f => by
      spl

Depends on / 依赖: Classical, scoped
-/
noncomputable def integralAgainstBilinCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂) :
    𝓓^{n}(Ω, F₁) ->L[𝕜] F₃ := open scoped Classical in
  TestFunction.limitCLM 𝕜
    (fun f => if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0)
    (fun K K_sub_Ω =>
      if LocallyIntegrableOn φ Ω μ
      then ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ
      else 0)
    (fun K K_sub_Ω f => by
      split_ifs with h
      · simp [h.integrableOn_compact_subset K_sub_Ω K.2]
      · simp)

open scoped Classical in
@[simp]
/--
lemma `integralAgainstBilinCLM_apply` / 引理 `integralAgainstBilinCLM_apply`

English:
lemma integralAgainstBilinCLM_apply
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: rfl

中文:
引理 integralAgainstBilinCLM_apply
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: rfl
-/
lemma integralAgainstBilinCLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinCLM B μ φ f =
      if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0 :=
  rfl

/--
lemma `integralAgainstBilinCLM_eq_integral` / 引理 `integralAgainstBilinCLM_eq_integral`

English:
lemma integralAgainstBilinCLM_eq_integral
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  simp [hφ]

中文:
引理 integralAgainstBilinCLM_eq_integral
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  simp [hφ]
-/
lemma integralAgainstBilinCLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ := by
  simp [hφ]

/--
lemma `integralAgainstBilinCLM_eq_zero` / 引理 `integralAgainstBilinCLM_eq_zero`

English:
lemma integralAgainstBilinCLM_eq_zero
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  ext
  simp [hφ]

中文:
引理 integralAgainstBilinCLM_eq_zero
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  ext
  simp [hφ]
-/
lemma integralAgainstBilinCLM_eq_zero {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : ¬ LocallyIntegrableOn φ Ω μ) :
    (integralAgainstBilinCLM B μ φ : 𝓓^{n}(Ω, F₁) ->L[𝕜] F₃) = 0 := by
  ext
  simp [hφ]

/--
lemma `integralAgainstBilinCLM_ofSupportedIn` / 引理 `integralAgainstBilinCLM_ofSupportedIn`

English:
lemma integralAgainstBilinCLM_ofSupportedIn
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  have hφ' := hφ.integrableOn_compact_subset K_sub_Ω K.isCompact
  simp [hφ, hφ']

中文:
引理 integralAgainstBilinCLM_ofSupportedIn
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  have hφ' := hφ.integrableOn_compact_subset K_sub_Ω K.isCompact
  simp [hφ, hφ']

Depends on / 依赖: K.isCompact, integrableOn_compact_subset, isCompact
-/
lemma integralAgainstBilinCLM_ofSupportedIn {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω)
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ (ofSupportedIn K_sub_Ω f) =
      ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ f := by
  have hφ' := hφ.integrableOn_compact_subset K_sub_Ω K.isCompact
  simp [hφ, hφ']

end Integral

end TestFunction
