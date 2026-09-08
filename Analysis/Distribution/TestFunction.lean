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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω₁ Ω₂ : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F']
  {n n₁ n₂ k : ℕ∞}

variable (Ω F n) in
/-- The type of bundled `n`-times continuously differentiable maps with compact support -/
/-
**TestFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_3} →   [inst : NormedAddCommGroup E] →     [NormedSpace ℝ E] →
       TopologicalSpace.Opens E →         (F : Type u_4) → [inst : NormedAddComm
Group F] → [NormedSpace ℝ F] → ℕ∞ → Type (max u_3 u_4)
参数：F : Type u_4；max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bundled `n`-times continuously differentiable maps with compact supp
ort
-/
structure TestFunction : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected hasCompactSupport' : HasCompactSupport toFun
  protected tsupport_subset' : tsupport toFun ⊆ Ω

/-- Notation for the space of bundled `n`-times continuously differentiable maps
with compact support. -/
scoped[Distributions] notation "𝓓^{" n "}(" Ω ", " F ")" => TestFunction Ω F n

/-- Notation for the space of "test functions", i.e. bundled smooth (infinitely differentiable) maps
with compact support. -/
scoped[Distributions] notation "𝓓(" Ω ", " F ")" => TestFunction Ω F ⊤

open Distributions

/-- `TestFunctionClass B Ω F n` states that `B` is a type of `n`-times continuously
differentiable functions `E → F` with compact support contained in `Ω : Opens E`. -/
/-
**TestFunctionClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_6 →   {E : outParam (Type u_7)} →     [inst : NormedAddCommGroup E]
 →       [NormedSpace ℝ E] →         outParam (TopologicalSpace.Opens E) →      
     (F : outParam (Type u_8)) →             [inst : NormedAddCommGroup F] → [No
rmedSpace ℝ F] → outParam ℕ∞ → Type (max (max u_6 u_7) u_8)
参数：Type u_7；TopologicalSpace.Opens E；F : outParam (Type u_8)；max (max u_6 u_7) u
_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TestFunctionClass B Ω F n` states that `B` is a type of `n`-times continuously
differentiable functions `E → F` with compact support contained in `Ω : Opens E`
.
-/
class TestFunctionClass (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_hasCompactSupport (f : B) : HasCompactSupport f
  tsupport_map_subset (f : B) : tsupport f ⊆ Ω

open TestFunctionClass

namespace TestFunctionClass

/-
**TestFunctionClass.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunctionClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B Ω F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous
/-
**TestFunctionClass.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunctionClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B Ω F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support (map_hasCompactSupport f)
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end TestFunctionClass

namespace TestFunction

/-
**TestFunction.toTestFunctionClass** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
形式化陈述：toTestFunctionClass : TestFunctionClass 𝓓^{n}(Ω, F) Ω F n where coe f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunction.contDiff'`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_
2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport'`：∀ {E : Type u_3} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}
   [inst_2 : NormedAd…
· 使用定理 `TestFunction.tsupport_subset'`：∀ {E : Type u_3} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}  
 [inst_2 : NormedAd…
-/
instance toTestFunctionClass : TestFunctionClass 𝓓^{n}(Ω, F) Ω F n where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_hasCompactSupport f := f.hasCompactSupport'
  tsupport_map_subset f := f.tsupport_subset'
/-
**TestFunction.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} (f : TestFunction Ω F n), ContDiff ℝ ↑n ⇑f
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunctionClass.map_contDiff`：∀ {B : Type u_6} {E : outParam (Type u_7
)} {inst : NormedAddCommGroup E} {inst_1 : NormedSpace ℝ E}   {Ω : outParam (Top
ologicalSpace.Opens …
-/
protected theorem contDiff (f : 𝓓^{n}(Ω, F)) : ContDiff ℝ n f := map_contDiff f
/-
**TestFunction.hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} (f : TestFunction Ω F n), HasCompactSupport 
⇑f
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunctionClass.map_hasCompactSupport`：∀ {B : Type u_6} {E : outParam 
(Type u_7)} {inst : NormedAddCommGroup E} {inst_1 : NormedSpace ℝ E}   {Ω : outP
aram (TopologicalSpace.Opens …
-/
protected theorem hasCompactSupport (f : 𝓓^{n}(Ω, F)) : HasCompactSupport f :=
  map_hasCompactSupport f
/-
**TestFunction.tsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} (f : TestFunction Ω F n), tsupport ⇑f ⊆ ↑Ω
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunctionClass.tsupport_map_subset`：∀ {B : Type u_6} {E : outParam (T
ype u_7)} {inst : NormedAddCommGroup E} {inst_1 : NormedSpace ℝ E}   {Ω : outPar
am (TopologicalSpace.Opens …
-/
protected theorem tsupport_subset (f : 𝓓^{n}(Ω, F)) : tsupport f ⊆ Ω := tsupport_map_subset f

@[fun_prop]
/-
**TestFunction.continuous** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} (f : TestFunction Ω F n), Continuous ⇑f
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `TestFunction.contDiff`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2
 : NormedAd…
-/
protected theorem continuous (f : 𝓓^{n}(Ω, F)) : Continuous f :=
  f.contDiff.continuous

@[simp]
/-
**TestFunction.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：toFun_eq_coe {f : 𝓓^{n}(Ω, F)} : f.toFun = (f : E -> F)
参数：Ω, F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : 𝓓^{n}(Ω, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
/-
**TestFunction.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction.Simps`。
形式化陈述：{E : Type u_3} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpa
ce ℝ E] →       {Ω : TopologicalSpace.Opens E} →         {F : Type u_4} →       
    [inst_2 : NormedAddCommGroup F] → [inst_3 : NormedSpace ℝ F] → {n : ℕ∞} → Te
stFunction Ω F n → E → F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [custom simps projection].
-/
def Simps.coe (f : 𝓓^{n}(Ω, F)) : E → F := f

initialize_simps_projections TestFunction (toFun → coe, as_prefix coe)

@[ext]
/-
**TestFunction.ext** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f = g
参数：Ω, F；h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : 𝓓^{n}(Ω, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `TestFunction` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**TestFunction.copy** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：{E : Type u_3} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpa
ce ℝ E] →       {Ω : TopologicalSpace.Opens E} →         {F : Type u_4} →       
    [inst_2 : NormedAddCommGroup F] →             [inst_3 : NormedSpace ℝ F] →  
             {n : ℕ∞} → (f : TestFunction Ω F n) → (f' : E → F) → f' = ⇑f → Test
Function Ω F n
参数：f : TestFunction Ω F n；f' : E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `TestFunction` with a new `toFun` equal to the old one. Useful to fix
definitional equalities.
-/
protected def copy (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(Ω, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  hasCompactSupport' := h.symm ▸ f.hasCompactSupport
  tsupport_subset' := h.symm ▸ f.tsupport_subset

@[simp]
/-
**TestFunction.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：coe_copy (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f) : ⇑(f.copy f' h) = f
'
参数：f : 𝓓^{n}(Ω, F)；f' : E -> F；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**TestFunction.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：copy_eq (f : 𝓓^{n}(Ω, F)) (f' : E -> F) (h : f' = f) : f.copy f' h = f
参数：f : 𝓓^{n}(Ω, F)；f' : E -> F；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**TestFunction.coe_toBoundedContinuousFunction** 是 Mathlib 中的一个定理，位于命名空间 `TestFu
nction`。
形式化陈述：coe_toBoundedContinuousFunction (f : 𝓓^{n}(Ω, F)) : (f : BoundedContinuous
Function E F) = (f : E -> F)
参数：f : 𝓓^{n}(Ω, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunctionClass.instBoundedContinuousMapClass`：∀ (B : Type u_6) {E : o
utParam (Type u_7)} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (
Ω : outParam (TopologicalSpace.Opens …
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
-/
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}(Ω, F)) :
    (f : BoundedContinuousFunction E F) = (f : E → F) := rfl

@[simp]
/-
**TestFunction.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：coe_mk {f : E -> F} {contDiff : ContDiff Real n f} {hasCompactSupport : Ha
sCompactSupport f} {tsupport_subset : tsupport f subseteq Ω} : TestFunction.mk f
 contDiff hasCompactSupport tsupport_subset = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f : E → F} {contDiff : ContDiff ℝ n f} {hasCompactSupport : HasCompactSupport f}
    {tsupport_subset : tsupport f ⊆ Ω} :
    TestFunction.mk f contDiff hasCompactSupport tsupport_subset = f :=
  rfl

section AddCommGroup

/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero 𝓓^{n}(Ω, F) where
  zero := ⟨0, contDiff_zero_fun, .zero, by simp only [tsupport_zero, empty_subset]⟩
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply 𝓓^{n}(Ω, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add 𝓓^{n}(Ω, F) where
  add f g := ⟨f + g, f.contDiff.add g.contDiff, f.hasCompactSupport.add g.hasCompactSupport,
    tsupport_add f g |>.trans <| union_subset f.tsupport_subset g.tsupport_subset⟩
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply 𝓓^{n}(Ω, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg 𝓓^{n}(Ω, F) where
  neg f := ⟨-f, f.contDiff.neg, f.hasCompactSupport.neg, tsupport_neg f ▸ f.tsupport_subset⟩
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply 𝓓^{n}(Ω, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub 𝓓^{n}(Ω, F) where
  sub f g := ⟨f - g, f.contDiff.sub g.contDiff, f.hasCompactSupport.sub g.hasCompactSupport,
    tsupport_sub f g |>.trans <| union_subset f.tsupport_subset g.tsupport_subset⟩
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply 𝓓^{n}(Ω, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}(Ω, F) where
  smul c f := ⟨c • f, f.contDiff.const_smul c, f.hasCompactSupport.smul_left,
    tsupport_smul_subset_right _ _ |>.trans f.tsupport_subset⟩
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    IsSMulApply R 𝓓^{n}(Ω, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_smul := FunLike.coe_smul
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup 𝓓^{n}(Ω, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

end AddCommGroup

section Module

/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(Ω, F) := fast_instance% FunLike.module
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S} [Semiring R] [Semiring S] [Module R F] [Module S F] [SMulCommClass ℝ R F]
    [SMulCommClass ℝ S F] [ContinuousConstSMul R F] [ContinuousConstSMul S F] [SMul R S]
    [IsScalarTower R S F] :
    IsScalarTower R S 𝓓^{n}(Ω, F) := FunLike.isScalarTower

end Module

open ContDiffMapSupportedIn

/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` when `K ⊆ Ω`. -/
@[simps -fullyApplied]
/-
**TestFunction.ofSupportedIn** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω) (f : 𝓓^{
n}_{K}(E, F)) : 𝓓^{n}(Ω, F)
参数：K_sub_Ω : (K : Set E) subseteq Ω；f : 𝓓^{n}_{K}(E, F)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedIn.contDiff`：∀ {E : Type u_2} {F : Type u_3} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `ContDiffMapSupportedIn.compact_supp`：∀ {E : Type u_2} {F : Type u_3} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGro
up F]   [inst_3 : NormedS…

--- 原说明 ---
The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` when `K ⊆ Ω`.
-/
def ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n}(Ω, F) :=
  ⟨f, f.contDiff, f.compact_supp, f.tsupport_subset.trans K_sub_Ω⟩

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [t : TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]

variable (Ω F n) in
/-- The "original topology" on `𝓓^{n}(Ω, F)`, defined as the supremum over all compacts `K ⊆ Ω` of
the topology on `𝓓^{n}_{K}(E, F)`. In other words, this topology makes `𝓓^{n}(Ω, F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of topological spaces**.

Note that this has no reason to be a locally convex (or even vector space) topology. For this
reason, we actually endow `𝓓^{n}(Ω, F)` with another topology, namely the finest locally convex
topology which is coarser than this original topology. See `TestFunction.topologicalSpace`. -/
@[instance_reducible]
/-
**TestFunction.originalTop** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：originalTop : TopologicalSpace 𝓓^{n}(Ω, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "original topology" on `𝓓^{n}(Ω, F)`, defined as the supremum over all compa
cts `K ⊆ Ω` of
the topology on `𝓓^{n}_{K}(E, F)`. In other words, this topology makes `𝓓^{n}(Ω,
 F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of topological spaces**.

Note that this has no reason to be a locally convex (or even vector space) topol
ogy. For this
reason, we actually endow `𝓓^{n}(Ω, F)` with another topology, namely the finest
 locally convex
topology which is coarser than this original topology. See `TestFunction.topolog
icalSpace`.
-/
noncomputable def originalTop : TopologicalSpace 𝓓^{n}(Ω, F) :=
  ⨆ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
    coinduced (ofSupportedIn K_sub_Ω) ContDiffMapSupportedIn.topologicalSpace

variable (Ω F n) in
/-- The canonical LF topology on `𝓓^{n}(Ω, F)`. This makes `𝓓^{n}(Ω, F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of locally convex topological vector spaces**
(over ℝ). See `TestFunction.continuous_iff_continuous_comp` for the corresponding universal
property.

More concretely, this is defined as the infimum of *all* locally convex topologies which are
coarser than the "original topology" `TestFunction.originalTop`, which corresponds to taking
the inductive limit in the category of topological spaces. -/
/-
**TestFunction.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
形式化陈述：topologicalSpace : TopologicalSpace 𝓓^{n}(Ω, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical LF topology on `𝓓^{n}(Ω, F)`. This makes `𝓓^{n}(Ω, F)` the inducti
ve
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of locally convex topological 
vector spaces**
(over ℝ). See `TestFunction.continuous_iff_continuous_comp` for the correspondin
g universal
property.

More concretely, this is defined as the infimum of *all* locally convex topologi
es which are
coarser than the "original topology" `TestFunction.originalTop`, which correspon
ds to taking
the inductive limit in the category of topological spaces.
-/
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(Ω, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(Ω, F) | originalTop Ω F n ≤ t ∧
    @IsTopologicalAddGroup 𝓓^{n}(Ω, F) t _ ∧
    @ContinuousSMul ℝ 𝓓^{n}(Ω, F) _ _ t ∧
    @LocallyConvexSpace ℝ 𝓓^{n}(Ω, F) _ _ _ _ t}
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsTopologicalAddGroup 𝓓^{n}(Ω, F) :=
  topologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ ↦ ht
/-
**TestFunction.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
形式化陈述：uniformSpace : UniformSpace 𝓓^{n}(Ω, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
-/
noncomputable instance uniformSpace : UniformSpace 𝓓^{n}(Ω, F) :=
  IsTopologicalAddGroup.rightUniformSpace 𝓓^{n}(Ω, F)
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsUniformAddGroup 𝓓^{n}(Ω, F) :=
  isUniformAddGroup_of_addCommGroup

-- TODO: deduce for `RCLike` field `𝕂`
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ContinuousSMul ℝ 𝓓^{n}(Ω, F) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ ↦ ht
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(Ω, F) :=
  .sInf fun _ ⟨_, _, _, ht⟩ ↦ ht
/-
**TestFunction.originalTop_le** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：originalTop_le : originalTop Ω F n <= topologicalSpace Ω F n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem originalTop_le : originalTop Ω F n ≤ topologicalSpace Ω F n :=
  le_sInf fun _t ⟨ht, _⟩ ↦ ht

/-- Fix a locally convex topology `t` on `𝓓^{n}(Ω, F)`. `t` is coarser than the canonical topology
on `𝓓^{n}(Ω, F)` if and only if it is coarser than the "original topology" given by
`TestFunction.originalTop`. -/
/-
**TestFunction.topologicalSpace_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：topologicalSpace_le_iff {t : TopologicalSpace 𝓓^{n}(Ω, F)} [@IsTopological
AddGroup _ t _] [@ContinuousSMul Real _ _ _ t] [@LocallyConvexSpace Real _ _ _ _
 _ t] : topologicalSpace Ω F n <= t ↔ originalTop Ω F n <= t
参数：Ω, F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `TestFunction.originalTop_le`：originalTop_le : originalTop Ω F n <= topol
ogicalSpace Ω F n
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
Fix a locally convex topology `t` on `𝓓^{n}(Ω, F)`. `t` is coarser than the cano
nical topology
on `𝓓^{n}(Ω, F)` if and only if it is coarser than the "original topology" given
 by
`TestFunction.originalTop`.
-/
theorem topologicalSpace_le_iff {t : TopologicalSpace 𝓓^{n}(Ω, F)}
    [@IsTopologicalAddGroup _ t _] [@ContinuousSMul ℝ _ _ _ t]
    [@LocallyConvexSpace ℝ _ _ _ _ _ t] :
    topologicalSpace Ω F n ≤ t ↔ originalTop Ω F n ≤ t :=
  ⟨le_trans originalTop_le, fun H ↦ sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

/-- For every compact `K ⊆ Ω`, the inclusion map `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous. It is in fact a topological embedding, though this fact is not in Mathlib yet. -/
@[fun_prop]
/-
**TestFunction.continuous_ofSupportedIn** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`
。
形式化陈述：continuous_ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq 
Ω) : Continuous (ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) -> 𝓓^{n}(Ω, F))
参数：K_sub_Ω : (K : Set E) subseteq Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `TestFunction.originalTop_le`：originalTop_le : originalTop Ω F n <= topol
ogicalSpace Ω F n

--- 原说明 ---
For every compact `K ⊆ Ω`, the inclusion map `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous. It is in fact a topological embedding, though this fact is not in Ma
thlib yet.
-/
theorem continuous_ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) :
    Continuous (ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) := by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le

variable (𝕜) in
/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)`, when `K ⊆ Ω`, as a continuous
linear map. -/
/-
**TestFunction.ofSupportedInCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：ofSupportedInCLM [SMulCommClass Real 𝕜 F] {K : Compacts E} (K_sub_Ω : (K :
 Set E) subseteq Ω) : 𝓓^{n}_{K}(E, F) ->L[𝕜] 𝓓^{n}(Ω, F) where toFun f
参数：K_sub_Ω : (K : Set E) subseteq Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)`, when `K ⊆ Ω`, as a contin
uous
linear map.
-/
noncomputable def ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}(Ω, F) where
  toFun f := ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**TestFunction.coe_ofSupportedInCLM** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] {Ω : TopologicalSpace.Open
s E} {F : Type u_4} [inst_3 : NormedAddCommGroup F]   [inst_4 : NormedSpace ℝ F]
 [inst_5 : NormedSpace 𝕜 F] {n : ℕ∞} [inst_6 : SMulCommClass ℝ 𝕜 F]   {K : Topol
ogicalSpace.Compacts E} (K_sub_Ω : ↑K ⊆ ↑Ω),   ⇑(TestFunction.ofSupportedInCLM 𝕜
 K_sub_Ω) = TestFunction.ofSupportedIn K_sub_Ω
参数：K_sub_Ω : ↑K ⊆ ↑Ω；TestFunction.ofSupportedInCLM 𝕜 K_sub_Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] theorem coe_ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    (ofSupportedInCLM 𝕜 K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) = ofSupportedIn K_sub_Ω :=
  rfl

/-- The **universal property** of the topology on `𝓓^{n}(Ω, F)`: a **linear** map from
`𝓓^{n}(Ω, F)` to a locally convex topological vector space is continuous if and only if its
precomposition with the inclusion `ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous for every compact `K ⊆ Ω`. -/
/-
**TestFunction.continuous_iff_continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `TestFun
ction`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] {Ω : TopologicalSpace.Open
s E} {F : Type u_4} [inst_3 : NormedAddCommGroup F]   [inst_4 : NormedSpace ℝ F]
 [inst_5 : NormedSpace 𝕜 F] {n : ℕ∞} {V : Type u_6} [inst_6 : AddCommGroup V]   
[inst_7 : _root_.Module ℝ V] [t : TopologicalSpace V] [IsTopologicalAddGroup V] 
[ContinuousSMul ℝ V]   [LocallyConvexSpace ℝ V] [inst_11 : Algebra ℝ 𝕜] [inst_12
 : IsScalarTower ℝ 𝕜 F] [inst_13 : _root_.Module 𝕜 V]   [IsScalarTower ℝ 𝕜 V] (f
 : TestFunction Ω F n →ₗ[𝕜] V),   Continuous ⇑f ↔     ∀ (K : TopologicalSpace.Co
mpacts E) (K_sub_Ω : ↑K ⊆ ↑Ω), Continuous (⇑f ∘ TestFunction.ofSupportedIn K_sub
_Ω)
参数：f : TestFunction Ω F n →ₗ[𝕜] V；K : TopologicalSpace.Compacts E；K_sub_Ω : ↑K ⊆
 ↑Ω；⇑f ∘ TestFunction.ofSupportedIn K_sub_Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TestFunction.instIsScalarTower`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `continuousSMul_induced`：continuousSMul_induced : @ContinuousSMul R M₁ _ 
u (t.induced f)
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LocallyConvexSpace.induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u_
4} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [i
nst_3 : _root_.M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The **universal property** of the topology on `𝓓^{n}(Ω, F)`: a **linear** map fr
om
`𝓓^{n}(Ω, F)` to a locally convex topological vector space is continuous if and 
only if its
precomposition with the inclusion `ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{
n}(Ω, F)` is
continuous for every compact `K ⊆ Ω`.
-/
protected theorem continuous_iff_continuous_comp [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]
    [Module 𝕜 V] [IsScalarTower ℝ 𝕜 V] (f : 𝓓^{n}(Ω, F) →ₗ[𝕜] V) :
    Continuous f ↔ ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (f ∘ ofSupportedIn K_sub_Ω) := by
  simp_rw [← f.coe_restrictScalars ℝ]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars ℝ) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul ℝ _ _ _ (induced (f.restrictScalars ℝ) t) := continuousSMul_induced _
  have : @LocallyConvexSpace ℝ _ _ _ _ _ (induced (f.restrictScalars ℝ) t) := .induced _
  simp_rw [topologicalSpace_le_iff, originalTop, iSup₂_le_iff, ← continuous_iff_le_induced,
    continuous_coinduced_dom]

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `limitCLM`. -/
@[simps]
/-
**TestFunction.mkCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：(𝕜 : Type u_1) →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_3}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace ℝ E] → 
          {Ω : TopologicalSpace.Opens E} →             {F : Type u_4} →         
      [inst_3 : NormedAddCommGroup F] →                 [inst_4 : NormedSpace ℝ 
F] →                   [inst_5 : NormedSpace 𝕜 F] →                     {n : ℕ∞}
 →                       {V : Type u_6} →                         [inst_6 : AddC
ommGroup V] →                           [inst_7 : _root_.Module ℝ V] →          
                   [t : TopologicalSpace V] →                               [IsT
opologicalAddGroup V] →                                 [ContinuousSMul ℝ V] →  
                                 [LocallyConvexSpace ℝ V] →                     
                [inst_11 : Algebra ℝ 𝕜] →                                       
[inst_12 : IsScalarTower ℝ 𝕜 F] →                                         [inst_
13 : _root_.Module 𝕜 V] →                                           [IsScalarTow
er ℝ 𝕜 V] →                                             (toFun : TestFunction Ω 
F n → V) →                                               (∀ (f g : TestFunction 
Ω F n), toFun (f + g) = toFun f + toFun g) →                                    
             (∀ (c : 𝕜) (f : TestFunction Ω F n), toFun (c • f) = c • toFun f) →
                                                   (∀ (K : TopologicalSpace.Comp
acts E) (K_sub_Ω : ↑K ⊆ ↑Ω),                                                    
   Continuous (toFun ∘ TestFunction.ofSupportedIn K_sub_Ω)) →                   
                                  TestFunction Ω F n →L[𝕜] V
参数：f g : TestFunction Ω F n；f + g；c : 𝕜；f : TestFunction Ω F n；c • f；K : Topolog
icalSpace.Compacts E；K_sub_Ω : ↑K ⊆ ↑Ω；toFun ∘ TestFunction.ofSupportedIn K_sub_
Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the
 form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` i
s an arbitrary
locally convex topological vector space. See also `limitCLM`.
-/
protected noncomputable def mkCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [Module 𝕜 V]
    [IsScalarTower ℝ 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) → V)
    (map_add : ∀ f g, toFun (f + g) = toFun f + toFun g)
    (map_smul : ∀ c : 𝕜, ∀ f, toFun (c • f) = c • toFun f)
    (cont : ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (toFun ∘ ofSupportedIn K_sub_Ω)) :
    𝓓^{n}(Ω, F) →L[𝕜] V :=
  letI Φ : 𝓓^{n}(Ω, F) →ₗ[𝕜] V := ⟨⟨toFun, map_add⟩, map_smul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by rwa [TestFunction.continuous_iff_continuous_comp] }

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `mkCLM`. -/
@[simps!]
/-
**TestFunction.limitCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：(𝕜 : Type u_1) →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_3}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace ℝ E] → 
          {Ω : TopologicalSpace.Opens E} →             {F : Type u_4} →         
      [inst_3 : NormedAddCommGroup F] →                 [inst_4 : NormedSpace ℝ 
F] →                   [inst_5 : NormedSpace 𝕜 F] →                     {n : ℕ∞}
 →                       {V : Type u_6} →                         [inst_6 : AddC
ommGroup V] →                           [inst_7 : _root_.Module ℝ V] →          
                   [t : TopologicalSpace V] →                               [IsT
opologicalAddGroup V] →                                 [ContinuousSMul ℝ V] →  
                                 [LocallyConvexSpace ℝ V] →                     
                [inst_11 : Algebra ℝ 𝕜] →                                       
[inst_12 : IsScalarTower ℝ 𝕜 F] →                                         [inst_
13 : _root_.Module 𝕜 V] →                                           [IsScalarTow
er ℝ 𝕜 V] →                                             (toFun : TestFunction Ω 
F n → V) →                                               (T :                   
                                (K : TopologicalSpace.Compacts E) →             
                                        ↑K ⊆ ↑Ω → ContDiffMapSupportedIn E F n K
 →L[𝕜] V) →                                                 (∀ (K : TopologicalS
pace.Compacts E) (K_sub_Ω : ↑K ⊆ ↑Ω)                                            
         (f : ContDiffMapSupportedIn E F n K),                                  
                   toFun (TestFunction.ofSupportedIn K_sub_Ω f) = (T K K_sub_Ω) 
f) →                                                   TestFunction Ω F n →L[𝕜] 
V
参数：K : TopologicalSpace.Compacts E；K : TopologicalSpace.Compacts E；K_sub_Ω : ↑K 
⊆ ↑Ω；f : ContDiffMapSupportedIn E F n K；TestFunction.ofSupportedIn K_sub_Ω f；T K
 K_sub_Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the
 form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` i
s an arbitrary
locally convex topological vector space. See also `mkCLM`.
-/
protected noncomputable def limitCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [Module 𝕜 V]
    [IsScalarTower ℝ 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) → V)
    (T : Π (K : Compacts E), (K : Set E) ⊆ Ω → 𝓓^{n}_{K}(E, F) →L[𝕜] V)
    (toFun_eq_T : ∀ K K_sub_Ω f, toFun (ofSupportedIn K_sub_Ω f) = T K K_sub_Ω f) :
    𝓓^{n}(Ω, F) →L[𝕜] V :=
  haveI toFun_add (f g : 𝓓^{n}(Ω, F)) : toFun (f + g) = toFun f + toFun g := by
    set K : Compacts E := ⟨tsupport f ∪ tsupport g, .union f.hasCompactSupport g.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) ⊆ Ω := union_subset f.tsupport_subset g.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset f.contDiff (subset_closure.trans subset_union_left)
    let g_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset g.contDiff (subset_closure.trans subset_union_right)
    change toFun (ofSupportedIn K_sub_Ω (f_K + g_K)) =
      toFun (ofSupportedIn K_sub_Ω f_K) + toFun (ofSupportedIn K_sub_Ω g_K)
    simp [toFun_eq_T]
  haveI toFun_smul (c : 𝕜) (f : 𝓓^{n}(Ω, F)) : toFun (c • f) = c • toFun f := by
    set K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) ⊆ Ω := f.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) := .of_support_subset f.contDiff subset_closure
    change toFun (ofSupportedIn K_sub_Ω (c • f_K)) = c • toFun (ofSupportedIn K_sub_Ω f_K)
    simp [toFun_eq_T]
  TestFunction.mkCLM 𝕜 toFun toFun_add toFun_smul
    (fun K K_sub_Ω ↦ .congr (T K K_sub_Ω).continuous (fun f ↦ (toFun_eq_T K K_sub_Ω f).symm))

end Topology

section ToBoundedContinuousFunctionCLM

variable (𝕜) in
/-- The inclusion of the space `𝓓^{n}(Ω, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
@[simps! apply]
/-
**TestFunction.toBoundedContinuousFunctionCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFun
ction`。
形式化陈述：toBoundedContinuousFunctionCLM [Algebra Real 𝕜] [IsScalarTower Real 𝕜 F] :
 𝓓^{n}(Ω, F) ->L[𝕜] E ->ᵇ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the space `𝓓^{n}(Ω, F)` into the space `E →ᵇ F` of bounded cont
inuous
functions as a continuous `𝕜`-linear map.
-/
noncomputable def toBoundedContinuousFunctionCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] :
    𝓓^{n}(Ω, F) →L[𝕜] E →ᵇ F :=
  TestFunction.mkCLM 𝕜 (↑) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous)
/-
**TestFunction.toBoundedContinuousFunctionCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位
于命名空间 `TestFunction`。
形式化陈述：toBoundedContinuousFunctionCLM_eq_of_scalars [Algebra Real 𝕜] [IsScalarTow
er Real 𝕜 F] (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algeb
ra Real 𝕜'] [IsScalarTower Real 𝕜' F] : (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n
}(Ω, F) -> _) = toBoundedContinuousFunctionCLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toBoundedContinuousFunctionCLM_eq_of_scalars [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) → _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
/-
**TestFunction.injective_toBoundedContinuousFunctionCLM** 是 Mathlib 中的一个定理，位于命名空
间 `TestFunction`。
形式化陈述：injective_toBoundedContinuousFunctionCLM [Algebra Real 𝕜] [IsScalarTower R
eal 𝕜 F] : Function.Injective (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) ->
L[𝕜] E ->ᵇ F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TestFunction.mkCLM_apply`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E
] {Ω : Topolog…
· 使用定理 `BoundedContinuousFunction.mk.injEq`：∀ {α : Type u} {β : Type v} [inst : 
TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (toContinuousMap : C(α, β))  
 (map_bounded' : ∃ C, ∀ …
· 使用定理 `ContinuousMap.mk.injEq`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (toFun : X → Y)   (continuous_toFun : 
autoParam (C…
-/
theorem injective_toBoundedContinuousFunctionCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] :
    Function.Injective (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) →L[𝕜] E →ᵇ F) :=
  fun f g ↦ by simp [toBoundedContinuousFunctionCLM]
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousEval 𝓓^{n}(Ω, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM ℝ).continuous
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T3Space 𝓓^{n}(Ω, F) :=
  suffices T2Space 𝓓^{n}(Ω, F) from inferInstance
  .of_injective_continuous (injective_toBoundedContinuousFunctionCLM ℝ)
    (ContinuousLinearMap.continuous _)

end ToBoundedContinuousFunctionCLM

section postcomp

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 F']

-- Note: generalizing this to a semilinear setting would require a typeclass-way of saying that
-- the `RingHom` is `ℝ`-linear.
/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}(Ω, F)` to `T ∘ f` as an element of `𝓓^{n}(Ω, F')`. -/
/-
**TestFunction.postcompCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：postcompCLM (T : F ->L[𝕜] F') : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{n}(Ω, F')
参数：T : F ->L[𝕜] F'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instContinuousSMulReal`：∀ {E : Type u_3} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type 
u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instLocallyConvexSpaceReal`：∀ {E : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : T
ype u_4}   [inst_2 : NormedAd…

--- 原说明 ---
Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}(Ω, F)` to `T ∘ f` as an element of `𝓓^{n}(Ω, F')`.
-/
noncomputable def postcompCLM (T : F →L[𝕜] F') :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, F') :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{n}(Ω, F') :=
    ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
      f.hasCompactSupport.comp_left (map_zero _),
      (tsupport_comp_subset (map_zero _) f).trans f.tsupport_subset⟩
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω ↦ ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.postcompCLM T)
    (fun _ _ _ ↦ by ext; simp [Φ])

@[simp]
/-
**TestFunction.postcompCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：postcompCLM_apply (T : F ->L[𝕜] F') (f : 𝓓^{n}(Ω, F)) : postcompCLM T f = 
T ∘ f
参数：T : F ->L[𝕜] F'；f : 𝓓^{n}(Ω, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma postcompCLM_apply (T : F →L[𝕜] F')
    (f : 𝓓^{n}(Ω, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

end postcomp

section Monotone

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
/-- If `n₁ ≥ n₂` and `Ω₁ ⊆ Ω₂`, `monoCLM 𝕜` is the continuous `𝕜`-linear inclusion of
`𝓓^{n₁}(Ω₁, F)` inside `𝓓^{n₂}(Ω₂, F)`. Otherwise, this is the zero map.

This is in fact a topological embedding when `n₁ = n₂` and `Ω₁ ⊆ Ω₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, Ω₁, Ω₂` are implicit as they can often be inferred from context, or
specified by a type ascription. -/
/-
**TestFunction.monoCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：monoCLM : 𝓓^{n₁}(Ω₁, F) ->L[𝕜] 𝓓^{n₂}(Ω₂, F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instContinuousSMulReal`：∀ {E : Type u_3} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type 
u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instLocallyConvexSpaceReal`：∀ {E : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : T
ype u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…

--- 原说明 ---
If `n₁ ≥ n₂` and `Ω₁ ⊆ Ω₂`, `monoCLM 𝕜` is the continuous `𝕜`-linear inclusion o
f
`𝓓^{n₁}(Ω₁, F)` inside `𝓓^{n₂}(Ω₂, F)`. Otherwise, this is the zero map.

This is in fact a topological embedding when `n₁ = n₂` and `Ω₁ ⊆ Ω₂` (not in Mat
hlib as of
March 2026).

The parameters `n₁, n₂, Ω₁, Ω₂` are implicit as they can often be inferred from 
context, or
specified by a type ascription.
-/
noncomputable def monoCLM :
    𝓓^{n₁}(Ω₁, F) →L[𝕜] 𝓓^{n₂}(Ω₂, F) :=
  open scoped Classical in
  letI Φ (f : 𝓓^{n₁}(Ω₁, F)) : 𝓓^{n₂}(Ω₂, F) :=
    if h : n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂ then
      ⟨f, f.contDiff.of_le (mod_cast h.1), f.hasCompactSupport, f.tsupport_subset.trans h.2⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω₁ ↦ if h : n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂
      then ofSupportedInCLM 𝕜 (K_sub_Ω₁.trans h.2) ∘L ContDiffMapSupportedIn.monoCLM 𝕜
      else 0)
    (fun _ _ _ ↦ by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

open scoped Classical in
@[simp]
/-
**TestFunction.monoCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：monoCLM_apply (f : 𝓓^{n₁}(Ω₁, F)) : ((monoCLM 𝕜 f : 𝓓^{n₂}(Ω₂, F)) : E -> 
F) = if n₂ <= n₁ ∧ Ω₁ <= Ω₂ then f else 0
参数：f : 𝓓^{n₁}(Ω₁, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instContinuousSMulReal`：∀ {E : Type u_3} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type 
u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instLocallyConvexSpaceReal`：∀ {E : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : T
ype u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TestFunction.monoCLM.eq_1`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ 
E] {Ω₁ Ω₂ : Top…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TestFunction.limitCLM.congr_simp`：∀ (𝕜 : Type u_1) [inst : NontriviallyN
ormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace ℝ E] {Ω : Topolog…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma monoCLM_apply (f : 𝓓^{n₁}(Ω₁, F)) :
    ((monoCLM 𝕜 f : 𝓓^{n₂}(Ω₂, F)) : E → F) = if n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂ then f else 0 := by
  rw [monoCLM]
  split_ifs <;> rfl
/-
**TestFunction.monoCLM_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：monoCLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ Ω₁ <= Ω₂)) : (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F)
 ->L[𝕜] 𝓓^{n₂}(Ω₂, F)) = 0
参数：H : ¬ (n₂ <= n₁ ∧ Ω₁ <= Ω₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TestFunction.monoCLM_apply`：monoCLM_apply (f : 𝓓^{n₁}(Ω₁, F)) : ((monoCL
M 𝕜 f : 𝓓^{n₂}(Ω₂, F)) : E -> F) = if n₂ <= n₁ ∧ Ω₁ <= Ω₂ then f else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `TestFunction.instIsZeroApply`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monoCLM_eq_zero (H : ¬ (n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂)) :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) →L[𝕜] 𝓓^{n₂}(Ω₂, F)) = 0 := by
  ext; simp [H]
/-
**TestFunction.monoCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：monoCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpa
ce 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] : (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F
) -> 𝓓^{n₂}(Ω₂, F)) = monoCLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) → 𝓓^{n₂}(Ω₂, F)) = monoCLM 𝕜' :=
  rfl

end Monotone

section FDerivCLM

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜 n k) in
/-- `fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map. -/
/-
**TestFunction.fderivCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, E ->L[Real] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)`
 to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the
 zero map.
-/
noncomputable def fderivCLM :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F) :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{k}(Ω, E →L[ℝ] F) :=
    if hk : k + 1 ≤ n then
      ⟨fderiv ℝ f, f.contDiff.fderiv_right (mod_cast hk),
        f.hasCompactSupport.fderiv ℝ, tsupport_fderiv_subset ℝ |>.trans f.tsupport_subset⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω ↦ ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.fderivCLM 𝕜 n k)
    (fun _ _ _ ↦ by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

@[simp]
/-
**TestFunction.fderivCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderivCLM 𝕜 n k f = if k + 1 <= n then
 fderiv Real f else 0
参数：f : 𝓓^{n}(Ω, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TestFunction.fderivCLM.eq_1`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormed
Field 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
ℝ E] {Ω : Topolog…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TestFunction.limitCLM.congr_simp`：∀ (𝕜 : Type u_1) [inst : NontriviallyN
ormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace ℝ E] {Ω : Topolog…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma fderivCLM_apply (f : 𝓓^{n}(Ω, F)) :
    fderivCLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 := by
  rw [fderivCLM]
  split_ifs <;> rfl
/-
**TestFunction.fderivCLM_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM_apply_of_le (f : 𝓓^{n}(Ω, F)) (hk : k + 1 <= n) : fderivCLM 𝕜 n 
k f = fderiv Real f
参数：f : 𝓓^{n}(Ω, F)；hk : k + 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCLM_apply_of_le (f : 𝓓^{n}(Ω, F)) (hk : k + 1 ≤ n) :
    fderivCLM 𝕜 n k f = fderiv ℝ f := by
  simp [hk]
/-
**TestFunction.fderivCLM_apply_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM_apply_of_gt (hk : n < k + 1) : (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) ->
L[𝕜] 𝓓^{k}(Ω, E ->L[Real] F)) = 0
参数：hk : n < k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `TestFunction.instIsZeroApply`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCLM_apply_of_gt (hk : n < k + 1) :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F)) = 0 := by
  ext : 2
  simp [not_le_of_gt hk]

variable (𝕜) in
/-
**TestFunction.fderivCLM_ofSupportedIn** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM_ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) subseteq Ω
) (f : 𝓓^{n}_{K}(E, F)) : fderivCLM 𝕜 n k (ofSupportedIn K_sub_Ω f) = ofSupporte
dIn K_sub_Ω (ContDiffMapSupportedIn.fderivCLM 𝕜 n k f)
参数：K_sub_Ω : (K : Set E) subseteq Ω；f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `TestFunction.coe_ofSupportedIn`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用引理 `ContDiffMapSupportedIn.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}_{K}(E
, F)) : fderivCLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCLM_ofSupportedIn {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k (ofSupportedIn K_sub_Ω f) =
      ofSupportedIn K_sub_Ω (ContDiffMapSupportedIn.fderivCLM 𝕜 n k f) := by
  ext
  simp

variable (𝕜) in
/-
**TestFunction.fderivCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：fderivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedS
pace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] : (fderivCLM 𝕜 n k : 𝓓^{n
}(Ω, F) -> _) = fderivCLM 𝕜' n k
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
lemma fderivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) → _) = fderivCLM 𝕜' n k :=
  rfl

end FDerivCLM

section LineDerivCLM

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- `lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative along the vector `v`, which is an element of `𝓓^{k}_{K}(E, F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

The parameters `n` and `k` are implicit as they can often be inferred from context, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of the `LineDeriv`
notation typeclass. -/
/-
**TestFunction.lineDerivCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：lineDerivCLM (v : E) : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)
参数：v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)
` to
its derivative along the vector `v`, which is an element of `𝓓^{k}_{K}(E, F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the
 zero map.

The parameters `n` and `k` are implicit as they can often be inferred from conte
xt, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of th
e `LineDeriv`
notation typeclass.
-/
noncomputable def lineDerivCLM (v : E) :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F) :=
  -- Cannot use `ContinuousLinearMap.apply` here because we are mixing `ℝ` and `𝕜`
  letI ev_v : (E →L[ℝ] F) →L[𝕜] F :=
  { toFun f := f v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  postcompCLM ev_v ∘L fderivCLM 𝕜 n k
/-
**TestFunction.lineDerivCLM_eq_fderivCLM** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction
`。
形式化陈述：lineDerivCLM_eq_fderivCLM {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} : (lineDerivCL
M 𝕜 v f : 𝓓^{k}(Ω, F)) x = fderivCLM 𝕜 n k f x v
参数：Ω, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma lineDerivCLM_eq_fderivCLM {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = fderivCLM 𝕜 n k f x v :=
  rfl

@[simp]
/-
**TestFunction.lineDerivCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} : (lineDerivCLM 𝕜 v f
 : 𝓓^{k}(Ω, F)) x = if k + 1 <= n then lineDeriv Real f x v else 0
参数：Ω, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TestFunction.lineDerivCLM_eq_fderivCLM`：lineDerivCLM_eq_fderivCLM {f : 𝓓
^{n}(Ω, F)} {v : E} {x : E} : (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = fderivCLM 𝕜
 n k f x v
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `DifferentiableAt.lineDeriv_eq_fderiv`：DifferentiableAt.lineDeriv_eq_fder
iv (hf : DifferentiableAt 𝕜 f x) : lineDeriv 𝕜 f x v = fderiv 𝕜 f x v
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `TestFunction.contDiff`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2
 : NormedAd…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 31 条，此处仅展示前 30 条）
-/
lemma lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = if k + 1 ≤ n then lineDeriv ℝ f x v else 0 := by
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply]
  split_ifs with hk
  · have hk' : 0 < (n : ℕ∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    rw [(f.contDiff.differentiable hk'.ne').differentiableAt.lineDeriv_eq_fderiv]
  · rfl
/-
**TestFunction.lineDerivCLM_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`
。
形式化陈述：lineDerivCLM_apply_of_le {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 <= 
n) : (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = lineDeriv Real f x v
参数：Ω, F；hk : k + 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TestFunction.lineDerivCLM_apply`：lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v
 : E} {x : E} : (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = if k + 1 <= n then lineDe
riv Real f x v else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_apply_of_le {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 ≤ n) :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = lineDeriv ℝ f x v := by
  simp [hk]
/-
**TestFunction.lineDerivCLM_apply_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`
。
形式化陈述：lineDerivCLM_apply_of_gt {v : E} (hk : n < k + 1) : (lineDerivCLM 𝕜 v : 𝓓^
{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) = 0
参数：hk : n < k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TestFunction.lineDerivCLM_apply`：lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v
 : E} {x : E} : (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = if k + 1 <= n then lineDe
riv Real f x v else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `TestFunction.instIsZeroApply`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_apply_of_gt {v : E} (hk : n < k + 1) :
    (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) = 0 := by
  ext
  simp [not_le_of_gt hk]

variable (𝕜) in
/-
**TestFunction.lineDerivCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `TestFunctio
n`。
形式化陈述：lineDerivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [Norm
edSpace 𝕜' F] [Algebra Real 𝕜'] [IsScalarTower Real 𝕜' F] {v : E} : (lineDerivCL
M 𝕜 v : 𝓓^{n}(Ω, F) -> 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜' v
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma lineDerivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F]
    {v : E} : (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) → 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜' v :=
  rfl
/-
**TestFunction.lineDerivCLM_add** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：lineDerivCLM_add {v₁ v₂ : E} : (lineDerivCLM 𝕜 (v₁ + v₂) : 𝓓^{n}(Ω, F) ->L
[𝕜] 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜 v₁ + lineDerivCLM 𝕜 v₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `TestFunction.instIsAddApply`：∀ {E : Type u_3} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [
inst_2 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM 𝕜 (v₁ + v₂) : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) =
      lineDerivCLM 𝕜 v₁ + lineDerivCLM 𝕜 v₂ := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]
/-
**TestFunction.lineDerivCLM_smul** 是 Mathlib 中的一个引理，位于命名空间 `TestFunction`。
形式化陈述：lineDerivCLM_smul {c : Real} {v : E} : (lineDerivCLM 𝕜 (c • v) : 𝓓^{n}(Ω, 
F) ->L[𝕜] 𝓓^{k}(Ω, F)) = c • lineDerivCLM 𝕜 v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TestFunction.instIsScalarTower`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `TestFunction.instContinuousSMulReal`：∀ {E : Type u_3} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type 
u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.ext`：ext {f g : 𝓓^{n}(Ω, F)} (h : forall a, f a = g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `TestFunction.fderivCLM_apply`：fderivCLM_apply (f : 𝓓^{n}(Ω, F)) : fderiv
CLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `TestFunction.instIsSMulApply`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_smul {c : ℝ} {v : E} :
    (lineDerivCLM 𝕜 (c • v) : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) =
      c • lineDerivCLM 𝕜 v := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

open LineDeriv

/-- Note: we cannot express the full generality of `lineDerivCLM` purely in terms of this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the input type
`𝓓^{n}_{K}(E, F)`. -/
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: we cannot express the full generality of `lineDerivCLM` purely in terms of
 this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the i
nput type
`𝓓^{n}_{K}(E, F)`.
-/
noncomputable instance : LineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp v := lineDerivCLM ℝ v

variable (𝕜) in
/-
**TestFunction.lineDerivOp_eq_lineDerivCLM** 是 Mathlib 中的一个引理，位于命名空间 `TestFuncti
on`。
形式化陈述：lineDerivOp_eq_lineDerivCLM {v : E} {f : 𝓓(Ω, F)} : ∂_{v} f = lineDerivCLM
 𝕜 v f
参数：Ω, F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lineDerivOp_eq_lineDerivCLM {v : E} {f : 𝓓(Ω, F)} :
    ∂_{v} f = lineDerivCLM 𝕜 v f :=
  rfl
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivAdd E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM ℝ v)
  lineDerivOp_left_add _ _ f := congr($lineDerivCLM_add f)
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivSMul 𝕜 E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM 𝕜 v)
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivLeftSMul ℝ E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_left_smul _ _ f := congr($lineDerivCLM_smul f)
/-
**TestFunction.** 是 Mathlib 中的一个实例，位于命名空间 `TestFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ContinuousLineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM ℝ v).continuous
/-
**TestFunction.lineDerivOpCLM_eq_lineDerivCLM** 是 Mathlib 中的一个引理，位于命名空间 `TestFun
ction`。
形式化陈述：lineDerivOpCLM_eq_lineDerivCLM {v : E} : lineDerivOpCLM 𝕜 𝓓(Ω, F) v = line
DerivCLM 𝕜 v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TestFunction.instLineDerivAddTopENat`：∀ {E : Type u_3} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type
 u_4}   [inst_2 : NormedAd…
· 使用定理 `TestFunction.instLineDerivSMulTopENat`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace ℝ E] {Ω : Topolog…
· 使用定理 `TestFunction.instContinuousLineDerivTopENat`：∀ {E : Type u_3} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F
 : Type u_4}   [inst_2 : NormedAd…
-/
lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM 𝕜 𝓓(Ω, F) v = lineDerivCLM 𝕜 v :=
  rfl

end LineDerivCLM

section Integral

open MeasureTheory

variable {m : MeasurableSpace E} [OpensMeasurableSpace E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
/-
**TestFunction.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} {m : MeasurableSpace E} [OpensMeasurableSpac
e E]   (f : TestFunction Ω F n), MeasureTheory.StronglyMeasurable ⇑f
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.stronglyMeasurable_of_hasCompactSupport`：∀ {α : Type u_1} {β 
: Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasu
rableSpace α]   [inst_3 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TestFunction.continuous`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst
_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
-/
protected theorem stronglyMeasurable (f : 𝓓^{n}(Ω, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
/-
**TestFunction.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} {m : MeasurableSpace E} [OpensMeasurableSpac
e E]   {μ : MeasureTheory.Measure E} (f : TestFunction Ω F n), MeasureTheory.AES
tronglyMeasurable (⇑f) μ
参数：f : TestFunction Ω F n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `TestFunction.stronglyMeasurable`：∀ {E : Type u_3} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}
   [inst_2 : NormedAd…
-/
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable
/-
**TestFunction.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} {m : MeasurableSpace E} [OpensMeasurableSpac
e E]   {μ : MeasureTheory.Measure E} (f : TestFunction Ω F n), MeasureTheory.Mem
Lp ⇑f ⊤ μ
参数：f : TestFunction Ω F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.memLp_top_of_hasCompactSupport`：∀ {E : Type u_4} [inst : Norm
edAddCommGroup E] {X : Type u_7} [inst_1 : TopologicalSpace X] [inst_2 : Measura
bleSpace X]   [OpensMeasurableS…
· 使用定理 `TestFunction.continuous`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst
_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
-/
protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ
/-
**TestFunction.integrable_bilin** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] {Ω : TopologicalSpace.Open
s E} {n : ℕ∞} {m : MeasurableSpace E} [OpensMeasurableSpace E]   {F₁ : Type u_6}
 {F₂ : Type u_7} {F₃ : Type u_8} [inst_4 : NormedAddCommGroup F₁] [inst_5 : Norm
edSpace 𝕜 F₁]   [inst_6 : NormedSpace ℝ F₁] [inst_7 : NormedAddCommGroup F₂] [in
st_8 : NormedSpace 𝕜 F₂]   [inst_9 : NormedAddCommGroup F₃] [inst_10 : NormedSpa
ce 𝕜 F₃] (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : MeasureTheory.Measure E}   {φ : E → F₂}
,   MeasureTheory.LocallyIntegrableOn φ (↑Ω) μ →     ∀ (f : TestFunction Ω F₁ n)
, MeasureTheory.Integrable (fun x => (B (f x)) (φ x)) μ
参数：B : F₁ →L[𝕜] F₂ →L[𝕜] F₃；↑Ω；f : TestFunction Ω F₁ n；fun x => (B (f x)) (φ x)。
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
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TestFunction.tsupport_subset`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ContinuousLinearMap.memLp_of_bilin`：memLp_of_bilin {f : α -> E} {g : α -
> F} (hf : MemLp f p μ) (hg : MemLp g q μ) : MemLp (fun x => B (f x) (g x)) r μ
· 使用定理 `TestFunction.memLp_top`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_
2 : NormedAd…
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
-/
protected theorem integrable_bilin (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) (f : 𝓓^{n}(Ω, F₁)) :
    Integrable (fun x ↦ B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x ↦ B (f x) (φ x)) (tsupport f) μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ (subset_tsupport f)
    exact fun x hx hfx ↦ hx (by simp [hfx])
  replace hφ := hφ.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

/-- A test function on `Ω` is `μ`-integrable for any measure `μ` on `E` satisfying
`LocallyIntegrableOn 1 Ω μ`. Note that this is a weaker assumption than both
- `IsLocallyFiniteMeasure (μ.restrict Ω)` (because we say nothing about points outside of `Ω`)
- `IsFiniteMeasureOnCompacts (μ.restrict Ω)` (because we say nothing about compacts not
  contained in `Ω`)

For example, if `μ` is the measure with density `fun (x : ℝ) ↦ x⁻¹` with respect to the Lebesgue
measure and `Ω` is the open set `Ioo 0 1`, we have `LocallyIntegrableOn 1 Ω μ` (hence `μ` defines
a distribution on `Ω`) but the other two conditions are not satisfied.
-/
/-
**TestFunction.integrable** 是 Mathlib 中的一个定理，位于命名空间 `TestFunction`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_2 : NormedAddCommGroup F] 
[inst_3 : NormedSpace ℝ F] {n : ℕ∞} {m : MeasurableSpace E} [OpensMeasurableSpac
e E]   {μ : MeasureTheory.Measure E},   MeasureTheory.LocallyIntegrableOn (fun x
 => 1) (↑Ω) μ → ∀ (f : TestFunction Ω F n), MeasureTheory.Integrable (⇑f) μ
参数：fun x => 1；↑Ω；f : TestFunction Ω F n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `TestFunction.tsupport_subset`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `TestFunction.hasCompactSupport`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `TestFunction.memLp_top`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   [inst_
2 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
A test function on `Ω` is `μ`-integrable for any measure `μ` on `E` satisfying
`LocallyIntegrableOn 1 Ω μ`. Note that this is a weaker assumption than both
- `IsLocallyFiniteMeasure (μ.restrict Ω)` (because we say nothing about points o
utside of `Ω`)
- `IsFiniteMeasureOnCompacts (μ.restrict Ω)` (because we say nothing about compa
cts not
  contained in `Ω`)

For example, if `μ` is the measure with density `fun (x : ℝ) ↦ x⁻¹` with respect
 to the Lebesgue
measure and `Ω` is the open set `Ioo 0 1`, we have `LocallyIntegrableOn 1 Ω μ` (
hence `μ` defines
a distribution on `Ω`) but the other two conditions are not satisfied.
-/
protected theorem integrable {μ : Measure E}
    (H : LocallyIntegrableOn (fun (_ : E) ↦ (1 : ℝ)) Ω μ)
    (f : 𝓓^{n}(Ω, F)) : Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport f)]
  replace H := H.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  suffices IntegrableOn ((1 : ℝ) • f) (tsupport f) μ by simpa
  rw [IntegrableOn, ← memLp_one_iff_integrable] at H ⊢
  exact f.memLp_top.smul H

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F₁] [NormedSpace ℝ F₃] [IsScalarTower ℝ 𝕜 F₃]

-- TODO: semilinearize
/-- Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on `E`,
and a function `φ : E → F₂` which is locally `μ`-integrable, this is the *continuous* `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}(E, F₁)` to `F₃`. Otherwise, this is the zero map. -/
/-
**TestFunction.integralAgainstBilinCLM** 是 Mathlib 中的一个定义，位于命名空间 `TestFunction`。
形式化陈述：integralAgainstBilinCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : 
E -> F₂) : 𝓓^{n}(Ω, F₁) ->L[𝕜] F₃
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；μ : Measure E；φ : E -> F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on
 `E`,
and a function `φ : E → F₂` which is locally `μ`-integrable, this is the *contin
uous* `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}(E, F₁)` to `F₃`. Otherwise, this is the 
zero map.
-/
noncomputable def integralAgainstBilinCLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂) :
    𝓓^{n}(Ω, F₁) →L[𝕜] F₃ := open scoped Classical in
  TestFunction.limitCLM 𝕜
    (fun f ↦ if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0)
    (fun K K_sub_Ω ↦
      if LocallyIntegrableOn φ Ω μ
      then ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ
      else 0)
    (fun K K_sub_Ω f ↦ by
      split_ifs with h
      · simp [h.integrableOn_compact_subset K_sub_Ω K.2]
      · simp)

open scoped Classical in
@[simp]
/-
**TestFunction.integralAgainstBilinCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `TestFunc
tion`。
形式化陈述：integralAgainstBilinCLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E}
 {φ : E -> F₂} {f : 𝓓^{n}(Ω, F₁)} : integralAgainstBilinCLM B μ φ f = if Locally
IntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0
参数：Ω, F₁。
该定理/引理给出了一组等式。
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
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma integralAgainstBilinCLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinCLM B μ φ f =
      if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0 :=
  rfl
/-
**TestFunction.integralAgainstBilinCLM_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `Te
stFunction`。
形式化陈述：integralAgainstBilinCLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Meas
ure E} {φ : E -> F₂} (hφ : LocallyIntegrableOn φ Ω μ) {f : 𝓓^{n}(Ω, F₁)} : integ
ralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ
参数：hφ : LocallyIntegrableOn φ Ω μ；Ω, F₁。
该定理/引理给出了一组等式。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integralAgainstBilinCLM_eq_integral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ := by
  simp [hφ]
/-
**TestFunction.integralAgainstBilinCLM_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `TestFu
nction`。
形式化陈述：integralAgainstBilinCLM_eq_zero {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure 
E} {φ : E -> F₂} (hφ : ¬ LocallyIntegrableOn φ Ω μ) : (integralAgainstBilinCLM B
 μ φ : 𝓓^{n}(Ω, F₁) ->L[𝕜] F₃) = 0
参数：hφ : ¬ LocallyIntegrableOn φ Ω μ。
该定理/引理给出了一组等式。
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
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integralAgainstBilinCLM_eq_zero {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : ¬ LocallyIntegrableOn φ Ω μ) :
    (integralAgainstBilinCLM B μ φ : 𝓓^{n}(Ω, F₁) →L[𝕜] F₃) = 0 := by
  ext
  simp [hφ]
/-
**TestFunction.integralAgainstBilinCLM_ofSupportedIn** 是 Mathlib 中的一个引理，位于命名空间 `
TestFunction`。
形式化陈述：integralAgainstBilinCLM_ofSupportedIn {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Me
asure E} {φ : E -> F₂} (hφ : LocallyIntegrableOn φ Ω μ) {K : Compacts E} (K_sub_
Ω : (K : Set E) subseteq Ω) {f : 𝓓^{n}_{K}(E, F₁)} : integralAgainstBilinCLM B μ
 φ (ofSupportedIn K_sub_Ω f) = ContDiffMapSupportedIn.integralAgainstBilinCLM B 
μ φ f
参数：hφ : LocallyIntegrableOn φ Ω μ；K_sub_Ω : (K : Set E) subseteq Ω；E, F₁。
该定理/引理给出了一组等式。
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
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TestFunction.coe_ofSupportedIn`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinCLM_apply`：integralAgainstBil
inCLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂} {f : 𝓓^{n
}_{K}(E, F₁)} : integralAgainstBilinCLM B …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integralAgainstBilinCLM_ofSupportedIn {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω)
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ (ofSupportedIn K_sub_Ω f) =
      ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ f := by
  have hφ' := hφ.integrableOn_compact_subset K_sub_Ω K.isCompact
  simp [hφ, hφ']

end Integral

end TestFunction

