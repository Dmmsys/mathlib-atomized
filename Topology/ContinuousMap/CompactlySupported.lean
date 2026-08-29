/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.Algebra.Order.Support
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Compactly supported continuous functions

In this file, we define the type `C_c(α, β)` of compactly supported continuous functions and the
class `CompactlySupportedContinuousMapClass`, and prove basic properties.

## Main definitions and results

This file contains various instances such as `Add`, `Mul`, `SMul F C_c(α, β)` when `F` is a class of
continuous functions.
When `β` has more structures, `C_c(α, β)` inherits such structures as `AddCommGroup`,
`NonUnitalRing` and `StarRing`.

When the domain `α` is compact, `CompactlySupportedContinuousMap.continuousMapEquiv`
gives the identification `C(α, β) ≃ C_c(α, β)`.

-/

@[expose] public section

variable {F α β γ : Type*} [TopologicalSpace α]

/--
Definition of `CompactlySupportedContinuousMap` / `CompactlySupportedContinuousMap` 的定义

English:
structure CompactlySupportedContinuousMap
  parameters: (α β : Type*) [TopologicalSpace α] [Zero β]
  extends: ContinuousMap α β
  axioms and operations (1):
    - hasCompactSupport' : HasCompactSupport toFun

中文:
结构 余mpactlySupportedContinuous映射
  参数: (α β : 类型) [拓扑空间 α] [零 β]
  继承: 连续映射 α β
  公理与运算 (1 个):
    - hasCompactSupport' : HasCompactSupport toFun
-/
structure CompactlySupportedContinuousMap (α β : Type*) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β where
  /-- The function has compact support . -/
  hasCompactSupport' : HasCompactSupport toFun

@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000)
  "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " ->C_c " β => CompactlySupportedContinuousMap α β

open CompactlySupported

section

/--
Definition of `CompactlySupportedContinuousMapClass` / `CompactlySupportedContinuousMapClass` 的定义

English:
class CompactlySupportedContinuousMapClass
  parameters: (F : Type*) (α β : outParam <| Type*)
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - hasCompactSupport((f : F)) : HasCompactSupport f

中文:
类 余mpactlySupportedContinuous映射类
  参数: (F : 类型) (α β : outParam <| 类型)
  继承: 连续映射类 F α β
  公理与运算 (1 个):
    - hasCompactSupport((f : F)) : HasCompactSupport f
-/
class CompactlySupportedContinuousMapClass (F : Type*) (α β : outParam <| Type*)
    [TopologicalSpace α] [Zero β] [TopologicalSpace β] [FunLike F α β] : Prop
    extends ContinuousMapClass F α β where
  /-- Each member of the class has compact support. -/
  hasCompactSupport (f : F) : HasCompactSupport f

end

namespace CompactlySupportedContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike C_c(α, β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 :
  签名: 函数状 C_c(α, β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance : FunLike C_c(α, β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
lemma `hasCompactSupport` / 引理 `hasCompactSupport`

English:
lemma hasCompactSupport
  given: (f : C_c(α, β))
  statement: HasCompactSupport f
  proof: f.hasCompactSupport'

中文:
引理 hasCompactSupport
  条件: (f : C_c(α, β))
  结论: HasCompactSupport f
  证明: f.hasCompactSupport'
-/
protected lemma hasCompactSupport (f : C_c(α, β)) : HasCompactSupport f := f.hasCompactSupport'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactlySupportedContinuousMapClass C_c(α, β) α β
  body: f.continuous_toFun
  hasCompactSupport f := f.hasCompactSupport'

@[simp]

中文:
实例 :
  签名: 余mpactlySupportedContinuous映射类 C_c(α, β) α β
  定义体: f.continuous_toFun
  hasCompactSupport f := f.hasCompactSupport'

@[simp]

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : CompactlySupportedContinuousMapClass C_c(α, β) α β where
  map_continuous f := f.continuous_toFun
  hasCompactSupport f := f.hasCompactSupport'

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (f : C_c(α, β))
  statement: (f.toContinuousMap : α -> β) = f
  proof: rfl

@[ext]

中文:
定理 coe_toContinuousMap
  条件: (f : C_c(α, β))
  结论: (f.toContinuousMap : α -> β) = f
  证明: rfl

@[ext]
-/
theorem coe_toContinuousMap (f : C_c(α, β)) : (f.toContinuousMap : α -> β) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : C_c(α, β)} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[simp]

中文:
定理 ext
  条件: {f g : C_c(α, β)} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : C_c(α, β)} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : C(α, β)) (h : HasCompactSupport f)
  statement: ⇑(⟨f, h⟩ : C_c(α, β)) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : C(α, β)) (h : HasCompactSupport f)
  结论: ⇑(⟨f, h⟩ : C_c(α, β)) = f
  证明: rfl
-/
theorem coe_mk (f : C(α, β)) (h : HasCompactSupport f) : ⇑(⟨f, h⟩ : C_c(α, β)) = f :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  body: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

@[simp]

中文:
定义 copy
  签名: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  定义体: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

@[simp]
-/
protected def copy (f : C_c(α, β)) (f' : α -> β) (h : f' = f) : C_c(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : C_c(α, β)) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : C_c(α, β)) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : C_c(α, β)) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
theorem `eq_of_empty` / 定理 `eq_of_empty`

English:
theorem eq_of_empty
  given: [IsEmpty α] (f g : C_c(α, β))
  statement: f = g
  proof: ext IsEmpty.elim ‹_›

中文:
定理 eq_of_empty
  条件: [是空 α] (f g : C_c(α, β))
  结论: f = g
  证明: ext IsEmpty.elim ‹_›

Depends on / 依赖: IsEmpty, IsEmpty.elim
-/
theorem eq_of_empty [IsEmpty α] (f g : C_c(α, β)) : f = g :=
ext IsEmpty.elim ‹_›

/-- A continuous function on a compact space automatically has compact support. -/
@[simps]
/--
Definition of `continuousMapEquiv` / `continuousMapEquiv` 的定义

English:
definition continuousMapEquiv
  signature: [CompactSpace α]
  body: { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  invFun f := f

中文:
定义 continuousMapEquiv
  签名: [紧空间 α]
  定义体: { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  invFun f := f

Depends on / 依赖: HasCompactSupport, HasCompactSupport.of_compactSpace, hasCompactSupport, invFun, of_compactSpace
-/
def continuousMapEquiv [CompactSpace α] : C(α, β) ≃ C_c(α, β) where
  toFun f :=
    { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  invFun f := f

variable {γ : Type*} [TopologicalSpace γ] [Zero γ]

/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (g : C(β, γ)) (f : C_c(α, β))
  body: by classical exact if g 0 = 0 then g.comp f else 0
  hasCompactSupport' := by
    split_ifs with hg
    · exact f.hasCompactSupport'.comp_left hg
    · exact .zero

中文:
定义 compLeft
  签名: (g : C(β, γ)) (f : C_c(α, β))
  定义体: by classical exact if g 0 = 0 then g.comp f else 0
  hasCompactSupport' := by
    split_ifs with hg
    · exact f.hasCompactSupport'.comp_left hg
    · exact .zero

Depends on / 依赖: classical, comp_left, f.hasCompactSupport, g.comp, hasCompactSupport, split_ifs
-/
noncomputable def compLeft (g : C(β, γ)) (f : C_c(α, β)) : C_c(α, γ) where
  toContinuousMap := by classical exact if g 0 = 0 then g.comp f else 0
  hasCompactSupport' := by
    split_ifs with hg
    · exact f.hasCompactSupport'.comp_left hg
    · exact .zero

/--
lemma `toContinuousMap_compLeft` / 引理 `toContinuousMap_compLeft`

English:
lemma toContinuousMap_compLeft
  given: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β))
  proof: if_pos hg

中文:
引理 toContinuousMap_compLeft
  条件: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β))
  证明: if_pos hg

Depends on / 依赖: if_pos
-/
lemma toContinuousMap_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) :
    (f.compLeft g).toContinuousMap = g.comp f := if_pos hg

/--
lemma `coe_compLeft` / 引理 `coe_compLeft`

English:
lemma coe_compLeft
  given: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β))
  statement: f.compLeft g = g ∘ f
  proof: by
  simp [compLeft, if_pos hg]

中文:
引理 coe_compLeft
  条件: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β))
  结论: f.compLeft g = g ∘ f
  证明: by
  simp [compLeft, if_pos hg]

Depends on / 依赖: compLeft, if_pos
-/
lemma coe_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) : f.compLeft g = g ∘ f := by
  simp [compLeft, if_pos hg]

/--
lemma `compLeft_apply` / 引理 `compLeft_apply`

English:
lemma compLeft_apply
  given: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α)
  proof: by simp [coe_compLeft hg f]

中文:
引理 compLeft_apply
  条件: {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α)
  证明: by simp [coe_compLeft hg f]

Depends on / 依赖: coe_compLeft
-/
lemma compLeft_apply {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α) :
    f.compLeft g a = g (f a) := by simp [coe_compLeft hg f]

/--
Definition of `toBoundedContinuousFunction` / `toBoundedContinuousFunction` 的定义

English:
definition toBoundedContinuousFunction
  signature: {β : Type*} [PseudoMetricSpace β] [Zero β]
  body: f
  map_bounded' := by
    have : IsCompact (Set.range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩

中文:
定义 toBoundedContinuousFunction
  签名: {β : 类型} [伪度量空间 β] [零 β]
  定义体: f
  map_bounded' := by
    have : IsCompact (Set.range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩
-/
@[simps] def toBoundedContinuousFunction {β : Type*} [PseudoMetricSpace β] [Zero β]
    (f : C_c(α, β)) : BoundedContinuousFunction α β where
  toFun := f
  map_bounded' := by
    have : IsCompact (Set.range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩

end Basics

/-! ### Algebraic structure

Whenever `β` has the structure of continuous additive monoid and a compatible topological structure,
then `C_c(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C_c(α, β)` will not have a multiplicative identity.
-/

section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] : Zero C_c(α, β) where
  body: { toFun := (0 : C(α, β))
            continuous_toFun := (0 : C(α, β)).2
            hasCompactSupport' := by simp [HasCompactSupport, tsupport] }

中文:
实例 [零
  签名: β] : 零 C_c(α, β) where
  定义体: { toFun := (0 : C(α, β))
            continuous_toFun := (0 : C(α, β)).2
            hasCompactSupport' := by simp [HasCompactSupport, tsupport] }
-/
instance [Zero β] : Zero C_c(α, β) where
  zero := { toFun := (0 : C(α, β))
            continuous_toFun := (0 : C(α, β)).2
            hasCompactSupport' := by simp [HasCompactSupport, tsupport] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] : Inhabited C_c(α, β)
  body: ⟨0⟩

@[simp]

中文:
实例 [零
  签名: β] : 可居 C_c(α, β)
  定义体: ⟨0⟩

@[simp]
-/
instance [Zero β] : Inhabited C_c(α, β) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  given: [Zero β]
  statement: ⇑(0 : C_c(α, β)) = 0
  proof: rfl

中文:
定理 coe_zero
  条件: [零 β]
  结论: ⇑(0 : C_c(α, β)) = 0
  证明: rfl
-/
theorem coe_zero [Zero β] : ⇑(0 : C_c(α, β)) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [Zero β]
  statement: (0 : C_c(α, β)) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: [零 β]
  结论: (0 : C_c(α, β)) x = 0
  证明: rfl
-/
theorem zero_apply [Zero β] : (0 : C_c(α, β)) x = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: β] [ContinuousMul β] : Mul C_c(α, β)
  body: ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]

中文:
实例 [乘零类
  签名: β] [连续乘法 β] : 乘法 C_c(α, β)
  定义体: ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]

Depends on / 依赖: HasCompactSupport, HasCompactSupport.mul_left, mul_left
-/
instance [MulZeroClass β] [ContinuousMul β] : Mul C_c(α, β) :=
  ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β))
  statement: ⇑(f * g) = f * g
  proof: rfl

中文:
定理 coe_mul
  条件: [乘零类 β] [连续乘法 β] (f g : C_c(α, β))
  结论: ⇑(f * g) = f * g
  证明: rfl
-/
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = f * g :=
  rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β))
  statement: (f * g) x = f x * g x
  proof: rfl

中文:
定理 mul_apply
  条件: [乘零类 β] [连续乘法 β] (f g : C_c(α, β))
  结论: (f * g) x = f x * g x
  证明: rfl
-/
theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
  body: ⟨⟨fun x => f x • g x, (map_continuous f).smul (map_continuous g)⟩, g.hasCompactSupport.smul_left⟩

@[simp]

中文:
实例 [零
  签名: β] [拓扑空间 γ] [SMulZero类 γ β] [连续标量乘法 γ β]
  定义体: ⟨⟨fun x => f x • g x, (map_continuous f).smul (map_continuous g)⟩, g.hasCompactSupport.smul_left⟩

@[simp]

Depends on / 依赖: g.hasCompactSupport.smul_left, hasCompactSupport, map_continuous, smul_left
-/
instance [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] : SMul F C_c(α, β) where
  smul f g :=
    ⟨⟨fun x => f x • g x, (map_continuous f).smul (map_continuous g)⟩, g.hasCompactSupport.smul_left⟩

@[simp]
/--
theorem `coe_smulc` / 定理 `coe_smulc`

English:
theorem coe_smulc
  statement: [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
  proof: rfl

中文:
定理 coe_smulc
  结论: [零 β] [拓扑空间 γ] [SMulZero类 γ β] [连续标量乘法 γ β]
  证明: rfl
-/
theorem coe_smulc [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) :
    ⇑(f • g) = fun x => f x • g x :=
  rfl

/--
theorem `smulc_apply` / 定理 `smulc_apply`

English:
theorem smulc_apply
  statement: [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
  proof: rfl

中文:
定理 smulc_apply
  结论: [零 β] [拓扑空间 γ] [SMulZero类 γ β] [连续标量乘法 γ β]
  证明: rfl
-/
theorem smulc_apply [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) (x : α) :
    (f • g) x = f x • g x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: β] [ContinuousMul β] : MulZeroClass C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

中文:
实例 [乘零类
  签名: β] [连续乘法 β] : 乘零类 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

Depends on / 依赖: fast_instance
-/
instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: β] [ContinuousMul β] :
  body: fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

中文:
实例 [带零半群
  签名: β] [连续乘法 β] :
  定义体: fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

Depends on / 依赖: fast_instance
-/
instance [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: β] [ContinuousAdd β] : Add C_c(α, β)
  body: ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]

中文:
实例 [加法零类
  签名: β] [连续加法 β] : 加法 C_c(α, β)
  定义体: ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]

Depends on / 依赖: HasCompactSupport, HasCompactSupport.add
-/
instance [AddZeroClass β] [ContinuousAdd β] : Add C_c(α, β) :=
  ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β))
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
定理 coe_add
  条件: [加法零类 β] [连续加法 β] (f g : C_c(α, β))
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : ⇑(f + g) = f + g :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β))
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
定理 add_apply
  条件: [加法零类 β] [连续加法 β] (f g : C_c(α, β))
  结论: (f + g) x = f x + g x
  证明: rfl
-/
theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: β] [ContinuousAdd β] : AddZeroClass C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

中文:
实例 [加法零类
  签名: β] [连续加法 β] : 加法零类 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

Depends on / 依赖: fast_instance
-/
instance [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/--
Definition of `coeFnMonoidHom` / `coeFnMonoidHom` 的定义

English:
definition coeFnMonoidHom
  signature: [AddMonoid β] [ContinuousAdd β]
  body: f
  map_zero' := coe_zero
  map_add' := coe_add

中文:
定义 coeFnMonoidHom
  签名: [加法幺半群 β] [连续加法 β]
  定义体: f
  map_zero' := coe_zero
  map_add' := coe_add
-/
def coeFnMonoidHom [AddMonoid β] [ContinuousAdd β] : C_c(α, β) ->+ α -> β where
  toFun f := f
  map_zero' := coe_zero
  map_add' := coe_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] {R
  body: fast_instance%
  ⟨fun r f => ⟨⟨r • ⇑f, (map_continuous f).const_smul r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]

中文:
实例 [零
  签名: β] {R
  定义体: fast_instance%
  ⟨fun r f => ⟨⟨r • ⇑f, (map_continuous f).const_smul r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: fast_instance
-/
instance [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] :
    SMul R C_c(α, β) := fast_instance%
  ⟨fun r f => ⟨⟨r • ⇑f, (map_continuous f).const_smul r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
  proof: rfl

中文:
定理 coe_smul
  结论: [零 β] {R : 类型} [SMulZero类 R β] [连续常数标量乘法 R β] (r : R)
  证明: rfl
-/
theorem coe_smul [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
  proof: rfl

中文:
定理 smul_apply
  结论: [零 β] {R : 类型} [SMulZero类 R β] [连续常数标量乘法 R β] (r : R)
  证明: rfl
-/
theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: β] [ContinuousAdd β] : AddMonoid C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 [加法幺半群
  签名: β] [连续加法 β] : 加法幺半群 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [AddMonoid β] [ContinuousAdd β] : AddMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: β] [ContinuousAdd β] : AddCommMonoid C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

@[simp]

中文:
实例 [加法交换幺半群
  签名: β] [连续加法 β] : 加法交换幺半群 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

@[simp]

Depends on / 依赖: fast_instance
-/
instance [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

@[simp]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι -> C_c(α, β))
  proof: map_sum coeFnMonoidHom f s

中文:
定理 coe_sum
  条件: [加法交换幺半群 β] [连续加法 β] {ι : 类型} (s : 有限集 ι) (f : ι -> C_c(α, β))
  证明: map_sum coeFnMonoidHom f s

Depends on / 依赖: coeFnMonoidHom, map_sum
-/
theorem coe_sum [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι -> C_c(α, β)) :
    ⇑(∑ i in s, f i) = ∑ i in s, (f i : α -> β) :=
  map_sum coeFnMonoidHom f s

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  statement: [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι -> C_c(α, β))
  proof: by simp

中文:
定理 sum_apply
  结论: [加法交换幺半群 β] [连续加法 β] {ι : 类型} (s : 有限集 ι) (f : ι -> C_c(α, β))
  证明: by simp
-/
theorem sum_apply [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι -> C_c(α, β))
    (a : α) : (∑ i in s, f i) a = ∑ i in s, f i a := by simp

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C_c(α, β))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg C_c(α, β)
  body: { toFun := -f.1
             continuous_toFun := map_continuous (-f.1)
             hasCompactSupport' := by simpa [HasCompactSupport, tsupport] using f.2 }

@[simp]

中文:
实例 :
  签名: 取负 C_c(α, β)
  定义体: { toFun := -f.1
             continuous_toFun := map_continuous (-f.1)
             hasCompactSupport' := by simpa [HasCompactSupport, tsupport] using f.2 }

@[simp]
-/
instance : Neg C_c(α, β) where
  neg f := { toFun := -f.1
             continuous_toFun := map_continuous (-f.1)
             hasCompactSupport' := by simpa [HasCompactSupport, tsupport] using f.2 }

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ⇑(-f) = -f
  proof: rfl

中文:
定理 coe_neg
  结论: ⇑(-f) = -f
  证明: rfl
-/
theorem coe_neg : ⇑(-f) = -f :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-f) x = -f x
  proof: rfl

中文:
定理 neg_apply
  结论: (-f) x = -f x
  证明: rfl
-/
theorem neg_apply : (-f) x = -f x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub C_c(α, β)
  body: { toFun := f.1 - g.1
               continuous_toFun := map_continuous (f.1 - g.1)
               hasCompactSupport' := by
                 simpa [sub_eq_add_neg] using HasCompactSupport.add f.2 (-g).2 }

@[simp]

中文:
实例 :
  签名: 减法 C_c(α, β)
  定义体: { toFun := f.1 - g.1
               continuous_toFun := map_continuous (f.1 - g.1)
               hasCompactSupport' := by
                 simpa [sub_eq_add_neg] using HasCompactSupport.add f.2 (-g).2 }

@[simp]
-/
instance : Sub C_c(α, β) where
  sub f g := { toFun := f.1 - g.1
               continuous_toFun := map_continuous (f.1 - g.1)
               hasCompactSupport' := by
                 simpa [sub_eq_add_neg] using HasCompactSupport.add f.2 (-g).2 }

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
定理 coe_sub
  结论: ⇑(f - g) = f - g
  证明: rfl
-/
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  statement: (f - g) x = f x - g x
  proof: rfl

中文:
定理 sub_apply
  结论: (f - g) x = f x - g x
  证明: rfl
-/
theorem sub_apply : (f - g) x = f x - g x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法群 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : AddGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: β] [IsTopologicalAddGroup β] : AddCommGroup C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

中文:
实例 [加法交换群
  签名: β] [是拓扑加群 β] : 加法交换群 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

Depends on / 依赖: fast_instance
-/
instance [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] {R
  body: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

中文:
实例 [零
  签名: β] {R
  定义体: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: op_smul_eq_smul
-/
instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C_c(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] {R
  body: fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

中文:
实例 [零
  签名: β] {R
  定义体: fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C_c(α, β) := fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] {R
  body: fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

中文:
实例 [零
  签名: β] {R
  定义体: fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C_c(α, β) := fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: β] [ContinuousAdd β] {R
  body: fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

中文:
实例 [加法交换幺半群
  签名: β] [连续加法 β] {R
  定义体: fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C_c(α, β) := fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: β] [IsTopologicalSemiring β] :
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [非幺非结合半环
  签名: β] [是TopologicalSemiring β] :
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: β] [IsTopologicalSemiring β] :
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [非幺半环
  签名: β] [是TopologicalSemiring β] :
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: β] [IsTopologicalSemiring β] :
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [非幺交换半环
  签名: β] [是TopologicalSemiring β] :
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: β] [IsTopologicalRing β] :
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺非结合环
  签名: β] [是拓扑环 β] :
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: β] [IsTopologicalRing β] : NonUnitalRing C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 [非幺环
  签名: β] [是拓扑环 β] : 非幺环 C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: β] [IsTopologicalRing β] :
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺交换环
  签名: β] [是拓扑环 β] :
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C_c(α, β) C_c(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_assoc]

instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C_c(α, β) C_c(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_comm]

end AlgebraicStructure

section Star

/-! ### Star structure

It is possible to equip `C_c(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`StarAddMonoid` is close enough.

The `StarAddMonoid` class on `C_c(α, β)` is inherited from their counterparts on `α →ᵇ β`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star C_c(α, β)
  body: { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      hasCompactSupport' := by
        rw [HasCompactSupport]; rw [tsupport]
        have support_star : (Function.support fun (x : α) => star (f x)) = Function.support f := by
          ext x
          simp only [Function.mem_support, ne_eq, star_eq_zero]
        rw [support_star]
        exact f.2 }

@[simp]

中文:
实例 :
  签名: 对合 C_c(α, β)
  定义体: { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      hasCompactSupport' := by
        rw [HasCompactSupport]; rw [tsupport]
        have support_star : (Function.support fun (x : α) => star (f x)) = Function.support f := by
          ext x
          simp only [Function.mem_support, ne_eq, star_eq_zero]
        rw [support_star]
        exact f.2 }

@[simp]

Depends on / 依赖: Function, Function.mem_support, Function.support, HasCompactSupport, continuous_toFun, hasCompactSupport, map_continuous, mem_support, ne_eq, star_eq_zero, support, support_star, tsupport
-/
instance : Star C_c(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      hasCompactSupport' := by
        rw [HasCompactSupport]; rw [tsupport]
        have support_star : (Function.support fun (x : α) => star (f x)) = Function.support f := by
          ext x
          simp only [Function.mem_support, ne_eq, star_eq_zero]
        rw [support_star]
        exact f.2 }

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (f : C_c(α, β))
  statement: ⇑(star f) = star (⇑f)
  proof: rfl

中文:
定理 coe_star
  条件: (f : C_c(α, β))
  结论: ⇑(star f) = star (⇑f)
  证明: rfl
-/
theorem coe_star (f : C_c(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: (f : C_c(α, β)) (x : α)
  statement: (star f) x = star (f x)
  proof: rfl

中文:
定理 star_apply
  条件: (f : C_c(α, β)) (x : α)
  结论: (star f) x = star (f x)
  证明: rfl
-/
theorem star_apply (f : C_c(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TrivialStar
  signature: β] : TrivialStar C_c(α, β) where
  body: ext fun x => star_trivial (f x)

中文:
实例 [TrivialStar
  签名: β] : TrivialStar C_c(α, β) where
  定义体: ext fun x => star_trivial (f x)

Depends on / 依赖: star_trivial
-/
instance [TrivialStar β] : TrivialStar C_c(α, β) where
    star_trivial f := ext fun x => star_trivial (f x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousAdd
  signature: β] : StarAddMonoid C_c(α, β) where
  body: ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

中文:
实例 [连续加法
  签名: β] : StarAdd幺半群 C_c(α, β) where
  定义体: ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

Depends on / 依赖: star_star
-/
instance [ContinuousAdd β] : StarAddMonoid C_c(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule 𝕜 C_c(α, β)
  body: ext fun x => star_smul k (f x)

中文:
实例 :
  签名: 对合模 𝕜 C_c(α, β)
  定义体: ext fun x => star_smul k (f x)

Depends on / 依赖: star_smul
-/
instance : StarModule 𝕜 C_c(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [IsTopologicalSemiring β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing C_c(α, β)
  body: { CompactlySupportedContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

中文:
实例 :
  签名: 对合环 C_c(α, β)
  定义体: { CompactlySupportedContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

Depends on / 依赖: CompactlySupportedContinuousMap, CompactlySupportedContinuousMap.instStarAddMonoid, instStarAddMonoid, star_mul
-/
instance : StarRing C_c(α, β) :=
  { CompactlySupportedContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section PartialOrder

/-! ### The partial order in `C_c`
When `β` is equipped with a partial order, `C_c(α, β)` is given the pointwise partial order.
-/

variable {β : Type*} [TopologicalSpace β] [Zero β] [PartialOrder β]

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder C_c(α, β)
  body: fast_instance% PartialOrder.lift (⇑) DFunLike.coe_injective

中文:
实例 partialOrder
  签名: : 偏序 C_c(α, β)
  定义体: fast_instance% PartialOrder.lift (⇑) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective, fast_instance
-/
instance partialOrder : PartialOrder C_c(α, β) :=
  fast_instance% PartialOrder.lift (⇑) DFunLike.coe_injective

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {f g : C_c(α, β)}
  statement: f <= g ↔ forall a, f a <= g a
  proof: Pi.le_def

中文:
定理 le_def
  条件: {f g : C_c(α, β)}
  结论: f <= g ↔ 对任意 a, f a <= g a
  证明: Pi.le_def

Depends on / 依赖: Pi.le_def, le_def
-/
theorem le_def {f g : C_c(α, β)} : f <= g ↔ forall a, f a <= g a := Pi.le_def

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {f g : C_c(α, β)}
  statement: f < g ↔ (forall a, f a <= g a) ∧ exists a, f a < g a
  proof: Pi.lt_def

中文:
定理 lt_def
  条件: {f g : C_c(α, β)}
  结论: f < g ↔ (对任意 a, f a <= g a) ∧ 存在 a, f a < g a
  证明: Pi.lt_def

Depends on / 依赖: Pi.lt_def, lt_def
-/
theorem lt_def {f g : C_c(α, β)} : f < g ↔ (forall a, f a <= g a) ∧ exists a, f a < g a := Pi.lt_def

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup β] [Zero β] [TopologicalSpace β] [ContinuousSup β]

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max C_c(α, β) where max f g
  body: { toFun := f ⊔ g
    continuous_toFun := Continuous.sup f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.sup g.hasCompactSupport }

中文:
实例 instSup
  签名: : 最大值 C_c(α, β) where 最大值 f g
  定义体: { toFun := f ⊔ g
    continuous_toFun := Continuous.sup f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.sup g.hasCompactSupport }

Depends on / 依赖: Continuous, Continuous.sup, continuous, continuous_toFun, f.continuous, f.hasCompactSupport.sup, g.continuous, g.hasCompactSupport, hasCompactSupport
-/
instance instSup : Max C_c(α, β) where max f g :=
  { toFun := f ⊔ g
    continuous_toFun := Continuous.sup f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.sup g.hasCompactSupport }

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (f g : C_c(α, β))
  statement: ⇑(f ⊔ g) = ⇑f ⊔ g
  proof: rfl

中文:
引理 coe_sup
  条件: (f g : C_c(α, β))
  结论: ⇑(f ⊔ g) = ⇑f ⊔ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (f g : C_c(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl

/--
lemma `sup_apply` / 引理 `sup_apply`

English:
lemma sup_apply
  given: (f g : C_c(α, β)) (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

中文:
引理 sup_apply
  条件: (f g : C_c(α, β)) (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl
-/
@[simp] lemma sup_apply (f g : C_c(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: : SemilatticeSup C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 semilatticeSup
  签名: : SemilatticeSup C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: fast_instance
-/
instance semilatticeSup : SemilatticeSup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/--
lemma `finsetSup'_apply` / 引理 `finsetSup'_apply`

English:
lemma finsetSup'_apply
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) (a : α)
  proof: Finset.apply_sup'_eq_sup'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

中文:
引理 finsetSup'_apply
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C_c(α, β)) (a : α)
  证明: Finset.apply_sup'_eq_sup'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.apply_sup, _comp, _eq_sup, apply_sup
-/
lemma finsetSup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i => f i a :=
  Finset.apply_sup'_eq_sup'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]
/--
lemma `coe_finsetSup'` / 引理 `coe_finsetSup'`

English:
lemma coe_finsetSup'
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β))
  proof: by ext; simp [finsetSup'_apply]

中文:
引理 coe_finsetSup'
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C_c(α, β))
  证明: by ext; simp [finsetSup'_apply]

Depends on / 依赖: _apply, finsetSup
-/
lemma coe_finsetSup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i => ⇑(f i) := by ext; simp [finsetSup'_apply]

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [Zero β] [TopologicalSpace β] [ContinuousInf β]

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min C_c(α, β) where min f g
  body: { toFun := f ⊓ g
    continuous_toFun := Continuous.inf f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.inf g.hasCompactSupport }

中文:
实例 instInf
  签名: : 最小值 C_c(α, β) where 最小值 f g
  定义体: { toFun := f ⊓ g
    continuous_toFun := Continuous.inf f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.inf g.hasCompactSupport }

Depends on / 依赖: Continuous, Continuous.inf, continuous, continuous_toFun, f.continuous, f.hasCompactSupport.inf, g.continuous, g.hasCompactSupport, hasCompactSupport
-/
instance instInf : Min C_c(α, β) where min f g :=
  { toFun := f ⊓ g
    continuous_toFun := Continuous.inf f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.inf g.hasCompactSupport }

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (f g : C_c(α, β))
  statement: ⇑(f ⊓ g) = ⇑f ⊓ g
  proof: rfl

中文:
引理 coe_inf
  条件: (f g : C_c(α, β))
  结论: ⇑(f ⊓ g) = ⇑f ⊓ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (f g : C_c(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl

/--
lemma `inf_apply` / 引理 `inf_apply`

English:
lemma inf_apply
  given: (f g : C_c(α, β)) (a : α)
  statement: (f ⊓ g) a = f a ⊓ g a
  proof: rfl

中文:
引理 inf_apply
  条件: (f g : C_c(α, β)) (a : α)
  结论: (f ⊓ g) a = f a ⊓ g a
  证明: rfl
-/
@[simp] lemma inf_apply (f g : C_c(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: : SemilatticeInf C_c(α, β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

中文:
实例 semilatticeInf
  签名: : SemilatticeInf C_c(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

Depends on / 依赖: fast_instance
-/
instance semilatticeInf : SemilatticeInf C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

/--
lemma `finsetInf'_apply` / 引理 `finsetInf'_apply`

English:
lemma finsetInf'_apply
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) (a : α)
  proof: Finset.apply_inf'_eq_inf'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

中文:
引理 finsetInf'_apply
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C_c(α, β)) (a : α)
  证明: Finset.apply_inf'_eq_inf'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.apply_inf, _comp, _eq_inf, apply_inf
-/
lemma finsetInf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i => f i a :=
  Finset.apply_inf'_eq_inf'_comp H (fun g : C_c(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]
/--
lemma `coe_finsetInf'` / 引理 `coe_finsetInf'`

English:
lemma coe_finsetInf'
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β))
  proof: by ext; simp [finsetInf'_apply]

中文:
引理 coe_finsetInf'
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C_c(α, β))
  证明: by ext; simp [finsetInf'_apply]

Depends on / 依赖: _apply, finsetInf
-/
lemma coe_finsetInf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i => ⇑(f i) := by ext; simp [finsetInf'_apply]

end SemilatticeInf

section Lattice

variable [TopologicalSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: β] [TopologicalLattice β] [Zero β] : Lattice C_c(α, β) where

中文:
实例 [格
  签名: β] [拓扑格 β] [零 β] : 格 C_c(α, β) where
-/
instance [Lattice β] [TopologicalLattice β] [Zero β] : Lattice C_c(α, β) where

/--
Instance `instMulLeftMono` / 实例 `instMulLeftMono`

English:
instance instMulLeftMono
  signature: [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulLeftMono β]
  body: ⟨fun _ _ _ hg₁₂ x => mul_le_mul_right (hg₁₂ x) _⟩

中文:
实例 instMulLeftMono
  签名: [偏序 β] [乘零类 β] [连续乘法 β] [MulLeftMono β]
  定义体: ⟨fun _ _ _ hg₁₂ x => mul_le_mul_right (hg₁₂ x) _⟩

Depends on / 依赖: mul_le_mul_right
-/
instance instMulLeftMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulLeftMono β] :
    MulLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_right (hg₁₂ x) _⟩

/--
Instance `instMulRightMono` / 实例 `instMulRightMono`

English:
instance instMulRightMono
  signature: [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulRightMono β]
  body: ⟨fun _ _ _ hg₁₂ x => mul_le_mul_left (hg₁₂ x) _⟩

中文:
实例 instMulRightMono
  签名: [偏序 β] [乘零类 β] [连续乘法 β] [MulRightMono β]
  定义体: ⟨fun _ _ _ hg₁₂ x => mul_le_mul_left (hg₁₂ x) _⟩

Depends on / 依赖: mul_le_mul_left
-/
instance instMulRightMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulRightMono β] :
    MulRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_left (hg₁₂ x) _⟩

/--
Instance `instAddLeftMono` / 实例 `instAddLeftMono`

English:
instance instAddLeftMono
  signature: [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddLeftMono β]
  body: ⟨fun _ _ _ hg₁₂ x => add_le_add_right (hg₁₂ x) _⟩

中文:
实例 instAddLeftMono
  签名: [偏序 β] [加法零类 β] [连续加法 β] [AddLeftMono β]
  定义体: ⟨fun _ _ _ hg₁₂ x => add_le_add_right (hg₁₂ x) _⟩

Depends on / 依赖: add_le_add_right
-/
instance instAddLeftMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddLeftMono β] :
    AddLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_right (hg₁₂ x) _⟩

/--
Instance `instAddRightMono` / 实例 `instAddRightMono`

English:
instance instAddRightMono
  signature: [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddRightMono β]
  body: ⟨fun _ _ _ hg₁₂ x => add_le_add_left (hg₁₂ x) _⟩

中文:
实例 instAddRightMono
  签名: [偏序 β] [加法零类 β] [连续加法 β] [AddRightMono β]
  定义体: ⟨fun _ _ _ hg₁₂ x => add_le_add_left (hg₁₂ x) _⟩

Depends on / 依赖: add_le_add_left
-/
instance instAddRightMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddRightMono β] :
    AddRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_left (hg₁₂ x) _⟩

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

end Lattice

section IsOrderedAddMonoid

variable [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
variable [PartialOrder β] [IsOrderedAddMonoid β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid C_c(α, β)
  body: add_le_add_left hfg c

中文:
实例 :
  签名: 是OrderedAdd幺半群 C_c(α, β)
  定义体: add_le_add_left hfg c

Depends on / 依赖: add_le_add_left
-/
instance : IsOrderedAddMonoid C_c(α, β) where
  add_le_add_left _ _ hfg c := add_le_add_left hfg c

end IsOrderedAddMonoid

/-! ### `C_c` as a functor

For each `β` with sufficient structure, there is a contravariant functor `C_c(-, β)` from the
category of topological spaces with morphisms given by `CocompactMap`s.
-/


variable {δ : Type*} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " ->co " β => CocompactMap α β

section

variable [Zero δ]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : C_c(γ, δ)) (g : β ->co γ)
  body: (f : C(γ, δ)).comp g
  hasCompactSupport' := by
    apply IsCompact.of_isClosed_subset (g.isCompact_preimage_of_isClosed f.2 (isClosed_tsupport _))
      (isClosed_tsupport (f ∘ g))
    intro x hx
    rw [tsupport]; rw [Set.mem_preimage]; rw [_root_.mem_closure_iff]
    intro o ho hgxo
    rw [tsupport]; rw [_root_.mem_closure_iff] at hx
    obtain ⟨y, hy⟩ := hx (g ⁻¹' o) (IsOpen.preimage g.1.2 ho) hgxo
    exact ⟨g y, hy⟩

@[simp]

中文:
定义 comp
  签名: (f : C_c(γ, δ)) (g : β ->co γ)
  定义体: (f : C(γ, δ)).comp g
  hasCompactSupport' := by
    apply IsCompact.of_isClosed_subset (g.isCompact_preimage_of_isClosed f.2 (isClosed_tsupport _))
      (isClosed_tsupport (f ∘ g))
    intro x hx
    rw [tsupport]; rw [Set.mem_preimage]; rw [_root_.mem_closure_iff]
    intro o ho hgxo
    rw [tsupport]; rw [_root_.mem_closure_iff] at hx
    obtain ⟨y, hy⟩ := hx (g ⁻¹' o) (IsOpen.preimage g.1.2 ho) hgxo
    exact ⟨g y, hy⟩

@[simp]
-/
def comp (f : C_c(γ, δ)) (g : β ->co γ) : C_c(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  hasCompactSupport' := by
    apply IsCompact.of_isClosed_subset (g.isCompact_preimage_of_isClosed f.2 (isClosed_tsupport _))
      (isClosed_tsupport (f ∘ g))
    intro x hx
    rw [tsupport]; rw [Set.mem_preimage]; rw [_root_.mem_closure_iff]
    intro o ho hgxo
    rw [tsupport]; rw [_root_.mem_closure_iff] at hx
    obtain ⟨y, hy⟩ := hx (g ⁻¹' o) (IsOpen.preimage g.1.2 ho) hgxo
    exact ⟨g y, hy⟩

@[simp]
/--
theorem `coe_comp_to_continuous_fun` / 定理 `coe_comp_to_continuous_fun`

English:
theorem coe_comp_to_continuous_fun
  given: (f : C_c(γ, δ)) (g : β ->co γ)
  statement: ((f.comp g) : β -> δ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp_to_continuous_fun
  条件: (f : C_c(γ, δ)) (g : β ->co γ)
  结论: ((f.comp g) : β -> δ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp_to_continuous_fun (f : C_c(γ, δ)) (g : β ->co γ) : ((f.comp g) : β -> δ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : C_c(γ, δ))
  statement: f.comp (CocompactMap.id γ) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : C_c(γ, δ))
  结论: f.comp (余compact映射.id γ) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : C_c(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C_c(γ, δ)) (g : β ->co γ) (h : α ->co β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C_c(γ, δ)) (g : β ->co γ) (h : α ->co β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C_c(γ, δ)) (g : β ->co γ) (h : α ->co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (g : β ->co γ)
  statement: (0 : C_c(γ, δ)).comp g = 0
  proof: rfl

中文:
定理 zero_comp
  条件: (g : β ->co γ)
  结论: (0 : C_c(γ, δ)).comp g = 0
  证明: rfl
-/
theorem zero_comp (g : β ->co γ) : (0 : C_c(γ, δ)).comp g = 0 :=
  rfl

end

/--
Definition of `compAddMonoidHom` / `compAddMonoidHom` 的定义

English:
definition compAddMonoidHom
  signature: [AddMonoid δ] [ContinuousAdd δ] (g : β ->co γ)
  body: f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

中文:
定义 compAddMonoidHom
  签名: [加法幺半群 δ] [连续加法 δ] (g : β ->co γ)
  定义体: f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

Depends on / 依赖: f.comp
-/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β ->co γ) : C_c(γ, δ) ->+ C_c(β, δ) where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

/--
Definition of `compMulHom` / `compMulHom` 的定义

English:
definition compMulHom
  signature: [MulZeroClass δ] [ContinuousMul δ] (g : β ->co γ)
  body: f.comp g
  map_mul' _ _ := rfl

中文:
定义 compMulHom
  签名: [乘零类 δ] [连续乘法 δ] (g : β ->co γ)
  定义体: f.comp g
  map_mul' _ _ := rfl

Depends on / 依赖: f.comp
-/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β ->co γ) : C_c(γ, δ) ->ₙ* C_c(β, δ) where
  toFun f := f.comp g
  map_mul' _ _ := rfl

/--
Definition of `compLinearMap` / `compLinearMap` 的定义

English:
definition compLinearMap
  signature: [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
  body: f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 compLinearMap
  签名: [加法交换幺半群 δ] [连续加法 δ] {R : 类型} [半环 R] [模 R δ]
  定义体: f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: f.comp
-/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β ->co γ) : C_c(γ, δ) ->ₗ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `compNonUnitalAlgHom` / `compNonUnitalAlgHom` 的定义

English:
definition compNonUnitalAlgHom
  signature: {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
  body: f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 compNonUnitalAlgHom
  签名: {R : 类型} [半环 R] [非幺非结合半环 δ]
  定义体: f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: f.comp
-/
def compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β ->co γ) :
    C_c(γ, δ) ->ₙₐ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end CompactlySupportedContinuousMap

namespace CompactlySupportedContinuousMapClass

section Basic

variable [Zero β] [TopologicalSpace β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (CompactlySupportedContinuousMap α β)
  body: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      hasCompactSupport' := hasCompactSupport f }⟩

中文:
实例 :
  签名: CoeTC F (余mpactlySupportedContinuous映射 α β)
  定义体: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      hasCompactSupport' := hasCompactSupport f }⟩

Depends on / 依赖: continuous_toFun, hasCompactSupport, map_continuous
-/
instance : CoeTC F (CompactlySupportedContinuousMap α β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      hasCompactSupport' := hasCompactSupport f }⟩

/--
lemma `of_compactSpace` / 引理 `of_compactSpace`

English:
lemma of_compactSpace
  statement: (G : Type*) [FunLike G α β]
  proof: map_continuous
  hasCompactSupport := by
    intro f
    exact HasCompactSupport.of_compactSpace f

中文:
引理 of_compactSpace
  结论: (G : 类型) [函数状 G α β]
  证明: map_continuous
  hasCompactSupport := by
    intro f
    exact HasCompactSupport.of_compactSpace f

Depends on / 依赖: map_continuous
-/
lemma of_compactSpace (G : Type*) [FunLike G α β]
    [ContinuousMapClass G α β] [CompactSpace α] : CompactlySupportedContinuousMapClass G α β where
  map_continuous := map_continuous
  hasCompactSupport := by
    intro f
    exact HasCompactSupport.of_compactSpace f

end Basic

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ] [FunLike F β γ]
  [CompactlySupportedContinuousMapClass F β γ]

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (f : F)
  statement: UniformContinuous (f : β -> γ)
  proof: (map_continuous f).uniformContinuous_of_tendsto_cocompact
  (HasCompactSupport.is_zero_at_infty (hasCompactSupport f))

中文:
定理 uniformContinuous
  条件: (f : F)
  结论: 一致连续 (f : β -> γ)
  证明: (map_continuous f).uniformContinuous_of_tendsto_cocompact
  (HasCompactSupport.is_zero_at_infty (hasCompactSupport f))

Depends on / 依赖: HasCompactSupport, HasCompactSupport.is_zero_at_infty, hasCompactSupport, is_zero_at_infty, map_continuous, uniformContinuous_of_tendsto_cocompact
-/
theorem uniformContinuous (f : F) : UniformContinuous (f : β -> γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact
  (HasCompactSupport.is_zero_at_infty (hasCompactSupport f))

end Uniform

section ZeroAtInfty

variable [TopologicalSpace β] [TopologicalSpace γ] [Zero γ]
  [FunLike F β γ] [CompactlySupportedContinuousMapClass F β γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ZeroAtInftyContinuousMapClass F β γ
  body: HasCompactSupport.is_zero_at_infty (hasCompactSupport f)

中文:
实例 :
  签名: ZeroAtInftyContinuous映射类 F β γ
  定义体: HasCompactSupport.is_zero_at_infty (hasCompactSupport f)

Depends on / 依赖: HasCompactSupport, HasCompactSupport.is_zero_at_infty, hasCompactSupport, is_zero_at_infty
-/
instance : ZeroAtInftyContinuousMapClass F β γ where
  zero_at_infty f := HasCompactSupport.is_zero_at_infty (hasCompactSupport f)

end ZeroAtInfty

end CompactlySupportedContinuousMapClass

section NonnegativePart

open NNReal

namespace CompactlySupportedContinuousMap

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_add_of_le` / 引理 `exists_add_of_le`

English:
lemma exists_add_of_le
  given: {f₁ f₂ : C_c(α, Real>=0)} (h : f₁ <= f₂)
  statement: exists (g : C_c(α, Real>=0)),
  proof: by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport]; rw [tsupport]; rw [← closure_union]
    apply closure_mono
    intro x hx
    contrapose hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)

中文:
引理 存在_add_of_le
  条件: {f₁ f₂ : C_c(α, 实数>=0)} (h : f₁ <= f₂)
  结论: 存在 (g : C_c(α, 实数>=0)),
  证明: by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport]; rw [tsupport]; rw [← closure_union]
    apply closure_mono
    intro x hx
    contrapose hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)
-/
protected lemma exists_add_of_le {f₁ f₂ : C_c(α, Real>=0)} (h : f₁ <= f₂) : exists (g : C_c(α, Real>=0)),
    f₁ + g = f₂ := by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport]; rw [tsupport]; rw [← closure_union]
    apply closure_mono
    intro x hx
    contrapose hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)

/--
Definition of `nnrealPart` / `nnrealPart` 的定义

English:
definition nnrealPart
  signature: (f : C_c(α, Real))
  body: Real.toNNReal.comp f.toFun
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' Real.toNNReal_zero

@[simp]

中文:
定义 nnrealPart
  签名: (f : C_c(α, 实数))
  定义体: Real.toNNReal.comp f.toFun
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' Real.toNNReal_zero

@[simp]

Depends on / 依赖: Real.toNNReal.comp, f.toFun, toNNReal
-/
noncomputable def nnrealPart (f : C_c(α, Real)) : C_c(α, Real>=0) where
  toFun := Real.toNNReal.comp f.toFun
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' Real.toNNReal_zero

@[simp]
/--
lemma `nnrealPart_apply` / 引理 `nnrealPart_apply`

English:
lemma nnrealPart_apply
  given: (f : C_c(α, Real)) (x : α)
  proof: rfl

中文:
引理 nnrealPart_apply
  条件: (f : C_c(α, 实数)) (x : α)
  证明: rfl
-/
lemma nnrealPart_apply (f : C_c(α, Real)) (x : α) :
    f.nnrealPart x = Real.toNNReal (f x) := rfl

/--
lemma `nnrealPart_neg_eq_zero_of_nonneg` / 引理 `nnrealPart_neg_eq_zero_of_nonneg`

English:
lemma nnrealPart_neg_eq_zero_of_nonneg
  given: {f : C_c(α, Real)} (hf : 0 <= f)
  statement: (-f).nnrealPart = 0
  proof: by
  ext x
  simpa using hf x

中文:
引理 nnrealPart_neg_eq_zero_of_nonneg
  条件: {f : C_c(α, 实数)} (hf : 0 <= f)
  结论: (-f).nnrealPart = 0
  证明: by
  ext x
  simpa using hf x
-/
lemma nnrealPart_neg_eq_zero_of_nonneg {f : C_c(α, Real)} (hf : 0 <= f) : (-f).nnrealPart = 0 := by
  ext x
  simpa using hf x

/--
lemma `nnrealPart_smul_pos` / 引理 `nnrealPart_smul_pos`

English:
lemma nnrealPart_smul_pos
  given: (f : C_c(α, Real)) {a : Real} (ha : 0 <= a)
  proof: by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, Real.coe_toNNReal', smul_eq_mul,
    NNReal.coe_mul, ha, sup_of_le_left]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [ha, hfx, mul_nonneg]
  · simp [mul_nonpos_iff, ha, hfx]

中文:
引理 nnrealPart_smul_pos
  条件: (f : C_c(α, 实数)) {a : 实数} (ha : 0 <= a)
  证明: by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, Real.coe_toNNReal', smul_eq_mul,
    NNReal.coe_mul, ha, sup_of_le_left]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [ha, hfx, mul_nonneg]
  · simp [mul_nonpos_iff, ha, hfx]

Depends on / 依赖: NNReal, NNReal.coe_mul, Pi.smul_apply, Real.coe_toNNReal, coe_mul, coe_smul, coe_toNNReal, le_total, mul_nonneg, mul_nonpos_iff, nnrealPart_apply, smul_apply, smul_eq_mul, sup_of_le_left
-/
lemma nnrealPart_smul_pos (f : C_c(α, Real)) {a : Real} (ha : 0 <= a) :
    (a • f).nnrealPart = a.toNNReal • f.nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, Real.coe_toNNReal', smul_eq_mul,
    NNReal.coe_mul, ha, sup_of_le_left]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [ha, hfx, mul_nonneg]
  · simp [mul_nonpos_iff, ha, hfx]

/--
lemma `nnrealPart_smul_neg` / 引理 `nnrealPart_smul_neg`

English:
lemma nnrealPart_smul_neg
  given: (f : C_c(α, Real)) {a : Real} (ha : a <= 0)
  proof: by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal', coe_neg,
    Pi.neg_apply, NNReal.coe_mul]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [mul_nonpos_iff, ha, hfx]
  · simp [ha, hfx, mul_nonneg_of_nonpos_of_nonpos]

中文:
引理 nnrealPart_smul_neg
  条件: (f : C_c(α, 实数)) {a : 实数} (ha : a <= 0)
  证明: by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal', coe_neg,
    Pi.neg_apply, NNReal.coe_mul]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [mul_nonpos_iff, ha, hfx]
  · simp [ha, hfx, mul_nonneg_of_nonpos_of_nonpos]

Depends on / 依赖: NNReal, NNReal.coe_mul, Pi.neg_apply, Pi.smul_apply, Real.coe_toNNReal, coe_mul, coe_neg, coe_smul, coe_toNNReal, le_total, mul_nonneg_of_nonpos_of_nonpos, mul_nonpos_iff, neg_apply, nnrealPart_apply, smul_apply, smul_eq_mul
-/
lemma nnrealPart_smul_neg (f : C_c(α, Real)) {a : Real} (ha : a <= 0) :
    (a • f).nnrealPart = (-a).toNNReal • (-f).nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal', coe_neg,
    Pi.neg_apply, NNReal.coe_mul]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [mul_nonpos_iff, ha, hfx]
  · simp [ha, hfx, mul_nonneg_of_nonpos_of_nonpos]

/--
lemma `nnrealPart_add_le_add_nnrealPart` / 引理 `nnrealPart_add_le_add_nnrealPart`

English:
lemma nnrealPart_add_le_add_nnrealPart
  given: (f g : C_c(α, Real))
  proof: by
  intro x
  simpa using Real.toNNReal_add_le

中文:
引理 nnrealPart_add_le_add_nnrealPart
  条件: (f g : C_c(α, 实数))
  证明: by
  intro x
  simpa using Real.toNNReal_add_le

Depends on / 依赖: Real.toNNReal_add_le, toNNReal_add_le
-/
lemma nnrealPart_add_le_add_nnrealPart (f g : C_c(α, Real)) :
    (f + g).nnrealPart <= f.nnrealPart + g.nnrealPart := by
  intro x
  simpa using Real.toNNReal_add_le

/--
lemma `exists_add_nnrealPart_add_eq` / 引理 `exists_add_nnrealPart_add_eq`

English:
lemma exists_add_nnrealPart_add_eq
  given: (f g : C_c(α, Real))
  statement: exists (h : C_c(α, Real>=0)),
  proof: by
  obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le
    (nnrealPart_add_le_add_nnrealPart f g)
  use h
  refine ⟨hh, ?_⟩
  ext x
  have hhx := congr(($hh x : Real))
  simp only [coe_add, Pi.add_apply, nnrealPart_apply, coe_neg, Pi.neg_apply, NNReal.coe_add,
    Real.coe_toNNReal', ← neg_add, max_neg_zero] at hhx ⊢
  linear_combination hhx

中文:
引理 存在_add_nnrealPart_add_eq
  条件: (f g : C_c(α, 实数))
  结论: 存在 (h : C_c(α, 实数>=0)),
  证明: by
  obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le
    (nnrealPart_add_le_add_nnrealPart f g)
  use h
  refine ⟨hh, ?_⟩
  ext x
  have hhx := congr(($hh x : Real))
  simp only [coe_add, Pi.add_apply, nnrealPart_apply, coe_neg, Pi.neg_apply, NNReal.coe_add,
    Real.coe_toNNReal', ← neg_add, max_neg_zero] at hhx ⊢
  linear_combination hhx

Depends on / 依赖: CompactlySupportedContinuousMap, CompactlySupportedContinuousMap.exists_add_of_le, NNReal, NNReal.coe_add, Pi.add_apply, Pi.neg_apply, Real.coe_toNNReal, add_apply, coe_add, coe_neg, coe_toNNReal, exists_add_of_le, linear_combination, max_neg_zero, neg_add, neg_apply, nnrealPart_add_le_add_nnrealPart, nnrealPart_apply
-/
lemma exists_add_nnrealPart_add_eq (f g : C_c(α, Real)) : exists (h : C_c(α, Real>=0)),
    (f + g).nnrealPart + h = f.nnrealPart + g.nnrealPart ∧
    (-f + -g).nnrealPart + h = (-f).nnrealPart + (-g).nnrealPart := by
  obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le
    (nnrealPart_add_le_add_nnrealPart f g)
  use h
  refine ⟨hh, ?_⟩
  ext x
  have hhx := congr(($hh x : Real))
  simp only [coe_add, Pi.add_apply, nnrealPart_apply, coe_neg, Pi.neg_apply, NNReal.coe_add,
    Real.coe_toNNReal', ← neg_add, max_neg_zero] at hhx ⊢
  linear_combination hhx

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: (f : C_c(α, Real>=0))
  body: f.compLeft ContinuousMap.coeNNRealReal

中文:
定义 to实数
  签名: (f : C_c(α, 实数>=0))
  定义体: f.compLeft ContinuousMap.coeNNRealReal

Depends on / 依赖: ContinuousMap, ContinuousMap.coeNNRealReal, coeNNRealReal, compLeft, f.compLeft
-/
noncomputable def toReal (f : C_c(α, Real>=0)) : C_c(α, Real) :=
  f.compLeft ContinuousMap.coeNNRealReal

/--
lemma `toReal_apply` / 引理 `toReal_apply`

English:
lemma toReal_apply
  given: (f : C_c(α, Real>=0)) (x : α)
  statement: f.toReal x = f x
  proof: compLeft_apply rfl _ _

中文:
引理 to实数_apply
  条件: (f : C_c(α, 实数>=0)) (x : α)
  结论: f.to实数 x = f x
  证明: compLeft_apply rfl _ _
-/
@[simp] lemma toReal_apply (f : C_c(α, Real>=0)) (x : α) : f.toReal x = f x := compLeft_apply rfl _ _
/--
lemma `toReal_nonneg` / 引理 `toReal_nonneg`

English:
lemma toReal_nonneg
  given: {f : C_c(α, Real>=0)}
  statement: 0 <= f.toReal
  proof: fun _ => by simp

中文:
引理 to实数_nonneg
  条件: {f : C_c(α, 实数>=0)}
  结论: 0 <= f.to实数
  证明: fun _ => by simp
-/
@[simp] lemma toReal_nonneg {f : C_c(α, Real>=0)} : 0 <= f.toReal := fun _ => by simp
/--
lemma `toReal_add` / 引理 `toReal_add`

English:
lemma toReal_add
  given: (f g : C_c(α, Real>=0))
  statement: (f + g).toReal = f.toReal + g.toReal
  proof: by ext; simp

中文:
引理 to实数_add
  条件: (f g : C_c(α, 实数>=0))
  结论: (f + g).to实数 = f.to实数 + g.to实数
  证明: by ext; simp
-/
@[simp] lemma toReal_add (f g : C_c(α, Real>=0)) : (f + g).toReal = f.toReal + g.toReal := by ext; simp
/--
lemma `toReal_smul` / 引理 `toReal_smul`

English:
lemma toReal_smul
  given: (r : Real>=0) (f : C_c(α, Real>=0))
  statement: (r • f).toReal = r • f.toReal
  proof: by
  ext; simp [NNReal.smul_def]

@[simp]

中文:
引理 to实数_smul
  条件: (r : 实数>=0) (f : C_c(α, 实数>=0))
  结论: (r • f).to实数 = r • f.to实数
  证明: by
  ext; simp [NNReal.smul_def]

@[simp]
-/
@[simp] lemma toReal_smul (r : Real>=0) (f : C_c(α, Real>=0)) : (r • f).toReal = r • f.toReal := by
  ext; simp [NNReal.smul_def]

@[simp]
/--
lemma `nnrealPart_sub_nnrealPart_neg` / 引理 `nnrealPart_sub_nnrealPart_neg`

English:
lemma nnrealPart_sub_nnrealPart_neg
  given: (f : C_c(α, Real))
  proof: by ext x; simp

中文:
引理 nnrealPart_sub_nnrealPart_neg
  条件: (f : C_c(α, 实数))
  证明: by ext x; simp
-/
lemma nnrealPart_sub_nnrealPart_neg (f : C_c(α, Real)) :
    (nnrealPart f).toReal - (nnrealPart (-f)).toReal = f := by ext x; simp

/--
Definition of `toRealLinearMap` / `toRealLinearMap` 的定义

English:
definition toRealLinearMap
  signature: : C_c(α, Real>=0) ->ₗ[Real>=0] C_c(α, Real) where
  body: toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp, norm_cast]

中文:
定义 to实数LinearMap
  签名: : C_c(α, 实数>=0) ->ₗ[实数>=0] C_c(α, 实数) where
  定义体: toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp, norm_cast]

Depends on / 依赖: toReal
-/
noncomputable def toRealLinearMap : C_c(α, Real>=0) ->ₗ[Real>=0] C_c(α, Real) where
  toFun := toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp, norm_cast]
/--
lemma `coe_toRealLinearMap` / 引理 `coe_toRealLinearMap`

English:
lemma coe_toRealLinearMap
  statement: (toRealLinearMap : C_c(α, Real>=0) -> C_c(α, Real)) = toReal
  proof: rfl

中文:
引理 coe_to实数LinearMap
  结论: (to实数LinearMap : C_c(α, 实数>=0) -> C_c(α, 实数)) = to实数
  证明: rfl
-/
lemma coe_toRealLinearMap : (toRealLinearMap : C_c(α, Real>=0) -> C_c(α, Real)) = toReal := rfl

/--
lemma `toRealLinearMap_apply` / 引理 `toRealLinearMap_apply`

English:
lemma toRealLinearMap_apply
  given: (f : C_c(α, Real>=0))
  statement: toRealLinearMap f = f.toReal
  proof: rfl

中文:
引理 to实数LinearMap_apply
  条件: (f : C_c(α, 实数>=0))
  结论: to实数LinearMap f = f.to实数
  证明: rfl
-/
lemma toRealLinearMap_apply (f : C_c(α, Real>=0)) : toRealLinearMap f = f.toReal := rfl

/--
lemma `toRealLinearMap_apply_apply` / 引理 `toRealLinearMap_apply_apply`

English:
lemma toRealLinearMap_apply_apply
  given: (f : C_c(α, Real>=0)) (x : α)
  proof: by simp

@[simp]

中文:
引理 to实数LinearMap_apply_apply
  条件: (f : C_c(α, 实数>=0)) (x : α)
  证明: by simp

@[simp]
-/
lemma toRealLinearMap_apply_apply (f : C_c(α, Real>=0)) (x : α) :
    toRealLinearMap f x = (f x).toReal := by simp

@[simp]
/--
lemma `nnrealPart_toReal_eq` / 引理 `nnrealPart_toReal_eq`

English:
lemma nnrealPart_toReal_eq
  given: (f : C_c(α, Real>=0))
  statement: nnrealPart (toReal f) = f
  proof: by ext x; simp

@[simp]

中文:
引理 nnrealPart_to实数_eq
  条件: (f : C_c(α, 实数>=0))
  结论: nnrealPart (to实数 f) = f
  证明: by ext x; simp

@[simp]
-/
lemma nnrealPart_toReal_eq (f : C_c(α, Real>=0)) : nnrealPart (toReal f) = f := by ext x; simp

@[simp]
/--
lemma `nnrealPart_neg_toReal_eq` / 引理 `nnrealPart_neg_toReal_eq`

English:
lemma nnrealPart_neg_toReal_eq
  given: (f : C_c(α, Real>=0))
  statement: nnrealPart (-toReal f) = 0
  proof: by ext x; simp

中文:
引理 nnrealPart_neg_to实数_eq
  条件: (f : C_c(α, 实数>=0))
  结论: nnrealPart (-to实数 f) = 0
  证明: by ext x; simp
-/
lemma nnrealPart_neg_toReal_eq (f : C_c(α, Real>=0)) : nnrealPart (-toReal f) = 0 := by ext x; simp

section toNNRealLinear

/--
Definition of `toNNRealLinear` / `toNNRealLinear` 的定义

English:
definition toNNRealLinear
  signature: (Λ : C_c(α, Real) ->ₚ[Real] Real)
  body: .mk (Λ (toRealLinearMap f)) (Λ.map_nonneg (by simp))
  map_add' f g := by simp; rfl
  map_smul' a f := by simp [NNReal.smul_def]; rfl

@[simp]

中文:
定义 toNN实数Linear
  签名: (Λ : C_c(α, 实数) ->ₚ[实数] 实数)
  定义体: .mk (Λ (toRealLinearMap f)) (Λ.map_nonneg (by simp))
  map_add' f g := by simp; rfl
  map_smul' a f := by simp [NNReal.smul_def]; rfl

@[simp]

Depends on / 依赖: map_nonneg, toRealLinearMap
-/
noncomputable def toNNRealLinear (Λ : C_c(α, Real) ->ₚ[Real] Real) :
    C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0 where
  toFun f := .mk (Λ (toRealLinearMap f)) (Λ.map_nonneg (by simp))
  map_add' f g := by simp; rfl
  map_smul' a f := by simp [NNReal.smul_def]; rfl

@[simp]
/--
lemma `toNNRealLinear_apply` / 引理 `toNNRealLinear_apply`

English:
lemma toNNRealLinear_apply
  given: (Λ : C_c(α, Real) ->ₚ[Real] Real) (f : C_c(α, Real>=0))
  proof: rfl

@[simp]

中文:
引理 toNN实数Linear_apply
  条件: (Λ : C_c(α, 实数) ->ₚ[实数] 实数) (f : C_c(α, 实数>=0))
  证明: rfl

@[simp]
-/
lemma toNNRealLinear_apply (Λ : C_c(α, Real) ->ₚ[Real] Real) (f : C_c(α, Real>=0)) :
    toNNRealLinear Λ f = Λ (toReal f) := rfl

@[simp]
/--
lemma `toNNRealLinear_inj` / 引理 `toNNRealLinear_inj`

English:
lemma toNNRealLinear_inj
  given: (Λ₁ Λ₂ : C_c(α, Real) ->ₚ[Real] Real)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  ext f
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply] at h
  simp_rw [map_sub, h]

中文:
引理 toNN实数Linear_inj
  条件: (Λ₁ Λ₂ : C_c(α, 实数) ->ₚ[实数] 实数)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  ext f
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply] at h
  simp_rw [map_sub, h]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, NNReal, NNReal.eq_iff, eq_iff, ext_iff, map_sub, nnrealPart_sub_nnrealPart_neg, simp_rw, toNNRealLinear_apply
-/
lemma toNNRealLinear_inj (Λ₁ Λ₂ : C_c(α, Real) ->ₚ[Real] Real) :
    toNNRealLinear Λ₁ = toNNRealLinear Λ₂ ↔ Λ₁ = Λ₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  ext f
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply] at h
  simp_rw [map_sub, h]

end toNNRealLinear

section toRealPositiveLinear

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toRealPositiveLinear` / `toRealPositiveLinear` 的定义

English:
definition toRealPositiveLinear
  signature: (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0)
  body: PositiveLinearMap.mk₀
    { toFun := fun f => Λ (nnrealPart f) - Λ (nnrealPart (- f))
      map_add' f g := by
        simp only [neg_add_rev]
        obtain ⟨h, hh⟩ := exists_add_nnrealPart_add_eq f g
        rw [← add_zero ((Λ (f + g).nnrealPart).toReal - (Λ (-g + -f).nnrealPart).toReal)]; rw [← sub_self (Λ h).toReal]; rw [sub_add_sub_comm]; rw [← NNReal.coe_add]; rw [← NNReal.coe_add]; rw [← map_add]; rw [← map_add]; rw [hh.1]; rw [add_comm (-g) (-f)]; rw [hh.2]
        simp only [map_add, NNReal.coe_add]
        ring
      map_smul' a f := by
        rcases le_total 0 a with ha | ha
        · rw [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f), nnrealPart_smul_pos f ha,
            nnrealPart_smul_pos (-f) ha]
          simp [sup_of_le_left ha, mul_sub]
        · simp only [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f),
            nnrealPart_smul_neg f ha, nnrealPart_smul_neg (-f) ha, map_smul,
            NNReal.coe_mul, Real.coe_toNNReal', neg_neg, sup_of_le_left (neg_nonneg.mpr ha)]
          ring }
    (fun g hg => by simp [nnrealPart_neg_eq_zero_of_nonneg hg])

中文:
定义 to实数PositiveLinear
  签名: (Λ : C_c(α, 实数>=0) ->ₗ[实数>=0] 实数>=0)
  定义体: PositiveLinearMap.mk₀
    { toFun := fun f => Λ (nnrealPart f) - Λ (nnrealPart (- f))
      map_add' f g := by
        simp only [neg_add_rev]
        obtain ⟨h, hh⟩ := exists_add_nnrealPart_add_eq f g
        rw [← add_zero ((Λ (f + g).nnrealPart).toReal - (Λ (-g + -f).nnrealPart).toReal)]; rw [← sub_self (Λ h).toReal]; rw [sub_add_sub_comm]; rw [← NNReal.coe_add]; rw [← NNReal.coe_add]; rw [← map_add]; rw [← map_add]; rw [hh.1]; rw [add_comm (-g) (-f)]; rw [hh.2]
        simp only [map_add, NNReal.coe_add]
        ring
      map_smul' a f := by
        rcases le_total 0 a with ha | ha
        · rw [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f), nnrealPart_smul_pos f ha,
            nnrealPart_smul_pos (-f) ha]
          simp [sup_of_le_left ha, mul_sub]
        · simp only [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f),
            nnrealPart_smul_neg f ha, nnrealPart_smul_neg (-f) ha, map_smul,
            NNReal.coe_mul, Real.coe_toNNReal', neg_neg, sup_of_le_left (neg_nonneg.mpr ha)]
          ring }
    (fun g hg => by simp [nnrealPart_neg_eq_zero_of_nonneg hg])

Depends on / 依赖: NNReal, NNReal.coe_add, PositiveLinearMap, PositiveLinearMap.mk, add_comm, add_zero, coe_add, exists_add_nnrealPart_add_eq, map_add, map_smul, neg_add_rev, nnrealPart, sub_add_sub_comm, sub_self, toReal
-/
noncomputable def toRealPositiveLinear (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) : C_c(α, Real) ->ₚ[Real] Real :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Λ (nnrealPart f) - Λ (nnrealPart (- f))
      map_add' f g := by
        simp only [neg_add_rev]
        obtain ⟨h, hh⟩ := exists_add_nnrealPart_add_eq f g
        rw [← add_zero ((Λ (f + g).nnrealPart).toReal - (Λ (-g + -f).nnrealPart).toReal)]; rw [← sub_self (Λ h).toReal]; rw [sub_add_sub_comm]; rw [← NNReal.coe_add]; rw [← NNReal.coe_add]; rw [← map_add]; rw [← map_add]; rw [hh.1]; rw [add_comm (-g) (-f)]; rw [hh.2]
        simp only [map_add, NNReal.coe_add]
        ring
      map_smul' a f := by
        rcases le_total 0 a with ha | ha
        · rw [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f), nnrealPart_smul_pos f ha,
            nnrealPart_smul_pos (-f) ha]
          simp [sup_of_le_left ha, mul_sub]
        · simp only [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f),
            nnrealPart_smul_neg f ha, nnrealPart_smul_neg (-f) ha, map_smul,
            NNReal.coe_mul, Real.coe_toNNReal', neg_neg, sup_of_le_left (neg_nonneg.mpr ha)]
          ring }
    (fun g hg => by simp [nnrealPart_neg_eq_zero_of_nonneg hg])

/--
lemma `toRealPositiveLinear_apply` / 引理 `toRealPositiveLinear_apply`

English:
lemma toRealPositiveLinear_apply
  given: {Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0} (f : C_c(α, Real))
  proof: rfl

@[simp]

中文:
引理 to实数PositiveLinear_apply
  条件: {Λ : C_c(α, 实数>=0) ->ₗ[实数>=0] 实数>=0} (f : C_c(α, 实数))
  证明: rfl

@[simp]
-/
lemma toRealPositiveLinear_apply {Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0} (f : C_c(α, Real)) :
    toRealPositiveLinear Λ f = Λ (nnrealPart f) - Λ (nnrealPart (-f)) := rfl

@[simp]
/--
lemma `eq_toRealPositiveLinear_toReal` / 引理 `eq_toRealPositiveLinear_toReal`

English:
lemma eq_toRealPositiveLinear_toReal
  given: (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) (f : C_c(α, Real>=0))
  proof: by
  simp [toRealPositiveLinear_apply]

@[simp]

中文:
引理 eq_to实数PositiveLinear_to实数
  条件: (Λ : C_c(α, 实数>=0) ->ₗ[实数>=0] 实数>=0) (f : C_c(α, 实数>=0))
  证明: by
  simp [toRealPositiveLinear_apply]

@[simp]

Depends on / 依赖: toRealPositiveLinear_apply
-/
lemma eq_toRealPositiveLinear_toReal (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) (f : C_c(α, Real>=0)) :
    toRealPositiveLinear Λ (toReal f) = Λ f := by
  simp [toRealPositiveLinear_apply]

@[simp]
/--
lemma `eq_toNNRealLinear_toRealPositiveLinear` / 引理 `eq_toNNRealLinear_toRealPositiveLinear`

English:
lemma eq_toNNRealLinear_toRealPositiveLinear
  given: (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0)
  proof: by
  ext f
  simp

中文:
引理 eq_toNN实数Linear_to实数PositiveLinear
  条件: (Λ : C_c(α, 实数>=0) ->ₗ[实数>=0] 实数>=0)
  证明: by
  ext f
  simp
-/
lemma eq_toNNRealLinear_toRealPositiveLinear (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) :
    toNNRealLinear (toRealPositiveLinear Λ) = Λ := by
  ext f
  simp

end toRealPositiveLinear

section pullback

variable [R1Space α] [Group α] [TopologicalSpace β] [R1Space β] [Group β] [ContinuousMul β]
  [NormedAddCommGroup γ] {φ : α ->* β} (hφ : Topology.IsClosedEmbedding φ)

open scoped Pointwise in
/-- Pull back a continuous compactly supported function `f` on `β` along a closed embedding
`φ : α →* β` to the continuous compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /-- Pull back a continuous compactly supported function `f` on `β` along a closed
embedding `φ : α →+ β` to the continuous compactly supported function `a ↦ f (b + φ a)` on `A`. -/]
/--
Definition of `pullback_monoidHom` / `pullback_monoidHom` 的定义

English:
definition pullback_monoidHom
  signature: (f : CompactlySupportedContinuousMap β γ) (b : β)
  body: f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      hφ.isCompact_preimage (hK.smul b⁻¹), fun x hx => hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by fun_prop

@[to_additive]

中文:
定义 pullback_monoidHom
  签名: (f : 余mpactlySupportedContinuous映射 β γ) (b : β)
  定义体: f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      hφ.isCompact_preimage (hK.smul b⁻¹), fun x hx => hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by fun_prop

@[to_additive]
-/
noncomputable def pullback_monoidHom (f : CompactlySupportedContinuousMap β γ) (b : β) :
    CompactlySupportedContinuousMap α γ where
  toFun a := f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      hφ.isCompact_preimage (hK.smul b⁻¹), fun x hx => hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by fun_prop

@[to_additive]
/--
theorem `pullback_monoidHom_def` / 定理 `pullback_monoidHom_def`

English:
theorem pullback_monoidHom_def
  given: (f : CompactlySupportedContinuousMap β γ) (b : β) (a : α)
  proof: rfl

中文:
定理 pullback_monoidHom_def
  条件: (f : 余mpactlySupportedContinuous映射 β γ) (b : β) (a : α)
  证明: rfl
-/
theorem pullback_monoidHom_def (f : CompactlySupportedContinuousMap β γ) (b : β) (a : α) :
    pullback_monoidHom hφ f b a = f (b * φ a) :=
  rfl

end pullback

end CompactlySupportedContinuousMap

end NonnegativePart
