/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import Mathlib.Topology.ContinuousMap.CocompactMap

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ C₀(α, β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more instances of algebraic structures (e.g., `NonUnitalSemiring`) once the necessary
  type classes (e.g., `IsTopologicalRing`) are sufficiently generalized.
* Relate the unitization of `C₀(α, β)` to the Alexandroff compactification.
-/

@[expose] public section


universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

/--
Definition of `ZeroAtInftyContinuousMap` / `ZeroAtInftyContinuousMap` 的定义

English:
structure ZeroAtInftyContinuousMap
  parameters: (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
  extends: ContinuousMap α β
  axioms and operations (1):
    - zero_at_infty' : Tendsto toFun (cocompact α) (𝓝 0)

中文:
结构 ZeroAtInftyContinuous映射
  参数: (α : 类型u) (β : 类型v) [拓扑空间 α] [零 β]
  继承: 连续映射 α β
  公理与运算 (1 个):
    - zero_at_infty' : 收敛 toFun (cocompact α) (𝓝 0)
-/
structure ZeroAtInftyContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] : Type max u v extends ContinuousMap α β where
  /-- The function tends to zero along the `cocompact` filter. -/
  zero_at_infty' : Tendsto toFun (cocompact α) (𝓝 0)

@[inherit_doc]
scoped[ZeroAtInfty] notation (priority := 2000) "C₀(" α ", " β ")" => ZeroAtInftyContinuousMap α β

@[inherit_doc]
scoped[ZeroAtInfty] notation α " ->C₀ " β => ZeroAtInftyContinuousMap α β

open ZeroAtInfty

section

/--
Definition of `ZeroAtInftyContinuousMapClass` / `ZeroAtInftyContinuousMapClass` 的定义

English:
class ZeroAtInftyContinuousMapClass
  parameters: (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - zero_at_infty((f : F)) : Tendsto f (cocompact α) (𝓝 0)

中文:
类 ZeroAtInftyContinuous映射类
  参数: (F : 类型) (α β : outParam 类型) [拓扑空间 α]
  继承: 连续映射类 F α β
  公理与运算 (1 个):
    - zero_at_infty((f : F)) : 收敛 f (cocompact α) (𝓝 0)
-/
class ZeroAtInftyContinuousMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
    [Zero β] [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- Each member of the class tends to zero along the `cocompact` filter. -/
  zero_at_infty (f : F) : Tendsto f (cocompact α) (𝓝 0)

end

export ZeroAtInftyContinuousMapClass (zero_at_infty)

namespace ZeroAtInftyContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β] [FunLike F α β] [ZeroAtInftyContinuousMapClass F α β]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike C₀(α, β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : 函数状 C₀(α, β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike C₀(α, β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `instZeroAtInftyContinuousMapClass` / 实例 `instZeroAtInftyContinuousMapClass`

English:
instance instZeroAtInftyContinuousMapClass
  signature: : ZeroAtInftyContinuousMapClass C₀(α, β) α β where
  body: f.continuous_toFun
  zero_at_infty f := f.zero_at_infty'

中文:
实例 instZeroAtInftyContinuousMapClass
  签名: : ZeroAtInftyContinuous映射类 C₀(α, β) α β where
  定义体: f.continuous_toFun
  zero_at_infty f := f.zero_at_infty'

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass C₀(α, β) α β where
  map_continuous f := f.continuous_toFun
  zero_at_infty f := f.zero_at_infty'

/--
Instance `instCoeTC` / 实例 `instCoeTC`

English:
instance instCoeTC
  signature: : CoeTC F C₀(α, β)
  body: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_at_infty' := zero_at_infty f }⟩

@[simp]

中文:
实例 instCoeTC
  签名: : CoeTC F C₀(α, β)
  定义体: ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_at_infty' := zero_at_infty f }⟩

@[simp]

Depends on / 依赖: continuous_toFun, map_continuous, zero_at_infty
-/
instance instCoeTC : CoeTC F C₀(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_at_infty' := zero_at_infty f }⟩

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (f : C₀(α, β))
  statement: (f.toContinuousMap : α -> β) = f
  proof: rfl

@[ext]

中文:
定理 coe_toContinuousMap
  条件: (f : C₀(α, β))
  结论: (f.toContinuousMap : α -> β) = f
  证明: rfl

@[ext]
-/
theorem coe_toContinuousMap (f : C₀(α, β)) : (f.toContinuousMap : α -> β) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : C₀(α, β)} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[simp]

中文:
定理 ext
  条件: {f g : C₀(α, β)} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : C₀(α, β)} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: {f : α -> β} (hf : Continuous f) (hf' : Tendsto f (cocompact α) (𝓝 0))
  proof: rfl

中文:
引理 coe_mk
  条件: {f : α -> β} (hf : 连续 f) (hf' : 收敛 f (cocompact α) (𝓝 0))
  证明: rfl
-/
lemma coe_mk {f : α -> β} (hf : Continuous f) (hf' : Tendsto f (cocompact α) (𝓝 0)) :
    { toFun := f,
      continuous_toFun := hf,
      zero_at_infty' := hf' : ZeroAtInftyContinuousMap α β } = f :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  body: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  zero_at_infty' := by
    simp_rw [h]
    exact f.zero_at_infty'

@[simp]

中文:
定义 copy
  签名: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  定义体: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  zero_at_infty' := by
    simp_rw [h]
    exact f.zero_at_infty'

@[simp]
-/
protected def copy (f : C₀(α, β)) (f' : α -> β) (h : f' = f) : C₀(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  zero_at_infty' := by
    simp_rw [h]
    exact f.zero_at_infty'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : C₀(α, β)) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : C₀(α, β)) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : C₀(α, β)) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
theorem `eq_of_empty` / 定理 `eq_of_empty`

English:
theorem eq_of_empty
  given: [IsEmpty α] (f g : C₀(α, β))
  statement: f = g
  proof: ext IsEmpty.elim ‹_›

中文:
定理 eq_of_empty
  条件: [是空 α] (f g : C₀(α, β))
  结论: f = g
  证明: ext IsEmpty.elim ‹_›

Depends on / 依赖: IsEmpty, IsEmpty.elim
-/
theorem eq_of_empty [IsEmpty α] (f g : C₀(α, β)) : f = g :=
ext IsEmpty.elim ‹_›

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. -/
@[simps]
/--
Definition of `ContinuousMap.liftZeroAtInfty` / `ContinuousMap.liftZeroAtInfty` 的定义

English:
definition ContinuousMap.liftZeroAtInfty
  signature: [CompactSpace α]
  body: { toFun := f
      zero_at_infty' := by simp }
  invFun f := f

中文:
定义 连续映射.liftZeroAtInfty
  签名: [紧空间 α]
  定义体: { toFun := f
      zero_at_infty' := by simp }
  invFun f := f

Depends on / 依赖: invFun, zero_at_infty
-/
def ContinuousMap.liftZeroAtInfty [CompactSpace α] : C(α, β) ≃ C₀(α, β) where
  toFun f :=
    { toFun := f
      zero_at_infty' := by simp }
  invFun f := f

/--
lemma `zeroAtInftyContinuousMapClass.ofCompact` / 引理 `zeroAtInftyContinuousMapClass.ofCompact`

English:
lemma zeroAtInftyContinuousMapClass.ofCompact
  statement: {G : Type*} [FunLike G α β]
  proof: map_continuous
  zero_at_infty := by simp

中文:
引理 zeroAtInftyContinuousMapClass.ofCompact
  结论: {G : 类型} [函数状 G α β]
  证明: map_continuous
  zero_at_infty := by simp

Depends on / 依赖: map_continuous
-/
lemma zeroAtInftyContinuousMapClass.ofCompact {G : Type*} [FunLike G α β]
    [ContinuousMapClass G α β] [CompactSpace α] : ZeroAtInftyContinuousMapClass G α β where
  map_continuous := map_continuous
  zero_at_infty := by simp

end Basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C₀(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C₀(α, β)` will not have a multiplicative identity.
-/


section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero β]
  body: ⟨⟨0, tendsto_const_nhds⟩⟩

中文:
实例 instZero
  签名: [零 β]
  定义体: ⟨⟨0, tendsto_const_nhds⟩⟩

Depends on / 依赖: tendsto_const_nhds
-/
instance instZero [Zero β] : Zero C₀(α, β) :=
  ⟨⟨0, tendsto_const_nhds⟩⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Zero β]
  body: ⟨0⟩

@[simp]

中文:
实例 instInhabited
  签名: [零 β]
  定义体: ⟨0⟩

@[simp]
-/
instance instInhabited [Zero β] : Inhabited C₀(α, β) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  given: [Zero β]
  statement: ⇑(0 : C₀(α, β)) = 0
  proof: rfl

中文:
定理 coe_zero
  条件: [零 β]
  结论: ⇑(0 : C₀(α, β)) = 0
  证明: rfl
-/
theorem coe_zero [Zero β] : ⇑(0 : C₀(α, β)) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [Zero β]
  statement: (0 : C₀(α, β)) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: [零 β]
  结论: (0 : C₀(α, β)) x = 0
  证明: rfl
-/
theorem zero_apply [Zero β] : (0 : C₀(α, β)) x = 0 :=
  rfl

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [MulZeroClass β] [ContinuousMul β]
  body: ⟨fun f g =>
    ⟨f * g, by simpa only [mul_zero] using! (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp]

中文:
实例 instMul
  签名: [乘零类 β] [连续乘法 β]
  定义体: ⟨fun f g =>
    ⟨f * g, by simpa only [mul_zero] using! (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp]

Depends on / 依赖: mul_zero, zero_at_infty
-/
instance instMul [MulZeroClass β] [ContinuousMul β] : Mul C₀(α, β) :=
  ⟨fun f g =>
    ⟨f * g, by simpa only [mul_zero] using! (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β))
  statement: ⇑(f * g) = f * g
  proof: rfl

中文:
定理 coe_mul
  条件: [乘零类 β] [连续乘法 β] (f g : C₀(α, β))
  结论: ⇑(f * g) = f * g
  证明: rfl
-/
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : ⇑(f * g) = f * g :=
  rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β))
  statement: (f * g) x = f x * g x
  proof: rfl

中文:
定理 mul_apply
  条件: [乘零类 β] [连续乘法 β] (f g : C₀(α, β))
  结论: (f * g) x = f x * g x
  证明: rfl
-/
theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
  rfl

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass β] [ContinuousMul β]
  body: fast_instance% DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

中文:
实例 instMulZeroClass
  签名: [乘零类 β] [连续乘法 β]
  定义体: fast_instance% DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulZeroClass, coe_injective, coe_mul, coe_zero, fast_instance, mulZeroClass
-/
instance instMulZeroClass [MulZeroClass β] [ContinuousMul β] : MulZeroClass C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero β] [ContinuousMul β]
  body: fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

中文:
实例 instSemigroupWithZero
  签名: [带零半群 β] [连续乘法 β]
  定义体: fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

Depends on / 依赖: fast_instance
-/
instance instSemigroupWithZero [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C₀(α, β) := fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [AddZeroClass β] [ContinuousAdd β]
  body: ⟨fun f g => ⟨f + g, by simpa only [add_zero] using! (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp]

中文:
实例 instAdd
  签名: [加法零类 β] [连续加法 β]
  定义体: ⟨fun f g => ⟨f + g, by simpa only [add_zero] using! (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp]

Depends on / 依赖: add_zero, zero_at_infty
-/
instance instAdd [AddZeroClass β] [ContinuousAdd β] : Add C₀(α, β) :=
  ⟨fun f g => ⟨f + g, by simpa only [add_zero] using! (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β))
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
定理 coe_add
  条件: [加法零类 β] [连续加法 β] (f g : C₀(α, β))
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : ⇑(f + g) = f + g :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β))
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
定理 add_apply
  条件: [加法零类 β] [连续加法 β] (f g : C₀(α, β))
  结论: (f + g) x = f x + g x
  证明: rfl
-/
theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
  rfl

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: [AddZeroClass β] [ContinuousAdd β]
  body: fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

中文:
实例 instAddZeroClass
  签名: [加法零类 β] [连续加法 β]
  定义体: fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addZeroClass, addZeroClass, coe_add, coe_injective, coe_zero, fast_instance
-/
instance instAddZeroClass [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
  body: ⟨fun r f => ⟨r • f, by simpa [smul_zero] using! (zero_at_infty f).const_smul r⟩⟩

@[simp, norm_cast]

中文:
实例 instSMul
  签名: [零 β] {R : 类型} [零 R] [带零标量乘法 R β] [连续常数标量乘法 R β]
  定义体: ⟨fun r f => ⟨r • f, by simpa [smul_zero] using! (zero_at_infty f).const_smul r⟩⟩

@[simp, norm_cast]

Depends on / 依赖: const_smul, smul_zero, zero_at_infty
-/
instance instSMul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMul R C₀(α, β) :=
  ⟨fun r f => ⟨r • f, by simpa [smul_zero] using! (zero_at_infty f).const_smul r⟩⟩

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
  proof: rfl

中文:
定理 coe_smul
  结论: [零 β] {R : 类型} [零 R] [带零标量乘法 R β] [连续常数标量乘法 R β] (r : R)
  证明: rfl
-/
theorem coe_smul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
    (f : C₀(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
  proof: rfl

中文:
定理 smul_apply
  结论: [零 β] {R : 类型} [零 R] [带零标量乘法 R β] [连续常数标量乘法 R β]
  证明: rfl
-/
theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
    (r : R) (f : C₀(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

variable [AddMonoid β] [ContinuousAdd β] (f g : C₀(α, β))

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid C₀(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 instAddMonoid
  签名: : 加法幺半群 C₀(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instAddMonoid : AddMonoid C₀(α, β) := fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid β] [ContinuousAdd β]
  body: fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 instAddCommMonoid
  签名: [加法交换幺半群 β] [连续加法 β]
  定义体: fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_zero, fast_instance
-/
instance instAddCommMonoid [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C₀(α, β))

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg C₀(α, β)
  body: ⟨fun f => ⟨-f, by simpa only [neg_zero] using! (zero_at_infty f).neg⟩⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 C₀(α, β)
  定义体: ⟨fun f => ⟨-f, by simpa only [neg_zero] using! (zero_at_infty f).neg⟩⟩

@[simp]

Depends on / 依赖: neg_zero, zero_at_infty
-/
instance instNeg : Neg C₀(α, β) :=
  ⟨fun f => ⟨-f, by simpa only [neg_zero] using! (zero_at_infty f).neg⟩⟩

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
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub C₀(α, β)
  body: ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using! (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp]

中文:
实例 instSub
  签名: : 减法 C₀(α, β)
  定义体: ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using! (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp]

Depends on / 依赖: sub_zero, zero_at_infty
-/
instance instSub : Sub C₀(α, β) :=
  ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using! (zero_at_infty f).sub (zero_at_infty g)⟩⟩

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
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: : AddGroup C₀(α, β)
  body: fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddGroup
  签名: : 加法群 C₀(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instAddGroup : AddGroup C₀(α, β) := fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup β] [IsTopologicalAddGroup β]
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

中文:
实例 instAddCommGroup
  签名: [加法交换群 β] [是拓扑加群 β]
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_sub, coe_zero, fast_instance
-/
instance instAddCommGroup [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C₀(α, β) :=
  fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
  body: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

中文:
实例 instIsCentralScalar
  签名: [零 β] {R : 类型} [零 R] [带零标量乘法 R β] [带零标量乘法 Rᵐᵒᵖ β]
  定义体: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: op_smul_eq_smul
-/
instance instIsCentralScalar [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C₀(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

/--
Instance `instSMulWithZero` / 实例 `instSMulWithZero`

English:
instance instSMulWithZero
  signature: [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
  body: fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

中文:
实例 instSMulWithZero
  签名: [零 β] {R : 类型} [零 R] [带零标量乘法 R β]
  定义体: fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance instSMulWithZero [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C₀(α, β) := fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

/--
Instance `instMulActionWithZero` / 实例 `instMulActionWithZero`

English:
instance instMulActionWithZero
  signature: [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
  body: fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

中文:
实例 instMulActionWithZero
  签名: [零 β] {R : 类型} [带零幺半群 R] [带零乘法作用 R β]
  定义体: fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance instMulActionWithZero [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C₀(α, β) := fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
  body: fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

中文:
实例 instModule
  签名: [加法交换幺半群 β] [连续加法 β] {R : 类型} [半环 R] [模 R β]
  定义体: fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance instModule [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C₀(α, β) := fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 β] [是TopologicalSemiring β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring β] [IsTopologicalSemiring β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 β] [是TopologicalSemiring β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instNonUnitalSemiring [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring β] [IsTopologicalSemiring β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 instNonUnitalCommSemiring
  签名: [非幺交换半环 β] [是TopologicalSemiring β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing β] [IsTopologicalRing β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instNonUnitalNonAssocRing
  签名: [非幺非结合环 β] [是拓扑环 β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing β] [IsTopologicalRing β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 instNonUnitalRing
  签名: [非幺环 β] [是拓扑环 β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalRing, coe_add, coe_injective, coe_mul, coe_neg, coe_sub, coe_zero, fast_instance, nonUnitalRing
-/
instance instNonUnitalRing [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C₀(α, β) :=
  fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing β] [IsTopologicalRing β]
  body: fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instNonUnitalCommRing
  签名: [非幺交换环 β] [是拓扑环 β]
  定义体: fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance instNonUnitalCommRing [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
  body: by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_assoc]

中文:
实例 instIsScalarTower
  签名: {R : 类型} [半环 R] [非幺非结合半环 β]
  定义体: by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_assoc]

Depends on / 依赖: Pi.mul_apply, Pi.smul_apply, coe_mul, coe_smul, mul_apply, smul_apply, smul_assoc, smul_eq_mul
-/
instance instIsScalarTower {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C₀(α, β) C₀(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_assoc]

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
  body: by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_comm]

中文:
实例 instSMulCommClass
  签名: {R : 类型} [半环 R] [非幺非结合半环 β]
  定义体: by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_comm]

Depends on / 依赖: Pi.mul_apply, Pi.smul_apply, coe_mul, coe_smul, mul_apply, smul_apply, smul_comm, smul_eq_mul
-/
instance instSMulCommClass {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C₀(α, β) C₀(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [smul_comm]

end AlgebraicStructure

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ]
variable [FunLike F β γ] [ZeroAtInftyContinuousMapClass F β γ]

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (f : F)
  statement: UniformContinuous (f : β -> γ)
  proof: (map_continuous f).uniformContinuous_of_tendsto_cocompact (zero_at_infty f)

中文:
定理 uniformContinuous
  条件: (f : F)
  结论: 一致连续 (f : β -> γ)
  证明: (map_continuous f).uniformContinuous_of_tendsto_cocompact (zero_at_infty f)

Depends on / 依赖: map_continuous, uniformContinuous_of_tendsto_cocompact, zero_at_infty
-/
theorem uniformContinuous (f : F) : UniformContinuous (f : β -> γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact (zero_at_infty f)

end Uniform

/-! ### Metric structure

When `β` is a metric space, then every element of `C₀(α, β)` is bounded, and so there is a natural
inclusion map `ZeroAtInftyContinuousMap.toBCF : C₀(α, β) → (α →ᵇ β)`. Via this map `C₀(α, β)`
inherits a metric as the pullback of the metric on `α →ᵇ β`. Moreover, this map has closed range
in `α →ᵇ β` and consequently `C₀(α, β)` is a complete space whenever `β` is complete.
-/


section Metric

open Metric Set

variable [PseudoMetricSpace β] [Zero β] [FunLike F α β] [ZeroAtInftyContinuousMapClass F α β]

/--
theorem `bounded` / 定理 `bounded`

English:
theorem bounded
  given: (f : F)
  statement: exists C, forall x y : α, dist ((f : α -> β) x) (f y) <= C
  proof: by
  obtain ⟨K : Set α, hK₁, hK₂⟩ := mem_cocompact.mp
    (tendsto_def.mp (zero_at_infty (f : F)) _ (closedBall_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).isBounded.subset_closedBall (0 : β)
  refine ⟨max C 1 + max C 1, fun x y => ?_⟩
  have : forall x, f x in closedBall (0 : β) (max C 1) := by
    intro x
    by_cases hx : x in K
    · exact (mem_closedBall.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closedBall.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closedBall.mp <| this x) (mem_closedBall'.mp <| this y))

中文:
定理 bounded
  条件: (f : F)
  结论: 存在 C, 对任意 x y : α, dist ((f : α -> β) x) (f y) <= C
  证明: by
  obtain ⟨K : Set α, hK₁, hK₂⟩ := mem_cocompact.mp
    (tendsto_def.mp (zero_at_infty (f : F)) _ (closedBall_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).isBounded.subset_closedBall (0 : β)
  refine ⟨max C 1 + max C 1, fun x y => ?_⟩
  have : forall x, f x in closedBall (0 : β) (max C 1) := by
    intro x
    by_cases hx : x in K
    · exact (mem_closedBall.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closedBall.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closedBall.mp <| this x) (mem_closedBall'.mp <| this y))
-/
protected theorem bounded (f : F) : exists C, forall x y : α, dist ((f : α -> β) x) (f y) <= C := by
  obtain ⟨K : Set α, hK₁, hK₂⟩ := mem_cocompact.mp
    (tendsto_def.mp (zero_at_infty (f : F)) _ (closedBall_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).isBounded.subset_closedBall (0 : β)
  refine ⟨max C 1 + max C 1, fun x y => ?_⟩
  have : forall x, f x in closedBall (0 : β) (max C 1) := by
    intro x
    by_cases hx : x in K
    · exact (mem_closedBall.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closedBall.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closedBall.mp <| this x) (mem_closedBall'.mp <| this y))

/--
theorem `isBounded_range` / 定理 `isBounded_range`

English:
theorem isBounded_range
  given: (f : C₀(α, β))
  statement: IsBounded (range f)
  proof: isBounded_range_iff.2 (ZeroAtInftyContinuousMap.bounded f)

中文:
定理 isBounded_range
  条件: (f : C₀(α, β))
  结论: IsBounded (range f)
  证明: isBounded_range_iff.2 (ZeroAtInftyContinuousMap.bounded f)

Depends on / 依赖: ZeroAtInftyContinuousMap, ZeroAtInftyContinuousMap.bounded, bounded, isBounded_range_iff
-/
theorem isBounded_range (f : C₀(α, β)) : IsBounded (range f) :=
  isBounded_range_iff.2 (ZeroAtInftyContinuousMap.bounded f)

/--
theorem `isBounded_image` / 定理 `isBounded_image`

English:
theorem isBounded_image
  given: (f : C₀(α, β)) (s : Set α)
  statement: IsBounded (f '' s)
  proof: f.isBounded_range.subset image_subset_range _ _

中文:
定理 isBounded_image
  条件: (f : C₀(α, β)) (s : 集合 α)
  结论: IsBounded (f '' s)
  证明: f.isBounded_range.subset image_subset_range _ _

Depends on / 依赖: f.isBounded_range.subset, image_subset_range, isBounded_range, subset
-/
theorem isBounded_image (f : C₀(α, β)) (s : Set α) : IsBounded (f '' s) :=
f.isBounded_range.subset image_subset_range _ _

instance (priority := 100) instBoundedContinuousMapClass : BoundedContinuousMapClass F α β :=
  { ‹ZeroAtInftyContinuousMapClass F α β› with
    map_bounded := fun f => ZeroAtInftyContinuousMap.bounded f }

/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps!]
/--
Definition of `toBCF` / `toBCF` 的定义

English:
definition toBCF
  signature: (f : C₀(α, β))
  body: ⟨f, map_bounded f⟩

中文:
定义 toBCF
  签名: (f : C₀(α, β))
  定义体: ⟨f, map_bounded f⟩

Depends on / 依赖: map_bounded
-/
def toBCF (f : C₀(α, β)) : α ->ᵇ β :=
  ⟨f, map_bounded f⟩

section

variable (α) (β)

/--
theorem `toBCF_injective` / 定理 `toBCF_injective`

English:
theorem toBCF_injective
  statement: Function.Injective (toBCF : C₀(α, β) -> α ->ᵇ β)
  proof: fun f g h => by
  ext x
  simpa only using! DFunLike.congr_fun h x

中文:
定理 toBCF_injective
  结论: 函数.单射 (toBCF : C₀(α, β) -> α ->ᵇ β)
  证明: fun f g h => by
  ext x
  simpa only using! DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem toBCF_injective : Function.Injective (toBCF : C₀(α, β) -> α ->ᵇ β) := fun f g h => by
  ext x
  simpa only using! DFunLike.congr_fun h x

end

variable {f g : C₀(α, β)}

/--
Instance `instPseudoMetricSpace` / 实例 `instPseudoMetricSpace`

English:
instance instPseudoMetricSpace
  signature: : PseudoMetricSpace C₀(α, β)
  body: fast_instance%
  PseudoMetricSpace.induced toBCF inferInstance

中文:
实例 instPseudoMetricSpace
  签名: : 伪度量空间 C₀(α, β)
  定义体: fast_instance%
  PseudoMetricSpace.induced toBCF inferInstance

Depends on / 依赖: fast_instance
-/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace C₀(α, β) := fast_instance%
  PseudoMetricSpace.induced toBCF inferInstance

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: {β : Type*} [MetricSpace β] [Zero β]
  body: fast_instance%
  MetricSpace.induced _ (toBCF_injective α β) inferInstance

@[simp]

中文:
实例 instMetricSpace
  签名: {β : 类型} [度量空间 β] [零 β]
  定义体: fast_instance%
  MetricSpace.induced _ (toBCF_injective α β) inferInstance

@[simp]

Depends on / 依赖: fast_instance
-/
noncomputable instance instMetricSpace {β : Type*} [MetricSpace β] [Zero β] :
    MetricSpace C₀(α, β) := fast_instance%
  MetricSpace.induced _ (toBCF_injective α β) inferInstance

@[simp]
/--
theorem `dist_toBCF_eq_dist` / 定理 `dist_toBCF_eq_dist`

English:
theorem dist_toBCF_eq_dist
  given: {f g : C₀(α, β)}
  statement: dist f.toBCF g.toBCF = dist f g
  proof: rfl

中文:
定理 dist_toBCF_eq_dist
  条件: {f g : C₀(α, β)}
  结论: dist f.toBCF g.toBCF = dist f g
  证明: rfl
-/
theorem dist_toBCF_eq_dist {f g : C₀(α, β)} : dist f.toBCF g.toBCF = dist f g :=
  rfl

open BoundedContinuousFunction

/--
theorem `tendsto_iff_tendstoUniformly` / 定理 `tendsto_iff_tendstoUniformly`

English:
theorem tendsto_iff_tendstoUniformly
  given: {ι : Type*} {F : ι -> C₀(α, β)} {f : C₀(α, β)} {l : Filter ι}
  proof: by
  simpa only [Metric.tendsto_nhds] using!
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.toBCF l

中文:
定理 tendsto_iff_tendstoUniformly
  条件: {ι : 类型} {F : ι -> C₀(α, β)} {f : C₀(α, β)} {l : 滤子 ι}
  证明: by
  simpa only [Metric.tendsto_nhds] using!
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.toBCF l

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.tendsto_iff_tendstoUniformly, Metric, Metric.tendsto_nhds, f.toBCF, tendsto_iff_tendstoUniformly, tendsto_nhds
-/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι -> C₀(α, β)} {f : C₀(α, β)} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l := by
  simpa only [Metric.tendsto_nhds] using!
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.toBCF l

/--
theorem `isometry_toBCF` / 定理 `isometry_toBCF`

English:
theorem isometry_toBCF
  statement: Isometry (toBCF : C₀(α, β) -> α ->ᵇ β)
  proof: by tauto

中文:
定理 isometry_toBCF
  结论: 等距 (toBCF : C₀(α, β) -> α ->ᵇ β)
  证明: by tauto
-/
theorem isometry_toBCF : Isometry (toBCF : C₀(α, β) -> α ->ᵇ β) := by tauto

/--
theorem `isClosed_range_toBCF` / 定理 `isClosed_range_toBCF`

English:
theorem isClosed_range_toBCF
  statement: IsClosed (range (toBCF : C₀(α, β) -> α ->ᵇ β))
  proof: by
  refine isClosed_iff_clusterPt.mpr fun f hf => ?_
  rw [clusterPt_principal_iff] at hf
  have : Tendsto f (cocompact α) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine (Metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
      (Eventually.of_forall fun x hx => ?_)
    calc
      dist (f x) 0 <= dist (g.toBCF x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.toBCF f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
      _ <= ε := by grw [mem_ball.1 hg, add_halves ε]
  exact ⟨⟨f.toContinuousMap, this⟩, rfl⟩

中文:
定理 isClosed_range_toBCF
  结论: 是闭集 (range (toBCF : C₀(α, β) -> α ->ᵇ β))
  证明: by
  refine isClosed_iff_clusterPt.mpr fun f hf => ?_
  rw [clusterPt_principal_iff] at hf
  have : Tendsto f (cocompact α) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine (Metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
      (Eventually.of_forall fun x hx => ?_)
    calc
      dist (f x) 0 <= dist (g.toBCF x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.toBCF f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
      _ <= ε := by grw [mem_ball.1 hg, add_halves ε]
  exact ⟨⟨f.toContinuousMap, this⟩, rfl⟩

Depends on / 依赖: Eventually, Eventually.of_forall, Metric, Metric.tendsto_nhds.mp, Metric.tendsto_nhds.mpr, Tendsto, add_lt_add_of_l, ball_mem_nhds, clusterPt_principal_iff, cocompact, dist_triangle_left, g.toBCF, half_pos, isClosed_iff_clusterPt, isClosed_iff_clusterPt.mpr, of_forall, tendsto_nhds, zero_at_infty
-/
theorem isClosed_range_toBCF : IsClosed (range (toBCF : C₀(α, β) -> α ->ᵇ β)) := by
  refine isClosed_iff_clusterPt.mpr fun f hf => ?_
  rw [clusterPt_principal_iff] at hf
  have : Tendsto f (cocompact α) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine (Metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
      (Eventually.of_forall fun x hx => ?_)
    calc
      dist (f x) 0 <= dist (g.toBCF x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.toBCF f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
      _ <= ε := by grw [mem_ball.1 hg, add_halves ε]
  exact ⟨⟨f.toContinuousMap, this⟩, rfl⟩


/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace β]
  body: (completeSpace_iff_isComplete_range isometry_toBCF.isUniformInducing).mpr
    isClosed_range_toBCF.isComplete

中文:
实例 instCompleteSpace
  签名: [完备空间 β]
  定义体: (completeSpace_iff_isComplete_range isometry_toBCF.isUniformInducing).mpr
    isClosed_range_toBCF.isComplete

Depends on / 依赖: completeSpace_iff_isComplete_range, isClosed_range_toBCF, isClosed_range_toBCF.isComplete, isComplete, isUniformInducing, isometry_toBCF, isometry_toBCF.isUniformInducing
-/
instance instCompleteSpace [CompleteSpace β] : CompleteSpace C₀(α, β) :=
  (completeSpace_iff_isComplete_range isometry_toBCF.isUniformInducing).mpr
    isClosed_range_toBCF.isComplete

end Metric

section Norm

/-! ### Normed space

The norm structure on `C₀(α, β)` is the one induced by the inclusion `toBCF : C₀(α, β) → (α →ᵇ b)`,
viewed as an additive monoid homomorphism. Then `C₀(α, β)` is naturally a normed space over a normed
field `𝕜` whenever `β` is as well.
-/


section NormedSpace

/--
Instance `instSeminormedAddCommGroup` / 实例 `instSeminormedAddCommGroup`

English:
instance instSeminormedAddCommGroup
  signature: [SeminormedAddCommGroup β]
  body: fast_instance%
  SeminormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)

中文:
实例 instSeminormedAddCommGroup
  签名: [SeminormedAddComm群 β]
  定义体: fast_instance%
  SeminormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)

Depends on / 依赖: fast_instance
-/
noncomputable instance instSeminormedAddCommGroup [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup C₀(α, β) := fast_instance%
  SeminormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: [NormedAddCommGroup β]
  body: fast_instance%
  NormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)
    (toBCF_injective α β)

中文:
实例 instNormedAddCommGroup
  签名: [赋范交换加群 β]
  定义体: fast_instance%
  NormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)
    (toBCF_injective α β)

Depends on / 依赖: fast_instance
-/
noncomputable instance instNormedAddCommGroup [NormedAddCommGroup β] :
    NormedAddCommGroup C₀(α, β) := fast_instance%
  NormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) ->+ α ->ᵇ β)
    (toBCF_injective α β)

variable [SeminormedAddCommGroup β] {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 β]

@[simp]
/--
theorem `norm_toBCF_eq_norm` / 定理 `norm_toBCF_eq_norm`

English:
theorem norm_toBCF_eq_norm
  given: {f : C₀(α, β)}
  statement: ‖f.toBCF‖ = ‖f‖
  proof: rfl

中文:
定理 norm_toBCF_eq_norm
  条件: {f : C₀(α, β)}
  结论: ‖f.toBCF‖ = ‖f‖
  证明: rfl
-/
theorem norm_toBCF_eq_norm {f : C₀(α, β)} : ‖f.toBCF‖ = ‖f‖ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedSpace 𝕜 C₀(α, β)
  body: norm_smul_le k f.toBCF

中文:
实例 :
  签名: 赋范空间 𝕜 C₀(α, β)
  定义体: norm_smul_le k f.toBCF

Depends on / 依赖: f.toBCF, norm_smul_le
-/
noncomputable instance : NormedSpace 𝕜 C₀(α, β) where
  norm_smul_le k f := norm_smul_le k f.toBCF

end NormedSpace

section NormedRing

/--
Instance `instNonUnitalSeminormedRing` / 实例 `instNonUnitalSeminormedRing`

English:
instance instNonUnitalSeminormedRing
  signature: [NonUnitalSeminormedRing β]
  body: { instNonUnitalRing, instSeminormedAddCommGroup with
    norm_mul_le f g := norm_mul_le f.toBCF g.toBCF }

中文:
实例 instNonUnitalSeminormedRing
  签名: [非幺Seminormed环 β]
  定义体: { instNonUnitalRing, instSeminormedAddCommGroup with
    norm_mul_le f g := norm_mul_le f.toBCF g.toBCF }

Depends on / 依赖: f.toBCF, g.toBCF, instNonUnitalRing, instSeminormedAddCommGroup, norm_mul_le
-/
noncomputable instance instNonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing C₀(α, β) :=
  { instNonUnitalRing, instSeminormedAddCommGroup with
    norm_mul_le f g := norm_mul_le f.toBCF g.toBCF }

/--
Instance `instNonUnitalNormedRing` / 实例 `instNonUnitalNormedRing`

English:
instance instNonUnitalNormedRing
  signature: [NonUnitalNormedRing β]
  body: { instNonUnitalSeminormedRing, instNormedAddCommGroup with }

中文:
实例 instNonUnitalNormedRing
  签名: [非幺赋范环 β]
  定义体: { instNonUnitalSeminormedRing, instNormedAddCommGroup with }

Depends on / 依赖: instNonUnitalSeminormedRing, instNormedAddCommGroup
-/
noncomputable instance instNonUnitalNormedRing [NonUnitalNormedRing β] :
    NonUnitalNormedRing C₀(α, β) :=
  { instNonUnitalSeminormedRing, instNormedAddCommGroup with }

/--
Instance `instNonUnitalSeminormedCommRing` / 实例 `instNonUnitalSeminormedCommRing`

English:
instance instNonUnitalSeminormedCommRing
  signature: [NonUnitalSeminormedCommRing β]
  body: { instNonUnitalSeminormedRing, instNonUnitalCommRing with }

中文:
实例 instNonUnitalSeminormedCommRing
  签名: [非幺SeminormedComm环 β]
  定义体: { instNonUnitalSeminormedRing, instNonUnitalCommRing with }

Depends on / 依赖: instNonUnitalCommRing, instNonUnitalSeminormedRing
-/
noncomputable instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing C₀(α, β) :=
  { instNonUnitalSeminormedRing, instNonUnitalCommRing with }

/--
Instance `instNonUnitalNormedCommRing` / 实例 `instNonUnitalNormedCommRing`

English:
instance instNonUnitalNormedCommRing
  signature: [NonUnitalNormedCommRing β]
  body: { instNonUnitalNormedRing, instNonUnitalCommRing with }

中文:
实例 instNonUnitalNormedCommRing
  签名: [非幺NormedComm环 β]
  定义体: { instNonUnitalNormedRing, instNonUnitalCommRing with }

Depends on / 依赖: instNonUnitalCommRing, instNonUnitalNormedRing
-/
noncomputable instance instNonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing C₀(α, β) :=
  { instNonUnitalNormedRing, instNonUnitalCommRing with }

end NormedRing

end Norm

section Star

/-! ### Star structure

It is possible to equip `C₀(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`StarAddMonoid` is close enough.

The `StarAddMonoid` and `NormedStarGroup` classes on `C₀(α, β)` are inherited from their
counterparts on `α →ᵇ β`. Ultimately, when `β` is a C⋆-ring, then so is `C₀(α, β)`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: : Star C₀(α, β) where
  body: { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      zero_at_infty' := by
        simpa only [star_zero] using! (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]

中文:
实例 instStar
  签名: : 对合 C₀(α, β) where
  定义体: { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      zero_at_infty' := by
        simpa only [star_zero] using! (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]

Depends on / 依赖: continuous_star, continuous_star.tendsto, continuous_toFun, map_continuous, star_zero, tendsto, zero_at_infty
-/
instance instStar : Star C₀(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      zero_at_infty' := by
        simpa only [star_zero] using! (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (f : C₀(α, β))
  statement: ⇑(star f) = star (⇑f)
  proof: rfl

中文:
定理 coe_star
  条件: (f : C₀(α, β))
  结论: ⇑(star f) = star (⇑f)
  证明: rfl
-/
theorem coe_star (f : C₀(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: (f : C₀(α, β)) (x : α)
  statement: (star f) x = star (f x)
  proof: rfl

中文:
定理 star_apply
  条件: (f : C₀(α, β)) (x : α)
  结论: (star f) x = star (f x)
  证明: rfl
-/
theorem star_apply (f : C₀(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: [ContinuousAdd β]
  body: ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

中文:
实例 instStarAddMonoid
  签名: [连续加法 β]
  定义体: ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

Depends on / 依赖: star_star
-/
instance instStarAddMonoid [ContinuousAdd β] : StarAddMonoid C₀(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section NormedStar

variable [NormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

/--
Instance `instNormedStarGroup` / 实例 `instNormedStarGroup`

English:
instance instNormedStarGroup
  signature: : NormedStarGroup C₀(α, β) where
  body: (norm_star f.toBCF :).le

中文:
实例 instNormedStarGroup
  签名: : NormedStar群 C₀(α, β) where
  定义体: (norm_star f.toBCF :).le

Depends on / 依赖: f.toBCF, norm_star
-/
instance instNormedStarGroup : NormedStarGroup C₀(α, β) where
  norm_star_le f := (norm_star f.toBCF :).le

end NormedStar

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: : StarModule 𝕜 C₀(α, β) where
  body: ext fun x => star_smul k (f x)

中文:
实例 instStarModule
  签名: : 对合模 𝕜 C₀(α, β) where
  定义体: ext fun x => star_smul k (f x)

Depends on / 依赖: star_smul
-/
instance instStarModule : StarModule 𝕜 C₀(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [IsTopologicalSemiring β]

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: : StarRing C₀(α, β)
  body: { ZeroAtInftyContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

中文:
实例 instStarRing
  签名: : 对合环 C₀(α, β)
  定义体: { ZeroAtInftyContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

Depends on / 依赖: ZeroAtInftyContinuousMap, ZeroAtInftyContinuousMap.instStarAddMonoid, instStarAddMonoid, star_mul
-/
instance instStarRing : StarRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section CStarRing

/--
Instance `instCStarRing` / 实例 `instCStarRing`

English:
instance instCStarRing
  signature: [NonUnitalNormedRing β] [StarRing β] [CStarRing β]
  body: CStarRing.norm_mul_self_le (x := f.toBCF)

中文:
实例 instCStarRing
  签名: [非幺赋范环 β] [对合环 β] [CStar环 β]
  定义体: CStarRing.norm_mul_self_le (x := f.toBCF)

Depends on / 依赖: CStarRing, CStarRing.norm_mul_self_le, f.toBCF, norm_mul_self_le
-/
instance instCStarRing [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C₀(α, β) where
  norm_mul_self_le f := CStarRing.norm_mul_self_le (x := f.toBCF)

end CStarRing

/-! ### C₀ as a functor

For each `β` with sufficient structure, there is a contravariant functor `C₀(-, β)` from the
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
  signature: (f : C₀(γ, δ)) (g : β ->co γ)
  body: (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]

中文:
定义 comp
  签名: (f : C₀(γ, δ)) (g : β ->co γ)
  定义体: (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]
-/
def comp (f : C₀(γ, δ)) (g : β ->co γ) : C₀(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]
/--
theorem `coe_comp_to_continuous_fun` / 定理 `coe_comp_to_continuous_fun`

English:
theorem coe_comp_to_continuous_fun
  given: (f : C₀(γ, δ)) (g : β ->co γ)
  statement: ((f.comp g) : β -> δ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp_to_continuous_fun
  条件: (f : C₀(γ, δ)) (g : β ->co γ)
  结论: ((f.comp g) : β -> δ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β ->co γ) : ((f.comp g) : β -> δ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : C₀(γ, δ))
  statement: f.comp (CocompactMap.id γ) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : C₀(γ, δ))
  结论: f.comp (余compact映射.id γ) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : C₀(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C₀(γ, δ)) (g : β ->co γ) (h : α ->co β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C₀(γ, δ)) (g : β ->co γ) (h : α ->co β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C₀(γ, δ)) (g : β ->co γ) (h : α ->co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (g : β ->co γ)
  statement: (0 : C₀(γ, δ)).comp g = 0
  proof: rfl

中文:
定理 zero_comp
  条件: (g : β ->co γ)
  结论: (0 : C₀(γ, δ)).comp g = 0
  证明: rfl
-/
theorem zero_comp (g : β ->co γ) : (0 : C₀(γ, δ)).comp g = 0 :=
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
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β ->co γ) : C₀(γ, δ) ->+ C₀(β, δ) where
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
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β ->co γ) : C₀(γ, δ) ->ₙ* C₀(β, δ) where
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
    [ContinuousConstSMul R δ] (g : β ->co γ) : C₀(γ, δ) ->ₗ[R] C₀(β, δ) where
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
    C₀(γ, δ) ->ₙₐ[R] C₀(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end ZeroAtInftyContinuousMap
