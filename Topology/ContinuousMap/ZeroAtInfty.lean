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

/-- `C₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C₀(α, β))`,
you should parametrize over `(F : Type*) [ZeroAtInftyContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `ZeroAtInftyContinuousMapClass`. -/
/-
**ZeroAtInftyContinuousMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (β : Type v) → [TopologicalSpace α] → [Zero β] → [Topologic
alSpace β] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity 
from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C₀(α, β))`,
you should parametrize over `(F : Type*) [ZeroAtInftyContinuousMapClass F α β] (
f : F)`.

When you extend this structure, make sure to extend `ZeroAtInftyContinuousMapCla
ss`.
-/
structure ZeroAtInftyContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] : Type max u v extends ContinuousMap α β where
  /-- The function tends to zero along the `cocompact` filter. -/
  zero_at_infty' : Tendsto toFun (cocompact α) (𝓝 0)

@[inherit_doc]
scoped[ZeroAtInfty] notation (priority := 2000) "C₀(" α ", " β ")" => ZeroAtInftyContinuousMap α β

@[inherit_doc]
scoped[ZeroAtInfty] notation α " →C₀ " β => ZeroAtInftyContinuousMap α β

open ZeroAtInfty

section

/-- `ZeroAtInftyContinuousMapClass F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `ZeroAtInftyContinuousMap`. -/
/-
**ZeroAtInftyContinuousMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_2) →   (α : outParam (Type u_3)) →     (β : outParam (Type u_4
)) → [TopologicalSpace α] → [Zero β] → [TopologicalSpace β] → [FunLike F α β] → 
Prop
参数：Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZeroAtInftyContinuousMapClass F α β` states that `F` is a type of continuous ma
ps which
vanish at infinity.

You should also extend this typeclass when you extend `ZeroAtInftyContinuousMap`
.
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

/-
**ZeroAtInftyContinuousMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyCon
tinuousMap`。
形式化陈述：instFunLike : FunLike C₀(α, β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike C₀(α, β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**ZeroAtInftyContinuousMap.instZeroAtInftyContinuousMapClass** 是 Mathlib 中的一个实例，
位于命名空间 `ZeroAtInftyContinuousMap`。
形式化陈述：instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass C₀(α, β)
 α β where map_continuous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `ZeroAtInftyContinuousMap.zero_at_infty'`：∀ {α : Type u} {β : Type v} [in
st : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : TopologicalSpace β]   (self
 : ZeroAtInftyContinuousMap α…
-/
instance instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass C₀(α, β) α β where
  map_continuous f := f.continuous_toFun
  zero_at_infty f := f.zero_at_infty'
/-
**ZeroAtInftyContinuousMap.instCoeTC** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：instCoeTC : CoeTC F C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMapClass.zero_at_infty`：∀ {F : Type u_2} {α : outPa
ram (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {inst_1 : 
Zero β}   {inst_2 : TopologicalSp…
-/
instance instCoeTC : CoeTC F C₀(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_at_infty' := zero_at_infty f }⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAt
InftyContinuousMap`。
形式化陈述：coe_toContinuousMap (f : C₀(α, β)) : (f.toContinuousMap : α -> β) = f
参数：f : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap (f : C₀(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
/-
**ZeroAtInftyContinuousMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinuousM
ap`。
形式化陈述：ext {f g : C₀(α, β)} (h : forall x, f x = g x) : f = g
参数：α, β；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : C₀(α, β)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `ZeroAtInftyContinuo
usMap`。
形式化陈述：coe_mk {f : α -> β} (hf : Continuous f) (hf' : Tendsto f (cocompact α) (𝓝 
0)) : { toFun
参数：hf : Continuous f；hf' : Tendsto f (cocompact α) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk {f : α → β} (hf : Continuous f) (hf' : Tendsto f (cocompact α) (𝓝 0)) :
    { toFun := f,
      continuous_toFun := hf,
      zero_at_infty' := hf' : ZeroAtInftyContinuousMap α β } = f :=
  rfl

/-- Copy of a `ZeroAtInftyContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**ZeroAtInftyContinuousMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInftyContinuous
Map`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : TopologicalSpace α] →       [i
nst_1 : TopologicalSpace β] →         [inst_2 : Zero β] → (f : ZeroAtInftyContin
uousMap α β) → (f' : α → β) → f' = ⇑f → ZeroAtInftyContinuousMap α β
参数：f : ZeroAtInftyContinuousMap α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ZeroAtInftyContinuousMap` with a new `toFun` equal to the old one. Us
eful
to fix definitional equalities.
-/
protected def copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : C₀(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  zero_at_infty' := by
    simp_rw [h]
    exact f.zero_at_infty'

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：coe_copy (f : C₀(α, β)) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : C₀(α, β)；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ZeroAtInftyContinuousMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：copy_eq (f : C₀(α, β)) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : C₀(α, β)；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : C₀(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
/-
**ZeroAtInftyContinuousMap.eq_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyCon
tinuousMap`。
形式化陈述：eq_of_empty [IsEmpty α] (f g : C₀(α, β)) : f = g
参数：f g : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
-/
theorem eq_of_empty [IsEmpty α] (f g : C₀(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. -/
@[simps]
/-
**ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty** 是 Mathlib 中的一个定义，位于命名
空间 `ZeroAtInftyContinuousMap.ContinuousMap`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : TopologicalSpace α] →       [i
nst_1 : TopologicalSpace β] → [inst_2 : Zero β] → [CompactSpace α] → C(α, β) ≃ Z
eroAtInftyContinuousMap α β
参数：α, β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function on a compact space is automatically a continuous function 
vanishing at
infinity.
-/
def ContinuousMap.liftZeroAtInfty [CompactSpace α] : C(α, β) ≃ C₀(α, β) where
  toFun f :=
    { toFun := f
      zero_at_infty' := by simp }
  invFun f := f

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. This is not an instance to avoid type class loops. -/
/-
**ZeroAtInftyContinuousMap.zeroAtInftyContinuousMapClass.ofCompact** 是 Mathlib 中
的一个定理，位于命名空间 `ZeroAtInftyContinuousMap.zeroAtInftyContinuousMapClass`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : Topologi
calSpace β] [inst_2 : Zero β] {G : Type u_2}   [inst_3 : FunLike G α β] [Continu
ousMapClass G α β] [CompactSpace α], ZeroAtInftyContinuousMapClass G α β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cocompact_eq_bot`：Filter.cocompact_eq_bot [CompactSpace X] : Filt
er.cocompact X = ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A continuous function on a compact space is automatically a continuous function 
vanishing at
infinity. This is not an instance to avoid type class loops.
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

/-
**ZeroAtInftyContinuousMap.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：instZero [Zero β] : Zero C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero β] : Zero C₀(α, β) :=
  ⟨⟨0, tendsto_const_nhds⟩⟩
/-
**ZeroAtInftyContinuousMap.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyC
ontinuousMap`。
形式化陈述：instInhabited [Zero β] : Inhabited C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Zero β] : Inhabited C₀(α, β) :=
  ⟨0⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：coe_zero [Zero β] : ⇑(0 : C₀(α, β)) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero [Zero β] : ⇑(0 : C₀(α, β)) = 0 :=
  rfl
/-
**ZeroAtInftyContinuousMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：zero_apply [Zero β] : (0 : C₀(α, β)) x = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [Zero β] : (0 : C₀(α, β)) x = 0 :=
  rfl
/-
**ZeroAtInftyContinuousMap.instMul** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：instMul [MulZeroClass β] [ContinuousMul β] : Mul C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [MulZeroClass β] [ContinuousMul β] : Mul C₀(α, β) :=
  ⟨fun f g =>
    ⟨f * g, by simpa only [mul_zero] using! (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : ⇑(f * g) = f
 * g
参数：f g : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : ⇑(f * g) = f * g :=
  rfl
/-
**ZeroAtInftyContinuousMap.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x 
= f x * g x
参数：f g : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
  rfl
/-
**ZeroAtInftyContinuousMap.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInf
tyContinuousMap`。
形式化陈述：instMulZeroClass [MulZeroClass β] [ContinuousMul β] : MulZeroClass C₀(α, β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass β] [ContinuousMul β] : MulZeroClass C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul
/-
**ZeroAtInftyContinuousMap.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Zero
AtInftyContinuousMap`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero β] [ContinuousMul β] : SemigroupW
ithZero C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C₀(α, β) := fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul
/-
**ZeroAtInftyContinuousMap.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：instAdd [AddZeroClass β] [ContinuousAdd β] : Add C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [AddZeroClass β] [ContinuousAdd β] : Add C₀(α, β) :=
  ⟨fun f g => ⟨f + g, by simpa only [add_zero] using! (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : ⇑(f + g) = f
 + g
参数：f g : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : ⇑(f + g) = f + g :=
  rfl
/-
**ZeroAtInftyContinuousMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x 
= f x + g x
参数：f g : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
  rfl
/-
**ZeroAtInftyContinuousMap.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInf
tyContinuousMap`。
形式化陈述：instAddZeroClass [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C₀(α, β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ coe_zero coe_add
/-
**ZeroAtInftyContinuousMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：instSMul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConst
SMul R β] : SMul R C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMul R C₀(α, β) :=
  ⟨fun r f => ⟨r • f, by simpa [smul_zero] using! (zero_at_infty f).const_smul r⟩⟩

@[simp, norm_cast]
/-
**ZeroAtInftyContinuousMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：coe_smul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConst
SMul R β] (r : R) (f : C₀(α, β)) : ⇑(r • f) = r • ⇑f
参数：r : R；f : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
    (f : C₀(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl
/-
**ZeroAtInftyContinuousMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousCon
stSMul R β] (r : R) (f : C₀(α, β)) (x : α) : (r • f) x = r • f x
参数：r : R；f : C₀(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
    (r : R) (f : C₀(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

variable [AddMonoid β] [ContinuousAdd β] (f g : C₀(α, β))

/-
**ZeroAtInftyContinuousMap.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyC
ontinuousMap`。
形式化陈述：instAddMonoid : AddMonoid C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid : AddMonoid C₀(α, β) := fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

/-
**ZeroAtInftyContinuousMap.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instAddCommMonoid [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C₀(α
, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C₀(α, β) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C₀(α, β))

/-
**ZeroAtInftyContinuousMap.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：instNeg : Neg C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance instNeg : Neg C₀(α, β) :=
  ⟨fun f => ⟨-f, by simpa only [neg_zero] using! (zero_at_infty f).neg⟩⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：coe_neg : ⇑(-f) = -f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(-f) = -f :=
  rfl
/-
**ZeroAtInftyContinuousMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：neg_apply : (-f) x = -f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-f) x = -f x :=
  rfl
/-
**ZeroAtInftyContinuousMap.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：instSub : Sub C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
-/
instance instSub : Sub C₀(α, β) :=
  ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using! (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：coe_sub : ⇑(f - g) = f - g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl
/-
**ZeroAtInftyContinuousMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：sub_apply : (f - g) x = f x - g x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (f - g) x = f x - g x :=
  rfl
/-
**ZeroAtInftyContinuousMap.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyCo
ntinuousMap`。
形式化陈述：instAddGroup : AddGroup C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
instance instAddGroup : AddGroup C₀(α, β) := fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

/-
**ZeroAtInftyContinuousMap.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInf
tyContinuousMap`。
形式化陈述：instAddCommGroup [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup
 C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C₀(α, β) :=
  fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl
/-
**ZeroAtInftyContinuousMap.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAt
InftyContinuousMap`。
形式化陈述：instIsCentralScalar [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMul
WithZero Rᵐᵒᵖ β] [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScal
ar R C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C₀(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
/-
**ZeroAtInftyContinuousMap.instSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInf
tyContinuousMap`。
形式化陈述：instSMulWithZero [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [Continu
ousConstSMul R β] : SMulWithZero R C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C₀(α, β) := fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul
/-
**ZeroAtInftyContinuousMap.instMulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Zero
AtInftyContinuousMap`。
形式化陈述：instMulActionWithZero [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWi
thZero R β] [ContinuousConstSMul R β] : MulActionWithZero R C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionWithZero [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C₀(α, β) := fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul
/-
**ZeroAtInftyContinuousMap.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：instModule [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [M
odule R β] [ContinuousConstSMul R β] : Module R C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C₀(α, β) := fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul
/-
**ZeroAtInftyContinuousMap.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名
空间 `ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [IsTopological
Semiring β] : NonUnitalNonAssocSemiring C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Zero
AtInftyContinuousMap`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring β] [IsTopologicalSemiring β] : No
nUnitalSemiring C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `
ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring β] [IsTopologicalSemiring
 β] : NonUnitalCommSemiring C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `
ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing β] [IsTopologicalRing β] 
: NonUnitalNonAssocRing C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instNonUnitalRing [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing 
C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C₀(α, β) :=
  fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Zero
AtInftyContinuousMap`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing β] [IsTopologicalRing β] : NonUni
talCommRing C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C₀(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl
/-
**ZeroAtInftyContinuousMap.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instIsScalarTower {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β] [
IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R
 β β] : IsScalarTower R C₀(α, β) C₀(α, β) where smul_assoc r f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C₀(α, β) C₀(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]
/-
**ZeroAtInftyContinuousMap.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instSMulCommClass {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β] [
IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R
 β β] : SMulCommClass R C₀(α, β) C₀(α, β) where smul_comm r f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C₀(α, β) C₀(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ]
variable [FunLike F β γ] [ZeroAtInftyContinuousMapClass F β γ]

/-
**ZeroAtInftyContinuousMap.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：uniformContinuous (f : F) : UniformContinuous (f : β -> γ)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.uniformContinuous_of_tendsto_cocompact`：Continuous.uniformCon
tinuous_of_tendsto_cocompact {f : α -> β} {x : β} (h_cont : Continuous f) (hx : 
Tendsto f (cocompact α) (𝓝 x)) : Unifor…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ZeroAtInftyContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α 
: outParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {in
st_1 : Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `ZeroAtInftyContinuousMapClass.zero_at_infty`：∀ {F : Type u_2} {α : outPa
ram (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {inst_1 : 
Zero β}   {inst_2 : TopologicalSp…
-/
theorem uniformContinuous (f : F) : UniformContinuous (f : β → γ) :=
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

/-
**ZeroAtInftyContinuousMap.bounded** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : TopologicalSpace α] [in
st_1 : PseudoMetricSpace β] [inst_2 : Zero β]   [inst_3 : FunLike F α β] [ZeroAt
InftyContinuousMapClass F α β] (f : F), ∃ C, ∀ (x y : α), dist (f x) (f y) ≤ C
参数：f : F；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `ZeroAtInftyContinuousMapClass.zero_at_infty`：∀ {F : Type u_2} {α : outPa
ram (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {inst_1 : 
Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Bornology.IsBounded.subset_closedBall`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α],   Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.clo
sedBall c r
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ZeroAtInftyContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α 
: outParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {in
st_1 : Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.mem_closedBall'`：mem_closedBall' : y in closedBall x ε ↔ dist x y
 <= ε
-/
protected theorem bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C := by
  obtain ⟨K : Set α, hK₁, hK₂⟩ := mem_cocompact.mp
    (tendsto_def.mp (zero_at_infty (f : F)) _ (closedBall_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).isBounded.subset_closedBall (0 : β)
  refine ⟨max C 1 + max C 1, fun x y => ?_⟩
  have : ∀ x, f x ∈ closedBall (0 : β) (max C 1) := by
    intro x
    by_cases hx : x ∈ K
    · exact (mem_closedBall.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closedBall.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closedBall.mp <| this x) (mem_closedBall'.mp <| this y))
/-
**ZeroAtInftyContinuousMap.isBounded_range** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInft
yContinuousMap`。
形式化陈述：isBounded_range (f : C₀(α, β)) : IsBounded (range f)
参数：f : C₀(α, β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `ZeroAtInftyContinuousMap.bounded`：∀ {F : Type u_1} {α : Type u} {β : Typ
e v} [inst : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero β
]   [inst_3 : FunLike …
-/
theorem isBounded_range (f : C₀(α, β)) : IsBounded (range f) :=
  isBounded_range_iff.2 (ZeroAtInftyContinuousMap.bounded f)
/-
**ZeroAtInftyContinuousMap.isBounded_image** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInft
yContinuousMap`。
形式化陈述：isBounded_image (f : C₀(α, β)) (s : Set α) : IsBounded (f '' s)
参数：f : C₀(α, β)；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `ZeroAtInftyContinuousMap.isBounded_range`：isBounded_range (f : C₀(α, β))
 : IsBounded (range f)
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem isBounded_image (f : C₀(α, β)) (s : Set α) : IsBounded (f '' s) :=
  f.isBounded_range.subset <| image_subset_range _ _
/-
**ZeroAtInftyContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinuousMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instBoundedContinuousMapClass : BoundedContinuousMapClass F α β :=
  { ‹ZeroAtInftyContinuousMapClass F α β› with
    map_bounded := fun f => ZeroAtInftyContinuousMap.bounded f }

/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps!]
/-
**ZeroAtInftyContinuousMap.toBCF** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInftyContinuou
sMap`。
形式化陈述：toBCF (f : C₀(α, β)) : α ->ᵇ β
参数：f : C₀(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bounded continuous function from a continuous function vanishing at 
infinity.
-/
def toBCF (f : C₀(α, β)) : α →ᵇ β :=
  ⟨f, map_bounded f⟩

section

variable (α) (β)

/-
**ZeroAtInftyContinuousMap.toBCF_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInft
yContinuousMap`。
形式化陈述：toBCF_injective : Function.Injective (toBCF : C₀(α, β) -> α ->ᵇ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toBCF_injective : Function.Injective (toBCF : C₀(α, β) → α →ᵇ β) := fun f g h => by
  ext x
  simpa only using! DFunLike.congr_fun h x

end

variable {f g : C₀(α, β)}

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `ZeroAtInftyContinuousMap.toBCF`, is a pseudo-metric space. -/
/-
**ZeroAtInftyContinuousMap.instPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Zero
AtInftyContinuousMap`。
形式化陈述：instPseudoMetricSpace : PseudoMetricSpace C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous functions vanishing at infinity, with the uniform distanc
e induced by the
inclusion `ZeroAtInftyContinuousMap.toBCF`, is a pseudo-metric space.
-/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace C₀(α, β) := fast_instance%
  PseudoMetricSpace.induced toBCF inferInstance

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `ZeroAtInftyContinuousMap.toBCF`, is a metric space. -/
/-
**ZeroAtInftyContinuousMap.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInft
yContinuousMap`。
形式化陈述：instMetricSpace {β : Type*} [MetricSpace β] [Zero β] : MetricSpace C₀(α, β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous functions vanishing at infinity, with the uniform distanc
e induced by the
inclusion `ZeroAtInftyContinuousMap.toBCF`, is a metric space.
-/
noncomputable instance instMetricSpace {β : Type*} [MetricSpace β] [Zero β] :
    MetricSpace C₀(α, β) := fast_instance%
  MetricSpace.induced _ (toBCF_injective α β) inferInstance

@[simp]
/-
**ZeroAtInftyContinuousMap.dist_toBCF_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtI
nftyContinuousMap`。
形式化陈述：dist_toBCF_eq_dist {f g : C₀(α, β)} : dist f.toBCF g.toBCF = dist f g
参数：α, β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_toBCF_eq_dist {f g : C₀(α, β)} : dist f.toBCF g.toBCF = dist f g :=
  rfl

open BoundedContinuousFunction

/-- Convergence in the metric on `C₀(α, β)` is uniform convergence. -/
/-
**ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空
间 `ZeroAtInftyContinuousMap`。
形式化陈述：tendsto_iff_tendstoUniformly {ι : Type*} {F : ι -> C₀(α, β)} {f : C₀(α, β)
} {l : Filter ι} : Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l
参数：α, β；α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.tendsto_iff_tendstoUniformly`：tendsto_iff_tend
stoUniformly {ι : Type*} {F : ι -> α ->ᵇ β} {f : α ->ᵇ β} {l : Filter ι} : Tends
to F l (𝓝 f) ↔ TendstoUniformly (fun i => F …

--- 原说明 ---
Convergence in the metric on `C₀(α, β)` is uniform convergence.
-/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → C₀(α, β)} {f : C₀(α, β)} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l := by
  simpa only [Metric.tendsto_nhds] using!
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.toBCF l
/-
**ZeroAtInftyContinuousMap.isometry_toBCF** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInfty
ContinuousMap`。
形式化陈述：isometry_toBCF : Isometry (toBCF : C₀(α, β) -> α ->ᵇ β)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isometry_toBCF : Isometry (toBCF : C₀(α, β) → α →ᵇ β) := by tauto
/-
**ZeroAtInftyContinuousMap.isClosed_range_toBCF** 是 Mathlib 中的一个定理，位于命名空间 `ZeroA
tInftyContinuousMap`。
形式化陈述：isClosed_range_toBCF : IsClosed (range (toBCF : C₀(α, β) -> α ->ᵇ β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `clusterPt_principal_iff`：clusterPt_principal_iff : ClusterPt x (𝓟 s) ↔ f
orall U in 𝓝 x, (U inter s).Nonempty
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZeroAtInftyContinuousMapClass.zero_at_infty`：∀ {F : Type u_2} {α : outPa
ram (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {inst_1 : 
Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `BoundedContinuousFunction.dist_coe_le_dist`：dist_coe_le_dist (x : α) : d
ist (f x) (g x) <= dist f g
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem isClosed_range_toBCF : IsClosed (range (toBCF : C₀(α, β) → α →ᵇ β)) := by
  refine isClosed_iff_clusterPt.mpr fun f hf => ?_
  rw [clusterPt_principal_iff] at hf
  have : Tendsto f (cocompact α) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine (Metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
      (Eventually.of_forall fun x hx => ?_)
    calc
      dist (f x) 0 ≤ dist (g.toBCF x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.toBCF f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
      _ ≤ ε := by grw [mem_ball.1 hg, add_halves ε]
  exact ⟨⟨f.toContinuousMap, this⟩, rfl⟩


/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
/-
**ZeroAtInftyContinuousMap.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instCompleteSpace [CompleteSpace β] : CompleteSpace C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
· 使用定理 `ZeroAtInftyContinuousMap.isometry_toBCF`：isometry_toBCF : Isometry (toBC
F : C₀(α, β) -> α ->ᵇ β)
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `ZeroAtInftyContinuousMap.isClosed_range_toBCF`：isClosed_range_toBCF : Is
Closed (range (toBCF : C₀(α, β) -> α ->ᵇ β))

--- 原说明 ---
Continuous functions vanishing at infinity taking values in a complete space for
m a
complete space.
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

/-
**ZeroAtInftyContinuousMap.instSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 
`ZeroAtInftyContinuousMap`。
形式化陈述：instSeminormedAddCommGroup [SeminormedAddCommGroup β] : SeminormedAddCommG
roup C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
noncomputable instance instSeminormedAddCommGroup [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup C₀(α, β) := fast_instance%
  SeminormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) →+ α →ᵇ β)
/-
**ZeroAtInftyContinuousMap.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Zer
oAtInftyContinuousMap`。
形式化陈述：instNormedAddCommGroup [NormedAddCommGroup β] : NormedAddCommGroup C₀(α, β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedAddCommGroup [NormedAddCommGroup β] :
    NormedAddCommGroup C₀(α, β) := fast_instance%
  NormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C₀(α, β) →+ α →ᵇ β)
    (toBCF_injective α β)

variable [SeminormedAddCommGroup β] {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 β]

@[simp]
/-
**ZeroAtInftyContinuousMap.norm_toBCF_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtI
nftyContinuousMap`。
形式化陈述：norm_toBCF_eq_norm {f : C₀(α, β)} : ‖f.toBCF‖ = ‖f‖
参数：α, β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_toBCF_eq_norm {f : C₀(α, β)} : ‖f.toBCF‖ = ‖f‖ :=
  rfl
/-
**ZeroAtInftyContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContinuousMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedSpace 𝕜 C₀(α, β) where
  norm_smul_le k f := norm_smul_le k f.toBCF

end NormedSpace

section NormedRing

/-
**ZeroAtInftyContinuousMap.instNonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间
 `ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalSeminormedRing [NonUnitalSeminormedRing β] : NonUnitalSeminor
medRing C₀(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
noncomputable instance instNonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing C₀(α, β) :=
  { instNonUnitalRing, instSeminormedAddCommGroup with
    norm_mul_le f g := norm_mul_le f.toBCF g.toBCF }
/-
**ZeroAtInftyContinuousMap.instNonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `Ze
roAtInftyContinuousMap`。
形式化陈述：instNonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing C₀(α
, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNonUnitalNormedRing [NonUnitalNormedRing β] :
    NonUnitalNormedRing C₀(α, β) :=
  { instNonUnitalSeminormedRing, instNormedAddCommGroup with }
/-
**ZeroAtInftyContinuousMap.instNonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于
命名空间 `ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] : NonUnita
lSeminormedCommRing C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing C₀(α, β) :=
  { instNonUnitalSeminormedRing, instNonUnitalCommRing with }
/-
**ZeroAtInftyContinuousMap.instNonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间
 `ZeroAtInftyContinuousMap`。
形式化陈述：instNonUnitalNormedCommRing [NonUnitalNormedCommRing β] : NonUnitalNormedC
ommRing C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**ZeroAtInftyContinuousMap.instStar** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：instStar : Star C₀(α, β) where star f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStar : Star C₀(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      zero_at_infty' := by
        simpa only [star_zero] using! (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContin
uousMap`。
形式化陈述：coe_star (f : C₀(α, β)) : ⇑(star f) = star (⇑f)
参数：f : C₀(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (f : C₀(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl
/-
**ZeroAtInftyContinuousMap.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：star_apply (f : C₀(α, β)) (x : α) : (star f) x = star (f x)
参数：f : C₀(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_apply (f : C₀(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl
/-
**ZeroAtInftyContinuousMap.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtIn
ftyContinuousMap`。
形式化陈述：instStarAddMonoid [ContinuousAdd β] : StarAddMonoid C₀(α, β) where star_in
volutive f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid [ContinuousAdd β] : StarAddMonoid C₀(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section NormedStar

variable [NormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

/-
**ZeroAtInftyContinuousMap.instNormedStarGroup** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAt
InftyContinuousMap`。
形式化陈述：instNormedStarGroup : NormedStarGroup C₀(α, β) where norm_star_le f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
-/
instance instNormedStarGroup : NormedStarGroup C₀(α, β) where
  norm_star_le f := (norm_star f.toBCF :).le

end NormedStar

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

/-
**ZeroAtInftyContinuousMap.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInfty
ContinuousMap`。
形式化陈述：instStarModule : StarModule 𝕜 C₀(α, β) where star_smul k f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
instance instStarModule : StarModule 𝕜 C₀(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [IsTopologicalSemiring β]

/-
**ZeroAtInftyContinuousMap.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyCo
ntinuousMap`。
形式化陈述：instStarRing : StarRing C₀(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing : StarRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section CStarRing

/-
**ZeroAtInftyContinuousMap.instCStarRing** 是 Mathlib 中的一个实例，位于命名空间 `ZeroAtInftyC
ontinuousMap`。
形式化陈述：instCStarRing [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRi
ng C₀(α, β) where norm_mul_self_le f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `CStarRing.norm_mul_self_le`：∀ {E : Type u_4} {inst : NonUnitalNormedRing
 E} {inst_1 : StarRing E} [self : CStarRing E] (x : E),   ‖x‖ * ‖x‖ ≤ ‖star x * 
x‖
-/
instance instCStarRing [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C₀(α, β) where
  norm_mul_self_le f := CStarRing.norm_mul_self_le (x := f.toBCF)

end CStarRing

/-! ### C₀ as a functor

For each `β` with sufficient structure, there is a contravariant functor `C₀(-, β)` from the
category of topological spaces with morphisms given by `CocompactMap`s.
-/


variable {δ : Type*} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

/-- Composition of a continuous function vanishing at infinity with a cocompact map yields another
continuous function vanishing at infinity. -/
/-
**ZeroAtInftyContinuousMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInftyContinuous
Map`。
形式化陈述：comp (f : C₀(γ, δ)) (g : β ->co γ) : C₀(β, δ) where toContinuousMap
参数：f : C₀(γ, δ)；g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a continuous function vanishing at infinity with a cocompact map 
yields another
continuous function vanishing at infinity.
-/
def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]
/-
**ZeroAtInftyContinuousMap.coe_comp_to_continuous_fun** 是 Mathlib 中的一个定理，位于命名空间 
`ZeroAtInftyContinuousMap`。
形式化陈述：coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β ->co γ) : ((f.comp g) : β
 -> δ) = f ∘ g
参数：f : C₀(γ, δ)；g : β ->co γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β →co γ) : ((f.comp g) : β → δ) = f ∘ g :=
  rfl

@[simp]
/-
**ZeroAtInftyContinuousMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyContinu
ousMap`。
形式化陈述：comp_id (f : C₀(γ, δ)) : f.comp (CocompactMap.id γ) = f
参数：f : C₀(γ, δ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMap.ext`：ext {f g : C₀(α, β)} (h : forall x, f x = 
g x) : f = g
-/
theorem comp_id (f : C₀(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
/-
**ZeroAtInftyContinuousMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：comp_assoc (f : C₀(γ, δ)) (g : β ->co γ) (h : α ->co β) : (f.comp g).comp 
h = f.comp (g.comp h)
参数：f : C₀(γ, δ)；g : β ->co γ；h : α ->co β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C₀(γ, δ)) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**ZeroAtInftyContinuousMap.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `ZeroAtInftyConti
nuousMap`。
形式化陈述：zero_comp (g : β ->co γ) : (0 : C₀(γ, δ)).comp g = 0
参数：g : β ->co γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_comp (g : β →co γ) : (0 : C₀(γ, δ)).comp g = 0 :=
  rfl

end

/-- Composition as an additive monoid homomorphism. -/
/-
**ZeroAtInftyContinuousMap.compAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInf
tyContinuousMap`。
形式化陈述：compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β ->co γ) : C₀(γ, δ)
 ->+ C₀(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as an additive monoid homomorphism.
-/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β →co γ) : C₀(γ, δ) →+ C₀(β, δ) where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

/-- Composition as a semigroup homomorphism. -/
/-
**ZeroAtInftyContinuousMap.compMulHom** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInftyCont
inuousMap`。
形式化陈述：compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β ->co γ) : C₀(γ, δ) ->
ₙ* C₀(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a semigroup homomorphism.
-/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β →co γ) : C₀(γ, δ) →ₙ* C₀(β, δ) where
  toFun f := f.comp g
  map_mul' _ _ := rfl

/-- Composition as a linear map. -/
/-
**ZeroAtInftyContinuousMap.compLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAtInftyC
ontinuousMap`。
形式化陈述：compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R]
 [Module R δ] [ContinuousConstSMul R δ] (g : β ->co γ) : C₀(γ, δ) ->ₗ[R] C₀(β, δ
) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a linear map.
-/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β →co γ) : C₀(γ, δ) →ₗ[R] C₀(β, δ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composition as a non-unital algebra homomorphism. -/
/-
**ZeroAtInftyContinuousMap.compNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `ZeroAt
InftyContinuousMap`。
形式化陈述：compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
 [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β ->co γ)
 : C₀(γ, δ) ->ₙₐ[R] C₀(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a non-unital algebra homomorphism.
-/
def compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β →co γ) :
    C₀(γ, δ) →ₙₐ[R] C₀(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end ZeroAtInftyContinuousMap

