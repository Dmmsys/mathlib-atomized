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

/-- `C_c(α, β)` is the type of continuous functions `α → β` with compact support from a topological
space to a topological space with a zero element.

When possible, instead of parametrizing results over `f : C_c(α, β)`,
you should parametrize over `{F : Type*} [CompactlySupportedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `CompactlySupportedContinuousMapClass`. -/
/-
**CompactlySupportedContinuousMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → (β : Type u_6) → [TopologicalSpace α] → [Zero β] → [Topol
ogicalSpace β] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C_c(α, β)` is the type of continuous functions `α → β` with compact support fro
m a topological
space to a topological space with a zero element.

When possible, instead of parametrizing results over `f : C_c(α, β)`,
you should parametrize over `{F : Type*} [CompactlySupportedContinuousMapClass F
 α β] (f : F)`.

When you extend this structure, make sure to extend `CompactlySupportedContinuou
sMapClass`.
-/
structure CompactlySupportedContinuousMap (α β : Type*) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β where
  /-- The function has compact support . -/
  hasCompactSupport' : HasCompactSupport toFun

@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000)
  "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

open CompactlySupported

section

/-- `CompactlySupportedContinuousMapClass F α β` states that `F` is a type of continuous maps with
compact support.

You should also extend this typeclass when you extend `CompactlySupportedContinuousMap`. -/
/-
**CompactlySupportedContinuousMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   (α : outParam (Type u_6)) →     (β : outParam (Type u_7
)) → [TopologicalSpace α] → [Zero β] → [TopologicalSpace β] → [FunLike F α β] → 
Prop
参数：Type u_6；Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CompactlySupportedContinuousMapClass F α β` states that `F` is a type of contin
uous maps with
compact support.

You should also extend this typeclass when you extend `CompactlySupportedContinu
ousMap`.
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

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike C_c(α, β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**CompactlySupportedContinuousMap.hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 `C
ompactlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : Zero β]   (f : CompactlySupportedContinuousMap α β), H
asCompactSupport ⇑f
参数：f : CompactlySupportedContinuousMap α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport'`：∀ {α : Type u_5} {β 
: Type u_6} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : TopologicalS
pace β]   (self : CompactlySupportedCont…
-/
protected lemma hasCompactSupport (f : C_c(α, β)) : HasCompactSupport f := f.hasCompactSupport'
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactlySupportedContinuousMapClass C_c(α, β) α β where
  map_continuous f := f.continuous_toFun
  hasCompactSupport f := f.hasCompactSupport'

@[simp]
/-
**CompactlySupportedContinuousMap.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 
`CompactlySupportedContinuousMap`。
形式化陈述：coe_toContinuousMap (f : C_c(α, β)) : (f.toContinuousMap : α -> β) = f
参数：f : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap (f : C_c(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
/-
**CompactlySupportedContinuousMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySuppor
tedContinuousMap`。
形式化陈述：ext {f g : C_c(α, β)} (h : forall x, f x = g x) : f = g
参数：α, β；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : C_c(α, β)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
/-
**CompactlySupportedContinuousMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySup
portedContinuousMap`。
形式化陈述：coe_mk (f : C(α, β)) (h : HasCompactSupport f) : ⇑(⟨f, h⟩ : C_c(α, β)) = f
参数：f : C(α, β)；h : HasCompactSupport f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : C(α, β)) (h : HasCompactSupport f) : ⇑(⟨f, h⟩ : C_c(α, β)) = f :=
  rfl

/-- Copy of a `CompactlySupportedContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**CompactlySupportedContinuousMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `CompactlySuppo
rtedContinuousMap`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         [inst_2 : Zero β] →           (f : Com
pactlySupportedContinuousMap α β) → (f' : α → β) → f' = ⇑f → CompactlySupportedC
ontinuousMap α β
参数：f : CompactlySupportedContinuousMap α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CompactlySupportedContinuousMap` with a new `toFun` equal to the old 
one. Useful
to fix definitional equalities.
-/
protected def copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : C_c(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

@[simp]
/-
**CompactlySupportedContinuousMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CompactlyS
upportedContinuousMap`。
形式化陈述：coe_copy (f : C_c(α, β)) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : C_c(α, β)；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CompactlySupportedContinuousMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：copy_eq (f : C_c(α, β)) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : C_c(α, β)；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : C_c(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
/-
**CompactlySupportedContinuousMap.eq_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Compact
lySupportedContinuousMap`。
形式化陈述：eq_of_empty [IsEmpty α] (f g : C_c(α, β)) : f = g
参数：f g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
-/
theorem eq_of_empty [IsEmpty α] (f g : C_c(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

/-- A continuous function on a compact space automatically has compact support. -/
@[simps]
/-
**CompactlySupportedContinuousMap.continuousMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CompactlySupportedContinuousMap`。
形式化陈述：continuousMapEquiv [CompactSpace α] : C(α, β) ≃ C_c(α, β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function on a compact space automatically has compact support.
-/
def continuousMapEquiv [CompactSpace α] : C(α, β) ≃ C_c(α, β) where
  toFun f :=
    { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  invFun f := f

variable {γ : Type*} [TopologicalSpace γ] [Zero γ]

/-- Composition of a continuous function `f` with compact support with another continuous function
`g` sending `0` to `0` from the left yields another continuous function `g ∘ f` with compact
support.

If `g` doesn't send `0` to `0`, `f.compLeft g` defaults to `0`. -/
/-
**CompactlySupportedContinuousMap.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `CompactlyS
upportedContinuousMap`。
形式化陈述：compLeft (g : C(β, γ)) (f : C_c(α, β)) : C_c(α, γ) where toContinuousMap
参数：g : C(β, γ)；f : C_c(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a continuous function `f` with compact support with another conti
nuous function
`g` sending `0` to `0` from the left yields another continuous function `g ∘ f` 
with compact
support.

If `g` doesn't send `0` to `0`, `f.compLeft g` defaults to `0`.
-/
noncomputable def compLeft (g : C(β, γ)) (f : C_c(α, β)) : C_c(α, γ) where
  toContinuousMap := by classical exact if g 0 = 0 then g.comp f else 0
  hasCompactSupport' := by
    split_ifs with hg
    · exact f.hasCompactSupport'.comp_left hg
    · exact .zero
/-
**CompactlySupportedContinuousMap.toContinuousMap_compLeft** 是 Mathlib 中的一个引理，位于
命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：toContinuousMap_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) : (f
.compLeft g).toContinuousMap = g.comp f
参数：β, γ；hg : g 0 = 0；f : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma toContinuousMap_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) :
    (f.compLeft g).toContinuousMap = g.comp f := if_pos hg
/-
**CompactlySupportedContinuousMap.coe_compLeft** 是 Mathlib 中的一个引理，位于命名空间 `Compac
tlySupportedContinuousMap`。
形式化陈述：coe_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) : f.compLeft g =
 g ∘ f
参数：β, γ；hg : g 0 = 0；f : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CompactlySupportedContinuousMap.mk.congr_simp`：∀ {α : Type u_5} {β : Typ
e u_6} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : TopologicalSpace 
β]   (toContinuousMap toContinuousM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) : f.compLeft g = g ∘ f := by
  simp [compLeft, if_pos hg]
/-
**CompactlySupportedContinuousMap.compLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：compLeft_apply {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α) : f.co
mpLeft g a = g (f a)
参数：β, γ；hg : g 0 = 0；f : C_c(α, β)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CompactlySupportedContinuousMap.coe_compLeft`：coe_compLeft {g : C(β, γ)}
 (hg : g 0 = 0) (f : C_c(α, β)) : f.compLeft g = g ∘ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compLeft_apply {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α) :
    f.compLeft g a = g (f a) := by simp [coe_compLeft hg f]

/-- A compactly supported continuous function gives rise to a bounded continuous function. -/
/-
**CompactlySupportedContinuousMap.toBoundedContinuousFunction** 是 Mathlib 中的一个定义
，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：{α : Type u_2} →   [inst : TopologicalSpace α] →     {β : Type u_6} →     
  [inst_1 : PseudoMetricSpace β] →         [inst_2 : Zero β] → CompactlySupporte
dContinuousMap α β → BoundedContinuousFunction α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compactly supported continuous function gives rise to a bounded continuous fun
ction.
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

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] : Zero C_c(α, β) where
  zero := { toFun := (0 : C(α, β))
            continuous_toFun := (0 : C(α, β)).2
            hasCompactSupport' := by simp [HasCompactSupport, tsupport] }
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] : Inhabited C_c(α, β) :=
  ⟨0⟩

@[simp]
/-
**CompactlySupportedContinuousMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `CompactlyS
upportedContinuousMap`。
形式化陈述：coe_zero [Zero β] : ⇑(0 : C_c(α, β)) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero [Zero β] : ⇑(0 : C_c(α, β)) = 0 :=
  rfl
/-
**CompactlySupportedContinuousMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：zero_apply [Zero β] : (0 : C_c(α, β)) x = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [Zero β] : (0 : C_c(α, β)) x = 0 :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass β] [ContinuousMul β] : Mul C_c(α, β) :=
  ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]
/-
**CompactlySupportedContinuousMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = 
f * g
参数：f g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = f * g :=
  rfl
/-
**CompactlySupportedContinuousMap.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x
 = f x * g x
参数：f g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
  rfl

/-- the product of `f : F` assuming `ContinuousMapClass F α γ` and `ContinuousSMul γ β` and
`g : C_c(α, β)` is in `C_c(α, β)` -/
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the product of `f : F` assuming `ContinuousMapClass F α γ` and `ContinuousSMul γ
 β` and
`g : C_c(α, β)` is in `C_c(α, β)`
-/
instance [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] : SMul F C_c(α, β) where
  smul f g :=
    ⟨⟨fun x ↦ f x • g x, (map_continuous f).smul (map_continuous g)⟩, g.hasCompactSupport.smul_left⟩

@[simp]
/-
**CompactlySupportedContinuousMap.coe_smulc** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：coe_smulc [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMu
l γ β] {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α
, β)) : ⇑(f • g) = fun x => f x • g x
参数：f : F；g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smulc [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) :
    ⇑(f • g) = fun x => f x • g x :=
  rfl
/-
**CompactlySupportedContinuousMap.smulc_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compact
lySupportedContinuousMap`。
形式化陈述：smulc_apply [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousS
Mul γ β] {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c
(α, β)) (x : α) : (f • g) x = f x • g x
参数：f : F；g : C_c(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulc_apply [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) (x : α) :
    (f • g) x = f x • g x :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass β] [ContinuousAdd β] : Add C_c(α, β) :=
  ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]
/-
**CompactlySupportedContinuousMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : ⇑(f + g) = 
f + g
参数：f g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : ⇑(f + g) = f + g :=
  rfl
/-
**CompactlySupportedContinuousMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x
 = f x + g x
参数：f g : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/-- Coercion to a function as a `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/
/-
**CompactlySupportedContinuousMap.coeFnMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：coeFnMonoidHom [AddMonoid β] [ContinuousAdd β] : C_c(α, β) ->+ α -> β wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as a `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`.
-/
def coeFnMonoidHom [AddMonoid β] [ContinuousAdd β] : C_c(α, β) →+ α → β where
  toFun f := f
  map_zero' := coe_zero
  map_add' := coe_add
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] :
    SMul R C_c(α, β) := fast_instance%
  ⟨fun r f => ⟨⟨r • ⇑f, (map_continuous f).const_smul r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]
/-
**CompactlySupportedContinuousMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `CompactlyS
upportedContinuousMap`。
形式化陈述：coe_smul [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β
] (r : R) (f : C_c(α, β)) : ⇑(r • f) = r • ⇑f
参数：r : R；f : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl
/-
**CompactlySupportedContinuousMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R
 β] (r : R) (f : C_c(α, β)) (x : α) : (r • f) x = r • f x
参数：r : R；f : C_c(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid β] [ContinuousAdd β] : AddMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

@[simp]
/-
**CompactlySupportedContinuousMap.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：coe_sum [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f 
: ι -> C_c(α, β)) : ⇑(∑ i in s, f i) = ∑ i in s, (f i : α -> β)
参数：s : Finset ι；f : ι -> C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coe_sum [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι → C_c(α, β)) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : α → β) :=
  map_sum coeFnMonoidHom f s
/-
**CompactlySupportedContinuousMap.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：sum_apply [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (
f : ι -> C_c(α, β)) (a : α) : (∑ i in s, f i) a = ∑ i in s, f i a
参数：s : Finset ι；f : ι -> C_c(α, β)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CompactlySupportedContinuousMap.coe_sum`：coe_sum [AddCommMonoid β] [Cont
inuousAdd β] {ι : Type*} (s : Finset ι) (f : ι -> C_c(α, β)) : ⇑(∑ i in s, f i) 
= ∑ i in s, (f i : α -> β)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_apply [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι → C_c(α, β))
    (a : α) : (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by simp

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C_c(α, β))

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg C_c(α, β) where
  neg f := { toFun := -f.1
             continuous_toFun := map_continuous (-f.1)
             hasCompactSupport' := by simpa [HasCompactSupport, tsupport] using f.2 }

@[simp]
/-
**CompactlySupportedContinuousMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：coe_neg : ⇑(-f) = -f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(-f) = -f :=
  rfl
/-
**CompactlySupportedContinuousMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：neg_apply : (-f) x = -f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-f) x = -f x :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub C_c(α, β) where
  sub f g := { toFun := f.1 - g.1
               continuous_toFun := map_continuous (f.1 - g.1)
               hasCompactSupport' := by
                 simpa [sub_eq_add_neg] using HasCompactSupport.add f.2 (-g).2 }

@[simp]
/-
**CompactlySupportedContinuousMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：coe_sub : ⇑(f - g) = f - g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl
/-
**CompactlySupportedContinuousMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：sub_apply : (f - g) x = f x - g x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (f - g) x = f x - g x :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C_c(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C_c(α, β) := fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C_c(α, β) := fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C_c(α, β) := fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C_c(α, β) C_c(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C_c(α, β) C_c(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

section Star

/-! ### Star structure

It is possible to equip `C_c(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`StarAddMonoid` is close enough.

The `StarAddMonoid` class on `C_c(α, β)` is inherited from their counterparts on `α →ᵇ β`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star C_c(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      hasCompactSupport' := by
        rw [HasCompactSupport, tsupport]
        have support_star : (Function.support fun (x : α) => star (f x)) = Function.support f := by
          ext x
          simp only [Function.mem_support, ne_eq, star_eq_zero]
        rw [support_star]
        exact f.2 }

@[simp]
/-
**CompactlySupportedContinuousMap.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `CompactlyS
upportedContinuousMap`。
形式化陈述：coe_star (f : C_c(α, β)) : ⇑(star f) = star (⇑f)
参数：f : C_c(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (f : C_c(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl
/-
**CompactlySupportedContinuousMap.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：star_apply (f : C_c(α, β)) (x : α) : (star f) x = star (f x)
参数：f : C_c(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_apply (f : C_c(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TrivialStar β] : TrivialStar C_c(α, β) where
    star_trivial f := ext fun x => star_trivial (f x)
/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousAdd β] : StarAddMonoid C_c(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule 𝕜 C_c(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [IsTopologicalSemiring β]

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**CompactlySupportedContinuousMap.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Compac
tlySupportedContinuousMap`。
形式化陈述：partialOrder : PartialOrder C_c(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder C_c(α, β) :=
  fast_instance% PartialOrder.lift (⇑) DFunLike.coe_injective
/-
**CompactlySupportedContinuousMap.le_def** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySup
portedContinuousMap`。
形式化陈述：le_def {f g : C_c(α, β)} : f <= g ↔ forall a, f a <= g a
参数：α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.le_def`：Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {
x y : forall i, π i} : x <= y ↔ forall i, x i <= y i
-/
theorem le_def {f g : C_c(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a := Pi.le_def
/-
**CompactlySupportedContinuousMap.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySup
portedContinuousMap`。
形式化陈述：lt_def {f g : C_c(α, β)} : f < g ↔ (forall a, f a <= g a) ∧ exists a, f a 
< g a
参数：α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
theorem lt_def {f g : C_c(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a := Pi.lt_def

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup β] [Zero β] [TopologicalSpace β] [ContinuousSup β]

/-
**CompactlySupportedContinuousMap.instSup** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：instSup : Max C_c(α, β) where max f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup : Max C_c(α, β) where max f g :=
  { toFun := f ⊔ g
    continuous_toFun := Continuous.sup f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.sup g.hasCompactSupport }
/-
**CompactlySupportedContinuousMap.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeSup β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousSup β] (f g : CompactlySupportedContinuousMap α β),   ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : CompactlySupportedContinuousMap α β；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (f g : C_c(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl
/-
**CompactlySupportedContinuousMap.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeSup β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousSup β] (f g : CompactlySupportedContinuousMap α β) (a : α),   (f ⊔ g) a = f 
a ⊔ g a
参数：f g : CompactlySupportedContinuousMap α β；a : α；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sup_apply (f g : C_c(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
/-
**CompactlySupportedContinuousMap.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：semilatticeSup : SemilatticeSup C_c(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup : SemilatticeSup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup
/-
**CompactlySupportedContinuousMap.finsetSup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeSup β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousSup β] {ι : Type u_5} {s : Finset ι} (H : s.Nonempty)   (f : ι → CompactlySu
pportedContinuousMap α β) (a : α), (s.sup' H f) a = s.sup' H fun i => (f i) a
参数：H : s.Nonempty；f : ι → CompactlySupportedContinuousMap α β；a : α；s.sup' H f；f
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
lemma finsetSup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i ↦ f i a :=
  Finset.apply_sup'_eq_sup'_comp H (fun g : C_c(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
/-
**CompactlySupportedContinuousMap.coe_finsetSup'** 是 Mathlib 中的一个引理，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：coe_finsetSup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α
, β)) : ⇑(s.sup' H f) = s.sup' H fun i => ⇑(f i)
参数：H : s.Nonempty；f : ι -> C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.finsetSup'_apply`：∀ {α : Type u_2} {β : 
Type u_3} [inst : TopologicalSpace α] [inst_1 : SemilatticeSup β] [inst_2 : Zero
 β]   [inst_3 : TopologicalSpace β] [i…
· 使用定理 `Finset.sup'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeSup (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_finsetSup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i ↦ ⇑(f i) := by ext; simp [finsetSup'_apply]

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [Zero β] [TopologicalSpace β] [ContinuousInf β]

/-
**CompactlySupportedContinuousMap.instInf** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：instInf : Min C_c(α, β) where min f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min C_c(α, β) where min f g :=
  { toFun := f ⊓ g
    continuous_toFun := Continuous.inf f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.inf g.hasCompactSupport }
/-
**CompactlySupportedContinuousMap.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeInf β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousInf β] (f g : CompactlySupportedContinuousMap α β),   ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
参数：f g : CompactlySupportedContinuousMap α β；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (f g : C_c(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl
/-
**CompactlySupportedContinuousMap.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeInf β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousInf β] (f g : CompactlySupportedContinuousMap α β) (a : α),   (f ⊓ g) a = f 
a ⊓ g a
参数：f g : CompactlySupportedContinuousMap α β；a : α；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inf_apply (f g : C_c(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl
/-
**CompactlySupportedContinuousMap.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：semilatticeInf : SemilatticeInf C_c(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf : SemilatticeInf C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf
/-
**CompactlySupportedContinuousMap.finsetInf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Semi
latticeInf β] [inst_2 : Zero β]   [inst_3 : TopologicalSpace β] [inst_4 : Contin
uousInf β] {ι : Type u_5} {s : Finset ι} (H : s.Nonempty)   (f : ι → CompactlySu
pportedContinuousMap α β) (a : α), (s.inf' H f) a = s.inf' H fun i => (f i) a
参数：H : s.Nonempty；f : ι → CompactlySupportedContinuousMap α β；a : α；s.inf' H f；f
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_inf'_eq_inf'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
lemma finsetInf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i ↦ f i a :=
  Finset.apply_inf'_eq_inf'_comp H (fun g : C_c(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
/-
**CompactlySupportedContinuousMap.coe_finsetInf'** 是 Mathlib 中的一个引理，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：coe_finsetInf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C_c(α
, β)) : ⇑(s.inf' H f) = s.inf' H fun i => ⇑(f i)
参数：H : s.Nonempty；f : ι -> C_c(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.finsetInf'_apply`：∀ {α : Type u_2} {β : 
Type u_3} [inst : TopologicalSpace α] [inst_1 : SemilatticeInf β] [inst_2 : Zero
 β]   [inst_3 : TopologicalSpace β] [i…
· 使用定理 `Finset.inf'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeInf (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_finsetInf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i ↦ ⇑(f i) := by ext; simp [finsetInf'_apply]

end SemilatticeInf

section Lattice

variable [TopologicalSpace β]

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice β] [TopologicalLattice β] [Zero β] : Lattice C_c(α, β) where
/-
**CompactlySupportedContinuousMap.instMulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Com
pactlySupportedContinuousMap`。
形式化陈述：instMulLeftMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulLe
ftMono β] : MulLeftMono C_c(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
instance instMulLeftMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulLeftMono β] :
    MulLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_right (hg₁₂ x) _⟩
/-
**CompactlySupportedContinuousMap.instMulRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：instMulRightMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulR
ightMono β] : MulRightMono C_c(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
instance instMulRightMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulRightMono β] :
    MulRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_left (hg₁₂ x) _⟩
/-
**CompactlySupportedContinuousMap.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Com
pactlySupportedContinuousMap`。
形式化陈述：instAddLeftMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddLe
ftMono β] : AddLeftMono C_c(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
instance instAddLeftMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddLeftMono β] :
    AddLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_right (hg₁₂ x) _⟩
/-
**CompactlySupportedContinuousMap.instAddRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：instAddRightMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddR
ightMono β] : AddRightMono C_c(α, β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
instance instAddRightMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddRightMono β] :
    AddRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_left (hg₁₂ x) _⟩

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

end Lattice

section IsOrderedAddMonoid

variable [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
variable [PartialOrder β] [IsOrderedAddMonoid β]

/-
**CompactlySupportedContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupported
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid C_c(α, β) where
  add_le_add_left _ _ hfg c := add_le_add_left hfg c

end IsOrderedAddMonoid

/-! ### `C_c` as a functor

For each `β` with sufficient structure, there is a contravariant functor `C_c(-, β)` from the
category of topological spaces with morphisms given by `CocompactMap`s.
-/


variable {δ : Type*} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

/-- Composition of a continuous function with compact support with a cocompact map
yields another continuous function with compact support. -/
/-
**CompactlySupportedContinuousMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `CompactlySuppo
rtedContinuousMap`。
形式化陈述：comp (f : C_c(γ, δ)) (g : β ->co γ) : C_c(β, δ) where toContinuousMap
参数：f : C_c(γ, δ)；g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a continuous function with compact support with a cocompact map
yields another continuous function with compact support.
-/
def comp (f : C_c(γ, δ)) (g : β →co γ) : C_c(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  hasCompactSupport' := by
    apply IsCompact.of_isClosed_subset (g.isCompact_preimage_of_isClosed f.2 (isClosed_tsupport _))
      (isClosed_tsupport (f ∘ g))
    intro x hx
    rw [tsupport, Set.mem_preimage, _root_.mem_closure_iff]
    intro o ho hgxo
    rw [tsupport, _root_.mem_closure_iff] at hx
    obtain ⟨y, hy⟩ := hx (g ⁻¹' o) (IsOpen.preimage g.1.2 ho) hgxo
    exact ⟨g y, hy⟩

@[simp]
/-
**CompactlySupportedContinuousMap.coe_comp_to_continuous_fun** 是 Mathlib 中的一个定理，
位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：coe_comp_to_continuous_fun (f : C_c(γ, δ)) (g : β ->co γ) : ((f.comp g) : 
β -> δ) = f ∘ g
参数：f : C_c(γ, δ)；g : β ->co γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_to_continuous_fun (f : C_c(γ, δ)) (g : β →co γ) : ((f.comp g) : β → δ) = f ∘ g :=
  rfl

@[simp]
/-
**CompactlySupportedContinuousMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CompactlySu
pportedContinuousMap`。
形式化陈述：comp_id (f : C_c(γ, δ)) : f.comp (CocompactMap.id γ) = f
参数：f : C_c(γ, δ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
-/
theorem comp_id (f : C_c(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
/-
**CompactlySupportedContinuousMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：comp_assoc (f : C_c(γ, δ)) (g : β ->co γ) (h : α ->co β) : (f.comp g).comp
 h = f.comp (g.comp h)
参数：f : C_c(γ, δ)；g : β ->co γ；h : α ->co β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C_c(γ, δ)) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**CompactlySupportedContinuousMap.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `Compactly
SupportedContinuousMap`。
形式化陈述：zero_comp (g : β ->co γ) : (0 : C_c(γ, δ)).comp g = 0
参数：g : β ->co γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_comp (g : β →co γ) : (0 : C_c(γ, δ)).comp g = 0 :=
  rfl

end

/-- Composition as an additive monoid homomorphism. -/
/-
**CompactlySupportedContinuousMap.compAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β ->co γ) : C_c(γ, δ
) ->+ C_c(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as an additive monoid homomorphism.
-/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β →co γ) : C_c(γ, δ) →+ C_c(β, δ) where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

/-- Composition as a semigroup homomorphism. -/
/-
**CompactlySupportedContinuousMap.compMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β ->co γ) : C_c(γ, δ) -
>ₙ* C_c(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a semigroup homomorphism.
-/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β →co γ) : C_c(γ, δ) →ₙ* C_c(β, δ) where
  toFun f := f.comp g
  map_mul' _ _ := rfl

/-- Composition as a linear map. -/
/-
**CompactlySupportedContinuousMap.compLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Compa
ctlySupportedContinuousMap`。
形式化陈述：compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R]
 [Module R δ] [ContinuousConstSMul R δ] (g : β ->co γ) : C_c(γ, δ) ->ₗ[R] C_c(β,
 δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a linear map.
-/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β →co γ) : C_c(γ, δ) →ₗ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composition as a non-unital algebra homomorphism. -/
/-
**CompactlySupportedContinuousMap.compNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 
`CompactlySupportedContinuousMap`。
形式化陈述：compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
 [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β ->co γ)
 : C_c(γ, δ) ->ₙₐ[R] C_c(β, δ) where toFun f
参数：g : β ->co γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a non-unital algebra homomorphism.
-/
def compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β →co γ) :
    C_c(γ, δ) →ₙₐ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end CompactlySupportedContinuousMap

namespace CompactlySupportedContinuousMapClass

section Basic

variable [Zero β] [TopologicalSpace β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

/-
**CompactlySupportedContinuousMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupp
ortedContinuousMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC F (CompactlySupportedContinuousMap α β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      hasCompactSupport' := hasCompactSupport f }⟩

/-- A continuous function on a compact space has automatically compact support. This is not an
/-
**CompactlySupportedContinuousMapClass.to** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySu
pportedContinuousMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance to avoid type class loops. -/
/-
**CompactlySupportedContinuousMapClass.of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间
 `CompactlySupportedContinuousMapClass`。
形式化陈述：of_compactSpace (G : Type*) [FunLike G α β] [ContinuousMapClass G α β] [Co
mpactSpace α] : CompactlySupportedContinuousMapClass G α β where map_continuous
参数：G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.of_compactSpace`：∀ {α : Type u_2} {γ : Type u_5} [inst
 : TopologicalSpace α] [inst_1 : Zero γ] [CompactSpace α] (f : α → γ),   HasComp
actSupport f

--- 原说明 ---
A continuous function on a compact space has automatically compact support. This
 is not an
instance to avoid type class loops.
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

/-
**CompactlySupportedContinuousMapClass.uniformContinuous** 是 Mathlib 中的一个定理，位于命名
空间 `CompactlySupportedContinuousMapClass`。
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
· 使用定理 `CompactlySupportedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u
_5} {α : outParam (Type u_6)} {β : outParam (Type u_7)} {inst : TopologicalSpace
 α} {inst_1 : Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `HasCompactSupport.is_zero_at_infty`：∀ {α : Type u_2} {γ : Type u_5} [ins
t : TopologicalSpace α] [inst_1 : Zero γ] {f : α → γ} [inst_2 : TopologicalSpace
 γ],   HasCompactSupport…
· 使用定理 `CompactlySupportedContinuousMapClass.hasCompactSupport`：∀ {F : Type u_5}
 {α : outParam (Type u_6)} {β : outParam (Type u_7)} {inst : TopologicalSpace α}
 {inst_1 : Zero β}   {inst_2 : TopologicalSp…
-/
theorem uniformContinuous (f : F) : UniformContinuous (f : β → γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact
  (HasCompactSupport.is_zero_at_infty (hasCompactSupport f))

end Uniform

section ZeroAtInfty

variable [TopologicalSpace β] [TopologicalSpace γ] [Zero γ]
  [FunLike F β γ] [CompactlySupportedContinuousMapClass F β γ]

/-
**CompactlySupportedContinuousMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `CompactlySupp
ortedContinuousMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ZeroAtInftyContinuousMapClass F β γ where
  zero_at_infty f := HasCompactSupport.is_zero_at_infty (hasCompactSupport f)

end ZeroAtInfty

end CompactlySupportedContinuousMapClass

section NonnegativePart

open NNReal

namespace CompactlySupportedContinuousMap

set_option backward.isDefEq.respectTransparency.types false in
/-
**CompactlySupportedContinuousMap.exists_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {f₁ f₂ : CompactlySupportedCo
ntinuousMap α NNReal},   f₁ ≤ f₂ → ∃ g, f₁ + g = f₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousSub`：ContinuousSub NNReal
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport'`：∀ {α : Type u_5} {β 
: Type u_6} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : TopologicalS
pace β]   (self : CompactlySupportedCont…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1 :
 TopologicalSpace X] (f : X → α),   tsupport f = closure (Function.support f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
-/
protected lemma exists_add_of_le {f₁ f₂ : C_c(α, ℝ≥0)} (h : f₁ ≤ f₂) : ∃ (g : C_c(α, ℝ≥0)),
    f₁ + g = f₂ := by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport, tsupport, ← closure_union]
    apply closure_mono
    intro x hx
    contrapose hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)

/-- The nonnegative part of a continuous compactly supported `ℝ`-valued function as a
continuous compactly supported `ℝ≥0`-valued function. -/
/-
**CompactlySupportedContinuousMap.nnrealPart** 是 Mathlib 中的一个定义，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：nnrealPart (f : C_c(α, Real)) : C_c(α, Real>=0) where toFun
参数：f : C_c(α, Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nonnegative part of a continuous compactly supported `ℝ`-valued function as 
a
continuous compactly supported `ℝ≥0`-valued function.
-/
noncomputable def nnrealPart (f : C_c(α, ℝ)) : C_c(α, ℝ≥0) where
  toFun := Real.toNNReal.comp f.toFun
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' Real.toNNReal_zero

@[simp]
/-
**CompactlySupportedContinuousMap.nnrealPart_apply** 是 Mathlib 中的一个引理，位于命名空间 `Co
mpactlySupportedContinuousMap`。
形式化陈述：nnrealPart_apply (f : C_c(α, Real)) (x : α) : f.nnrealPart x = Real.toNNRe
al (f x)
参数：f : C_c(α, Real)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnrealPart_apply (f : C_c(α, ℝ)) (x : α) :
    f.nnrealPart x = Real.toNNReal (f x) := rfl
/-
**CompactlySupportedContinuousMap.nnrealPart_neg_eq_zero_of_nonneg** 是 Mathlib 中
的一个引理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_neg_eq_zero_of_nonneg {f : C_c(α, Real)} (hf : 0 <= f) : (-f).n
nrealPart = 0
参数：α, Real；hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma nnrealPart_neg_eq_zero_of_nonneg {f : C_c(α, ℝ)} (hf : 0 ≤ f) : (-f).nnrealPart = 0 := by
  ext x
  simpa using hf x
/-
**CompactlySupportedContinuousMap.nnrealPart_smul_pos** 是 Mathlib 中的一个引理，位于命名空间 
`CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_smul_pos (f : C_c(α, Real)) {a : Real} (ha : 0 <= a) : (a • f).
nnrealPart = a.toNNReal • f.nnrealPart
参数：f : C_c(α, Real)；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma nnrealPart_smul_pos (f : C_c(α, ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    (a • f).nnrealPart = a.toNNReal • f.nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, Real.coe_toNNReal', smul_eq_mul,
    NNReal.coe_mul, ha, sup_of_le_left]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [ha, hfx, mul_nonneg]
  · simp [mul_nonpos_iff, ha, hfx]
/-
**CompactlySupportedContinuousMap.nnrealPart_smul_neg** 是 Mathlib 中的一个引理，位于命名空间 
`CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_smul_neg (f : C_c(α, Real)) {a : Real} (ha : a <= 0) : (a • f).
nnrealPart = (-a).toNNReal • (-f).nnrealPart
参数：f : C_c(α, Real)；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 38 条，此处仅展示前 30 条）
-/
lemma nnrealPart_smul_neg (f : C_c(α, ℝ)) {a : ℝ} (ha : a ≤ 0) :
    (a • f).nnrealPart = (-a).toNNReal • (-f).nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal', coe_neg,
    Pi.neg_apply, NNReal.coe_mul]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [mul_nonpos_iff, ha, hfx]
  · simp [ha, hfx, mul_nonneg_of_nonpos_of_nonpos]
/-
**CompactlySupportedContinuousMap.nnrealPart_add_le_add_nnrealPart** 是 Mathlib 中
的一个引理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_add_le_add_nnrealPart (f g : C_c(α, Real)) : (f + g).nnrealPart
 <= f.nnrealPart + g.nnrealPart
参数：f g : C_c(α, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Real.toNNReal_add_le`：toNNReal_add_le {r p : Real} : Real.toNNReal (r + 
p) <= Real.toNNReal r + Real.toNNReal p
-/
lemma nnrealPart_add_le_add_nnrealPart (f g : C_c(α, ℝ)) :
    (f + g).nnrealPart ≤ f.nnrealPart + g.nnrealPart := by
  intro x
  simpa using Real.toNNReal_add_le
/-
**CompactlySupportedContinuousMap.exists_add_nnrealPart_add_eq** 是 Mathlib 中的一个引
理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：exists_add_nnrealPart_add_eq (f g : C_c(α, Real)) : exists (h : C_c(α, Rea
l>=0)), (f + g).nnrealPart + h = f.nnrealPart + g.nnrealPart ∧ (-f + -g).nnrealP
art + h = (-f).nnrealPart + (-g).nnrealPart
参数：f g : C_c(α, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `CompactlySupportedContinuousMap.exists_add_of_le`：∀ {α : Type u_2} [inst
 : TopologicalSpace α] {f₁ f₂ : CompactlySupportedContinuousMap α NNReal},   f₁ 
≤ f₂ → ∃ g, f₁ + g = f₂
· 使用引理 `CompactlySupportedContinuousMap.nnrealPart_add_le_add_nnrealPart`：nnreal
Part_add_le_add_nnrealPart (f g : C_c(α, Real)) : (f + g).nnrealPart <= f.nnreal
Part + g.nnrealPart
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_neg_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] [AddLeftMono α] (a : α), max (-a) 0 = -a + max a 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 50 条，此处仅展示前 30 条）
-/
lemma exists_add_nnrealPart_add_eq (f g : C_c(α, ℝ)) : ∃ (h : C_c(α, ℝ≥0)),
    (f + g).nnrealPart + h = f.nnrealPart + g.nnrealPart ∧
    (-f + -g).nnrealPart + h = (-f).nnrealPart + (-g).nnrealPart := by
  obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le
    (nnrealPart_add_le_add_nnrealPart f g)
  use h
  refine ⟨hh, ?_⟩
  ext x
  have hhx := congr(($hh x : ℝ))
  simp only [coe_add, Pi.add_apply, nnrealPart_apply, coe_neg, Pi.neg_apply, NNReal.coe_add,
    Real.coe_toNNReal', ← neg_add, max_neg_zero] at hhx ⊢
  linear_combination hhx

/-- The compactly supported continuous `ℝ≥0`-valued function as a compactly supported `ℝ`-valued
function. -/
/-
**CompactlySupportedContinuousMap.toReal** 是 Mathlib 中的一个定义，位于命名空间 `CompactlySup
portedContinuousMap`。
形式化陈述：toReal (f : C_c(α, Real>=0)) : C_c(α, Real)
参数：f : C_c(α, Real>=0)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compactly supported continuous `ℝ≥0`-valued function as a compactly supporte
d `ℝ`-valued
function.
-/
noncomputable def toReal (f : C_c(α, ℝ≥0)) : C_c(α, ℝ) :=
  f.compLeft ContinuousMap.coeNNRealReal
/-
**CompactlySupportedContinuousMap.toReal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Compac
tlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (f : CompactlySupportedContin
uousMap α NNReal) (x : α), f.toReal x = ↑(f x)
参数：f : CompactlySupportedContinuousMap α NNReal；x : α；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CompactlySupportedContinuousMap.compLeft_apply`：compLeft_apply {g : C(β,
 γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α) : f.compLeft g a = g (f a)
-/
@[simp] lemma toReal_apply (f : C_c(α, ℝ≥0)) (x : α) : f.toReal x = f x := compLeft_apply rfl _ _
/-
**CompactlySupportedContinuousMap.toReal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Compa
ctlySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {f : CompactlySupportedContin
uousMap α NNReal}, 0 ≤ f.toReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
-/
@[simp] lemma toReal_nonneg {f : C_c(α, ℝ≥0)} : 0 ≤ f.toReal := fun _ ↦ by simp
/-
**CompactlySupportedContinuousMap.toReal_add** 是 Mathlib 中的一个定理，位于命名空间 `Compactl
ySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (f g : CompactlySupportedCont
inuousMap α NNReal),   (f + g).toReal = f.toReal + g.toReal
参数：f g : CompactlySupportedContinuousMap α NNReal；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toReal_add (f g : C_c(α, ℝ≥0)) : (f + g).toReal = f.toReal + g.toReal := by ext; simp
/-
**CompactlySupportedContinuousMap.toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 `Compact
lySupportedContinuousMap`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (r : NNReal) (f : CompactlySu
pportedContinuousMap α NNReal),   (r • f).toReal = r • f.toReal
参数：r : NNReal；f : CompactlySupportedContinuousMap α NNReal；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toReal_smul (r : ℝ≥0) (f : C_c(α, ℝ≥0)) : (r • f).toReal = r • f.toReal := by
  ext; simp [NNReal.smul_def]

@[simp]
/-
**CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg** 是 Mathlib 中的一个
引理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_sub_nnrealPart_neg (f : C_c(α, Real)) : (nnrealPart f).toReal -
 (nnrealPart (-f)).toReal = f
参数：f : C_c(α, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `max_zero_sub_max_neg_zero_eq_self`：∀ {α : Type u_1} [inst : AddGroup α] 
[inst_1 : LinearOrder α] [AddLeftMono α] (a : α), max a 0 - max (-a) 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrealPart_sub_nnrealPart_neg (f : C_c(α, ℝ)) :
    (nnrealPart f).toReal - (nnrealPart (-f)).toReal = f := by ext x; simp

/-- The map `toReal` defined as a `ℝ≥0`-linear map. -/
/-
**CompactlySupportedContinuousMap.toRealLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Com
pactlySupportedContinuousMap`。
形式化陈述：toRealLinearMap : C_c(α, Real>=0) ->ₗ[Real>=0] C_c(α, Real) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `toReal` defined as a `ℝ≥0`-linear map.
-/
noncomputable def toRealLinearMap : C_c(α, ℝ≥0) →ₗ[ℝ≥0] C_c(α, ℝ) where
  toFun := toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp, norm_cast]
/-
**CompactlySupportedContinuousMap.coe_toRealLinearMap** 是 Mathlib 中的一个引理，位于命名空间 
`CompactlySupportedContinuousMap`。
形式化陈述：coe_toRealLinearMap : (toRealLinearMap : C_c(α, Real>=0) -> C_c(α, Real)) 
= toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma coe_toRealLinearMap : (toRealLinearMap : C_c(α, ℝ≥0) → C_c(α, ℝ)) = toReal := rfl
/-
**CompactlySupportedContinuousMap.toRealLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空
间 `CompactlySupportedContinuousMap`。
形式化陈述：toRealLinearMap_apply (f : C_c(α, Real>=0)) : toRealLinearMap f = f.toReal
参数：f : C_c(α, Real>=0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma toRealLinearMap_apply (f : C_c(α, ℝ≥0)) : toRealLinearMap f = f.toReal := rfl
/-
**CompactlySupportedContinuousMap.toRealLinearMap_apply_apply** 是 Mathlib 中的一个引理
，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：toRealLinearMap_apply_apply (f : C_c(α, Real>=0)) (x : α) : toRealLinearMa
p f x = (f x).toReal
参数：f : C_c(α, Real>=0)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toRealLinearMap_apply_apply (f : C_c(α, ℝ≥0)) (x : α) :
    toRealLinearMap f x = (f x).toReal := by simp

@[simp]
/-
**CompactlySupportedContinuousMap.nnrealPart_toReal_eq** 是 Mathlib 中的一个引理，位于命名空间
 `CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_toReal_eq (f : C_c(α, Real>=0)) : nnrealPart (toReal f) = f
参数：f : C_c(α, Real>=0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrealPart_toReal_eq (f : C_c(α, ℝ≥0)) : nnrealPart (toReal f) = f := by ext x; simp

@[simp]
/-
**CompactlySupportedContinuousMap.nnrealPart_neg_toReal_eq** 是 Mathlib 中的一个引理，位于
命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：nnrealPart_neg_toReal_eq (f : C_c(α, Real>=0)) : nnrealPart (-toReal f) = 
0
参数：f : C_c(α, Real>=0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrealPart_neg_toReal_eq (f : C_c(α, ℝ≥0)) : nnrealPart (-toReal f) = 0 := by ext x; simp

section toNNRealLinear

/-- For a positive linear functional `Λ : C_c(α, ℝ) → ℝ`, define a `ℝ≥0`-linear map. -/
/-
**CompactlySupportedContinuousMap.toNNRealLinear** 是 Mathlib 中的一个定义，位于命名空间 `Comp
actlySupportedContinuousMap`。
形式化陈述：toNNRealLinear (Λ : C_c(α, Real) ->ₚ[Real] Real) : C_c(α, Real>=0) ->ₗ[Rea
l>=0] Real>=0 where toFun f
参数：Λ : C_c(α, Real) ->ₚ[Real] Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a positive linear functional `Λ : C_c(α, ℝ) → ℝ`, define a `ℝ≥0`-linear map.
-/
noncomputable def toNNRealLinear (Λ : C_c(α, ℝ) →ₚ[ℝ] ℝ) :
    C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := .mk (Λ (toRealLinearMap f)) (Λ.map_nonneg (by simp))
  map_add' f g := by simp; rfl
  map_smul' a f := by simp [NNReal.smul_def]; rfl

@[simp]
/-
**CompactlySupportedContinuousMap.toNNRealLinear_apply** 是 Mathlib 中的一个引理，位于命名空间
 `CompactlySupportedContinuousMap`。
形式化陈述：toNNRealLinear_apply (Λ : C_c(α, Real) ->ₚ[Real] Real) (f : C_c(α, Real>=0
)) : toNNRealLinear Λ f = Λ (toReal f)
参数：Λ : C_c(α, Real) ->ₚ[Real] Real；f : C_c(α, Real>=0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
-/
lemma toNNRealLinear_apply (Λ : C_c(α, ℝ) →ₚ[ℝ] ℝ) (f : C_c(α, ℝ≥0)) :
    toNNRealLinear Λ f = Λ (toReal f) := rfl

@[simp]
/-
**CompactlySupportedContinuousMap.toNNRealLinear_inj** 是 Mathlib 中的一个引理，位于命名空间 `
CompactlySupportedContinuousMap`。
形式化陈述：toNNRealLinear_inj (Λ₁ Λ₂ : C_c(α, Real) ->ₚ[Real] Real) : toNNRealLinear 
Λ₁ = toNNRealLinear Λ₂ ↔ Λ₁ = Λ₂
参数：Λ₁ Λ₂ : C_c(α, Real) ->ₚ[Real] Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用引理 `PositiveLinearMap.ext`：ext {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x
) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg`：nnrealPar
t_sub_nnrealPart_neg (f : C_c(α, Real)) : (nnrealPart f).toReal - (nnrealPart (-
f)).toReal = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNNRealLinear_inj (Λ₁ Λ₂ : C_c(α, ℝ) →ₚ[ℝ] ℝ) :
    toNNRealLinear Λ₁ = toNNRealLinear Λ₂ ↔ Λ₁ = Λ₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  ext f
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply] at h
  simp_rw [map_sub, h]

end toNNRealLinear

section toRealPositiveLinear

set_option backward.isDefEq.respectTransparency false in
/-- For a positive linear functional `Λ : C_c(α, ℝ≥0) → ℝ≥0`, define a positive `ℝ`-linear map. -/
/-
**CompactlySupportedContinuousMap.toRealPositiveLinear** 是 Mathlib 中的一个定义，位于命名空间
 `CompactlySupportedContinuousMap`。
形式化陈述：toRealPositiveLinear (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) : C_c(α, R
eal) ->ₚ[Real] Real
参数：Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
For a positive linear functional `Λ : C_c(α, ℝ≥0) → ℝ≥0`, define a positive `ℝ`-
linear map.
-/
noncomputable def toRealPositiveLinear (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : C_c(α, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Λ (nnrealPart f) - Λ (nnrealPart (- f))
      map_add' f g := by
        simp only [neg_add_rev]
        obtain ⟨h, hh⟩ := exists_add_nnrealPart_add_eq f g
        rw [← add_zero ((Λ (f + g).nnrealPart).toReal - (Λ (-g + -f).nnrealPart).toReal),
          ← sub_self (Λ h).toReal, sub_add_sub_comm, ← NNReal.coe_add, ← NNReal.coe_add,
          ← map_add, ← map_add, hh.1, add_comm (-g) (-f), hh.2]
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
    (fun g hg ↦ by simp [nnrealPart_neg_eq_zero_of_nonneg hg])
/-
**CompactlySupportedContinuousMap.toRealPositiveLinear_apply** 是 Mathlib 中的一个引理，
位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：toRealPositiveLinear_apply {Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0} (f :
 C_c(α, Real)) : toRealPositiveLinear Λ f = Λ (nnrealPart f) - Λ (nnrealPart (-f
))
参数：α, Real>=0；f : C_c(α, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma toRealPositiveLinear_apply {Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0} (f : C_c(α, ℝ)) :
    toRealPositiveLinear Λ f = Λ (nnrealPart f) - Λ (nnrealPart (-f)) := rfl

@[simp]
/-
**CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal** 是 Mathlib 中的一
个引理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：eq_toRealPositiveLinear_toReal (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) 
(f : C_c(α, Real>=0)) : toRealPositiveLinear Λ (toReal f) = Λ f
参数：Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0；f : C_c(α, Real>=0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CompactlySupportedContinuousMap.nnrealPart_toReal_eq`：nnrealPart_toReal_
eq (f : C_c(α, Real>=0)) : nnrealPart (toReal f) = f
· 使用引理 `CompactlySupportedContinuousMap.nnrealPart_neg_toReal_eq`：nnrealPart_neg
_toReal_eq (f : C_c(α, Real>=0)) : nnrealPart (-toReal f) = 0
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
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_toRealPositiveLinear_toReal (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) (f : C_c(α, ℝ≥0)) :
    toRealPositiveLinear Λ (toReal f) = Λ f := by
  simp [toRealPositiveLinear_apply]

@[simp]
/-
**CompactlySupportedContinuousMap.eq_toNNRealLinear_toRealPositiveLinear** 是 Mat
hlib 中的一个引理，位于命名空间 `CompactlySupportedContinuousMap`。
形式化陈述：eq_toNNRealLinear_toRealPositiveLinear (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] R
eal>=0) : toNNRealLinear (toRealPositiveLinear Λ) = Λ
参数：Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal`：eq_toRea
lPositiveLinear_toReal (Λ : C_c(α, Real>=0) ->ₗ[Real>=0] Real>=0) (f : C_c(α, Re
al>=0)) : toRealPositiveLinear Λ (toReal f) = Λ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_toNNRealLinear_toRealPositiveLinear (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) :
    toNNRealLinear (toRealPositiveLinear Λ) = Λ := by
  ext f
  simp

end toRealPositiveLinear

section pullback

variable [R1Space α] [Group α] [TopologicalSpace β] [R1Space β] [Group β] [ContinuousMul β]
  [NormedAddCommGroup γ] {φ : α →* β} (hφ : Topology.IsClosedEmbedding φ)

open scoped Pointwise in
/-- Pull back a continuous compactly supported function `f` on `β` along a closed embedding
`φ : α →* β` to the continuous compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /-- Pull back a continuous compactly supported function `f` on `β` along a closed
embedding `φ : α →+ β` to the continuous compactly supported function `a ↦ f (b + φ a)` on `A`. -/]
/-
**CompactlySupportedContinuousMap.pullback_monoidHom** 是 Mathlib 中的一个定义，位于命名空间 `
CompactlySupportedContinuousMap`。
形式化陈述：pullback_monoidHom (f : CompactlySupportedContinuousMap β γ) (b : β) : Com
pactlySupportedContinuousMap α γ where toFun a
参数：f : CompactlySupportedContinuousMap β γ；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def pullback_monoidHom (f : CompactlySupportedContinuousMap β γ) (b : β) :
    CompactlySupportedContinuousMap α γ where
  toFun a := f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      hφ.isCompact_preimage (hK.smul b⁻¹), fun x hx ↦ hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by fun_prop

@[to_additive]
/-
**CompactlySupportedContinuousMap.pullback_monoidHom_def** 是 Mathlib 中的一个定理，位于命名
空间 `CompactlySupportedContinuousMap`。
形式化陈述：pullback_monoidHom_def (f : CompactlySupportedContinuousMap β γ) (b : β) (
a : α) : pullback_monoidHom hφ f b a = f (b * φ a)
参数：f : CompactlySupportedContinuousMap β γ；b : β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_monoidHom_def (f : CompactlySupportedContinuousMap β γ) (b : β) (a : α) :
    pullback_monoidHom hφ f b a = f (b * φ a) :=
  rfl

end pullback

end CompactlySupportedContinuousMap

end NonnegativePart

