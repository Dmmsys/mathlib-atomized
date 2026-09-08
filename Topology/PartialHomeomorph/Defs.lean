/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.ContinuousOn

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between subsets of topological spaces. An element `e` of
`PartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that the functions are continuous on them. Equivalently, they are
homeomorphisms there.

As for `Equiv`s, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toPartialHomeomorph`: associating a partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `PartialHomeomorph.symm`: the inverse of a partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

/-- Partial homeomorphisms, defined on subsets of the space -/
/-
**PartialHomeomorph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_7) → (Y : Type u_8) → [TopologicalSpace X] → [TopologicalSpace
 Y] → Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial homeomorphisms, defined on subsets of the space
-/
structure PartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] extends PartialEquiv X Y where
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/
section Basic
/-- Coercion of a partial homeomorphisms to a function. We don't use `e.toFun` because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. -/
/-
**PartialHomeomorph.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → PartialHomeomorph X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a partial homeomorphisms to a function. We don't use `e.toFun` becau
se it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialE
quiv`.
-/
@[coe] def toFun' : X → Y := e.toFun

/-- Coercion of a `PartialHomeomorph` to function.
Note that a `PartialHomeomorph` is not `DFunLike`. -/
/-
**PartialHomeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `PartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a `PartialHomeomorph` to function.
Note that a `PartialHomeomorph` is not `DFunLike`.
-/
instance : CoeFun (PartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a partial homeomorphism -/
@[symm]
/-
**PartialHomeomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     [inst : TopologicalSpace X] → [ins
t_1 : TopologicalSpace Y] → PartialHomeomorph X Y → PartialHomeomorph Y X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…

--- 原说明 ---
The inverse of a partial homeomorphism
-/
protected def symm : PartialHomeomorph Y X where
  toPartialEquiv := e.toPartialEquiv.symm
  continuousOn_toFun := e.continuousOn_invFun
  continuousOn_invFun := e.continuousOn_toFun

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**PartialHomeomorph.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorph.Sim
ps`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → PartialHomeomorph X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (e : PartialHomeomorph X Y) : X → Y := e

/-- See Note [custom simps projection] -/
/-
**PartialHomeomorph.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorp
h.Simps`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → PartialHomeomorph X Y → Y → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : PartialHomeomorph X Y) : Y → X := e.symm

initialize_simps_projections PartialHomeomorph (toFun → apply, invFun → symm_apply)

@[fun_prop]
/-
**PartialHomeomorph.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   ContinuousOn (↑e) e.source
参数：e : PartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
-/
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun

@[fun_prop]
/-
**PartialHomeomorph.continuousOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomor
ph`。
形式化陈述：continuousOn_symm : ContinuousOn e.symm e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
-/
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp]
/-
**PartialHomeomorph.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：coe_mk (e : PartialEquiv X Y) (h₁ h₂) : (PartialHomeomorph.mk e h₁ h₂ : X 
-> Y) = e
参数：e : PartialEquiv X Y；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : PartialEquiv X Y) (h₁ h₂) : (PartialHomeomorph.mk e h₁ h₂ : X → Y) = e := rfl

@[simp]
/-
**PartialHomeomorph.coe_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂) : ((PartialHomeomorph.mk e h₁ h
₂).symm : Y -> X) = e.symm
参数：e : PartialEquiv X Y；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂) :
    ((PartialHomeomorph.mk e h₁ h₂).symm : Y → X) = e.symm :=
  rfl
/-
**PartialHomeomorph.toPartialEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `PartialH
omeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y],   Function.Injective PartialHomeomorph.toPartialEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv_injective :
    Injective (toPartialEquiv : PartialHomeomorph X Y → PartialEquiv X Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp]
/-
**PartialHomeomorph.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：toFun_eq_coe (e : PartialHomeomorph X Y) : e.toFun = e
参数：e : PartialHomeomorph X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register a few simp lemmas to make sure that `simp` puts the application of a lo
cal
homeomorphism in its normal form, i.e., in terms of its coercion to a function.
-/
theorem toFun_eq_coe (e : PartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp]
/-
**PartialHomeomorph.invFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：invFun_eq_coe (e : PartialHomeomorph X Y) : e.invFun = e.symm
参数：e : PartialHomeomorph X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_coe (e : PartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp]
/-
**PartialHomeomorph.coe_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomo
rph`。
形式化陈述：coe_toPartialEquiv : (e.toPartialEquiv : X -> Y) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialEquiv : (e.toPartialEquiv : X → Y) = e :=
  rfl

@[simp]
/-
**PartialHomeomorph.coe_toPartialEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHo
meomorph`。
形式化陈述：coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y -> X) = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y → X) = e.symm :=
  rfl

@[simp]
/-
**PartialHomeomorph.map_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：map_source {x : X} (h : x in e.source) : e x in e.target
参数：h : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
-/
theorem map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `map_source`, stated in terms of subsets. -/
/-
**PartialHomeomorph.image_source_subset** 是 Mathlib 中的一个引理，位于命名空间 `PartialHomeom
orph`。
形式化陈述：image_source_subset : e '' e.source subseteq e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target

--- 原说明 ---
Variant of `map_source`, stated in terms of subsets.
-/
lemma image_source_subset : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp]
/-
**PartialHomeomorph.map_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：map_target {x : Y} (h : x in e.target) : e.symm x in e.source
参数：h : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : β⦄, x ∈ self.target → self.invFun x ∈ self.source
-/
theorem map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp]
/-
**PartialHomeomorph.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：left_inv {x : X} (h : x in e.source) : e.symm (e x) = x
参数：h : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
-/
theorem left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp]
/-
**PartialHomeomorph.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：right_inv {x : Y} (h : x in e.target) : e (e.symm x) = x
参数：h : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x
-/
theorem right_inv {x : Y} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
/-
**PartialHomeomorph.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：eq_symm_apply {x : X} {y : Y} (hx : x in e.source) (hy : y in e.target) : 
x = e.symm y ↔ e x = y
参数：hx : x in e.source；hy : y in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.eq_symm_apply`：eq_symm_apply {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : x = e.symm y ↔ e x = y
-/
theorem eq_symm_apply {x : X} {y : Y} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy
/-
**PartialHomeomorph.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.MapsTo (↑e) e.source e.target
参数：e : PartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source) : e
 x in e.target
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
/-
**PartialHomeomorph.mapsTo_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.MapsTo (↑e.symm) e.target e.s
ource
参数：e : PartialHomeomorph X Y；↑e.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.M
apsTo (↑e) e.s…
-/
protected theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo
/-
**PartialHomeomorph.leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.LeftInvOn (↑e.symm) (↑e) e.so
urce
参数：e : PartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e.sym
m (e x) = x
-/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
/-
**PartialHomeomorph.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.RightInvOn (↑e.symm) (↑e) e.t
arget
参数：e : PartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) : e (
e.symm x) = x
-/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
/-
**PartialHomeomorph.invOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.InvOn (↑e.symm) (↑e) e.source
 e.target
参数：e : PartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Se
t.LeftInvOn (↑e.s…
· 使用定理 `PartialHomeomorph.rightInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   S
et.RightInvOn (↑e.…
-/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
/-
**PartialHomeomorph.injOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.InjOn (↑e) e.source
参数：e : PartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `PartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Se
t.LeftInvOn (↑e.s…
-/
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
/-
**PartialHomeomorph.bijOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.BijOn (↑e) e.source e.target
参数：e : PartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `PartialHomeomorph.invOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.In
vOn (↑e.symm)…
· 使用定理 `PartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.M
apsTo (↑e) e.s…
· 使用定理 `PartialHomeomorph.mapsTo_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   
Set.MapsTo (↑e.symm…
-/
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.mapsTo_symm
/-
**PartialHomeomorph.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   Set.SurjOn (↑e) e.source e.target
参数：e : PartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `PartialHomeomorph.bijOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.Bi
jOn (↑e) e.so…
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

end Basic

/-- Interpret a `Homeomorph` as a `PartialHomeomorph` by restricting it
to a set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialEquiv,
  simps! -isSimp source target]
/-
**PartialHomeomorph._root_.Homeomorph.toPartialHomeomorphOfImageEq** 是 Mathlib 中
的一个定义，位于命名空间 `PartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Homeomorph.toPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X)
    (t : Set Y) (h : e '' s = t) : PartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquivOfImageEq s t h
  continuousOn_toFun := e.continuous.continuousOn
  continuousOn_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a partial homeomorphism on the whole space -/
@[simps! -fullyApplied]
/-
**PartialHomeomorph._root_.Homeomorph.toPartialHomeomorph** 是 Mathlib 中的一个定义，位于命
名空间 `PartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism induces a partial homeomorphism on the whole space
-/
def _root_.Homeomorph.toPartialHomeomorph (e : X ≃ₜ Y) : PartialHomeomorph X Y :=
  e.toPartialHomeomorphOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
/-
**PartialHomeomorph.replacePartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeom
orph`。
形式化陈述：replacePartialEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y) (h
 : e.toPartialEquiv = e') : PartialHomeomorph X Y where toPartialEquiv
参数：e : PartialHomeomorph X Y；e' : PartialEquiv X Y；h : e.toPartialEquiv = e'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace `toPartialEquiv` field to provide better definitional equalities.
-/
def replacePartialEquiv (e : PartialHomeomorph X Y) (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : PartialHomeomorph X Y where
  toPartialEquiv := e'
  continuousOn_toFun := h ▸ e.continuousOn_toFun
  continuousOn_invFun := h ▸ e.continuousOn_invFun
/-
**PartialHomeomorph.replacePartialEquiv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Parti
alHomeomorph`。
形式化陈述：replacePartialEquiv_eq_self (e' : PartialEquiv X Y) (h : e.toPartialEquiv 
= e') : e.replacePartialEquiv e' h = e
参数：e' : PartialEquiv X Y；h : e.toPartialEquiv = e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem replacePartialEquiv_eq_self (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : e.replacePartialEquiv e' h = e := by
  cases e
  subst e'
  rfl

/-- Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
/-
**PartialHomeomorph.ext** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e e' : PartialHomeomorph X Y),   (∀ (x : X), ↑e x = ↑e' x) → 
(∀ (x : Y), ↑e.symm x = ↑e'.symm x) → e.source = e'.source → e = e'
参数：e e' : PartialHomeomorph X Y；∀ (x : X), ↑e x = ↑e' x；∀ (x : Y), ↑e.symm x = ↑
e'.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.toPartialEquiv_injective`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Function.Inject
ive PartialHomeomorph.toPartialE…
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…

--- 原说明 ---
Two partial homeomorphisms are equal when they have equal `toFun`, `invFun` and 
`source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines
 `invFun` on
the target. This would only be true for a weaker notion of equality, arguably th
e right one,
called `EqOnSource`.
-/
protected theorem ext (e' : PartialHomeomorph X Y) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialEquiv_injective (PartialEquiv.ext h hinv hs)

@[simp]
/-
**PartialHomeomorph.symm_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeom
orph`。
形式化陈述：symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

-- The following lemmas are already simp via `PartialEquiv`
/-
**PartialHomeomorph.symm_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：symm_source : e.symm.source = e.target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_source : e.symm.source = e.target :=
  rfl
/-
**PartialHomeomorph.symm_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：symm_target : e.symm.target = e.source
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_target : e.symm.target = e.source :=
  rfl
/-
**PartialHomeomorph.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : PartialHomeomorph X Y),   e.symm.symm = e
参数：e : PartialHomeomorph X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_symm : e.symm.symm = e := rfl
/-
**PartialHomeomorph.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`
。
形式化陈述：symm_bijective : Function.Bijective (PartialHomeomorph.symm : PartialHomeo
morph X Y -> PartialHomeomorph Y X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `PartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   e.
symm.symm = e
-/
theorem symm_bijective : Function.Bijective
    (PartialHomeomorph.symm : PartialHomeomorph X Y → PartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

end PartialHomeomorph

