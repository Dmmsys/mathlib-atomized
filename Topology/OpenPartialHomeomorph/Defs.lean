/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.PartialHomeomorph.Defs

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`OpenPartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As for `Equiv`s, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toOpenPartialHomeomorph`: associating an open partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `OpenPartialHomeomorph.symm`: the inverse of an open partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

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

/-- Partial homeomorphisms, defined on open subsets of the space -/
/-
**OpenPartialHomeomorph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_7) → (Y : Type u_8) → [TopologicalSpace X] → [TopologicalSpace
 Y] → Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial homeomorphisms, defined on open subsets of the space
-/
structure OpenPartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] extends PartialHomeomorph X Y where
  open_source : IsOpen source
  open_target : IsOpen target

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/
section Basic
/-- Coercion of an open partial homeomorphisms to a function. We don't use `e.toFun` because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. -/
/-
**OpenPartialHomeomorph.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → OpenPartialHomeomorph X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an open partial homeomorphisms to a function. We don't use `e.toFun`
 because it is
actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialE
quiv`.
-/
@[coe] def toFun' : X → Y := e.toFun

/-- Coercion of an `OpenPartialHomeomorph` to function.
Note that an `OpenPartialHomeomorph` is not `DFunLike`. -/
/-
**OpenPartialHomeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `OpenPartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an `OpenPartialHomeomorph` to function.
Note that an `OpenPartialHomeomorph` is not `DFunLike`.
-/
instance : CoeFun (OpenPartialHomeomorph X Y) fun _ => X → Y :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of an open partial homeomorphism -/
@[symm]
/-
**OpenPartialHomeomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     [inst : TopologicalSpace X] → [ins
t_1 : TopologicalSpace Y] → OpenPartialHomeomorph X Y → OpenPartialHomeomorph Y 
X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
The inverse of an open partial homeomorphism
-/
protected def symm : OpenPartialHomeomorph Y X where
  toPartialHomeomorph := e.toPartialHomeomorph.symm
  open_source := e.open_target
  open_target := e.open_source

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**OpenPartialHomeomorph.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeom
orph.Simps`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → OpenPartialHomeomorph X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (e : OpenPartialHomeomorph X Y) : X → Y := e

/-- See Note [custom simps projection] -/
/-
**OpenPartialHomeomorph.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialH
omeomorph.Simps`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → OpenPartialHomeomorph X Y → Y → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : OpenPartialHomeomorph X Y) : Y → X := e.symm

initialize_simps_projections OpenPartialHomeomorph (toFun → apply, invFun → symm_apply)

@[fun_prop]
/-
**OpenPartialHomeomorph.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), ContinuousOn (↑e) e.source
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
-/
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuousOn_toFun

@[fun_prop]
/-
**OpenPartialHomeomorph.continuousOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：continuousOn_symm : ContinuousOn e.symm e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
-/
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuousOn_invFun

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：coe_mk (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) : (OpenPartialHomeomorph.mk (.
mk e h₁ h₂) h₃ h₄ : X -> Y) = e
参数：e : PartialEquiv X Y；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) :
    (OpenPartialHomeomorph.mk (.mk e h₁ h₂) h₃ h₄ : X → Y) = e :=
  rfl

@[deprecated (since := "2026-05-20")] alias mk_coe := coe_mk

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) : ((OpenPartialHomeomorph
.mk (.mk e h₁ h₂) h₃ h₄).symm : Y -> X) = e.symm
参数：e : PartialEquiv X Y；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk_symm (e : PartialEquiv X Y) (h₁ h₂ h₃ h₄) :
    ((OpenPartialHomeomorph.mk (.mk e h₁ h₂) h₃ h₄).symm : Y → X) = e.symm :=
  rfl

@[deprecated (since := "2026-05-20")] alias mk_coe_symm := coe_mk_symm
/-
**OpenPartialHomeomorph.toPartialHomeomorph_injective** 是 Mathlib 中的一个定理，位于命名空间 
`OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y],   Function.Injective OpenPartialHomeomorph.toPartialHomeomorph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialHomeomorph_injective :
    Injective (toPartialHomeomorph : OpenPartialHomeomorph X Y → PartialHomeomorph X Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
/-
**OpenPartialHomeomorph.toPartialEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：toPartialEquiv_injective : Injective (fun f => f.toPartialEquiv : OpenPart
ialHomeomorph X Y -> PartialEquiv X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `PartialHomeomorph.toPartialEquiv_injective`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Function.Inject
ive PartialHomeomorph.toPartialE…
· 使用定理 `OpenPartialHomeomorph.toPartialHomeomorph_injective`：∀ {X : Type u_1} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Functi
on.Injective OpenPartialHomeomorph.toPart…
-/
theorem toPartialEquiv_injective :
    Injective (fun f ↦ f.toPartialEquiv : OpenPartialHomeomorph X Y → PartialEquiv X Y) :=
  PartialHomeomorph.toPartialEquiv_injective.comp toPartialHomeomorph_injective

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：toFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.toFun = e
参数：e : OpenPartialHomeomorph X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register a few simp lemmas to make sure that `simp` puts the application of a lo
cal
homeomorphism in its normal form, i.e., in terms of its coercion to a function.
-/
theorem toFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.toFun = e :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.invFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：invFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.invFun = e.symm
参数：e : OpenPartialHomeomorph X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_coe (e : OpenPartialHomeomorph X Y) : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：coe_toPartialEquiv : (e.toPartialEquiv : X -> Y) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialEquiv : (e.toPartialEquiv : X → Y) = e :=
  rfl

@[deprecated (since := "2026-05-18")] alias coe_coe := coe_toPartialEquiv

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_toPartialEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y -> X) = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialEquiv_symm : (e.toPartialEquiv.symm : Y → X) = e.symm :=
  rfl

@[deprecated (since := "2026-05-18")] alias coe_coe_symm := coe_toPartialEquiv_symm

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.map_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：map_source {x : X} (h : x in e.source) : e x in e.target
参数：h : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
-/
theorem map_source {x : X} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_toPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：coe_toPartialHomeomorph : (e.toPartialHomeomorph : X -> Y) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialHomeomorph : (e.toPartialHomeomorph : X → Y) = e :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_toPartialHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：coe_toPartialHomeomorph_symm : (e.toPartialHomeomorph.symm : Y -> X) = e.s
ymm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPartialHomeomorph_symm : (e.toPartialHomeomorph.symm : Y → X) = e.symm :=
  rfl

/-- Variant of `map_source`, stated for images of subsets of `source`. -/
/-
**OpenPartialHomeomorph.image_source_subset** 是 Mathlib 中的一个引理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：image_source_subset : e '' e.source subseteq e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target

--- 原说明 ---
Variant of `map_source`, stated for images of subsets of `source`.
-/
lemma image_source_subset : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.map_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：map_target {x : Y} (h : x in e.target) : e.symm x in e.source
参数：h : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : β⦄, x ∈ self.target → self.invFun x ∈ self.source
-/
theorem map_target {x : Y} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorp
h`。
形式化陈述：left_inv {x : X} (h : x in e.source) : e.symm (e x) = x
参数：h : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
-/
theorem left_inv {x : X} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
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
**OpenPartialHomeomorph.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
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
**OpenPartialHomeomorph.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.MapsTo (↑e) e.source e.ta
rget
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
/-
**OpenPartialHomeomorph.mapsTo_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.MapsTo (↑e.symm) e.target
 e.source
参数：e : OpenPartialHomeomorph X Y；↑e.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
-/
protected theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

@[deprecated (since := "2026-05-28")] alias symm_mapsTo := OpenPartialHomeomorph.mapsTo_symm
/-
**OpenPartialHomeomorph.leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.LeftInvOn (↑e.symm) (↑e) 
e.source
参数：e : OpenPartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
/-
**OpenPartialHomeomorph.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.RightInvOn (↑e.symm) (↑e)
 e.target
参数：e : OpenPartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
-/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
/-
**OpenPartialHomeomorph.invOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.InvOn (↑e.symm) (↑e) e.so
urce e.target
参数：e : OpenPartialHomeomorph X Y；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), Set.LeftInvOn (…
· 使用定理 `OpenPartialHomeomorph.rightInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph
 X Y), Set.RightInvOn …
-/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
/-
**OpenPartialHomeomorph.injOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.InjOn (↑e) e.source
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `OpenPartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), Set.LeftInvOn (…
-/
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
/-
**OpenPartialHomeomorph.bijOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.BijOn (↑e) e.source e.tar
get
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `OpenPartialHomeomorph.invOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InvOn (↑e.s…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `OpenPartialHomeomorph.mapsTo_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y), Set.MapsTo (↑e.…
-/
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.mapsTo_symm
/-
**OpenPartialHomeomorph.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), Set.SurjOn (↑e) e.source e.ta
rget
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `OpenPartialHomeomorph.bijOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.BijOn (↑e) …
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

end Basic

/-- Interpret a `Homeomorph` as an `OpenPartialHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! -fullyApplied apply symm_apply toPartialHomeomorph,
  simps! -isSimp source target]
/-
**OpenPartialHomeomorph._root_.Homeomorph.toOpenPartialHomeomorphOfImageEq** 是 M
athlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Homeomorph.toOpenPartialHomeomorphOfImageEq (e : X ≃ₜ Y) (s : Set X) (hs : IsOpen s)
    (t : Set Y) (h : e '' s = t) : OpenPartialHomeomorph X Y where
  toPartialHomeomorph := e.toPartialHomeomorphOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]

/-- A homeomorphism induces an open partial homeomorphism on the whole space -/
@[simps! (attr := mfld_simps) -fullyApplied]
/-
**OpenPartialHomeomorph._root_.Homeomorph.toOpenPartialHomeomorph** 是 Mathlib 中的
一个定义，位于命名空间 `OpenPartialHomeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism induces an open partial homeomorphism on the whole space
-/
def _root_.Homeomorph.toOpenPartialHomeomorph (e : X ≃ₜ Y) : OpenPartialHomeomorph X Y :=
  e.toOpenPartialHomeomorphOfImageEq univ isOpen_univ univ <|
    by rw [image_univ, e.surjective.range_eq]

/-- Replace `toPartialEquiv` field to provide better definitional equalities. -/
/-
**OpenPartialHomeomorph.replacePartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：replacePartialEquiv (e : OpenPartialHomeomorph X Y) (e' : PartialEquiv X Y
) (h : e.toPartialEquiv = e') : OpenPartialHomeomorph X Y where toPartialHomeomo
rph
参数：e : OpenPartialHomeomorph X Y；e' : PartialEquiv X Y；h : e.toPartialEquiv = e'
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace `toPartialEquiv` field to provide better definitional equalities.
-/
def replacePartialEquiv (e : OpenPartialHomeomorph X Y) (e' : PartialEquiv X Y)
    (h : e.toPartialEquiv = e') : OpenPartialHomeomorph X Y where
  toPartialHomeomorph := e.toPartialHomeomorph.replacePartialEquiv e' h
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target

@[deprecated (since := "2026-05-19")] alias replaceEquiv := replacePartialEquiv
/-
**OpenPartialHomeomorph.replacePartialEquiv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph`。
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

@[deprecated (since := "2026-05-20")] alias replaceEquiv_eq_self := replacePartialEquiv_eq_self

/-- Two open partial homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
/-
**OpenPartialHomeomorph.ext** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e e' : OpenPartialHomeomorph X Y),   (∀ (x : X), ↑e x = ↑e' x
) → (∀ (x : Y), ↑e.symm x = ↑e'.symm x) → e.source = e'.source → e = e'
参数：e e' : OpenPartialHomeomorph X Y；∀ (x : X), ↑e x = ↑e' x；∀ (x : Y), ↑e.symm x
 = ↑e'.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialHomeomorph_injective`：∀ {X : Type u_1} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Functi
on.Injective OpenPartialHomeomorph.toPart…
· 使用定理 `PartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y]   (e e' : PartialHomeomorph X Y),   (∀ 
(x : X), ↑e…

--- 原说明 ---
Two open partial homeomorphisms are equal when they have equal `toFun`, `invFun`
 and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines
 `invFun` on
the target. This would only be true for a weaker notion of equality, arguably th
e right one,
called `EqOnSource`.
-/
protected theorem ext (e' : OpenPartialHomeomorph X Y) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toPartialHomeomorph_injective
    (PartialHomeomorph.ext e.toPartialHomeomorph e'.toPartialHomeomorph h hinv hs)

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.symm_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

-- The following lemmas are already simp via `PartialEquiv`
/-
**OpenPartialHomeomorph.symm_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：symm_source : e.symm.source = e.target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_source : e.symm.source = e.target :=
  rfl
/-
**OpenPartialHomeomorph.symm_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：symm_target : e.symm.target = e.source
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_target : e.symm.target = e.source :=
  rfl
/-
**OpenPartialHomeomorph.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y), e.symm.symm = e
参数：e : OpenPartialHomeomorph X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl
/-
**OpenPartialHomeomorph.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：symm_bijective : Function.Bijective (OpenPartialHomeomorph.symm : OpenPart
ialHomeomorph X Y -> OpenPartialHomeomorph Y X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective
    (OpenPartialHomeomorph.symm : OpenPartialHomeomorph X Y → OpenPartialHomeomorph Y X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

end OpenPartialHomeomorph

