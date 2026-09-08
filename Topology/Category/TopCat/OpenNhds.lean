/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Data.Set.Subsingleton

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `TopCat` of topological spaces and a point `x : X`, this file
builds the type `OpenNhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `Set X`). This is used in `Topology.Sheaves.Stalks` to build the stalk of a sheaf
at `x` as a limit over `OpenNhds x`.

## Main declarations

Besides `OpenNhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `OpenNhds x ⥤ Opens X`
* `functorNhds`: An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`
* `adjunctionNhds`: An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and
                    `OpenNhds (f x)`.
-/

@[expose] public section


open CategoryTheory TopologicalSpace Opposite Topology

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

/-- The type of open neighbourhoods of a point `x` in a (bundled) topological space. -/
/-
**TopologicalSpace.OpenNhds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：OpenNhds (x : X) : Type u
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open neighbourhoods of a point `x` in a (bundled) topological space.
-/
def OpenNhds (x : X) : Type u := { U : Opens X // x ∈ U }

namespace OpenNhds
variable {x : X} {U V W : OpenNhds x}

/-
**TopologicalSpace.OpenNhds.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalS
pace.OpenNhds`。
形式化陈述：partialOrder (x : X) : PartialOrder (OpenNhds x)
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder (x : X) : PartialOrder (OpenNhds x) :=
  inferInstanceAs (PartialOrder { U : Opens X // x ∈ U })
/-
**TopologicalSpace.OpenNhds.le_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
penNhds`。
形式化陈述：le_def (U V : OpenNhds x) : U <= V ↔ U.1 <= V.1
参数：U V : OpenNhds x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def (U V : OpenNhds x) : U ≤ V ↔ U.1 ≤ V.1 := Iff.rfl
/-
**TopologicalSpace.OpenNhds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenNhd
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Lattice (OpenNhds x) :=
  { inf := fun U V => ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩
    le_inf := fun U V W => @le_inf _ _ U.1.1 V.1.1 W.1.1
    inf_le_left := fun U V => @inf_le_left _ _ U.1.1 V.1.1
    inf_le_right := fun U V => @inf_le_right _ _ U.1.1 V.1.1
    sup := fun U V => ⟨U.1 ⊔ V.1, Set.mem_union_left V.1.1 U.2⟩
    sup_le := fun U V W => @sup_le _ _ U.1.1 V.1.1 W.1.1
    le_sup_left := fun U V => @le_sup_left _ _ U.1.1 V.1.1
    le_sup_right := fun U V => @le_sup_right _ _ U.1.1 V.1.1 }

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopologicalSpace.OpenNhds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenNhd
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : OrderTop (OpenNhds x) where
  top := ⟨⊤, trivial⟩
  le_top x := by
    cases x
    simp [le_def]

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopologicalSpace.OpenNhds.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenNhd
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Inhabited (OpenNhds x) :=
  ⟨⊤⟩
/-
**TopologicalSpace.OpenNhds.opensNhds.instFunLike** 是 Mathlib 中的一个定义，位于命名空间 `Top
ologicalSpace.OpenNhds.opensNhds`。
形式化陈述：{X : TopCat} → {x : ↑X} → {U V : TopologicalSpace.OpenNhds x} → FunLike (U
 ⟶ V) ↥↑U ↥↑V
参数：U ⟶ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance opensNhds.instFunLike : FunLike (U ⟶ V) U.1 V.1 where
  coe f := Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!
/-
**TopologicalSpace.OpenNhds.apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.OpenNhds`。
形式化陈述：∀ {X : TopCat} {x : ↑X} {U V : TopologicalSpace.OpenNhds x} (f : U ⟶ V) (y
 : ↑X) (hy : y ∈ ↑U), f ⟨y, hy⟩ = ⟨y, ⋯⟩
参数：f : U ⟶ V；y : ↑X；hy : y ∈ ↑U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma apply_mk (f : U ⟶ V) (y : X) (hy) : f ⟨y, hy⟩ = ⟨y, f.le hy⟩ := rfl
/-
**TopologicalSpace.OpenNhds.val_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.OpenNhds`。
形式化陈述：∀ {X : TopCat} {x : ↑X} {U V : TopologicalSpace.OpenNhds x} (f : U ⟶ V) (y
 : ↥↑U), ↑(f y) = ↑y
参数：f : U ⟶ V；y : ↥↑U；f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_apply (f : U ⟶ V) (y : U.1) : (f y : X) = y := rfl
/-
**TopologicalSpace.OpenNhds.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
penNhds`。
形式化陈述：∀ {X : TopCat} {x : ↑X} {U : TopologicalSpace.OpenNhds x} (f : U ⟶ U), ⇑f 
= id
参数：f : U ⟶ U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_id (f : U ⟶ U) : ⇑f = id := rfl
/-
**TopologicalSpace.OpenNhds.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace
.OpenNhds`。
形式化陈述：id_apply (f : U ⟶ U) (y : U.1) : f y = y
参数：f : U ⟶ U；y : U.1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_apply (f : U ⟶ U) (y : U.1) : f y = y := rfl
/-
**TopologicalSpace.OpenNhds.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.OpenNhds`。
形式化陈述：∀ {X : TopCat} {x : ↑X} {U V W : TopologicalSpace.OpenNhds x} (f : U ⟶ V) 
(g : V ⟶ W) (x_1 : ↥↑U),   (CategoryTheory.CategoryStruct.comp f g) x_1 = g (f x
_1)
参数：f : U ⟶ V；g : V ⟶ W；x_1 : ↥↑U；CategoryTheory.CategoryStruct.comp f g；f x_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U.1) : (f ≫ g) x = g (f x) := rfl

/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets. -/
/-
**TopologicalSpace.OpenNhds.infLELeft** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpac
e.OpenNhds`。
形式化陈述：infLELeft {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ U
参数：U V : OpenNhds x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def infLELeft {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ U :=
  homOfLE inf_le_left

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets. -/
/-
**TopologicalSpace.OpenNhds.infLERight** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpa
ce.OpenNhds`。
形式化陈述：infLERight {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ V
参数：U V : OpenNhds x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def infLERight {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ V :=
  homOfLE inf_le_right

/-- The inclusion functor from open neighbourhoods of `x`
to open sets in the ambient topological space. -/
/-
**TopologicalSpace.OpenNhds.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpac
e.OpenNhds`。
形式化陈述：inclusion (x : X) : OpenNhds x ⥤ Opens X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor from open neighbourhoods of `x`
to open sets in the ambient topological space.
-/
def inclusion (x : X) : OpenNhds x ⥤ Opens X :=
  (Subtype.mono_coe _).functor

@[simp]
/-
**TopologicalSpace.OpenNhds.inclusion_obj** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.OpenNhds`。
形式化陈述：inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U, p⟩ = U
参数：x : X；U；p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U, p⟩ = U :=
  rfl
/-
**TopologicalSpace.OpenNhds.isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.OpenNhds`。
形式化陈述：isOpenEmbedding {x : X} (U : OpenNhds x) : IsOpenEmbedding U.1.inclusion'
参数：U : OpenNhds x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
theorem isOpenEmbedding {x : X} (U : OpenNhds x) : IsOpenEmbedding U.1.inclusion' :=
  U.1.isOpenEmbedding

/-- The preimage functor from neighborhoods of `f x` to neighborhoods of `x`. -/
/-
**TopologicalSpace.OpenNhds.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Open
Nhds`。
形式化陈述：map (x : X) : OpenNhds (f x) ⥤ OpenNhds x where obj U
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage functor from neighborhoods of `f x` to neighborhoods of `x`.
-/
def map (x : X) : OpenNhds (f x) ⥤ OpenNhds x where
  obj U := ⟨(Opens.map f).obj U.1, U.2⟩
  map i := (Opens.map f).map i

@[simp]
/-
**TopologicalSpace.OpenNhds.map_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
OpenNhds`。
形式化陈述：map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩
参数：x : X；U；q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩ :=
  rfl

@[simp]
/-
**TopologicalSpace.OpenNhds.map_id_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.OpenNhds`。
形式化陈述：map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U
参数：x : X；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U := rfl

@[simp]
/-
**TopologicalSpace.OpenNhds.map_id_obj'** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.OpenNhds`。
形式化陈述：map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩,
 q⟩
参数：x : X；U；p；q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**TopologicalSpace.OpenNhds.map_id_obj_unop** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.OpenNhds`。
形式化陈述：map_id_obj_unop (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) 
= unop U
参数：x : X；U : (OpenNhds x)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id_obj_unop (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopologicalSpace.OpenNhds.op_map_id_obj** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.OpenNhds`。
形式化陈述：op_map_id_obj (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U
参数：x : X；U : (OpenNhds x)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_map_id_obj (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U := by simp

/-- `Opens.map f` and `OpenNhds.map f` form a commuting square (up to natural isomorphism)
with the inclusion functors into `Opens X`. -/
/-
**TopologicalSpace.OpenNhds.inclusionMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Topologic
alSpace.OpenNhds`。
形式化陈述：inclusionMapIso (x : X) : inclusion (f x) ⋙ Opens.map f ≅ map f x ⋙ inclus
ion x
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Opens.map f` and `OpenNhds.map f` form a commuting square (up to natural isomor
phism)
with the inclusion functors into `Opens X`.
-/
def inclusionMapIso (x : X) : inclusion (f x) ⋙ Opens.map f ≅ map f x ⋙ inclusion x :=
  NatIso.ofComponents fun U => { hom := 𝟙 _, inv := 𝟙 _ }

@[simp]
/-
**TopologicalSpace.OpenNhds.inclusionMapIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.OpenNhds`。
形式化陈述：inclusionMapIso_hom (x : X) : (inclusionMapIso f x).hom = 𝟙 _
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusionMapIso_hom (x : X) : (inclusionMapIso f x).hom = 𝟙 _ :=
  rfl

@[simp]
/-
**TopologicalSpace.OpenNhds.inclusionMapIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.OpenNhds`。
形式化陈述：inclusionMapIso_inv (x : X) : (inclusionMapIso f x).inv = 𝟙 _
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusionMapIso_inv (x : X) : (inclusionMapIso f x).inv = 𝟙 _ :=
  rfl

end OpenNhds

end TopologicalSpace

namespace IsOpenMap

open TopologicalSpace

variable {f}

/-- An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`. -/
@[simps]
/-
**IsOpenMap.functorNhds** 是 Mathlib 中的一个定义，位于命名空间 `IsOpenMap`。
形式化陈述：functorNhds (h : IsOpenMap f) (x : X) : OpenNhds x ⥤ OpenNhds (f x) where 
obj U
参数：h : IsOpenMap f；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`.
-/
def functorNhds (h : IsOpenMap f) (x : X) : OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map i := h.functor.map i

/-- An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and `OpenNhds (f x)`. -/
/-
**IsOpenMap.adjunctionNhds** 是 Mathlib 中的一个定义，位于命名空间 `IsOpenMap`。
形式化陈述：adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ Ope
nNhds.map f x where unit
参数：h : IsOpenMap f；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and `OpenNhds
 (f x)`.
-/
def adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ OpenNhds.map f x where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

end IsOpenMap

section

variable {f}

/--
An open embedding `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`.
We define `IsOpenEmbedding.functorNhds` as `IsOpenEmbedding.isOpenMap.functorNds`, so it won't
default to `IsInducing.functorNhds` (which is equal but not defeq).
-/
/-
**Topology.IsOpenEmbedding.functorNhds** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.functorNhds (h : Topology.IsOpenEmbedding f) (x :
 X)
参数：h : Topology.IsOpenEmbedding f；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open embedding `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`.
We define `IsOpenEmbedding.functorNhds` as `IsOpenEmbedding.isOpenMap.functorNds
`, so it won't
default to `IsInducing.functorNhds` (which is equal but not defeq).
-/
abbrev Topology.IsOpenEmbedding.functorNhds (h : Topology.IsOpenEmbedding f) (x : X) :=
    h.isOpenMap.functorNhds x

/--
An open embedding `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and `OpenNhds (f x)`.
We define `IsOpenEmbedding.adjunctionNhds` as `IsOpenEmbedding.isOpenMap.adjunctionNds`, so it
won't default to `IsInducing.adjunctionNhds`, which is an adjunction in the other direction.
-/
/-
**Topology.IsOpenEmbedding.adjunctionNhds** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.adjunctionNhds (h : Topology.IsOpenEmbedding f) (
x : X)
参数：h : Topology.IsOpenEmbedding f；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open embedding `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and `Op
enNhds (f x)`.
We define `IsOpenEmbedding.adjunctionNhds` as `IsOpenEmbedding.isOpenMap.adjunct
ionNds`, so it
won't default to `IsInducing.adjunctionNhds`, which is an adjunction in the othe
r direction.
-/
abbrev Topology.IsOpenEmbedding.adjunctionNhds (h : Topology.IsOpenEmbedding f) (x : X) :=
  h.isOpenMap.adjunctionNhds x

end

namespace Topology.IsInducing

open TopologicalSpace

variable {f}

/-- An inducing map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`. -/
@[simps]
/-
**Topology.IsInducing.functorNhds** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInducing
`。
形式化陈述：functorNhds (h : IsInducing f) (x : X) : OpenNhds x ⥤ OpenNhds (f x) where
 obj U
参数：h : IsInducing f；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`.
-/
def functorNhds (h : IsInducing f) (x : X) :
    OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, (h.mem_functorObj_iff U.1).mpr U.2⟩
  map := h.functor.map

/--
An inducing map `f : X ⟶ Y` induces an adjunction between `OpenNhds (f x)` and `OpenNhds x`.
-/
/-
**Topology.IsInducing.adjunctionNhds** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInduc
ing`。
形式化陈述：adjunctionNhds (h : IsInducing f) (x : X) : OpenNhds.map f x ⊣ h.functorNh
ds x where unit
参数：h : IsInducing f；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing map `f : X ⟶ Y` induces an adjunction between `OpenNhds (f x)` and `
OpenNhds x`.
-/
def adjunctionNhds (h : IsInducing f) (x : X) :
    OpenNhds.map f x ⊣ h.functorNhds x where
  unit := { app := fun U => homOfLE (h.adjunction.unit.app U.1).le }
  counit := { app := fun U => homOfLE (h.adjunction.counit.app U.1).le }

end Topology.IsInducing

