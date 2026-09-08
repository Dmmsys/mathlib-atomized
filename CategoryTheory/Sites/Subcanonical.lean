/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.CategoryTheory.Sites.Continuous
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.val.obj X`.
-/
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.obj.
obj (op X)
参数：Type v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence between natural transformations from the yoneda embedding (to th
e sheaf category)
and elements of `F.val.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_apply** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) 
: yonedaEquiv J f = f.hom.app (op X) (𝟙 X)
参数：Type v；f : J.yoneda.obj X ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.hom.app (op X) (𝟙 X) :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_symm_app_apply** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.obj.obj (
op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) : dsimp% (J.yonedaEquiv.symm x).hom.app Y f = 
F.obj.map f.op x
参数：Type v；x : F.obj.obj (op X)；Y : Cᵒᵖ；f : Y.unop ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.obj.obj (op X))
    (Y : Cᵒᵖ) (f : Y.unop ⟶ X) : dsimp% (J.yonedaEquiv.symm x).hom.app Y f = F.obj.map f.op x :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- See also `yonedaEquiv_naturality'` for a more general version. -/
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj 
X ⟶ F) (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.
map g ≫ f)
参数：Type v；f : J.yoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_naturality`：yonedaEquiv_naturality {X Y : C} 
{F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) : F.map g.op (yonedaEquiv
 f) = yonedaEquiv (yoneda.m…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β

--- 原说明 ---
See also `yonedaEquiv_naturality'` for a more general version.
-/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality'** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.o
bj (unop X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.
yoneda.map g.unop ≫ f)
参数：Type v；f : J.yoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality`：yonedaEquiv_
naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) (g : Y ⟶ X)
 : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEq…

--- 原说明 ---
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strict
ly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes prefera
ble because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F)
 (β : F ⟶ G) : J.yonedaEquiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv α)
参数：Type v；α : J.yoneda.obj X ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv α) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_yoneda_map** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map
 f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_apply`：yonedaEquiv_apply
 {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) : yonedaEquiv J f = f.h
om.app (op X) (𝟙 X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_symm_naturality_left** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Typ
e v)) (x : F.obj.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEqui
v.symm ((F.obj.map f.op) x)
参数：f : X' ⟶ X；F : Sheaf J (Type v)；x : F.obj.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_comp`：yonedaEquiv_comp {
X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) : J.yonedaE
quiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv …
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_yoneda_map`：yonedaEquiv_
yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.obj.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.obj.map f.op) x) := by
  apply J.yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simp
  rfl
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_symm_naturality_right** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F
 ⟶ F') (x : F.obj.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.ho
m.app ⟨X⟩ x)
参数：X : C；Type v；f : F ⟶ F'；x : F.obj.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.obj.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
/-
**CategoryTheory.GrothendieckTopology.map_yonedaEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) 
(g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = f.hom.app (op Y) g
参数：Type v；f : J.yoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality`：yonedaEquiv_
naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) (g : Y ⟶ X)
 : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEq…
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_comp`：yonedaEquiv_comp {
X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) : J.yonedaE
quiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv …
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_yoneda_map`：yonedaEquiv_
yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f

--- 原说明 ---
See also `map_yonedaEquiv'` for a more general version.
-/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = f.hom.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
/-
**CategoryTheory.GrothendieckTopology.map_yonedaEquiv'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (uno
p X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = f.hom.app Y g.unop
参数：Type v；f : J.yoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality'`：yonedaEquiv
_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F) 
(g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.y…
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_comp`：yonedaEquiv_comp {
X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) : J.yonedaE
quiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv …
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_yoneda_map`：yonedaEquiv_
yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f

--- 原说明 ---
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more
 general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = f.hom.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]
/-
**CategoryTheory.GrothendieckTopology.yonedaEquiv_symm_map** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F
.obj.obj X) : J.yonedaEquiv.symm (F.obj.map f t) = J.yoneda.map f.unop ≫ J.yoned
aEquiv.symm t
参数：f : X ⟶ Y；Type v；t : F.obj.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality'`：yonedaEquiv
_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F) 
(g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.y…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.obj.obj X) :
    J.yonedaEquiv.symm (F.obj.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
/-
**CategoryTheory.GrothendieckTopology.hom_ext_yoneda** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q} (h : forall (X : C) 
(p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
参数：Type v；h : forall (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with m
orphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The Yoneda lemma for sheaves. -/
@[simps! +dsimpLhs hom_app_app_hom_apply_down inv_app_app]
/-
**CategoryTheory.GrothendieckTopology.yonedaOpCompCoyoneda** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：yonedaOpCompCoyoneda : J.yoneda.op ⋙ coyoneda ≅ evaluation Cᵒᵖ (Type v) ⋙ 
(whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ (whiskeringLeft _ _ _).obj (sheaf
ToPresheaf _ _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda lemma for sheaves.
-/
def yonedaOpCompCoyoneda :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

/-- A version of `yonedaEquiv` for `uliftYoneda`. -/
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} : ((uliftYoneda.{
v'} J).obj X ⟶ F) ≃ F.obj.obj (op X)
参数：Type (max v v')。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A version of `yonedaEquiv` for `uliftYoneda`.
-/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_apply** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))} (f : J.ulif
tYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.hom.app (op X) ⟨𝟙 X⟩
参数：Type (max v v')；f : J.uliftYoneda.obj X ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.hom.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_symm_app_apply** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))} (x
 : F.obj.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) : dsimp% (J.uliftYonedaEquiv.sym
m x).hom.app Y ⟨f⟩ = F.obj.map f.op x
参数：Type (max v v')；x : F.obj.obj (op X)；Y : Cᵒᵖ；f : Y.unop ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.obj.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    dsimp% (J.uliftYonedaEquiv.symm x).hom.app Y ⟨f⟩ = F.obj.map f.op x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- See also `uliftYonedaEquiv_naturality'` for a more general version. -/
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))} (f :
 J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) : F.obj.map g.op (J.uliftYonedaEquiv f) = 
J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f)
参数：Type (max v v')；f : J.uliftYoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `uliftYonedaEquiv_naturality'` for a more general version.
-/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.obj.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.hom.app (op X) ≫ F.obj.map g.op) ⟨𝟙 X⟩ = f.hom.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.hom.naturality]
  simp [uliftYoneda]

/-- Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically strictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is sometimes
preferable because it can avoid the "motive is not type correct" error. -/
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality'** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))} (
f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.uliftYonedaEqui
v f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f)
参数：Type (max v v')；f : J.uliftYoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality`：uliftYo
nedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))} (f : J.uliftYoned
a.obj X ⟶ F) (g : Y ⟶ X) : F.obj.map g.op (J.uliftYon…

--- 原说明 ---
Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically s
trictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is
 sometimes
preferable because it can avoid the "motive is not type correct" error.
-/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_comp** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uli
ftYoneda.obj X ⟶ F) (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.hom.app _ (J.ul
iftYonedaEquiv α)
参数：Type (max v v')；α : J.uliftYoneda.obj X ⟶ F；β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.hom.app _ (J.uliftYonedaEquiv α) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) : (uliftYonedaEquiv
.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_apply`：uliftYonedaE
quiv_apply {X : C} {F : Sheaf J (Type (max v v'))} (f : J.uliftYoneda.obj X ⟶ F)
 : uliftYonedaEquiv.{v'} J f = f.hom.app (op X) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.sheafCompose_map_hom`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.uliftFunctor_map`：∀ {X x : Type u} (f : X ⟶ x),   Categor
yTheory.uliftFunctor.{v, u}.map f =     TypeCat.ofHom fun x_1 => { down := (Cate
goryTheory.ConcreteCa…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_symm_naturality_left** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J
 (Type (max v v'))) (x : F.obj.obj ⟨X⟩) : J.uliftYoneda.map f ≫ J.uliftYonedaEqu
iv.symm x = J.uliftYonedaEquiv.symm ((F.obj.map f.op) x)
参数：f : X' ⟶ X；F : Sheaf J (Type (max v v'))；x : F.obj.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map`：ul
iftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) : (uliftYonedaEquiv.{v'} J)
 (J.uliftYoneda.map f) = ⟨f⟩
-/
lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.obj.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.obj.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_symm_naturality_right** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max 
v v'))} (f : F ⟶ F') (x : F.obj.obj ⟨X⟩) : J.uliftYonedaEquiv.symm x ≫ f = J.uli
ftYonedaEquiv.symm (f.hom.app ⟨X⟩ x)
参数：X : C；Type (max v v')；f : F ⟶ F'；x : F.obj.obj ⟨X⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.obj.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
/-
**CategoryTheory.GrothendieckTopology.map_uliftYonedaEquiv** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))} (f : J.ulif
tYoneda.obj X ⟶ F) (g : Y ⟶ X) : F.obj.map g.op (J.uliftYonedaEquiv f) = f.hom.a
pp (op Y) ⟨g⟩
参数：Type (max v v')；f : J.uliftYoneda.obj X ⟶ F；g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality`：uliftYo
nedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))} (f : J.uliftYoned
a.obj X ⟶ F) (g : Y ⟶ X) : F.obj.map g.op (J.uliftYon…
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_comp`：uliftYonedaEq
uiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
 (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.h…
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map`：ul
iftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) : (uliftYonedaEquiv.{v'} J)
 (J.uliftYoneda.map f) = ⟨f⟩

--- 原说明 ---
See also `map_yonedaEquiv'` for a more general version.
-/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.obj.map g.op (J.uliftYonedaEquiv f) = f.hom.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

/-- Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
/-
**CategoryTheory.GrothendieckTopology.map_uliftYonedaEquiv'** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))} (f : J.u
liftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.uliftYonedaEquiv f) = 
f.hom.app Y ⟨g.unop⟩
参数：Type (max v v')；f : J.uliftYoneda.obj (unop X) ⟶ F；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality'`：uliftY
onedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))} (f : J.uliftY
oneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.u…
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_comp`：uliftYonedaEq
uiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
 (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.h…
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map`：ul
iftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) : (uliftYonedaEquiv.{v'} J)
 (J.uliftYoneda.map f) = ⟨f⟩

--- 原说明 ---
Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly
 more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable 
because it
can avoid the "motive is not type correct" error.
-/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = f.hom.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality', uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_symm_map** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max 
v v'))} (t : F.obj.obj X) : J.uliftYonedaEquiv.symm (F.obj.map f t) = J.uliftYon
eda.map f.unop ≫ J.uliftYonedaEquiv.symm t
参数：f : X ⟶ Y；Type (max v v')；t : F.obj.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.uliftYonedaEquiv_naturality'`：uliftY
onedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))} (f : J.uliftY
oneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : F.obj.map g (J.u…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.obj.obj X) : J.uliftYonedaEquiv.symm (F.obj.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
/-
**CategoryTheory.GrothendieckTopology.hom_ext_uliftYoneda** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q} (h : f
orall (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) : f = g
参数：Type (max v v')；h : forall (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫
 g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of the Yoneda lemma for sheaves with a raise in the universe level. -/
@[simps! +dsimpLhs -isSimp]
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaOpCompCoyoneda** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaOpCompCoyoneda : J.uliftYoneda.op ⋙ coyoneda ≅ evaluation Cᵒᵖ (
Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ (whiskeringLeft 
_ _ _).obj (sheafToPresheaf _ _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of the Yoneda lemma for sheaves with a raise in the universe level.
-/
def uliftYonedaOpCompCoyoneda :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

attribute [simp] uliftYonedaOpCompCoyoneda_hom_app_app_hom_apply_down

-- @[simp]
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaOpCompCoyoneda_inv_app_app** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaOpCompCoyoneda_inv_app_app (X : Cᵒᵖ) (F : Sheaf J (Type max v v
')) (s : ULift.{u} (F.obj.obj X)) : dsimp% (J.uliftYonedaOpCompCoyoneda.inv.app 
X).app F s = J.uliftYonedaEquiv.symm s.down
参数：X : Cᵒᵖ；F : Sheaf J (Type max v v')；s : ULift.{u} (F.obj.obj X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaOpCompCoyoneda_inv_app_app (X : Cᵒᵖ) (F : Sheaf J (Type max v v'))
    (s : ULift.{u} (F.obj.obj X)) :
    dsimp% (J.uliftYonedaOpCompCoyoneda.inv.app X).app F s = J.uliftYonedaEquiv.symm s.down :=
  rfl
/-
**CategoryTheory.GrothendieckTopology.uliftYonedaOpCompCoyoneda_app_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：uliftYonedaOpCompCoyoneda_app_app (X : Cᵒᵖ) (F : Sheaf J (Type (max v v'))
) : (J.uliftYonedaOpCompCoyoneda.app X).app F = (J.uliftYonedaEquiv.trans Equiv.
ulift.symm).toIso
参数：X : Cᵒᵖ；F : Sheaf J (Type (max v v'))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uliftYonedaOpCompCoyoneda_app_app (X : Cᵒᵖ) (F : Sheaf J (Type (max v v'))) :
    (J.uliftYonedaOpCompCoyoneda.app X).app F = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

open Limits
/-
**CategoryTheory.GrothendieckTopology.preservesLimitsOfSize_yoneda** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesLimitsOfSize_yoneda : PreservesLimitsOfSize J.yoneda
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
instance preservesLimitsOfSize_yoneda : PreservesLimitsOfSize J.yoneda := by
  refine ⟨fun {I} _ ↦ ?_⟩
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
    inferInstanceAs <| PreservesLimitsOfShape I CategoryTheory.yoneda
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Let `{ Xᵢ ⟶ Y }` be a family of pairwise disjoint maps that form a cover in `J`. Then its
image under the yoneda embedding to `J`-sheaves is a coproduct.
-/
/-
**CategoryTheory.GrothendieckTopology.isColimitCofanMkYoneda** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isColimitCofanMkYoneda {ι : Type*} (X : ι -> C) {c : Cofan X} (H : (Sieve.
ofArrows _ c.inj) in J c.pt) [forall (i : ι), Mono (c.inj i)] (hempty : (Y : C) 
-> IsInitial Y -> ⊥ in J Y) (hdisj : forall {i j : ι} (_ : i != j) {Y : C} (a : 
Y ⟶ X i) (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j -> Nonempty (IsInitial Y)) : I
sColimit (Cofan.mk _ fun i => J.yoneda.map (c.inj i))
参数：X : ι -> C；H : (Sieve.ofArrows _ c.inj) in J c.pt；i : ι；c.inj i；hempty : (Y :
 C) -> IsInitial Y -> ⊥ in J Y；hdisj : forall {i j : ι} (_ : i != j) {Y : C} (a 
: Y ⟶ X i) (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j -> Nonempty (IsInitial Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `{ Xᵢ ⟶ Y }` be a family of pairwise disjoint maps that form a cover in `J`.
 Then its
image under the yoneda embedding to `J`-sheaves is a coproduct.
-/
noncomputable def isColimitCofanMkYoneda {ι : Type*} (X : ι → C) {c : Cofan X}
    (H : (Sieve.ofArrows _ c.inj) ∈ J c.pt) [∀ (i : ι), Mono (c.inj i)]
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y)
    (hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
      (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i ↦ J.yoneda.map (c.inj i)) := by
  have heq (s : Cofan fun i ↦ J.yoneda.obj (X i))
      {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (hab : a ≫ c.inj i = b ≫ c.inj j) :
      (s.inj i).hom.app (op Y) a = (s.inj j).hom.app (op Y) b := by
    by_cases h : i = j
    · subst h
      rw [(cancel_mono _).mp hab]
    · obtain ⟨h⟩ := hdisj h a b hab
      have := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y h))
      exact Subsingleton.elim _ _
  refine Cofan.IsColimit.mk _ (fun s ↦ ⟨?_⟩) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · refine (s.pt.2.isSheafFor _ H).extend ?_
    refine ⟨fun Y ↦ ↾fun g ↦ ((s.inj (Sieve.ofArrows.i g.2)).hom.app Y)
      (Sieve.ofArrows.h g.2), ?_⟩
    intro ⟨Y⟩ ⟨Z⟩ ⟨(g : Z ⟶ Y)⟩
    ext u
    simp only [Sieve.functor_obj, Sieve.generate_apply, Sieve.functor_map, Quiver.Hom.unop_op',
      TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
      ← heq s (g ≫ Sieve.ofArrows.h u.2)
      (Sieve.ofArrows.h <| Sieve.downward_closed _ u.2 g) (by simp)]
    exact ConcreteCategory.congr_hom ((s.inj _).hom.naturality g.op) _
  · ext : 1
    let u (j : ι) : CategoryTheory.yoneda.obj (X j) ⟶ (Sieve.ofArrows _ c.inj).functor :=
      (Sieve.ofArrows _ c.inj).toFunctor (c.inj j) (Sieve.ofArrows_mk _ _ j)
    have (j : ι) : u j ≫ (Sieve.ofArrows _ c.inj).functorInclusion =
      CategoryTheory.yoneda.map (c.inj j) := rfl
    dsimp
    simp only [← this, Category.assoc, Presieve.IsSheafFor.functorInclusion_comp_extend]
    ext Z (g : Z.unop ⟶ X j)
    have h : Sieve.ofArrows X c.inj (g ≫ c.inj j) :=
      Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    exact heq s (Sieve.ofArrows.h h) g (by simp)
  · ext : 1
    dsimp
    apply Presieve.IsSheafFor.unique_extend
    ext Y ⟨g, hg⟩
    simp [← hm (Sieve.ofArrows.i hg)]

/-- If the coproduct inclusions form a covering of `J` and coproducts are disjoint,
the yoneda embedding to `J`-sheaves preserves coproducts. -/
/-
**CategoryTheory.GrothendieckTopology.preservesColimitsOfShape_yoneda_of_ofArrow
s_inj_mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem {ι : Type*} [Coproduct
sOfShapeDisjoint C ι] [HasPullbacks C] [HasStrictInitialObjects C] (hcov : foral
l {X : ι -> C} {c : Cofan X} (_ : IsColimit c), Sieve.ofArrows X c.inj in J c.pt
) (htriv : forall (Y : C), IsInitial Y -> ⊥ in J Y) : PreservesColimitsOfShape (
Discrete ι) J.yoneda
参数：hcov : forall {X : ι -> C} {c : Cofan X} (_ : IsColimit c), Sieve.ofArrows X 
c.inj in J c.pt；htriv : forall (Y : C), IsInitial Y -> ⊥ in J Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_discrete`：preservesCol
imitsOfShape_of_discrete (F : C ⥤ D) [forall (f : J -> C), PreservesColimit (Dis
crete.functor f) F] : PreservesColimitsOfShape (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Mono.of_coproductDisjoint`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {ι : Type u_1} {X : ι → C}   [CategoryTheory.Limits.C
oproductDisjoint X] {c : Categ…
· 使用定理 `CategoryTheory.Limits.CoproductsOfShapeDisjoint.coproductDisjoint`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {ι : Type u_2}   [self
 : CategoryTheory.Limits.CoproductsOfShapeDisjoint C ι]…
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…

--- 原说明 ---
If the coproduct inclusions form a covering of `J` and coproducts are disjoint,
the yoneda embedding to `J`-sheaves preserves coproducts.
-/
lemma preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem {ι : Type*}
    [CoproductsOfShapeDisjoint C ι] [HasPullbacks C] [HasStrictInitialObjects C]
    (hcov : ∀ {X : ι → C} {c : Cofan X} (_ : IsColimit c), Sieve.ofArrows X c.inj ∈ J c.pt)
    (htriv : ∀ (Y : C), IsInitial Y → ⊥ ∈ J Y) :
    PreservesColimitsOfShape (Discrete ι) J.yoneda := by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X ↦ ⟨fun {c : Cofan X} hc ↦ ⟨(Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  have (i : ι) : Mono (c.inj i) := .of_coproductDisjoint hc _
  refine isColimitCofanMkYoneda _ _ (hcov hc) htriv fun hij Y a b hab ↦ ⟨?_⟩
  exact .ofCoproductDisjointOfCommSq hij hc _ _ hab

variable {D : Type*} [Category.{v'} D] (F : C ⥤ D) (J : GrothendieckTopology C)
  (K : GrothendieckTopology D)
/-
**CategoryTheory.GrothendieckTopology.subcanonical_of_full_of_faithful** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：subcanonical_of_full_of_faithful [F.Full] [F.Faithful] [Functor.IsContinuo
us F J K] [K.Subcanonical] : J.Subcanonical
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_iso_iff`：isSheaf_of_iso_iff {P P' : C
ᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P'
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_isSheaf`：op_comp_isSheaf_of_is
Sheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) : Presheaf.I
sSheaf J (F.op ⋙ P)
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresenta
ble`：isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J] (P
 : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Functor.instIsRepresentableObjOppositeTypeUliftYoneda`：∀ 
{C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C},   (CategoryTh
eory.uliftYoneda.{w, v₁, u₁}.obj X).IsRepresentable
· 使用引理 `CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`：isSheaf_iff_of_nat_equ
iv : Presieve.IsSheaf J P₁ ↔ Presieve.IsSheaf J P₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma subcanonical_of_full_of_faithful [F.Full] [F.Faithful]
    [Functor.IsContinuous F J K] [K.Subcanonical] :
    J.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun Y ↦ ?_
  suffices h : Presieve.IsSheaf J (CategoryTheory.uliftYoneda.{v'}.obj Y) by
    rwa [Presieve.isSheaf_iff_of_nat_equiv]
    · intro
      exact Equiv.ulift.symm
    · intros
      rfl
  rw [← isSheaf_iff_isSheaf_of_type, Presheaf.isSheaf_of_iso_iff
    ((Functor.FullyFaithful.ofFullyFaithful F).compUliftYonedaCompWhiskeringLeft.app Y).symm]
  refine F.op_comp_isSheaf_of_isSheaf J K _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  apply GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable

end CategoryTheory.GrothendieckTopology

