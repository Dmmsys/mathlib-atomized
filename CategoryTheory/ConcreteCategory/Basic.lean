/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov, Anne Baanen,
  Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Concrete categories

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types. We define concrete categories using
`class ConcreteCategory`. To convert an object to a type, write `ToType`. To convert a morphism
to a (bundled) function, write `hom`.

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`,
see the file `Mathlib.CategoryTheory.ConcreteCategory.Forget`

## Implementation notes

We do not use `CoeSort` to convert objects in a concrete category to types, since this would lead
to elaboration mismatches between results taking a `[ConcreteCategory C]` instance and specific
types `C` that hold a `ConcreteCategory C` instance: the first gets a literal `CoeSort.coe` and
the second gets unfolded to the actual `coe` field.

`ToType` and `ToHom` are `abbrev`s so that we do not need to copy over instances such as `Ring`
or `RingHomClass` respectively.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

@[expose] public section


assert_not_exists CategoryTheory.CommSq CategoryTheory.Adjunction

universe w w' v v' v'' u u' u''

namespace CategoryTheory

section ConcreteCategory

/-- A concrete category is a category `C` where objects correspond to types and morphisms to
(bundled) functions between those types.

In other words, it has a fixed faithful functor `forget : C ⥤ Type`.

Note that `ConcreteCategory` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `Category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)

They are specified that order, to avoid unnecessary universe annotations.
-/
/-
**CategoryTheory.ConcreteCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：ConcreteCategory (C : Type u) [Category.{v} C] (FC : outParam <| C -> C ->
 Type*) {CC : outParam <| C -> Type w} [outParam <| forall X Y, FunLike (FC X Y)
 (CC X) (CC Y)] where /-- Convert a morphism of `C` to a bundled function. -/ (h
om : forall {X Y}, (X ⟶ Y) -> FC X Y) /-- Convert a bundled function to a morphi
sm of `C`. -/ (ofHom : forall {X Y}, FC X Y -> (X ⟶ Y)) (hom_ofHom : forall {X Y
} (f : FC X Y), hom (ofHom f) = f
参数：C : Type u；FC : outParam <| C -> C -> Type*；FC X Y；CC X；CC Y；hom : forall {X 
Y}, (X ⟶ Y) -> FC X Y；ofHom : forall {X Y}, FC X Y -> (X ⟶ Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A concrete category is a category `C` where objects correspond to types and morp
hisms to
(bundled) functions between those types.

In other words, it has a fixed faithful functor `forget : C ⥤ Type`.

Note that `ConcreteCategory` potentially depends on three independent universe l
evels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `Category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)

They are specified that order, to avoid unnecessary universe annotations.
-/
class ConcreteCategory (C : Type u) [Category.{v} C]
    (FC : outParam <| C → C → Type*) {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] where
  /-- Convert a morphism of `C` to a bundled function. -/
  (hom : ∀ {X Y}, (X ⟶ Y) → FC X Y)
  /-- Convert a bundled function to a morphism of `C`. -/
  (ofHom : ∀ {X Y}, FC X Y → (X ⟶ Y))
  (hom_ofHom : ∀ {X Y} (f : FC X Y), hom (ofHom f) = f := by cat_disch)
  (ofHom_hom : ∀ {X Y} (f : X ⟶ Y), ofHom (hom f) = f := by cat_disch)
  (id_apply : ∀ {X} (x : CC X), hom (𝟙 X) x = x := by cat_disch)
  (comp_apply : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X),
    hom (f ≫ g) x = hom g (hom f x) := by cat_disch)

attribute [simp] ConcreteCategory.hom_ofHom ConcreteCategory.ofHom_hom

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]

/-- `ToType X` converts the object `X` of the concrete category `C` to a type.

This is an `abbrev` so that instances on `X` (e.g. `Ring`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `CC`.
/-
**CategoryTheory.ToType** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ToType [ConcreteCategory C FC]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ToType X` converts the object `X` of the concrete category `C` to a type.

This is an `abbrev` so that instances on `X` (e.g. `Ring`) do not need to be red
eclared.
-/
abbrev ToType [ConcreteCategory C FC] := CC

/-- `ToHom X Y` is the type of (bundled) functions between objects `X Y : C`.

This is an `abbrev` so that instances (e.g. `RingHomClass`) do not need to be redeclared.
-/
@[nolint unusedArguments] -- Need the instance to trigger unification that finds `FC`.
/-
**CategoryTheory.ToHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ToHom [ConcreteCategory C FC]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ToHom X Y` is the type of (bundled) functions between objects `X Y : C`.

This is an `abbrev` so that instances (e.g. `RingHomClass`) do not need to be re
declared.
-/
abbrev ToHom [ConcreteCategory C FC] := FC

variable [ConcreteCategory C FC]

namespace ConcreteCategory

/-- We can apply morphisms of concrete categories by first casting them down
to the base functions.
-/
/-
**CategoryTheory.ConcreteCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Con
creteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can apply morphisms of concrete categories by first casting them down
to the base functions.
-/
instance {X Y : C} : CoeFun (X ⟶ Y) (fun _ ↦ ToType X → ToType Y) where
  coe f := hom f

/-- A non-instance `FunLike` instance on `X ⟶ Y`. -/
@[deprecated "No replacement" (since := "2026-04-23")]
/-
**CategoryTheory.ConcreteCategory.instFunLike** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.ConcreteCategory`。
形式化陈述：instFunLike {X Y : C} : FunLike (X ⟶ Y) (ToType X) (ToType Y) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-instance `FunLike` instance on `X ⟶ Y`.
-/
abbrev instFunLike {X Y : C} :
    FunLike (X ⟶ Y) (ToType X) (ToType Y) where
  coe f := f
  coe_injective f g h := by
    rw [← ofHom_hom f, ← ofHom_hom g]
    simp_all

@[deprecated (since := "2026-04-03")] alias _root_.CategoryTheory.HasForget.instFunLike :=
  instFunLike

/--
`ConcreteCategory.hom` bundled as an `Equiv`.
-/
/-
**CategoryTheory.ConcreteCategory.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ConcreteCategory`。
形式化陈述：homEquiv {X Y : C} : (X ⟶ Y) ≃ ToHom X Y where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ofHom_hom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…

--- 原说明 ---
`ConcreteCategory.hom` bundled as an `Equiv`.
-/
def homEquiv {X Y : C} : (X ⟶ Y) ≃ ToHom X Y where
  toFun := hom
  invFun := ofHom
  left_inv := ofHom_hom
  right_inv := hom_ofHom
/-
**CategoryTheory.ConcreteCategory.hom_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ConcreteCategory`。
形式化陈述：hom_bijective {X Y : C} : Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma hom_bijective {X Y : C} : Function.Bijective (hom : (X ⟶ Y) → ToHom X Y) :=
  homEquiv.bijective
/-
**CategoryTheory.ConcreteCategory.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ConcreteCategory`。
形式化陈述：hom_injective {X Y : C} : Function.Injective (hom : (X ⟶ Y) -> ToHom X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `CategoryTheory.ConcreteCategory.hom_bijective`：hom_bijective {X Y : C} :
 Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y)
-/
lemma hom_injective {X Y : C} : Function.Injective (hom : (X ⟶ Y) → ToHom X Y) :=
  hom_bijective.injective
/-
**CategoryTheory.ConcreteCategory.hom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ConcreteCategory`。
形式化陈述：hom_surjective {X Y : C} : Function.Surjective (hom : (X ⟶ Y) -> ToHom X Y
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `CategoryTheory.ConcreteCategory.hom_bijective`：hom_bijective {X Y : C} :
 Function.Bijective (hom : (X ⟶ Y) -> ToHom X Y)
-/
lemma hom_surjective {X Y : C} : Function.Surjective (hom : (X ⟶ Y) → ToHom X Y) :=
  hom_bijective.surjective

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations. -/
/-
**CategoryTheory.ConcreteCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
ConcreteCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC] {X Y : C}   {f g : X ⟶ Y}, Cate
goryTheory.ConcreteCategory.hom f = CategoryTheory.ConcreteCategory.hom g → f = 
g
参数：X Y : C；FC X Y；CC X；CC Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ConcreteCategory.hom_injective`：hom_injective {X Y : C} :
 Function.Injective (hom : (X ⟶ Y) -> ToHom X Y)

--- 原说明 ---
In any concrete category, we can test equality of morphisms by pointwise evaluat
ions.
-/
@[ext] lemma ext {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g) : f = g :=
  hom_injective h
/-
**CategoryTheory.ConcreteCategory.coe_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ConcreteCategory`。
形式化陈述：coe_ext {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g)) : f = g
参数：h : ⇑(hom f) = ⇑(hom g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma coe_ext {X Y : C} {f g : X ⟶ Y} (h : ⇑(hom f) = ⇑(hom g)) : f = g :=
  ext (DFunLike.coe_injective h)
/-
**CategoryTheory.ConcreteCategory.ext_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ConcreteCategory`。
形式化陈述：ext_apply {X Y : C} {f g : X ⟶ Y} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma ext_apply {X Y : C} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  ext (DFunLike.ext _ _ h)

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations. -/
@[ext low]
/-
**CategoryTheory.ConcreteCategory.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ConcreteCategory`。
形式化陈述：hom_ext {X Y : C} (f g : X ⟶ Y) (w : forall x, f x = g x) : f = g
参数：f g : X ⟶ Y；w : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
In any concrete category, we can test equality of morphisms by pointwise evaluat
ions.
-/
theorem hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x, f x = g x) : f = g :=
  ext (DFunLike.ext _ _ w)

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
/-
**CategoryTheory.ConcreteCategory.congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ConcreteCategory`。
形式化陈述：congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x
参数：h : f = g；x : ToType X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : ToType X) : f x = g x :=
  congrFun (congrArg (fun k : X ⟶ Y => (k : ToType X → ToType Y)) h) x
/-
**CategoryTheory.ConcreteCategory.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ConcreteCategory`。
形式化陈述：coe_id {X : C} : (𝟙 X : ToType X -> ToType X) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.id_apply`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C 
→ Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_id {X : C} : (𝟙 X : ToType X → ToType X) = id := by
  ext
  simp [ConcreteCategory.id_apply]
/-
**CategoryTheory.ConcreteCategory.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ConcreteCategory`。
形式化陈述：coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X -> ToType
 Z) = g ∘ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X → ToType Z) = g ∘ f := by
  ext
  simp [ConcreteCategory.comp_apply]
/-
**CategoryTheory.ConcreteCategory._root_.CategoryTheory.id_apply** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.CategoryTheory.id_apply {X : C} (x : ToType X) :
    𝟙 X x = x := by
  simp [ConcreteCategory.id_apply _]
/-
**CategoryTheory.ConcreteCategory._root_.CategoryTheory.comp_apply** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.CategoryTheory.comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ToType X) : (f ≫ g) x = g (f x) := by
  simp [ConcreteCategory.comp_apply]

@[deprecated (since := "2026-02-06")] alias _root_.CategoryTheory.comp_apply' :=
  _root_.CategoryTheory.comp_apply
/-
**CategoryTheory.ConcreteCategory.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ConcreteCategory`。
形式化陈述：congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x
'
参数：f : X ⟶ Y；h : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_arg {X Y : C} (f : X ⟶ Y) {x x' : ToType X} (h : x = x') : f x = f x' :=
  congrArg (f : ToType X → ToType Y) h

end ConcreteCategory

/-
**CategoryTheory.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_id {X : C} : (𝟙 X : ToType X -> ToType X) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_id {X : C} : (𝟙 X : ToType X → ToType X) = id := by
  ext
  simp
/-
**CategoryTheory.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X -> ToType
 Z) = g ∘ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : ToType X → ToType Z) = g ∘ f := by
  ext
  simp

open ConcreteCategory

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InducedCategory.concreteCategory** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.InducedCategory`。
形式化陈述：{C : Type u} →   {D : Type u'} →     [inst : CategoryTheory.Category.{v', 
u'} D] →       {FD : D → D → Type u_2} →         {CD : D → Type w} →           [
inst_1 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)] →             [CategoryTheo
ry.ConcreteCategory D FD] →               (f : C → D) →                 Category
Theory.ConcreteCategory (CategoryTheory.InducedCategory D f) fun X Y => FD (f X)
 (f Y)
参数：X Y : D；FD X Y；CD X；CD Y；f : C → D；CategoryTheory.InducedCategory D f；f X；f Y
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InducedCategory.concreteCategory {C : Type u} {D : Type u'} [Category.{v'} D]
    {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{w} D FD] (f : C → D) :
    ConcreteCategory (InducedCategory D f) (fun X Y => FD (f X) (f Y)) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _
/-
**CategoryTheory.ObjectProperty.FullSubcategory.concreteCategory** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.ObjectProperty.FullSubcategory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {FC : C →
 C → Type u_2} →       {CC : C → Type w} →         [inst_1 : (X Y : C) → FunLike
 (FC X Y) (CC X) (CC Y)] →           [CategoryTheory.ConcreteCategory C FC] →   
          (P : CategoryTheory.ObjectProperty C) →               CategoryTheory.C
oncreteCategory P.FullSubcategory fun X Y => FC X.obj Y.obj
参数：X Y : C；FC X Y；CC X；CC Y；P : CategoryTheory.ObjectProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ObjectProperty.FullSubcategory.concreteCategory {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} C FC]
    (P : ObjectProperty C) : ConcreteCategory P.FullSubcategory (fun X Y => FC X.1 Y.1) where
  hom f := hom f.hom
  ofHom g := homMk (ofHom g)
  hom_ofHom _ := hom_ofHom _
  ofHom_hom _ := by ext; simp [ofHom_hom]
  comp_apply _ _ _ := ConcreteCategory.comp_apply _ _ _
  id_apply _ := ConcreteCategory.id_apply _

@[deprecated (since := "2026-04-18")] alias FullSubcategory.concreteCategory :=
  ObjectProperty.FullSubcategory.concreteCategory

end ConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {D : Type*} [Category* D] {FD : outParam <| D → D → Type*}
    {CD : outParam <| D → Type w}
    [outParam <| ∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

-- TODO: generate this lemma with the `elementwise` attribute.
@[simp]
/-
**CategoryTheory.NatTrans.naturality_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   {FD : outParam (D → D → Type u_2
)} {CD : outParam (D → Type w)}   [inst_2 : outParam ((X Y : D) → FunLike (FD X 
Y) (CD X) (CD Y))] [inst_3 : CategoryTheory.ConcreteCategory D FD]   {F G : Cate
goryTheory.Functor C D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y) (x : CategoryTheory.To
Type (F.obj X)),   (CategoryTheory.ConcreteCategory.hom (φ.app Y)) ((CategoryThe
ory.ConcreteCategory.hom (F.map f)) x) =     (CategoryTheory.ConcreteCategory.ho
m (G.map f)) ((CategoryTheory.ConcreteCategory.hom (φ.app X)) x)
参数：D → D → Type u_2；D → Type w；(X Y : D) → FunLike (FD X Y) (CD X) (CD Y)；φ : F 
⟶ G；f : X ⟶ Y；x : CategoryTheory.ToType (F.obj X)；CategoryTheory.ConcreteCategor
y.hom (φ.app Y)；(CategoryTheory.ConcreteCategory.hom (F.map f)) x；CategoryTheory
.ConcreteCategory.hom (G.map f)；(CategoryTheory.ConcreteCategory.hom (φ.app X)) 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (x : ToType (F.obj X)) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simp [← CategoryTheory.comp_apply]

end CategoryTheory

