/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `Comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `Comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

Comma, Slice, Coslice, Over, Under
-/

@[expose] public section


namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u₁} [Category.{v₁} T]
variable {D : Type u₂} [Category.{v₂} D]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles. -/
@[stacks 001G, implicit_reducible]
/-
**CategoryTheory.Over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Over (X : T)
参数：X : T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The over category has as objects arrows in `T` with codomain `X` and as morphism
s commutative
triangles.
-/
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X

/-- The type of morphisms in the category `Over`. -/
/-
**CategoryTheory.Over.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {X : T
} → CategoryTheory.Over X → CategoryTheory.Over X → Type (max v₁ 0)
参数：max v₁ 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Over`.
-/
protected def Over.Hom {X : T} (f g : Over X) := CommaMorphism f g
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : T} : Category (Over X) where
  Hom := Over.Hom
  __ := (inferInstance : Category (Comma _ _))

-- Satisfying the inhabited linter
/-
**CategoryTheory.Over.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] → [inst_1 : 
Inhabited T] → Inhabited (CategoryTheory.Over default)
参数：CategoryTheory.Over default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Over

variable {X : T}

/-- The underlying object of an object in `Over X`. -/
/-
**CategoryTheory.Over.left** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：left (f : Over X) : T
参数：f : Over X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of an object in `Over X`.
-/
abbrev left (f : Over X) : T := Comma.left f

/-- The morphism that is part of an object in `Over X`. -/
/-
**CategoryTheory.Over.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：hom (f : Over X) : f.left ⟶ X
参数：f : Over X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism that is part of an object in `Over X`.
-/
abbrev hom (f : Over X) : f.left ⟶ X := Comma.hom f

variable {f g : Over X} (φ : f ⟶ g)

/-- The morphism that is part of a morphism in `Over X`. -/
/-
**CategoryTheory.Over.Hom.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over.Ho
m`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] → {X : T} → 
{f g : CategoryTheory.Over X} → (f ⟶ g) → (f.left ⟶ g.left)
参数：f ⟶ g；f.left ⟶ g.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism that is part of a morphism in `Over X`.
-/
abbrev Hom.left : f.left ⟶ g.left := CommaMorphism.left φ

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：w : φ.left ≫ g.hom = f.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
theorem w : φ.left ≫ g.hom = f.hom := by
  simpa using (CommaMorphism.w φ)

@[reassoc]
/-
**CategoryTheory.Over.Hom.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over.Hom`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} {f g :
 CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheory.CategoryStruct.comp (Categ
oryTheory.Over.Hom.left φ) g.hom = f.hom
参数：φ : f ⟶ g；CategoryTheory.Over.Hom.left φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
lemma Hom.w : φ.left ≫ g.hom = f.hom := Over.w φ

@[ext]
/-
**CategoryTheory.Over.OverMorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Over.OverMorphism`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} {U V :
 CategoryTheory.Over X} {f g : U ⟶ V},   CategoryTheory.Over.Hom.left f = Catego
ryTheory.Over.Hom.left g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]
/-
**CategoryTheory.Over.over_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：over_right (U : Over X) : U.right = ⟨⟨⟩⟩
参数：U : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only

@[simp]
/-
**CategoryTheory.Over.id_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：id_left (U : Over X) : Hom.left (𝟙 U) = 𝟙 U.left
参数：U : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_left (U : Over X) : Hom.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.Over.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left
 ≫ g.left
参数：a b c : Over X；f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps! left hom, implicit_reducible]
/-
**CategoryTheory.Over.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mk {X Y : T} (f : Y ⟶ X) : Over X
参数：f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an object in the over category, it suffices to give a morphism with codo
main `X`.
-/
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
be a global instance, but it is sometimes useful. -/
@[instance_reducible]
/-
**CategoryTheory.Over.coeFromHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can set up a coercion from arrows with codomain `X` to `over X`. This most li
kely should not
be a global instance, but it is sometimes useful.
-/
def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk

section

attribute [local instance] coeFromHom

@[simp]
/-
**CategoryTheory.Over.coe_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f
参数：f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
triangle. -/
@[simps! left]
/-
**CategoryTheory.Over.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom
参数：f : U.left ⟶ V.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give a morphism in the over category, it suffices to give an arrow fitting in
 a commutative
triangle.
-/
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch) : U ⟶ V :=
  CostructuredArrow.homMk f w

@[simp]
/-
**CategoryTheory.Over.homMk_eta** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：homMk_eta {U V : Over X} (f : U ⟶ V) (h) : homMk f.left h = f
参数：f : U ⟶ V；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_eta {U V : Over X} (f : U ⟶ V) (h) :
    homMk f.left h = f :=
  rfl

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
/-
**CategoryTheory.Over.homMk_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：homMk_comp {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w
_f w_g) : homMk (f ≫ g) (by simp_all) = homMk f w_f ≫ homMk g w_g
参数：f : U.left ⟶ V.left；g : V.left ⟶ W.left；w_f w_g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equ
ivalence.
-/
lemma homMk_comp {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g) :
    homMk (f ≫ g) (by simp_all) = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_left inv_left]
/-
**CategoryTheory.Over.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom
参数：hl : f.left ≅ g.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in the over category given isomorphisms of the objects 
whose forward
direction gives a commutative triangle.
-/
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw

@[simp]
/-
**CategoryTheory.Over.eqToHom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：eqToHom_left {f g : Over X} (h : f = g) : (eqToHom h).left = eqToHom (by r
w [h])
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_left {f g : Over X} (h : f = g) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.hom_left_inv_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：hom_left_inv_left {f g : Over X} (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙
 f.left
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_left_inv_left {f g : Over X} (e : f ≅ g) :
    e.hom.left ≫ e.inv.left = 𝟙 f.left := by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.inv_left_hom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：inv_left_hom_left {f g : Over X} (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙
 g.left
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_left_hom_left {f g : Over X} (e : f ≅ g) :
    e.inv.left ≫ e.hom.left = 𝟙 g.left := by
  simp [← Over.comp_left]
/-
**CategoryTheory.Over.forall_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：forall_iff (P : Over X -> Prop) : (forall Y, P Y) ↔ (forall (Y) (f : Y ⟶ X
), P (.mk f))
参数：P : Over X -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma forall_iff (P : Over X → Prop) :
    (∀ Y, P Y) ↔ (∀ (Y) (f : Y ⟶ X), P (.mk f)) := by
  aesop
/-
**CategoryTheory.Over.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ov
er`。
形式化陈述：mk_surjective {S : T} (X : Over S) : exists (Y : T) (f : Y ⟶ S), Over.mk f
 = X
参数：X : Over S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective {S : T} (X : Over S) :
    ∃ (Y : T) (f : Y ⟶ S), Over.mk f = X :=
  ⟨_, X.hom, rfl⟩
/-
**CategoryTheory.Over.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Over`。
形式化陈述：homMk_surjective {S : T} {X Y : Over S} (f : X ⟶ Y) : exists (g : X.left ⟶
 Y.left) (hg : g ≫ Y.hom = X.hom), f = Over.homMk g
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
lemma homMk_surjective
    {S : T} {X Y : Over S} (f : X ⟶ Y) :
    ∃ (g : X.left ⟶ Y.left) (hg : g ≫ Y.hom = X.hom), f = Over.homMk g :=
  ⟨f.left, by simp⟩

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
@[stacks 001G]
/-
**CategoryTheory.Over.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：forget : Over X ⥤ T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor mapping an arrow to its domain.
-/
def forget : Over X ⥤ T :=
  Comma.fst _ _

end

@[simp]
/-
**CategoryTheory.Over.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：forget_obj {U : Over X} : (forget X).obj U = U.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl

@[simp]
/-
**CategoryTheory.Over.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`. -/
@[simps]
/-
**CategoryTheory.Over.forgetCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：forgetCocone (X : T) : Limits.Cocone (forget X)
参数：X : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`
.
-/
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }

/-- A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way. -/
@[stacks 001G, implicit_reducible]
/-
**CategoryTheory.Over.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way.
-/
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
/-
**CategoryTheory.Over.map_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：map_obj_left : ((map f).obj U).left = U.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[simp]
/-
**CategoryTheory.Over.map_obj_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over
`。
形式化陈述：map_obj_hom : ((map f).obj U).hom = U.hom ≫ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl

@[simp]
/-
**CategoryTheory.Over.map_map_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：map_map_left : ((map f).map g).left = g.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

/-- If `f` is an isomorphism, `map f` is an equivalence of categories. -/
/-
**CategoryTheory.Over.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapIso (f : X ≅ Y) : Over X ≌ Over Y
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an isomorphism, `map f` is an equivalence of categories.
-/
def mapIso (f : X ≅ Y) : Over X ≌ Over Y :=
  Comma.mapRightIso _ <| Discrete.natIso fun _ ↦ f
/-
**CategoryTheory.Over.mapIso_functor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X Y : T} (f :
 X ≅ Y),   (CategoryTheory.Over.mapIso f).functor = CategoryTheory.Over.map f.ho
m
参数：f : X ≅ Y；CategoryTheory.Over.mapIso f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
/-
**CategoryTheory.Over.mapIso_inverse** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X Y : T} (f :
 X ≅ Y),   (CategoryTheory.Over.mapIso f).inverse = CategoryTheory.Over.map f.in
v
参数：f : X ≅ Y；CategoryTheory.Over.mapIso f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIso f] : (Over.map f).IsEquivalence := (Over.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that over categories assemble into a
functor `mapFunctor : T ⥤ Cat`.

These equalities between functors are then converted to natural
isomorphisms using `eqToIso`. Such natural isomorphisms could be
obtained directly using `Iso.refl` but this method will have
better computational properties, when used, for instance, in
developing the theory of Beck-Chevalley transformations.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism arising from `mapForget_eq`. -/
@[simps!]
/-
**CategoryTheory.Over.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _
参数：Y : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism arising from `mapForget_eq`.
-/
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Mapping by the identity morphism is just the identity functor. -/
/-
**CategoryTheory.Over.mapId_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _
参数：Y : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Over.eqToHom_left`：eqToHom_left {f g : Over X} (h : f = g
) : (eqToHom h).left = eqToHom (by rw [h])
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping by the identity morphism is just the identity functor.
-/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ :=
  Functor.ext_of_iso (mapId Y) (fun _ ↦ by simp [map, Comma.mapRight]; rfl)
    (fun _ ↦ by ext; simp [eqToHom_left])

/-- Mapping by `f` and then forgetting is the same as forgetting. -/
/-
**CategoryTheory.Over.mapForget_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：mapForget_eq {X Y : T} (f : X ⟶ Y) : (map f) ⋙ (forget Y) = (forget X)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping by `f` and then forgetting is the same as forgetting.
-/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) = (forget X) := rfl

/-- The natural isomorphism arising from `mapForget_eq`. -/
/-
**CategoryTheory.Over.mapForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapForget {X Y : T} (f : X ⟶ Y) : (map f) ⋙ (forget Y) ≅ (forget X)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.mapForget_eq`：mapForget_eq {X Y : T} (f : X ⟶ Y) : (
map f) ⋙ (forget Y) = (forget X)

--- 原说明 ---
The natural isomorphism arising from `mapForget_eq`.
-/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) ≅ (forget X) := eqToIso (mapForget_eq f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
/-
**CategoryTheory.Over.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism arising from `mapComp_eq`.
-/
def mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
/-
**CategoryTheory.Over.mapComp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = (map f) ⋙ (
map g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用引理 `CategoryTheory.Over.eqToHom_left`：eqToHom_left {f g : Over X} (h : f = g
) : (eqToHom h).left = eqToHom (by rw [h])

--- 原说明 ---
Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by 
`g`.
-/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f) ⋙ (map g) :=
  Functor.ext_of_iso (mapComp f g)
    (fun _ ↦ by simp [map, Comma.mapRight])
    (fun _ ↦ by ext; simp [eqToHom_left])

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
/-
**CategoryTheory.Over.mapCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g
参数：f g : X ⟶ Y；h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f = g`, then `map f` is naturally isomorphic to `map g`.
-/
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Over.mapCongr_rfl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：mapCongr_rfl {X Y : T} (f : X ⟶ Y) : mapCongr f f rfl = Iso.refl _
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapCongr_rfl {X Y : T} (f : X ⟶ Y) :
    mapCongr f f rfl = Iso.refl _ := rfl

variable (T) in
/-- The functor defined by the over categories -/
/-
**CategoryTheory.Over.mapFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：(T : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} T] → CategoryTheo
ry.Functor T CategoryTheory.Cat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor defined by the over categories
-/
@[simps] def mapFunctor : T ⥤ Cat where
  obj X := Cat.of (Over X)
  map f := (map f).toCatHom
  map_id X := congr($(mapId_eq X).toCatHom)
  map_comp f g := congr($(mapComp_eq f g).toCatHom)

end coherences

/-
**CategoryTheory.Over.forget_reflects_iso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：forget_reflects_iso : (forget X).ReflectsIsomorphisms where reflects f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects f _ := ⟨Over.homMk (inv ((forget X).map f) :), by cat_disch⟩

/-- The identity over `X` is terminal. -/
/-
**CategoryTheory.Over.mkIdTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：mkIdTerminal : Limits.IsTerminal (mk (𝟙 X))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C], (CategoryTheory.Functor.id C).Full
· 使用定理 `CategoryTheory.Functor.Faithful.id`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C], (CategoryTheory.Functor.id C).Faithful

--- 原说明 ---
The identity over `X` is terminal.
-/
noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

set_option backward.defeqAttrib.useBackward true in
-- We could make this defeq if we care.
/-
**CategoryTheory.Over.mkIdTerminal_from_left** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Over`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} (Y : C
ategoryTheory.Over X),   CategoryTheory.Over.Hom.left (CategoryTheory.Over.mkIdT
erminal.from Y) = Y.hom
参数：Y : CategoryTheory.Over X；CategoryTheory.Over.mkIdTerminal.from Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
@[simp] lemma mkIdTerminal_from_left (Y : Over X) : (mkIdTerminal.from Y).left = Y.hom := by
  rw [mkIdTerminal.hom_ext (mkIdTerminal.from Y) (homMk Y.hom)]
  rfl
/-
**CategoryTheory.Over.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T}, (Cate
goryTheory.Over.forget X).Faithful
参数：CategoryTheory.Over.forget X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary products.
/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `Over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Over.epi_left_of_epi`.
-/
/-
**CategoryTheory.Over.epi_of_epi_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k
参数：k : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.forget_faithful`：∀ {T : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Over.forget X).Faithful

--- 原说明 ---
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `Over
.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying cate
gory, see
`CategoryTheory.Over.epi_left_of_epi`.
-/
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk
/-
**CategoryTheory.Over.epi_homMk** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
形式化陈述：epi_homMk {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w) : Epi (homMk f 
w)
参数：w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.forget_faithful`：∀ {T : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Over.forget X).Faithful
-/
instance epi_homMk {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `Over.forget X` reflects
monomorphisms.
The converse of `CategoryTheory.Over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
/-
**CategoryTheory.Over.mono_of_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k
参数：k : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.forget_faithful`：∀ {T : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Over.forget X).Faithful

--- 原说明 ---
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `Over
.forget X` reflects
monomorphisms.
The converse of `CategoryTheory.Over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk
/-
**CategoryTheory.Over.mono_homMk** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：mono_homMk {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w) : Mono (homMk
 f w)
参数：w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.forget_faithful`：∀ {T : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Over.forget X).Faithful
-/
instance mono_homMk {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

set_option backward.defeqAttrib.useBackward true in
/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `Over.forget X` preserves
monomorphisms.
The converse of `CategoryTheory.Over.mono_of_mono_left`.
-/
/-
**CategoryTheory.Over.mono_left_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left
参数：k : f ⟶ g。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…

--- 原说明 ---
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `Over
.forget X` preserves
monomorphisms.
The converse of `CategoryTheory.Over.mono_of_mono_left`.
-/
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
/-
**CategoryTheory.Over.iteratedSliceForward** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Over`。
形式化陈述：iteratedSliceForward : Over f ⥤ Over f.left where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y
-/
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
/-
**CategoryTheory.Over.iteratedSliceBackward** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Over`。
形式化陈述：iteratedSliceBackward : Over f.left ⥤ Over f where obj g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f
-/
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))
/-
**CategoryTheory.Over.iteratedSliceBackward_forget** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Over`。
形式化陈述：iteratedSliceBackward_forget (f : Over X) : iteratedSliceBackward f ⋙ Over
.forget f = Over.map f.hom
参数：f : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedSliceBackward_forget (f : Over X) :
    iteratedSliceBackward f ⋙ Over.forget f = Over.map f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
/-
**CategoryTheory.Over.iteratedSliceEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Over`。
形式化陈述：iteratedSliceEquiv : Over f ≌ Over f.left where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y
-/
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))
/-
**CategoryTheory.Over.iteratedSliceForward_forget** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：iteratedSliceForward_forget : iteratedSliceForward f ⋙ forget f.left = for
get f ⋙ forget X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl
/-
**CategoryTheory.Over.iteratedSliceBackward_forget_forget** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Over`。
形式化陈述：iteratedSliceBackward_forget_forget : iteratedSliceBackward f ⋙ forget f ⋙
 forget X = forget f.left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

variable {f}

/-- The naturality of the iterated slice equivalence up to isomorphism. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Over.iteratedSliceForwardNaturalityIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Over`。
形式化陈述：iteratedSliceForwardNaturalityIso {g : Over X} (p : f ⟶ g) : iteratedSlice
Forward f ⋙ Over.map p.left ≅ Over.map p ⋙ iteratedSliceForward g
参数：p : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The naturality of the iterated slice equivalence up to isomorphism.
-/
def iteratedSliceForwardNaturalityIso {g : Over X} (p : f ⟶ g) :
    iteratedSliceForward f ⋙ Over.map p.left ≅ Over.map p ⋙ iteratedSliceForward g :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism relating the functor `Over.map p` to the functor `Over.map p.left`,
mediated by the underlying functor of the iterated slice equivalence.
Note that `iteratedSliceForward` can in fact be considered as a natural transformation from the
2-functor `Over (C := Over X) : Over X ⥤ Cat` to the composite 2-functor
`forget X ⋙ Over : Over X ⥤ Cat`, and the naturality isomorphism is then given by
`iteratedSliceEquivOverMapIso`.
-/
@[simps! hom_app_left_left inv_app_left_left]
/-
**CategoryTheory.Over.iteratedSliceEquivOverMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Over`。
形式化陈述：iteratedSliceEquivOverMapIso {f g : Over X} (p : f ⟶ g) : f.iteratedSliceF
orward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p
参数：p : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism relating the functor `Over.map p` to the functor `Over.m
ap p.left`,
mediated by the underlying functor of the iterated slice equivalence.
Note that `iteratedSliceForward` can in fact be considered as a natural transfor
mation from the
2-functor `Over (C := Over X) : Over X ⥤ Cat` to the composite 2-functor
`forget X ⋙ Over : Over X ⥤ Cat`, and the naturality isomorphism is then given b
y
`iteratedSliceEquivOverMapIso`.
-/
def iteratedSliceEquivOverMapIso {f g : Over X} (p : f ⟶ g) :
    f.iteratedSliceForward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p :=
  NatIso.ofComponents (fun h => Over.isoMk (Over.isoMk (Iso.refl _)))

end IteratedSlice

set_option backward.defeqAttrib.useBackward true in
/-- A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious way. -/
@[simps]
/-
**CategoryTheory.Over.post** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where obj Y
参数：F : T ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious
 way.
-/
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Over.homMk (F.map f.left) (by simp [← F.map_comp])
/-
**CategoryTheory.Over.post_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) : post (X
参数：F : T ⥤ D；G : D ⥤ E。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl
/-
**CategoryTheory.Over.post_forget_eq_forget_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Over`。
形式化陈述：post_forget_eq_forget_comp (F : T ⥤ D) (X : T) : post F ⋙ forget (F.obj X)
 = forget X ⋙ F
参数：F : T ⥤ D；X : T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma post_forget_eq_forget_comp (F : T ⥤ D) (X : T) :
    post F ⋙ forget (F.obj X) = forget X ⋙ F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
/-
**CategoryTheory.Over.postComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) : post (X
参数：F : T ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`.
-/
def postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ by
    ext
    dsimp only [Iso.refl_hom, Over.comp_left, Over.id_left]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Over X` up to `Over.map`. -/
@[simps]
/-
**CategoryTheory.Over.postMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where 
app Y
参数：e : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `F ⟶ G` induces a natural transformation on
`Over X` up to `Over.map`.
-/
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where
  app Y := Over.homMk (e.app Y.left)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `G` are naturally isomorphic, then `Over.post F` and `Over.post G` are also naturally
isomorphic up to `Over.map` -/
@[simps!]
/-
**CategoryTheory.Over.postCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G
参数：e : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` and `G` are naturally isomorphic, then `Over.post F` and `Over.post G` ar
e also naturally
isomorphic up to `Over.map`
-/
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G :=
  NatIso.ofComponents (fun A ↦ Over.isoMk (e.app A.left))

variable (X) (F : T ⥤ D)
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    exact ⟨Over.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is fully faithful, then so is `Over.post F`. -/
/-
**CategoryTheory.Over._root_.CategoryTheory.Functor.FullyFaithful.over** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is fully faithful, then so is `Over.post F`.
-/
def _root_.CategoryTheory.Functor.FullyFaithful.over (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
  preimage {A B} f := Over.homMk (h.preimage f.left) <| h.map_injective (by simpa using Over.w f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `G` is a right adjoint, then so is `post G : Over Y ⥤ Over (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(X ⟶ G Y) ↦ (F X ⟶ F G Y ⟶ Y)`. -/
@[simps]
/-
**CategoryTheory.Over.postAdjunctionRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：postAdjunctionRight {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) : post F ⋙
 map (a.counit.app Y) ⊣ post G where unit.app A
参数：a : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a right adjoint, then so is `post G : Over Y ⥤ Over (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(X ⟶ G Y) ↦ (F X ⟶ F G Y ⟶ Y)`.
-/
def postAdjunctionRight {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⋙ map (a.counit.app Y) ⊣ post G where
  unit.app A := homMk <| a.unit.app A.left
  counit.app A := homMk <| a.counit.app A.left
  counit.naturality _ _ f := by
    ext
    exact a.counit_naturality f.left
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]
/-
**CategoryTheory.Over.isRightAdjoint_post** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：isRightAdjoint_post {Y : D} {G : D ⥤ T} [G.IsRightAdjoint] : (post (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isRightAdjoint_post {Y : D} {G : D ⥤ T} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence on over categories. -/
@[simps]
/-
**CategoryTheory.Over.postEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where functor
参数：F : T ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories induces an equivalence on over categories.
-/
def postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where
  functor := Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.counitIso.app A.left))

/-- `post (Over.forget X) : Over f ⥤ Over (forget.obj f)` is naturally isomorphic to the
functor `Over.iteratedSliceForward : Over f ⥤ Over f.left`. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Over.iteratedSliceForwardIsoPost** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：iteratedSliceForwardIsoPost (f : Over X) : post (Over.forget X) ≅ Over.ite
ratedSliceForward f
参数：f : Over X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`post (Over.forget X) : Over f ⥤ Over (forget.obj f)` is naturally isomorphic to
 the
functor `Over.iteratedSliceForward : Over f ⥤ Over f.left`.
-/
def iteratedSliceForwardIsoPost (f : Over X) :
    post (Over.forget X) ≅ Over.iteratedSliceForward f :=
  Iso.refl _

open Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/-- If `X : T` is terminal, then the over category of `X` is equivalent to `T`. -/
@[simps]
/-
**CategoryTheory.Over.equivalenceOfIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Over`。
形式化陈述：equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ T where functor
参数：hX : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : T` is terminal, then the over category of `X` is equivalent to `T`.
-/
def equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ ↦ .refl _

set_option backward.defeqAttrib.useBackward true in
/-- The induced functor to `Over X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`.
For the converse direction see `CategoryTheory.WithTerminal.commaFromOver`. -/
@[simps]
/-
**CategoryTheory.Over.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {J : T
ype u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} J] →         (D : 
CategoryTheory.Functor J T) →           {X : T} → (D ⟶ (CategoryTheory.Functor.c
onst J).obj X) → CategoryTheory.Functor J (CategoryTheory.Over X)
参数：D : CategoryTheory.Functor J T；D ⟶ (CategoryTheory.Functor.const J).obj X；Cat
egoryTheory.Over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor to `Over X` from a functor `J ⥤ C` and natural maps `sᵢ : X 
⟶ Dᵢ`.
For the converse direction see `CategoryTheory.WithTerminal.commaFromOver`.
-/
protected def lift {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X) :
    J ⥤ Over X where
  obj j := mk (s.app j)
  map f := homMk (D.map f) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced cone on `Over X` on the lifted functor. -/
@[simps]
/-
**CategoryTheory.Over.liftCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：liftCone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.c
onst J).obj X) (c : Cone D) (p : c.pt ⟶ X) (hp : forall j, c.π.app j ≫ s.app j =
 p) : Cone (Over.lift D s) where pt
参数：D : J ⥤ T；s : D ⟶ (Functor.const J).obj X；c : Cone D；p : c.pt ⟶ X；hp : forall
 j, c.π.app j ≫ s.app j = p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced cone on `Over X` on the lifted functor.
-/
def liftCone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p) :
    Cone (Over.lift D s) where
  pt := mk p
  π.app j := homMk (c.π.app j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The lifted cone on `Over X` is a limit cone if the original cone was limiting
and `J` is nonempty. -/
/-
**CategoryTheory.Over.isLimitLiftCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：isLimitLiftCone {J : Type*} [Category* J] [Nonempty J] (D : J ⥤ T) {X : T}
 (s : D ⟶ (Functor.const J).obj X) (c : Cone D) (p : c.pt ⟶ X) (hp : forall j, c
.π.app j ≫ s.app j = p) (hc : IsLimit c) : IsLimit (Over.liftCone D s c p hp) wh
ere lift t
参数：D : J ⥤ T；s : D ⟶ (Functor.const J).obj X；c : Cone D；p : c.pt ⟶ X；hp : forall
 j, c.π.app j ≫ s.app j = p；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifted cone on `Over X` is a limit cone if the original cone was limiting
and `J` is nonempty.
-/
def isLimitLiftCone {J : Type*} [Category* J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p)
    (hc : IsLimit c) :
    IsLimit (Over.liftCone D s c p hp) where
  lift t := homMk (hc.lift ((forget _).mapCone t)) (by
    let j : J := Classical.arbitrary _
    simp [← hp j, dsimp% (t.π.app j).w, dsimp% hc.fac_assoc ((forget X).mapCone t) j])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j ↦ ?_)
    simp [dsimp% hc.fac ((forget X).mapCone t) j, ← hm]

end Over

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Restrict a cone to the diagram over `j`. This preserves being limiting if the forgetful functor
`Over j ⥤ J` is initial (see `CategoryTheory.Limits.IsLimit.overPost`).
-/
@[simps]
/-
**CategoryTheory.Limits.Cone.overPost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cone`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} J] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C] →         {D
 : CategoryTheory.Functor J C} →           CategoryTheory.Limits.Cone D → (j : J
) → CategoryTheory.Limits.Cone (CategoryTheory.Over.post D)
参数：j : J；CategoryTheory.Over.post D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a cone to the diagram over `j`. This preserves being limiting if the fo
rgetful functor
`Over j ⥤ J` is initial (see `CategoryTheory.Limits.IsLimit.overPost`).
-/
def Limits.Cone.overPost
    {J C : Type*} [Category* J] [Category* C] {D : J ⥤ C} (c : Cone D) (j : J) :
    Cone (Over.post (X := j) D) where
  pt := Over.mk (c.π.app j)
  π.app k := Over.homMk (c.π.app k.left)

namespace CostructuredArrow

/-- Reinterpreting an `F`-costructured arrow `F.obj d ⟶ X` as an arrow over `X` induces a functor
    `CostructuredArrow F X ⥤ Over X`. -/
@[simps! obj_left obj_hom map_left]
/-
**CategoryTheory.CostructuredArrow.toOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.CostructuredArrow`。
形式化陈述：toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X
参数：F : D ⥤ T；X : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpreting an `F`-costructured arrow `F.obj d ⟶ X` as an arrow over `X` indu
ces a functor
    `CostructuredArrow F X ⥤ Over X`.
-/
def toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X :=
  CostructuredArrow.pre F (𝟭 T) X
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ T) (X : T) [F.Faithful] : (toOver F X).Faithful :=
  show (CostructuredArrow.pre _ _ _).Faithful from inferInstance
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ T) (X : T) [F.Full] : (toOver F X).Full :=
  show (CostructuredArrow.pre _ _ _).Full from inferInstance
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ T) (X : T) [F.EssSurj] : (toOver F X).EssSurj :=
  show (CostructuredArrow.pre _ _ _).EssSurj from inferInstance

/-- An equivalence `F` induces an equivalence `CostructuredArrow F X ≌ Over X`. -/
/-
**CategoryTheory.CostructuredArrow.isEquivalence_toOver** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.CostructuredArrow`。
形式化陈述：isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] : (toOver F X).
IsEquivalence
参数：F : D ⥤ T；X : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `F` induces an equivalence `CostructuredArrow F X ≌ Over X`.
-/
instance isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] :
    (toOver F X).IsEquivalence :=
  CostructuredArrow.isEquivalence_pre _ _ _

namespace costructuredArrowToOverEquivalence

variable (F : D ⥤ T) {X : T} (Y : Over X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.costructuredArrowToOverEquivalence.functor** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.costructuredArrowToOve
rEquivalence`。
形式化陈述：functor : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left wh
ere obj Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `costructuredArrowToOverEquivalence`.
-/
def functor : CostructuredArrow (toOver F X) Y ⥤ CostructuredArrow F Y.left where
  obj Z := CostructuredArrow.mk Z.hom.left
  map f :=
    CostructuredArrow.homMk f.left.left (by rw [← CostructuredArrow.w f]; dsimp)

/-- Auxiliary definition for `costructuredArrowToOverEquivalence`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.costructuredArrowToOverEquivalence.inverse** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.costructuredArrowToOve
rEquivalence`。
形式化陈述：inverse : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y wh
ere obj Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `costructuredArrowToOverEquivalence`.
-/
def inverse : CostructuredArrow F Y.left ⥤ CostructuredArrow (toOver F X) Y where
  obj Z :=
    CostructuredArrow.mk (Y := CostructuredArrow.mk (Z.hom ≫ Y.hom))
      (Over.homMk Z.hom)
  map f :=
    CostructuredArrow.homMk
      (CostructuredArrow.homMk f.left)
        (by ext; exact CostructuredArrow.w f)

end costructuredArrowToOverEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A category of costructured arrows for a functor `toOver F X` identifies
to a category of costructured arrows for `F`. -/
/-
**CategoryTheory.CostructuredArrow.costructuredArrowToOverEquivalence** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：costructuredArrowToOverEquivalence (F : D ⥤ T) {X : T} (Y : Over X) : Cost
ructuredArrow (toOver F X) Y ≌ CostructuredArrow F Y.left where functor
参数：F : D ⥤ T；Y : Over X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category of costructured arrows for a functor `toOver F X` identifies
to a category of costructured arrows for `F`.
-/
def costructuredArrowToOverEquivalence (F : D ⥤ T) {X : T} (Y : Over X) :
    CostructuredArrow (toOver F X) Y ≌ CostructuredArrow F Y.left where
  functor := costructuredArrowToOverEquivalence.functor F Y
  inverse := costructuredArrowToOverEquivalence.inverse F Y
  unitIso :=
    NatIso.ofComponents (fun f ↦
      CostructuredArrow.isoMk (CostructuredArrow.isoMk (Iso.refl _)
        (by simpa using f.hom.w)))
  counitIso := Iso.refl _

end CostructuredArrow

/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
@[implicit_reducible]
/-
**CategoryTheory.Under** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Under (X : T)
参数：X : T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The under category has as objects arrows with domain `X` and as morphisms commut
ative
    triangles.
-/
def Under (X : T) :=
  StructuredArrow X (𝟭 T)

/-- The type of morphisms in the category `Under`. -/
/-
**CategoryTheory.Under.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {X : T
} → CategoryTheory.Under X → CategoryTheory.Under X → Type (max 0 v₁)
参数：max 0 v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Under`.
-/
protected def Under.Hom {X : T} (f g : Under X) := CommaMorphism f g
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : T} : Category (Under X) where
  Hom := Under.Hom
  __ := (inferInstance : Category (Comma _ _))

-- Satisfying the inhabited linter
/-
**CategoryTheory.Under.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] → [inst_1 : 
Inhabited T] → Inhabited (CategoryTheory.Under default)
参数：CategoryTheory.Under default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Under

variable {X : T}

/-- The underlying object of an object in `Under X`. -/
/-
**CategoryTheory.Under.right** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：right (f : Under X) : T
参数：f : Under X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of an object in `Under X`.
-/
abbrev right (f : Under X) : T := Comma.right f

/-- The morphism that is part of an object in `Under X`. -/
/-
**CategoryTheory.Under.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：hom (f : Under X) : X ⟶ f.right
参数：f : Under X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism that is part of an object in `Under X`.
-/
abbrev hom (f : Under X) : X ⟶ f.right := Comma.hom f

variable {f g : Under X} (φ : f ⟶ g)

/-- The morphism that is part of a morphism in `Under X`. -/
/-
**CategoryTheory.Under.Hom.right** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
.Hom`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] → {X : T} → 
{f g : CategoryTheory.Under X} → (f ⟶ g) → (f.right ⟶ g.right)
参数：f ⟶ g；f.right ⟶ g.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism that is part of a morphism in `Under X`.
-/
abbrev Hom.right : f.right ⟶ g.right := CommaMorphism.right φ

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Under.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Under`。
形式化陈述：w : f.hom ≫ φ.right = g.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
theorem w : f.hom ≫ φ.right = g.hom := by
  simpa using (CommaMorphism.w φ).symm

@[reassoc]
/-
**CategoryTheory.Under.Hom.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Under.Hom
`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} {f g :
 CategoryTheory.Under X} (φ : f ⟶ g),   CategoryTheory.CategoryStruct.comp f.hom
 (CategoryTheory.Under.Hom.right φ) = g.hom
参数：φ : f ⟶ g；CategoryTheory.Under.Hom.right φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
-/
lemma Hom.w : f.hom ≫ φ.right = g.hom := Under.w φ

@[ext]
/-
**CategoryTheory.Under.UnderMorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Under.UnderMorphism`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} {U V :
 CategoryTheory.Under X} {f g : U ⟶ V},   CategoryTheory.Under.Hom.right f = Cat
egoryTheory.Under.Hom.right g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) :
    f = g := by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]
/-
**CategoryTheory.Under.under_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：under_left (U : Under X) : U.left = ⟨⟨⟩⟩
参数：U : Under X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by simp only

@[simp]
/-
**CategoryTheory.Under.id_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Under`
。
形式化陈述：id_right (U : Under X) : Hom.right (𝟙 U) = 𝟙 U.right
参数：U : Under X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_right (U : Under X) : Hom.right (𝟙 U) = 𝟙 U.right :=
  rfl

@[simp]
/-
**CategoryTheory.Under.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.r
ight ≫ g.right
参数：a b c : Under X；f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[implicit_reducible, simps! right hom]
/-
**CategoryTheory.Under.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：mk {X Y : T} (f : X ⟶ Y) : Under X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an object in the under category, it suffices to give an arrow with domai
n `X`.
-/
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps! right]
/-
**CategoryTheory.Under.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom
参数：f : U.right ⟶ V.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give a morphism in the under category, it suffices to give a morphism fitting
 in a
    commutative triangle.
-/
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by cat_disch) : U ⟶ V :=
  StructuredArrow.homMk f w

@[simp]
/-
**CategoryTheory.Under.homMk_eta** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：homMk_eta {U V : Under X} (f : U ⟶ V) (h) : homMk f.right h = f
参数：f : U ⟶ V；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_eta {U V : Under X} (f : U ⟶ V) (h) :
    homMk f.right h = f :=
  rfl

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
/-
**CategoryTheory.Under.homMk_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：homMk_comp {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.righ
t) (w_f w_g) : homMk (f ≫ g) (by simp only [reassoc_of% w_f, w_g]) = homMk f w_f
 ≫ homMk g w_g
参数：f : U.right ⟶ V.right；g : V.right ⟶ W.right；w_f w_g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equ
ivalence.
-/
lemma homMk_comp {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.right) (w_f w_g) :
    homMk (f ≫ g) (by simp only [reassoc_of% w_f, w_g]) = homMk f w_f ≫ homMk g w_g :=
  rfl

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_right inv_right]
/-
**CategoryTheory.Under.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：isoMk {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.ho
m
参数：hr : f.right ≅ g.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in the over category given isomorphisms of the objects 
whose forward
direction gives a commutative triangle.
-/
def isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by cat_disch) : f ≅ g :=
  StructuredArrow.isoMk hr hw

@[simp]
/-
**CategoryTheory.Under.eqToHom_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：eqToHom_right {f g : Under X} (h : f = g) : (eqToHom h).right = eqToHom (b
y rw [h])
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_right {f g : Under X} (h : f = g) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Under.hom_right_inv_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：hom_right_inv_right {f g : Under X} (e : f ≅ g) : e.hom.right ≫ e.inv.righ
t = 𝟙 f.right
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_right_inv_right {f g : Under X} (e : f ≅ g) :
    e.hom.right ≫ e.inv.right = 𝟙 f.right := by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Under.inv_right_hom_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：inv_right_hom_right {f g : Under X} (e : f ≅ g) : e.inv.right ≫ e.hom.righ
t = 𝟙 g.right
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_right_hom_right {f g : Under X} (e : f ≅ g) :
    e.inv.right ≫ e.hom.right = 𝟙 g.right := by
  simp [← Under.comp_right]
/-
**CategoryTheory.Under.forall_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：forall_iff (P : Under X -> Prop) : (forall Y, P Y) ↔ (forall (Y) (f : X ⟶ 
Y), P (.mk f))
参数：P : Under X -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma forall_iff (P : Under X → Prop) :
    (∀ Y, P Y) ↔ (∀ (Y) (f : X ⟶ Y), P (.mk f)) := by
  aesop
/-
**CategoryTheory.Under.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：mk_surjective {S : T} (X : Under S) : exists (Y : T) (f : S ⟶ Y), Under.mk
 f = X
参数：X : Under S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective {S : T} (X : Under S) :
    ∃ (Y : T) (f : S ⟶ Y), Under.mk f = X :=
  ⟨_, X.hom, rfl⟩
/-
**CategoryTheory.Under.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Under`。
形式化陈述：homMk_surjective {S : T} {X Y : Under S} (f : X ⟶ Y) : exists (g : X.right
 ⟶ Y.right) (hg : X.hom ≫ g = Y.hom), Under.homMk g = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
-/
lemma homMk_surjective
    {S : T} {X Y : Under S} (f : X ⟶ Y) :
    ∃ (g : X.right ⟶ Y.right) (hg : X.hom ≫ g = Y.hom), Under.homMk g = f :=
  ⟨f.right, by simp⟩

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
/-
**CategoryTheory.Under.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：forget : Under X ⥤ T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor mapping an arrow to its domain.
-/
def forget : Under X ⥤ T :=
  Comma.snd _ _

end

@[simp]
/-
**CategoryTheory.Under.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：forget_obj {U : Under X} : (forget X).obj U = U.right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl

@[simp]
/-
**CategoryTheory.Under.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`. -/
@[simps]
/-
**CategoryTheory.Under.forgetCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：forgetCone (X : T) : Limits.Cone (forget X)
参数：X : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`.
-/
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { pt := X
    π := { app := Comma.hom } }

/-- A morphism `X ⟶ Y` induces a functor `Under Y ⥤ Under X` in the obvious way. -/
/-
**CategoryTheory.Under.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `X ⟶ Y` induces a functor `Under Y ⥤ Under X` in the obvious way.
-/
def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
  Comma.mapLeft _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
/-
**CategoryTheory.Under.map_obj_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：map_obj_right : ((map f).obj U).right = U.right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl

@[simp]
/-
**CategoryTheory.Under.map_obj_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Und
er`。
形式化陈述：map_obj_hom : ((map f).obj U).hom = f ≫ U.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj_hom : ((map f).obj U).hom = f ≫ U.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Under.map_map_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：map_map_right : ((map f).map g).right = g.right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl

/-- If `f` is an isomorphism, `map f` is an equivalence of categories. -/
/-
**CategoryTheory.Under.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：mapIso (f : X ≅ Y) : Under Y ≌ Under X
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an isomorphism, `map f` is an equivalence of categories.
-/
def mapIso (f : X ≅ Y) : Under Y ≌ Under X :=
  Comma.mapLeftIso _ <| Discrete.natIso fun _ ↦ f.symm
/-
**CategoryTheory.Under.mapIso_functor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Under`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X Y : T} (f :
 X ≅ Y),   (CategoryTheory.Under.mapIso f).functor = CategoryTheory.Under.map f.
hom
参数：f : X ≅ Y；CategoryTheory.Under.mapIso f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
/-
**CategoryTheory.Under.mapIso_inverse** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Under`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X Y : T} (f :
 X ≅ Y),   (CategoryTheory.Under.mapIso f).inverse = CategoryTheory.Under.map f.
inv
参数：f : X ≅ Y；CategoryTheory.Under.mapIso f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIso f] : (Under.map f).IsEquivalence := (Under.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that under categories assemble into a
functor `mapFunctor : Tᵒᵖ ⥤ Cat`.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping by the identity morphism is just the identity functor. -/
@[simps!]
/-
**CategoryTheory.Under.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _
参数：Y : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping by the identity morphism is just the identity functor.
-/
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Mapping by the identity morphism is just the identity functor. -/
/-
**CategoryTheory.Under.mapId_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Under`
。
形式化陈述：mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _
参数：Y : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Under.eqToHom_right`：eqToHom_right {f g : Under X} (h : f
 = g) : (eqToHom h).right = eqToHom (by rw [h])
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping by the identity morphism is just the identity functor.
-/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ :=
  Functor.ext_of_iso (mapId Y) (fun _ ↦ by simp [map, Comma.mapLeft]; rfl)
    (fun _ ↦ by ext; simp [eqToHom_right])

/-- Mapping by `f` and then forgetting is the same as forgetting. -/
/-
**CategoryTheory.Under.mapForget_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Un
der`。
形式化陈述：mapForget_eq {X Y : T} (f : X ⟶ Y) : (map f) ⋙ (forget X) = (forget Y)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping by `f` and then forgetting is the same as forgetting.
-/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) = (forget Y) := rfl

/-- The natural isomorphism arising from `mapForget_eq`. -/
/-
**CategoryTheory.Under.mapForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：mapForget {X Y : T} (f : X ⟶ Y) : (map f) ⋙ (forget X) ≅ (forget Y)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Under.mapForget_eq`：mapForget_eq {X Y : T} (f : X ⟶ Y) : 
(map f) ⋙ (forget X) = (forget Y)

--- 原说明 ---
The natural isomorphism arising from `mapForget_eq`.
-/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) ≅ (forget Y) := eqToIso (mapForget_eq f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
/-
**CategoryTheory.Under.mapComp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = (map g) ⋙ (
map f)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Under.eqToHom_right`：eqToHom_right {f g : Under X} (h : f
 = g) : (eqToHom h).right = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by 
`g`.
-/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map g) ⋙ (map f) := by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
/-
**CategoryTheory.Under.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Under.mapComp_eq`：mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g :
 Y ⟶ Z) : map (f ≫ g) = (map g) ⋙ (map f)

--- 原说明 ---
The natural isomorphism arising from `mapComp_eq`.
-/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  eqToIso (mapComp_eq f g)

/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
/-
**CategoryTheory.Under.mapCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`
。
形式化陈述：mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g
参数：f g : X ⟶ Y；h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f = g`, then `map f` is naturally isomorphic to `map g`.
-/
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

variable (T) in
/-- The functor defined by the under categories -/
/-
**CategoryTheory.Under.mapFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：(T : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} T] → CategoryTheo
ry.Functor Tᵒᵖ CategoryTheory.Cat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor defined by the under categories
-/
@[simps] def mapFunctor : Tᵒᵖ ⥤ Cat where
  obj X := Cat.of (Under X.unop)
  map f := (map f.unop).toCatHom
  map_id X := congr($(mapId_eq X.unop).toCatHom)
  map_comp f g := congr($(mapComp_eq (g.unop) (f.unop)).toCatHom)

end coherences

/-
**CategoryTheory.Under.forget_reflects_iso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：forget_reflects_iso : (forget X).ReflectsIsomorphisms where reflects {Y Z}
 f t
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Under.homMk_right`：∀ {T : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X}   (f : U.right ⟶ V.
right)   (w : autoPara…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := ⟨Under.homMk (inv ((forget X).map f) :), by cat_disch⟩

/-- The identity under `X` is initial. -/
/-
**CategoryTheory.Under.mkIdInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Und
er`。
形式化陈述：mkIdInitial : Limits.IsInitial (mk (𝟙 X))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C], (CategoryTheory.Functor.id C).Full
· 使用定理 `CategoryTheory.Functor.Faithful.id`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C], (CategoryTheory.Functor.id C).Faithful

--- 原说明 ---
The identity under `X` is initial.
-/
noncomputable def mkIdInitial : Limits.IsInitial (mk (𝟙 X)) :=
  StructuredArrow.mkIdInitial

set_option backward.defeqAttrib.useBackward true in
-- We could make this defeq if we care.
/-
**CategoryTheory.Under.mkIdInitial_to_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Under`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T} (Y : C
ategoryTheory.Under X),   CategoryTheory.Under.Hom.right (CategoryTheory.Under.m
kIdInitial.to Y) = Y.hom
参数：Y : CategoryTheory.Under X；CategoryTheory.Under.mkIdInitial.to Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
@[simp] lemma mkIdInitial_to_right (Y : Under X) : (mkIdInitial.to Y).right = Y.hom := by
  rw [mkIdInitial.hom_ext (mkIdInitial.to Y) (homMk Y.hom)]
  rfl
/-
**CategoryTheory.Under.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Under`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {X : T}, (Cate
goryTheory.Under.forget X).Faithful
参数：CategoryTheory.Under.forget X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary coproducts.
/-- If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Under.mono_right_of_mono`.
-/
/-
**CategoryTheory.Under.mono_of_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Under`。
形式化陈述：mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono 
k
参数：k : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Under.forget_faithful`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Under.forget X).Faithful

--- 原说明 ---
If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `Und
er.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying cate
gory, see
`CategoryTheory.Under.mono_right_of_mono`.
-/
theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk
/-
**CategoryTheory.Under.mono_homMk** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：mono_homMk {U V : Under X} {f : U.right ⟶ V.right} [Mono f] (w) : Mono (ho
mMk f w)
参数：w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Under.forget_faithful`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Under.forget X).Faithful
-/
instance mono_homMk {U V : Under X} {f : U.right ⟶ V.right} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

/--
If `k.right` is an epimorphism, then `k` is an epimorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse of `CategoryTheory.Under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/
/-
**CategoryTheory.Under.epi_of_epi_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Under`。
形式化陈述：epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k
参数：k : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Under.forget_faithful`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Under.forget X).Faithful

--- 原说明 ---
If `k.right` is an epimorphism, then `k` is an epimorphism. In other words, `Und
er.forget X`
reflects epimorphisms.
The converse of `CategoryTheory.Under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk
/-
**CategoryTheory.Under.epi_homMk** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：epi_homMk {U V : Under X} {f : U.right ⟶ V.right} [Epi f] (w) : Epi (homMk
 f w)
参数：w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Under.forget_faithful`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T}, (CategoryTheory.Under.forget X).Faithful
-/
instance epi_homMk {U V : Under X} {f : U.right ⟶ V.right} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

set_option backward.defeqAttrib.useBackward true in
/--
If `k` is an epimorphism, then `k.right` is an epimorphism. In other words, `Under.forget X`
preserves epimorphisms.
The converse of `CategoryTheory.under.epi_of_epi_right`.
-/
/-
**CategoryTheory.Under.epi_right_of_epi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Under`。
形式化陈述：epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right
参数：k : f ⟶ g。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…

--- 原说明 ---
If `k` is an epimorphism, then `k.right` is an epimorphism. In other words, `Und
er.forget X`
preserves epimorphisms.
The converse of `CategoryTheory.under.epi_of_epi_right`.
-/
instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  suffices l' = (homMk m) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

set_option backward.defeqAttrib.useBackward true in
/-- A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvious way. -/
@[simps]
/-
**CategoryTheory.Under.post** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where obj Y
参数：F : T ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvio
us way.
-/
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Under.homMk (F.map f.right) (by simp [← F.map_comp])
/-
**CategoryTheory.Under.post_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) : post (X
参数：F : T ⥤ D；G : D ⥤ E。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma post_comp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl
/-
**CategoryTheory.Under.post_forget_eq_forget_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Under`。
形式化陈述：post_forget_eq_forget_comp (F : T ⥤ D) (X : T) : post F ⋙ forget (F.obj X)
 = forget X ⋙ F
参数：F : T ⥤ D；X : T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma post_forget_eq_forget_comp (F : T ⥤ D) (X : T) :
    post F ⋙ forget (F.obj X) = forget X ⋙ F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
/-
**CategoryTheory.Under.postComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`
。
形式化陈述：postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) : post (X
参数：F : T ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`.
-/
def postComp {E : Type*} [Category* E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ by
    ext
    dsimp only [Iso.refl_hom, Under.comp_right, Under.id_right]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Under X` up to `Under.map`. -/
@[simps]
/-
**CategoryTheory.Under.postMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：postMap {F G : T ⥤ D} (e : F ⟶ G) : post (X
参数：e : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `F ⟶ G` induces a natural transformation on
`Under X` up to `Under.map`.
-/
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post (X := X) F ⟶ post G ⋙ map (e.app X) where
  app Y := Under.homMk (e.app Y.right)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `G` are naturally isomorphic, then `Under.post F` and `Under.post G` are also
naturally isomorphic up to `Under.map` -/
@[simps!]
/-
**CategoryTheory.Under.postCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ≅ post G ⋙ map (e.hom.app X)
参数：e : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` and `G` are naturally isomorphic, then `Under.post F` and `Under.post G` 
are also
naturally isomorphic up to `Under.map`
-/
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ≅ post G ⋙ map (e.hom.app X) :=
  NatIso.ofComponents (fun A ↦ Under.isoMk (e.app A.right))

variable (X) (F : T ⥤ D)
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (Under.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] [F.Full] : (Under.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    exact ⟨Under.homMk a (F.map_injective (by simp [ha, dsimp% f.w])), by ext; simpa⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] [F.EssSurj] : (Under.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsEquivalence] : (Under.post (X := X) F).IsEquivalence where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is fully faithful, then so is `Under.post F`. -/
/-
**CategoryTheory.Under._root_.CategoryTheory.Functor.FullyFaithful.under** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is fully faithful, then so is `Under.post F`.
-/
def _root_.CategoryTheory.Functor.FullyFaithful.under (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
  preimage {A B} f := Under.homMk (h.preimage f.right) <| h.map_injective (by simpa using Under.w f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is a left adjoint, then so is `post F : Under X ⥤ Under (F X)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(F X ⟶ Y) ↦ (X ⟶ G F X ⟶ G Y)`. -/
@[simps]
/-
**CategoryTheory.Under.postAdjunctionLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Under`。
形式化陈述：postAdjunctionLeft {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) : post F ⊣ 
post G ⋙ map (a.unit.app X) where unit.app A
参数：a : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is a left adjoint, then so is `post F : Under X ⥤ Under (F X)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given 
by
`(F X ⟶ Y) ↦ (X ⟶ G F X ⟶ G Y)`.
-/
def postAdjunctionLeft {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⊣ post G ⋙ map (a.unit.app X) where
  unit.app A := homMk <| a.unit.app A.right
  counit.app A := homMk <| a.counit.app A.right
  unit.naturality _ _ f := by
    ext
    exact (a.unit_naturality f.right).symm
  counit.naturality _ _ f := by
    ext
    exact (a.counit_naturality f.right)
  left_triangle_components A := by
    ext
    simp [-Functor.id_obj]
  right_triangle_components A := by
    ext
    simp [-Functor.id_obj]
/-
**CategoryTheory.Under.isLeftAdjoint_post** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Under`。
形式化陈述：isLeftAdjoint_post [F.IsLeftAdjoint] : (post (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLeftAdjoint_post [F.IsLeftAdjoint] : (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence on under categories. -/
@[simps]
/-
**CategoryTheory.Under.postEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：postEquiv (F : T ≌ D) : Under X ≌ Under (F.functor.obj X) where functor
参数：F : T ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories induces an equivalence on under categories.
-/
def postEquiv (F : T ≌ D) : Under X ≌ Under (F.functor.obj X) where
  functor := post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.counitIso.app A.right))

open Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/-- If `X : T` is initial, then the under category of `X` is equivalent to `T`. -/
@[simps]
/-
**CategoryTheory.Under.equivalenceOfIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Under`。
形式化陈述：equivalenceOfIsInitial (hX : IsInitial X) : Under X ≌ T where functor
参数：hX : IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : T` is initial, then the under category of `X` is equivalent to `T`.
-/
def equivalenceOfIsInitial (hX : IsInitial X) : Under X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.to Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ ↦ .refl _

set_option backward.defeqAttrib.useBackward true in
/-- The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`. -/
@[simps]
/-
**CategoryTheory.Under.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {J : T
ype u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} J] →         (D : 
CategoryTheory.Functor J T) →           {X : T} → ((CategoryTheory.Functor.const
 J).obj X ⟶ D) → CategoryTheory.Functor J (CategoryTheory.Under X)
参数：D : CategoryTheory.Functor J T；(CategoryTheory.Functor.const J).obj X ⟶ D；Cat
egoryTheory.Under X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X
 ⟶ Dᵢ`.
-/
protected def lift {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D) :
    J ⥤ Under X where
  obj j := .mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced cocone on `Under X` from on the lifted functor. -/
@[simps]
/-
**CategoryTheory.Under.liftCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Unde
r`。
形式化陈述：liftCocone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.con
st J).obj X ⟶ D) (c : Cocone D) (p : X ⟶ c.pt) (hp : forall j, s.app j ≫ c.ι.app
 j = p) : Cocone (Under.lift D s) where pt
参数：D : J ⥤ T；s : (Functor.const J).obj X ⟶ D；c : Cocone D；p : X ⟶ c.pt；hp : fora
ll j, s.app j ≫ c.ι.app j = p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced cocone on `Under X` from on the lifted functor.
-/
def liftCocone {J : Type*} [Category* J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p) :
    Cocone (Under.lift D s) where
  pt := mk p
  ι.app j := homMk (c.ι.app j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The lifted cocone on `Under X` is a colimit cocone if the original cocone was colimiting
and `J` is nonempty. -/
/-
**CategoryTheory.Under.isColimitLiftCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：isColimitLiftCocone {J : Type*} [Category* J] [Nonempty J] (D : J ⥤ T) {X 
: T} (s : (Functor.const J).obj X ⟶ D) (c : Cocone D) (p : X ⟶ c.pt) (hp : foral
l j, s.app j ≫ c.ι.app j = p) (hc : IsColimit c) : IsColimit (liftCocone D s c p
 hp) where desc t
参数：D : J ⥤ T；s : (Functor.const J).obj X ⟶ D；c : Cocone D；p : X ⟶ c.pt；hp : fora
ll j, s.app j ≫ c.ι.app j = p；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifted cocone on `Under X` is a colimit cocone if the original cocone was co
limiting
and `J` is nonempty.
-/
def isColimitLiftCocone {J : Type*} [Category* J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p)
    (hc : IsColimit c) :
    IsColimit (liftCocone D s c p hp) where
  desc t := Under.homMk (hc.desc ((Under.forget _).mapCocone t)) (by
    let j : J := Classical.arbitrary _
    simp [← dsimp% (t.ι.app j).w, ← dsimp% (hp j), dsimp% hc.fac ((forget X).mapCocone t)])
  fac t j := by
    ext
    simp [dsimp% hc.fac ((forget X).mapCocone t) j]
  uniq t _ hm := by
    ext
    refine hc.hom_ext (fun j ↦ ?_)
    simp [dsimp% hc.fac ((forget X).mapCocone t) j, ← hm]

end Under

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Restrict a cocone to the diagram under `j`. This preserves being colimiting if the forgetful functor
`Over j ⥤ J` is final (see `CategoryTheory.Limits.IsColimit.underPost`).
-/
@[simps]
/-
**CategoryTheory.Limits.Cocone.underPost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Cocone`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} J] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C] →         {D
 : CategoryTheory.Functor J C} →           CategoryTheory.Limits.Cocone D → (j :
 J) → CategoryTheory.Limits.Cocone (CategoryTheory.Under.post D)
参数：j : J；CategoryTheory.Under.post D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a cocone to the diagram under `j`. This preserves being colimiting if t
he forgetful functor
`Over j ⥤ J` is final (see `CategoryTheory.Limits.IsColimit.underPost`).
-/
def Limits.Cocone.underPost {J C : Type*} [Category* J] [Category* C]
    {D : J ⥤ C} (c : Cocone D) (j : J) :
    Cocone (Under.post (X := j) D) where
  pt := Under.mk (c.ι.app j)
  ι.app k := Under.homMk (c.ι.app k.right)

namespace StructuredArrow

variable {D : Type u₂} [Category.{v₂} D]

/-- Reinterpreting an `F`-structured arrow `X ⟶ F.obj d` as an arrow under `X` induces a functor
    `StructuredArrow X F ⥤ Under X`. -/
@[simps! obj_right obj_hom map_right]
/-
**CategoryTheory.StructuredArrow.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.StructuredArrow`。
形式化陈述：toUnder (X : T) (F : D ⥤ T) : StructuredArrow X F ⥤ Under X
参数：X : T；F : D ⥤ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpreting an `F`-structured arrow `X ⟶ F.obj d` as an arrow under `X` induc
es a functor
    `StructuredArrow X F ⥤ Under X`.
-/
def toUnder (X : T) (F : D ⥤ T) : StructuredArrow X F ⥤ Under X :=
  StructuredArrow.pre X F (𝟭 T)
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : T) (F : D ⥤ T) [F.Faithful] : (toUnder X F).Faithful :=
  show (StructuredArrow.pre _ _ _).Faithful from inferInstance
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : T) (F : D ⥤ T) [F.Full] : (toUnder X F).Full :=
  show (StructuredArrow.pre _ _ _).Full from inferInstance
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : T) (F : D ⥤ T) [F.EssSurj] : (toUnder X F).EssSurj :=
  show (StructuredArrow.pre _ _ _).EssSurj from inferInstance

/-- An equivalence `F` induces an equivalence `StructuredArrow X F ≌ Under X`. -/
/-
**CategoryTheory.StructuredArrow.isEquivalence_toUnder** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.StructuredArrow`。
形式化陈述：isEquivalence_toUnder (X : T) (F : D ⥤ T) [F.IsEquivalence] : (toUnder X F
).IsEquivalence
参数：X : T；F : D ⥤ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `F` induces an equivalence `StructuredArrow X F ≌ Under X`.
-/
instance isEquivalence_toUnder (X : T) (F : D ⥤ T) [F.IsEquivalence] :
    (toUnder X F).IsEquivalence :=
  StructuredArrow.isEquivalence_pre _ _ _

end StructuredArrow

namespace Functor
variable {X : T} {F : T ⥤ D}

/-
**CategoryTheory.Functor.essImage.of_overPost** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor.essImage`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : T} {F : CategoryTheory.Func
tor T D} {Y : CategoryTheory.Over (F.obj X)},   (CategoryTheory.Over.post F).ess
Image Y → F.essImage Y.left
参数：F.obj X；CategoryTheory.Over.post F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essImage.of_overPost {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y → F.essImage Y.left :=
  fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩
/-
**CategoryTheory.Functor.essImage.of_underPost** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.essImage`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : T} {F : CategoryTheory.Func
tor T D} {Y : CategoryTheory.Under (F.obj X)},   (CategoryTheory.Under.post F).e
ssImage Y → F.essImage Y.right
参数：F.obj X；CategoryTheory.Under.post F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essImage.of_underPost {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y → F.essImage Y.right :=
  fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-- The essential image of `Over.post F` where `F` is full is the same as the essential image of
`F`. -/
/-
**CategoryTheory.Functor.essImage_overPost** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : T} {F : CategoryTheory.Func
tor T D} [F.Full] {Y : CategoryTheory.Over (F.obj X)},   (CategoryTheory.Over.po
st F).essImage Y ↔ F.essImage Y.left
参数：F.obj X；CategoryTheory.Over.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.of_overPost`：∀ {T : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} T] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {X : T} {F : Categ…
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The essential image of `Over.post F` where `F` is full is the same as the essent
ial image of
`F`.
-/
@[simp] lemma essImage_overPost [F.Full] {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y ↔ F.essImage Y.left where
  mp := .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-- The essential image of `Under.post F` where `F` is full is the same as the essential image of
`F`. -/
/-
**CategoryTheory.Functor.essImage_underPost** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：∀ {T : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} T] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : T} {F : CategoryTheory.Func
tor T D} [F.Full] {Y : CategoryTheory.Under (F.obj X)},   (CategoryTheory.Under.
post F).essImage Y ↔ F.essImage Y.right
参数：F.obj X；CategoryTheory.Under.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.of_underPost`：∀ {T : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} T] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {X : T} {F : Categ…
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The essential image of `Under.post F` where `F` is full is the same as the essen
tial image of
`F`.
-/
@[simp] lemma essImage_underPost [F.Full] {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y ↔ F.essImage Y.right where
  mp := .of_underPost
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩

variable {S : Type u₂} [Category.{v₂} S]

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Over X`, it suffices to
    provide maps `F.obj Y ⟶ X` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[simps! obj_left map_left]
/-
**CategoryTheory.Functor.toOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：toOver (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X) (h : forall {Y Z :
 S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X
参数：F : S ⥤ T；X : T；f : (Y : S) -> F.obj Y ⟶ X；h : forall {Y Z : S} (g : Y ⟶ Z), 
F.map g ≫ f Z = f Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Over X`, it su
ffices to
    provide maps `F.obj Y ⟶ X` for all `Y` making the obvious triangles involvin
g all `F.map g`
    commute.
-/
def toOver (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X :=
  F.toCostructuredArrow (𝟭 _) X f h

/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Over X` and composing with the forgetful functor
    `Over X ⥤ T` recovers the original functor. -/
/-
**CategoryTheory.Functor.toOverCompForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X) (h : for
all {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _
 ≅ F
参数：F : S ⥤ T；X : T；f : (Y : S) -> F.obj Y ⟶ X；h : forall {Y Z : S} (g : Y ⟶ Z), 
F.map g ≫ f Z = f Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrading a functor `S ⥤ T` to a functor `S ⥤ Over X` and composing with the for
getful functor
    `Over X ⥤ T` recovers the original functor.
-/
def toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
/-
**CategoryTheory.Functor.toOver_comp_forget** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) -> F.obj Y ⟶ X) (h : f
orall {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget
 _ = F
参数：F : S ⥤ T；X : T；f : (Y : S) -> F.obj Y ⟶ X；h : forall {Y Z : S} (g : Y ⟶ Z), 
F.map g ≫ f Z = f Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ = F :=
  rfl

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Under X`, it suffices to
    provide maps `X ⟶ F.obj Y` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[simps! obj_right map_right]
/-
**CategoryTheory.Functor.toUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：toUnder (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y) (h : forall {Y Z 
: S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : S ⥤ Under X
参数：F : S ⥤ T；X : T；f : (Y : S) -> X ⟶ F.obj Y；h : forall {Y Z : S} (g : Y ⟶ Z), 
f Y ≫ F.map g = f Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Under X`, it s
uffices to
    provide maps `X ⟶ F.obj Y` for all `Y` making the obvious triangles involvin
g all `F.map g`
    commute.
-/
def toUnder (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : S ⥤ Under X :=
  F.toStructuredArrow X (𝟭 _) f h

/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Under X` and composing with the forgetful functor
    `Under X ⥤ T` recovers the original functor. -/
/-
**CategoryTheory.Functor.toUnderCompForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：toUnderCompForget (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y) (h : fo
rall {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forge
t _ ≅ F
参数：F : S ⥤ T；X : T；f : (Y : S) -> X ⟶ F.obj Y；h : forall {Y Z : S} (g : Y ⟶ Z), 
f Y ≫ F.map g = f Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrading a functor `S ⥤ T` to a functor `S ⥤ Under X` and composing with the fo
rgetful functor
    `Under X ⥤ T` recovers the original functor.
-/
def toUnderCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
/-
**CategoryTheory.Functor.toUnder_comp_forget** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：toUnder_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) -> X ⟶ F.obj Y) (h : 
forall {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.for
get _ = F
参数：F : S ⥤ T；X : T；f : (Y : S) -> X ⟶ F.obj Y；h : forall {Y Z : S} (g : Y ⟶ Z), 
f Y ≫ F.map g = f Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnder_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ = F :=
  rfl

end Functor

namespace StructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor from the structured arrow category on the projection functor for any structured
arrow category. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.ofStructuredArrowProjEquivalence.functor** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.StructuredArrow.ofStructuredArrowProjEquival
ence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor D T) →           (Y : T) →             (X : D) →            
   CategoryTheory.Functor (CategoryTheory.StructuredArrow X (CategoryTheory.Stru
cturedArrow.proj Y F))                 (CategoryTheory.StructuredArrow Y ((Categ
oryTheory.Under.forget X).comp F))
参数：F : CategoryTheory.Functor D T；Y : T；X : D；CategoryTheory.StructuredArrow X (
CategoryTheory.StructuredArrow.proj Y F)；CategoryTheory.StructuredArrow Y ((Cate
goryTheory.Under.forget X).comp F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor from the structured arrow category on the projection functor for any s
tructured
arrow category.
-/
def ofStructuredArrowProjEquivalence.functor (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ⥤ StructuredArrow Y (Under.forget X ⋙ F) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofStructuredArrowProjEquivalence.functor`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.ofStructuredArrowProjEquivalence.inverse** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.StructuredArrow.ofStructuredArrowProjEquival
ence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor D T) →           (Y : T) →             (X : D) →            
   CategoryTheory.Functor (CategoryTheory.StructuredArrow Y ((CategoryTheory.Und
er.forget X).comp F))                 (CategoryTheory.StructuredArrow X (Categor
yTheory.StructuredArrow.proj Y F))
参数：F : CategoryTheory.Functor D T；Y : T；X : D；CategoryTheory.StructuredArrow Y (
(CategoryTheory.Under.forget X).comp F)；CategoryTheory.StructuredArrow X (Catego
ryTheory.StructuredArrow.proj Y F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of `ofStructuredArrowProjEquivalence.functor`.
-/
def ofStructuredArrowProjEquivalence.inverse (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow Y (Under.forget X ⋙ F) ⥤ StructuredArrow X (StructuredArrow.proj Y F) :=
  Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the structured arrow category on the projection functor of any
structured arrow category. -/
/-
**CategoryTheory.StructuredArrow.ofStructuredArrowProjEquivalence** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) : StructuredA
rrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
 functor
参数：F : D ⥤ T；Y : T；X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of the structured arrow category on the projection functor of a
ny
structured arrow category.
-/
def ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
  functor := ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the structured arrow category on the diagonal functor
`T ⥤ T × T` to the structured arrow category on `Under.forget`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.ofDiagEquivalence.functor** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.StructuredArrow.ofDiagEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
 × T) →       CategoryTheory.Functor (CategoryTheory.StructuredArrow X (Category
Theory.Functor.diag T))         (CategoryTheory.StructuredArrow X.2 (CategoryThe
ory.Under.forget X.1))
参数：X : T × T；CategoryTheory.StructuredArrow X (CategoryTheory.Functor.diag T)；Ca
tegoryTheory.StructuredArrow X.2 (CategoryTheory.Under.forget X.1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from the structured arrow category on the diagonal functor
`T ⥤ T × T` to the structured arrow category on `Under.forget`.
-/
def ofDiagEquivalence.functor (X : T × T) :
    StructuredArrow X (Functor.diag _) ⥤ StructuredArrow X.2 (Under.forget X.1) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f ↦ f.hom.1) (fun g ↦ by simp [← w g])) _ _
    (fun f ↦ f.hom.2) (fun g ↦ by simp [← w g])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.ofDiagEquivalence.inverse** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.StructuredArrow.ofDiagEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
 × T) →       CategoryTheory.Functor (CategoryTheory.StructuredArrow X.2 (Catego
ryTheory.Under.forget X.1))         (CategoryTheory.StructuredArrow X (CategoryT
heory.Functor.diag T))
参数：X : T × T；CategoryTheory.StructuredArrow X.2 (CategoryTheory.Under.forget X.1
)；CategoryTheory.StructuredArrow X (CategoryTheory.Functor.diag T)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of `ofDiagEquivalence.functor`.
-/
def ofDiagEquivalence.inverse (X : T × T) :
    StructuredArrow X.2 (Under.forget X.1) ⥤ StructuredArrow X (Functor.diag _) :=
  Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the structured arrow category on the diagonal functor `T ⥤ T × T`. -/
/-
**CategoryTheory.StructuredArrow.ofDiagEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.StructuredArrow`。
形式化陈述：ofDiagEquivalence (X : T × T) : StructuredArrow X (Functor.diag _) ≌ Struc
turedArrow X.2 (Under.forget X.1) where functor
参数：X : T × T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of the structured arrow category on the diagonal functor `T ⥤ T
 × T`.
-/
def ofDiagEquivalence (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.2 (Under.forget X.1) where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- A version of `StructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
/-
**CategoryTheory.StructuredArrow.ofDiagEquivalence'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.StructuredArrow`。
形式化陈述：ofDiagEquivalence' (X : T × T) : StructuredArrow X (Functor.diag _) ≌ Stru
cturedArrow X.1 (Under.forget X.2)
参数：X : T × T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `StructuredArrow.ofDiagEquivalence` with the roles of the first and
 second
projection swapped.
-/
def ofDiagEquivalence' (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.1 (Under.forget X.2) :=
  (ofDiagEquivalence X).trans <|
    (ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps]
/-
**CategoryTheory.StructuredArrow.ofCommaSndEquivalenceFunctor** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：ofCommaSndEquivalenceFunctor (c : C) : StructuredArrow c (Comma.fst F G) ⥤
 Comma (Under.forget c ⋙ F) G where obj X
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor used to define the equivalence `ofCommaSndEquivalence`.
-/
def ofCommaSndEquivalenceFunctor (c : C) :
    StructuredArrow c (Comma.fst F G) ⥤ Comma (Under.forget c ⋙ F) G where
  obj X := ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simp [dsimp% f.w]), f.right.right, by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps!]
/-
**CategoryTheory.StructuredArrow.ofCommaSndEquivalenceInverse** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：ofCommaSndEquivalenceInverse (c : C) : Comma (Under.forget c ⋙ F) G ⥤ Stru
cturedArrow c (Comma.fst F G)
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor used to define the equivalence `ofCommaSndEquivalence`.
-/
def ofCommaSndEquivalenceInverse (c : C) :
    Comma (Under.forget c ⋙ F) G ⥤ StructuredArrow c (Comma.fst F G) :=
  Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the structured arrow category with domain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Under.forget c ⋙ F : Under c ⥤ T` and `G`. -/
@[simps]
/-
**CategoryTheory.StructuredArrow.ofCommaSndEquivalence** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.StructuredArrow`。
形式化陈述：ofCommaSndEquivalence (c : C) : StructuredArrow c (Comma.fst F G) ≌ Comma 
(Under.forget c ⋙ F) G where functor
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical equivalence between the structured arrow category with doma
in `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Under.forget c ⋙ F : Under c ⥤ T` and `G`.
-/
def ofCommaSndEquivalence (c : C) :
    StructuredArrow c (Comma.fst F G) ≌ Comma (Under.forget c ⋙ F) G where
  functor := ofCommaSndEquivalenceFunctor F G c
  inverse := ofCommaSndEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end StructuredArrow

namespace CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor from the costructured arrow category on the projection functor for any costructured
arrow category. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.ofCostructuredArrowProjEquivalence.functor** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.ofCostructuredArrowPro
jEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor T D) →           (Y : D) →             (X : T) →            
   CategoryTheory.Functor (CategoryTheory.CostructuredArrow (CategoryTheory.Cost
ructuredArrow.proj F Y) X)                 (CategoryTheory.CostructuredArrow ((C
ategoryTheory.Over.forget X).comp F) Y)
参数：F : CategoryTheory.Functor T D；Y : D；X : T；CategoryTheory.CostructuredArrow (
CategoryTheory.CostructuredArrow.proj F Y) X；CategoryTheory.CostructuredArrow ((
CategoryTheory.Over.forget X).comp F) Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor from the costructured arrow category on the projection functor for any
 costructured
arrow category.
-/
def ofCostructuredArrowProjEquivalence.functor (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X ⥤ CostructuredArrow (Over.forget X ⋙ F) Y :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofCostructuredArrowProjEquivalence.functor`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.ofCostructuredArrowProjEquivalence.inverse** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.ofCostructuredArrowPro
jEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor T D) →           (Y : D) →             (X : T) →            
   CategoryTheory.Functor (CategoryTheory.CostructuredArrow ((CategoryTheory.Ove
r.forget X).comp F) Y)                 (CategoryTheory.CostructuredArrow (Catego
ryTheory.CostructuredArrow.proj F Y) X)
参数：F : CategoryTheory.Functor T D；Y : D；X : T；CategoryTheory.CostructuredArrow (
(CategoryTheory.Over.forget X).comp F) Y；CategoryTheory.CostructuredArrow (Categ
oryTheory.CostructuredArrow.proj F Y) X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of `ofCostructuredArrowProjEquivalence.functor`.
-/
def ofCostructuredArrowProjEquivalence.inverse (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (Over.forget X ⋙ F) Y ⥤ CostructuredArrow (CostructuredArrow.proj F Y) X :=
  Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the costructured arrow category on the projection functor of any
costructured arrow category. -/
/-
**CategoryTheory.CostructuredArrow.ofCostructuredArrowProjEquivalence** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：ofCostructuredArrowProjEquivalence (F : T ⥤ D) (Y : D) (X : T) : Costructu
redArrow (CostructuredArrow.proj F Y) X ≌ CostructuredArrow (Over.forget X ⋙ F) 
Y where functor
参数：F : T ⥤ D；Y : D；X : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of the costructured arrow category on the projection functor of
 any
costructured arrow category.
-/
def ofCostructuredArrowProjEquivalence (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X
      ≌ CostructuredArrow (Over.forget X ⋙ F) Y where
  functor := ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from the costructured arrow category on the diagonal functor
`T ⥤ T × T` to the costructured arrow category on `Under.forget`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.ofDiagEquivalence.functor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CostructuredArrow.ofDiagEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
 × T) →       CategoryTheory.Functor (CategoryTheory.CostructuredArrow (Category
Theory.Functor.diag T) X)         (CategoryTheory.CostructuredArrow (CategoryThe
ory.Over.forget X.1) X.2)
参数：X : T × T；CategoryTheory.CostructuredArrow (CategoryTheory.Functor.diag T) X；
CategoryTheory.CostructuredArrow (CategoryTheory.Over.forget X.1) X.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from the costructured arrow category on the diagonal funct
or
`T ⥤ T × T` to the costructured arrow category on `Under.forget`.
-/
def ofDiagEquivalence.functor (X : T × T) :
    CostructuredArrow (Functor.diag _) X ⥤ CostructuredArrow (Over.forget X.1) X.2 :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; cat_disch))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.ofDiagEquivalence.inverse** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CostructuredArrow.ofDiagEquivalence`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
 × T) →       CategoryTheory.Functor (CategoryTheory.CostructuredArrow (Category
Theory.Over.forget X.1) X.2)         (CategoryTheory.CostructuredArrow (Category
Theory.Functor.diag T) X)
参数：X : T × T；CategoryTheory.CostructuredArrow (CategoryTheory.Over.forget X.1) X
.2；CategoryTheory.CostructuredArrow (CategoryTheory.Functor.diag T) X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of `ofDiagEquivalence.functor`.
-/
def ofDiagEquivalence.inverse (X : T × T) :
    CostructuredArrow (Over.forget X.1) X.2 ⥤ CostructuredArrow (Functor.diag _) X :=
  Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Characterization of the costructured arrow category on the diagonal functor `T ⥤ T × T`. -/
/-
**CategoryTheory.CostructuredArrow.ofDiagEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.CostructuredArrow`。
形式化陈述：ofDiagEquivalence (X : T × T) : CostructuredArrow (Functor.diag _) X ≌ Cos
tructuredArrow (Over.forget X.1) X.2 where functor
参数：X : T × T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of the costructured arrow category on the diagonal functor `T ⥤
 T × T`.
-/
def ofDiagEquivalence (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.1) X.2 where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- A version of `CostructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
-- noncomputability is only for performance
/-
**CategoryTheory.CostructuredArrow.ofDiagEquivalence'** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CostructuredArrow`。
形式化陈述：ofDiagEquivalence' (X : T × T) : CostructuredArrow (Functor.diag _) X ≌ Co
structuredArrow (Over.forget X.2) X.1
参数：X : T × T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ofDiagEquivalence' (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.2) X.1 :=
  (ofDiagEquivalence X).trans <|
    (ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.ofCommaFstEquivalenceFunctor** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：ofCommaFstEquivalenceFunctor (c : C) : CostructuredArrow (Comma.fst F G) c
 ⥤ Comma (Over.forget c ⋙ F) G where obj X
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor used to define the equivalence `ofCommaFstEquivalence`.
-/
def ofCommaFstEquivalenceFunctor (c : C) :
    CostructuredArrow (Comma.fst F G) c ⥤ Comma (Over.forget c ⋙ F) G where
  obj X := ⟨Over.mk X.hom, X.left.right, X.left.hom⟩
  map f := ⟨Over.homMk f.left.left (by simpa using f.w), f.left.right, by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps!]
/-
**CategoryTheory.CostructuredArrow.ofCommaFstEquivalenceInverse** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：ofCommaFstEquivalenceInverse (c : C) : Comma (Over.forget c ⋙ F) G ⥤ Costr
ucturedArrow (Comma.fst F G) c
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor used to define the equivalence `ofCommaFstEquivalence`.
-/
def ofCommaFstEquivalenceInverse (c : C) :
    Comma (Over.forget c ⋙ F) G ⥤ CostructuredArrow (Comma.fst F G) c :=
  Functor.toCostructuredArrow (Comma.preLeft (Over.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the costructured arrow category with codomain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`. -/
@[simps]
/-
**CategoryTheory.CostructuredArrow.ofCommaFstEquivalence** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：ofCommaFstEquivalence (c : C) : CostructuredArrow (Comma.fst F G) c ≌ Comm
a (Over.forget c ⋙ F) G where functor
参数：c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical equivalence between the costructured arrow category with co
domain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`.
-/
def ofCommaFstEquivalence (c : C) :
    CostructuredArrow (Comma.fst F G) c ≌ Comma (Over.forget c ⋙ F) G where
  functor := ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end CostructuredArrow

section Opposite

open Opposite

variable (X : T)

set_option backward.defeqAttrib.useBackward true in
/-- The canonical equivalence between over and under categories by reversing structure arrows. -/
@[simps]
/-
**CategoryTheory.Over.opEquivOpUnder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
) → CategoryTheory.Over (Opposite.op X) ≌ (CategoryTheory.Under X)ᵒᵖ
参数：X : T；Opposite.op X；CategoryTheory.Under X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical equivalence between over and under categories by reversing structu
re arrows.
-/
def Over.opEquivOpUnder : Over (op X) ≌ (Under X)ᵒᵖ where
  functor.obj Y := ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
  inverse.map {Z Y} f := Over.homMk f.unop.right.op <| by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The canonical equivalence between under and over categories by reversing structure arrows. -/
@[simps]
/-
**CategoryTheory.Under.opEquivOpOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：{T : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} T] →     (X : T
) → CategoryTheory.Under (Opposite.op X) ≌ (CategoryTheory.Over X)ᵒᵖ
参数：X : T；Opposite.op X；CategoryTheory.Over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical equivalence between under and over categories by reversing structu
re arrows.
-/
def Under.opEquivOpOver : Under (op X) ≌ (Over X)ᵒᵖ where
  functor.obj Y := ⟨Over.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩
  inverse.obj Y := Under.mk (Y.unop.hom.op)
  inverse.map {Z Y} f := Under.homMk f.unop.left.op <| by dsimp; rw [← Over.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Opposite

end CategoryTheory

