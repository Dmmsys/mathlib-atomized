/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison, David Wärn
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Groupoids

We define `Groupoid` as a typeclass extending `Category`,
asserting that all morphisms have inverses.

The instance `IsIso.ofGroupoid (f : X ⟶ Y) : IsIso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `Groupoid.ofIsIso` from an existing category
with `IsIso f` for every `f`.

## See also

See also `CategoryTheory.Core` for the groupoid of isomorphisms in a category.
-/

@[expose] public section

namespace CategoryTheory

universe v v₂ u u₂

-- morphism levels before object levels. See note [category theory universes].
/-- A `Groupoid` is a category such that all morphisms are isomorphisms. -/
/-
**CategoryTheory.Groupoid** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj wher
e /-- The inverse morphism -/ inv : forall {X Y : obj}, (X ⟶ Y) -> (Y ⟶ X) /-- `
inv f` composed `f` is the identity -/ inv_comp : forall {X Y : obj} (f : X ⟶ Y)
, comp (inv f) f = id Y
参数：obj : Type u。
继承自：Category.{v} obj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Groupoid` is a category such that all morphisms are isomorphisms.
-/
class Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj where
  /-- The inverse morphism -/
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  /-- `inv f` composed `f` is the identity -/
  inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by cat_disch
  /-- `f` composed with `inv f` is the identity -/
  comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by cat_disch

initialize_simps_projections Groupoid (-Hom)

/-- A `LargeGroupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
/-
**CategoryTheory.LargeGroupoid** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：LargeGroupoid (C : Type (u + 1)) : Type (u + 1)
参数：C : Type (u + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LargeGroupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C

/-- A `SmallGroupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
/-
**CategoryTheory.SmallGroupoid** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：SmallGroupoid (C : Type u) : Type (u + 1)
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SmallGroupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C

section

variable {C : Type u} [Groupoid.{v} C] {X Y : C}

-- see Note [lower instance priority]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩

@[simp]
/-
**CategoryTheory.Groupoid.inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.G
roupoid`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {X Y : C} (f : X ⟶ Y),  
 CategoryTheory.Groupoid.inv f = CategoryTheory.inv f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Groupoid.comp_inv`：∀ {obj : Type u} [self : CategoryTheor
y.Groupoid obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f 
(CategoryTheory.Groupo…
-/
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = CategoryTheory.inv f :=
  IsIso.eq_inv_of_hom_inv_id <| Groupoid.comp_inv f

/-- `Groupoid.inv` is involutive. -/
@[simps]
/-
**CategoryTheory.Groupoid.invEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gro
upoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → {X Y : C} → (X ⟶ Y) ≃ 
(Y ⟶ X)
参数：X ⟶ Y；Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Groupoid.inv` is involutive.
-/
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C where
  reverse' f := Groupoid.inv f
  inv' f := by
    dsimp [Quiver.reverse]
    simp

@[simp]
/-
**CategoryTheory.Groupoid.reverse_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Groupoid`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {X Y : C} (f : X ⟶ Y),  
 Quiver.reverse f = CategoryTheory.Groupoid.inv f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.functorMapReverse** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.Ma
pReverse where map_reverse' f
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse where
  map_reverse' f := by simp

variable (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
@[simps!]
/-
**CategoryTheory.Groupoid.isoEquivHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Groupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → (X Y : C) → (X ≅ Y) ≃ 
(X ⟶ Y)
参数：X Y : C；X ≅ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a groupoid, isomorphisms are equivalent to morphisms.
-/
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun f := { hom := f, inv := Groupoid.inv f }

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps]
/-
**CategoryTheory.Groupoid.invEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Groupoid`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Groupoid C] → C ≌ Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence from a groupoid `C` to its opposite sending every morphism to it
s inverse.
-/
def Groupoid.invEquivalence : C ≌ Cᵒᵖ where
  functor.obj := Opposite.op
  functor.map {_ _} f := (inv f).op
  inverse.obj := Opposite.unop
  inverse.map {x y} f := inv f.unop
  unitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)

end

section

/-- A Prop-valued typeclass asserting that a given category is a groupoid. -/
/-
**CategoryTheory.IsGroupoid** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsGroupoid (C : Type u) [Category.{v} C] : Prop where all_isIso {X Y : C} 
(f : X ⟶ Y) : IsIso f
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Prop-valued typeclass asserting that a given category is a groupoid.
-/
class IsGroupoid (C : Type u) [Category.{v} C] : Prop where
  all_isIso {X Y : C} (f : X ⟶ Y) : IsIso f := by infer_instance

attribute [instance] IsGroupoid.all_isIso
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {C : Type u} [Groupoid.{v} C] : IsGroupoid C where

variable {C : Type u} [Category.{v} C]

/-- Promote (noncomputably) an `IsGroupoid` to a `Groupoid` structure. -/
@[instance_reducible]
/-
**CategoryTheory.Groupoid.ofIsGroupoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Groupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.IsGroupoid C] → CategoryTheory.Groupoid C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …

--- 原说明 ---
Promote (noncomputably) an `IsGroupoid` to a `Groupoid` structure.
-/
noncomputable def Groupoid.ofIsGroupoid [IsGroupoid C] :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f

/-- A category where every morphism `IsIso` is a groupoid. -/
@[instance_reducible]
/-
**CategoryTheory.Groupoid.ofIsIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grou
poid`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (∀ {X Y :
 C} (f : X ⟶ Y), CategoryTheory.IsIso f) → CategoryTheory.Groupoid C
参数：∀ {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category where every morphism `IsIso` is a groupoid.
-/
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f

/-- A category with a unique morphism between any two objects is a groupoid -/
@[instance_reducible]
/-
**CategoryTheory.Groupoid.ofHomUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Groupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → ({X Y : C} → Un
ique (X ⟶ Y)) → CategoryTheory.Groupoid C
参数：{X Y : C} → Unique (X ⟶ Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with a unique morphism between any two objects is a groupoid
-/
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C where
  inv _ := all_unique.default

end

/-
**CategoryTheory.isGroupoid_of_reflects_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isGroupoid_of_reflects_iso {C D : Type*} [Category* C] [Category* D] (F : 
C ⥤ D) [F.ReflectsIsomorphisms] [IsGroupoid D] : IsGroupoid C where all_isIso _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
-/
lemma isGroupoid_of_reflects_iso {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.ReflectsIsomorphisms] [IsGroupoid D] :
    IsGroupoid C where
  all_isIso _ := isIso_of_reflects_iso _ F

/-- A category equipped with a fully faithful functor to a groupoid is fully faithful -/
@[instance_reducible]
/-
**CategoryTheory.Groupoid.ofFullyFaithfulToGroupoid** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Groupoid`。
形式化陈述：{C : Type u_1} →   [𝒞 : CategoryTheory.Category.{u_2, u_1} C] →     {D : T
ype u} →       [inst : CategoryTheory.Groupoid D] →         (F : CategoryTheory.
Functor C D) → F.FullyFaithful → CategoryTheory.Groupoid C
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category equipped with a fully faithful functor to a groupoid is fully faithfu
l
-/
def Groupoid.ofFullyFaithfulToGroupoid {C : Type*} [𝒞 : Category C] {D : Type u} [Groupoid.{v} D]
    (F : C ⥤ D) (h : F.FullyFaithful) : Groupoid C :=
  { 𝒞 with
    inv f := h.preimage <| Groupoid.inv (F.map f)
    inv_comp f := by
      apply h.map_injective
      simp
    comp_inv f := by
      apply h.map_injective
      simp }
/-
**CategoryTheory.InducedCategory.groupoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.InducedCategory`。
形式化陈述：{C : Type u} →   (D : Type u₂) →     [CategoryTheory.Groupoid D] → (F : C 
→ D) → CategoryTheory.Groupoid (CategoryTheory.InducedCategory D F)
参数：D : Type u₂；F : C → D；CategoryTheory.InducedCategory D F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  Groupoid.ofFullyFaithfulToGroupoid (inducedFunctor F) (fullyFaithfulInducedFunctor F)
/-
**CategoryTheory.InducedCategory.isGroupoid** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.InducedCategory`。
形式化陈述：∀ {C : Type u} (D : Type u₂) [inst : CategoryTheory.Category.{v, u₂} D] [C
ategoryTheory.IsGroupoid D] (F : C → D),   CategoryTheory.IsGroupoid (CategoryTh
eory.InducedCategory D F)
参数：D : Type u₂；F : C → D；CategoryTheory.InducedCategory D F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isGroupoid_of_reflects_iso`：isGroupoid_of_reflects_iso {C
 D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.ReflectsIsomorphisms] [Is
Groupoid D] : IsGroupoid C wher…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.InducedCategory.full`：∀ {C : Type u₁} {D : Type u₂} [inst
 : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.inducedFunc
tor F).Full
· 使用定理 `CategoryTheory.InducedCategory.faithful`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.induced
Functor F).Faithful
-/
instance InducedCategory.isGroupoid {C : Type u} (D : Type u₂)
    [Category.{v} D] [IsGroupoid D] (F : C → D) :
    IsGroupoid (InducedCategory D F) :=
  isGroupoid_of_reflects_iso (inducedFunctor F)

section

/-
**CategoryTheory.groupoidPi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：groupoidPi {I : Type u} {J : I -> Type u₂} [forall i, Groupoid.{v} (J i)] 
: Groupoid.{max u v} (forall i : I, J i) where inv f
参数：J i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (∀ i : I, J i) where
  inv f := fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp
/-
**CategoryTheory.groupoidProd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β]
 : Groupoid.{max u₂ v₂} (α × β) where inv f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where
  inv f := (Groupoid.inv f.1, Groupoid.inv f.2)
/-
**CategoryTheory.isGroupoidPi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isGroupoidPi {I : Type u} {J : I -> Type u₂} [forall i, Category.{v} (J i)
] [forall i, IsGroupoid (J i)] : IsGroupoid (forall i : I, J i) where all_isIso 
f
参数：J i；J i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.isIso_pi_iff`：isIso_pi_iff {X Y : forall i, C i} (f : X ⟶
 Y) : IsIso f ↔ forall i, IsIso (f i)
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
-/
instance isGroupoidPi {I : Type u} {J : I → Type u₂}
    [∀ i, Category.{v} (J i)] [∀ i, IsGroupoid (J i)] :
    IsGroupoid (∀ i : I, J i) where
  all_isIso f := (isIso_pi_iff f).mpr (fun _ ↦ inferInstance)
/-
**CategoryTheory.isGroupoidProd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isGroupoidProd {α : Type u} {β : Type u₂} [Category.{v} α] [Category.{v₂} 
β] [IsGroupoid α] [IsGroupoid β] : IsGroupoid (α × β) where all_isIso f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isIso_prod_iff`：isIso_prod_iff {P Q : C} {S T : D} {f : (
P, S) ⟶ (Q, T)} : IsIso f ↔ IsIso f.1 ∧ IsIso f.2
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
-/
instance isGroupoidProd {α : Type u} {β : Type u₂} [Category.{v} α] [Category.{v₂} β]
    [IsGroupoid α] [IsGroupoid β] :
    IsGroupoid (α × β) where
  all_isIso f := (isIso_prod_iff (f := f)).mpr ⟨inferInstance, inferInstance⟩

end

open MorphismProperty in
/-
**CategoryTheory.isGroupoid_iff_isomorphisms_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：isGroupoid_iff_isomorphisms_eq_top (C : Type*) [Category* C] : IsGroupoid 
C ↔ isomorphisms C = ⊤
参数：C : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用引理 `CategoryTheory.MorphismProperty.of_eq_top`：of_eq_top {P : MorphismProper
ty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y) : P f
-/
lemma isGroupoid_iff_isomorphisms_eq_top (C : Type*) [Category* C] :
    IsGroupoid C ↔ isomorphisms C = ⊤ := by
  constructor
  · rw [eq_top_iff]
    intro _ _
    simp only [isomorphisms.iff, top_apply]
    infer_instance
  · intro h
    exact ⟨of_eq_top h⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Type*} : IsGroupoid (Discrete I) where

end CategoryTheory

