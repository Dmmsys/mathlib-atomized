/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/

@[expose] public section


namespace CategoryTheory

namespace Sigma

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

/-- The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : C j`, a morphism
`(i, X) ⟶ (j, Y)` when `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` then there are no such
morphisms.
-/
/-
**CategoryTheory.Sigma.SigmaHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Sigm
a`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [(i : I) → CategoryTheory.Catego
ry.{v₁, u₁} (C i)] → (i : I) × C i → (i : I) × C i → Type (max w₁ v₁ u₁)
参数：i : I；C i；i : I；i : I；max w₁ v₁ u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : 
C j`, a morphism
`(i, X) ⟶ (j, Y)` when `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` then t
here are no such
morphisms.
-/
inductive SigmaHom : (Σ i, C i) → (Σ i, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → SigmaHom ⟨i, X⟩ ⟨i, Y⟩

namespace SigmaHom

/-- The identity morphism on an object. -/
/-
**CategoryTheory.Sigma.SigmaHom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sig
ma.SigmaHom`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] → (X : (i : I) × C i) → CategoryTheory.Sigma.SigmaHom 
X X
参数：i : I；C i；X : (i : I) × C i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism on an object.
-/
def id : ∀ X : Σ i, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)
/-
**CategoryTheory.Sigma.SigmaHom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sigma
.SigmaHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Σ i, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩

/-- Composition of sigma homomorphisms. -/
/-
**CategoryTheory.Sigma.SigmaHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
igma.SigmaHom`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       {X Y Z : (i : I) × C i} →         CategoryTheo
ry.Sigma.SigmaHom X Y → CategoryTheory.Sigma.SigmaHom Y Z → CategoryTheory.Sigma
.SigmaHom X Z
参数：i : I；C i；i : I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of sigma homomorphisms.
-/
def comp : ∀ {X Y Z : Σ i, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)
/-
**CategoryTheory.Sigma.SigmaHom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sigma
.SigmaHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryStruct (Σ i, C i) where
  Hom := SigmaHom
  id := id
  comp f g := comp f g

@[simp]
/-
**CategoryTheory.Sigma.SigmaHom.comp_def** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sigma.SigmaHom`。
形式化陈述：comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g
) = mk (f ≫ g)
参数：i : I；X Y Z : C i；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl
/-
**CategoryTheory.Sigma.SigmaHom.assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Sigma.SigmaHom`。
形式化陈述：∀ {I : Type w₁} {C : I → Type u₁} [inst : (i : I) → CategoryTheory.Categor
y.{v₁, u₁} (C i)] {X Y Z W : (i : I) × C i}   (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W
),   CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp f g)
 h =     CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.com
p g h)
参数：i : I；C i；i : I；f : X ⟶ Y；g : Y ⟶ Z；h : Z ⟶ W；CategoryTheory.CategoryStruct.c
omp f g；CategoryTheory.CategoryStruct.comp g h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma assoc : ∀ {X Y Z W : Σ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk _, mk _, mk _ => congr_arg mk (Category.assoc _ _ _)
/-
**CategoryTheory.Sigma.SigmaHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Sigma.SigmaHom`。
形式化陈述：∀ {I : Type w₁} {C : I → Type u₁} [inst : (i : I) → CategoryTheory.Categor
y.{v₁, u₁} (C i)] {X Y : (i : I) × C i}   (f : X ⟶ Y), CategoryTheory.CategorySt
ruct.comp (CategoryTheory.CategoryStruct.id X) f = f
参数：i : I；C i；i : I；f : X ⟶ Y；CategoryTheory.CategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma id_comp : ∀ {X Y : Σ i, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk _ => congr_arg mk (Category.id_comp _)
/-
**CategoryTheory.Sigma.SigmaHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Sigma.SigmaHom`。
形式化陈述：∀ {I : Type w₁} {C : I → Type u₁} [inst : (i : I) → CategoryTheory.Categor
y.{v₁, u₁} (C i)] {X Y : (i : I) × C i}   (f : X ⟶ Y), CategoryTheory.CategorySt
ruct.comp f (CategoryTheory.CategoryStruct.id Y) = f
参数：i : I；C i；i : I；f : X ⟶ Y；CategoryTheory.CategoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma comp_id : ∀ {X Y : Σ i, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk _ => congr_arg mk (Category.comp_id _)

end SigmaHom

/-
**CategoryTheory.Sigma.sigma** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：sigma : Category (Σ i, C i) where id_comp
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sigma.SigmaHom.id_comp`：∀ {I : Type w₁} {C : I → Type u₁}
 [inst : (i : I) → CategoryTheory.Category.{v₁, u₁} (C i)] {X Y : (i : I) × C i}
   (f : X ⟶ Y), CategoryThe…
· 使用定理 `CategoryTheory.Sigma.SigmaHom.comp_id`：∀ {I : Type w₁} {C : I → Type u₁}
 [inst : (i : I) → CategoryTheory.Category.{v₁, u₁} (C i)] {X Y : (i : I) × C i}
   (f : X ⟶ Y), CategoryThe…
· 使用定理 `CategoryTheory.Sigma.SigmaHom.assoc`：∀ {I : Type w₁} {C : I → Type u₁} [
inst : (i : I) → CategoryTheory.Category.{v₁, u₁} (C i)] {X Y Z W : (i : I) × C 
i}   (f : X ⟶ Y) (g : Y ⟶…
-/
instance sigma : Category (Σ i, C i) where
  id_comp := SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
/-
**CategoryTheory.Sigma.incl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：incl (i : I) : C i ⥤ Σ i, C i where obj X
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor into the disjoint union of categories.
-/
def incl (i : I) : C i ⥤ Σ i, C i where
  obj X := ⟨i, X⟩
  map := SigmaHom.mk

@[simp]
/-
**CategoryTheory.Sigma.incl_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sigma`
。
形式化陈述：incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩
参数：X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl
/-
**CategoryTheory.Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : I) : Functor.Full (incl i : C i ⥤ Σ i, C i) where
  map_surjective := fun ⟨f⟩ => ⟨f, rfl⟩
/-
**CategoryTheory.Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : I) : Functor.Faithful (incl i : C i ⥤ Σ i, C i) where
  map_injective {_ _ _ _} h := by injection h

section

variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)

/--
To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
/-
**CategoryTheory.Sigma.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`
。
形式化陈述：natTrans {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G
) : F ⟶ G where app
参数：Σ i, C i；h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To build a natural transformation over the sigma category, it suffices to specif
y it restricted to
each subcategory.
-/
def natTrans {F G : (Σ i, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality

@[simp]
/-
**CategoryTheory.Sigma.natTrans_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Si
gma`。
形式化陈述：natTrans_app {F G : (Σ i, C i) ⥤ D} (h : forall i : I, incl i ⋙ F ⟶ incl i
 ⋙ G) (i : I) (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X
参数：Σ i, C i；h : forall i : I, incl i ⋙ F ⟶ incl i ⋙ G；i : I；X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTrans_app {F G : (Σ i, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl

/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
/-
**CategoryTheory.Sigma.descMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       {D : Type u₂} →         [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D] →           (F : (i : I) → CategoryTheory.Functor (C i) 
D) →             (X Y : (i : I) × C i) → (X ⟶ Y) → ((F X.fst).obj X.snd ⟶ (F Y.f
st).obj Y.snd)
参数：i : I；C i；F : (i : I) → CategoryTheory.Functor (C i) D；X Y : (i : I) × C i；X 
⟶ Y；(F X.fst).obj X.snd ⟶ (F Y.fst).obj Y.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). An auxiliary definition to build the functor `desc`.
-/
def descMap : ∀ X Y : Σ i, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, SigmaHom.mk g => (F _).map g

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
/-
**CategoryTheory.Sigma.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：desc : (Σ i, C i) ⥤ D where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, 
C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricte
d to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural i
somorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
def desc : (Σ i, C i) ⥤ D where
  obj X := (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp

@[simp]
/-
**CategoryTheory.Sigma.desc_map_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sig
ma`。
形式化陈述：desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f)
 = (F i).map f
参数：X Y : C i；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl

set_option backward.defeqAttrib.useBackward true in
-- We hand-generate the simp lemmas about this since they come out cleaner.
/-- This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
/-
**CategoryTheory.Sigma.inclDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`
。
形式化陈述：inclDesc (i : I) : incl i ⋙ desc F ≅ F i
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This shows that when `desc F` is restricted to just the subcategory `C i`, `desc
 F` agrees with
`F i`.
-/
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
/-
**CategoryTheory.Sigma.inclDesc_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sigma`。
形式化陈述：inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).o
bj X)
参数：i : I；X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).obj X) :=
  rfl

@[simp]
/-
**CategoryTheory.Sigma.inclDesc_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sigma`。
形式化陈述：inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).o
bj X)
参数：i : I；X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl

/-- If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
/-
**CategoryTheory.Sigma.descUniq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`
。
形式化陈述：descUniq (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) : q ≅ desc 
F
参数：q : (Σ i, C i) ⥤ D；h : forall i, incl i ⋙ q ≅ F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is 
isomorphic to
`desc F`.
-/
def descUniq (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f

@[simp]
/-
**CategoryTheory.Sigma.descUniq_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sigma`。
形式化陈述：descUniq_hom_app (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i 
: I) (X : C i) : (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X
参数：q : (Σ i, C i) ⥤ D；h : forall i, incl i ⋙ q ≅ F i；i : I；X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descUniq_hom_app (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X :=
  rfl

@[simp]
/-
**CategoryTheory.Sigma.descUniq_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sigma`。
形式化陈述：descUniq_inv_app (q : (Σ i, C i) ⥤ D) (h : forall i, incl i ⋙ q ≅ F i) (i 
: I) (X : C i) : (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X
参数：q : (Σ i, C i) ⥤ D；h : forall i, incl i ⋙ q ≅ F i；i : I；X : C i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descUniq_inv_app (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
/-
**CategoryTheory.Sigma.natIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：natIso {q₁ q₂ : (Σ i, C i) ⥤ D} (h : forall i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) 
: q₁ ≅ q₂ where hom
参数：Σ i, C i；h : forall i, incl i ⋙ q₁ ≅ incl i ⋙ q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and 
`q₂` are isomorphic.
-/
def natIso {q₁ q₂ : (Σ i, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  hom := natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv

end

section

variable (C) {J : Type w₂} (g : J → I)

/-- A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`. -/
/-
**CategoryTheory.Sigma.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：map : (Σ j : J, C (g j)) ⥤ Σ i : I, C i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`.
-/
def map : (Σ j : J, C (g j)) ⥤ Σ i : I, C i :=
  desc fun j => incl (g j)

@[simp]
/-
**CategoryTheory.Sigma.map_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩
参数：j : J；X : C (g j)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.Sigma.map_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) : (Sigma.map C g).map (SigmaHo
m.mk f) = SigmaHom.mk f
参数：g j；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl

/-- The functor `Sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps!]
/-
**CategoryTheory.Sigma.inclCompMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sig
ma`。
形式化陈述：inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Sigma.map C g` restricted to the subcategory `C j` acts as the incl
usion of `g j`.
-/
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Sigma.map` applied to the identity function is just the identity functor. -/
@[simps!]
/-
**CategoryTheory.Sigma.mapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：mapId : map C (id : I -> I) ≅ 𝟭 (Σ i, C i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Sigma.map` applied to the identity function is just the identity fu
nctor.
-/
def mapId : map C (id : I → I) ≅ 𝟭 (Σ i, C i) :=
  natIso fun i => NatIso.ofComponents fun _ => Iso.refl _

variable {I} {K : Type w₃}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `Sigma.map` applied to a composition is a composition of functors. -/
@[simps!]
/-
**CategoryTheory.Sigma.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sigma`。
形式化陈述：mapComp (f : K -> J) (g : J -> I) : map (fun x => C (g x)) f ⋙ (map C g :)
 ≅ map C (g ∘ f)
参数：f : K -> J；g : J -> I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Sigma.map` applied to a composition is a composition of functors.
-/
def mapComp (f : K → J) (g : J → I) : map (fun x ↦ C (g x)) f ⋙ (map C g :) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (Functor.isoWhiskerRight (inclCompMap _ f k) (map C g :) :) ≪≫ inclCompMap _ g (f k)

end

namespace Functor

-- variable {C}
variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

/-- Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
/-
**CategoryTheory.Sigma.Functor.sigma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
igma.Functor`。
形式化陈述：sigma (F : forall i, C i ⥤ D i) : (Σ i, C i) ⥤ Σ i, D i
参数：F : forall i, C i ⥤ D i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of functors into a functor between the sigma type
s.
-/
def sigma (F : ∀ i, C i ⥤ D i) : (Σ i, C i) ⥤ Σ i, D i :=
  desc fun i => F i ⋙ incl i

end Functor

namespace natTrans

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]
variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
/-
**CategoryTheory.Sigma.natTrans.sigma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Sigma.natTrans`。
形式化陈述：sigma (α : forall i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where 
app f
参数：α : forall i, F i ⟶ G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an `I`-indexed family of natural transformations into a single natural 
transformation.
-/
def sigma (α : ∀ i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where
  app f := SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]

end natTrans

end Sigma

end CategoryTheory

