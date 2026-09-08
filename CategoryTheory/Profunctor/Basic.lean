/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Adam Topaz, Adrian Marti
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!

# Profunctors

A profunctor from a category `C` to a category `D` is a functor from `C` to a category of
presheaves of sets on `D`. We define this as `Profunctor.{w} C D := C ⥤ Dᵒᵖ ⥤ Type w`.

This file provides convenient constructors `ProfunctorCore` and `ProfunctorCore.Hom` for profunctors
and natural transformations between them. We also define the identity profunctor `Profunctor.id`
as the Yoneda bifunctor, the opposite of a profunctor, the `ulift` of a profunctor, whiskering
of a profunctor with functors, and the profunctors in both directions corresponding to a functor
`C ⥤ D` (see `Functor.toProfunctor` and `Functor.toProfunctorFlip`).

## Future work

- Define composition of profunctors.
- Define the bicategory of categories where the 1-morphisms are profunctors.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe w' w v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

/-- Custom structure to construct profunctors, i.e. bifunctors `C ⥤ Dᵒᵖ ⥤ Type w`. -/
@[pp_with_univ]
/-
**CategoryTheory.ProfunctorCore** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：ProfunctorCore where /-- The object part -/ obj : C -> D -> Type w /-- The
 morphism part -/ map {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') : obj X Y'
 ⟶ obj X' Y map_id (X : C) (Y : D) : map (𝟙 X) (𝟙 Y) = 𝟙 _
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Custom structure to construct profunctors, i.e. bifunctors `C ⥤ Dᵒᵖ ⥤ Type w`.
-/
structure ProfunctorCore where
  /-- The object part -/
  obj : C → D → Type w
  /-- The morphism part -/
  map {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') : obj X Y' ⟶ obj X' Y
  map_id (X : C) (Y : D) : map (𝟙 X) (𝟙 Y) = 𝟙 _ := by cat_disch
  map_comp {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : D} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    map (f ≫ f') (g ≫ g') = map f g' ≫ map f' g := by cat_disch

attribute [simp] ProfunctorCore.map_id ProfunctorCore.map_comp

/-- A profunctor from C to D (`Profunctor.{w} C D`) is a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w`. -/
@[pp_with_univ]
/-
**CategoryTheory.Profunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：Profunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A profunctor from C to D (`Profunctor.{w} C D`) is a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w
`.
-/
abbrev Profunctor := C ⥤ Dᵒᵖ ⥤ Type w

variable {C D}

/-- Typecheck a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w` as a profunctor. -/
/-
**CategoryTheory.Functor.profunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Functor C (CategoryTheory.Functor Dᵒᵖ (Type w)) →           CategoryTheor
y.Profunctor.{w, v₁, v₂, u₁, u₂} C D
参数：CategoryTheory.Functor Dᵒᵖ (Type w)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w` as a profunctor.
-/
abbrev Functor.profunctor (F : C ⥤ Dᵒᵖ ⥤ Type w) : Profunctor.{w} C D := F

namespace ProfunctorCore

/-- Custom structure to construct natural transformations between profunctors, see
`CategoryTheory.Profunctor.ofHom`. -/
/-
**CategoryTheory.ProfunctorCore.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Pr
ofunctorCore`。
形式化陈述：Hom (P Q : ProfunctorCore.{w} C D) where /-- The components of the natural
 transformation -/ app (X : C) (Y : D) : P.obj X Y ⟶ Q.obj X Y naturality ⦃X X' 
: C⦄ ⦃Y Y' : D⦄ (f : X ⟶ X') (g : Y ⟶ Y') : P.map f g ≫ app X' Y = app X Y' ≫ Q.
map f g
参数：P Q : ProfunctorCore.{w} C D；X : C；Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Custom structure to construct natural transformations between profunctors, see
`CategoryTheory.Profunctor.ofHom`.
-/
structure Hom (P Q : ProfunctorCore.{w} C D) where
  /-- The components of the natural transformation -/
  app (X : C) (Y : D) : P.obj X Y ⟶ Q.obj X Y
  naturality ⦃X X' : C⦄ ⦃Y Y' : D⦄ (f : X ⟶ X') (g : Y ⟶ Y') :
    P.map f g ≫ app X' Y = app X Y' ≫ Q.map f g := by cat_disch

attribute [reassoc (attr := simp)] ProfunctorCore.Hom.naturality

@[simp]
/-
**CategoryTheory.ProfunctorCore.map_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ProfunctorCore`。
形式化陈述：map_id_comp (P : ProfunctorCore.{w} C D) (X : C) {Y Y' Y'' : D} (g : Y ⟶ Y
') (g' : Y' ⟶ Y'') : P.map (𝟙 X) (g ≫ g') = P.map (𝟙 X) g' ≫ P.map (𝟙 X) g
参数：P : ProfunctorCore.{w} C D；X : C；g : Y ⟶ Y'；g' : Y' ⟶ Y''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ProfunctorCore.map_comp`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id_comp (P : ProfunctorCore.{w} C D) (X : C) {Y Y' Y'' : D}
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    P.map (𝟙 X) (g ≫ g') = P.map (𝟙 X) g' ≫ P.map (𝟙 X) g := by
  nth_rw 1 [← Category.id_comp (𝟙 X)]
  simp only [P.map_comp]

@[simp]
/-
**CategoryTheory.ProfunctorCore.map_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ProfunctorCore`。
形式化陈述：map_comp_id (P : ProfunctorCore.{w} C D) {X X' X'' : C} (Y : D) (f : X ⟶ X
') (f' : X' ⟶ X'') : P.map (f ≫ f') (𝟙 Y) = P.map f (𝟙 Y) ≫ P.map f' (𝟙 Y)
参数：P : ProfunctorCore.{w} C D；Y : D；f : X ⟶ X'；f' : X' ⟶ X''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ProfunctorCore.map_comp`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_id (P : ProfunctorCore.{w} C D) {X X' X'' : C} (Y : D)
    (f : X ⟶ X') (f' : X' ⟶ X'') :
    P.map (f ≫ f') (𝟙 Y) = P.map f (𝟙 Y) ≫ P.map f' (𝟙 Y) := by
  nth_rw 1 [← Category.id_comp (𝟙 Y)]
  simp only [P.map_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProfunctorCore.map_lid_comp_map_rid** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ProfunctorCore`。
形式化陈述：map_lid_comp_map_rid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D} (f
 : X ⟶ X') (g : Y ⟶ Y') : P.map (𝟙 _) g ≫ P.map f (𝟙 _) = P.map f g
参数：P : ProfunctorCore.{w} C D；f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ProfunctorCore.map_comp`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_lid_comp_map_rid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') : P.map (𝟙 _) g ≫ P.map f (𝟙 _) = P.map f g := by
  simp [← P.map_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProfunctorCore.map_rid_comp_map_lid** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ProfunctorCore`。
形式化陈述：map_rid_comp_map_lid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D} (f
 : X ⟶ X') (g : Y ⟶ Y') : P.map f (𝟙 _) ≫ P.map (𝟙 _) g = P.map f g
参数：P : ProfunctorCore.{w} C D；f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ProfunctorCore.map_comp`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_rid_comp_map_lid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') : P.map f (𝟙 _) ≫ P.map (𝟙 _) g = P.map f g := by
  simp [← P.map_comp]

end ProfunctorCore

namespace Profunctor

/-- Construct a profunctor from a `ProfunctorCore`. -/
@[simps]
/-
**CategoryTheory.Profunctor.ofCore** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pro
functor`。
形式化陈述：ofCore (P : ProfunctorCore.{w} C D) : Profunctor.{w} C D where obj X
参数：P : ProfunctorCore.{w} C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a profunctor from a `ProfunctorCore`.
-/
def ofCore (P : ProfunctorCore.{w} C D) : Profunctor.{w} C D where
  obj X := { obj Y := P.obj X (unop Y), map f := P.map (𝟙 _) f.unop }
  map g := { app X := P.map g (𝟙 _) }

set_option backward.defeqAttrib.useBackward true in
/-- Construct a natural transformation between profunctors from a `ProfunctorCore.Hom`. -/
@[simps]
/-
**CategoryTheory.Profunctor.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Prof
unctor`。
形式化陈述：ofHom {P Q : ProfunctorCore.{w} C D} (f : P.Hom Q) : ofCore P ⟶ ofCore Q w
here app X
参数：f : P.Hom Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural transformation between profunctors from a `ProfunctorCore.Ho
m`.
-/
def ofHom {P Q : ProfunctorCore.{w} C D} (f : P.Hom Q) : ofCore P ⟶ ofCore Q where
  app X := { app Y := f.app X (unop Y) }

/-- The identity profunctor from `C` to `C`. This is defined as the Yoneda bifunctor. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Profunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Profunc
tor`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Profunctor.{v₁, v₁, v₁, u₁, u₁} C C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity profunctor from `C` to `C`. This is defined as the Yoneda bifunctor
.
-/
protected def id : Profunctor.{v₁} C C := yoneda

/-- The opposite of a profunctor. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Profunctor.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Profunc
tor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Profunctor.{w, v₁, v₂, u₁, u₂} C D → CategoryTheory.Profunctor.{w, v₂, v₁
, u₂, u₁} Dᵒᵖ Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a profunctor.
-/
protected def op (P : Profunctor.{w} C D) : Profunctor.{w} Dᵒᵖ Cᵒᵖ :=
  .ofCore {
    obj X Y := (P.obj (unop Y)).obj X
    map f g := (P.map g.unop).app _ ≫ (P.obj _).map f }

/-- Whisker a profunctor from `C` to `D` with functors into `C` and `D`. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Profunctor.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Profunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a profunctor from `C` to `D` with functors into `C` and `D`.
-/
def whiskerLeft₂ {A B : Type*} [Category* A] [Category* B]
    (P : Profunctor.{w} C D) (F : A ⥤ C) (G : B ⥤ D) : Profunctor.{w} A B :=
  (((Functor.whiskeringLeft₂ _).obj F).obj G.op).obj P

/-- Increase the universe level of a profunctor. -/
@[pp_with_univ, simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Profunctor.ulift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Prof
unctor`。
形式化陈述：ulift (P : Profunctor.{w} C D) : Profunctor.{max w' w} C D
参数：P : Profunctor.{w} C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase the universe level of a profunctor.
-/
def ulift (P : Profunctor.{w} C D) : Profunctor.{max w' w} C D :=
  (Functor.postcompose₂.obj uliftFunctor).obj P

/-- Increase the universe level of a profunctor by one. This enables dot notation `P.ulift1`,
which is not possible with `Profunctor.ulift`. -/
/-
**CategoryTheory.Profunctor.ulift1** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.P
rofunctor`。
形式化陈述：ulift1 (P : Profunctor.{w} C D) : Profunctor.{w + 1} C D
参数：P : Profunctor.{w} C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase the universe level of a profunctor by one. This enables dot notation `P
.ulift1`,
which is not possible with `Profunctor.ulift`.
-/
abbrev ulift1 (P : Profunctor.{w} C D) : Profunctor.{w + 1} C D :=
  Profunctor.ulift.{w + 1} P

end Profunctor

/-- Given a functor from `C` to `D`, this is the corresponding profunctor from `C` to `D`. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Functor.toProfunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Functor C D → CategoryTheory.Profunctor.{v₂, v₁, v₂, u₁, u₂} C D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor from `C` to `D`, this is the corresponding profunctor from `C` t
o `D`.
-/
def Functor.toProfunctor (F : C ⥤ D) : Profunctor.{v₂} C D :=
  (Profunctor.id (C := D)).whiskerLeft₂ F (𝟭 _)

/-- Given a functor from `C` to `D`, this is the corresponding profunctor from `D` to `C`. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.Functor.toProfunctorRev** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Functor C D → CategoryTheory.Profunctor.{v₂, v₂, v₁, u₂, u₁} D C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor from `C` to `D`, this is the corresponding profunctor from `D` t
o `C`.
-/
def Functor.toProfunctorRev (F : C ⥤ D) : Profunctor.{v₂} D C :=
  (Profunctor.id (C := D)).whiskerLeft₂ (𝟭 _) F

end CategoryTheory

