/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We provide an induction principle `Sum.homInduction` to reason and work with morphisms in this
category.

The sum of two functors `F : A ⥤ C` and `G : B ⥤ C` is a functor `A ⊕ B ⥤ C`, written `F.sum' G`.
This construction should be preferred when defining functors out of a sum.

We provide natural isomorphisms `inlCompSum' : inl_ ⋙ F.sum' G ≅ F` and
`inrCompSum' : inr_ ⋙ F.sum' G ≅ G`.

Furthermore, we provide `Functor.sumIsoExt`, which
constructs a natural isomorphism of functors out of a sum out of natural isomorphism with
their precomposition with the inclusion. This construction should be preferred when trying
to construct isomorphisms between functors out of a sum.

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/

@[expose] public section


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [category_theory universes].
open Sum CategoryTheory.Functor

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- `sum C D` gives the direct sum of two categories.
-/
/-
**CategoryTheory.sum** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：sum : Category.{max v₁ v₂} (C oplus D) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sum C D` gives the direct sum of two categories.
-/
instance sum : Category.{max v₁ v₂} (C ⊕ D) where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => ULift.{max v₁ v₂} (X ⟶ Y)
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => ULift.{max v₁ v₂} (X ⟶ Y)
  id X :=
    match X with
    | inl X => ULift.up (𝟙 X)
    | inr X => ULift.up (𝟙 X)
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => ULift.up <| f.down ≫ g.down
    | inr _, inr _, inr _, f, g => ULift.up <| f.down ≫ g.down

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.hom_inl_inr_false** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False
参数：f : Sum.inl X ⟶ Sum.inr Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False := by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.hom_inr_inl_false** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False
参数：f : Sum.inr X ⟶ Sum.inl Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False := by
  cases f

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps! obj]
/-
**CategoryTheory.Sum.inl_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：inl_ : C ⥤ C oplus D where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`inl_` is the functor `X ↦ inl X`.
-/
def inl_ : C ⥤ C ⊕ D where
  obj X := inl X
  map f := ULift.up f

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps! obj]
/-
**CategoryTheory.Sum.inr_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：inr_ : D ⥤ C oplus D where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`inr_` is the functor `X ↦ inr X`.
-/
def inr_ : D ⥤ C ⊕ D where
  obj X := inr X
  map f := ULift.up f

variable {C D}

/-- An induction principle for morphisms in a sum of categories: a morphism is either of the form
`(inl_ _ _).map _` or of the form `(inr_ _ _).map _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**CategoryTheory.Sum.homInduction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：homInduction {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*} (inl : forall x y
 : C, (f : x ⟶ y) -> P ((inl_ C D).map f)) (inr : forall x y : D, (f : x ⟶ y) ->
 P ((inr_ C D).map f)) {x y : C oplus D} (f : x ⟶ y) : P f
参数：x ⟶ y；inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f)；inr : forall 
x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f)；f : x ⟶ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction principle for morphisms in a sum of categories: a morphism is eithe
r of the form
`(inl_ _ _).map _` or of the form `(inr_ _ _).map _`.
-/
def homInduction {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : C ⊕ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .inl x, .inl y, f => inl x y f.down
  | .inr x, .inr y, f => inr x y f.down

@[simp]
/-
**CategoryTheory.Sum.homInduction_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Sum`。
形式化陈述：homInduction_left {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*} (inl : foral
l x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f)) (inr : forall x y : D, (f : x ⟶ 
y) -> P ((inr_ C D).map f)) {x y : C} (f : x ⟶ y) : homInduction inl inr ((inl_ 
C D).map f) = inl x y f
参数：x ⟶ y；inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f)；inr : forall 
x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f)；f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homInduction_left {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : C} (f : x ⟶ y) : homInduction inl inr ((inl_ C D).map f) = inl x y f :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.homInduction_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sum`。
形式化陈述：homInduction_right {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*} (inl : fora
ll x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f)) (inr : forall x y : D, (f : x ⟶
 y) -> P ((inr_ C D).map f)) {x y : D} (f : x ⟶ y) : homInduction inl inr ((inr_
 C D).map f) = inr x y f
参数：x ⟶ y；inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f)；inr : forall 
x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f)；f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homInduction_right {P : {x y : C ⊕ D} → (x ⟶ y) → Sort*}
    (inl : ∀ x y : C, (f : x ⟶ y) → P ((inl_ C D).map f))
    (inr : ∀ x y : D, (f : x ⟶ y) → P ((inr_ C D).map f))
    {x y : D} (f : x ⟶ y) : homInduction inl inr ((inr_ C D).map f) = inr x y f :=
  rfl

end Sum

namespace Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

section Sum'

variable (F : A ⥤ C) (G : B ⥤ C)

set_option backward.isDefEq.respectTransparency false in
/-- The sum of two functors that land in a given category `C`. -/
/-
**CategoryTheory.Functor.sum'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：sum' : A oplus B ⥤ C where obj | inl X => F.obj X | inr X => G.obj X map {
X Y} f
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two functors that land in a given category `C`.
-/
def sum' : A ⊕ B ⥤ C where
  obj
  | inl X => F.obj X
  | inr X => G.obj X
  map {X Y} f := Sum.homInduction (inl := fun _ _ f ↦ F.map f) (inr := fun _ _ g ↦ G.map g) f
  map_comp {x y z} f g := by
    cases f <;> cases g <;> simp [← Functor.map_comp]
  map_id x := by
    cases x <;> (simp only [← map_id]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The sum `F.sum' G` precomposed with the left inclusion functor is isomorphic to `F` -/
@[simps!]
/-
**CategoryTheory.Functor.inlCompSum'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：inlCompSum' : Sum.inl_ A B ⋙ F.sum' G ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum `F.sum' G` precomposed with the left inclusion functor is isomorphic to 
`F`
-/
def inlCompSum' : Sum.inl_ A B ⋙ F.sum' G ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The sum `F.sum' G` precomposed with the right inclusion functor is isomorphic to `G` -/
@[simps!]
/-
**CategoryTheory.Functor.inrCompSum'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：inrCompSum' : Sum.inr_ A B ⋙ F.sum' G ≅ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum `F.sum' G` precomposed with the right inclusion functor is isomorphic to
 `G`
-/
def inrCompSum' : Sum.inr_ A B ⋙ F.sum' G ≅ G :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
/-
**CategoryTheory.Functor.sum'_obj_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] (F : CategoryTheory.Functor A C)   (G : CategoryTheo
ry.Functor B C) (a : A), (F.sum' G).obj (Sum.inl a) = F.obj a
参数：F : CategoryTheory.Functor A C；G : CategoryTheory.Functor B C；a : A；F.sum' G；
Sum.inl a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_obj_inl (a : A) : (F.sum' G).obj (inl a) = (F.obj a) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.sum'_obj_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] (F : CategoryTheory.Functor A C)   (G : CategoryTheo
ry.Functor B C) (b : B), (F.sum' G).obj (Sum.inr b) = G.obj b
参数：F : CategoryTheory.Functor A C；G : CategoryTheory.Functor B C；b : B；F.sum' G；
Sum.inr b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_obj_inr (b : B) : (F.sum' G).obj (inr b) = (G.obj b) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.sum'_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] (F : CategoryTheory.Functor A C)   (G : CategoryTheo
ry.Functor B C) {a a' : A} (f : a ⟶ a'),   (F.sum' G).map ((CategoryTheory.Sum.i
nl_ A B).map f) = F.map f
参数：F : CategoryTheory.Functor A C；G : CategoryTheory.Functor B C；f : a ⟶ a'；F.su
m' G；(CategoryTheory.Sum.inl_ A B).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_map_inl {a a' : A} (f : a ⟶ a') :
    (F.sum' G).map ((Sum.inl_ _ _).map f) = F.map f :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.sum'_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] (F : CategoryTheory.Functor A C)   (G : CategoryTheo
ry.Functor B C) {b b' : B} (f : b ⟶ b'),   (F.sum' G).map ((CategoryTheory.Sum.i
nr_ A B).map f) = G.map f
参数：F : CategoryTheory.Functor A C；G : CategoryTheory.Functor B C；f : b ⟶ b'；F.su
m' G；(CategoryTheory.Sum.inr_ A B).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_map_inr {b b' : B} (f : b ⟶ b') :
    (F.sum' G).map ((Sum.inr_ _ _).map f) = G.map f :=
  rfl

end Sum'

/-- The sum of two functors. -/
/-
**CategoryTheory.Functor.sum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sum (F : A ⥤ B) (G : C ⥤ D) : A oplus C ⥤ B oplus D
参数：F : A ⥤ B；G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two functors.
-/
def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D := (F ⋙ Sum.inl_ _ _).sum' (G ⋙ Sum.inr_ _ _)

@[simp]
/-
**CategoryTheory.Functor.sum_obj_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.sum G).obj (inl a) = inl 
(F.obj a)
参数：F : A ⥤ B；G : C ⥤ D；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.sum G).obj (inl a) = inl (F.obj a) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.sum_obj_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.sum G).obj (inr c) = inr 
(G.obj c)
参数：F : A ⥤ B；G : C ⥤ D；c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.sum G).obj (inr c) = inr (G.obj c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.sum_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a') : (F.sum G).ma
p ((Sum.inl_ _ _).map f) = (Sum.inl_ _ _).map (F.map f)
参数：F : A ⥤ B；G : C ⥤ D；f : a ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a') :
    (F.sum G).map ((Sum.inl_ _ _).map f) = (Sum.inl_ _ _).map (F.map f) := by
  simp [sum]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.sum_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c') : (F.sum G).ma
p ((Sum.inr_ _ _).map f) = (Sum.inr_ _ _).map (G.map f)
参数：F : A ⥤ B；G : C ⥤ D；f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c') :
    (F.sum G).map ((Sum.inr_ _ _).map f) = (Sum.inr_ _ _).map (G.map f) := by
  simp [sum]

section

variable {F G : A ⊕ B ⥤ C}
  (e₁ : Sum.inl_ A B ⋙ F ≅ Sum.inl_ A B ⋙ G)
  (e₂ : Sum.inr_ A B ⋙ F ≅ Sum.inr_ A B ⋙ G)

/-- A functor out of a sum is uniquely characterized by its precompositions with `inl_` and `inr_`.
-/
/-
**CategoryTheory.Functor.sumIsoExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：sumIsoExt : F ≅ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor out of a sum is uniquely characterized by its precompositions with `in
l_` and `inr_`.
-/
def sumIsoExt : F ≅ G :=
  NatIso.ofComponents (fun x ↦
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f ↦ by
      cases f
      · simpa using! e₁.hom.naturality _
      · simpa using! e₂.hom.naturality _)

@[simp]
/-
**CategoryTheory.Functor.sumIsoExt_hom_app_inl** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：sumIsoExt_hom_app_inl (a : A) : (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom
.app a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumIsoExt_hom_app_inl (a : A) : (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom.app a := rfl

@[simp]
/-
**CategoryTheory.Functor.sumIsoExt_hom_app_inr** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：sumIsoExt_hom_app_inr (b : B) : (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom
.app b
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumIsoExt_hom_app_inr (b : B) : (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom.app b := rfl

@[simp]
/-
**CategoryTheory.Functor.sumIsoExt_inv_app_inl** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：sumIsoExt_inv_app_inl (a : A) : (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv
.app a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumIsoExt_inv_app_inl (a : A) : (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv.app a := rfl

@[simp]
/-
**CategoryTheory.Functor.sumIsoExt_inv_app_inr** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：sumIsoExt_inv_app_inr (b : B) : (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv
.app b
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumIsoExt_inv_app_inr (b : B) : (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv.app b := rfl

end

section

variable (F : A ⊕ B ⥤ C)

/-- Any functor out of a sum is the sum of its precomposition with the inclusions. -/
/-
**CategoryTheory.Functor.isoSum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：isoSum : F ≅ (Sum.inl_ A B ⋙ F).sum' (Sum.inr_ A B ⋙ F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor out of a sum is the sum of its precomposition with the inclusions.
-/
def isoSum : F ≅ (Sum.inl_ A B ⋙ F).sum' (Sum.inr_ A B ⋙ F) :=
  sumIsoExt (inlCompSum' _ _).symm (inrCompSum' _ _).symm

variable (a : A) (b : B)

@[simp]
/-
**CategoryTheory.Functor.isoSum_hom_app_inl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoSum_hom_app_inl : (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSum_hom_app_inl : (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
/-
**CategoryTheory.Functor.isoSum_hom_app_inr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoSum_hom_app_inr : (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSum_hom_app_inr : (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

@[simp]
/-
**CategoryTheory.Functor.isoSum_inv_app_inl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoSum_inv_app_inl : (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSum_inv_app_inl : (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
/-
**CategoryTheory.Functor.isoSum_inv_app_inr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoSum_inv_app_inr : (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSum_inv_app_inr : (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

end

end Functor

namespace NatTrans

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sum of two natural transformations, where all functors have the same target category. -/
/-
**CategoryTheory.NatTrans.sum'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTran
s`。
形式化陈述：sum' {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) : F.sum' H ⟶ G.su
m' I where app X
参数：α : F ⟶ G；β : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two natural transformations, where all functors have the same target 
category.
-/
def sum' {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) : F.sum' H ⟶ G.sum' I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f := by
    cases f <;> simp

@[simp]
/-
**CategoryTheory.NatTrans.sum'_app_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] {F G : CategoryTheory.Functor A C}   {H I : Category
Theory.Functor B C} (α : F ⟶ G) (β : H ⟶ I) (a : A),   (CategoryTheory.NatTrans.
sum' α β).app (Sum.inl a) = α.app a
参数：α : F ⟶ G；β : H ⟶ I；a : A；CategoryTheory.NatTrans.sum' α β；Sum.inl a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_app_inl {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum' α β).app (inl a) = α.app a :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.sum'_app_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：∀ {A : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} A] {B : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} B]   {C : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} C] {F G : CategoryTheory.Functor A C}   {H I : Category
Theory.Functor B C} (α : F ⟶ G) (β : H ⟶ I) (b : B),   (CategoryTheory.NatTrans.
sum' α β).app (Sum.inr b) = β.app b
参数：α : F ⟶ G；β : H ⟶ I；b : B；CategoryTheory.NatTrans.sum' α β；Sum.inr b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum'_app_inr {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (b : B) :
    (sum' α β).app (inr b) = β.app b :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sum of two natural transformations. -/
/-
**CategoryTheory.NatTrans.sum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans
`。
形式化陈述：sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum 
I where app X
参数：α : F ⟶ G；β : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two natural transformations.
-/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => (Sum.inl_ B D).map (α.app X)
    | inr X => (Sum.inr_ B D).map (β.app X)
  naturality X Y f := by
    cases f <;> simp [← Functor.map_comp]

@[simp]
/-
**CategoryTheory.NatTrans.sum_app_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) : 
(sum α β).app (inl a) = (Sum.inl_ _ _).map (α.app a)
参数：α : F ⟶ G；β : H ⟶ I；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = (Sum.inl_ _ _).map (α.app a) :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.sum_app_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) : 
(sum α β).app (inr c) = (Sum.inr_ _ _).map (β.app c)
参数：α : F ⟶ G；β : H ⟶ I；c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = (Sum.inr_ _ _).map (β.app c) :=
  rfl

end NatTrans

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The functor exchanging two direct summand categories. -/
/-
**CategoryTheory.Sum.swap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：swap : C oplus D ⥤ D oplus C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor exchanging two direct summand categories.
-/
def swap : C ⊕ D ⥤ D ⊕ C := (inr_ D C).sum' (inl_ D C)

@[simp]
/-
**CategoryTheory.Sum.swap_obj_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.swap_obj_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X
参数：X : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.swap_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.swap_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f :=
  rfl

/-- Precomposing `swap` with the left inclusion gives the right inclusion. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Sum.swapCompInl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：swapCompInl : inl_ C D ⋙ swap C D ≅ inr_ D C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposing `swap` with the left inclusion gives the right inclusion.
-/
def swapCompInl : inl_ C D ⋙ swap C D ≅ inr_ D C :=
  Functor.inlCompSum' (inr_ _ _) (inl_ _ _)

/-- Precomposing `swap` with the right inclusion gives the left inclusion. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Sum.swapCompInr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：swapCompInr : inr_ C D ⋙ swap C D ≅ inl_ D C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposing `swap` with the right inclusion gives the left inclusion.
-/
def swapCompInr : inr_ C D ⋙ swap C D ≅ inl_ D C :=
  Functor.inrCompSum' (inr_ _ _) (inl_ _ _)

namespace Swap

set_option backward.defeqAttrib.useBackward true in
/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
@[simps functor inverse]
/-
**CategoryTheory.Sum.Swap.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Sum.Swap`。
形式化陈述：equivalence : C oplus D ≌ D oplus C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`.
-/
def equivalence : C ⊕ D ≌ D ⊕ C where
  functor := swap C D
  inverse := swap D C
  unitIso := Functor.sumIsoExt
    (calc inl_ C D ⋙ 𝟭 (C ⊕ D)
        ≅ inl_ C D := rightUnitor _
      _ ≅ inr_ D C ⋙ swap D C := (swapCompInr D C).symm
      _ ≅ (inl_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInl C D).symm _
      _ ≅ inl_ C D ⋙ swap C D ⋙ swap D C := associator _ _ _)
    (calc inr_ C D ⋙ 𝟭 (C ⊕ D)
        ≅ inr_ C D := rightUnitor _
      _ ≅ inl_ D C ⋙ swap D C := (swapCompInl D C).symm
      _ ≅ (inr_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInr C D).symm _
      _ ≅ inr_ C D ⋙ swap C D ⋙ swap D C := associator _ _ _)
  counitIso := Functor.sumIsoExt
    (calc inl_ D C ⋙ swap D C ⋙ swap C D
        ≅ (inl_ D C ⋙ swap D C) ⋙ swap C D := (associator _ _ _).symm
      _ ≅ inr_ C D ⋙ swap C D := isoWhiskerRight (swapCompInl D C) _
      _ ≅ inl_ D C := swapCompInr C D
      _ ≅ inl_ D C ⋙ 𝟭 (D ⊕ C) := (rightUnitor _).symm)
    (calc inr_ D C ⋙ swap D C ⋙ swap C D
        ≅ (inr_ D C ⋙ swap D C) ⋙ swap C D := (associator _ _ _).symm
      _ ≅ inl_ C D ⋙ swap C D := isoWhiskerRight (swapCompInr D C) _
      _ ≅ inr_ D C := swapCompInl C D
      _ ≅ inr_ D C ⋙ 𝟭 (D ⊕ C) := (rightUnitor _).symm)
/-
**CategoryTheory.Sum.Swap.isEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Sum.Swap`。
形式化陈述：isEquivalence : (swap C D).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance isEquivalence : (swap C D).IsEquivalence :=
  (by infer_instance : (equivalence C D).functor.IsEquivalence)

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
/-
**CategoryTheory.Sum.Swap.symmetry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum
.Swap`。
形式化陈述：symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C oplus D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double swap on `C ⊕ D` is naturally isomorphic to the identity functor.
-/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C ⊕ D) :=
  (equivalence C D).unitIso.symm

end Swap

end Sum

end CategoryTheory

