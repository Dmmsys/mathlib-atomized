/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.CategoryTheory.IsoReassoc
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Whiskering

Given a functor `F : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whiskerLeft F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskeringLeft`. Here
`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

We show the associator and unitor natural isomorphisms satisfy the triangle and pentagon
identities.
-/

@[expose] public section


namespace CategoryTheory

namespace Functor

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

/-- If `α : G ⟶ H` then `whiskerLeft F α : F ⋙ G ⟶ F ⋙ H` has components `α.app (F.obj X)`. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.Functor.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : F ⋙ G ⟶ F ⋙ H where ap
p X
参数：F : C ⥤ D；α : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α : G ⟶ H` then `whiskerLeft F α : F ⋙ G ⟶ F ⋙ H` has components `α.app (F.o
bj X)`.
-/
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

@[simp, to_dual self]
/-
**CategoryTheory.Functor.id_hcomp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α
参数：F : C ⥤ D；α : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.hcomp_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α := by
  ext
  simp

/-- If `α : G ⟶ H` then `whiskerRight α F : G ⋙ F ⟶ H ⋙ F` has components `F.map (α.app X)`. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.Functor.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : G ⋙ F ⟶ H ⋙ F where a
pp X
参数：α : G ⟶ H；F : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α : G ⟶ H` then `whiskerRight α F : G ⋙ F ⟶ H ⋙ F` has components `F.map (α.
app X)`.
-/
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp, α.naturality]

@[simp, to_dual self]
/-
**CategoryTheory.Functor.hcomp_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：hcomp_id {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : α ◫ 𝟙 F = whiskerRight α 
F
参数：α : G ⟶ H；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.hcomp_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hcomp_id {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : α ◫ 𝟙 F = whiskerRight α F := by
  ext
  simp

variable (C D E)

set_option backward.defeqAttrib.useBackward true in
/-- Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
-/
def whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  obj F :=
    { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }

set_option backward.defeqAttrib.useBackward true in
/-- Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskeringRight.obj H).obj F` is `F ⋙ H`, and
`(whiskeringRight.obj H).map α` is `whiskerRight α H`.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where obj H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskeringRight.obj H).obj F` is `F ⋙ H`, and
`(whiskeringRight.obj H).map α` is `whiskerRight α H`.
-/
def whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  obj H :=
    { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }

variable {C} {D} {E}
/-
**CategoryTheory.Functor.faithful_whiskeringRight_obj** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] : ((whiskeringRight 
C D E).obj F).Faithful where map_injective hαβ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] :
    ((whiskeringRight C D E).obj F).Faithful where
  map_injective hαβ := by
    ext X
    exact F.map_injective <| congr_fun (congr_arg NatTrans.app hαβ) X

/-- If `F : D ⥤ E` is fully faithful, then so is
`(whiskeringRight C D E).obj F : (C ⥤ D) ⥤ C ⥤ E`. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.whiskeringRight** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：{D : Type u₂} →   [inst : CategoryTheory.Category.{v₂, u₂} D] →     {E : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} E] →         {F : Cat
egoryTheory.Functor D E} →           F.FullyFaithful →             (C : Type u_1
) →               [inst_2 : CategoryTheory.Category.{v_1, u_1} C] →             
    ((CategoryTheory.Functor.whiskeringRight C D E).obj F).FullyFaithful
参数：C : Type u_1；(CategoryTheory.Functor.whiskeringRight C D E).obj F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : D ⥤ E` is fully faithful, then so is
`(whiskeringRight C D E).obj F : (C ⥤ D) ⥤ C ⥤ E`.
-/
def FullyFaithful.whiskeringRight {F : D ⥤ E} (hF : F.FullyFaithful)
    (C : Type*) [Category* C] :
    ((whiskeringRight C D E).obj F).FullyFaithful where
  preimage f :=
    { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        simp only [map_comp, map_preimage]
        apply f.naturality }
/-
**CategoryTheory.Functor.whiskeringLeft_obj_id** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：whiskeringLeft_obj_id : (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringLeft_obj_id : (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between left-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
/-
**CategoryTheory.Functor.whiskeringLeftObjIdIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between left-whiskering on the identity functor and the identity
 of the functor
between the resulting functor categories.
-/
def whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _
/-
**CategoryTheory.Functor.whiskeringLeft_obj_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：whiskeringLeft_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G :
 D ⥤ D') : (whiskeringLeft C D' E).obj (F ⋙ G) = (whiskeringLeft D D' E).obj G ⋙
 (whiskeringLeft C D E).obj F
参数：F : C ⥤ D；G : D ⥤ D'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringLeft_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) =
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  rfl

/-- The isomorphism between left-whiskering on the composition of functors and the composition
of two left-whiskering applications. -/
@[simps!]
/-
**CategoryTheory.Functor.whiskeringLeftObjCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G 
: D ⥤ D') : (whiskeringLeft C D' E).obj (F ⋙ G) ≅ (whiskeringLeft D D' E).obj G 
⋙ (whiskeringLeft C D E).obj F
参数：F : C ⥤ D；G : D ⥤ D'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between left-whiskering on the composition of functors and the c
omposition
of two left-whiskering applications.
-/
def whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) ≅
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  Iso.refl _
/-
**CategoryTheory.Functor.whiskeringRight_obj_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：whiskeringRight_obj_id : (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringRight_obj_id : (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _ :=
  rfl

/-- The isomorphism between right-whiskering on the identity functor and the identity of the functor
between the resulting functor categories. -/
@[simps!]
/-
**CategoryTheory.Functor.whiskeringRightObjIdIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：whiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between right-whiskering on the identity functor and the identit
y of the functor
between the resulting functor categories.
-/
def whiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _
/-
**CategoryTheory.Functor.whiskeringRight_obj_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：whiskeringRight_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G 
: D ⥤ D') : (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G = (wh
iskeringRight E C D').obj (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ D'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringRight_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G =
    (whiskeringRight E C D').obj (F ⋙ G) :=
  rfl

/-- The isomorphism between right-whiskering on the composition of functors and the composition
of two right-whiskering applications. -/
@[simps!]
/-
**CategoryTheory.Functor.whiskeringRightObjCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G
 : D ⥤ D') : (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅ (w
hiskeringRight E C D').obj (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ D'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between right-whiskering on the composition of functors and the 
composition
of two right-whiskering applications.
-/
def whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅
    (whiskeringRight E C D').obj (F ⋙ G) :=
  Iso.refl _
/-
**CategoryTheory.Functor.full_whiskeringRight_obj** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] : ((whiskeringR
ight C D E).obj F).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] :
    ((whiskeringRight C D E).obj F).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]
/-
**CategoryTheory.Functor.whiskerLeft_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (NatTrans.id G) = N
atTrans.id (F.comp G)
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} :
    whiskerLeft F (NatTrans.id G) = NatTrans.id (F.comp G) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.whiskerLeft_id'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp 
G)
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.whiskerRight_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (NatTrans.id G) F =
 NatTrans.id (G.comp F)
参数：F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp]
/-
**CategoryTheory.Functor.whiskerRight_id'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.com
p F)
参数：F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.Functor.whiskerLeft_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) : whi
skerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β
参数：F : C ⥤ D；α : G ⟶ H；β : H ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β :=
  rfl

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.Functor.whiskerRight_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : wh
iskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F
参数：α : G ⟶ H；β : H ⟶ K；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β

@[to_dual none, reassoc]
/-
**CategoryTheory.Functor.whiskerLeft_comp_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β :
 H ⟶ K) : whiskerLeft F β ≫ whiskerRight α K = whiskerRight α H ≫ whiskerLeft G 
β
参数：α : F ⟶ G；β : H ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟶ G) (β : H ⟶ K) :
    whiskerLeft F β ≫ whiskerRight α K = whiskerRight α H ≫ whiskerLeft G β := by
  ext
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_dual hcomp_eq_whiskerRight_comp_whiskerLeft]
/-
**CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {F G : CategoryTheory.Functor C D}   {H K : Category
Theory.Functor D E} (α : F ⟶ G) (β : H ⟶ K),   α ◫ β = CategoryTheory.CategorySt
ruct.comp (F.whiskerLeft β) (CategoryTheory.Functor.whiskerRight α K)
参数：α : F ⟶ G；β : H ⟶ K；F.whiskerLeft β；CategoryTheory.Functor.whiskerRight α K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight {F G : C ⥤ D} {H K : D ⥤ E}
    (α : F ⟶ G) (β : H ⟶ K) : α ◫ β = whiskerLeft F β ≫ whiskerRight α K := by
  ext
  simp

/-- If `α : G ≅ H` is a natural isomorphism then
`isoWhiskerLeft F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
/-
**CategoryTheory.Functor.isoWhiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H
参数：F : C ⥤ D；α : G ≅ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α : G ≅ H` is a natural isomorphism then
`isoWhiskerLeft F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerLeft_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (isoWhiskerLeft
 F α).hom = whiskerLeft F α.hom
参数：F : C ⥤ D；α : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).hom = whiskerLeft F α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerLeft_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (isoWhiskerLeft
 F α).inv = whiskerLeft F α.inv
参数：F : C ⥤ D；α : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).inv = whiskerLeft F α.inv :=
  rfl
/-
**CategoryTheory.Functor.isoWhiskerLeft_symm** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isoWhiskerLeft_symm (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (isoWhiskerLef
t F α).symm = isoWhiskerLeft F α.symm
参数：F : C ⥤ D；α : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoWhiskerLeft_symm (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).symm = isoWhiskerLeft F α.symm :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerLeft_refl** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isoWhiskerLeft_refl (F : C ⥤ D) (G : D ⥤ E) : isoWhiskerLeft F (Iso.refl G
) = Iso.refl _
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoWhiskerLeft_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerLeft F (Iso.refl G) = Iso.refl _ :=
  rfl

/-- If `α : G ≅ H` then
`isoWhiskerRight α F : (G ⋙ F) ≅ (H ⋙ F)` has components `F.map_iso (α.app X)`.
-/
/-
**CategoryTheory.Functor.isoWhiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F
参数：α : G ≅ H；F : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α : G ≅ H` then
`isoWhiskerRight α F : (G ⋙ F) ≅ (H ⋙ F)` has components `F.map_iso (α.app X)`.
-/
def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerRight_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (isoWhiskerRig
ht α F).hom = whiskerRight α.hom F
参数：α : G ≅ H；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).hom = whiskerRight α.hom F :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (isoWhiskerRig
ht α F).inv = whiskerRight α.inv F
参数：α : G ≅ H；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).inv = whiskerRight α.inv F :=
  rfl
/-
**CategoryTheory.Functor.isoWhiskerRight_symm** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerRight_symm {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (isoWhiskerRi
ght α F).symm = isoWhiskerRight α.symm F
参数：α : G ≅ H；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoWhiskerRight_symm {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).symm = isoWhiskerRight α.symm F :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerRight_refl** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerRight_refl (F : C ⥤ D) (G : D ⥤ E) : isoWhiskerRight (Iso.refl F
) G = Iso.refl _
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoWhiskerRight_refl (F : C ⥤ D) (G : D ⥤ E) :
    isoWhiskerRight (Iso.refl F) G = Iso.refl _ := by
  cat_disch

@[to_dual self]
/-
**CategoryTheory.Functor.isIso_whiskerLeft** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] : IsIso 
(whiskerLeft F α)
参数：F : C ⥤ D；α : G ⟶ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  (isoWhiskerLeft F (asIso α)).isIso_hom

@[to_dual self]
/-
**CategoryTheory.Functor.isIso_whiskerRight** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] : IsIso
 (whiskerRight α F)
参数：α : G ⟶ H；F : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  (isoWhiskerRight (asIso α) F).isIso_hom

@[simp, to_dual self]
/-
**CategoryTheory.Functor.inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：inv_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] : inv (wh
iskerRight α F) = whiskerRight (inv α) F
参数：α : G ⟶ H；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    inv (whiskerRight α F) = whiskerRight (inv α) F := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerRight_comp]

@[simp, to_dual self]
/-
**CategoryTheory.Functor.inv_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：inv_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] : inv (whi
skerLeft F α) = whiskerLeft F (inv α)
参数：F : C ⥤ D；α : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    inv (whiskerLeft F α) = whiskerLeft F (inv α) := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← whiskerLeft_comp]

@[simp, reassoc]
/-
**CategoryTheory.Functor.isoWhiskerLeft_trans** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerLeft_trans (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K) :
 isoWhiskerLeft F (α ≪≫ β) = isoWhiskerLeft F α ≪≫ isoWhiskerLeft F β
参数：F : C ⥤ D；α : G ≅ H；β : H ≅ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoWhiskerLeft_trans (F : C ⥤ D) {G H K : D ⥤ E} (α : G ≅ H) (β : H ≅ K) :
    isoWhiskerLeft F (α ≪≫ β) = isoWhiskerLeft F α ≪≫ isoWhiskerLeft F β :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.Functor.isoWhiskerRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isoWhiskerRight_trans {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E) 
: isoWhiskerRight (α ≪≫ β) F = isoWhiskerRight α F ≪≫ isoWhiskerRight β F
参数：α : G ≅ H；β : H ≅ K；F : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mapIso_trans`：mapIso_trans (F : C ⥤ D) {X Y Z : C
} (i : X ≅ Y) (j : Y ≅ Z) : F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j
-/
theorem isoWhiskerRight_trans {G H K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E) :
    isoWhiskerRight (α ≪≫ β) F = isoWhiskerRight α F ≪≫ isoWhiskerRight β F :=
  ((whiskeringRight C D E).obj F).mapIso_trans α β

@[reassoc]
/-
**CategoryTheory.Functor.isoWhiskerLeft_trans_isoWhiskerRight** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isoWhiskerLeft_trans_isoWhiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ 
G) (β : H ≅ K) : isoWhiskerLeft F β ≪≫ isoWhiskerRight α K = isoWhiskerRight α H
 ≪≫ isoWhiskerLeft G β
参数：α : F ≅ G；β : H ≅ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoWhiskerLeft_trans_isoWhiskerRight {F G : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G) (β : H ≅ K) :
    isoWhiskerLeft F β ≪≫ isoWhiskerRight α K = isoWhiskerRight α H ≪≫ isoWhiskerLeft G β := by
  ext
  simp

variable {B : Type u₄} [Category.{v₄} B]

@[simp, to_dual none]
/-
**CategoryTheory.Functor.whiskerLeft_twice** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whis
kerLeft F (whiskerLeft G α) = (Functor.associator _ _ _).inv ≫ whiskerLeft (F ⋙ 
G) α ≫ (Functor.associator _ _ _).hom
参数：F : B ⥤ C；G : C ⥤ D；α : H ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) =
    (Functor.associator _ _ _).inv ≫ whiskerLeft (F ⋙ G) α ≫ (Functor.associator _ _ _).hom := by
  cat_disch

@[simp, to_dual none]
/-
**CategoryTheory.Functor.whiskerRight_twice** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) : whi
skerRight (whiskerRight α F) G = (Functor.associator _ _ _).hom ≫ whiskerRight α
 (F ⋙ G) ≫ (Functor.associator _ _ _).inv
参数：F : C ⥤ D；G : D ⥤ E；α : H ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G =
    (Functor.associator _ _ _).hom ≫ whiskerRight α (F ⋙ G) ≫ (Functor.associator _ _ _).inv := by
  cat_disch

@[to_dual none]
/-
**CategoryTheory.Functor.whiskerRight_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) : whis
kerRight (whiskerLeft F α) K = (Functor.associator _ _ _).hom ≫ whiskerLeft F (w
hiskerRight α K) ≫ (Functor.associator _ _ _).inv
参数：F : B ⥤ C；α : G ⟶ H；K : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K =
    (Functor.associator _ _ _).hom ≫ whiskerLeft F (whiskerRight α K) ≫
      (Functor.associator _ _ _).inv := by
  cat_disch

@[simp]
/-
**CategoryTheory.Functor.isoWhiskerLeft_twice** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K) : i
soWhiskerLeft F (isoWhiskerLeft G α) = (Functor.associator _ _ _).symm ≪≫ isoWhi
skerLeft (F ⋙ G) α ≪≫ Functor.associator _ _ _
参数：F : B ⥤ C；G : C ⥤ D；α : H ≅ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoWhiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ≅ K) :
    isoWhiskerLeft F (isoWhiskerLeft G α) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft (F ⋙ G) α ≪≫ Functor.associator _ _ _ := by
  cat_disch

@[simp, reassoc]
/-
**CategoryTheory.Functor.isoWhiskerRight_twice** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isoWhiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K) : 
isoWhiskerRight (isoWhiskerRight α F) G = Functor.associator _ _ _ ≪≫ isoWhisker
Right α (F ⋙ G) ≪≫ (Functor.associator _ _ _).symm
参数：F : C ⥤ D；G : D ⥤ E；α : H ≅ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_twice`：whiskerRight_twice {H K : B ⥤
 C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) : whiskerRight (whiskerRight α F) G = (F
unctor.associator _ _ _).hom ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoWhiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ≅ K) :
    isoWhiskerRight (isoWhiskerRight α F) G =
    Functor.associator _ _ _ ≪≫ isoWhiskerRight α (F ⋙ G) ≪≫ (Functor.associator _ _ _).symm := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.Functor.isoWhiskerRight_left** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) : i
soWhiskerRight (isoWhiskerLeft F α) K = Functor.associator _ _ _ ≪≫ isoWhiskerLe
ft F (isoWhiskerRight α K) ≪≫ (Functor.associator _ _ _).symm
参数：F : B ⥤ C；α : G ≅ H；K : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoWhiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerRight (isoWhiskerLeft F α) K =
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (isoWhiskerRight α K) ≪≫
      (Functor.associator _ _ _).symm := by
  cat_disch

@[reassoc]
/-
**CategoryTheory.Functor.isoWhiskerLeft_right** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isoWhiskerLeft_right (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) : i
soWhiskerLeft F (isoWhiskerRight α K) = (Functor.associator _ _ _).symm ≪≫ isoWh
iskerRight (isoWhiskerLeft F α) K ≪≫ Functor.associator _ _ _
参数：F : B ⥤ C；α : G ≅ H；K : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoWhiskerLeft_right (F : B ⥤ C) {G H : C ⥤ D} (α : G ≅ H) (K : D ⥤ E) :
    isoWhiskerLeft F (isoWhiskerRight α K) =
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (isoWhiskerLeft F α) K ≪≫
      Functor.associator _ _ _ := by
  cat_disch

end

universe u₅ v₅

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

@[reassoc]
/-
**CategoryTheory.Functor.triangleIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：triangleIso : associator F (𝟭 B) G ≪≫ isoWhiskerLeft F (leftUnitor G) = is
oWhiskerRight (rightUnitor F) G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangleIso :
    associator F (𝟭 B) G ≪≫ isoWhiskerLeft F (leftUnitor G) =
      isoWhiskerRight (rightUnitor F) G := by cat_disch

@[reassoc]
/-
**CategoryTheory.Functor.pentagonIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：pentagonIso : isoWhiskerRight (associator F G H) K ≪≫ associator F (G ⋙ H)
 K ≪≫ isoWhiskerLeft F (associator G H K) = associator (F ⋙ G) H K ≪≫ associator
 F G (H ⋙ K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagonIso :
    isoWhiskerRight (associator F G H) K ≪≫
        associator F (G ⋙ H) K ≪≫ isoWhiskerLeft F (associator G H K) =
      associator (F ⋙ G) H K ≪≫ associator F G (H ⋙ K) := by cat_disch
/-
**CategoryTheory.Functor.triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：triangle : (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
 whiskerRight (rightUnitor F).hom G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangle :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by cat_disch
/-
**CategoryTheory.Functor.pentagon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：pentagon : whiskerRight (associator F G H).hom K ≫ (associator F (G ⋙ H) K
).hom ≫ whiskerLeft F (associator G H K).hom = (associator (F ⋙ G) H K).hom ≫ (a
ssociator F G (H ⋙ K)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by cat_disch

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃] (E : Type*) [Category* E]

/-- The obvious functor `(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E)`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E)`.
-/
def whiskeringLeft₂ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E) where
  obj F₁ :=
    { obj := fun F₂ ↦
        (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
          (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁
      map := fun φ ↦ whiskerRight
        ((whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).map ((whiskeringLeft C₂ D₂ E).map φ)) _ }
  map ψ :=
    { app := fun F₂ ↦ whiskerLeft _ ((whiskeringLeft C₁ D₁ (C₂ ⥤ E)).map ψ) }

/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E :=
  (whiskeringRight _ _ _).obj (((whiskeringLeft₂ E).obj F₂).obj F₃) ⋙
    (whiskeringLeft C₁ D₁ _).obj F₁

/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃ObjObjMap (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) {F₃ F₃' : C₃ ⥤ D₃} (τ₃ : F₃ ⟶ F₃') :
    whiskeringLeft₃ObjObjObj E F₁ F₂ F₃ ⟶
      whiskeringLeft₃ObjObjObj E F₁ F₂ F₃' where
  app F := whiskerLeft _ (whiskerLeft _ (((whiskeringLeft₂ E).obj F₂).map τ₃))

variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₃ := whiskeringLeft₃ObjObjObj E F₁ F₂ F₃
  map τ₃ := whiskeringLeft₃ObjObjMap E F₁ F₂ τ₃

variable (C₃ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃ObjMap (F₁ : C₁ ⥤ D₁) {F₂ F₂' : C₂ ⥤ D₂} (τ₂ : F₂ ⟶ F₂') :
    whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂ ⟶ whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂' where
  app F₃ := whiskerRight ((whiskeringRight _ _ _).map (((whiskeringLeft₂ E).map τ₂).app F₃)) _

variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃Obj (F₁ : C₁ ⥤ D₁) :
    (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₂ := whiskeringLeft₃ObjObj C₃ D₃ E F₁ F₂
  map τ₂ := whiskeringLeft₃ObjMap C₃ D₃ E F₁ τ₂

variable (C₂ C₃ D₂ D₃) in
/-- Auxiliary definition for `whiskeringLeft₃`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `whiskeringLeft₃`.
-/
def whiskeringLeft₃Map {F₁ F₁' : C₁ ⥤ D₁} (τ₁ : F₁ ⟶ F₁') :
    whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁ ⟶ whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁' where
  app F₂ := { app F₃ := whiskerLeft _ ((whiskeringLeft _ _ _).map τ₁) }

/-- The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.whiskeringLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor
`(C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)`.
-/
def whiskeringLeft₃ :
    (C₁ ⥤ D₁) ⥤ (C₂ ⥤ D₂) ⥤ (C₃ ⥤ D₃) ⥤ (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) where
  obj F₁ := whiskeringLeft₃Obj C₂ C₃ D₂ D₃ E F₁
  map τ₁ := whiskeringLeft₃Map C₂ C₃ D₂ D₃ E τ₁

variable {E}

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E'`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E'`.
-/
def postcompose₂ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ E' :=
  whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

/-- The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E'`. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.Functor.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "postcomposition" with a functor `E ⥤ E'` gives a functor
`(E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E'`.
-/
def postcompose₃ {E' : Type*} [Category* E'] :
    (E ⥤ E') ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E' :=
  whiskeringRight C₃ _ _ ⋙ whiskeringRight C₂ _ _ ⋙ whiskeringRight C₁ _ _

end Functor

end CategoryTheory

