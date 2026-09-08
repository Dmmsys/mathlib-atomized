/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Chosen.End

/-!
# Ends and coends in `Type`

This file constructs explicit ends and coends in `Type` and provides
`ChosenEnds` and `ChosenCoends` instances using these constructions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite TypeCat ConcreteCategory

namespace Limits.Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

/-- The relation on the sigma type `(W : J) × (F.obj (op W)).obj W` used to construct explicit
coends in `Type`. Two terms `⟨j, x⟩` and `⟨j', x'⟩` are related if and only if there is a
morphism `f : j ⟶ j'` in `J` and an element `y : (F.obj (op j')).obj j` such that
`(F.map f.op).app j y = x` and `(F.obj _).map f y = x'`, see `coendRel_iff` below. -/
/-
**CategoryTheory.Limits.Types.coendRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Limits.Types`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     (F : Cate
goryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))) →       (j :
 J) × (F.obj (Opposite.op j)).obj j → (j : J) × (F.obj (Opposite.op j)).obj j → 
Prop
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))；j 
: J；F.obj (Opposite.op j)；j : J；F.obj (Opposite.op j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on the sigma type `(W : J) × (F.obj (op W)).obj W` used to construc
t explicit
coends in `Type`. Two terms `⟨j, x⟩` and `⟨j', x'⟩` are related if and only if t
here is a
morphism `f : j ⟶ j'` in `J` and an element `y : (F.obj (op j')).obj j` such tha
t
`(F.map f.op).app j y = x` and `(F.obj _).map f y = x'`, see `coendRel_iff` belo
w.
-/
inductive coendRel : (j : J) × (F.obj (op j)).obj j → (j : J) × (F.obj (op j)).obj j → Prop where
  | mk {j j' : J} (f : j ⟶ j') (x : (F.obj (op j')).obj j) :
    coendRel ⟨j, TypeCat.Hom.hom ((F.map f.op).app _) x⟩
      ⟨j', TypeCat.Hom.hom ((F.obj _).map f) x⟩
/-
**CategoryTheory.Limits.Types.coendRel_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits.Types`。
形式化陈述：coendRel_iff (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).o
bj j') : coendRel F ⟨j, x⟩ ⟨j', x'⟩ ↔ exists (f : j ⟶ j') (y : (F.obj (op j')).o
bj j), (F.map f.op).app _ y = x ∧ (F.obj _).map f y = x'
参数：j j' : J；x : (F.obj (op j)).obj j；x' : (F.obj (op j')).obj j'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma coendRel_iff (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j') :
    coendRel F ⟨j, x⟩ ⟨j', x'⟩ ↔
      ∃ (f : j ⟶ j') (y : (F.obj (op j')).obj j),
        (F.map f.op).app _ y = x ∧ (F.obj _).map f y = x' := by
  constructor
  · rintro ⟨f, x⟩
    exact ⟨f, x, by simp⟩
  · rintro ⟨f, y, rfl, rfl⟩
    exact coendRel.mk f y

/-- The coend of a bifunctor valued in `Type`, defined as a quotient. -/
/-
**CategoryTheory.Limits.Types.coend** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits.Types`。
形式化陈述：coend : Type max w u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coend of a bifunctor valued in `Type`, defined as a quotient.
-/
abbrev coend : Type max w u := Quot (coendRel F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ Type*`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend F`
for any `j : J`, which sends `x` to `Quot.mk _ ⟨j, x⟩` -/
/-
**CategoryTheory.Limits.Types.coend.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ Type*`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend
 F`
for any `j : J`, which sends `x` to `Quot.mk _ ⟨j, x⟩`
-/
def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F := ↾fun x ↦ Quot.mk _ ⟨j, x⟩

variable {F}

@[reassoc]
/-
**CategoryTheory.Limits.Types.coend.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Types.coend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} {j j' : J} (f : j 
⟶ j'),   CategoryTheory.CategoryStruct.comp ((F.map f.op).app j) (CategoryTheory
.Limits.Types.coend.ι F j) =     CategoryTheory.CategoryStruct.comp ((F.obj (Opp
osite.op j')).map f) (CategoryTheory.Limits.Types.coend.ι F j')
参数：CategoryTheory.Functor J (Type (max w u))；f : j ⟶ j'；(F.map f.op).app j；Categ
oryTheory.Limits.Types.coend.ι F j；(F.obj (Opposite.op j')).map f；CategoryTheory
.Limits.Types.coend.ι F j'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma coend.condition {j j' : J} (f : j ⟶ j') :
    (F.map f.op).app _ ≫ coend.ι F j = (F.obj _).map f ≫ coend.ι F j' := by
  ext
  apply Quot.sound
  apply coendRel.mk

variable (F)

/-- The cowedge corresponding to the explicit coend in `Type` -/
/-
**CategoryTheory.Limits.Types.cowedge** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Types`。
形式化陈述：cowedge : Cowedge F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cowedge corresponding to the explicit coend in `Type`
-/
def cowedge : Cowedge F := Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition)

/-- The cowedge corresponding to the explicit coend in `Type` is colimiting. -/
/-
**CategoryTheory.Limits.Types.cowedgeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Types`。
形式化陈述：cowedgeIsColimit : IsColimit (cowedge F) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cowedge corresponding to the explicit coend in `Type` is colimiting.
-/
def cowedgeIsColimit : IsColimit (cowedge F) where
  desc s := TypeCat.ofHom <| Quot.lift (fun x ↦ Multicofork.π s x.fst x.snd) fun _ _ h ↦ by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

end Types

/-- A `ChosenCoends` instance on `Type` given by the explicit quotient construction above. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ChosenCoends` instance on `Type` given by the explicit quotient construction 
above.
-/
instance : ChosenCoends.{v, u} (Type max w u) where
  cowedge := Types.cowedge
  isCoend := Types.cowedgeIsColimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}
/-
**CategoryTheory.Limits.Types.chosenCoend_def** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Types`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))},   CategoryTheory.
Limits.chosenCoend F = Quot (CategoryTheory.Limits.Types.coendRel F)
参数：CategoryTheory.Functor J (Type (max w u))；CategoryTheory.Limits.Types.coendRe
l F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Types.chosenCoend_def : chosenCoend F = Quot (coendRel F) := rfl

attribute [local simp] Types.chosenCoend_def
/-
**CategoryTheory.Limits.chosenCoend.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenCoend.ι_apply (j : J) (x : (F.obj (op j)).obj j) :
    dsimp% chosenCoend.ι F j x = Quot.mk _ ⟨j, x⟩ :=
  rfl
/-
**CategoryTheory.Limits.chosenCoend.desc_apply** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} {X : Type (max w u
)}   (f : (j : J) → (F.obj (Opposite.op j)).obj j ⟶ X)   (hf :     ∀ ⦃i j : J⦄ (
g : i ⟶ j),       CategoryTheory.CategoryStruct.comp ((F.map g.op).app i) (f i) 
=         CategoryTheory.CategoryStruct.comp ((F.obj (Opposite.op j)).map g) (f 
j))   (x : CategoryTheory.Limits.chosenCoend F),   (CategoryTheory.ConcreteCateg
ory.hom (CategoryTheory.Limits.chosenCoend.desc f hf)) x =     Quot.lift (fun j 
=> (CategoryTheory.ConcreteCategory.hom (f j.fst)) j.snd) ⋯ x
参数：CategoryTheory.Functor J (Type (max w u))；max w u；f : (j : J) → (F.obj (Oppos
ite.op j)).obj j ⟶ X；hf :     ∀ ⦃i j : J⦄ (g : i ⟶ j),       CategoryTheory.Cate
goryStruct.comp ((F.map g.op).app i) (f i) =         CategoryTheory.CategoryStru
ct.comp ((F.obj (Opposite.op j)).map g) (f j)；x : CategoryTheory.Limits.chosenCo
end F；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.chosenCoend.des
c f hf)；fun j => (CategoryTheory.ConcreteCategory.hom (f j.fst)) j.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenCoend.desc_apply {X : Type max w u} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)
    (x : chosenCoend F) : dsimp% chosenCoend.desc f hf x =
      Quot.lift (fun j ↦ f j.fst j.snd) (fun _ _ h ↦ by
        cases h with | mk f x => exact ConcreteCategory.congr_hom (hf f) _) x :=
  rfl
/-
**CategoryTheory.Limits.chosenCoend.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.chosenCoend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F G : Category
Theory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} (f : F ⟶ G)   (x
 : CategoryTheory.Limits.chosenCoend F),   (CategoryTheory.ConcreteCategory.hom 
(CategoryTheory.Limits.chosenCoend.map f)) x =     Quot.lift       (fun x =>    
     Quot.mk (CategoryTheory.Limits.Types.coendRel G)           ⟨x.fst, (Categor
yTheory.ConcreteCategory.hom ((f.app (Opposite.op x.fst)).app x.fst)) x.snd⟩)   
    ⋯ x
参数：CategoryTheory.Functor J (Type (max w u))；f : F ⟶ G；x : CategoryTheory.Limits
.chosenCoend F；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.chosen
Coend.map f)；fun x =>         Quot.mk (CategoryTheory.Limits.Types.coendRel G)  
         ⟨x.fst, (CategoryTheory.ConcreteCategory.hom ((f.app (Opposite.op x.fst
)).app x.fst)) x.snd⟩。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenCoend.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F) :
    dsimp% chosenCoend.map f x =
      Quot.lift (fun ⟨j, y⟩ ↦ Quot.mk _ ⟨j, (f.app _).app _ y⟩) (fun _ _ ↦ by
        rintro ⟨g, y⟩
        apply Quot.sound
        rw [Types.coendRel_iff]
        refine ⟨g, (f.app _).app _ y, ?_, ?_⟩
        · simp only [← NatTrans.comp_app_apply, f.naturality]
        · simp [← NatTrans.naturality_apply]) x :=
  rfl

namespace Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

/-- The end of a bifunctor valued in `Type`, defined as the subtype of compatible families. -/
/-
**CategoryTheory.Limits.Types.end_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Types`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     CategoryT
heory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u))) → Type (max w u)
参数：CategoryTheory.Functor J (Type (max w u))；max w u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The end of a bifunctor valued in `Type`, defined as the subtype of compatible fa
milies.
-/
abbrev end_ : Type max w u :=
  { x : ∀ j, (F.obj (op j)).obj j // ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TypeCat.Hom.hom ((F.obj (op i)).map f) (x i) =
        TypeCat.Hom.hom ((F.map f.op).app j) (x j) }

/-- Given `F : Jᵒᵖ ⥤ J ⥤ Type*`, this is the projection `end_ F ⟶ (F.obj (op j)).obj j`
for any `j : J`, which sends `x` to `x.1 j`. -/
/-
**CategoryTheory.Limits.Types.end_.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ Type*`, this is the projection `end_ F ⟶ (F.obj (op j)).obj
 j`
for any `j : J`, which sends `x` to `x.1 j`.
-/
def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := ↾fun x ↦ x.1 j

variable {F}

@[reassoc]
/-
**CategoryTheory.Limits.Types.end_.condition** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types.end_`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} {i j : J} (f : i ⟶
 j),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Types.end_.π F 
i) ((F.obj (Opposite.op i)).map f) =     CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.Limits.Types.end_.π F j) ((F.map f.op).app j)
参数：CategoryTheory.Functor J (Type (max w u))；f : i ⟶ j；CategoryTheory.Limits.Typ
es.end_.π F i；(F.obj (Opposite.op i)).map f；CategoryTheory.Limits.Types.end_.π F
 j；(F.map f.op).app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma end_.condition {i j : J} (f : i ⟶ j) :
    end_.π F i ≫ (F.obj (op i)).map f = end_.π F j ≫ (F.map f.op).app j := by
  ext x
  exact x.2 f

variable (F)

/-- The wedge corresponding to the explicit end in `Type`. -/
/-
**CategoryTheory.Limits.Types.wedge** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Types`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     (F : Cate
goryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))) → CategoryTh
eory.Limits.Wedge F
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The wedge corresponding to the explicit end in `Type`.
-/
def wedge : Wedge F := Wedge.mk (end_ F) (end_.π F) (by intros; apply end_.condition)

/-- The wedge corresponding to the explicit end in `Type` is limiting. -/
/-
**CategoryTheory.Limits.Types.wedgeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Types`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     (F : Cate
goryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))) →       Cate
goryTheory.Limits.IsLimit (CategoryTheory.Limits.Types.wedge F)
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))；Ca
tegoryTheory.Limits.Types.wedge F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The wedge corresponding to the explicit end in `Type` is limiting.
-/
def wedgeIsLimit : IsLimit (wedge F) where
  lift s := TypeCat.ofHom <| fun x ↦
    (⟨fun j : J ↦ Multifork.ι s j x, fun _ _ f ↦ by
      exact ConcreteCategory.congr_hom (Wedge.condition s f) x⟩ : end_ F)
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by
    ext x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (h (.left j)) x

end Types

/-- A `ChosenEnds` instance on `Type` given by the explicit subtype construction above. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ChosenEnds` instance on `Type` given by the explicit subtype construction abo
ve.
-/
instance : ChosenEnds.{v, u} (Type max w u) where
  wedge := Types.wedge
  isEnd := Types.wedgeIsLimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}
/-
**CategoryTheory.Limits.Types.chosenEnd_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Types`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))},   CategoryTheory.
Limits.chosenEnd F = CategoryTheory.Limits.Types.end_ F
参数：CategoryTheory.Functor J (Type (max w u))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Types.chosenEnd_def : chosenEnd F = Types.end_ F := rfl

attribute [local simp] Types.chosenEnd_def
/-
**CategoryTheory.Limits.chosenEnd.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenEnd.π_apply (j : J) (x : Types.end_ F) :
    dsimp% chosenEnd.π (C := Type max w u) F j x = x.1 j :=
  rfl
/-
**CategoryTheory.Limits.chosenEnd.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F : CategoryTh
eory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} {X : Type (max w u
)}   (f : (j : J) → X ⟶ (F.obj (Opposite.op j)).obj j)   (hf :     ∀ ⦃i j : J⦄ (
g : i ⟶ j),       CategoryTheory.CategoryStruct.comp (f i) ((F.obj (Opposite.op 
i)).map g) =         CategoryTheory.CategoryStruct.comp (f j) ((F.map g.op).app 
j))   (x : X),   (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.cho
senEnd.lift f hf)) x =     ⟨fun j => (CategoryTheory.ConcreteCategory.hom (f j))
 x, ⋯⟩
参数：CategoryTheory.Functor J (Type (max w u))；max w u；f : (j : J) → X ⟶ (F.obj (O
pposite.op j)).obj j；hf :     ∀ ⦃i j : J⦄ (g : i ⟶ j),       CategoryTheory.Cate
goryStruct.comp (f i) ((F.obj (Opposite.op i)).map g) =         CategoryTheory.C
ategoryStruct.comp (f j) ((F.map g.op).app j)；x : X；CategoryTheory.ConcreteCateg
ory.hom (CategoryTheory.Limits.chosenEnd.lift f hf)；CategoryTheory.ConcreteCateg
ory.hom (f j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenEnd.lift_apply {X : Type max w u} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)
    (x : X) : dsimp% chosenEnd.lift (C := Type max w u) (F := F) f hf x =
      (⟨fun j ↦ f j x, fun _ _ g ↦ ConcreteCategory.congr_hom (hf g) x⟩ : Types.end_ F) :=
  rfl
/-
**CategoryTheory.Limits.chosenEnd.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.chosenEnd`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J]   {F G : Category
Theory.Functor Jᵒᵖ (CategoryTheory.Functor J (Type (max w u)))} (f : F ⟶ G)   (x
 : CategoryTheory.Limits.Types.end_ F),   (CategoryTheory.ConcreteCategory.hom (
CategoryTheory.Limits.chosenEnd.map f)) x =     ⟨fun j => (CategoryTheory.Concre
teCategory.hom ((f.app (Opposite.op j)).app j)) (↑x j), ⋯⟩
参数：CategoryTheory.Functor J (Type (max w u))；f : F ⟶ G；x : CategoryTheory.Limits
.Types.end_ F；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.chosenE
nd.map f)；CategoryTheory.ConcreteCategory.hom ((f.app (Opposite.op j)).app j)；↑x
 j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chosenEnd.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G)
    (x : Types.end_ F) :
    dsimp% chosenEnd.map (C := Type max w u) f x =
      ⟨fun j ↦ (f.app (op j)).app j (x.1 j), by
        intro i j g
        rw [← (f.app (op i)).naturality_apply]
        simp [x.2 g, ← comp_apply, -types_comp_apply]⟩ :=
  rfl

end CategoryTheory.Limits

