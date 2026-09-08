/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The bicategory of `V`-enriched categories

We define the bicategory `EnrichedCat V` of (bundled) `V`-enriched categories for a fixed monoidal
category `V`.

## Future work

* Define change of base and `ForgetEnrichment` as 2-functors.
* Define the bicategory of enriched ordinary categories.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe w v u u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- Category of `V`-enriched categories for a monoidal category `V`. -/
/-
**CategoryTheory.EnrichedCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：EnrichedCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category of `V`-enriched categories for a monoidal category `V`.
-/
def EnrichedCat := Bundled (EnrichedCategory.{w, v, u} V)

namespace EnrichedCat

/-
**CategoryTheory.EnrichedCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Enriched
Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (EnrichedCat V) (Type u) :=
  ⟨Bundled.α⟩
/-
**CategoryTheory.EnrichedCat.str** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Enric
hedCat`。
形式化陈述：str (C : EnrichedCat.{w, v, u} V) : EnrichedCategory.{w, v, u} V C
参数：C : EnrichedCat.{w, v, u} V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance str (C : EnrichedCat.{w, v, u} V) : EnrichedCategory.{w, v, u} V C :=
  Bundled.str C

/-- Construct a bundled `EnrichedCat` from the underlying type and the typeclass. -/
/-
**CategoryTheory.EnrichedCat.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Enrich
edCat`。
形式化陈述：of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `EnrichedCat` from the underlying type and the typeclass.
-/
def of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V :=
  Bundled.of C

open EnrichedCategory ForgetEnrichment

variable {V} {C : Type u} [EnrichedCategory V C] {D : Type u₁} [EnrichedCategory V D]
  {E : Type u₂} [EnrichedCategory V E] {E' : Type u₃} [EnrichedCategory V E']

/-- Whisker a `V`-enriched natural transformation on the left. -/
@[simps!]
/-
**CategoryTheory.EnrichedCat.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.EnrichedCat`。
形式化陈述：whiskerLeft (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α :
 G ⟶ H) : F.comp V G ⟶ F.comp V H
参数：F : EnrichedFunctor V C D；α : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a `V`-enriched natural transformation on the left.
-/
def whiskerLeft
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : G ⟶ H) :
    F.comp V G ⟶ F.comp V H :=
  ⟨(F.forgetComp G).hom ≫ F.forget.whiskerLeft α.out ≫ (F.forgetComp H).inv⟩

/-- Whisker a `V`-enriched natural transformation on the right. -/
@[simps!]
/-
**CategoryTheory.EnrichedCat.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.EnrichedCat`。
形式化陈述：whiskerRight {F G : EnrichedFunctor V C D} (α : F ⟶ G) (H : EnrichedFuncto
r V D E) : F.comp V H ⟶ G.comp V H
参数：α : F ⟶ G；H : EnrichedFunctor V D E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a `V`-enriched natural transformation on the right.
-/
def whiskerRight
    {F G : EnrichedFunctor V C D} (α : F ⟶ G) (H : EnrichedFunctor V D E) :
    F.comp V H ⟶ G.comp V H :=
  ⟨(F.forgetComp H).hom ≫ Functor.whiskerRight α.out H.forget ≫ (G.forgetComp H).inv⟩

/-- Composing the `V`-enriched identity functor with any functor is isomorphic to that functor. -/
@[simps!]
/-
**CategoryTheory.EnrichedCat.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.EnrichedCat`。
形式化陈述：leftUnitor (F : EnrichedFunctor V C D) : (EnrichedFunctor.id V _).comp V F
 ≅ F
参数：F : EnrichedFunctor V C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the `V`-enriched identity functor with any functor is isomorphic to th
at functor.
-/
def leftUnitor (F : EnrichedFunctor V C D) : (EnrichedFunctor.id V _).comp V F ≅ F :=
  EnrichedFunctor.isoMk <| (EnrichedFunctor.id V C).forgetComp F ≪≫
    Functor.isoWhiskerRight (EnrichedFunctor.forgetId V C) _ ≪≫ Functor.leftUnitor F.forget

/-- Composing any `V`-enriched functor with the identity functor is isomorphic to the former
functor. -/
@[simps!]
/-
**CategoryTheory.EnrichedCat.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.EnrichedCat`。
形式化陈述：rightUnitor (F : EnrichedFunctor V C D) : EnrichedFunctor.comp V F (Enrich
edFunctor.id V _) ≅ F
参数：F : EnrichedFunctor V C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing any `V`-enriched functor with the identity functor is isomorphic to th
e former
functor.
-/
def rightUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V _) ≅ F :=
  EnrichedFunctor.isoMk <| F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

/-- Composition of `V`-enriched functors is associative up to isomorphism. -/
@[simps!]
/-
**CategoryTheory.EnrichedCat.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.EnrichedCat`。
形式化陈述：associator (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E) (H : En
richedFunctor V E E') : EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H ≅ 
EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H)
参数：F : EnrichedFunctor V C D；G : EnrichedFunctor V D E；H : EnrichedFunctor V E E
'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `V`-enriched functors is associative up to isomorphism.
-/
def associator (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    (H : EnrichedFunctor V E E') :
    EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H ≅
    EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H) :=
  EnrichedFunctor.isoMk <| (F.comp V G).forgetComp H ≪≫
    Functor.isoWhiskerRight (F.forgetComp G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.forgetComp H).symm ≪≫
    (F.forgetComp _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.EnrichedCat.comp_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.EnrichedCat`。
形式化陈述：comp_whiskerRight {F G H : EnrichedFunctor V C D} (α : F ⟶ G) (β : G ⟶ H) 
(I : EnrichedFunctor V D E) : whiskerRight ⟨α.out ≫ β.out⟩ I = whiskerRight α I 
≫ whiskerRight β I
参数：α : F ⟶ G；β : G ⟶ H；I : EnrichedFunctor V D E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.EnrichedFunctor.hom_ext`：hom_ext {F G : EnrichedFunctor V
 C D} {α β : F ⟶ G} (h : forall X : C, α.out.app X = β.out.app X) : α = β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.EnrichedCat.whiskerRight_out_app`：∀ {V : Type v} [inst : 
CategoryTheory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] {
C : Type u}   [inst_2 : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.EnrichedFunctor.map_comp`：∀ {V : Type v} [inst : Category
Theory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : Type
 u₁}   [inst_2 : CategoryTheo…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_whiskerRight {F G H : EnrichedFunctor V C D} (α : F ⟶ G)
    (β : G ⟶ H) (I : EnrichedFunctor V D E) :
    whiskerRight ⟨α.out ≫ β.out⟩ I = whiskerRight α I ≫ whiskerRight β I := by
  ext X
  simp only [whiskerRight_out_app, NatTrans.comp_app, EnrichedFunctor.category_comp_out,
    EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map]
  simp [← ForgetEnrichment.homOf_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.EnrichedCat.whisker_exchange** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.EnrichedCat`。
形式化陈述：whisker_exchange {F G : EnrichedFunctor V C D} {H I : EnrichedFunctor V D 
E} (α : F ⟶ G) (β : H ⟶ I) : whiskerLeft F β ≫ whiskerRight α I = whiskerRight α
 H ≫ whiskerLeft G β
参数：α : F ⟶ G；β : H ⟶ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.EnrichedFunctor.hom_ext`：hom_ext {F G : EnrichedFunctor V
 C D} {α β : F ⟶ G} (h : forall X : C, α.out.app X = β.out.app X) : α = β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.EnrichedCat.whiskerLeft_out_app`：∀ {V : Type v} [inst : C
ategoryTheory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C
 : Type u}   [inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.EnrichedCat.whiskerRight_out_app`：∀ {V : Type v} [inst : 
CategoryTheory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] {
C : Type u}   [inst_2 : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma whisker_exchange {F G : EnrichedFunctor V C D} {H I : EnrichedFunctor V D E}
    (α : F ⟶ G) (β : H ⟶ I) :
    whiskerLeft F β ≫ whiskerRight α I = whiskerRight α H ≫ whiskerLeft G β := by
  ext X
  simp only [EnrichedFunctor.forget_obj, EnrichedFunctor.comp_obj,
    EnrichedFunctor.category_comp_out, NatTrans.comp_app, whiskerLeft_out_app,
    whiskerRight_out_app]
  exact (β.out.naturality (α.out.app (ForgetEnrichment.of V X))).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The bicategory structure on `EnrichedCat V` for a monoidal category `V`. -/
/-
**CategoryTheory.EnrichedCat.bicategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.EnrichedCat`。
形式化陈述：bicategory : Bicategory (EnrichedCat.{w, v, u} V) where Hom C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory structure on `EnrichedCat V` for a monoidal category `V`.
-/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H := whiskerLeft F
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerRight := comp_whiskerRight
  whisker_exchange := whisker_exchange

end EnrichedCat

end CategoryTheory

