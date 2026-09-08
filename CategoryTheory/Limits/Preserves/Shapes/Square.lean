/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Preservation of pullback/pushout squares

If a functor `F : C ⥤ D` preserves suitable cospans (resp. spans),
and `sq : Square C` is a pullback square (resp. a pushout square)
then so is the square `sq.map F`.

The lemma `Square.isPullback_iff_map_coyoneda_isPullback` also
shows that a square is a pullback square iff it is so after the
application of the functor `coyoneda.obj X` for all `X : Cᵒᵖ`.
Similarly, a square is a pushout square iff the opposite
square becomes a pullback square after the application of the
functor `yoneda.obj X` for all `X : C`.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Square

variable {sq : Square C}

/-
**CategoryTheory.Square.IsPullback.map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {sq : CategoryTheory.Square C},   s
q.IsPullback →     ∀ (F : CategoryTheory.Functor C D)       [CategoryTheory.Limi
ts.PreservesLimit (CategoryTheory.Limits.cospan sq.f₂₄ sq.f₃₄) F], (sq.map F).Is
Pullback
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan sq.f₂₄ sq.f₃₄；sq.
map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.mk`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limit
s.IsLimit sq.pullbackCone…
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma IsPullback.map (h : sq.IsPullback) (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback :=
  Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)
/-
**CategoryTheory.Square.IsPullback.of_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {sq : CategoryTheory.Square C} (F :
 CategoryTheory.Functor C D)   [CategoryTheory.Limits.ReflectsLimit (CategoryThe
ory.Limits.cospan sq.f₂₄ sq.f₃₄) F],   (sq.map F).IsPullback → sq.IsPullback
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan sq.f₂₄ sq.f₃₄；sq.
map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_map`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma IsPullback.of_map (F : C ⥤ D) [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F]
    (h : (sq.map F).IsPullback) : sq.IsPullback :=
  CategoryTheory.IsPullback.of_map F sq.fac h

variable (sq) in
/-
**CategoryTheory.Square.IsPullback.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Square.IsPullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (sq : CategoryTheory.Square C) (F :
 CategoryTheory.Functor C D)   [CategoryTheory.Limits.PreservesLimit (CategoryTh
eory.Limits.cospan sq.f₂₄ sq.f₃₄) F]   [CategoryTheory.Limits.ReflectsLimit (Cat
egoryTheory.Limits.cospan sq.f₂₄ sq.f₃₄) F],   (sq.map F).IsPullback ↔ sq.IsPull
back
参数：sq : CategoryTheory.Square C；F : CategoryTheory.Functor C D；CategoryTheory.Li
mits.cospan sq.f₂₄ sq.f₃₄；CategoryTheory.Limits.cospan sq.f₂₄ sq.f₃₄；sq.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.of_map`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} D]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.IsPullback.map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
D]   {sq : CategoryTheory.…
-/
lemma IsPullback.map_iff (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F]
    [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback ↔ sq.IsPullback :=
  ⟨fun h ↦ of_map F h, fun h ↦ h.map F⟩
/-
**CategoryTheory.Square.IsPushout.map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {sq : CategoryTheory.Square C},   s
q.IsPushout →     ∀ (F : CategoryTheory.Functor C D)       [CategoryTheory.Limit
s.PreservesColimit (CategoryTheory.Limits.span sq.f₁₂ sq.f₁₃) F], (sq.map F).IsP
ushout
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span sq.f₁₂ sq.f₁₃；sq.ma
p F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPushout.mk`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limits
.IsColimit sq.pushoutCoc…
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma IsPushout.map (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout :=
  Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)
/-
**CategoryTheory.Square.IsPushout.of_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {sq : CategoryTheory.Square C} (F :
 CategoryTheory.Functor C D)   [CategoryTheory.Limits.ReflectsColimit (CategoryT
heory.Limits.span sq.f₁₂ sq.f₁₃) F],   (sq.map F).IsPushout → sq.IsPushout
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span sq.f₁₂ sq.f₁₃；sq.ma
p F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_map`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
-/
lemma IsPushout.of_map (F : C ⥤ D) [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F]
    (h : (sq.map F).IsPushout) : sq.IsPushout :=
  CategoryTheory.IsPushout.of_map F sq.fac h

variable (sq) in
/-
**CategoryTheory.Square.IsPushout.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Square.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (sq : CategoryTheory.Square C) (F :
 CategoryTheory.Functor C D)   [CategoryTheory.Limits.PreservesColimit (Category
Theory.Limits.span sq.f₁₂ sq.f₁₃) F]   [CategoryTheory.Limits.ReflectsColimit (C
ategoryTheory.Limits.span sq.f₁₂ sq.f₁₃) F],   (sq.map F).IsPushout ↔ sq.IsPusho
ut
参数：sq : CategoryTheory.Square C；F : CategoryTheory.Functor C D；CategoryTheory.Li
mits.span sq.f₁₂ sq.f₁₃；CategoryTheory.Limits.span sq.f₁₂ sq.f₁₃；sq.map F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPushout.of_map`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'
} D]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.IsPushout.map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D
]   {sq : CategoryTheory.…
-/
lemma IsPushout.map_iff (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F]
    [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout ↔ sq.IsPushout :=
  ⟨fun h ↦ of_map F h, fun h ↦ h.map F⟩

variable (sq)
/-
**CategoryTheory.Square.isPullback_iff_map_coyoneda_isPullback** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Square`。
形式化陈述：isPullback_iff_map_coyoneda_isPullback : sq.IsPullback ↔ forall (X : Cᵒᵖ),
 (sq.map (coyoneda.obj X)).IsPullback
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
D]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.IsPullback.mk`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limit
s.IsLimit sq.pullbackCone…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isPullback_iff_map_coyoneda_isPullback :
    sq.IsPullback ↔ ∀ (X : Cᵒᵖ), (sq.map (coyoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.map _, fun h ↦ IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X ↦ (h X).isLimit))⟩
/-
**CategoryTheory.Square.isPushout_iff_op_map_yoneda_isPullback** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Square`。
形式化陈述：isPushout_iff_op_map_yoneda_isPullback : sq.IsPushout ↔ forall (X : C), (s
q.op.map (yoneda.obj X)).IsPullback
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Square.IsPullback.map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
D]   {sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.IsPushout.op`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {sq : CategoryTheory.Square C}, sq.IsPushout → sq.op.IsPull
back
· 使用定理 `CategoryTheory.Square.IsPushout.mk`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limits
.IsColimit sq.pushoutCoc…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Square.map_f₁₂`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (s
q : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.op_f₁₂`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] (sq : CategoryTheory.Square C), sq.op.f₁₂ = sq.f₂₄.op
· 使用定理 `CategoryTheory.Limits.PushoutCocone.op_π_app`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (c : Cat
egoryTheory.Limits.PushoutCocone f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Square.map_f₁₃`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (s
q : CategoryTheory.…
· 使用定理 `CategoryTheory.Square.op_f₁₃`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] (sq : CategoryTheory.Square C), sq.op.f₁₃ = sq.f₃₄.op
-/
lemma isPushout_iff_op_map_yoneda_isPullback :
    sq.IsPushout ↔ ∀ (X : C), (sq.op.map (yoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.op.map _, fun h ↦ IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X ↦ IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

section

variable {sq₁ : Square (Type v)} {sq₂ : Square (Type u)}
  (e₁ : sq₁.X₁ ≃ sq₂.X₁) (e₂ : sq₁.X₂ ≃ sq₂.X₂)
  (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄ : sq₁.X₄ ≃ sq₂.X₄)
  (comm₁₂ : e₂ ∘ sq₁.f₁₂ = sq₂.f₁₂ ∘ e₁)
  (comm₁₃ : e₃ ∘ sq₁.f₁₃ = sq₂.f₁₃ ∘ e₁)
  (comm₂₄ : e₄ ∘ sq₁.f₂₄ = sq₂.f₂₄ ∘ e₂)
  (comm₃₄ : e₄ ∘ sq₁.f₃₄ = sq₂.f₃₄ ∘ e₃)
include comm₁₂ comm₁₃ comm₂₄ comm₃₄

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (sq₁ sq₂) in
/-
**CategoryTheory.Square.IsPullback.iff_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Square.IsPullback`。
形式化陈述：∀ (sq₁ : CategoryTheory.Square (Type v)) (sq₂ : CategoryTheory.Square (Typ
e u)) (e₁ : sq₁.X₁ ≃ sq₂.X₁)   (e₂ : sq₁.X₂ ≃ sq₂.X₂) (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄
 : sq₁.X₄ ≃ sq₂.X₄),   ⇑e₂ ∘ ⇑(CategoryTheory.ConcreteCategory.hom sq₁.f₁₂) = ⇑(
CategoryTheory.ConcreteCategory.hom sq₂.f₁₂) ∘ ⇑e₁ →     ⇑e₃ ∘ ⇑(CategoryTheory.
ConcreteCategory.hom sq₁.f₁₃) = ⇑(CategoryTheory.ConcreteCategory.hom sq₂.f₁₃) ∘
 ⇑e₁ →       ⇑e₄ ∘ ⇑(CategoryTheory.ConcreteCategory.hom sq₁.f₂₄) = ⇑(CategoryTh
eory.ConcreteCategory.hom sq₂.f₂₄) ∘ ⇑e₂ →         ⇑e₄ ∘ ⇑(CategoryTheory.Concre
teCategory.hom sq₁.f₃₄) = ⇑(CategoryTheory.ConcreteCategory.hom sq₂.f₃₄) ∘ ⇑e₃ →
           (sq₁.IsPullback ↔ sq₂.IsPullback)
参数：sq₁ : CategoryTheory.Square (Type v)；sq₂ : CategoryTheory.Square (Type u)；e₁ 
: sq₁.X₁ ≃ sq₂.X₁；e₂ : sq₁.X₂ ≃ sq₂.X₂；e₃ : sq₁.X₃ ≃ sq₂.X₃；e₄ : sq₁.X₄ ≃ sq₂.X₄
；CategoryTheory.ConcreteCategory.hom sq₁.f₁₂；CategoryTheory.ConcreteCategory.hom
 sq₂.f₁₂；CategoryTheory.ConcreteCategory.hom sq₁.f₁₃；CategoryTheory.ConcreteCate
gory.hom sq₂.f₁₃；CategoryTheory.ConcreteCategory.hom sq₁.f₂₄；CategoryTheory.Conc
reteCategory.hom sq₂.f₂₄；CategoryTheory.ConcreteCategory.hom sq₁.f₃₄；CategoryThe
ory.ConcreteCategory.hom sq₂.f₃₄；sq₁.IsPullback ↔ sq₂.IsPullback。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Square.IsPullback.map_iff`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', 
u'} D]   (sq : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.instPreservesLimitsOfSizeUliftFunctor`：Categ
oryTheory.Limits.PreservesLimitsOfSize.{w', w, u, max u v, u + 1, max (u + 1) (v
 + 1)}   CategoryTheory.uliftFunctor.{v, u}
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `CategoryTheory.Square.IsPullback.iff_of_iso`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {sq₁ sq₂ : CategoryTheory.Square C} (e : sq₁ ≅ sq₂
),   sq₁.IsPullback ↔ sq₂.IsPullb…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma IsPullback.iff_of_equiv : sq₁.IsPullback ↔ sq₂.IsPullback := by
  rw [← IsPullback.map_iff sq₁ uliftFunctor.{max u v},
      ← IsPullback.map_iff sq₂ uliftFunctor.{max u v}]
  refine iff_of_iso (Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₃).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₄).trans Equiv.ulift.symm).toIso)
    ?_ ?_ ?_ ?_)
  all_goals ext; apply ULift.down_injective
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₂ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₃ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₂₄ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₃₄ _
/-
**CategoryTheory.Square.IsPullback.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Square.IsPullback`。
形式化陈述：∀ {sq₁ : CategoryTheory.Square (Type v)} {sq₂ : CategoryTheory.Square (Typ
e u)} (e₁ : sq₁.X₁ ≃ sq₂.X₁)   (e₂ : sq₁.X₂ ≃ sq₂.X₂) (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄
 : sq₁.X₄ ≃ sq₂.X₄),   ⇑e₂ ∘ ⇑(CategoryTheory.ConcreteCategory.hom sq₁.f₁₂) = ⇑(
CategoryTheory.ConcreteCategory.hom sq₂.f₁₂) ∘ ⇑e₁ →     ⇑e₃ ∘ ⇑(CategoryTheory.
ConcreteCategory.hom sq₁.f₁₃) = ⇑(CategoryTheory.ConcreteCategory.hom sq₂.f₁₃) ∘
 ⇑e₁ →       ⇑e₄ ∘ ⇑(CategoryTheory.ConcreteCategory.hom sq₁.f₂₄) = ⇑(CategoryTh
eory.ConcreteCategory.hom sq₂.f₂₄) ∘ ⇑e₂ →         ⇑e₄ ∘ ⇑(CategoryTheory.Concre
teCategory.hom sq₁.f₃₄) = ⇑(CategoryTheory.ConcreteCategory.hom sq₂.f₃₄) ∘ ⇑e₃ →
           sq₁.IsPullback → sq₂.IsPullback
参数：Type v；Type u；e₁ : sq₁.X₁ ≃ sq₂.X₁；e₂ : sq₁.X₂ ≃ sq₂.X₂；e₃ : sq₁.X₃ ≃ sq₂.X₃；
e₄ : sq₁.X₄ ≃ sq₂.X₄；CategoryTheory.ConcreteCategory.hom sq₁.f₁₂；CategoryTheory.
ConcreteCategory.hom sq₂.f₁₂；CategoryTheory.ConcreteCategory.hom sq₁.f₁₃；Categor
yTheory.ConcreteCategory.hom sq₂.f₁₃；CategoryTheory.ConcreteCategory.hom sq₁.f₂₄
；CategoryTheory.ConcreteCategory.hom sq₂.f₂₄；CategoryTheory.ConcreteCategory.hom
 sq₁.f₃₄；CategoryTheory.ConcreteCategory.hom sq₂.f₃₄。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Square.IsPullback.iff_of_equiv`：∀ (sq₁ : CategoryTheory.S
quare (Type v)) (sq₂ : CategoryTheory.Square (Type u)) (e₁ : sq₁.X₁ ≃ sq₂.X₁)   
(e₂ : sq₁.X₂ ≃ sq₂.X₂) (e₃ : sq₁.X₃…
-/
lemma IsPullback.of_equiv (h₁ : sq₁.IsPullback) : sq₂.IsPullback :=
  (iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄ comm₁₂ comm₁₃ comm₂₄ comm₃₄).1 h₁

end

end Square

end CategoryTheory

