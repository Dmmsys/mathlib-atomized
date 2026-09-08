/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monad.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Adjunctions related to the over category

In a category with pullbacks, for any morphism `f : X ⟶ Y`, the functor
`Over.map f : Over X ⥤ Over Y` has a right adjoint `Over.pullback f`.

In a category with binary products, for any object `X` the functor
`Over.forget X : Over X ⥤ C` has a right adjoint `Over.star X`.

## Main declarations

- `Over.pullback f : Over Y ⥤ Over X` is the functor induced by a morphism `f : X ⟶ Y`.
- `Over.mapPullbackAdj` is the adjunction `Over.map f ⊣ Over.pullback f`.
- `star : C ⥤ Over X` is the functor induced by an object `X`.
- `forgetAdjStar` is the adjunction  `forget X ⊣ star X`.

## TODO
Show `star X` itself has a right adjoint provided `C` is Cartesian closed and has pullbacks.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X Y : C)
variable {D : Type u₂} [Category.{v₂} D]


namespace Over

open Limits

attribute [local instance] hasPullback_of_right_iso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤ Over X`,
by pulling back a morphism along `f`. -/
@[simps! +simpRhs obj_left obj_hom map_left, implicit_reducible]
/-
**CategoryTheory.Over.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : Over Y ⥤ Over X whe
re obj g
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤
 Over X`,
by pulling back a morphism along `f`.
-/
def pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.Over.mapPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：mapPullbackAdj {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : Over.map f ⊣ 
pullback f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Over.map f` is left adjoint to `Over.pullback f`.
-/
def mapPullbackAdj {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
          invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp [← Over.w v, pullback.condition]
          left_inv := by cat_disch
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : (Over.map f).IsLeftAdjoint :=
  (Over.mapPullbackAdj f).isLeftAdjoint
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : (Over.pullback f).IsRightAdjoint :=
  (Over.mapPullbackAdj f).isRightAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- The pullback along an epi that's preserved under pullbacks is faithful.

This "preserved under pullbacks" condition is automatically satisfied in abelian categories:
```
example [Abelian C] [Epi f] : (pullback f).Faithful := inferInstance
```
-/
/-
**CategoryTheory.Over.faithful_pullback** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：faithful_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] [forall Z (g
 : Z ⟶ Y), Epi (pullback.fst g f)] : (pullback f).Faithful
参数：f : X ⟶ Y；g : Z ⟶ Y；pullback.fst g f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.mapPullbackAdj_counit_app`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasPullbacksAlong f] (Y_1 :…
· 使用引理 `CategoryTheory.Adjunction.faithful_R_of_epi_counit_app`：faithful_R_of_ep
i_counit_app [forall X, Epi (h.counit.app X)] : R.Faithful where map_injective {
X Y f g} hfg

--- 原说明 ---
The pullback along an epi that's preserved under pullbacks is faithful.

This "preserved under pullbacks" condition is automatically satisfied in abelian
 categories:
```
example [Abelian C] [Epi f] : (pullback f).Faithful := inferInstance
```
-/
instance faithful_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [∀ Z (g : Z ⟶ Y), Epi (pullback.fst g f)] : (pullback f).Faithful := by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by
    simp only [Functor.comp_obj, Functor.id_obj, mapPullbackAdj_counit_app]; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

/-- pullback (𝟙 X) : Over X ⥤ Over X is the identity functor. -/
/-
**CategoryTheory.Over.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`
。
形式化陈述：pullbackId {X : C} : pullback (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pullback (𝟙 X) : Over X ⥤ Over X is the identity functor.
-/
def pullbackId {X : C} : pullback (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

/-- pullback commutes with composition (up to natural isomorphism). -/
/-
**CategoryTheory.Over.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [Ha
sPullbacksAlong g] : pullback (f ≫ g) ≅ pullback g ⋙ pullback f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pullback commutes with composition (up to natural isomorphism).
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm
/-
**CategoryTheory.Over.pullbackIsRightAdjoint** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Over`。
形式化陈述：pullbackIsRightAdjoint {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : (pull
back f).IsRightAdjoint
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pullbackIsRightAdjoint {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    (pullback f).IsRightAdjoint :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open pullback in
/-- If `F` is a left adjoint and its source category has pullbacks, then so is
`post F : Over Y ⥤ Over (G Y)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(Y ⟶ F X) ↦ (G Y ⟶ X ×_{G F X} G Y ⟶ X)`. -/
@[simps!]
/-
**CategoryTheory.Over.postAdjunctionLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Over`。
形式化陈述：postAdjunctionLeft [HasPullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F
 ⊣ G) : post F ⊣ post G ⋙ pullback (a.unit.app X)
参数：a : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is a left adjoint and its source category has pullbacks, then so is
`post F : Over Y ⥤ Over (G Y)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given 
by
`(Y ⟶ F X) ↦ (G Y ⟶ X ×_{G F X} G Y ⟶ X)`.
-/
def postAdjunctionLeft [HasPullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⊣ post G ⋙ pullback (a.unit.app X) :=
  ((mapPullbackAdj (a.unit.app X)).comp (postAdjunctionRight a)).ofNatIsoLeft <|
    NatIso.ofComponents fun Y ↦ isoMk (.refl _)
/-
**CategoryTheory.Over.isLeftAdjoint_post** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Over`。
形式化陈述：isLeftAdjoint_post [HasPullbacks C] {F : C ⥤ D} [F.IsLeftAdjoint] : (post 
(X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance isLeftAdjoint_post [HasPullbacks C] {F : C ⥤ D} [F.IsLeftAdjoint] :
    (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

open Limits

set_option backward.defeqAttrib.useBackward true in
/-- The category over any object `X` factors through the category over the terminal object `T`. -/
@[simps!]
/-
**CategoryTheory.Over.forgetMapTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：forgetMapTerminal {T : C} (hT : IsTerminal T) : forget X ≅ map (hT.from X)
 ⋙ (equivalenceOfIsTerminal hT).functor
参数：hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category over any object `X` factors through the category over the terminal 
object `T`.
-/
noncomputable def forgetMapTerminal {T : C} (hT : IsTerminal T) :
    forget X ≅ map (hT.from X) ⋙ (equivalenceOfIsTerminal hT).functor :=
  NatIso.ofComponents fun X ↦ .refl _

section HasBinaryProducts
variable [HasBinaryProducts C]

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
/-
**CategoryTheory.Over.star** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：star : C ⥤ Over X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, someti
mes denoted `X*`.
-/
def star : C ⥤ Over X := cofree _ ⋙ coalgebraToOver X

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
/-
**CategoryTheory.Over.forgetAdjStar** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ov
er`。
形式化陈述：forgetAdjStar : forget X ⊣ star X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right 
adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar : forget X ⊣ star X := (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Over.forgetAdjStar_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Over`。
形式化陈述：forgetAdjStar_counit_app (X Y : C) : (Over.forgetAdjStar X).counit.app Y =
 prod.snd
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Comonad.adj_counit`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] (G : CategoryTheory.Comonad C),   G.adj.counit = { app :=
 fun Y => G.ε.app Y, na…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma forgetAdjStar_counit_app (X Y : C) : (Over.forgetAdjStar X).counit.app Y = prod.snd := by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Over.forgetAdjStar_unit_app_left** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：forgetAdjStar_unit_app_left (X : C) (Y : Over X) : ((Over.forgetAdjStar X)
.unit.app Y).left = prod.lift Y.hom (𝟙 _)
参数：X : C；Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.mk.congr_simp`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} {A B : G.
Coalgebra}   (f f_1 : A.A ⟶ B.A) (e_f : …
· 使用定理 `CategoryTheory.Comonad.adj_unit`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (G : CategoryTheory.Comonad C),   G.adj.unit = { app := fun
 X => { f := X.a, h :…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma forgetAdjStar_unit_app_left (X : C) (Y : Over X) :
    ((Over.forgetAdjStar X).unit.app Y).left = prod.lift Y.hom (𝟙 _) := by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (star X).IsRightAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`. -/
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the binary products assumption is necessary: the existence of a right 
adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance : (forget X).IsLeftAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lifting to over `Y` and pulling back along `X ⟶ Y` is the same as lifting to over `X`. -/
@[simps!]
/-
**CategoryTheory.Over.starPullbackIsoStar** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：starPullbackIsoStar [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : star Y ⋙ pull
back f ≅ star X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting to over `Y` and pulling back along `X ⟶ Y` is the same as lifting to ove
r `X`.
-/
noncomputable def starPullbackIsoStar [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    star Y ⋙ pullback f ≅ star X :=
  NatIso.ofComponents
    (fun Z ↦
      Over.isoMk
      (pullback.congrHom (by simp) rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackProdFstIsoProd _ _)
    (by simp))

end HasBinaryProducts
end Over

namespace Under

attribute [local instance] hasPushout_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
/-
**CategoryTheory.Under.pushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] : Under X ⥤ Under Y whe
re obj x
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under
 Y`,
by pushing a morphism forward along `f`.
-/
def pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    Under X ⥤ Under Y where
  obj x := Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

set_option backward.isDefEq.respectTransparency false in
/-- `Under.pushout f` is left adjoint to `Under.map f`. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.Under.mapPushoutAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.U
nder`。
形式化陈述：mapPushoutAdj {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] : pushout f ⊣ map
 f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Under.pushout f` is left adjoint to `Under.map f`.
-/
def mapPushoutAdj {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    pushout f ⊣ map f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
      toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) <| by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [map_obj_right, pushout_obj, mk_right, mk_hom]
        rw [← assoc, ← assoc, pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by cat_disch
    }
  }

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- simp followed by infer_instance
/-- The pushout along a mono that's preserved under pushouts is faithful.

This "preserved under pushouts" condition is automatically satisfied in abelian categories:
```
example [Abelian C] [Mono f] : (pushout f).Faithful := inferInstance
```
-/
/-
**CategoryTheory.Under.faithful_pushout** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Under`。
形式化陈述：faithful_pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] [forall Z (g :
 X ⟶ Z), Mono (pushout.inl g f)] : (pushout f).Faithful
参数：f : X ⟶ Y；g : X ⟶ Z；pushout.inl g f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Under.mapPushoutAdj_unit_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasPushoutsAlong f] (X_1 : …
· 使用引理 `CategoryTheory.Adjunction.faithful_L_of_mono_unit_app`：faithful_L_of_mon
o_unit_app [forall X, Mono (h.unit.app X)] : L.Faithful where map_injective {X Y
 f g} hfg

--- 原说明 ---
The pushout along a mono that's preserved under pushouts is faithful.

This "preserved under pushouts" condition is automatically satisfied in abelian 
categories:
```
example [Abelian C] [Mono f] : (pushout f).Faithful := inferInstance
```
-/
instance faithful_pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
    [∀ Z (g : X ⟶ Z), Mono (pushout.inl g f)] : (pushout f).Faithful := by
  have (Z : Under X) : Mono ((mapPushoutAdj f).unit.app Z) := by simp; infer_instance
  exact (mapPushoutAdj f).faithful_L_of_mono_unit_app

/-- pushout (𝟙 X) : Under X ⥤ Under X is the identity functor. -/
/-
**CategoryTheory.Under.pushoutId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under
`。
形式化陈述：pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
pushout (𝟙 X) : Under X ⥤ Under X is the identity functor.
-/
def pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _))).symm
    (Under.mapId X).symm

/-- pushout commutes with composition (up to natural isomorphism). -/
/-
**CategoryTheory.Under.pushoutComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Und
er`。
形式化陈述：pushoutComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPushoutsAlong f] [HasP
ushoutsAlong g] : pushout (f ≫ g) ≅ pushout f ⋙ pushout g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
pushout commutes with composition (up to natural isomorphism).
-/
def pushoutComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPushoutsAlong f] [HasPushoutsAlong g] :
    pushout (f ≫ g) ≅ pushout f ⋙ pushout g :=
  (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _)).symm
    (mapComp f g).symm
/-
**CategoryTheory.Under.pushoutIsLeftAdjoint** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Under`。
形式化陈述：pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] : (pushout
 f).IsLeftAdjoint
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    (pushout f).IsLeftAdjoint :=
  ⟨_, ⟨mapPushoutAdj f⟩⟩

set_option backward.isDefEq.respectTransparency false in
open pushout in
/-- If `G` is a right adjoint and its source category has pushouts, then so is
`post G : Under Y ⥤ Under (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(G Y ⟶ X) ↦ (Y ⟶ Y ⨿_{F G Y} F X ⟶ F X)`. -/
@[simps!]
/-
**CategoryTheory.Under.postAdjunctionRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：postAdjunctionRight [HasPushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F
 ⊣ G) : post F ⋙ pushout (a.counit.app Y) ⊣ post G
参数：a : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a right adjoint and its source category has pushouts, then so is
`post G : Under Y ⥤ Under (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(G Y ⟶ X) ↦ (Y ⟶ Y ⨿_{F G Y} F X ⟶ F X)`.
-/
def postAdjunctionRight [HasPushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⋙ pushout (a.counit.app Y) ⊣ post G :=
  ((postAdjunctionLeft a).comp (mapPushoutAdj (a.counit.app Y))).ofNatIsoRight <|
    NatIso.ofComponents fun Y ↦ isoMk (.refl _)

open pushout in
/-
**CategoryTheory.Under.isRightAdjoint_post** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Under`。
形式化陈述：isRightAdjoint_post [HasPushouts D] {Y : D} {G : D ⥤ C} [G.IsRightAdjoint]
 : (post (X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance isRightAdjoint_post [HasPushouts D] {Y : D} {G : D ⥤ C} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

/-- The category under any object `X` factors through the category under the initial object `I`. -/
@[simps!]
/-
**CategoryTheory.Under.forgetMapInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Under`。
形式化陈述：forgetMapInitial {I : C} (hI : IsInitial I) : forget X ≅ map (hI.to X) ⋙ (
equivalenceOfIsInitial hI).functor
参数：hI : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category under any object `X` factors through the category under the initial
 object `I`.
-/
noncomputable def forgetMapInitial {I : C} (hI : IsInitial I) :
    forget X ≅ map (hI.to X) ⋙ (equivalenceOfIsInitial hI).functor :=
  NatIso.ofComponents fun X ↦ .refl _

section HasBinaryCoproducts
variable [HasBinaryCoproducts C]

/-- The functor from `C` to `Under X` which sends `Y : C` to `in₁ : X ⟶ X ⨿ Y`. -/
@[simps! obj_left obj_hom]
/-
**CategoryTheory.Under.costar** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：costar : C ⥤ Under X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `C` to `Under X` which sends `Y : C` to `in₁ : X ⟶ X ⨿ Y`.
-/
def costar : C ⥤ Under X := Monad.free _ ⋙ algebraToUnder X

/-- The functor `Under.forget X : Under X ⥤ C` has a left adjoint given by `costar X`.

Note that the binary coproducts assumption is necessary: the existence of a left adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`. -/
/-
**CategoryTheory.Under.costarAdjForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Under`。
形式化陈述：costarAdjForget : costar X ⊣ forget X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Under.forget X : Under X ⥤ C` has a left adjoint given by `costar X
`.

Note that the binary coproducts assumption is necessary: the existence of a left
 adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`
.
-/
def costarAdjForget : costar X ⊣ forget X := (Monad.adj _).comp (algebraEquivUnder X).toAdjunction
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (costar X).IsLeftAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

/-- Note that the binary coproducts assumption is necessary: the existence of a left adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`. -/
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the binary coproducts assumption is necessary: the existence of a left
 adjoint to
`Under.forget X` is equivalent to the existence of each binary coproduct `X ⨿ -`
.
-/
instance : (forget X).IsRightAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

end HasBinaryCoproducts
end Under

end CategoryTheory

