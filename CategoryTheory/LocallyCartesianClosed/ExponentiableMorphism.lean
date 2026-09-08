/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# Exponentiable morphisms

We define an exponentiable morphism `f : I ⟶ J` to be a morphism with a functorial choice of
pullbacks, given by `ChosenPullbacksAlong f`, together with a right adjoint to
the pullback functor `ChosenPullbacksAlong.pullback f : Over J ⥤ Over I`. We call this right adjoint
the pushforward functor along `f`.

## Main results

- The identity morphisms are exponentiable.
- The composition of exponentiable morphisms is exponentiable.

### TODO

- Any pullback of an exponentiable morphism is exponentiable.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category MonoidalCategory CategoryTheory.Functor Adjunction

open ChosenPullbacksAlong

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
/-
**CategoryTheory.ExponentiableMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {I J : C}
 → (f : I ⟶ J) → [CategoryTheory.ChosenPullbacksAlong f] → Type (max u v)
参数：f : I ⟶ J；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I
`
has a right adjoint.
-/
class ExponentiableMorphism {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  pullbackPushforwardAdj (f) : pullback f ⊣ pushforward

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
/-
**CategoryTheory.IsExponentiable** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsExponentiable [ChosenPullbacks C] : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I
`
has a right adjoint.
-/
abbrev IsExponentiable [ChosenPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ IsLeftAdjoint (pullback f)

namespace ExponentiableMorphism

/-
**CategoryTheory.ExponentiableMorphism.isExponentiable** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：isExponentiable [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMo
rphism f] : IsExponentiable f
参数：f : I ⟶ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isExponentiable [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f] :
  IsExponentiable f := ⟨pushforward f, ⟨pullbackPushforwardAdj f⟩⟩

section

variable {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] [ExponentiableMorphism f]

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
/-
**CategoryTheory.ExponentiableMorphism.ev** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ExponentiableMorphism`。
形式化陈述：ev : pushforward f ⋙ pullback f ⟶ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dependent evaluation natural transformation as the counit of the adjunction.
-/
def ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
  pullbackPushforwardAdj f |>.counit

/-- The dependent coevaluation natural transformation as the unit of the adjunction. -/
/-
**CategoryTheory.ExponentiableMorphism.coev** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ExponentiableMorphism`。
形式化陈述：coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dependent coevaluation natural transformation as the unit of the adjunction.
-/
def coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
  pullbackPushforwardAdj f |>.unit

@[simp]
/-
**CategoryTheory.ExponentiableMorphism.ev_def** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ExponentiableMorphism`。
形式化陈述：ev_def : ev f = (pullbackPushforwardAdj f).counit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ev_def : ev f = (pullbackPushforwardAdj f).counit :=
  rfl

@[simp]
/-
**CategoryTheory.ExponentiableMorphism.coev_def** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ExponentiableMorphism`。
形式化陈述：coev_def : coev f = (pullbackPushforwardAdj f).unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coev_def : coev f = (pullbackPushforwardAdj f).unit :=
  rfl

@[reassoc]
/-
**CategoryTheory.ExponentiableMorphism.ev_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ExponentiableMorphism`。
形式化陈述：ev_naturality {X Y : Over I} (g : X ⟶ Y) : (pullback f).map ((pushforward 
f).map g) ≫ (ev f).app Y = (ev f).app X ≫ g
参数：g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem ev_naturality {X Y : Over I} (g : X ⟶ Y) :
    (pullback f).map ((pushforward f).map g) ≫ (ev f).app Y = (ev f).app X ≫ g :=
  ev f |>.naturality g

@[reassoc]
/-
**CategoryTheory.ExponentiableMorphism.coev_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：coev_naturality {X Y : Over J} (g : X ⟶ Y) : g ≫ (coev f).app Y = (coev f)
.app X ≫ (pushforward f).map ((pullback f).map g)
参数：g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem coev_naturality {X Y : Over J} (g : X ⟶ Y) :
    g ≫ (coev f).app Y = (coev f).app X ≫ (pushforward f).map ((pullback f).map g) :=
  coev f |>.naturality g

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
/-
**CategoryTheory.ExponentiableMorphism.ev_coev** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ExponentiableMorphism`。
形式化陈述：ev_coev (X : Over J) : (pullback f).map (coev f |>.app X) ≫ (ev f |>.app (
pullback f |>.obj X)) = 𝟙 (pullback f |>.obj X)
参数：X : Over J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
The first triangle identity for the counit and unit of the adjunction.
-/
theorem ev_coev (X : Over J) :
    (pullback f).map (coev f |>.app X) ≫ (ev f |>.app (pullback f |>.obj X)) =
    𝟙 (pullback f |>.obj X) :=
  pullbackPushforwardAdj f |>.left_triangle_components X

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
/-
**CategoryTheory.ExponentiableMorphism.coev_ev** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ExponentiableMorphism`。
形式化陈述：coev_ev (Y : Over I) : (coev f |>.app (pushforward f |>.obj Y)) ≫ (pushfor
ward f |>.map (ev f |>.app Y)) = 𝟙 (pushforward f |>.obj Y)
参数：Y : Over I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
The second triangle identity for the counit and unit of the adjunction.
-/
theorem coev_ev (Y : Over I) :
    (coev f |>.app (pushforward f |>.obj Y)) ≫
    (pushforward f |>.map (ev f |>.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
  pullbackPushforwardAdj f |>.right_triangle_components Y

variable {f}

/-- The currying of `(pullback f).obj A ⟶ X` in `Over I` to a morphism `A ⟶ (pushforward f).obj X`
in `Over J`. -/
/-
**CategoryTheory.ExponentiableMorphism.pushforwardCurry** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardCurry {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) : 
A ⟶ (pushforward f).obj X
参数：u : (pullback f).obj A ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The currying of `(pullback f).obj A ⟶ X` in `Over I` to a morphism `A ⟶ (pushfor
ward f).obj X`
in `Over J`.
-/
def pushforwardCurry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
  pullbackPushforwardAdj f |>.homEquiv A X u

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
/-
**CategoryTheory.ExponentiableMorphism.pushforwardUncurry** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardUncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj 
X) : (pullback f).obj A ⟶ X
参数：v : A ⟶ (pushforward f).obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`.
-/
def pushforwardUncurry {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    (pullback f).obj A ⟶ X :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.invFun v
/-
**CategoryTheory.ExponentiableMorphism.homEquiv_apply_eq** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：homEquiv_apply_eq {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) :
 (pullbackPushforwardAdj f |>.homEquiv _ _) u = pushforwardCurry u
参数：u : (pullback f).obj A ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homEquiv_apply_eq {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _) u = pushforwardCurry u :=
  rfl
/-
**CategoryTheory.ExponentiableMorphism.homEquiv_symm_apply_eq** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：homEquiv_symm_apply_eq {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).
obj X) : (pullbackPushforwardAdj f |>.homEquiv _ _).symm v = pushforwardUncurry 
v
参数：v : A ⟶ (pushforward f).obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem homEquiv_symm_apply_eq {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _).symm v = pushforwardUncurry v :=
  rfl
/-
**CategoryTheory.ExponentiableMorphism.pushforward_uncurry_curry** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforward_uncurry_curry {X : Over I} {A : Over J} (u : (pullback f).obj 
A ⟶ X) : pushforwardUncurry (pushforwardCurry u) = u
参数：u : (pullback f).obj A ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem pushforward_uncurry_curry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.left_inv u
/-
**CategoryTheory.ExponentiableMorphism.pushforward_curry_uncurry** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward 
f).obj X) : pushforwardCurry (pushforwardUncurry v) = v
参数：v : A ⟶ (pushforward f).obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v :=
  pullbackPushforwardAdj f |>.homEquiv A X |>.right_inv v
/-
**CategoryTheory.ExponentiableMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.ExponentiableMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ChosenPullbacksAlong (Over.mk f).hom :=
  inferInstanceAs <| ChosenPullbacksAlong f
/-
**CategoryTheory.ExponentiableMorphism.OverMkHom** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.ExponentiableMorphism`。
形式化陈述：OverMkHom : ExponentiableMorphism (Over.mk f).hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OverMkHom : ExponentiableMorphism (Over.mk f).hom :=
  inferInstanceAs <| ExponentiableMorphism f

end

section

/-- The identity morphisms `𝟙 _` are exponentiable. -/
@[instance_reducible]
/-
**CategoryTheory.ExponentiableMorphism.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ExponentiableMorphism`。
形式化陈述：id (I : C) [ChosenPullbacksAlong (𝟙 I)] : ExponentiableMorphism (𝟙 I)
参数：I : C；𝟙 I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphisms `𝟙 _` are exponentiable.
-/
def id (I : C) [ChosenPullbacksAlong (𝟙 I)] : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩
/-
**CategoryTheory.ExponentiableMorphism.id_pushforward** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ExponentiableMorphism`。
形式化陈述：id_pushforward (I : C) [ChosenPullbacksAlong (𝟙 I)] : (id I).pushforward =
 𝟭 (Over I)
参数：I : C；𝟙 I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_pushforward (I : C) [ChosenPullbacksAlong (𝟙 I)] :
    (id I).pushforward = 𝟭 (Over I) := by
  dsimp +instances only [id]

/-- Any pushforward of the identity morphism is naturally isomorphic to the identity functor. -/
/-
**CategoryTheory.ExponentiableMorphism.pushforwardId** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardId (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism 
(𝟙 I)] : pushforward (𝟙 I) ≅ 𝟭 (Over I)
参数：I : C；𝟙 I；𝟙 I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any pushforward of the identity morphism is naturally isomorphic to the identity
 functor.
-/
def pushforwardId (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    pushforward (𝟙 I) ≅ 𝟭 (Over I) :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (𝟙 I)) (id I).pullbackPushforwardAdj

@[reassoc (attr := simp)]
/-
**CategoryTheory.ExponentiableMorphism.unit_pushforwardId_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：unit_pushforwardId_hom (I : C) [ChosenPullbacksAlong (𝟙 I)] [Exponentiable
Morphism (𝟙 I)] : (pullbackPushforwardAdj (𝟙 I)).unit ≫ (pullback (𝟙 I)).whisker
Left (pushforwardId I).hom = (id I).pullbackPushforwardAdj.unit
参数：I : C；𝟙 I；𝟙 I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ExponentiableMorphism.pushforwardId.eq_1`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (I : C)   [inst_1 : CategoryTheory.Cho
senPullbacksAlong (CategoryTheory.CategoryStr…
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom`：unit_rightAdjointUn
iq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : adj1.unit ≫ w
hiskerLeft F (rightAdjointUniq adj1 adj2)…
-/
theorem unit_pushforwardId_hom (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    (pullbackPushforwardAdj (𝟙 I)).unit ≫
      (pullback (𝟙 I)).whiskerLeft (pushforwardId I).hom =
      (id I).pullbackPushforwardAdj.unit := by
  rw [pushforwardId, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ExponentiableMorphism.pushforwardId_hom_counit** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardId_hom_counit (I : C) [ChosenPullbacksAlong (𝟙 I)] [Exponentiab
leMorphism (𝟙 I)] : Functor.whiskerRight (pushforwardId I).hom (pullback (𝟙 I)) 
≫ (id I).pullbackPushforwardAdj.counit = (pullbackPushforwardAdj (𝟙 I)).counit
参数：I : C；𝟙 I；𝟙 I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ExponentiableMorphism.pushforwardId.eq_1`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (I : C)   [inst_1 : CategoryTheory.Cho
senPullbacksAlong (CategoryTheory.CategoryStr…
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_counit`：rightAdjointUniq_
hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : whiskerRi
ght (rightAdjointUniq adj1 adj2).hom F ≫ ad…
-/
theorem pushforwardId_hom_counit (I : C) [ChosenPullbacksAlong (𝟙 I)]
    [ExponentiableMorphism (𝟙 I)] :
    Functor.whiskerRight (pushforwardId I).hom (pullback (𝟙 I)) ≫
      (id I).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (𝟙 I)).counit := by
  rw [pushforwardId, Adjunction.rightAdjointUniq_hom_counit]

/-- The composition of exponentiable morphisms is exponentiable. -/
@[instance_reducible]
/-
**CategoryTheory.ExponentiableMorphism.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ExponentiableMorphism`。
形式化陈述：comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K) [ChosenPullbacksAlong f] [ChosenP
ullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] [ExponentiableMorphism f] [Expon
entiableMorphism g] : ExponentiableMorphism (f ≫ g)
参数：f : I ⟶ J；g : J ⟶ K；f ≫ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of exponentiable morphisms is exponentiable.
-/
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackPushforwardAdj g |>.comp <| pullbackPushforwardAdj f)
    (pullbackComp f g).symm⟩
/-
**CategoryTheory.ExponentiableMorphism.comp_pushforward** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：comp_pushforward {I J K : C} (f : I ⟶ J) (g : J ⟶ K) [ChosenPullbacksAlong
 f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] [ExponentiableMorphi
sm f] [ExponentiableMorphism g] : (comp f g).pushforward = pushforward f ⋙ pushf
orward g
参数：f : I ⟶ J；g : J ⟶ K；f ≫ g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_pushforward {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    (comp f g).pushforward = pushforward f ⋙ pushforward g := by
  dsimp +instances only [comp]

/-- The natural isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
/-
**CategoryTheory.ExponentiableMorphism.pushforwardComp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardComp {I J K : C} (f : I ⟶ J) (g : J ⟶ K) [ChosenPullbacksAlong 
f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] [ExponentiableMorphis
m f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] : pushforward (C
参数：f : I ⟶ J；g : J ⟶ K；f ≫ g；f ≫ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between pushforward of the composition and the compositi
on of
pushforward functors.
-/
def pushforwardComp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    pushforward (C := C) (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (f ≫ g)) ((comp f g).pullbackPushforwardAdj)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ExponentiableMorphism.unit_pushforwardComp_hom** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：unit_pushforwardComp_hom {I J K : C} (f : I ⟶ J) (g : J ⟶ K) [ChosenPullba
cksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] [Exponentiab
leMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] : (pullb
ackPushforwardAdj (f ≫ g)).unit ≫ (pullback (f ≫ g)).whiskerLeft (pushforwardCom
p f g).hom = (comp f g).pullbackPushforwardAdj.unit
参数：f : I ⟶ J；g : J ⟶ K；f ≫ g；f ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ExponentiableMorphism.pushforwardComp.eq_1`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {I J K : C} (f : I ⟶ J) (g : J ⟶ K) 
  [inst_1 : CategoryTheory.ChosenPullbacksAlong…
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom`：unit_rightAdjointUn
iq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : adj1.unit ≫ w
hiskerLeft F (rightAdjointUniq adj1 adj2)…
-/
theorem unit_pushforwardComp_hom {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    (pullbackPushforwardAdj (f ≫ g)).unit ≫
      (pullback (f ≫ g)).whiskerLeft (pushforwardComp f g).hom =
      (comp f g).pullbackPushforwardAdj.unit := by
  rw [pushforwardComp, Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ExponentiableMorphism.pushforwardComp_hom_counit** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ExponentiableMorphism`。
形式化陈述：pushforwardComp_hom_counit {I J K : C} (f : I ⟶ J) (g : J ⟶ K) [ChosenPull
backsAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] [Exponenti
ableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] : Func
tor.whiskerRight (pushforwardComp f g).hom (pullback (f ≫ g)) ≫ (comp f g).pullb
ackPushforwardAdj.counit = (pullbackPushforwardAdj (f ≫ g)).counit
参数：f : I ⟶ J；g : J ⟶ K；f ≫ g；f ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ExponentiableMorphism.pushforwardComp.eq_1`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {I J K : C} (f : I ⟶ J) (g : J ⟶ K) 
  [inst_1 : CategoryTheory.ChosenPullbacksAlong…
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_counit`：rightAdjointUniq_
hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : whiskerRi
ght (rightAdjointUniq adj1 adj2).hom F ≫ ad…
-/
theorem pushforwardComp_hom_counit {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    Functor.whiskerRight (pushforwardComp f g).hom (pullback (f ≫ g)) ≫
      (comp f g).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (f ≫ g)).counit := by
  rw [pushforwardComp, Adjunction.rightAdjointUniq_hom_counit]

end

end ExponentiableMorphism

end CategoryTheory

