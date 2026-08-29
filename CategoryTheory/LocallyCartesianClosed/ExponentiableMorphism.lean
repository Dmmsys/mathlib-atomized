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

/--
Definition of `ExponentiableMorphism` / `ExponentiableMorphism` 的定义

English:
class ExponentiableMorphism
  parameters: {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f]
  axioms and operations (2):
    - pushforward : Over I ⥤ Over J
    - pullbackPushforwardAdj((f)) : pullback f ⊣ pushforward

中文:
类 ExponentiableMorphism
  参数: {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f]
  公理与运算 (2 个):
    - pushforward : Over I ⥤ Over J
    - pullbackPushforwardAdj((f)) : pullback f ⊣ pushforward
-/
class ExponentiableMorphism {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  pullbackPushforwardAdj (f) : pullback f ⊣ pushforward

/--
Definition of `IsExponentiable` / `IsExponentiable` 的定义

English:
abbreviation IsExponentiable
  signature: [ChosenPullbacks C]
  body: fun _ _ f => IsLeftAdjoint (pullback f)

中文:
缩写 IsExponentiable
  签名: [ChosenPullbacks C]
  定义体: fun _ _ f => IsLeftAdjoint (pullback f)

Depends on / 依赖: IsLeftAdjoint, pullback
-/
abbrev IsExponentiable [ChosenPullbacks C] : MorphismProperty C :=
  fun _ _ f => IsLeftAdjoint (pullback f)

namespace ExponentiableMorphism

/--
Instance `isExponentiable` / 实例 `isExponentiable`

English:
instance isExponentiable
  signature: [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f]
  body: ⟨pushforward f, ⟨pullbackPushforwardAdj f⟩⟩

中文:
实例 isExponentiable
  签名: [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f]
  定义体: ⟨pushforward f, ⟨pullbackPushforwardAdj f⟩⟩

Depends on / 依赖: pullbackPushforwardAdj, pushforward
-/
instance isExponentiable [ChosenPullbacks C] {I J : C} (f : I ⟶ J) [ExponentiableMorphism f] :
  IsExponentiable f := ⟨pushforward f, ⟨pullbackPushforwardAdj f⟩⟩

section

variable {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] [ExponentiableMorphism f]

/--
Definition of `ev` / `ev` 的定义

English:
definition ev
  signature: : pushforward f ⋙ pullback f ⟶ 𝟭 _
  body: .counit pullbackPushforwardAdj f

中文:
定义 ev
  签名: : pushforward f ⋙ pullback f ⟶ 𝟭 _
  定义体: .counit pullbackPushforwardAdj f

Depends on / 依赖: counit, pullbackPushforwardAdj
-/
def ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
.counit pullbackPushforwardAdj f

/--
Definition of `coev` / `coev` 的定义

English:
definition coev
  signature: : 𝟭 _ ⟶ pullback f ⋙ pushforward f
  body: .unit pullbackPushforwardAdj f

@[simp]

中文:
定义 coev
  签名: : 𝟭 _ ⟶ pullback f ⋙ pushforward f
  定义体: .unit pullbackPushforwardAdj f

@[simp]

Depends on / 依赖: pullbackPushforwardAdj
-/
def coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
.unit pullbackPushforwardAdj f

@[simp]
/--
theorem `ev_def` / 定理 `ev_def`

English:
theorem ev_def
  statement: ev f = (pullbackPushforwardAdj f).counit
  proof: rfl

@[simp]

中文:
定理 ev_def
  结论: ev f = (pullbackPushforwardAdj f).counit
  证明: rfl

@[simp]
-/
theorem ev_def : ev f = (pullbackPushforwardAdj f).counit :=
  rfl

@[simp]
/--
theorem `coev_def` / 定理 `coev_def`

English:
theorem coev_def
  statement: coev f = (pullbackPushforwardAdj f).unit
  proof: rfl

@[reassoc]

中文:
定理 coev_def
  结论: coev f = (pullbackPushforwardAdj f).unit
  证明: rfl

@[reassoc]
-/
theorem coev_def : coev f = (pullbackPushforwardAdj f).unit :=
  rfl

@[reassoc]
/--
theorem `ev_naturality` / 定理 `ev_naturality`

English:
theorem ev_naturality
  given: {X Y : Over I} (g : X ⟶ Y)
  proof: .naturality g ev f

@[reassoc]

中文:
定理 ev_naturality
  条件: {X Y : Over I} (g : X ⟶ Y)
  证明: .naturality g ev f

@[reassoc]

Depends on / 依赖: naturality
-/
theorem ev_naturality {X Y : Over I} (g : X ⟶ Y) :
    (pullback f).map ((pushforward f).map g) ≫ (ev f).app Y = (ev f).app X ≫ g :=
.naturality g ev f

@[reassoc]
/--
theorem `coev_naturality` / 定理 `coev_naturality`

English:
theorem coev_naturality
  given: {X Y : Over J} (g : X ⟶ Y)
  proof: .naturality g coev f

中文:
定理 coev_naturality
  条件: {X Y : Over J} (g : X ⟶ Y)
  证明: .naturality g coev f

Depends on / 依赖: naturality
-/
theorem coev_naturality {X Y : Over J} (g : X ⟶ Y) :
    g ≫ (coev f).app Y = (coev f).app X ≫ (pushforward f).map ((pullback f).map g) :=
.naturality g coev f

/-- The first triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
/--
theorem `ev_coev` / 定理 `ev_coev`

English:
theorem ev_coev
  given: (X : Over J)
  proof: .left_triangle_components X pullbackPushforwardAdj f

中文:
定理 ev_coev
  条件: (X : Over J)
  证明: .left_triangle_components X pullbackPushforwardAdj f

Depends on / 依赖: left_triangle_components, pullbackPushforwardAdj
-/
theorem ev_coev (X : Over J) :
    (pullback f).map (coev f |>.app X) ≫ (ev f |>.app (pullback f |>.obj X)) =
    𝟙 (pullback f |>.obj X) :=
.left_triangle_components X pullbackPushforwardAdj f

/-- The second triangle identity for the counit and unit of the adjunction. -/
@[reassoc]
/--
theorem `coev_ev` / 定理 `coev_ev`

English:
theorem coev_ev
  given: (Y : Over I)
  proof: .right_triangle_components Y pullbackPushforwardAdj f

中文:
定理 coev_ev
  条件: (Y : Over I)
  证明: .right_triangle_components Y pullbackPushforwardAdj f

Depends on / 依赖: pullbackPushforwardAdj, right_triangle_components
-/
theorem coev_ev (Y : Over I) :
    (coev f |>.app (pushforward f |>.obj Y)) ≫
    (pushforward f |>.map (ev f |>.app Y)) =
    𝟙 (pushforward f |>.obj Y) :=
.right_triangle_components Y pullbackPushforwardAdj f

variable {f}

/--
Definition of `pushforwardCurry` / `pushforwardCurry` 的定义

English:
definition pushforwardCurry
  signature: {X : Over I} {A : Over J}
  body: .homEquiv A X u pullbackPushforwardAdj f

中文:
定义 pushforwardCurry
  签名: {X : Over I} {A : Over J}
  定义体: .homEquiv A X u pullbackPushforwardAdj f

Depends on / 依赖: homEquiv, pullbackPushforwardAdj
-/
def pushforwardCurry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    A ⟶ (pushforward f).obj X :=
.homEquiv A X u pullbackPushforwardAdj f

/--
Definition of `pushforwardUncurry` / `pushforwardUncurry` 的定义

English:
definition pushforwardUncurry
  signature: {X : Over I} {A : Over J}
  body: .invFun v .homEquiv A X pullbackPushforwardAdj f

中文:
定义 pushforwardUncurry
  签名: {X : Over I} {A : Over J}
  定义体: .invFun v .homEquiv A X pullbackPushforwardAdj f

Depends on / 依赖: homEquiv, invFun, pullbackPushforwardAdj
-/
def pushforwardUncurry {X : Over I} {A : Over J}
    (v : A ⟶ (pushforward f).obj X) :
    (pullback f).obj A ⟶ X :=
.invFun v .homEquiv A X pullbackPushforwardAdj f

/--
theorem `homEquiv_apply_eq` / 定理 `homEquiv_apply_eq`

English:
theorem homEquiv_apply_eq
  given: {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X)
  proof: rfl

中文:
定理 homEquiv_apply_eq
  条件: {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X)
  证明: rfl
-/
theorem homEquiv_apply_eq {X : Over I} {A : Over J} (u : (pullback f).obj A ⟶ X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _) u = pushforwardCurry u :=
  rfl

/--
theorem `homEquiv_symm_apply_eq` / 定理 `homEquiv_symm_apply_eq`

English:
theorem homEquiv_symm_apply_eq
  given: {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X)
  proof: rfl

中文:
定理 homEquiv_symm_apply_eq
  条件: {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X)
  证明: rfl
-/
theorem homEquiv_symm_apply_eq {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    (pullbackPushforwardAdj f |>.homEquiv _ _).symm v = pushforwardUncurry v :=
  rfl

/--
theorem `pushforward_uncurry_curry` / 定理 `pushforward_uncurry_curry`

English:
theorem pushforward_uncurry_curry
  statement: {X : Over I} {A : Over J}
  proof: .left_inv u .homEquiv A X pullbackPushforwardAdj f

中文:
定理 pushforward_uncurry_curry
  结论: {X : Over I} {A : Over J}
  证明: .left_inv u .homEquiv A X pullbackPushforwardAdj f

Depends on / 依赖: homEquiv, left_inv, pullbackPushforwardAdj
-/
theorem pushforward_uncurry_curry {X : Over I} {A : Over J}
    (u : (pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u :=
.left_inv u .homEquiv A X pullbackPushforwardAdj f

/--
theorem `pushforward_curry_uncurry` / 定理 `pushforward_curry_uncurry`

English:
theorem pushforward_curry_uncurry
  given: {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X)
  proof: .right_inv v .homEquiv A X pullbackPushforwardAdj f

中文:
定理 pushforward_curry_uncurry
  条件: {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X)
  证明: .right_inv v .homEquiv A X pullbackPushforwardAdj f

Depends on / 依赖: homEquiv, pullbackPushforwardAdj, right_inv
-/
theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforward f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v :=
.right_inv v .homEquiv A X pullbackPushforwardAdj f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChosenPullbacksAlong (Over.mk f).hom
  body: inferInstanceAs ChosenPullbacksAlong f

中文:
实例 :
  签名: ChosenPullbacksAlong (Over.mk f).hom
  定义体: inferInstanceAs ChosenPullbacksAlong f

Depends on / 依赖: ChosenPullbacksAlong
-/
instance : ChosenPullbacksAlong (Over.mk f).hom :=
inferInstanceAs ChosenPullbacksAlong f

/--
Instance `OverMkHom` / 实例 `OverMkHom`

English:
instance OverMkHom
  signature: : ExponentiableMorphism (Over.mk f).hom
  body: inferInstanceAs ExponentiableMorphism f

中文:
实例 OverMkHom
  签名: : ExponentiableMorphism (Over.mk f).hom
  定义体: inferInstanceAs ExponentiableMorphism f

Depends on / 依赖: ExponentiableMorphism
-/
instance OverMkHom : ExponentiableMorphism (Over.mk f).hom :=
inferInstanceAs ExponentiableMorphism f

end

section

/-- The identity morphisms `𝟙 _` are exponentiable. -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  body: ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩

中文:
定义 id
  签名: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  定义体: ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩

Depends on / 依赖: Adjunction, Adjunction.id, ofNatIsoLeft, pullbackId
-/
def id (I : C) [ChosenPullbacksAlong (𝟙 I)] : ExponentiableMorphism (𝟙 I) :=
  ⟨𝟭 _, ofNatIsoLeft (F := 𝟭 _) Adjunction.id (pullbackId I).symm⟩

/--
theorem `id_pushforward` / 定理 `id_pushforward`

English:
theorem id_pushforward
  given: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  proof: by
  dsimp +instances only [id]

中文:
定理 id_pushforward
  条件: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  证明: by
  dsimp +instances only [id]

Depends on / 依赖: instances
-/
theorem id_pushforward (I : C) [ChosenPullbacksAlong (𝟙 I)] :
    (id I).pushforward = 𝟭 (Over I) := by
  dsimp +instances only [id]

/--
Definition of `pushforwardId` / `pushforwardId` 的定义

English:
definition pushforwardId
  signature: (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)]
  body: Adjunction.rightAdjointUniq (pullbackPushforwardAdj (𝟙 I)) (id I).pullbackPushforwardAdj

@[reassoc (attr := simp)]

中文:
定义 pushforwardId
  签名: (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)]
  定义体: Adjunction.rightAdjointUniq (pullbackPushforwardAdj (𝟙 I)) (id I).pullbackPushforwardAdj

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq, pullbackPushforwardAdj, rightAdjointUniq
-/
def pushforwardId (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    pushforward (𝟙 I) ≅ 𝟭 (Over I) :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (𝟙 I)) (id I).pullbackPushforwardAdj

@[reassoc (attr := simp)]
/--
theorem `unit_pushforwardId_hom` / 定理 `unit_pushforwardId_hom`

English:
theorem unit_pushforwardId_hom
  given: (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)]
  proof: by
  rw [pushforwardId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

中文:
定理 unit_pushforwardId_hom
  条件: (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)]
  证明: by
  rw [pushforwardId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.unit_rightAdjointUniq_hom, pushforwardId, unit_rightAdjointUniq_hom
-/
theorem unit_pushforwardId_hom (I : C) [ChosenPullbacksAlong (𝟙 I)] [ExponentiableMorphism (𝟙 I)] :
    (pullbackPushforwardAdj (𝟙 I)).unit ≫
      (pullback (𝟙 I)).whiskerLeft (pushforwardId I).hom =
      (id I).pullbackPushforwardAdj.unit := by
  rw [pushforwardId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/--
theorem `pushforwardId_hom_counit` / 定理 `pushforwardId_hom_counit`

English:
theorem pushforwardId_hom_counit
  statement: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  proof: by
  rw [pushforwardId]; rw [Adjunction.rightAdjointUniq_hom_counit]

中文:
定理 pushforwardId_hom_counit
  结论: (I : C) [ChosenPullbacksAlong (𝟙 I)]
  证明: by
  rw [pushforwardId]; rw [Adjunction.rightAdjointUniq_hom_counit]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq_hom_counit, pushforwardId, rightAdjointUniq_hom_counit
-/
theorem pushforwardId_hom_counit (I : C) [ChosenPullbacksAlong (𝟙 I)]
    [ExponentiableMorphism (𝟙 I)] :
    Functor.whiskerRight (pushforwardId I).hom (pullback (𝟙 I)) ≫
      (id I).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (𝟙 I)).counit := by
  rw [pushforwardId]; rw [Adjunction.rightAdjointUniq_hom_counit]

/-- The composition of exponentiable morphisms is exponentiable. -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  body: ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackPushforwardAdj g |>.comp <| pullbackPushforwardAdj f)
    (pullbackComp f g).symm⟩

中文:
定义 comp
  签名: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  定义体: ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackPushforwardAdj g |>.comp <| pullbackPushforwardAdj f)
    (pullbackComp f g).symm⟩

Depends on / 依赖: ofNatIsoLeft, pullbackComp, pullbackPushforwardAdj, pushforward
-/
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    ExponentiableMorphism (f ≫ g) :=
  ⟨pushforward f ⋙ pushforward g,
    ofNatIsoLeft (pullbackPushforwardAdj g |>.comp <| pullbackPushforwardAdj f)
    (pullbackComp f g).symm⟩

/--
theorem `comp_pushforward` / 定理 `comp_pushforward`

English:
theorem comp_pushforward
  statement: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  proof: by
  dsimp +instances only [comp]

中文:
定理 comp_pushforward
  结论: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  证明: by
  dsimp +instances only [comp]

Depends on / 依赖: instances
-/
theorem comp_pushforward {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    (comp f g).pushforward = pushforward f ⋙ pushforward g := by
  dsimp +instances only [comp]

/--
Definition of `pushforwardComp` / `pushforwardComp` 的定义

English:
definition pushforwardComp
  signature: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  body: Adjunction.rightAdjointUniq (pullbackPushforwardAdj (f ≫ g)) ((comp f g).pullbackPushforwardAdj)

@[reassoc (attr := simp)]

中文:
定义 pushforwardComp
  签名: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  定义体: Adjunction.rightAdjointUniq (pullbackPushforwardAdj (f ≫ g)) ((comp f g).pullbackPushforwardAdj)

@[reassoc (attr := simp)]

Depends on / 依赖: pushforward
-/
def pushforwardComp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    pushforward (C := C) (f ≫ g) ≅ pushforward f ⋙ pushforward g :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdj (f ≫ g)) ((comp f g).pullbackPushforwardAdj)

@[reassoc (attr := simp)]
/--
theorem `unit_pushforwardComp_hom` / 定理 `unit_pushforwardComp_hom`

English:
theorem unit_pushforwardComp_hom
  statement: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  proof: by
  rw [pushforwardComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

中文:
定理 unit_pushforwardComp_hom
  结论: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  证明: by
  rw [pushforwardComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.unit_rightAdjointUniq_hom, pushforwardComp, unit_rightAdjointUniq_hom
-/
theorem unit_pushforwardComp_hom {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    (pullbackPushforwardAdj (f ≫ g)).unit ≫
      (pullback (f ≫ g)).whiskerLeft (pushforwardComp f g).hom =
      (comp f g).pullbackPushforwardAdj.unit := by
  rw [pushforwardComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/--
theorem `pushforwardComp_hom_counit` / 定理 `pushforwardComp_hom_counit`

English:
theorem pushforwardComp_hom_counit
  statement: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  proof: by
  rw [pushforwardComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

中文:
定理 pushforwardComp_hom_counit
  结论: {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  证明: by
  rw [pushforwardComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq_hom_counit, pushforwardComp, rightAdjointUniq_hom_counit
-/
theorem pushforwardComp_hom_counit {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)]
    [ExponentiableMorphism f] [ExponentiableMorphism g] [ExponentiableMorphism (f ≫ g)] :
    Functor.whiskerRight (pushforwardComp f g).hom (pullback (f ≫ g)) ≫
      (comp f g).pullbackPushforwardAdj.counit =
      (pullbackPushforwardAdj (f ≫ g)).counit := by
  rw [pushforwardComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

end

end ExponentiableMorphism

end CategoryTheory
