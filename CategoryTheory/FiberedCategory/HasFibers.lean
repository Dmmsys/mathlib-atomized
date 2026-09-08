/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!

# Fibers of functors

In this file we introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S`
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

We also provide a canonical `HasFibers` instance, which uses the standard fibers `Fiber p S`
(see `Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`). This makes it so that any result proven
about `HasFibers` can be used for the standard fibers as well.

The reason for introducing this typeclass is that in practice, when working with (pre)fibered
categories one often already has a collection of categories `Fib S` for every `S` that are
equivalent to the fibers `Fiber p S`. One would then like to use these categories `Fib S` directly,
instead of working through this equivalence of categories. By developing an API for the `HasFibers`
typeclass, this will be possible.

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types
`F : 𝒮ᵒᵖ ⥤ Type _`. The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a`
is an element of `F(S)`. The fiber category `Fiber p S` is then equivalent to the discrete category
`Fib S` with objects `a` in `F(S)`. In this case, the `HasFibers` instance is given by the
categories `F(S)` and the functor `ι` sends `a : F(S)` to `(S, a)` in the fibered category.

## Main API
The following API is developed so that the fibers from a `HasFibers` instance can be used
analogously to the standard fibers.

- `Fib.homMk φ` is a lift of a morphism `φ : (ι S).obj a ⟶ (ι S).obj b` in `𝒳`, which lies over
  `𝟙 S`, to a morphism in the fiber over `S`.
- `Fib.mk` gives an object in the fiber over `S` which is isomorphic to a given `a : 𝒳` that
  satisfies `p(a) = S`. The isomorphism is given by `Fib.mkIsoSelf`.
- `HasFibers.mkPullback` is a version of `IsPreFibered.mkPullback` which ensures that the object
  lies in a given fiber. The corresponding Cartesian morphism is given by `HasFibers.pullbackMap`.
- `HasFibers.inducedMap` is a version of `IsCartesian.inducedMap` which gives the corresponding
  morphism in the fiber category.
- `fiber_factorization` is the statement that any morphism in `𝒳` can be factored as a morphism in
  some fiber followed by a pullback.

-/

@[expose] public section

universe v₃ u₃ v₂ u₂ v₁ u₁

open CategoryTheory Functor Category IsCartesian IsHomLift Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

set_option linter.checkUnivs false in
/-- HasFibers is an extrinsic notion of fibers on a functor `p : 𝒳 ⥤ 𝒮`. It is given by a
collection of categories `Fib S` for every `S : 𝒮` (the fiber categories), each equipped with a
functors `ι : Fib S ⥤ 𝒳` which map constantly to `S` on the base such that the induced functor
`Fib S ⥤ Fiber p S` is an equivalence. -/
/-
**HasFibers** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：HasFibers (p : 𝒳 ⥤ 𝒮) where /-- The type of objects of the category `Fib S
` for each `S`. -/ Fib (S : 𝒮) : Type u₃ /-- `Fib S` is a category. -/ category 
(S : 𝒮) : Category.{v₃} (Fib S)
参数：p : 𝒳 ⥤ 𝒮；S : 𝒮。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
HasFibers is an extrinsic notion of fibers on a functor `p : 𝒳 ⥤ 𝒮`. It is given
 by a
collection of categories `Fib S` for every `S : 𝒮` (the fiber categories), each 
equipped with a
functors `ι : Fib S ⥤ 𝒳` which map constantly to `S` on the base such that the i
nduced functor
`Fib S ⥤ Fiber p S` is an equivalence.
-/
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  /-- The type of objects of the category `Fib S` for each `S`. -/
  Fib (S : 𝒮) : Type u₃
  /-- `Fib S` is a category. -/
  category (S : 𝒮) : Category.{v₃} (Fib S) := by infer_instance
  /-- The functor `ι : Fib S ⥤ 𝒳`. -/
  ι (S : 𝒮) : Fib S ⥤ 𝒳
  /-- The composition with the functor `p` is *equal* to the constant functor mapping to `S`. -/
  comp_const (S : 𝒮) : ι S ⋙ p = (const (Fib S)).obj S
  /-- The induced functor from `Fib S` to the fiber of `𝒳 ⥤ 𝒮` over `S` is an equivalence. -/
  equiv (S : 𝒮) : Functor.IsEquivalence (inducedFunctor (comp_const S)) := by infer_instance

namespace HasFibers

/-- The `HasFibers` on `p : 𝒳 ⥤ 𝒮` given by the fibers of `p` -/
@[instance_reducible]
/-
**HasFibers.canonical** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where Fib
参数：p : 𝒳 ⥤ 𝒮。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.Fiber.fiberInclusion_comp_eq_const`：fiberInclusio
n_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).obj S

--- 原说明 ---
The `HasFibers` on `p : 𝒳 ⥤ 𝒮` given by the fibers of `p`
-/
def canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι S := fiberInclusion
  comp_const S := fiberInclusion_comp_eq_const
  equiv S := by exact isEquivalence_of_iso (F := 𝟭 (Fiber p S)) (Iso.refl _)

section

variable (p : 𝒳 ⥤ 𝒮) [HasFibers p] (S : 𝒮)

attribute [instance_reducible, instance] category

/-- The induced functor from `Fib p S` to the standard fiber. -/
@[simps!]
/-
**HasFibers.inducedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：inducedFunctor : Fib p S ⥤ Fiber p S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasFibers.comp_const`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} {inst : CategoryTheo
ry.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳}   {p : Cat
egoryTheor…

--- 原说明 ---
The induced functor from `Fib p S` to the standard fiber.
-/
def inducedFunctor : Fib p S ⥤ Fiber p S :=
  Fiber.inducedFunctor (comp_const S)

/-- The natural transformation `ι S ≅ (inducedFunctor p S) ⋙ (fiberInclusion p S)` -/
/-
**HasFibers.inducedFunctor.natIso** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers.inducedFu
nctor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         (p : Cat
egoryTheory.Functor 𝒳 𝒮) →           [inst_2 : HasFibers p] →             (S : 𝒮
) → HasFibers.ι S ≅ (HasFibers.inducedFunctor p S).comp CategoryTheory.Functor.F
iber.fiberInclusion
参数：p : CategoryTheory.Functor 𝒳 𝒮；S : 𝒮；HasFibers.inducedFunctor p S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasFibers.comp_const`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} {inst : CategoryTheo
ry.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳}   {p : Cat
egoryTheor…

--- 原说明 ---
The natural transformation `ι S ≅ (inducedFunctor p S) ⋙ (fiberInclusion p S)`
-/
def inducedFunctor.natIso : ι S ≅ (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctorCompIsoSelf (comp_const S)
/-
**HasFibers.inducedFunctor_comp** 是 Mathlib 中的一个引理，位于命名空间 `HasFibers`。
形式化陈述：inducedFunctor_comp : ι S = (inducedFunctor p S) ⋙ fiberInclusion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.Fiber.inducedFunctor_comp`：inducedFunctor_comp : 
(inducedFunctor hF) ⋙ fiberInclusion = F
· 使用定理 `HasFibers.comp_const`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} {inst : CategoryTheo
ry.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳}   {p : Cat
egoryTheor…
-/
lemma inducedFunctor_comp : ι S = (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctor_comp (comp_const S)
/-
**HasFibers.** 是 Mathlib 中的一个实例，位于命名空间 `HasFibers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.IsEquivalence (inducedFunctor p S) := equiv S
/-
**HasFibers.** 是 Mathlib 中的一个实例，位于命名空间 `HasFibers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Faithful (ι (p := p) S) :=
  Functor.Faithful.of_iso (inducedFunctor.natIso p S).symm

end

section

variable {p : 𝒳 ⥤ 𝒮} [HasFibers p]

@[simp]
/-
**HasFibers.proj_eq** 是 Mathlib 中的一个引理，位于命名空间 `HasFibers`。
形式化陈述：proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) = S
参数：a : Fib p S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFibers.comp_const`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} {inst : CategoryTheo
ry.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳}   {p : Cat
egoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) = S := by
  simp only [← comp_obj, comp_const, const_obj_obj]

/-- The morphism `R ⟶ S` in `𝒮` obtained by projecting a morphism
`φ : (ι R).obj a ⟶ (ι S).obj b`. -/
/-
**HasFibers.projMap** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：projMap {R S : 𝒮} {a : Fib p R} {b : Fib p S} (φ : (ι R).obj a ⟶ (ι S).obj
 b) : R ⟶ S
参数：φ : (ι R).obj a ⟶ (ι S).obj b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HasFibers.proj_eq`：proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) =
 S

--- 原说明 ---
The morphism `R ⟶ S` in `𝒮` obtained by projecting a morphism
`φ : (ι R).obj a ⟶ (ι S).obj b`.
-/
def projMap {R S : 𝒮} {a : Fib p R} {b : Fib p S}
    (φ : (ι R).obj a ⟶ (ι S).obj b) : R ⟶ S :=
  eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For any homomorphism `φ` in a fiber `Fib S`, its image under `ι S` lies over `𝟙 S`. -/
/-
**HasFibers.homLift** 是 Mathlib 中的一个实例，位于命名空间 `HasFibers`。
形式化陈述：homLift {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((ι S).map
 φ)
参数：φ : a ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_fac`：of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) 
(φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : f = eqToHom ha.symm ≫ p.m
ap φ ≫ eqToHom hb) : …
· 使用引理 `HasFibers.proj_eq`：proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) =
 S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `HasFibers.comp_const`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} {inst : CategoryTheo
ry.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳}   {p : Cat
egoryTheor…
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)

--- 原说明 ---
For any homomorphism `φ` in a fiber `Fib S`, its image under `ι S` lies over `𝟙 
S`.
-/
instance homLift {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((ι S).map φ) := by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map, Functor.congr_hom (comp_const S)]
  simp

/-- A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside the category
`𝒳`. -/
/-
**HasFibers.Fib.homMk** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers.Fib`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         {p : Cat
egoryTheory.Functor 𝒳 𝒮} →           [inst_2 : HasFibers p] →             {S : 𝒮
} →               {a b : HasFibers.Fib p S} →                 (φ : (HasFibers.ι 
S).obj a ⟶ (HasFibers.ι S).obj b) →                   [p.IsHomLift (CategoryTheo
ry.CategoryStruct.id S) φ] → a ⟶ b
参数：φ : (HasFibers.ι S).obj a ⟶ (HasFibers.ι S).obj b；CategoryTheory.CategoryStru
ct.id S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside
 the category
`𝒳`.
-/
noncomputable def Fib.homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : a ⟶ b :=
  (inducedFunctor _ S).preimage (Fiber.homMk p S φ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HasFibers.Fib.map_homMk** 是 Mathlib 中的一个定理，位于命名空间 `HasFibers.Fib`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheory.Functor 𝒳 𝒮}
 [inst_2 : HasFibers p] {S : 𝒮} {a b : HasFibers.Fib p S}   (φ : (HasFibers.ι S)
.obj a ⟶ (HasFibers.ι S).obj b) [inst_3 : p.IsHomLift (CategoryTheory.CategorySt
ruct.id S) φ],   (HasFibers.ι S).map (HasFibers.Fib.homMk φ) = φ
参数：φ : (HasFibers.ι S).obj a ⟶ (HasFibers.ι S).obj b；CategoryTheory.CategoryStru
ct.id S；HasFibers.ι S；HasFibers.Fib.homMk φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用引理 `HasFibers.inducedFunctor_comp`：inducedFunctor_comp : ι S = (inducedFunct
or p S) ⋙ fiberInclusion
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Fib.map_homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : (ι S).map (homMk φ) = φ := by
  simp [Fib.homMk, congr_hom (inducedFunctor_comp p S)]

@[ext]
/-
**HasFibers.Fib.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `HasFibers.Fib`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheory.Functor 𝒳 𝒮}
 [inst_2 : HasFibers p] {S : 𝒮} {a b : HasFibers.Fib p S} {f g : a ⟶ b},   (HasF
ibers.ι S).map f = (HasFibers.ι S).map g → f = g
参数：HasFibers.ι S；HasFibers.ι S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HasFibers.instFaithfulFibι`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : Catego
ryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p
 : CategoryTheor…
-/
lemma Fib.hom_ext {S : 𝒮} {a b : Fib p S} {f g : a ⟶ b}
    (h : (ι S).map f = (ι S).map g) : f = g :=
  (ι S).map_injective h

/-- The lift of an isomorphism `Φ : (ι S).obj a ≅ (ι S).obj b` lying over `𝟙 S` to an isomorphism
in `Fib S`. -/
@[simps]
/-
**HasFibers.Fib.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers.Fib`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         {p : Cat
egoryTheory.Functor 𝒳 𝒮} →           [inst_2 : HasFibers p] →             {S : 𝒮
} →               {a b : HasFibers.Fib p S} →                 (Φ : (HasFibers.ι 
S).obj a ≅ (HasFibers.ι S).obj b) →                   p.IsHomLift (CategoryTheor
y.CategoryStruct.id S) Φ.hom → (a ≅ b)
参数：Φ : (HasFibers.ι S).obj a ≅ (HasFibers.ι S).obj b；CategoryTheory.CategoryStru
ct.id S；a ≅ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of an isomorphism `Φ : (ι S).obj a ≅ (ι S).obj b` lying over `𝟙 S` to a
n isomorphism
in `Fib S`.
-/
noncomputable def Fib.isoMk {S : 𝒮} {a b : Fib p S}
    (Φ : (ι S).obj a ≅ (ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b where
  hom := Fib.homMk Φ.hom
  inv := Fib.homMk Φ.inv

/-- An object in `Fib p S` isomorphic in `𝒳` to a given object `a : 𝒳` such that `p(a) = S`. -/
/-
**HasFibers.Fib.mk** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers.Fib`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         {p : Cat
egoryTheory.Functor 𝒳 𝒮} → [inst_2 : HasFibers p] → {S : 𝒮} → {a : 𝒳} → p.obj a 
= S → HasFibers.Fib p S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object in `Fib p S` isomorphic in `𝒳` to a given object `a : 𝒳` such that `p(
a) = S`.
-/
noncomputable def Fib.mk {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fib p S :=
  Functor.objPreimage (inducedFunctor p S) (Fiber.mk ha)

/-- Applying `ι S` to the preimage of `a : 𝒳` in `Fib p S` yields an object isomorphic to `a`. -/
/-
**HasFibers.Fib.mkIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers.Fib`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         {p : Cat
egoryTheory.Functor 𝒳 𝒮} →           [inst_2 : HasFibers p] →             {S : 𝒮
} → {a : 𝒳} → (ha : p.obj a = S) → (HasFibers.ι S).obj (HasFibers.Fib.mk ha) ≅ a
参数：ha : p.obj a = S；HasFibers.ι S；HasFibers.Fib.mk ha。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `ι S` to the preimage of `a : 𝒳` in `Fib p S` yields an object isomorph
ic to `a`.
-/
noncomputable def Fib.mkIsoSelf {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    (ι S).obj (Fib.mk ha) ≅ a :=
  fiberInclusion.mapIso (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha))
/-
**HasFibers.Fib.mkIsoSelfIsHomLift** 是 Mathlib 中的一个定理，位于命名空间 `HasFibers.Fib`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheory.Functor 𝒳 𝒮}
 [inst_2 : HasFibers p] {S : 𝒮} {a : 𝒳} (ha : p.obj a = S),   p.IsHomLift (Categ
oryTheory.CategoryStruct.id S) (HasFibers.Fib.mkIsoSelf ha).hom
参数：ha : p.obj a = S；CategoryTheory.CategoryStruct.id S；HasFibers.Fib.mkIsoSelf h
a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `HasFibers.instIsEquivalenceFibFiberInducedFunctor`：∀ {𝒮 : Type u₁} {𝒳 : 
Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
-/
instance Fib.mkIsoSelfIsHomLift {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    IsHomLift p (𝟙 S) (Fib.mkIsoSelf ha).hom :=
  (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha)).hom.2

section

variable [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (f : R ⟶ S) (ha : p.obj a = S)

/-- The domain, taken in `Fib p R`, of some Cartesian morphism lifting a given
`f : R ⟶ S` in `𝒮` -/
/-
**HasFibers.mkPullback** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：mkPullback : Fib p R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain, taken in `Fib p R`, of some Cartesian morphism lifting a given
`f : R ⟶ S` in `𝒮`
-/
noncomputable def mkPullback : Fib p R :=
  Fib.mk (domain_eq p f (IsPreFibered.pullbackMap ha f))

/-- A Cartesian morphism lifting `f : R ⟶ S` with domain in the image of `Fib p R` -/
/-
**HasFibers.pullbackMap** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：pullbackMap : (ι R).obj (mkPullback f ha) ⟶ a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Cartesian morphism lifting `f : R ⟶ S` with domain in the image of `Fib p R`
-/
noncomputable def pullbackMap : (ι R).obj (mkPullback f ha) ⟶ a :=
  (Fib.mkIsoSelf (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

set_option backward.isDefEq.respectTransparency false in
/-
**HasFibers.pullbackMap.isCartesian** 是 Mathlib 中的一个定理，位于命名空间 `HasFibers.pullbac
kMap`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheory.Functor 𝒳 𝒮}
 [inst_2 : HasFibers p] [inst_3 : p.IsPreFibered] {R S : 𝒮} {a : 𝒳} (f : R ⟶ S) 
  (ha : p.obj a = S), p.IsCartesian f (HasFibers.pullbackMap f ha)
参数：f : R ⟶ S；ha : p.obj a = S；HasFibers.pullbackMap f ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.IsPreFibered.pullbackMap.IsCartesian`：∀ {𝒮 : Type
 u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Categor
yTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheor…
· 使用定理 `HasFibers.Fib.mkIsoSelfIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : 
CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳
]   {p : CategoryTheor…
-/
instance pullbackMap.isCartesian : IsCartesian p f (pullbackMap f ha) := by
  conv in f => rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

end

section

variable {R S : 𝒮} {a : 𝒳} {b b' : Fib p R} (f : R ⟶ S) (ψ : (ι R).obj b' ⟶ a)
    [IsCartesian p f ψ] (φ : (ι R).obj b ⟶ a) [IsHomLift p f φ]

/-- Given a fibered category p, b' b in Fib R, and a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b can be lifted to the fiber over R -/
/-
**HasFibers.inducedMap** 是 Mathlib 中的一个定义，位于命名空间 `HasFibers`。
形式化陈述：inducedMap : b ⟶ b'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fibered category p, b' b in Fib R, and a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b can be lifted to the fiber over R
-/
noncomputable def inducedMap : b ⟶ b' :=
  Fib.homMk (IsCartesian.map p f ψ φ)

@[reassoc]
/-
**HasFibers.inducedMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HasFibers`。
形式化陈述：inducedMap_comp : (ι R).map (inducedMap f ψ φ) ≫ ψ = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFibers.Fib.map_homMk`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryT
heory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : 
CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsCartesian.fac`：fac : IsCartesian.map p f φ φ' ≫
 φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inducedMap_comp : (ι R).map (inducedMap f ψ φ) ≫ ψ = φ := by
  simp only [inducedMap, Fib.map_homMk, IsCartesian.fac]

end

section

variable [IsFibered p] {R S : 𝒮} {a : 𝒳} {b : Fib p R}

/-- Given `a : 𝒳`, `b : Fib p R`, and a diagram
```
  b --φ--> a
  -        -
  |        |
  v        v
  R --f--> S
```
It can be factorized as
```
  b --τ--> b'--ψ--> a
  -        -        -
  |        |        |
  v        v        v
  R ====== R --f--> S
```
with `ψ` Cartesian over `f` and `τ` a map in `Fib p R`. -/
/-
**HasFibers.fiber_factorization** 是 Mathlib 中的一个引理，位于命名空间 `HasFibers`。
形式化陈述：fiber_factorization (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R
).obj b ⟶ a) [IsHomLift p f φ] : exists (b' : Fib p R) (τ : b ⟶ b') (ψ : (ι R).o
bj b' ⟶ a), IsStronglyCartesian p f ψ ∧ (((ι R).map τ) ≫ ψ = φ)
参数：ha : p.obj a = S；f : R ⟶ S；φ : (ι R).obj b ⟶ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsFibered.toIsPreFibered`：∀ {𝒮 : Type u₁} {𝒳 : Ty
pe u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `HasFibers.pullbackMap.isCartesian`：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst :
 CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Category.{v₂, u₂} 
𝒳]   {p : CategoryTheor…
· 使用引理 `HasFibers.inducedMap_comp`：inducedMap_comp : (ι R).map (inducedMap f ψ φ
) ≫ ψ = φ

--- 原说明 ---
Given `a : 𝒳`, `b : Fib p R`, and a diagram
```
  b --φ--> a
  -        -
  |        |
  v        v
  R --f--> S
```
It can be factorized as
```
  b --τ--> b'--ψ--> a
  -        -        -
  |        |        |
  v        v        v
  R ====== R --f--> S
```
with `ψ` Cartesian over `f` and `τ` a map in `Fib p R`.
-/
lemma fiber_factorization (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R).obj b ⟶ a)
    [IsHomLift p f φ] : ∃ (b' : Fib p R) (τ : b ⟶ b') (ψ : (ι R).obj b' ⟶ a),
      IsStronglyCartesian p f ψ ∧ (((ι R).map τ) ≫ ψ = φ) :=
  let ψ := pullbackMap f ha
  ⟨mkPullback f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

end

end

end HasFibers

