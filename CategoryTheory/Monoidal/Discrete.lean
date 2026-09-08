/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induce monoidal functors.
-/

@[expose] public section


universe u u'

open CategoryTheory Discrete MonoidalCategory

variable (M : Type u) [Monoid M]

namespace CategoryTheory

@[to_additive (attr := simps tensorObj_as leftUnitor rightUnitor associator) Discrete.addMonoidal]
/-
**CategoryTheory.Discrete.monoidal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dis
crete`。
形式化陈述：(M : Type u) → [Monoid M] → CategoryTheory.MonoidalCategory (CategoryTheor
y.Discrete M)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Discrete.monoidal : MonoidalCategory (Discrete M) where
  tensorUnit := Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Discrete.eqToIso (mul_one X.as)
  associator _ _ _ := Discrete.eqToIso (mul_assoc _ _ _)

@[to_additive (attr := simp) Discrete.addMonoidal_tensorUnit_as]
/-
**CategoryTheory.Discrete.monoidal_tensorUnit_as** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Discrete`。
形式化陈述：∀ (M : Type u) [inst : Monoid M], (CategoryTheory.MonoidalCategoryStruct.t
ensorUnit (CategoryTheory.Discrete M)).as = 1
参数：M : Type u；CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.D
iscrete M)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidal_tensorUnit_as : (𝟙_ (Discrete M)).as = 1 := rfl

variable {M} {N : Type u'} [Monoid N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive Discrete.addMonoidalFunctor /--
An additive morphism between `AddMonoid`s gives a
monoidal functor between the corresponding discrete monoidal categories. -/]
/-
**CategoryTheory.Discrete.monoidalFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Discrete`。
形式化陈述：{M : Type u} →   [inst : Monoid M] →     {N : Type u'} →       [inst_1 : M
onoid N] → (M →* N) → CategoryTheory.Functor (CategoryTheory.Discrete M) (Catego
ryTheory.Discrete N)
参数：M →* N；CategoryTheory.Discrete M；CategoryTheory.Discrete N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Discrete.monoidalFunctor (F : M →* N) : Discrete M ⥤ Discrete N :=
  Discrete.functor (fun X ↦ Discrete.mk (F X))

@[to_additive (attr := simp) Discrete.addMonoidalFunctor_obj]
/-
**CategoryTheory.Discrete.monoidalFunctor_obj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Discrete`。
形式化陈述：∀ {M : Type u} [inst : Monoid M] {N : Type u'} [inst_1 : Monoid N] (F : M 
→* N) (m : M),   (CategoryTheory.Discrete.monoidalFunctor F).obj { as := m } = {
 as := F m }
参数：F : M →* N；m : M；CategoryTheory.Discrete.monoidalFunctor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidalFunctor_obj (F : M →* N) (m : M) :
    (Discrete.monoidalFunctor F).obj (Discrete.mk m) = Discrete.mk (F m) := rfl

@[to_additive Discrete.addMonoidalFunctorMonoidal]
/-
**CategoryTheory.Discrete.monoidalFunctorMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Discrete`。
形式化陈述：{M : Type u} →   [inst : Monoid M] →     {N : Type u'} → [inst_1 : Monoid 
N] → (F : M →* N) → (CategoryTheory.Discrete.monoidalFunctor F).Monoidal
参数：F : M →* N；CategoryTheory.Discrete.monoidalFunctor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Discrete.monoidalFunctorMonoidal (F : M →* N) :
    (Discrete.monoidalFunctor F).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_one.symm
        μIso := fun m₁ m₂ ↦ Discrete.eqToIso (F.map_mul _ _).symm }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[to_additive Discrete.addMonoidalFunctor_ε]
/-
**CategoryTheory.Discrete.monoidalFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidalFunctor_ε (F : M →* N) :
    ε (monoidalFunctor F) = Discrete.eqToHom F.map_one.symm := rfl

@[to_additive Discrete.addMonoidalFunctor_η]
/-
**CategoryTheory.Discrete.monoidalFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidalFunctor_η (F : M →* N) :
    η (monoidalFunctor F) = Discrete.eqToHom F.map_one := rfl

@[to_additive Discrete.addMonoidalFunctor_μ]
/-
**CategoryTheory.Discrete.monoidalFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidalFunctor_μ (F : M →* N) (m₁ m₂ : Discrete M) :
    μ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _).symm := rfl

@[to_additive Discrete.addMonoidalFunctor_δ]
/-
**CategoryTheory.Discrete.monoidalFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Discrete.monoidalFunctor_δ (F : M →* N) (m₁ m₂ : Discrete M) :
    δ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _) := rfl

variable {K : Type u} [Monoid K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Discrete.addMonoidalFunctorComp
      /-- The monoidal natural isomorphism corresponding to
composing two additive morphisms. -/]
/-
**CategoryTheory.Discrete.monoidalFunctorComp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Discrete`。
形式化陈述：{M : Type u} →   [inst : Monoid M] →     {N : Type u'} →       [inst_1 : M
onoid N] →         {K : Type u} →           [inst_2 : Monoid K] →             (F
 : M →* N) →               (G : N →* K) →                 (CategoryTheory.Discre
te.monoidalFunctor F).comp (CategoryTheory.Discrete.monoidalFunctor G) ≅        
           CategoryTheory.Discrete.monoidalFunctor (G.comp F)
参数：F : M →* N；G : N →* K；CategoryTheory.Discrete.monoidalFunctor F；CategoryTheor
y.Discrete.monoidalFunctor G；G.comp F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Discrete.monoidalFunctorComp (F : M →* N) (G : N →* K) :
    Discrete.monoidalFunctor F ⋙ Discrete.monoidalFunctor G ≅
      Discrete.monoidalFunctor (G.comp F) := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
@[to_additive Discrete.addMonoidalFunctorComp_isMonoidal]
/-
**CategoryTheory.Discrete.monoidalFunctorComp_isMonoidal** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Discrete`。
形式化陈述：∀ {M : Type u} [inst : Monoid M] {N : Type u'} [inst_1 : Monoid N] {K : Ty
pe u} [inst_2 : Monoid K] (F : M →* N)   (G : N →* K), CategoryTheory.NatTrans.I
sMonoidal (CategoryTheory.Discrete.monoidalFunctorComp F G).hom
参数：F : M →* N；G : N →* K；CategoryTheory.Discrete.monoidalFunctorComp F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance Discrete.monoidalFunctorComp_isMonoidal (F : M →* N) (G : N →* K) :
    NatTrans.IsMonoidal (Discrete.monoidalFunctorComp F G).hom where
  unit := by
    dsimp only [comp_ε, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_μ]
    simp [eqToHom_map]

end CategoryTheory

