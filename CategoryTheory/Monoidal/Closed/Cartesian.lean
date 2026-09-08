/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian closed categories

A cartesian closed category is a category with `CartesianMonoidalCategory` and `MonoidalClosed`
instances. There used to be a separate definition `CartesianClosed`, with its own API, but over time
this ended up as a duplicate of the former. Now, `CartesianClosed` and the surrounding API has been
deprecated, and the API for `MonoidalClosed` should be used instead. This file now contains a few
basic constructions for cartesian closed categories.

-/

@[expose] public section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X X' Y Y' Z : C}

/-
**CategoryTheory.CartesianMonoidalCategory.isLeftAdjoint_prod_functor** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] (A : C)   [CategoryTheory.Closed A], (Categ
oryTheory.Limits.prod.functor.obj A).IsLeftAdjoint
参数：A : C；CategoryTheory.Limits.prod.functor.obj A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_iso`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.ihom.instIsLeftAdjointTensorLeft`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (
A : C)   [CategoryTheory.Closed A], (…
-/
instance CartesianMonoidalCategory.isLeftAdjoint_prod_functor
    (A : C) [Closed A] :
    (prod.functor.obj A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

namespace CartesianClosed

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms obtained using an exponentiable object. -/
scoped notation:20 A " ⟹ " B:19 => (ihom A).obj B

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Functor.obj` -/
@[app_delab Functor.obj]
meta def delabFunctorObjExp : Delab :=
    whenPPOption getPPNotation <| withOverApp 6 do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Functor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``ihom 5
    withNaryArg 3 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms from an exponentiable object. -/
scoped notation:30 B " ^^ " A:30 => (ihom A).obj B

end CartesianClosed

open CartesianClosed

/-- The internal element which points at the given morphism. -/
/-
**CategoryTheory.internalizeHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：internalizeHom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
 {A Y : C} [Closed A] (f : A ⟶ Y) : 𝟙_ C ⟶ A ⟹ Y
参数：f : A ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The internal element which points at the given morphism.
-/
def internalizeHom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A Y : C} [Closed A]
    (f : A ⟶ Y) : 𝟙_ C ⟶ A ⟹ Y :=
  MonoidalClosed.curry (fst _ _ ≫ f)

variable {A B : C} [Closed A]

open MonoidalClosed

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
/-
**CategoryTheory.zeroMul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：zeroMul {I : C} (t : IsInitial I) : A otimes I ≅ I where hom
参数：t : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`.
-/
def zeroMul {I : C} (t : IsInitial I) : A ⊗ I ≅ I where
  hom := snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
/-
**CategoryTheory.mulZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：mulZero [BraidedCategory C] {I : C} (t : IsInitial I) : I otimes A ≅ I
参数：t : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`.
-/
def mulZero [BraidedCategory C] {I : C} (t : IsInitial I) : I ⊗ A ≅ I :=
  β_ _ _ ≪≫ zeroMul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
/-
**CategoryTheory.powZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：powZero [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C] :
 I ⟹ B ≅ 𝟙_ C where hom
参数：t : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`.
-/
def powZero [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C] : I ⟹ B ≅ 𝟙_ C where
  hom := default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
/-
**CategoryTheory.strict_initial** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f
参数：t : IsInitial I；f : A ⟶ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.zeroMul_hom`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] {A : C}   [in
st_2 : CategoryT…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.isIso_of_mono_of_isSplitEpi`：isIso_of_mono_of_isSplitEpi 
{X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f

--- 原说明 ---
If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial obje
ct from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  have : Mono f := by
    rw [← lift_snd (𝟙 A) f, ← zeroMul_hom t]
    exact mono_comp _ _
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi
/-
**CategoryTheory.to_initial_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f
参数：f : A ⟶ ⊥_ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.strict_initial`：strict_initial {I : C} (t : IsInitial I) 
(f : A ⟶ I) : IsIso f
-/
instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
/-
**CategoryTheory.initial_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：initial_mono {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C] : Mono (
t.to B)
参数：B : C；t : IsInitial I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.strict_initial`：strict_initial {I : C} (t : IsInitial I) 
(f : A ⟶ I) : IsIso f
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
If an initial object `0` exists in a CCC then every morphism from it is monic.
-/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩
/-
**CategoryTheory.Initial.mono_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Initi
al`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasInitia
l C] (B : C) [CategoryTheory.MonoidalClosed C],   CategoryTheory.Mono (CategoryT
heory.Limits.initial.to B)
参数：B : C；CategoryTheory.Limits.initial.to B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.initial_mono`：initial_mono {I : C} (B : C) (t : IsInitial
 I) [MonoidalClosed C] : Mono (t.to B)
-/
instance Initial.mono_to [HasInitial C] (B : C) [MonoidalClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial

variable {D : Type u₂} [Category.{v₂} D]

section Functor

variable [CartesianMonoidalCategory D]

/-- Transport the property of being Cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
@[instance_reducible]
/-
**CategoryTheory.cartesianClosedOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：cartesianClosedOfEquiv (e : C ≌ D) [MonoidalClosed C] : MonoidalClosed D
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…

--- 原说明 ---
Transport the property of being Cartesian closed across an equivalence of catego
ries.

Note we didn't require any coherence between the choice of finite products here,
 since we transport
along the `prodComparison` isomorphism.
-/
noncomputable def cartesianClosedOfEquiv (e : C ≌ D) [MonoidalClosed C] : MonoidalClosed D :=
  letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

end Functor

end CategoryTheory

