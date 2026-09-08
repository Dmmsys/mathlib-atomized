/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Adjunctions and (co)monads

We develop the basic relationship between adjunctions and (co)monads.

Given an adjunction `h : L ⊣ R`, we have `h.toMonad : Monad C` and `h.toComonad : Comonad D`.
We then have
`Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.algebra`
sending `Y : D` to the Eilenberg-Moore algebra for `L ⋙ R` with underlying object `R.obj X`,
and dually `Comonad.comparison`.

We say `R : D ⥤ C` is `MonadicRightAdjoint`, if it is a right adjoint and its `Monad.comparison`
is an equivalence of categories. (Similarly for `ComonadicLeftAdjoint`.)

Finally we prove that reflective functors are `MonadicRightAdjoint` and coreflective functors are
`ComonadicLeftAdjoint`.
-/

@[expose] public section


namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

set_option backward.defeqAttrib.useBackward true in
/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps! coe η μ]
/-
**CategoryTheory.Adjunction.toMonad** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ad
junction`。
形式化陈述：toMonad (h : L ⊣ R) : Monad C where toFunctor
参数：h : L ⊣ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induc
es a monad on
the category `C`.
-/
def toMonad (h : L ⊣ R) : Monad C where
  toFunctor := L ⋙ R
  η := h.unit
  μ := whiskerRight (whiskerLeft L h.counit) R
  assoc X := by
    dsimp
    rw [← R.map_comp]
    simp
  right_unit X := by
    dsimp
    rw [← R.map_comp]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
@[simps coe ε δ]
/-
**CategoryTheory.Adjunction.toComonad** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Adjunction`。
形式化陈述：toComonad (h : L ⊣ R) : Comonad D where toFunctor
参数：h : L ⊣ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induc
es a comonad on
the category `D`.
-/
def toComonad (h : L ⊣ R) : Comonad D where
  toFunctor := R ⋙ L
  ε := h.counit
  δ := whiskerRight (whiskerLeft R h.unit) L
  coassoc X := by
    dsimp
    rw [← L.map_comp]
    simp
  right_counit X := by
    dsimp
    rw [← L.map_comp]
    simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The monad induced by the Eilenberg-Moore adjunction is the original monad. -/
@[simps!]
/-
**CategoryTheory.Adjunction.adjToMonadIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：adjToMonadIso (T : Monad C) : T.adj.toMonad ≅ T
参数：T : Monad C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad induced by the Eilenberg-Moore adjunction is the original monad.
-/
def adjToMonadIso (T : Monad C) : T.adj.toMonad ≅ T :=
  MonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps!]
/-
**CategoryTheory.Adjunction.adjToComonadIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：adjToComonadIso (G : Comonad C) : G.adj.toComonad ≅ G
参数：G : Comonad C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comonad induced by the Eilenberg-Moore adjunction is the original comonad.
-/
def adjToComonadIso (G : Comonad C) : G.adj.toComonad ≅ G :=
  ComonadIso.mk (NatIso.ofComponents fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Given an adjunction `L ⊣ R`, if `L ⋙ R` is abstractly isomorphic to the identity functor, then the
unit is an isomorphism.
-/
/-
**CategoryTheory.Adjunction.unitAsIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：unitAsIsoOfIso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : 𝟭 C ≅ L ⋙ R where hom
参数：adj : L ⊣ R；i : L ⋙ R ≅ 𝟭 C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `L ⊣ R`, if `L ⋙ R` is abstractly isomorphic to the identity
 functor, then the
unit is an isomorphism.
-/
def unitAsIsoOfIso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : 𝟭 C ≅ L ⋙ R where
  hom := adj.unit
  inv := i.hom ≫ (adj.toMonad.transport i).μ
  hom_inv_id := by
    rw [← assoc]
    ext X
    exact (adj.toMonad.transport i).right_unit X
  inv_hom_id := by
    rw [assoc, ← Iso.eq_inv_comp, comp_id, ← id_comp i.inv, Iso.eq_comp_inv, assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toMonad.transport i).right_unit X

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Adjunction.isIso_unit_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：isIso_unit_of_iso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit
参数：adj : L ⊣ R；i : L ⋙ R ≅ 𝟭 C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_unit_of_iso (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit :=
  (inferInstanceAs (IsIso (unitAsIsoOfIso adj i).hom))

/--
Given an adjunction `L ⊣ R`, if `L ⋙ R` is isomorphic to the identity functor, then `L` is
fully faithful.
-/
/-
**CategoryTheory.Adjunction.fullyFaithfulLOfCompIsoId** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：fullyFaithfulLOfCompIsoId (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : L.FullyFaithfu
l
参数：adj : L ⊣ R；i : L ⋙ R ≅ 𝟭 C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isIso_unit_of_iso`：isIso_unit_of_iso (adj : L 
⊣ R) (i : L ⋙ R ≅ 𝟭 C) : IsIso adj.unit

--- 原说明 ---
Given an adjunction `L ⊣ R`, if `L ⋙ R` is isomorphic to the identity functor, t
hen `L` is
fully faithful.
-/
noncomputable def fullyFaithfulLOfCompIsoId (adj : L ⊣ R) (i : L ⋙ R ≅ 𝟭 C) : L.FullyFaithful :=
  haveI := adj.isIso_unit_of_iso i
  adj.fullyFaithfulLOfIsIsoUnit

set_option backward.isDefEq.respectTransparency false in
/--
Given an adjunction `L ⊣ R`, if `R ⋙ L` is abstractly isomorphic to the identity functor, then the
counit is an isomorphism.
-/
/-
**CategoryTheory.Adjunction.counitAsIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：counitAsIsoOfIso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R ⋙ L ≅ 𝟭 D where hom
参数：adj : L ⊣ R；j : R ⋙ L ≅ 𝟭 D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `L ⊣ R`, if `R ⋙ L` is abstractly isomorphic to the identity
 functor, then the
counit is an isomorphism.
-/
def counitAsIsoOfIso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R ⋙ L ≅ 𝟭 D where
  hom := adj.counit
  inv := (adj.toComonad.transport j).δ ≫ j.inv
  hom_inv_id := by
    rw [← assoc, Iso.comp_inv_eq, id_comp, ← comp_id j.hom, ← Iso.inv_comp_eq, ← assoc,
      NatTrans.id_comm]
    ext X
    exact (adj.toComonad.transport j).right_counit X
  inv_hom_id := by
    rw [assoc]
    ext X
    exact (adj.toComonad.transport j).right_counit X
/-
**CategoryTheory.Adjunction.isIso_counit_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Adjunction`。
形式化陈述：isIso_counit_of_iso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit
参数：adj : L ⊣ R；j : R ⋙ L ≅ 𝟭 D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_counit_of_iso (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit :=
  inferInstanceAs (IsIso (counitAsIsoOfIso adj j).hom)

/--
Given an adjunction `L ⊣ R`, if `R ⋙ L` is isomorphic to the identity functor, then `R` is
fully faithful.
-/
/-
**CategoryTheory.Adjunction.fullyFaithfulROfCompIsoId** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：fullyFaithfulROfCompIsoId (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R.FullyFaithfu
l
参数：adj : L ⊣ R；j : R ⋙ L ≅ 𝟭 D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isIso_counit_of_iso`：isIso_counit_of_iso (adj 
: L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : IsIso adj.counit

--- 原说明 ---
Given an adjunction `L ⊣ R`, if `R ⋙ L` is isomorphic to the identity functor, t
hen `R` is
fully faithful.
-/
noncomputable def fullyFaithfulROfCompIsoId (adj : L ⊣ R) (j : R ⋙ L ≅ 𝟭 D) : R.FullyFaithful :=
  haveI := adj.isIso_counit_of_iso j
  adj.fullyFaithfulROfIsIsoCounit

end Adjunction

set_option backward.defeqAttrib.useBackward true in
/-- Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
/-
**CategoryTheory.Monad.comparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mona
d`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {R : CategoryTheory.Functor D C} → (h : L ⊣
 R) → CategoryTheory.Functor D h.toMonad.Algebra
参数：h : L ⊣ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Mona
d.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying 
object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
def Monad.comparison (h : L ⊣ R) : D ⥤ h.toMonad.Algebra where
  obj X :=
    { A := R.obj X
      a := R.map (h.counit.app X)
      assoc := by
        dsimp
        rw [← R.map_comp, ← Adjunction.counit_naturality, R.map_comp] }
  map f :=
    { f := R.map f
      h := by
        dsimp
        rw [← R.map_comp, Adjunction.counit_naturality, R.map_comp] }

set_option backward.defeqAttrib.useBackward true in
/-- The underlying object of `(Monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
/-
**CategoryTheory.Monad.comparisonForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Monad`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {R : CategoryTheory.Functor D C} → (h : L ⊣
 R) → (CategoryTheory.Monad.comparison h).comp h.toMonad.forget ≅ R
参数：h : L ⊣ R；CategoryTheory.Monad.comparison h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of `(Monad.comparison R).obj X` is just `R.obj X`.
-/
def Monad.comparisonForget (h : L ⊣ R) : Monad.comparison h ⋙ h.toMonad.forget ≅ R where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
/-
**CategoryTheory.Monad.left_comparison** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Monad`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheory.Functor C D}
 {R : CategoryTheory.Functor D C} (h : L ⊣ R),   L.comp (CategoryTheory.Monad.co
mparison h) = h.toMonad.free
参数：h : L ⊣ R；CategoryTheory.Monad.comparison h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monad.left_comparison (h : L ⊣ R) : L ⋙ Monad.comparison h = h.toMonad.free :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.Faithful] (h : L ⊣ R) : (Monad.comparison h).Faithful where
  map_injective {_ _} _ _ w := R.map_injective (congr_arg Monad.Algebra.Hom.f w :)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (T : Monad C) : (Monad.comparison T.adj).Full where
  map_surjective {_ _} f := ⟨⟨f.f, by simpa using! f.h⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (T : Monad C) : (Monad.comparison T.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        unit := by simpa using X.unit
        assoc := by simpa using X.assoc },
    ⟨Monad.Algebra.isoMk (Iso.refl _)⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
/-
**CategoryTheory.Comonad.comparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Co
monad`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {R : CategoryTheory.Functor D C} → (h : L ⊣
 R) → CategoryTheory.Functor C h.toComonad.Coalgebra
参数：h : L ⊣ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any adjunction `L ⊣ R`, there is a comparison functor `CategoryTheory.Como
nad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlyin
g object
`L.obj X`.
-/
def Comonad.comparison (h : L ⊣ R) : C ⥤ h.toComonad.Coalgebra where
  obj X :=
    { A := L.obj X
      a := L.map (h.unit.app X)
      coassoc := by
        dsimp
        rw [← L.map_comp, ← Adjunction.unit_naturality, L.map_comp] }
  map f :=
    { f := L.map f
      h := by
        dsimp
        rw [← L.map_comp]
        simp }

set_option backward.defeqAttrib.useBackward true in
/-- The underlying object of `(Comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
/-
**CategoryTheory.Comonad.comparisonForget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comonad`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {R : CategoryTheory.Functor D C} →         
    (h : L ⊣ R) → (CategoryTheory.Comonad.comparison h).comp h.toComonad.forget 
≅ L
参数：h : L ⊣ R；CategoryTheory.Comonad.comparison h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of `(Comonad.comparison L).obj X` is just `L.obj X`.
-/
def Comonad.comparisonForget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    Comonad.comparison h ⋙ h.toComonad.forget ≅ L where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
/-
**CategoryTheory.Comonad.left_comparison** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Comonad`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheory.Functor C D}
 {R : CategoryTheory.Functor D C} (h : L ⊣ R),   R.comp (CategoryTheory.Comonad.
comparison h) = h.toComonad.cofree
参数：h : L ⊣ R；CategoryTheory.Comonad.comparison h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Comonad.left_comparison (h : L ⊣ R) : R ⋙ Comonad.comparison h = h.toComonad.cofree :=
  rfl
/-
**CategoryTheory.Comonad.comparison_faithful_of_faithful** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Comonad`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheory.Functor C D}
 {R : CategoryTheory.Functor D C} [L.Faithful] (h : L ⊣ R),   (CategoryTheory.Co
monad.comparison h).Faithful
参数：h : L ⊣ R；CategoryTheory.Comonad.comparison h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance Comonad.comparison_faithful_of_faithful [L.Faithful] (h : L ⊣ R) :
    (Comonad.comparison h).Faithful where
  map_injective {_ _} _ _ w := L.map_injective (congr_arg Comonad.Coalgebra.Hom.f w :)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : Comonad C) : (Comonad.comparison G.adj).Full where
  map_surjective f := ⟨⟨f.f, by simpa using! f.h⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : Comonad C) : (Comonad.comparison G.adj).EssSurj where
  mem_essImage X :=
    ⟨{  A := X.A
        a := X.a
        counit := by simpa using X.counit
        coassoc := by simpa using X.coassoc },
      ⟨Comonad.Coalgebra.isoMk (Iso.refl _)⟩⟩

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `Monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
/-
**CategoryTheory.MonadicRightAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor D C → Type (max (max (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `Mona
d.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an eq
uivalence.
-/
class MonadicRightAdjoint (R : D ⥤ C) where
  /-- a choice of left adjoint for `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R
  eqv : (Monad.comparison adj).IsEquivalence

/-- The left adjoint functor to `R` given by `[MonadicRightAdjoint R]`. -/
/-
**CategoryTheory.monadicLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monadicLeftAdjoint (R : D ⥤ C) [MonadicRightAdjoint R] : C ⥤ D
参数：R : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint functor to `R` given by `[MonadicRightAdjoint R]`.
-/
def monadicLeftAdjoint (R : D ⥤ C) [MonadicRightAdjoint R] : C ⥤ D :=
  MonadicRightAdjoint.L (R := R)

/-- The adjunction `monadicLeftAdjoint R ⊣ R` given by `[MonadicRightAdjoint R]`. -/
/-
**CategoryTheory.monadicAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monadicAdjunction (R : D ⥤ C) [MonadicRightAdjoint R] : monadicLeftAdjoint
 R ⊣ R
参数：R : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `monadicLeftAdjoint R ⊣ R` given by `[MonadicRightAdjoint R]`.
-/
def monadicAdjunction (R : D ⥤ C) [MonadicRightAdjoint R] :
    monadicLeftAdjoint R ⊣ R :=
  MonadicRightAdjoint.adj
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : D ⥤ C) [MonadicRightAdjoint R] :
    (Monad.comparison (monadicAdjunction R)).IsEquivalence :=
  MonadicRightAdjoint.eqv
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : D ⥤ C) [MonadicRightAdjoint R] : R.IsRightAdjoint :=
  (monadicAdjunction R).isRightAdjoint
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (T : Monad C) : MonadicRightAdjoint T.forget where
  L := T.free
  adj := T.adj
  eqv := { }

/--
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `Comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
/-
**CategoryTheory.ComonadicLeftAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → Type (max (max (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `Com
onad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an eq
uivalence.
-/
class ComonadicLeftAdjoint (L : C ⥤ D) where
  /-- a choice of right adjoint for `L` -/
  R : D ⥤ C
  /-- `L` is a left adjoint -/
  adj : L ⊣ R
  eqv : (Comonad.comparison adj).IsEquivalence

/-- The right adjoint functor to `L` given by `[ComonadicLeftAdjoint L]`. -/
/-
**CategoryTheory.comonadicRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：comonadicRightAdjoint (L : C ⥤ D) [ComonadicLeftAdjoint L] : D ⥤ C
参数：L : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint functor to `L` given by `[ComonadicLeftAdjoint L]`.
-/
def comonadicRightAdjoint (L : C ⥤ D) [ComonadicLeftAdjoint L] : D ⥤ C :=
  ComonadicLeftAdjoint.R (L := L)

/-- The adjunction `L ⊣ comonadicRightAdjoint L` given by `[ComonadicLeftAdjoint L]`. -/
/-
**CategoryTheory.comonadicAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：comonadicAdjunction (L : C ⥤ D) [ComonadicLeftAdjoint L] : L ⊣ comonadicRi
ghtAdjoint L
参数：L : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `L ⊣ comonadicRightAdjoint L` given by `[ComonadicLeftAdjoint L]`
.
-/
def comonadicAdjunction (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    L ⊣ comonadicRightAdjoint L :=
  ComonadicLeftAdjoint.adj
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : C ⥤ D) [ComonadicLeftAdjoint L] :
    (Comonad.comparison (comonadicAdjunction L)).IsEquivalence :=
  ComonadicLeftAdjoint.eqv
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : C ⥤ D) [ComonadicLeftAdjoint L] : L.IsLeftAdjoint :=
  (comonadicAdjunction L).isLeftAdjoint
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (G : Comonad C) : ComonadicLeftAdjoint G.forget where
  R := G.cofree
  adj := G.adj
  eqv := { }

set_option backward.defeqAttrib.useBackward true in
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance μ_iso_of_reflective [Reflective R] : IsIso (reflectorAdjunction R).toMonad.μ := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance δ_iso_of_coreflective [Coreflective R] : IsIso (coreflectorAdjunction R).toComonad.δ := by
  dsimp
  infer_instance

attribute [instance] MonadicRightAdjoint.eqv
attribute [instance] ComonadicLeftAdjoint.eqv

namespace Reflective

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Reflective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Reflectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Reflective R] (X : (reflectorAdjunction R).toMonad.Algebra) :
    IsIso ((reflectorAdjunction R).unit.app X.A) :=
  ⟨⟨X.a,
      ⟨X.unit, by
        dsimp only [Functor.id_obj]
        rw [← (reflectorAdjunction R).unit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [unit_obj_eq_map_unit, ← Functor.map_comp, ← Functor.map_comp]
        dsimp [X.unit]
        simpa using congrArg (fun t ↦ R.map ((reflector R).map t)) X.unit ⟩⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Reflective.comparison_essSurj** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Reflective`。
形式化陈述：comparison_essSurj [Reflective R] : (Monad.comparison (reflectorAdjunction
 R)).EssSurj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Reflective.instIsIsoAppUnitReflectorAdjunctionA`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   {R : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Monad.Algebra.unit_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (self : T.Algebra) {Z 
: C}   (h : self.A ⟶ Z),   Ca…
-/
instance comparison_essSurj [Reflective R] :
    (Monad.comparison (reflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(reflector R).obj X.A, ⟨?_⟩⟩⟩
  symm
  refine Monad.Algebra.isoMk ?_ ?_
  · exact asIso ((reflectorAdjunction R).unit.app X.A)
  dsimp only [Functor.comp_map, Monad.comparison_obj_a, asIso_hom, Functor.comp_obj,
    Monad.comparison_obj_A, Adjunction.toMonad_coe]
  rw [← cancel_epi ((reflectorAdjunction R).unit.app X.A)]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, comp_id]
  apply (X.unit_assoc _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Reflective.comparison_full** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Reflective`。
形式化陈述：comparison_full [R.Full] {L : C ⥤ D} (adj : L ⊣ R) : (Monad.comparison adj
).Full where map_surjective f
参数：adj : L ⊣ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.ext'`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (X Y : T.Algebra)   (f g
 : X ⟶ Y), f.f = g.f → f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Monad.comparison_map_f`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : L ⊣ R) :
    (Monad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by cat_disch⟩

end Reflective

namespace Coreflective

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Coreflective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Corefle
ctive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Coreflective R] (X : (coreflectorAdjunction R).toComonad.Coalgebra) :
    IsIso ((coreflectorAdjunction R).counit.app X.A) :=
  ⟨⟨X.a,
      ⟨by
        dsimp only [Functor.id_obj]
        rw [← (coreflectorAdjunction R).counit_naturality]
        dsimp only [Functor.comp_obj, Adjunction.toMonad_coe]
        rw [counit_obj_eq_map_counit, ← Functor.map_comp, ← Functor.map_comp]
        simpa using congrArg (fun t ↦ R.map ((coreflector R).map t)) X.counit, X.counit⟩⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Coreflective.comparison_essSurj** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Coreflective`。
形式化陈述：comparison_essSurj [Coreflective R] : (Comonad.comparison (coreflectorAdju
nction R)).EssSurj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Coreflective.instIsIsoAppCounitCoreflectorAdjunctionA`：∀ 
{C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 
: CategoryTheory.Category.{v₂, u₂} D]   {R : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.Comonad.Coalgebra.counit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (self : G.Coalgebra)
,   CategoryTheory.CategorySt…
-/
instance comparison_essSurj [Coreflective R] :
    (Comonad.comparison (coreflectorAdjunction R)).EssSurj := by
  refine ⟨fun X => ⟨(coreflector R).obj X.A, ⟨?_⟩⟩⟩
  refine Comonad.Coalgebra.isoMk ?_ ?_
  · exact (asIso ((coreflectorAdjunction R).counit.app X.A))
  rw [← cancel_mono ((coreflectorAdjunction R).counit.app X.A)]
  simp only [Functor.comp_obj, Functor.id_obj,
    assoc]
  simpa using (coreflectorAdjunction R).counit.app X.A ≫= X.counit.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Coreflective.comparison_full** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Coreflective`。
形式化陈述：comparison_full [R.Full] {L : C ⥤ D} (adj : R ⊣ L) : (Comonad.comparison a
dj).Full where map_surjective f
参数：adj : R ⊣ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.ext'`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (X Y : G.Coalgebra
)   (f g : X ⟶ Y), f.f = g.f → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Comonad.comparison_map_f`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comparison_full [R.Full] {L : C ⥤ D} (adj : R ⊣ L) :
    (Comonad.comparison adj).Full where
  map_surjective f := ⟨R.preimage f.f, by cat_disch⟩

end Coreflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
-- see Note [lower instance priority]
/-- Any reflective inclusion has a monadic right adjoint.
cf Prop 5.3.3 of [Riehl][riehl2017] -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any reflective inclusion has a monadic right adjoint.
cf Prop 5.3.3 of [Riehl][riehl2017]
-/
instance (priority := 100) monadicOfReflective [Reflective R] :
    MonadicRightAdjoint R where
  L := reflector R
  adj := reflectorAdjunction R
  eqv := { full := Reflective.comparison_full _ }

/-- Any coreflective inclusion has a comonadic left adjoint.
cf Dual statement of Prop 5.3.3 of [Riehl][riehl2017] -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any coreflective inclusion has a comonadic left adjoint.
cf Dual statement of Prop 5.3.3 of [Riehl][riehl2017]
-/
instance (priority := 100) comonadicOfCoreflective [Coreflective R] :
    ComonadicLeftAdjoint R where
  R := coreflector R
  adj := coreflectorAdjunction R
  eqv := { full := Coreflective.comparison_full _ }

end CategoryTheory

