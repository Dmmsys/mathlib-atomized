/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Limits and colimits in the category of (co)algebras

This file shows that the forgetful functor `forget T : Algebra T ⥤ C` for a monad `T : C ⥤ C`
creates limits and creates any colimits which `T` preserves.
This is used to show that `Algebra T` has any limits which `C` has, and any colimits which `C` has
and `T` preserves.
This is generalised to the case of a monadic functor `D ⥤ C`.

Dually, this file shows that the forgetful functor `forget T : Coalgebra T ⥤ C` for a
comonad `T : C ⥤ C` creates colimits and creates any limits which `T` preserves.
This is used to show that `Coalgebra T` has any colimits which `C` has, and any limits which `C` has
and `T` preserves.
This is generalised to the case of a comonadic functor `D ⥤ C`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category CategoryTheory.Functor

open CategoryTheory.Limits

universe v u v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
namespace Monad

variable {C : Type u₁} [Category.{v₁} C]
variable {T : Monad C}
variable {J : Type u} [Category.{v} J]

namespace ForgetCreatesLimits

variable (D : J ⥤ Algebra T) (c : Cone (D ⋙ T.forget)) (t : IsLimit c)

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) The natural transformation used to define the new cone -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesLimits.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Monad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) The natural transformation used to define the new cone
-/
def γ : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j := (D.obj j).a

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simps! π_app]
/-
**CategoryTheory.Monad.ForgetCreatesLimits.newCone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Monad.ForgetCreatesLimits`。
形式化陈述：newCone : Cone (D ⋙ forget T) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) This new cone is used to construct the algebra structure
-/
def newCone : Cone (D ⋙ forget T) where
  pt := T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D

set_option backward.isDefEq.respectTransparency false in
/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesLimits.conePoint** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Monad.ForgetCreatesLimits`。
形式化陈述：conePoint : Algebra T where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra structure which will be the apex of the new limit cone for `D`.
-/
def conePoint : Algebra T where
  A := c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc, t.fac, newCone_π_app, ← T.η.naturality_assoc, Functor.id_map,
        (D.obj j).unit]
      simp
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc, Category.assoc, t.fac (newCone D c), newCone_π_app, ←
        Functor.map_comp_assoc, t.fac (newCone D c), newCone_π_app, ← T.μ.naturality_assoc,
        (D.obj j).assoc, Functor.map_comp, Category.assoc]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Construct the lifted cone in `Algebra T` which will be limiting. -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesLimits.liftedCone** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Monad.ForgetCreatesLimits`。
形式化陈述：liftedCone : Cone D where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Construct the lifted cone in `Algebra T` which will be limiting.
-/
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f).symm }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesLimits.liftedConeIsLimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Monad.ForgetCreatesLimits`。
形式化陈述：liftedConeIsLimit : IsLimit (liftedCone D c t) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Prove that the lifted cone is limiting.
-/
def liftedConeIsLimit : IsLimit (liftedCone D c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc, Category.assoc, t.fac, newCone_π_app, ← Functor.map_comp_assoc,
            t.fac, Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)

end ForgetCreatesLimits

-- Theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
/-
**CategoryTheory.Monad.forgetCreatesLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Monad`。
形式化陈述：forgetCreatesLimits : CreatesLimitsOfSize (forget T) where CreatesLimitsOf
Shape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category creates limits.
-/
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize (forget T) where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }

/-- `D ⋙ forget T` has a limit, then `D` has a limit. -/
/-
**CategoryTheory.Monad.hasLimit_of_comp_forget_hasLimit** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Monad`。
形式化陈述：hasLimit_of_comp_forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget
 T)] : HasLimit D
参数：D : J ⥤ Algebra T；D ⋙ forget T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K

--- 原说明 ---
`D ⋙ forget T` has a limit, then `D` has a limit.
-/
theorem hasLimit_of_comp_forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)] :
    HasLimit D :=
  hasLimit_of_created D (forget T)

namespace ForgetCreatesColimits

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Algebra T} (c : Cocone (D ⋙ forget T)) (t : IsColimit c)

-- We have a diagram D of shape J in the category of algebras, and we assume that we are given a
-- colimit for its image D ⋙ forget T under the forgetful functor, say its point is L.
-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the point of a cocone for this
-- diagram. In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the point of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:
/-- (Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
point `colimit (D ⋙ forget T)`.
-/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesColimits.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Monad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
The natural transformation given by the algebra structure maps, used to construc
t a cocone `c` with
point `colimit (D ⋙ forget T)`.
-/
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j := (D.obj j).a

/-- (Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesColimits.newCocone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：newCocone : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural tra
nsformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
def newCocone : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  ι := γ ≫ c.ι

variable [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]

/-- (Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
/-
**CategoryTheory.Monad.ForgetCreatesColimits.lambda** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra 
on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and 
the fact that
`T` preserves colimits to produce this morphism.
-/
noncomputable abbrev lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt :=
  (isColimitOfPreserves _ t).desc (newCocone c)

/-- (Impl) The key property defining the map `λ : TL ⟶ L`. -/
/-
**CategoryTheory.Monad.ForgetCreatesColimits.commuting** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a
 ≫ c.ι.app j
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…

--- 原说明 ---
(Impl) The key property defining the map `λ : TL ⟶ L`.
-/
theorem commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
  (isColimitOfPreserves _ t).fac (newCocone c) j

variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesColimits.coconePoint** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：coconePoint : Algebra T where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We
 are required to
show it satisfies the two algebra laws, which follow from the algebra laws for t
he image of `D` and
our `commuting` lemma.
-/
noncomputable def coconePoint : Algebra T where
  A := c.pt
  a := lambda c t
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _,
      commuting, Algebra.unit_assoc (D.obj j)]
    simp
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app, Functor.mapCocone_ι_app,
      show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _, ←
      Functor.map_comp_assoc, commuting, Functor.map_comp, Category.assoc, commuting]
    apply (D.obj j).assoc_assoc _

set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) Construct the lifted cocone in `Algebra T` which will be colimiting. -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesColimits.liftedCocone** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：liftedCocone : Cocone D where pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.ForgetCreatesColimits.commuting`：commuting (j : J) 
: (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j

--- 原说明 ---
(Impl) Construct the lifted cocone in `Algebra T` which will be colimiting.
-/
noncomputable def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
/-
**CategoryTheory.Monad.ForgetCreatesColimits.liftedCoconeIsColimit** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Monad.ForgetCreatesColimits`。
形式化陈述：liftedCoconeIsColimit : IsColimit (liftedCocone c t) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Prove that the lifted cocone is colimiting.
-/
noncomputable def liftedCoconeIsColimit : IsColimit (liftedCocone c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc, ← Category.assoc, t.fac, commuting, Category.assoc, t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)

end ForgetCreatesColimits

open ForgetCreatesColimits

-- TODO: the converse of this is true as well
set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
/-
**CategoryTheory.Monad.forgetCreatesColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Monad`。
形式化陈述：forgetCreatesColimit (D : J ⥤ Algebra T) [PreservesColimit (D ⋙ forget T) 
(T : C ⥤ C)] [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesColim
it D (forget T)
参数：D : J ⥤ Algebra T；D ⋙ forget T；T : C ⥤ C；(D ⋙ forget T) ⋙ ↑T；T : C ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.ForgetCreatesColimits.commuting`：commuting (j : J) 
: (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category for a monad creates any 
colimit
which the monad itself preserves.
-/
noncomputable instance forgetCreatesColimit (D : J ⥤ Algebra T)
    [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesColimit D (forget T) :=
  createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f) } }
      validLift := Cocone.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }
/-
**CategoryTheory.Monad.forgetCreatesColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Monad`。
形式化陈述：forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] : Cr
eatesColimitsOfShape J (forget T) where CreatesColimit
参数：T : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] :
    CreatesColimitsOfShape J (forget T) where CreatesColimit := by infer_instance
/-
**CategoryTheory.Monad.forgetCreatesColimits** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Monad`。
形式化陈述：forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] : Creat
esColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape
参数：T : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape := by infer_instance

/-- For `D : J ⥤ Algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
of shape `J` are preserved by `T`.
-/
/-
**CategoryTheory.Monad.forget_creates_colimits_of_monad_preserves** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：forget_creates_colimits_of_monad_preserves [PreservesColimitsOfShape J (T 
: C ⥤ C)] (D : J ⥤ Algebra T) [HasColimit (D ⋙ forget T)] : HasColimit D
参数：T : C ⥤ C；D : J ⥤ Algebra T；D ⋙ forget T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
For `D : J ⥤ Algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit pr
ovided colimits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_colimits_of_monad_preserves [PreservesColimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Algebra T) [HasColimit (D ⋙ forget T)] : HasColimit D :=
  hasColimit_of_created D (forget T)

end Monad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type u} [Category.{v} J]

/-
**CategoryTheory.comp_comparison_forget_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory`。
形式化陈述：comp_comparison_forget_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoi
nt R] [HasLimit (F ⋙ R)] : HasLimit ((F ⋙ Monad.comparison (monadicAdjunction R)
) ⋙ Monad.forget _)
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp_comparison_forget_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] :
    HasLimit ((F ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _) := by
  assumption
/-
**CategoryTheory.comp_comparison_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R] [
HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (monadicAdjunction R))
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.hasLimit_of_comp_forget_hasLimit`：hasLimit_of_comp_
forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)] : HasLimit D
-/
instance comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (monadicAdjunction R)) :=
  Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))

/-- Any monadic functor creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.monadicCreatesLimits** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] : CreatesLimitsOf
Size.{v, u} R
参数：R : D ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceAlgebraToMonadMonadicAdjunctionCompariso
n`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (R : CategoryTheor…

--- 原说明 ---
Any monadic functor creates limits.
-/
noncomputable def monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] :
    CreatesLimitsOfSize.{v, u} R :=
  createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
@[instance_reducible]
/-
**CategoryTheory.monadicCreatesColimitOfPreservesColimit** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory`。
形式化陈述：monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D) [MonadicRi
ghtAdjoint R] [PreservesColimit (K ⋙ R) (monadicLeftAdjoint R ⋙ R)] [PreservesCo
limit ((K ⋙ R) ⋙ monadicLeftAdjoint R ⋙ R) (monadicLeftAdjoint R ⋙ R)] : Creates
Colimit K R
参数：R : D ⥤ C；K : J ⥤ D；K ⋙ R；monadicLeftAdjoint R ⋙ R；(K ⋙ R) ⋙ monadicLeftAdjoi
nt R ⋙ R；monadicLeftAdjoint R ⋙ R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceAlgebraToMonadMonadicAdjunctionCompariso
n`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (R : CategoryTheor…

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category for a monad creates any 
colimit
which the monad itself preserves.
-/
noncomputable def monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D)
    [MonadicRightAdjoint R] [PreservesColimit (K ⋙ R) (monadicLeftAdjoint R ⋙ R)]
    [PreservesColimit ((K ⋙ R) ⋙ monadicLeftAdjoint R ⋙ R) (monadicLeftAdjoint R ⋙ R)] :
      CreatesColimit K R := by
  -- Porting note: It would be nice to have a variant of apply which introduces goals for missing
  -- instances.
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e

/-- A monadic functor creates any colimits of shapes it preserves. -/
@[instance_reducible]
/-
**CategoryTheory.monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C) [Monad
icRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R
参数：R : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monadic functor creates any colimits of shapes it preserves.
-/
noncomputable def monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C)
    [MonadicRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R :=
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjoint_preservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩

/-- A monadic functor creates colimits if it preserves colimits. -/
@[instance_reducible]
/-
**CategoryTheory.monadicCreatesColimitsOfPreservesColimits** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory`。
形式化陈述：monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint
 R] [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R where Cr
eatesColimitsOfShape
参数：R : D ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A monadic functor creates colimits if it preserves colimits.
-/
noncomputable def monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint R]
    [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R where
  CreatesColimitsOfShape :=
    monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _

section

/-
**CategoryTheory.hasLimit_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflect
ive R] : HasLimit F
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
theorem hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] :
    HasLimit F :=
  haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R

/-- If `C` has limits of shape `J` then any reflective subcategory has limits of shape `J`. -/
/-
**CategoryTheory.hasLimitsOfShape_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflect
ive R] : HasLimitsOfShape J D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_reflective`：hasLimit_of_reflective (F : J ⥤ D
) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] : HasLimit F
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has limits of shape `J` then any reflective subcategory has limits of sha
pe `J`.
-/
theorem hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_reflective F R⟩

/-- If `C` has limits then any reflective subcategory has limits. -/
/-
**CategoryTheory.hasLimits_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：hasLimits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective
 R] : HasLimitsOfSize.{v, u} D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_reflective`：hasLimitsOfShape_of_refle
ctive [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] : HasLimitsOfShape J D
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has limits then any reflective subcategory has limits.
-/
theorem hasLimits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_reflective R⟩

/-- If `C` has colimits of shape `J` then any reflective subcategory has colimits of shape `J`. -/
/-
**CategoryTheory.hasColimitsOfShape_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOf
Shape J C] : HasColimitsOfShape J D where has_colimit
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `C` has colimits of shape `J` then any reflective subcategory has colimits of
 shape `J`.
-/
theorem hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D where
  has_colimit := fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      let : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjoint_preservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) :) ≪≫ F.rightUnitor

/-- If `C` has colimits then any reflective subcategory has colimits. -/
/-
**CategoryTheory.hasColimits_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：hasColimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v
, u} C] : HasColimitsOfSize.{v, u} D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_reflective`：hasColimitsOfShape_of_r
eflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] : HasColimitsOfSha
pe J D where has_colimit
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits then any reflective subcategory has colimits.
-/
theorem hasColimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_reflective R⟩

/-- The reflector always preserves terminal objects. Note this in general doesn't apply to any other
limit.
-/
/-
**CategoryTheory.leftAdjoint_preservesTerminal_of_reflective** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：leftAdjoint_preservesTerminal_of_reflective (R : D ⥤ C) [Reflective R] : P
reservesLimitsOfShape (Discrete.{v} PEmpty) (monadicLeftAdjoint R) where preserv
esLimit {K}
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_reflective`：hasLimit_of_reflective (F : J ⥤ D
) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] : HasLimit F
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.Reflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u
₂} D}   {R : CategoryTheor…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
The reflector always preserves terminal objects. Note this in general doesn't ap
ply to any other
limit.
-/
lemma leftAdjoint_preservesTerminal_of_reflective (R : D ⥤ C) [Reflective R] :
    PreservesLimitsOfShape (Discrete.{v} PEmpty) (monadicLeftAdjoint R) where
  preservesLimit {K} := by
    let F := Functor.empty.{v} D
    let : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      have : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasLimit F := hasLimit_of_reflective F R
      constructor
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit F R
      apply (isLimitOfPreserves _ (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

end

-- We dualise all of the above for comonads.
namespace Comonad

variable {T : Comonad C}

namespace ForgetCreatesColimits'

variable (D : J ⥤ Coalgebra T) (c : Cocone (D ⋙ T.forget)) (t : IsColimit c)

/-- (Impl) The natural transformation used to define the new cocone -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesColimits.** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Comonad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) The natural transformation used to define the new cocone
-/
def γ : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T where app j := (D.obj j).a

/-- (Impl) This new cocone is used to construct the coalgebra structure -/
@[simps! ι_app]
/-
**CategoryTheory.Comonad.ForgetCreatesColimits.newCocone** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Comonad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) This new cocone is used to construct the coalgebra structure
-/
def newCocone : Cocone (D ⋙ forget T) where
  pt := T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The coalgebra structure which will be the point of the new colimit cone for `D`. -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesColimits.coconePoint** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Comonad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coalgebra structure which will be the point of the new colimit cone for `D`.
-/
def coconePoint : Coalgebra T where
  A := c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc, (D.obj j).counit, Category.id_comp]
  coassoc := t.hom_ext fun j ↦ by
    simp only [Functor.comp_obj, forget_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc, (D.obj j).coassoc, ← Functor.map_comp, t.fac (newCocone D c) j,
      newCocone_ι_app, Functor.map_comp, assoc]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Construct the lifted cocone in `Coalgebra T` which will be colimiting. -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesColimits.liftedCocone** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Comonad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Construct the lifted cocone in `Coalgebra T` which will be colimiting.
-/
def liftedCocone : Cocone D where
  pt := coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f) }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesColimits.liftedCoconeIsColimit** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ForgetCreatesColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Prove that the lifted cocone is colimiting.
-/
def liftedCoconeIsColimit : IsColimit (liftedCocone D c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc, ← Category.assoc, t.fac, newCocone_ι_app, t.fac,
            Functor.mapCocone_ι_app, Category.assoc, ← Functor.map_comp, t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesColimits'

-- Dual to theorem 5.6.5 from [Riehl][riehl2017]
/-- The forgetful functor from the Eilenberg-Moore category creates colimits. -/
/-
**CategoryTheory.Comonad.forgetCreatesColimit** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Comonad`。
形式化陈述：forgetCreatesColimit : CreatesColimitsOfSize (forget T) where CreatesColim
itsOfShape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category creates colimits.
-/
noncomputable instance forgetCreatesColimit : CreatesColimitsOfSize (forget T) where
  CreatesColimitsOfShape := {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocone.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }

/-- If `D ⋙ forget T` has a colimit, then `D` has a colimit. -/
/-
**CategoryTheory.Comonad.hasColimit_of_comp_forget_hasColimit** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：hasColimit_of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D 
⋙ forget T)] : HasColimit D
参数：D : J ⥤ Coalgebra T；D ⋙ forget T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K

--- 原说明 ---
If `D ⋙ forget T` has a colimit, then `D` has a colimit.
-/
theorem hasColimit_of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)] :
    HasColimit D :=
  hasColimit_of_created D (forget T)

namespace ForgetCreatesLimits'

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Coalgebra T} (c : Cone (D ⋙ forget T)) (t : IsLimit c)

/-- (Impl)
The natural transformation given by the coalgebra structure maps, used to construct a cone `c` with
point `limit (D ⋙ forget T)`.
-/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
The natural transformation given by the coalgebra structure maps, used to constr
uct a cone `c` with
point `limit (D ⋙ forget T)`.
-/
def γ : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j := (D.obj j).a

/-- (Impl)
A cone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the limiting cone for `D ⋙ forget T`.
-/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.newCone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
A cone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural trans
formation `γ`
with the limiting cone for `D ⋙ forget T`.
-/
def newCone : Cone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  π := c.π ≫ γ

variable [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]

/-- (Impl)
Define the map `λ : L ⟶ TL`, which will serve as the structure of the algebra on `L`, and
we will show is the limiting object. We use the cone constructed by `c` and the fact that
`T` preserves limits to produce this morphism.
-/
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.lambda** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
Define the map `λ : L ⟶ TL`, which will serve as the structure of the algebra on
 `L`, and
we will show is the limiting object. We use the cone constructed by `c` and the 
fact that
`T` preserves limits to produce this morphism.
-/
noncomputable abbrev lambda : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt :=
  (isLimitOfPreserves _ t).lift (newCone c)

/-- (Impl) The key property defining the map `λ : L ⟶ TL`. -/
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.commuting** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) The key property defining the map `λ : L ⟶ TL`.
-/
theorem commuting (j : J) : lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a :=
  (isLimitOfPreserves _ t).fac (newCone c) j

variable [PreservesLimit ((D ⋙ forget T) ⋙ T.toFunctor) T.toFunctor]
variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl)
Construct the limiting coalgebra from the map `λ : L ⟶ TL` given by `lambda`. We are required to
show it satisfies the two coalgebra laws, which follow from the coalgebra laws for the image of `D`
and our `commuting` lemma.
-/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.conePoint** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl)
Construct the limiting coalgebra from the map `λ : L ⟶ TL` given by `lambda`. We
 are required to
show it satisfies the two coalgebra laws, which follow from the coalgebra laws f
or the image of `D`
and our `commuting` lemma.
-/
noncomputable def conePoint : Coalgebra T where
  A := c.pt
  a := lambda c t
  counit := t.hom_ext fun j ↦ by
    rw [assoc, ← show _ = _ ≫ c.π.app j from T.ε.naturality _, ← assoc, commuting, assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app, Functor.mapCone_π_app, assoc,
      ← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _, assoc, ← Functor.map_comp, commuting,
      Functor.map_comp, ← assoc, commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc, ← assoc, ← assoc, commuting]

set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) Construct the lifted cone in `Coalgebra T` which will be limiting. -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.liftedCone** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Construct the lifted cone in `Coalgebra T` which will be limiting.
-/
noncomputable def liftedCone : Cone D where
  pt := conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp, ← c.w]
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
/-
**CategoryTheory.Comonad.ForgetCreatesLimits.liftedConeIsLimit** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Comonad.ForgetCreatesLimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Prove that the lifted cone is limiting.
-/
noncomputable def liftedConeIsLimit : IsLimit (liftedCone c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc, ← t.fac, Category.assoc, t.fac, commuting, ← assoc, ← assoc, t.fac,
            assoc, ← Functor.map_comp, t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesLimits'

open ForgetCreatesLimits'

-- TODO: the converse of this is true as well
set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from the Eilenberg-Moore category for a comonad creates any limit
which the comonad itself preserves.
-/
/-
**CategoryTheory.Comonad.forgetCreatesLimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Comonad`。
形式化陈述：forgetCreatesLimit (D : J ⥤ Coalgebra T) [PreservesLimit (D ⋙ forget T) (T
 : C ⥤ C)] [PreservesLimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesLimit D (
forget T)
参数：D : J ⥤ Coalgebra T；D ⋙ forget T；T : C ⥤ C；(D ⋙ forget T) ⋙ ↑T；T : C ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.ForgetCreatesLimits'.commuting`：commuting (j : J)
 : lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category for a comonad creates an
y limit
which the comonad itself preserves.
-/
noncomputable instance forgetCreatesLimit (D : J ⥤ Coalgebra T)
    [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesLimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesLimit D (forget T) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f).symm } }
      validLift := Cone.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }
/-
**CategoryTheory.Comonad.forgetCreatesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Comonad`。
形式化陈述：forgetCreatesLimitsOfShape [PreservesLimitsOfShape J (T : C ⥤ C)] : Create
sLimitsOfShape J (forget T) where CreatesLimit
参数：T : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forgetCreatesLimitsOfShape [PreservesLimitsOfShape J (T : C ⥤ C)] :
    CreatesLimitsOfShape J (forget T) where CreatesLimit := by infer_instance
/-
**CategoryTheory.Comonad.forgetCreatesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Comonad`。
形式化陈述：forgetCreatesLimits [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)] : CreatesLi
mitsOfSize.{v, u} (forget T) where CreatesLimitsOfShape
参数：T : C ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forgetCreatesLimits [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesLimitsOfSize.{v, u} (forget T) where CreatesLimitsOfShape := by infer_instance

/-- For `D : J ⥤ Coalgebra T`, `D ⋙ forget T` has a limit, then `D` has a limit provided limits
of shape `J` are preserved by `T`.
-/
/-
**CategoryTheory.Comonad.forget_creates_limits_of_comonad_preserves** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：forget_creates_limits_of_comonad_preserves [PreservesLimitsOfShape J (T : 
C ⥤ C)] (D : J ⥤ Coalgebra T) [HasLimit (D ⋙ forget T)] : HasLimit D
参数：T : C ⥤ C；D : J ⥤ Coalgebra T；D ⋙ forget T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
For `D : J ⥤ Coalgebra T`, `D ⋙ forget T` has a limit, then `D` has a limit prov
ided limits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_limits_of_comonad_preserves [PreservesLimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Coalgebra T) [HasLimit (D ⋙ forget T)] : HasLimit D :=
  hasLimit_of_created D (forget T)

end Comonad

/-
**CategoryTheory.comp_comparison_forget_hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：comp_comparison_forget_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAd
joint R] [HasColimit (F ⋙ R)] : HasColimit ((F ⋙ Comonad.comparison (comonadicAd
junction R)) ⋙ Comonad.forget _)
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp_comparison_forget_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] :
    HasColimit ((F ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _) := by
  assumption
/-
**CategoryTheory.comp_comparison_hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory`。
形式化陈述：comp_comparison_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R
] [HasColimit (F ⋙ R)] : HasColimit (F ⋙ Comonad.comparison (comonadicAdjunction
 R))
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.hasColimit_of_comp_forget_hasColimit`：hasColimit_
of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)] : Ha
sColimit D
-/
instance comp_comparison_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] : HasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R)) :=
  Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))

/-- Any comonadic functor creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.comonadicCreatesColimits** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：comonadicCreatesColimits (R : D ⥤ C) [ComonadicLeftAdjoint R] : CreatesCol
imitsOfSize.{v, u} R
参数：R : D ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceCoalgebraToComonadComonadicAdjunctionCom
parison`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u
₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (L : CategoryTheor…

--- 原说明 ---
Any comonadic functor creates colimits.
-/
noncomputable def comonadicCreatesColimits (R : D ⥤ C) [ComonadicLeftAdjoint R] :
    CreatesColimitsOfSize.{v, u} R :=
  createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))

/-- The forgetful functor from the Eilenberg-Moore category for a comonad creates any limit
which the comonad itself preserves.
-/
@[instance_reducible]
/-
**CategoryTheory.comonadicCreatesLimitOfPreservesLimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory`。
形式化陈述：comonadicCreatesLimitOfPreservesLimit (R : D ⥤ C) (K : J ⥤ D) [ComonadicLe
ftAdjoint R] [PreservesLimit (K ⋙ R) (comonadicRightAdjoint R ⋙ R)] [PreservesLi
mit ((K ⋙ R) ⋙ comonadicRightAdjoint R ⋙ R) (comonadicRightAdjoint R ⋙ R)] : Cre
atesLimit K R
参数：R : D ⥤ C；K : J ⥤ D；K ⋙ R；comonadicRightAdjoint R ⋙ R；(K ⋙ R) ⋙ comonadicRigh
tAdjoint R ⋙ R；comonadicRightAdjoint R ⋙ R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceCoalgebraToComonadComonadicAdjunctionCom
parison`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u
₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (L : CategoryTheor…

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category for a comonad creates an
y limit
which the comonad itself preserves.
-/
noncomputable def comonadicCreatesLimitOfPreservesLimit (R : D ⥤ C) (K : J ⥤ D)
    [ComonadicLeftAdjoint R] [PreservesLimit (K ⋙ R) (comonadicRightAdjoint R ⋙ R)]
    [PreservesLimit ((K ⋙ R) ⋙ comonadicRightAdjoint R ⋙ R) (comonadicRightAdjoint R ⋙ R)] :
      CreatesLimit K R := by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e

/-- A comonadic functor creates any limits of shapes it preserves. -/
@[instance_reducible]
/-
**CategoryTheory.comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape (R : D ⥤ C) [Comonad
icLeftAdjoint R] [PreservesLimitsOfShape J R] : CreatesLimitsOfShape J R
参数：R : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonadic functor creates any limits of shapes it preserves.
-/
noncomputable def comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape (R : D ⥤ C)
    [ComonadicLeftAdjoint R] [PreservesLimitsOfShape J R] : CreatesLimitsOfShape J R :=
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjoint_preservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩

/-- A comonadic functor creates limits if it preserves limits. -/
@[instance_reducible]
/-
**CategoryTheory.comonadicCreatesLimitsOfPreservesLimits** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory`。
形式化陈述：comonadicCreatesLimitsOfPreservesLimits (R : D ⥤ C) [ComonadicLeftAdjoint 
R] [PreservesLimitsOfSize.{v, u} R] : CreatesLimitsOfSize.{v, u} R where Creates
LimitsOfShape
参数：R : D ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A comonadic functor creates limits if it preserves limits.
-/
noncomputable def comonadicCreatesLimitsOfPreservesLimits (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [PreservesLimitsOfSize.{v, u} R] : CreatesLimitsOfSize.{v, u} R where
  CreatesLimitsOfShape :=
    comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _

section

/-
**CategoryTheory.hasColimit_of_coreflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：hasColimit_of_coreflective (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [C
oreflective R] : HasColimit F
参数：F : J ⥤ D；R : D ⥤ C；F ⋙ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
-/
theorem hasColimit_of_coreflective (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] :
    HasColimit F :=
  haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R

/-- If `C` has colimits of shape `J` then any coreflective subcategory has colimits of shape `J`. -/
/-
**CategoryTheory.hasColimitsOfShape_of_coreflective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：hasColimitsOfShape_of_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [C
oreflective R] : HasColimitsOfShape J D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_coreflective`：hasColimit_of_coreflective (F
 : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] : HasColimit F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits of shape `J` then any coreflective subcategory has colimits 
of shape `J`.
-/
theorem hasColimitsOfShape_of_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R] :
    HasColimitsOfShape J D :=
  ⟨fun F => hasColimit_of_coreflective F R⟩

/-- If `C` has colimits then any coreflective subcategory has colimits. -/
/-
**CategoryTheory.hasColimits_of_coreflective** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：hasColimits_of_coreflective (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Core
flective R] : HasColimitsOfSize.{v, u} D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_coreflective`：hasColimitsOfShape_of
_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R] : HasColimit
sOfShape J D
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits then any coreflective subcategory has colimits.
-/
theorem hasColimits_of_coreflective (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Coreflective R] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩

/-- If `C` has limits of shape `J` then any coreflective subcategory has limits of shape `J`. -/
/-
**CategoryTheory.hasLimitsOfShape_of_coreflective** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：hasLimitsOfShape_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOf
Shape J C] : HasLimitsOfShape J D where has_limit
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Coreflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂,
 u₂} D}   {L : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `C` has limits of shape `J` then any coreflective subcategory has limits of s
hape `J`.
-/
theorem hasLimitsOfShape_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D where
  has_limit := fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      let : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjoint_preservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) :))).symm

/-- If `C` has limits then any coreflective subcategory has limits. -/
/-
**CategoryTheory.hasLimits_of_coreflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：hasLimits_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v
, u} C] : HasLimitsOfSize.{v, u} D
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_coreflective`：hasLimitsOfShape_of_cor
eflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C] : HasLimitsOfShape
 J D where has_limit
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has limits then any coreflective subcategory has limits.
-/
theorem hasLimits_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩

/-- The coreflector always preserves initial objects. Note this in general doesn't apply to any
other colimit.
-/
/-
**CategoryTheory.rightAdjoint_preservesInitial_of_coreflective** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory`。
形式化陈述：rightAdjoint_preservesInitial_of_coreflective (R : D ⥤ C) [Coreflective R]
 : PreservesColimitsOfShape (Discrete.{v} PEmpty) (comonadicRightAdjoint R) wher
e preservesColimit {K}
参数：R : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_coreflective`：hasColimit_of_coreflective (F
 : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] : HasColimit F
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFull`：∀ {C : Type u₁} {D : Type u₂} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Coreflective.toFaithful`：∀ {C : Type u₁} {D : Type u₂} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂,
 u₂} D}   {L : CategoryTheor…
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
The coreflector always preserves initial objects. Note this in general doesn't a
pply to any
other colimit.
-/
lemma rightAdjoint_preservesInitial_of_coreflective (R : D ⥤ C) [Coreflective R] :
    PreservesColimitsOfShape (Discrete.{v} PEmpty) (comonadicRightAdjoint R) where
  preservesColimit {K} := by
    let F := Functor.empty.{v} D
    let : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      have : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasColimit F := hasColimit_of_coreflective F R
      constructor
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit F R
      apply (isColimitOfPreserves _ (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

end

end CategoryTheory

