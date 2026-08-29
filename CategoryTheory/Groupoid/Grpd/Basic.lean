/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Category of groupoids

This file contains the definition of the category `Grpd` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Grpd ⥤ Type`
and `forgetToCat : Grpd ⥤ Cat`.

## Implementation notes

Though `Grpd` is not a concrete category, we use `Bundled` to define
its carrier type.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/--
Definition of `Grpd` / `Grpd` 的定义

English:
definition Grpd
  body: Bundled Groupoid.{v, u}

中文:
定义 Grpd
  定义体: Bundled Groupoid.{v, u}

Depends on / 依赖: Bundled, Groupoid
-/
def Grpd :=
  Bundled Groupoid.{v, u}

namespace Grpd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Grpd
  body: ⟨Bundled.of (SingleObj PUnit)⟩

中文:
实例 :
  签名: Inhabited Grpd
  定义体: ⟨Bundled.of (SingleObj PUnit)⟩

Depends on / 依赖: Bundled, Bundled.of, SingleObj
-/
instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩


/--
Instance `str'` / 实例 `str'`

English:
instance str'
  signature: (C : Grpd.{v, u})
  body: C.str

中文:
实例 str'
  签名: (C : Grpd.{v, u})
  定义体: C.str

Depends on / 依赖: C.str
-/
instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Grpd Type*
  body: Bundled.coeSort

中文:
实例 :
  签名: CoeSort Grpd 类型
  定义体: Bundled.coeSort

Depends on / 依赖: Bundled, Bundled.coeSort, coeSort
-/
instance : CoeSort Grpd Type* :=
  Bundled.coeSort

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (C : Type u) [Groupoid.{v} C]
  body: Bundled.of C

@[simp]

中文:
定义 of
  签名: (C : 类型u) [Groupoid.{v} C]
  定义体: Bundled.of C

@[simp]

Depends on / 依赖: Bundled, Bundled.of
-/
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (C : Type u) [Groupoid C]
  statement: (of C : Type u) = C
  proof: rfl

中文:
定理 coe_of
  条件: (C : 类型u) [Groupoid C]
  结论: (of C : 类型u) = C
  证明: rfl
-/
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : LargeCategory.{max v u} Grpd.{v, u} where
  body: C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl

中文:
实例 category
  签名: : LargeCategory.{max v u} Grpd.{v, u} where
  定义体: C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl
-/
instance category : LargeCategory.{max v u} Grpd.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl

/--
Definition of `objects` / `objects` 的定义

English:
definition objects
  signature: : Grpd.{v, u} ⥤ Type u where
  body: Bundled.α C
  map F := ↾F.obj

中文:
定义 objects
  签名: : Grpd.{v, u} ⥤ 类型u where
  定义体: Bundled.α C
  map F := ↾F.obj

Depends on / 依赖: Bundled
-/
def objects : Grpd.{v, u} ⥤ Type u where
  obj C := Bundled.α C
  map F := ↾F.obj

/--
Definition of `forgetToCat` / `forgetToCat` 的定义

English:
definition forgetToCat
  signature: : Grpd.{v, u} ⥤ Cat.{v, u} where
  body: Cat.of C
  map := Functor.toCatHom

中文:
定义 forgetToCat
  签名: : Grpd.{v, u} ⥤ Cat.{v, u} where
  定义体: Cat.of C
  map := Functor.toCatHom

Depends on / 依赖: Cat.of, HasInitial, hasInitial
-/
def forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of C
  map := Functor.toCatHom

instance (X : Grpd) : Groupoid (Grpd.forgetToCat.obj X) := inferInstanceAs (Groupoid X)

/--
Instance `forgetToCat_full` / 实例 `forgetToCat_full`

English:
instance forgetToCat_full
  signature: : forgetToCat.Full where map_surjective f
  body: ⟨f.toFunctor, rfl⟩

中文:
实例 forgetToCat_full
  签名: : forgetToCat.Full where map_surjective f
  定义体: ⟨f.toFunctor, rfl⟩

Depends on / 依赖: HasTerminal, f.toFunctor, hasTerminal, toFunctor
-/
instance forgetToCat_full : forgetToCat.Full where map_surjective f := ⟨f.toFunctor, rfl⟩

/--
Instance `forgetToCat_faithful` / 实例 `forgetToCat_faithful`

English:
instance forgetToCat_faithful
  signature: : forgetToCat.Faithful where
  body: congrArg (Cat.Hom.toFunctor)

中文:
实例 forgetToCat_faithful
  签名: : forgetToCat.Faithful where
  定义体: congrArg (Cat.Hom.toFunctor)

Depends on / 依赖: Cat.Hom.toFunctor, toFunctor
-/
instance forgetToCat_faithful : forgetToCat.Faithful where
  map_injective := congrArg (Cat.Hom.toFunctor)

/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E)
  statement: f ≫ g = f ⋙ g
  proof: rfl

中文:
定理 comp_eq_comp
  条件: {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E)
  结论: f ≫ g = f ⋙ g
  证明: rfl
-/
theorem comp_eq_comp {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl

/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: {C : Grpd.{v, u}}
  statement: 𝟙 C = 𝟭 C
  proof: rfl

中文:
定理 id_eq_id
  条件: {C : Grpd.{v, u}}
  结论: 𝟙 C = 𝟭 C
  证明: rfl
-/
theorem id_eq_id {C : Grpd.{v, u}} : 𝟙 C = 𝟭 C :=
  rfl

section Products

/--
Definition of `piLimitFan` / `piLimitFan` 的定义

English:
definition piLimitFan
  signature: ⦃J
  body: Limits.Fan.mk (@of (forall j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

中文:
定义 piLimitFan
  签名: ⦃J
  定义体: Limits.Fan.mk (@of (forall j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

Depends on / 依赖: CategoryTheory, CategoryTheory.Pi.eval, Limits, Limits.Fan.mk
-/
def piLimitFan ⦃J : Type u⦄ (F : J -> Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (forall j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `piLimitFanIsLimit` / `piLimitFanIsLimit` 的定义

English:
definition piLimitFanIsLimit
  signature: ⦃J
  body: Limits.Fan.IsLimit.mk (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)

中文:
定义 piLimitFanIsLimit
  签名: ⦃J
  定义体: Limits.Fan.IsLimit.mk (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)

Depends on / 依赖: Functor, Functor.pi, Functor.pi_ext, InitialMonoClass, IsLimit, Limits, Limits.Fan.IsLimit.mk, comp_eq_comp, initialMonoClass, intros, piLimitFan, pi_ext, s.proj, specialize
-/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J -> Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.Fan.IsLimit.mk (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)

/--
Instance `has_pi` / 实例 `has_pi`

English:
instance has_pi
  signature: : Limits.HasProducts.{u} Grpd.{u, u}
  body: Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

中文:
实例 has_pi
  签名: : Limits.HasProducts.{u} Grpd.{u, u}
  定义体: Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

Depends on / 依赖: Limits, Limits.hasProducts_of_limit_fans, hasProducts_of_limit_fans, piLimitFan, piLimitFanIsLimit
-/
instance has_pi : Limits.HasProducts.{u} Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

/--
Definition of `piIsoPi` / `piIsoPi` 的定义

English:
definition piIsoPi
  signature: (J : Type u) (f : J -> Grpd.{u, u})
  body: Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

中文:
定义 piIsoPi
  签名: (J : 类型u) (f : J -> Grpd.{u, u})
  定义体: Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

Depends on / 依赖: Discrete, Discrete.functor, HasZeroObject, HasZeroObject.zeroIsoTerminal.symm, IsLimit, Limits, Limits.IsLimit.conePointUniqueUpToIso, Limits.limit.isLimit, conePointUniqueUpToIso, functor, isLimit, isZero_zero, of_iso, piLimitFanIsLimit, zeroIsoTerminal
-/
noncomputable def piIsoPi (J : Type u) (f : J -> Grpd.{u, u}) : @of (forall j, f j) _ ≅ ∏ᶜ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `piIsoPi_hom_π` / 定理 `piIsoPi_hom_π`

English:
theorem piIsoPi_hom_π
  given: (J : Type u) (f : J -> Grpd.{u, u}) (j : J)
  proof: by
  simp [piIsoPi]
  rfl

中文:
定理 piIsoPi_hom_π
  条件: (J : 类型u) (f : J -> Grpd.{u, u}) (j : J)
  证明: by
  simp [piIsoPi]
  rfl

Depends on / 依赖: piIsoPi
-/
theorem piIsoPi_hom_π (J : Type u) (f : J -> Grpd.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl

end Products

end Grpd

end CategoryTheory
