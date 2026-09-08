/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGrpCat.free`: constructs the functor associating to a type `X` the free abelian group
  with generators `x : X`.
* `GrpCat.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `GrpCat.abelianize`: constructs the functor which sends a group `G` to its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGrpCat.adj`: proves that `AddCommGrpCat.free` is the left adjoint
  of the forgetful functor from abelian groups to types.
* `GrpCat.adj`: proves that `GrpCat.free` is the left adjoint of the forgetful functor
  from groups to types.
* `abelianizeAdj`: proves that `GrpCat.abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

universe u

open CategoryTheory Limits

namespace AddCommGrpCat

/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
@[simps obj map]
/-
**AddCommGrpCat.free** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：free : Type u ⥤ AddCommGrpCat where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGrpCat where
  obj α := of (FreeAbelianGroup α)
  map f := ofHom (FreeAbelianGroup.map f)

@[simp]
/-
**AddCommGrpCat.free_obj_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)
/-
**AddCommGrpCat.free_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：free_map_coe {α β : Type u} {f : α ⟶ β} (x : FreeAbelianGroup α) : (free.m
ap f) x = f < > x
参数：x : FreeAbelianGroup α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem free_map_coe {α β : Type u} {f : α ⟶ β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free-forgetful adjunction for abelian groups.
-/
/-
**AddCommGrpCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：adj : free ⊣ forget AddCommGrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := by
        refine ConcreteCategory.homEquiv.trans (Equiv.trans ?_ TypeCat.homEquiv.symm)
        exact FreeAbelianGroup.lift.symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be just `by intros; ext; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        dsimp [ConcreteCategory.homEquiv]
        rw [← FreeAbelianGroup.lift_comp]
        rfl }
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget AddCommGrpCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
/-
**AddCommGrpCat.** 是 Mathlib 中的一个示例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGrpCat.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective _).mp (Functor.map_mono (forget AddCommGrpCat) f)
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (free.{u}).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    by_cases! hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj free _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsSplitMono f := IsSplitMono.mk' { retraction := ↾g }
      infer_instance

end AddCommGrpCat

namespace GrpCat

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
/-
**GrpCat.free** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：free : Type u ⥤ GrpCat where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ Group` sending a type `X` to the free group with gene
rators `x : X`.
-/
def free : Type u ⥤ GrpCat where
  obj α := of (FreeGroup α)
  map f := ofHom (FreeGroup.map f)

/-- The free-forgetful adjunction for groups.
-/
/-
**GrpCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：adj : free ⊣ forget GrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget GrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans
          (Equiv.trans (FreeGroup.lift.symm) TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` doesn't apply this theorem anymore
        apply FreeGroup.ext_hom
        intros
        rfl }
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget GrpCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
-/
/-
**GrpCat.abelianize** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：abelianize : GrpCat.{u} ⥤ CommGrpCat.{u} where obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelia
nization `Gᵃᵇ`.
-/
def abelianize : GrpCat.{u} ⥤ CommGrpCat.{u} where
  obj G := CommGrpCat.of (Abelianization G)
  map f := CommGrpCat.ofHom (Abelianization.lift (Abelianization.of.comp f.hom))
  map_id := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization.lift).mp
    rfl
  map_comp := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization.lift).mp
    rfl

/-- The abelianization-forgetful adjunction from `Group` to `CommGroup`. -/
/-
**GrpCat.abelianizeAdj** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：abelianizeAdj : abelianize ⊣ forget₂ CommGrpCat.{u} GrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The abelianization-forgetful adjunction from `Group` to `CommGroup`.
-/
def abelianizeAdj : abelianize ⊣ forget₂ CommGrpCat.{u} GrpCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ((ConcreteCategory.homEquiv (C := CommGrpCat)).trans
        Abelianization.lift.symm).trans
        (ConcreteCategory.homEquiv (C := GrpCat)).symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp +instances only
        apply Eq.symm
        apply Abelianization.lift_unique
        intros
        apply Abelianization.lift_apply_of }

end Abelianization

end GrpCat

/-- The functor taking a monoid to its subgroup of units. -/
@[simps!]
/-
**MonCat.units** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonCat.units : MonCat.{u} ⥤ GrpCat.{u} where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a monoid to its subgroup of units.
-/
def MonCat.units : MonCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of Rˣ
  map f := GrpCat.ofHom <| Units.map f.hom
  map_id _ := GrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := GrpCat.ext fun _ => Units.ext rfl

/-- The forgetful-units adjunction between `GrpCat` and `MonCat`. -/
/-
**GrpCat.forget** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful-units adjunction between `GrpCat` and `MonCat`.
-/
def GrpCat.forget₂MonAdj : forget₂ GrpCat MonCat ⊣ MonCat.units.{u} := Adjunction.mk' {
  homEquiv _ Y :=
    { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
      invFun f := MonCat.ofHom ((Units.coeHom Y).comp f.hom) }
  unit :=
    { app X := ofHom (@toUnits X _)
      naturality _ _ _ := GrpCat.ext fun _ => Units.ext rfl }
  counit :=
    { app X := MonCat.ofHom (Units.coeHom X)
      naturality _ _ _ := MonCat.ext fun _ => rfl } }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨GrpCat.forget₂MonAdj⟩⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps!]
/-
**CommMonCat.units** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonCat.units : CommMonCat.{u} ⥤ CommGrpCat.{u} where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a monoid to its subgroup of units.
-/
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrpCat.{u} where
  obj R := CommGrpCat.of Rˣ
  map f := CommGrpCat.ofHom <| Units.map f.hom
  map_id _ := CommGrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := CommGrpCat.ext fun _ => Units.ext rfl

/-- The forgetful-units adjunction between `CommGrpCat` and `CommMonCat`. -/
/-
**CommGrpCat.forget** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful-units adjunction between `CommGrpCat` and `CommMonCat`.
-/
def CommGrpCat.forget₂CommMonAdj : forget₂ CommGrpCat CommMonCat ⊣ CommMonCat.units.{u} :=
  Adjunction.mk' {
    homEquiv := fun _ Y ↦
      { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
        invFun f := CommMonCat.ofHom ((Units.coeHom Y).comp f.hom) }
    unit.app X := ofHom toUnits.toMonoidHom
    -- `aesop` can find the following proof but it takes `0.5`s.
    unit.naturality _ _ _ := CommGrpCat.ext fun _ => Units.ext rfl
    counit.app X := CommMonCat.ofHom (Units.coeHom X)
    -- `aesop` can find the following proof but it takes `0.5`s.
    counit.naturality _ _ _ := CommMonCat.ext fun _ => rfl
    -- `aesop` can find the following proof but it takes `0.2`s.
    homEquiv_unit := by intros; rfl
    -- `aesop` can find the following proof but it takes `0.2`s.
    homEquiv_counit := by intros; rfl }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGrpCat.forget₂CommMonAdj⟩⟩
