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
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ AddCommGrpCat where
  body: of (FreeAbelianGroup α)
  map f := ofHom (FreeAbelianGroup.map f)

@[simp]

中文:
定义 free
  签名: : 类型u ⥤ 加法交换群范畴 where
  定义体: of (FreeAbelianGroup α)
  map f := ofHom (FreeAbelianGroup.map f)

@[simp]

Depends on / 依赖: FreeAbelianGroup
-/
def free : Type u ⥤ AddCommGrpCat where
  obj α := of (FreeAbelianGroup α)
  map f := ofHom (FreeAbelianGroup.map f)

@[simp]
/--
theorem `free_obj_coe` / 定理 `free_obj_coe`

English:
theorem free_obj_coe
  given: {α : Type u}
  statement: (free.obj α : Type u) = FreeAbelianGroup α
  proof: rfl

中文:
定理 free_obj_coe
  条件: {α : 类型u}
  结论: (free.obj α : 类型u) = 自由交换群 α
  证明: rfl
-/
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)
/--
theorem `free_map_coe` / 定理 `free_map_coe`

English:
theorem free_map_coe
  given: {α β : Type u} {f : α ⟶ β} (x : FreeAbelianGroup α)
  proof: rfl

中文:
定理 free_map_coe
  条件: {α β : 类型u} {f : α ⟶ β} (x : 自由交换群 α)
  证明: rfl
-/
theorem free_map_coe {α β : Type u} {f : α ⟶ β} (x : FreeAbelianGroup α) :
(free.map f) x = f < > x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget AddCommGrpCat.{u}
  body: Adjunction.mkOfHomEquiv
    { homEquiv X Y := by
        refine ConcreteCategory.homEquiv.trans (Equiv.trans ?_ TypeCat.homEquiv.symm)
        exact FreeAbelianGroup.lift.symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be just `by intros; ext; rfl`

中文:
定义 adj
  签名: : free ⊣ forget 加法交换群范畴.{u}
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X Y := by
        refine ConcreteCategory.homEquiv.trans (Equiv.trans ?_ TypeCat.homEquiv.symm)
        exact FreeAbelianGroup.lift.symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be just `by intros; ext; rfl`

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, ConcreteCategory, ConcreteCategory.homEquiv.trans, Equiv.trans, FreeAbelianGroup, FreeAbelianGroup.lift.symm, TypeCat, TypeCat.homEquiv.symm, homEquiv, mkOfHomEquiv
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: free.{u}.IsLeftAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: free.{u}.是左伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget AddCommGrpCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: (forget 加法交换群范畴.{u}).是右伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : (forget AddCommGrpCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGrpCat.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective _).mp (Functor.map_mono (forget AddCommGrpCat) f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (free.{u}).PreservesMonomorphisms
  body: by
    by_cases! hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj free _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsS

中文:
实例 :
  签名: (free.{u}).保持Monomorphisms
  定义体: by
    by_cases! hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj free _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsS

Depends on / 依赖: Function, Function.Injective, Injective, IsEmpty, IsInitial, IsInitial.isInitialObj, IsSplitMono, IsSplitMono.mk, Types.initial_iff_empty, eq_of_tgt, hasLeftInverse, hf.hasLeftInverse, infer_instance, initial_iff_empty, intros, isInitialObj, isZero, isZero.eq_of_tgt, mono_iff_injective, retraction
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

/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ GrpCat where
  body: of (FreeGroup α)
  map f := ofHom (FreeGroup.map f)

中文:
定义 free
  签名: : 类型u ⥤ 群范畴 where
  定义体: of (FreeGroup α)
  map f := ofHom (FreeGroup.map f)

Depends on / 依赖: FreeGroup
-/
def free : Type u ⥤ GrpCat where
  obj α := of (FreeGroup α)
  map f := ofHom (FreeGroup.map f)

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget GrpCat.{u}
  body: Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans
          (Equiv.trans (FreeGroup.lift.symm) TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        -- Porting note (https://github.com/leanprover-community/mathlib4

中文:
定义 adj
  签名: : free ⊣ forget 群范畴.{u}
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans
          (Equiv.trans (FreeGroup.lift.symm) TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        -- Porting note (https://github.com/leanprover-community/mathlib4

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, ConcreteCategory, ConcreteCategory.homEquiv.trans, Equiv.trans, FreeGroup, FreeGroup.lift.symm, TypeCat, TypeCat.homEquiv.symm, homEquiv, homEquiv_naturality_left_symm, intros, mkOfHomEquiv
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget GrpCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: (forget 群范畴.{u}).是右伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : (forget GrpCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

section Abelianization

/--
Definition of `abelianize` / `abelianize` 的定义

English:
definition abelianize
  signature: : GrpCat.{u} ⥤ CommGrpCat.{u} where
  body: CommGrpCat.of (Abelianization G)
  map f := CommGrpCat.ofHom (Abelianization.lift (Abelianization.of.comp f.hom))
  map_id := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization.lift).mp
    rfl
  map_comp := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization

中文:
定义 abelianize
  签名: : 群范畴.{u} ⥤ 交换群范畴.{u} where
  定义体: CommGrpCat.of (Abelianization G)
  map f := CommGrpCat.ofHom (Abelianization.lift (Abelianization.of.comp f.hom))
  map_id := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization.lift).mp
    rfl
  map_comp := by
    intros
    ext : 1
    apply (Equiv.eq_symm_apply Abelianization

Depends on / 依赖: Abelianization, CommGrpCat, CommGrpCat.of
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

/--
Definition of `abelianizeAdj` / `abelianizeAdj` 的定义

English:
definition abelianizeAdj
  signature: : abelianize ⊣ forget₂ CommGrpCat.{u} GrpCat.{u}
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ((ConcreteCategory.homEquiv (C := CommGrpCat)).trans
        Abelianization.lift.symm).trans
        (ConcreteCategory.homEquiv (C := GrpCat)).symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be j

中文:
定义 abelianizeAdj
  签名: : abelianize ⊣ forget₂ 交换群范畴.{u} 群范畴.{u}
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ((ConcreteCategory.homEquiv (C := CommGrpCat)).trans
        Abelianization.lift.symm).trans
        (ConcreteCategory.homEquiv (C := GrpCat)).symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be j

Depends on / 依赖: Abelianization, Abelianization.lift.symm, Adjunction, Adjunction.mkOfHomEquiv, CommGrpCat, ConcreteCategory, ConcreteCategory.homEquiv, GrpCat, homEquiv, mkOfHomEquiv
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
/--
Definition of `MonCat.units` / `MonCat.units` 的定义

English:
definition MonCat.units
  signature: : MonCat.{u} ⥤ GrpCat.{u} where
  body: GrpCat.of Rˣ
map f := GrpCat.ofHom Units.map f.hom
  map_id _ := GrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := GrpCat.ext fun _ => Units.ext rfl

中文:
定义 幺半群范畴.units
  签名: : 幺半群范畴.{u} ⥤ 群范畴.{u} where
  定义体: GrpCat.of Rˣ
map f := GrpCat.ofHom Units.map f.hom
  map_id _ := GrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := GrpCat.ext fun _ => Units.ext rfl

Depends on / 依赖: GrpCat, GrpCat.of
-/
def MonCat.units : MonCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of Rˣ
map f := GrpCat.ofHom Units.map f.hom
  map_id _ := GrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := GrpCat.ext fun _ => Units.ext rfl

/--
Definition of `GrpCat.forget₂MonAdj` / `GrpCat.forget₂MonAdj` 的定义

English:
definition GrpCat.forget₂MonAdj
  signature: : forget₂ GrpCat MonCat ⊣ MonCat.units.{u}
  body: Adjunction.mk' {
  homEquiv _ Y :=
    { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
      invFun f := MonCat.ofHom ((Units.coeHom Y).comp f.hom) }
  unit :=
    { app X := ofHom (@toUnits X _)
      naturality _ _ _ := GrpCat.ext fun _ => Units.ext rfl }
  counit :=
    { app X := MonCat.ofHom (U

中文:
定义 群范畴.forget₂MonAdj
  签名: : forget₂ 群范畴 幺半群范畴 ⊣ 幺半群范畴.units.{u}
  定义体: Adjunction.mk' {
  homEquiv _ Y :=
    { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
      invFun f := MonCat.ofHom ((Units.coeHom Y).comp f.hom) }
  unit :=
    { app X := ofHom (@toUnits X _)
      naturality _ _ _ := GrpCat.ext fun _ => Units.ext rfl }
  counit :=
    { app X := MonCat.ofHom (U

Depends on / 依赖: Adjunction, Adjunction.mk
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonCat.units.{u}.IsRightAdjoint
  body: ⟨_, ⟨GrpCat.forget₂MonAdj⟩⟩

中文:
实例 :
  签名: 幺半群范畴.units.{u}.是右伴随
  定义体: ⟨_, ⟨GrpCat.forget₂MonAdj⟩⟩

Depends on / 依赖: GrpCat, GrpCat.forget
-/
instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨GrpCat.forget₂MonAdj⟩⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps!]
/--
Definition of `CommMonCat.units` / `CommMonCat.units` 的定义

English:
definition CommMonCat.units
  signature: : CommMonCat.{u} ⥤ CommGrpCat.{u} where
  body: CommGrpCat.of Rˣ
map f := CommGrpCat.ofHom Units.map f.hom
  map_id _ := CommGrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := CommGrpCat.ext fun _ => Units.ext rfl

中文:
定义 交换幺半群范畴.units
  签名: : 交换幺半群范畴.{u} ⥤ 交换群范畴.{u} where
  定义体: CommGrpCat.of Rˣ
map f := CommGrpCat.ofHom Units.map f.hom
  map_id _ := CommGrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := CommGrpCat.ext fun _ => Units.ext rfl

Depends on / 依赖: CommGrpCat, CommGrpCat.of
-/
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrpCat.{u} where
  obj R := CommGrpCat.of Rˣ
map f := CommGrpCat.ofHom Units.map f.hom
  map_id _ := CommGrpCat.ext fun _ => Units.ext rfl
  map_comp _ _ := CommGrpCat.ext fun _ => Units.ext rfl

/--
Definition of `CommGrpCat.forget₂CommMonAdj` / `CommGrpCat.forget₂CommMonAdj` 的定义

English:
definition CommGrpCat.forget₂CommMonAdj
  signature: : forget₂ CommGrpCat CommMonCat ⊣ CommMonCat.units.{u}
  body: Adjunction.mk' {
    homEquiv := fun _ Y =>
      { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
        invFun f := CommMonCat.ofHom ((Units.coeHom Y).comp f.hom) }
    unit.app X := ofHom toUnits.toMonoidHom
    -- `aesop` can find the following proof but it takes `0.5`s.
    unit.naturality _ _ 

中文:
定义 交换群范畴.forget₂CommMonAdj
  签名: : forget₂ 交换群范畴 交换幺半群范畴 ⊣ 交换幺半群范畴.units.{u}
  定义体: Adjunction.mk' {
    homEquiv := fun _ Y =>
      { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
        invFun f := CommMonCat.ofHom ((Units.coeHom Y).comp f.hom) }
    unit.app X := ofHom toUnits.toMonoidHom
    -- `aesop` can find the following proof but it takes `0.5`s.
    unit.naturality _ _ 

Depends on / 依赖: Adjunction, Adjunction.mk, CommMonCat, CommMonCat.ofHom, MonoidHom, MonoidHom.toHomUnits, Units.coeHom, coeHom, f.hom, homEquiv, invFun, toHomUnits, toMonoidHom, toUnits, toUnits.toMonoidHom, unit.app
-/
def CommGrpCat.forget₂CommMonAdj : forget₂ CommGrpCat CommMonCat ⊣ CommMonCat.units.{u} :=
  Adjunction.mk' {
    homEquiv := fun _ Y =>
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonCat.units.{u}.IsRightAdjoint
  body: ⟨_, ⟨CommGrpCat.forget₂CommMonAdj⟩⟩

中文:
实例 :
  签名: 交换幺半群范畴.units.{u}.是右伴随
  定义体: ⟨_, ⟨CommGrpCat.forget₂CommMonAdj⟩⟩

Depends on / 依赖: CommGrpCat, CommGrpCat.forget
-/
instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGrpCat.forget₂CommMonAdj⟩⟩
