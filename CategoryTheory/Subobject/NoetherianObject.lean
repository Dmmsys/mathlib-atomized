/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects

We shall say that an object `X` in a category `C` is Noetherian
(type class `IsNoetherianObject X`) if the ordered type `Subobject X`
satisfies the ascending chain condition. The corresponding property of
objects `isNoetherianObject : ObjectProperty C` is always
closed under subobjects.

## Future works

* show that `isNoetherian` is a Serre class when `C` is an abelian category
  (TODO @joelriou)

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Noetherian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsNoetherianObject` instead. -/
@[stacks 0FCG]
/--
Definition of `isNoetherianObject` / `isNoetherianObject` 的定义

English:
definition isNoetherianObject
  signature: : ObjectProperty C
  body: fun X => WellFoundedGT (Subobject X)

中文:
定义 isNoetherianObject
  签名: : ObjectProperty C
  定义体: fun X => WellFoundedGT (Subobject X)

Depends on / 依赖: Subobject, WellFoundedGT
-/
def isNoetherianObject : ObjectProperty C :=
  fun X => WellFoundedGT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. -/
@[stacks 0FCG]
/--
Definition of `IsNoetherianObject` / `IsNoetherianObject` 的定义

English:
abbreviation IsNoetherianObject
  signature: : Prop
  body: isNoetherianObject.Is X

中文:
缩写 IsNoetherianObject
  签名: : 命题
  定义体: isNoetherianObject.Is X

Depends on / 依赖: isNoetherianObject, isNoetherianObject.Is
-/
abbrev IsNoetherianObject : Prop := isNoetherianObject.Is X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianObject
  signature: X] : WellFoundedGT (Subobject X)
  body: isNoetherianObject.prop_of_is X

中文:
实例 [IsNoetherianObject
  签名: X] : WellFoundedGT (Subobject X)
  定义体: isNoetherianObject.prop_of_is X

Depends on / 依赖: isNoetherianObject, isNoetherianObject.prop_of_is, prop_of_is
-/
instance [IsNoetherianObject X] : WellFoundedGT (Subobject X) :=
  isNoetherianObject.prop_of_is X

/--
lemma `isNoetherianObject_iff_monotone_chain_condition` / 引理 `isNoetherianObject_iff_monotone_chain_condition`

English:
lemma isNoetherianObject_iff_monotone_chain_condition
  proof: by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [wellFoundedGT_iff_monotone_chain_condition]

中文:
引理 isNoetherianObject_iff_monotone_chain_condition
  证明: by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [wellFoundedGT_iff_monotone_chain_condition]

Depends on / 依赖: IsNoetherianObject, ObjectProperty, ObjectProperty.is_iff, isNoetherianObject, is_iff, wellFoundedGT_iff_monotone_chain_condition
-/
lemma isNoetherianObject_iff_monotone_chain_condition :
    IsNoetherianObject X ↔ forall (f : Nat ->o Subobject X),
      exists (n : Nat), forall (m : Nat), n <= m -> f n = f m := by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
/--
lemma `monotone_chain_condition_of_isNoetherianObject` / 引理 `monotone_chain_condition_of_isNoetherianObject`

English:
lemma monotone_chain_condition_of_isNoetherianObject
  proof: (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f

中文:
引理 monotone_chain_condition_of_isNoetherianObject
  证明: (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f

Depends on / 依赖: isNoetherianObject_iff_monotone_chain_condition
-/
lemma monotone_chain_condition_of_isNoetherianObject
    [IsNoetherianObject X] (f : Nat ->o Subobject X) :
    exists (n : Nat), forall (m : Nat), n <= m -> f n = f m :=
  (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f

/--
lemma `isNoetherianObject_iff_not_strictMono` / 引理 `isNoetherianObject_iff_not_strictMono`

English:
lemma isNoetherianObject_iff_not_strictMono
  proof: by
  refine ⟨fun _ => not_strictMono_of_wellFoundedGT, fun h => ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [WellFoundedGT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2

中文:
引理 isNoetherianObject_iff_not_strictMono
  证明: by
  refine ⟨fun _ => not_strictMono_of_wellFoundedGT, fun h => ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [WellFoundedGT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2

Depends on / 依赖: IsNoetherianObject, ObjectProperty, ObjectProperty.is_iff, RelEmbedding, RelEmbedding.wellFounded_iff_isEmpty, WellFoundedGT, f.map_rel_iff, f.toFun, isNoetherianObject, isWellFounded_iff, is_iff, map_rel_iff, not_strictMono_of_wellFoundedGT, wellFounded_iff_isEmpty
-/
lemma isNoetherianObject_iff_not_strictMono :
    IsNoetherianObject X ↔ forall (f : Nat -> Subobject X), ¬ StrictMono f := by
  refine ⟨fun _ => not_strictMono_of_wellFoundedGT, fun h => ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff]; rw [isNoetherianObject]; rw [WellFoundedGT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2 h)⟩

variable {X} in
/--
lemma `not_strictMono_of_isNoetherianObject` / 引理 `not_strictMono_of_isNoetherianObject`

English:
lemma not_strictMono_of_isNoetherianObject
  proof: (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

中文:
引理 not_strictMono_of_isNoetherianObject
  证明: (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

Depends on / 依赖: isNoetherianObject_iff_not_strictMono
-/
lemma not_strictMono_of_isNoetherianObject
    [IsNoetherianObject X] (f : Nat -> Subobject X) :
    ¬ StrictMono f :=
  (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isNoetherianObject_iff_isEventuallyConstant` / 引理 `isNoetherianObject_iff_isEventuallyConstant`

English:
lemma isNoetherianObject_iff_isEventuallyConstant
  proof: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h (G ⋙ (Subobject.equivMonoOver _).inverse).toOrderHom
    refine ⟨n, fun m hm => ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · obtain ⟨n, hn⟩ := h

中文:
引理 isNoetherianObject_iff_isEventuallyConstant
  证明: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h (G ⋙ (Subobject.equivMonoOver _).inverse).toOrderHom
    refine ⟨n, fun m hm => ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · obtain ⟨n, hn⟩ := h

Depends on / 依赖: F.monotone.functor, MonoOver, MonoOver.isIso_iff_isIso_hom_left, MonoOver.isIso_iff_subobjectMk_eq, PartialOrder, PartialOrder.isIso_iff_eq, Subobject, Subobject.equivMonoOver, Subobject.representative, equivMonoOver, functor, homOfLE, inverse, isIso_iff_eq, isIso_iff_isIso_hom_left, isIso_iff_of_reflects_iso, isIso_iff_subobjectMk_eq, isNoetherianObject_iff_monotone_chain_condition, leOfHom, monotone
-/
lemma isNoetherianObject_iff_isEventuallyConstant :
    IsNoetherianObject X ↔ forall (F : Nat ⥤ MonoOver X),
      IsFiltered.IsEventuallyConstant F := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h (G ⋙ (Subobject.equivMonoOver _).inverse).toOrderHom
    refine ⟨n, fun m hm => ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ Subobject.representative)
    refine ⟨n, fun m hm => ?_⟩
    simpa [← MonoOver.isIso_iff_isIso_hom_left, isIso_iff_of_reflects_iso,
      PartialOrder.isIso_iff_eq] using hn (homOfLE hm)

variable {X} in
/--
lemma `isEventuallyConstant_of_isNoetherianObject` / 引理 `isEventuallyConstant_of_isNoetherianObject`

English:
lemma isEventuallyConstant_of_isNoetherianObject
  statement: [IsNoetherianObject X]
  proof: (isNoetherianObject_iff_isEventuallyConstant X).1 inferInstance F

中文:
引理 isEventuallyConstant_of_isNoetherianObject
  结论: [IsNoetherianObject X]
  证明: (isNoetherianObject_iff_isEventuallyConstant X).1 inferInstance F

Depends on / 依赖: isNoetherianObject_iff_isEventuallyConstant
-/
lemma isEventuallyConstant_of_isNoetherianObject [IsNoetherianObject X]
    (F : Nat ⥤ MonoOver X) : IsFiltered.IsEventuallyConstant F :=
  (isNoetherianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}

/--
lemma `isNoetherianObject_of_isZero` / 引理 `isNoetherianObject_of_isZero`

English:
lemma isNoetherianObject_of_isZero
  given: (hX : IsZero X)
  statement: IsNoetherianObject X
  proof: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

中文:
引理 isNoetherianObject_of_isZero
  条件: (hX : 是零 X)
  结论: IsNoetherianObject X
  证明: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

Depends on / 依赖: Subobject, Subobject.subsingleton_of_isZero, Subsingleton, Subsingleton.elim, isNoetherianObject_iff_monotone_chain_condition, subsingleton_of_isZero
-/
lemma isNoetherianObject_of_isZero (hX : IsZero X) : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : (isNoetherianObject (C := C)).ContainsZero where
  body: ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩

中文:
实例 [有ZeroObject
  签名: C] : (isNoetherianObject (C := C)).余ntainsZero where
  定义体: ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩

Depends on / 依赖: ContainsZero
-/
instance [HasZeroObject C] : (isNoetherianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩

/--
lemma `isNoetherianObject_of_mono` / 引理 `isNoetherianObject_of_mono`

English:
lemma isNoetherianObject_of_mono
  given: (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y]
  proof: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

中文:
引理 isNoetherianObject_of_mono
  条件: (i : X ⟶ Y) [单态射 i] [IsNoetherianObject Y]
  证明: by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

Depends on / 依赖: Subobject, Subobject.map, Subobject.map_obj_injective, isNoetherianObject_iff_monotone_chain_condition, map_obj_injective, monotone, monotone.comp, monotone_chain_condition_of_isNoetherianObject
-/
lemma isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isNoetherianObject (C := C)).IsClosedUnderSubobjects
  body: by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

中文:
实例 :
  签名: (isNoetherianObject (C := C)).是ClosedUnderSubobjects
  定义体: by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

Depends on / 依赖: IsClosedUnderSubobjects
-/
instance : (isNoetherianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

end CategoryTheory
