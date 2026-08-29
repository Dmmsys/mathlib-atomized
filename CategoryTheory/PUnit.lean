/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Data.ULift

/-!
# The category `Discrete PUnit`

We define `star : C ⥤ Discrete PUnit` sending everything to `PUnit.star`,
show that any two functors to `Discrete PUnit` are naturally isomorphic,
and construct the equivalence `(Discrete PUnit ⥤ C) ≌ C`.
-/

@[expose] public section

universe w v u

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace Functor

/-- The constant functor sending everything to `PUnit.star`. -/
@[simps!]
/--
Definition of `star` / `star` 的定义

English:
definition star
  signature: : C ⥤ Discrete PUnit.{w + 1}
  body: (Functor.const _).obj ⟨⟨⟩⟩

中文:
定义 star
  签名: : C ⥤ 离散 命题单元.{w + 1}
  定义体: (Functor.const _).obj ⟨⟨⟩⟩

Depends on / 依赖: Functor, Functor.const, variable
-/
def star : C ⥤ Discrete PUnit.{w + 1} :=
  (Functor.const _).obj ⟨⟨⟩⟩
variable {C}

/-- Any two functors to `Discrete PUnit` are isomorphic. -/
@[simps!]
/--
Definition of `punitExt` / `punitExt` 的定义

English:
definition punitExt
  signature: (F G : C ⥤ Discrete PUnit.{w + 1})
  body: NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])

中文:
定义 punitExt
  签名: (F G : C ⥤ 离散 命题单元.{w + 1})
  定义体: NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, eq_iff_true_of_subsingleton, ofComponents
-/
def punitExt (F G : C ⥤ Discrete PUnit.{w + 1}) : F ≅ G :=
  NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])

/--
theorem `punit_ext'` / 定理 `punit_ext'`

English:
theorem punit_ext'
  given: (F G : C ⥤ Discrete PUnit.{w + 1})
  statement: F = G
  proof: Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]

中文:
定理 punit_ext'
  条件: (F G : C ⥤ 离散 命题单元.{w + 1})
  结论: F = G
  证明: Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]

Depends on / 依赖: Functor, Functor.ext, eq_iff_true_of_subsingleton
-/
theorem punit_ext' (F G : C ⥤ Discrete PUnit.{w + 1}) : F = G :=
  Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]

/--
Definition of `fromPUnit` / `fromPUnit` 的定义

English:
abbreviation fromPUnit
  signature: (X : C)
  body: (Functor.const _).obj X

中文:
缩写 fromPUnit
  签名: (X : C)
  定义体: (Functor.const _).obj X

Depends on / 依赖: Functor, Functor.const
-/
abbrev fromPUnit (X : C) : Discrete PUnit.{w + 1} ⥤ C :=
  (Functor.const _).obj X

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functors from `Discrete PUnit` are equivalent to the category itself. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : Discrete PUnit.{w + 1} ⥤ C ≌ C where
  body: { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := NatIso.ofComponents fun _ => Discrete.natIso fun _ => Iso.refl _
  counitIso := NatIso.ofComponents Iso.refl

中文:
定义 equiv
  签名: : 离散 命题单元.{w + 1} ⥤ C ≌ C where
  定义体: { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := NatIso.ofComponents fun _ => Discrete.natIso fun _ => Iso.refl _
  counitIso := NatIso.ofComponents Iso.refl

Depends on / 依赖: Discrete, Discrete.natIso, F.obj, Functor, Functor.const, Iso.refl, NatIso, NatIso.ofComponents, counitIso, inverse, natIso, ofComponents, unitIso
-/
def equiv : Discrete PUnit.{w + 1} ⥤ C ≌ C where
  functor :=
    { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := NatIso.ofComponents fun _ => Discrete.natIso fun _ => Iso.refl _
  counitIso := NatIso.ofComponents Iso.refl

end Functor

set_option backward.defeqAttrib.useBackward true in
/--
theorem `equiv_punit_iff_unique` / 定理 `equiv_punit_iff_unique`

English:
theorem equiv_punit_iff_unique
  proof: by
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro ?_⟩
    let f : x ⟶ y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert! h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert! h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subs

中文:
定理 equiv_punit_iff_unique
  证明: by
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro ?_⟩
    let f : x ⟶ y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert! h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert! h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subs

Depends on / 依赖: Functor, Functor.comp_map, Nonempty, Nonempty.intro, Subsingleton, Subsingleton.intro, comp_map, convert, functor, h.functor, h.inverse, h.inverse.obj, h.unit.app, h.unitInv.app, inverse, uniqueOfSubsingleton, unitInv
-/
theorem equiv_punit_iff_unique :
Nonempty (C ≌ Discrete PUnit.{w + 1}) ↔ Nonempty C ∧ forall x y : C, Nonempty Unique (x ⟶ y) := by
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro ?_⟩
    let f : x ⟶ y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert! h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert! h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subsingleton (x ⟶ y) from uniqueOfSubsingleton f
    have : forall z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unitInv.app y := by
      simp
    apply Subsingleton.intro
    intro a b
    rw [this a]; rw [this b]
    simp only [Functor.comp_map]
    congr 3
    apply ULift.ext
    simp [eq_iff_true_of_subsingleton]
  · rintro ⟨⟨p⟩, h⟩
    have := fun x y => (h x y).some
    refine
      Nonempty.intro
        (CategoryTheory.Equivalence.mk ((Functor.const _).obj ⟨⟨⟩⟩)
          ((@Functor.const <| Discrete PUnit).obj p) ?_ (by apply Functor.punitExt))
    exact
      NatIso.ofComponents fun _ =>
        { hom := default
          inv := default }

end CategoryTheory
