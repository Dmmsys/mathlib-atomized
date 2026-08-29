/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `Quiver.FreeGroupoid V`: a type synonym for `V`.
- `Quiver.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `Quiver.FreeGroupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `Quiver.FreeGroupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/

@[expose] public section

open Set Function

namespace Quiver

open CategoryTheory

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v} V]

/--
Definition of `Hom.toPosPath` / `Hom.toPosPath` 的定义

English:
abbreviation Hom.toPosPath
  signature: {X Y : V} (f : X ⟶ Y)
  body: f.toPos.toPath

中文:
缩写 态射.toPosPath
  签名: {X Y : V} (f : X ⟶ Y)
  定义体: f.toPos.toPath

Depends on / 依赖: f.toPos.toPath, toPath
-/
abbrev Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath

/--
Definition of `Hom.toNegPath` / `Hom.toNegPath` 的定义

English:
abbreviation Hom.toNegPath
  signature: {X Y : V} (f : X ⟶ Y)
  body: f.toNeg.toPath

中文:
缩写 态射.toNegPath
  签名: {X Y : V} (f : X ⟶ Y)
  定义体: f.toNeg.toPath

Depends on / 依赖: f.toNeg.toPath, toPath
-/
abbrev Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath

/--
Inductive type `FreeGroupoid.redStep` / 归纳类型 `FreeGroupoid.redStep`

English:
inductive FreeGroupoid.redStep
  parameters: : HomRel (Paths (Quiver.Symmetrify V))
  constructors (1):
    - step: (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) : redStep (𝟙 ((Paths.of (Quiver.Symmetrify V)).obj X)) (f.toPath ≫ (Quiver.reverse f).toPath)

中文:
归纳类型 FreeGroupoid.redStep
  参数: : HomRel (Paths (箭图.Symmetrify V))
  构造子 (1 个):
    - step: (X Z : 箭图.Symmetrify V) (f : X ⟶ Z) : redStep (𝟙 ((Paths.of (箭图.Symmetrify V)).obj X)) (f.toPath ≫ (箭图.reverse f).toPath)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, FreeGroupoid, FreeGroupoid.redStep, Quotient, redStep
-/
inductive FreeGroupoid.redStep : HomRel (Paths (Quiver.Symmetrify V))
  | step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) :
    redStep (𝟙 ((Paths.of (Quiver.Symmetrify V)).obj X)) (f.toPath ≫ (Quiver.reverse f).toPath)

/--
Definition of `FreeGroupoid` / `FreeGroupoid` 的定义

English:
definition FreeGroupoid
  signature: (V) [Q : Quiver V]
  body: CategoryTheory.Quotient (@FreeGroupoid.redStep V Q)

中文:
定义 FreeGroupoid
  签名: (V) [Q : 箭图 V]
  定义体: CategoryTheory.Quotient (@FreeGroupoid.redStep V Q)
-/
protected def FreeGroupoid (V) [Q : Quiver V] :=
  CategoryTheory.Quotient (@FreeGroupoid.redStep V Q)

namespace FreeGroupoid

open Quiver

instance {V} [Quiver V] [Nonempty V] : Nonempty (Quiver.FreeGroupoid V) := by
  inhabit V; exact ⟨⟨@default V _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `congr_reverse` / 定理 `congr_reverse`

English:
theorem congr_reverse
  given: {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y)
  proof: by
  rintro ⟨_, _, XW, _, _, WY, _, _, f⟩
  have : HomRel.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this

中文:
定理 congr_reverse
  条件: {X Y : Paths <| 箭图.Symmetrify V} (p q : X ⟶ Y)
  证明: by
  rintro ⟨_, _, XW, _, _, WY, _, _, f⟩
  have : HomRel.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, CategoryStruct.id, CompClosure, HomRel, HomRel.CompClosure, Quiver, Quiver.Path.comp_assoc, Quiver.Path.nil_comp, Quiver.Path.reverse, Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath, Quiver.reverse, Quiver.reverse_reverse, WY.reverse, XW.reverse, comp_assoc, f.toPath, nil_comp, redStep
-/
theorem congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    HomRel.CompClosure redStep p q -> HomRel.CompClosure redStep p.reverse q.reverse := by
  rintro ⟨_, _, XW, _, _, WY, _, _, f⟩
  have : HomRel.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this

set_option backward.isDefEq.respectTransparency.types false in
open Relation in
/--
theorem `congr_comp_reverse` / 定理 `congr_comp_reverse`

English:
theorem congr_comp_reverse
  given: {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y)
  proof: by
  apply Quot.eqvGen_sound
  induction p with
  | nil => apply EqvGen.refl
  | cons q f ih =>
    simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: dot notation for `Quiver.Path.*` and `Quiver.Hom.*` not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : HomRel.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply HomRel.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change HomRel.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih

中文:
定理 congr_comp_reverse
  条件: {X Y : Paths <| 箭图.Symmetrify V} (p : X ⟶ Y)
  证明: by
  apply Quot.eqvGen_sound
  induction p with
  | nil => apply EqvGen.refl
  | cons q f ih =>
    simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: dot notation for `Quiver.Path.*` and `Quiver.Hom.*` not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : HomRel.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply HomRel.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change HomRel.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih

Depends on / 依赖: EqvGen, EqvGen.refl, EqvGen.trans, Quiver, Quiver.Path.reverse, Quot.eqvGen_sound, eqvGen_sound, fapply, reverse
-/
theorem congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p ≫ p.reverse) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 X) := by
  apply Quot.eqvGen_sound
  induction p with
  | nil => apply EqvGen.refl
  | cons q f ih =>
    simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: dot notation for `Quiver.Path.*` and `Quiver.Hom.*` not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : HomRel.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply HomRel.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change HomRel.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih

/--
theorem `congr_reverse_comp` / 定理 `congr_reverse_comp`

English:
theorem congr_reverse_comp
  given: {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y)
  proof: by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse

中文:
定理 congr_reverse_comp
  条件: {X Y : Paths <| 箭图.Symmetrify V} (p : X ⟶ Y)
  证明: by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse

Depends on / 依赖: Quiver, Quiver.Path.reverse_reverse, congr_comp_reverse, nth_rw, reverse_reverse
-/
theorem congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p.reverse ≫ p) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 Y) := by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Quiver.FreeGroupoid V)
  body: Quotient.category redStep

中文:
实例 :
  签名: 范畴 (箭图.FreeGroupoid V)
  定义体: Quotient.category redStep

Depends on / 依赖: Quotient, Quotient.category, category, redStep
-/
instance : Category (Quiver.FreeGroupoid V) :=
  Quotient.category redStep

/--
Definition of `quotInv` / `quotInv` 的定义

English:
definition quotInv
  signature: {X Y : Quiver.FreeGroupoid V} (f : X ⟶ Y)
  body: Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
Quot.sound congr_reverse pp qq con

中文:
定义 quotInv
  签名: {X Y : 箭图.FreeGroupoid V} (f : X ⟶ Y)
  定义体: Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
Quot.sound congr_reverse pp qq con

Depends on / 依赖: Quot.liftOn, Quot.mk, Quot.sound, congr_reverse, liftOn, pp.reverse, reverse
-/
def quotInv {X Y : Quiver.FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
Quot.sound congr_reverse pp qq con

/--
Instance `instGroupoid` / 实例 `instGroupoid`

English:
instance instGroupoid
  signature: : Groupoid (Quiver.FreeGroupoid V) where
  body: quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp

中文:
实例 instGroupoid
  签名: : 群胚 (箭图.FreeGroupoid V) where
  定义体: quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp

Depends on / 依赖: quotInv
-/
instance instGroupoid : Groupoid (Quiver.FreeGroupoid V) where
  inv := quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (V) [Quiver V]
  body: ⟨X⟩
  map f := Quot.mk _ f.toPosPath

中文:
定义 of
  签名: (V) [箭图 V]
  定义体: ⟨X⟩
  map f := Quot.mk _ f.toPosPath
-/
def of (V) [Quiver V] : V ⥤q Quiver.FreeGroupoid V where
  obj X := ⟨X⟩
  map f := Quot.mk _ f.toPosPath

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  proof: rfl

中文:
定理 of_eq
  证明: rfl
-/
theorem of_eq :
    of V = (Quiver.Symmetrify.of ⋙q (Paths.of (Quiver.Symmetrify V))).comp
      (Quotient.functor <| @redStep V _).toPrefunctor := rfl

section UniversalProperty

variable {V' : Type u'} [Groupoid V']

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (φ : V ⥤q V')
  body: CategoryTheory.Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv

中文:
定义 lift
  签名: (φ : V ⥤q V')
  定义体: CategoryTheory.Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, Paths.lift, Quiver, Quiver.Symmetrify.lift, Quotient, Symmetrify
-/
def lift (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ V' :=
CategoryTheory.Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  given: (φ : V ⥤q V')
  statement: of V ⋙q (lift φ).toPrefunctor = φ
  proof: by
  rw [of_eq]; rw [Prefunctor.comp_assoc]; rw [Prefunctor.comp_assoc]; rw [Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec]; rw [Paths.lift_spec]; rw [Quiver.Symmetrify.lift_spec]

中文:
定理 lift_spec
  条件: (φ : V ⥤q V')
  结论: of V ⋙q (lift φ).toPrefunctor = φ
  证明: by
  rw [of_eq]; rw [Prefunctor.comp_assoc]; rw [Prefunctor.comp_assoc]; rw [Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec]; rw [Paths.lift_spec]; rw [Quiver.Symmetrify.lift_spec]

Depends on / 依赖: Functor, Functor.toPrefunctor_comp, Paths.lift_spec, Prefunctor, Prefunctor.comp_assoc, Quiver, Quiver.Symmetrify.lift_spec, Quotient, Quotient.lift_spec, Symmetrify, comp_assoc, lift_spec, of_eq, toPrefunctor_comp
-/
theorem lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ := by
  rw [of_eq]; rw [Prefunctor.comp_assoc]; rw [Prefunctor.comp_assoc]; rw [Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec]; rw [Paths.lift_spec]; rw [Quiver.Symmetrify.lift_spec]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (φ : V ⥤q V') (Φ : Quiver.FreeGroupoid V ⥤ V')
  proof: by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map]
    change Φ.map (Groupoid.inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      Groupoid.inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert! this <;> simp only [Groupoid.inv_eq_inv]

中文:
定理 lift_unique
  结论: (φ : V ⥤q V') (Φ : 箭图.FreeGroupoid V ⥤ V')
  证明: by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map]
    change Φ.map (Groupoid.inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      Groupoid.inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert! this <;> simp only [Groupoid.inv_eq_inv]

Depends on / 依赖: Functor, Functor.map_inv, Functor.toPrefunctor_comp, Groupoid, Groupoid.inv, Paths.lift_unique, Paths.of_map, Prefunctor, Prefunctor.comp_map, Quiver, Quiver.Symmetrify.lift_unique, Quotient, Quotient.functor, Quotient.lift_unique, Symmetrify, comp_map, convert, f.toPath, fapply, functor
-/
theorem lift_unique (φ : V ⥤q V') (Φ : Quiver.FreeGroupoid V ⥤ V')
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map]
    change Φ.map (Groupoid.inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      Groupoid.inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert! this <;> simp only [Groupoid.inv_eq_inv]

end UniversalProperty

end FreeGroupoid

section Functoriality

open FreeGroupoid

variable {V' : Type u'} [Quiver.{v'} V'] {V'' : Type u''} [Quiver.{v''} V'']

/--
Definition of `freeGroupoidFunctor` / `freeGroupoidFunctor` 的定义

English:
definition freeGroupoidFunctor
  signature: (φ : V ⥤q V')
  body: lift (φ ⋙q of V')

中文:
定义 freeGroupoidFunctor
  签名: (φ : V ⥤q V')
  定义体: lift (φ ⋙q of V')
-/
def freeGroupoidFunctor (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ Quiver.FreeGroupoid V' :=
  lift (φ ⋙q of V')

/--
theorem `freeGroupoidFunctor_id` / 定理 `freeGroupoidFunctor_id`

English:
theorem freeGroupoidFunctor_id
  proof: by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

中文:
定理 freeGroupoidFunctor_id
  证明: by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

Depends on / 依赖: freeGroupoidFunctor, lift_unique
-/
theorem freeGroupoidFunctor_id :
    freeGroupoidFunctor (Prefunctor.id V) = Functor.id (Quiver.FreeGroupoid V) := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

/--
theorem `freeGroupoidFunctor_comp` / 定理 `freeGroupoidFunctor_comp`

English:
theorem freeGroupoidFunctor_comp
  given: (φ : V ⥤q V') (φ' : V' ⥤q V'')
  proof: by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

中文:
定理 freeGroupoidFunctor_comp
  条件: (φ : V ⥤q V') (φ' : V' ⥤q V'')
  证明: by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

Depends on / 依赖: freeGroupoidFunctor, lift_unique
-/
theorem freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') :
    freeGroupoidFunctor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ' := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

end Functoriality

end Quiver
