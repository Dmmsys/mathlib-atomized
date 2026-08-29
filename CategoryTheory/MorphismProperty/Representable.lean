/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Relatively representable morphisms

In this file we define and develop basic results about relatively representable morphisms.

Classically, a morphism `f : F ⟶ G` of presheaves is said to be representable if for any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square of the following form
```
  yoneda.obj Y --yoneda.map snd--> yoneda.obj X
      | |
     fst g
      | |
      v v
      F ------------ f --------------> G
```

In this file, we define a notion of relative representability which works with respect to any
functor, and not just `yoneda`. The fact that a morphism `f : F ⟶ G` between presheaves is
representable in the classical case will then be given by `yoneda.relativelyRepresentable f`.

## Main definitions

Throughout this file, `F : C ⥤ D` is a functor between categories `C` and `D`.

* `Functor.relativelyRepresentable`: A morphism `f : X ⟶ Y` in `D` is said to be relatively
  representable with respect to `F`, if for any `g : F.obj a ⟶ Y`, there exists a pullback square
  of the following form
  ```
  F.obj b --F.map snd--> F.obj a
      | |
     fst g
      | |
      v v
      X ------- f --------> Y
  ```

* `MorphismProperty.relative`: Given a morphism property `P` in `C`, a morphism `f : X ⟶ Y` in `D`
  satisfies `P.relative F` if it is relatively representable and for any `g : F.obj a ⟶ Y`, the
  property `P` holds for any represented pullback of `f` by `g`.

## API

Given `hf : relativelyRepresentable f`, with `f : X ⟶ Y` and `g : F.obj a ⟶ Y`, we provide:
* `hf.pullback g` which is the object in `C` such that `F.obj (hf.pullback g)` is a
  pullback of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ F.obj a`
* `hf.fst g` is the morphism `F.obj (hf.pullback g) ⟶ X`
* If `F` is full, and `f` is of type `F.obj c ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ X`
  which is the preimage under `F` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
  For these theorems we also need that `F` is full and/or faithful.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`. We assume that `F` is fully faithful here.

We also provide some basic API for dealing with triple pullbacks, i.e. given
`hf₁ : relativelyRepresentable f₁`, `f₂ : F.obj A₂ ⟶ X` and `f₃ : F.obj A₃ ⟶ X`, we define
`hf₁.pullback₃ f₂ f₃` to be the pullback of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. We then develop
some API for working with this object, mirroring the usual API for pullbacks, but where as much
as possible is phrased internally to `C`.

## Main results

* `relativelyRepresentable.isMultiplicative`: The class of relatively representable morphisms is
  multiplicative.
* `relativelyRepresentable.isStableUnderBaseChange`: Being relatively representable is stable under
  base change.
* `relativelyRepresentable.of_isIso`: Isomorphisms are relatively representable.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/--
Definition of `Functor.relativelyRepresentable` / `Functor.relativelyRepresentable` 的定义

English:
definition Functor.relativelyRepresentable
  signature: : MorphismProperty D
  body: fun X Y f => forall ⦃a : C⦄ (g : F.obj a ⟶ Y), exists (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

中文:
定义 Functor.relativelyRepresentable
  签名: : Morphism命题erty D
  定义体: fun X Y f => forall ⦃a : C⦄ (g : F.obj a ⟶ Y), exists (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

Depends on / 依赖: F.map, F.obj, IsPullback
-/
def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f => forall ⦃a : C⦄ (g : F.obj a ⟶ Y), exists (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

namespace Functor.relativelyRepresentable

section

variable {F}
variable {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: : C
  body: (hf g).choose

中文:
定义 pullback
  签名: : C
  定义体: (hf g).choose
-/
noncomputable def pullback : C :=
  (hf g).choose

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: : hf.pullback g ⟶ a
  body: (hf g).choose_spec.choose

中文:
缩写 snd
  签名: : hf.pullback g ⟶ a
  定义体: (hf g).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose
-/
noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: : F.obj (hf.pullback g) ⟶ X
  body: (hf g).choose_spec.choose_spec.choose

中文:
缩写 fst
  签名: : F.obj (hf.pullback g) ⟶ X
  定义体: (hf g).choose_spec.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose
-/
noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose

/--
Definition of `fst'` / `fst'` 的定义

English:
abbreviation fst'
  signature: [Full F]
  body: F.preimage (hf'.fst g)

中文:
缩写 fst'
  签名: [Full F]
  定义体: F.preimage (hf'.fst g)

Depends on / 依赖: F.preimage, preimage
-/
noncomputable abbrev fst' [Full F] : hf'.pullback g ⟶ b :=
  F.preimage (hf'.fst g)

/--
lemma `map_fst'` / 引理 `map_fst'`

English:
lemma map_fst'
  given: [Full F]
  statement: F.map (hf'.fst' g) = hf'.fst g
  proof: F.map_preimage _

中文:
引理 map_fst'
  条件: [Full F]
  结论: F.map (hf'.fst' g) = hf'.fst g
  证明: F.map_preimage _

Depends on / 依赖: F.map_preimage, map_preimage
-/
lemma map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g :=
  F.map_preimage _

/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  statement: IsPullback (hf.fst g) (F.map (hf.snd g)) f g
  proof: (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]

中文:
引理 isPullback
  结论: IsPullback (hf.fst g) (F.map (hf.snd g)) f g
  证明: (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec
-/
lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]
/--
lemma `w` / 引理 `w`

English:
lemma w
  statement: hf.fst g ≫ f = F.map (hf.snd g) ≫ g
  proof: (hf.isPullback g).w

中文:
引理 w
  结论: hf.fst g ≫ f = F.map (hf.snd g) ≫ g
  证明: (hf.isPullback g).w

Depends on / 依赖: hf.isPullback, isPullback
-/
lemma w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g := (hf.isPullback g).w

/--
lemma `isPullback'` / 引理 `isPullback'`

English:
lemma isPullback'
  given: [Full F]
  statement: IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g
  proof: (hf'.map_fst' _) ▸ hf'.isPullback g

@[reassoc]

中文:
引理 isPullback'
  条件: [Full F]
  结论: IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g
  证明: (hf'.map_fst' _) ▸ hf'.isPullback g

@[reassoc]

Depends on / 依赖: isPullback, map_fst
-/
lemma isPullback' [Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g :=
  (hf'.map_fst' _) ▸ hf'.isPullback g

@[reassoc]
/--
lemma `w'` / 引理 `w'`

English:
lemma w'
  statement: {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
  proof: F.map_injective by simp [(hf.w (F.map g))]

中文:
引理 w'
  结论: {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
  证明: F.map_injective by simp [(hf.w (F.map g))]

Depends on / 依赖: F.map, F.map_injective, hf.w, map_injective
-/
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
    [Full F] [Faithful F] : hf.fst' (F.map g) ≫ f = hf.snd (F.map g) ≫ g :=
F.map_injective by simp [(hf.w (F.map g))]

/--
lemma `isPullback_of_map` / 引理 `isPullback_of_map`

English:
lemma isPullback_of_map
  statement: {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
  proof: IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))

中文:
引理 isPullback_of_map
  结论: {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
  证明: IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))

Depends on / 依赖: F.map, IsPullback, IsPullback.of_map, hf.isPullback, hf.w, isPullback, of_map
-/
lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
    (g : Y ⟶ Z) [Full F] [Faithful F] :
    IsPullback (hf.fst' (F.map g)) (hf.snd (F.map g)) f g :=
  IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))

variable {g}

/-- Two morphisms `a b : c ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback ⟶ X` are equal.
* The compositions of `F.map a` and `F.map b` with `hf.fst g` are equal. -/
@[ext 100]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
  proof: F.map_injective
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using! F.congr_map h₂)

中文:
引理 hom_ext
  结论: [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
  证明: F.map_injective
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using! F.congr_map h₂)

Depends on / 依赖: F.congr_map, F.map_injective, IsLimit, PullbackCone, PullbackCone.IsLimit.hom_ext, congr_map, hf.isPullback, hom_ext, isLimit, isPullback, map_injective
-/
lemma hom_ext [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
    (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
F.map_injective
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using! F.congr_map h₂)

/-- In the case of a representable morphism `f' : F.obj Y ⟶ G`, whose codomain lies
in the image of `F`, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback ⟶ Y` are equal. -/
@[ext]
/--
lemma `hom_ext'` / 引理 `hom_ext'`

English:
lemma hom_ext'
  statement: [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
  proof: hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂

中文:
引理 hom_ext'
  结论: [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
  证明: hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂

Depends on / 依赖: F.congr_map, congr_map, hom_ext, map_fst
-/
lemma hom_ext' [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
    (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂

section

variable {c : C} (i : F.obj c ⟶ X) (h : c ⟶ a) (hi : i ≫ f = F.map h ≫ g)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [Full F]
  body: F.preimage PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

中文:
定义 lift
  签名: [Full F]
  定义体: F.preimage PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

Depends on / 依赖: F.preimage, IsLimit, PullbackCone, PullbackCone.IsLimit.lift, hf.isPullback, isLimit, isPullback, preimage
-/
noncomputable def lift [Full F] : c ⟶ hf.pullback g :=
F.preimage PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  given: [Full F]
  statement: F.map (hf.lift i h hi) ≫ hf.fst g = i
  proof: by
  simpa [lift] using! PullbackCone.IsLimit.lift_fst _ _ _ _

中文:
引理 lift_fst
  条件: [Full F]
  结论: F.map (hf.lift i h hi) ≫ hf.fst g = i
  证明: by
  simpa [lift] using! PullbackCone.IsLimit.lift_fst _ _ _ _

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift_fst, lift_fst
-/
lemma lift_fst [Full F] : F.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using! PullbackCone.IsLimit.lift_fst _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `lift_snd` / 引理 `lift_snd`

English:
lemma lift_snd
  given: [Full F] [Faithful F]
  statement: hf.lift i h hi ≫ hf.snd g = h
  proof: F.map_injective by simpa [lift] using! PullbackCone.IsLimit.lift_snd _ _ _ _

中文:
引理 lift_snd
  条件: [Full F] [Faithful F]
  结论: hf.lift i h hi ≫ hf.snd g = h
  证明: F.map_injective by simpa [lift] using! PullbackCone.IsLimit.lift_snd _ _ _ _

Depends on / 依赖: F.map_injective, IsLimit, PullbackCone, PullbackCone.IsLimit.lift_snd, lift_snd, map_injective
-/
lemma lift_snd [Full F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h :=
F.map_injective by simpa [lift] using! PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {c : C} (i : c ⟶ b) (h : c ⟶ a) (hi : F.map i ≫ f' = F.map h ≫ g)

/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: [Full F]
  body: hf'.lift _ _ hi

@[reassoc (attr := simp)]

中文:
定义 lift'
  签名: [Full F]
  定义体: hf'.lift _ _ hi

@[reassoc (attr := simp)]
-/
noncomputable def lift' [Full F] : c ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
/--
lemma `lift'_fst` / 引理 `lift'_fst`

English:
lemma lift'_fst
  given: [Full F] [Faithful F]
  statement: hf'.lift' i h hi ≫ hf'.fst' g = i
  proof: F.map_injective (by simp [lift'])

@[reassoc (attr := simp)]

中文:
引理 lift'_fst
  条件: [Full F] [Faithful F]
  结论: hf'.lift' i h hi ≫ hf'.fst' g = i
  证明: F.map_injective (by simp [lift'])

@[reassoc (attr := simp)]
-/
lemma lift'_fst [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  F.map_injective (by simp [lift'])

@[reassoc (attr := simp)]
/--
lemma `lift'_snd` / 引理 `lift'_snd`

English:
lemma lift'_snd
  given: [Full F] [Faithful F]
  statement: hf'.lift' i h hi ≫ hf'.snd g = h
  proof: by
  simp [lift']

中文:
引理 lift'_snd
  条件: [Full F] [Faithful F]
  结论: hf'.lift' i h hi ≫ hf'.snd g = h
  证明: by
  simp [lift']
-/
lemma lift'_snd [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/--
Definition of `symmetry` / `symmetry` 的定义

English:
definition symmetry
  signature: [Full F]
  body: hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]

中文:
定义 symmetry
  签名: [Full F]
  定义体: hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]

Depends on / 依赖: hg.lift, isPullback, w.symm
-/
noncomputable def symmetry [Full F] : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]
/--
lemma `symmetry_fst` / 引理 `symmetry_fst`

English:
lemma symmetry_fst
  given: [Full F] [Faithful F]
  statement: hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g
  proof: by
  simp [symmetry]

@[reassoc (attr := simp)]

中文:
引理 symmetry_fst
  条件: [Full F] [Faithful F]
  结论: hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g
  证明: by
  simp [symmetry]

@[reassoc (attr := simp)]

Depends on / 依赖: symmetry
-/
lemma symmetry_fst [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by
  simp [symmetry]

@[reassoc (attr := simp)]
/--
lemma `symmetry_snd` / 引理 `symmetry_snd`

English:
lemma symmetry_snd
  given: [Full F] [Faithful F]
  statement: hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g
  proof: by
  simp [symmetry]

@[reassoc (attr := simp)]

中文:
引理 symmetry_snd
  条件: [Full F] [Faithful F]
  结论: hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g
  证明: by
  simp [symmetry]

@[reassoc (attr := simp)]

Depends on / 依赖: symmetry
-/
lemma symmetry_snd [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by
  simp [symmetry]

@[reassoc (attr := simp)]
/--
lemma `symmetry_symmetry` / 引理 `symmetry_symmetry`

English:
lemma symmetry_symmetry
  given: [Full F] [Faithful F]
  statement: hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _
  proof: hom_ext' hf' (by simp) (by simp)

中文:
引理 symmetry_symmetry
  条件: [Full F] [Faithful F]
  结论: hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _
  证明: hom_ext' hf' (by simp) (by simp)

Depends on / 依赖: hom_ext
-/
lemma symmetry_symmetry [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ :=
  hom_ext' hf' (by simp) (by simp)

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
/--
Definition of `symmetryIso` / `symmetryIso` 的定义

English:
definition symmetryIso
  signature: [Full F] [Faithful F]
  body: hf'.symmetry hg
  inv := hg.symmetry hf'

中文:
定义 symmetryIso
  签名: [Full F] [Faithful F]
  定义体: hf'.symmetry hg
  inv := hg.symmetry hf'

Depends on / 依赖: symmetry
-/
noncomputable def symmetryIso [Full F] [Faithful F] : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Full
  signature: F] [Faithful F] : IsIso (hf'.symmetry hg)
  body: (hf'.symmetryIso hg).isIso_hom

中文:
实例 [Full
  签名: F] [Faithful F] : IsIso (hf'.symmetry hg)
  定义体: (hf'.symmetryIso hg).isIso_hom

Depends on / 依赖: isIso_hom, symmetryIso
-/
instance [Full F] [Faithful F] : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

/--
lemma `map` / 引理 `map`

English:
lemma map
  statement: [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
  proof: fun c g => by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
apply F.map_isPullback IsPullback.of_hasPullback f g

中文:
引理 map
  结论: [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
  证明: fun c g => by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
apply F.map_isPullback IsPullback.of_hasPullback f g

Depends on / 依赖: F.map, F.map_isPullback, F.map_surjective, IsPullback, IsPullback.of_hasPullback, Limits, Limits.pullback, Limits.pullback.fst, Limits.pullback.snd, map_isPullback, map_surjective, of_hasPullback, pullback
-/
lemma map [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
    [forall c (g : c ⟶ b), PreservesLimit (cospan f g) F] :
    F.relativelyRepresentable (F.map f) := fun c g => by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
apply F.map_isPullback IsPullback.of_hasPullback f g

/--
lemma `of_isIso` / 引理 `of_isIso`

English:
lemma of_isIso
  given: {X Y : D} (f : X ⟶ Y) [IsIso f]
  statement: F.relativelyRepresentable f
  proof: fun a g => ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

中文:
引理 of_isIso
  条件: {X Y : D} (f : X ⟶ Y) [IsIso f]
  结论: F.relativelyRepresentable f
  证明: fun a g => ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.inv, IsPullback, IsPullback.of_vert_isIso, of_vert_isIso
-/
lemma of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f :=
  fun a g => ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

/--
lemma `isomorphisms_le` / 引理 `isomorphisms_le`

English:
lemma isomorphisms_le
  statement: MorphismProperty.isomorphisms D <= F.relativelyRepresentable
  proof: fun _ _ f hf => letI : IsIso f := hf; of_isIso F f

中文:
引理 isomorphisms_le
  结论: Morphism命题erty.isomorphisms D <= F.relativelyRepresentable
  证明: fun _ _ f hf => letI : IsIso f := hf; of_isIso F f

Depends on / 依赖: of_isIso
-/
lemma isomorphisms_le : MorphismProperty.isomorphisms D <= F.relativelyRepresentable :=
  fun _ _ f hf => letI : IsIso f := hf; of_isIso F f

/--
Instance `isMultiplicative` / 实例 `isMultiplicative`

English:
instance isMultiplicative
  signature: : IsMultiplicative F.relativelyRepresentable where
  body: of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h =>
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

中文:
实例 isMultiplicative
  签名: : IsMultiplicative F.relativelyRepresentable where
  定义体: of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h =>
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

Depends on / 依赖: of_isIso
-/
instance isMultiplicative : IsMultiplicative F.relativelyRepresentable where
  id_mem _ := of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h =>
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

/--
Instance `isStableUnderBaseChange` / 实例 `isStableUnderBaseChange`

English:
instance isStableUnderBaseChange
  signature: : IsStableUnderBaseChange F.relativelyRepresentable where
  body: by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

中文:
实例 isStableUnderBaseChange
  签名: : IsStableUnderBaseChange F.relativelyRepresentable where
  定义体: by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

Depends on / 依赖: F.map, IsPullback, IsPullback.of_right, hg.fst, hg.isPullback, hg.pullback, hg.snd, hg.w, isPullback, of_right, pullback
-/
instance isStableUnderBaseChange : IsStableUnderBaseChange F.relativelyRepresentable where
  of_isPullback {X Y Y' X' f g f' g'} P₁ hg a h := by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

/--
Instance `respectsIso` / 实例 `respectsIso`

English:
instance respectsIso
  signature: : RespectsIso F.relativelyRepresentable
  body: (isStableUnderBaseChange F).respectsIso

中文:
实例 respectsIso
  签名: : RespectsIso F.relativelyRepresentable
  定义体: (isStableUnderBaseChange F).respectsIso

Depends on / 依赖: P.le_shift, isStableUnderBaseChange, le_shift, respectsIso
-/
instance respectsIso : RespectsIso F.relativelyRepresentable :=
  (isStableUnderBaseChange F).respectsIso

end Functor.relativelyRepresentable

namespace MorphismProperty

open Functor.relativelyRepresentable

variable {X Y : D} (P : MorphismProperty C)

/--
Definition of `relative` / `relative` 的定义

English:
definition relative
  signature: : MorphismProperty D
  body: fun X Y f => F.relativelyRepresentable f ∧
    forall ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd

中文:
定义 relative
  签名: : Morphism命题erty D
  定义体: fun X Y f => F.relativelyRepresentable f ∧
    forall ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd

Depends on / 依赖: F.map, F.obj, F.relativelyRepresentable, IsPullback, P.le_shift, le_shift, relativelyRepresentable
-/
def relative : MorphismProperty D :=
  fun X Y f => F.relativelyRepresentable f ∧
    forall ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd

/--
Definition of `presheaf` / `presheaf` 的定义

English:
abbreviation presheaf
  signature: : MorphismProperty (Cᵒᵖ ⥤ Type v₁)
  body: P.relative yoneda

中文:
缩写 presheaf
  签名: : Morphism命题erty (Cᵒᵖ ⥤ 类型v₁)
  定义体: P.relative yoneda

Depends on / 依赖: Opposite, Opposite.op, P.ext_of_isTriangulatedClosed, P.relative, e.symm.op, mem_distTriang_op_iff, relative, yoneda
-/
abbrev presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v₁) := P.relative yoneda

variable {P} {F}

/--
lemma `relative.rep` / 引理 `relative.rep`

English:
lemma relative.rep
  given: {f : X ⟶ Y} (hf : P.relative F f)
  statement: F.relativelyRepresentable f
  proof: hf.1

中文:
引理 relative.rep
  条件: {f : X ⟶ Y} (hf : P.relative F f)
  结论: F.relativelyRepresentable f
  证明: hf.1

Depends on / 依赖: Opposite, Opposite.unop, P.ext_of_isTriangulatedClosed, e.symm.unop, op_distinguished
-/
lemma relative.rep {f : X ⟶ Y} (hf : P.relative F f) : F.relativelyRepresentable f :=
  hf.1

/--
lemma `relative.property` / 引理 `relative.property`

English:
lemma relative.property
  given: {f : X ⟶ Y} (hf : P.relative F f)
  proof: hf.2

中文:
引理 relative.property
  条件: {f : X ⟶ Y} (hf : P.relative F f)
  证明: hf.2
-/
lemma relative.property {f : X ⟶ Y} (hf : P.relative F f) :
    forall ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (_ : IsPullback fst (F.map snd) f g), P snd :=
  hf.2

/--
lemma `relative.property_snd` / 引理 `relative.property_snd`

English:
lemma relative.property_snd
  given: {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y)
  proof: hf.property g _ _ (hf.rep.isPullback g)

中文:
引理 relative.property_snd
  条件: {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y)
  证明: hf.property g _ _ (hf.rep.isPullback g)

Depends on / 依赖: hf.property, hf.rep.isPullback, isPullback, property
-/
lemma relative.property_snd {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y) :
    P (hf.rep.snd g) :=
  hf.property g _ _ (hf.rep.isPullback g)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `relative.of_exists` / 引理 `relative.of_exists`

English:
lemma relative.of_exists
  statement: [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
  proof: by
  refine ⟨fun a g => ?_, fun a b g fst snd h => ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))

中文:
引理 relative.of_exists
  结论: [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
  证明: by
  refine ⟨fun a g => ?_, fun a b g fst snd h => ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))

Depends on / 依赖: Arrow.isoMk, F.map_injective, F.obj, F.preimageIso, Iso.refl, P.arrow_mk_iso_iff, all_goals, arrow_mk_iso_iff, g_fst, g_snd, h.isoIsPullback, isoIsPullback, map_injective, preimageIso
-/
lemma relative.of_exists [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (h₀ : forall ⦃a : C⦄ (g : F.obj a ⟶ Y), exists (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd) : P.relative F f := by
  refine ⟨fun a g => ?_, fun a b g fst snd h => ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))

/--
lemma `relative_of_snd` / 引理 `relative_of_snd`

English:
lemma relative_of_snd
  statement: [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
  proof: relative.of_exists (fun _ g => ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

中文:
引理 relative_of_snd
  结论: [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
  证明: relative.of_exists (fun _ g => ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

Depends on / 依赖: hf.fst, hf.isPullback, hf.pullback, hf.snd, isPullback, of_exists, pullback, relative, relative.of_exists
-/
lemma relative_of_snd [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (hf : F.relativelyRepresentable f) (h : forall ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    P.relative F f :=
  relative.of_exists (fun _ g => ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

/--
lemma `relative_map` / 引理 `relative_map`

English:
lemma relative_map
  statement: [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
  proof: by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩

中文:
引理 relative_map
  结论: [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
  证明: by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩

Depends on / 依赖: F.map_surjective, IsPullback, IsPullback.of_hasPullback, P.pullback_snd, map_surjective, of_exists, of_hasPullback, pullback_snd, relative, relative.of_exists
-/
lemma relative_map [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
    {a b : C} {f : a ⟶ b} [forall c (g : c ⟶ b), PreservesLimit (cospan f g) F]
    (hf : P f) : P.relative F (F.map f) := by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩

/--
lemma `of_relative_map` / 引理 `of_relative_map`

English:
lemma of_relative_map
  given: {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f))
  statement: P f
  proof: hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))

中文:
引理 of_relative_map
  条件: {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f))
  结论: P f
  证明: hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))

Depends on / 依赖: F.map, IsPullback, IsPullback.id_horiz, hf.property, id_horiz, property
-/
lemma of_relative_map {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f :=
  hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))

/--
lemma `relative_map_iff` / 引理 `relative_map_iff`

English:
lemma relative_map_iff
  statement: [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
  proof: ⟨fun hf => of_relative_map hf, fun hf => relative_map hf⟩

中文:
引理 relative_map_iff
  结论: [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
  证明: ⟨fun hf => of_relative_map hf, fun hf => relative_map hf⟩

Depends on / 依赖: of_relative_map, relative_map
-/
lemma relative_map_iff [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [IsStableUnderBaseChange P] {X Y : C} {f : X ⟶ Y} :
    P.relative F (F.map f) ↔ P f :=
  ⟨fun hf => of_relative_map hf, fun hf => relative_map hf⟩

/--
lemma `relative_monotone` / 引理 `relative_monotone`

English:
lemma relative_monotone
  given: {P' : MorphismProperty C} (h : P <= P')
  proof: fun _ _ _ hf =>
  ⟨hf.rep, fun _ _ g fst snd BC => h _ (hf.property g fst snd BC)⟩

中文:
引理 relative_monotone
  条件: {P' : Morphism命题erty C} (h : P <= P')
  证明: fun _ _ _ hf =>
  ⟨hf.rep, fun _ _ g fst snd BC => h _ (hf.property g fst snd BC)⟩
-/
lemma relative_monotone {P' : MorphismProperty C} (h : P <= P') :
    P.relative F <= P'.relative F := fun _ _ _ hf =>
  ⟨hf.rep, fun _ _ g fst snd BC => h _ (hf.property g fst snd BC)⟩

section

variable (P)

/--
lemma `relative_isStableUnderBaseChange` / 引理 `relative_isStableUnderBaseChange`

English:
lemma relative_isStableUnderBaseChange
  statement: IsStableUnderBaseChange (P.relative F) where
  proof: ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC => hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩

中文:
引理 relative_isStableUnderBaseChange
  结论: IsStableUnderBaseChange (P.relative F) where
  证明: ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC => hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩

Depends on / 依赖: IsPullback, IsPullback.paste_horiz, hg.property, hg.rep, of_isPullback, paste_horiz, property
-/
lemma relative_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) where
  of_isPullback hfBC hg :=
    ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC => hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩

/--
Instance `relative_isStableUnderComposition` / 实例 `relative_isStableUnderComposition`

English:
instance relative_isStableUnderComposition
  signature: [F.Faithful] [F.Full] [P.IsStableUnderComposition]
  body: by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h => ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
 

中文:
实例 relative_isStableUnderComposition
  签名: [F.Faithful] [F.Full] [P.IsStableUnderComposition]
  定义体: by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h => ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
 

Depends on / 依赖: Functor, Functor.map_comp, IsPullback, IsPullback.of_bot, comp_mem, hf.property, hg.property_snd, isPullback, lift_fst, lift_snd, map_comp, of_bot, property, property_snd
-/
instance relative_isStableUnderComposition [F.Faithful] [F.Full] [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.relative F) where
  comp_mem {F G H} f g hf hg := by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h => ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
      exact h
    · symm
      apply hg.1.lift_fst

/--
Instance `relative_respectsIso` / 实例 `relative_respectsIso`

English:
instance relative_respectsIso
  signature: : RespectsIso (P.relative F)
  body: (relative_isStableUnderBaseChange P).respectsIso

中文:
实例 relative_respectsIso
  签名: : RespectsIso (P.relative F)
  定义体: (relative_isStableUnderBaseChange P).respectsIso

Depends on / 依赖: relative_isStableUnderBaseChange, respectsIso
-/
instance relative_respectsIso : RespectsIso (P.relative F) :=
  (relative_isStableUnderBaseChange P).respectsIso

/--
Instance `relative_isMultiplicative` / 实例 `relative_isMultiplicative`

English:
instance relative_isMultiplicative
  signature: [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso]
  body: relative.of_exists
    (fun Y g => ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)

中文:
实例 relative_isMultiplicative
  签名: [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso]
  定义体: relative.of_exists
    (fun Y g => ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)

Depends on / 依赖: of_exists, relative, relative.of_exists
-/
instance relative_isMultiplicative [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso] :
    IsMultiplicative (P.relative F) where
  id_mem X := relative.of_exists
    (fun Y g => ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)

end

section

-- TODO(Calle): This could be generalized to functors whose image forms a separating family.
/--
lemma `presheaf_monomorphisms_le_monomorphisms` / 引理 `presheaf_monomorphisms_le_monomorphisms`

English:
lemma presheaf_monomorphisms_le_monomorphisms
  proof: fun F G f hf => by
  suffices forall {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f -> a = b from
    ⟨fun _ _ h => hom_ext_yoneda (fun _ _ => this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, wh

中文:
引理 presheaf_monomorphisms_le_monomorphisms
  证明: fun F G f hf => by
  suffices forall {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f -> a = b from
    ⟨fun _ _ h => hom_ext_yoneda (fun _ _ => this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, wh

Depends on / 依赖: hom_ext_yoneda, yoneda, yoneda.obj
-/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf <= monomorphisms _ := fun F G f hf => by
  suffices forall {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f -> a = b from
    ⟨fun _ _ h => hom_ext_yoneda (fun _ _ => this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, where `g = a ≫ f = a ≫ f`. -/
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  -- This follows from the fact that the induced maps `hf.rep.pullback g ⟶ X` are mono.
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), lift_snd]

variable {G : Cᵒᵖ ⥤ Type v₁}

/--
lemma `presheaf_mono_of_le` / 引理 `presheaf_mono_of_le`

English:
lemma presheaf_mono_of_le
  statement: (hP : P <= MorphismProperty.monomorphisms C)
  proof: MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

中文:
引理 presheaf_mono_of_le
  结论: (hP : P <= Morphism命题erty.monomorphisms C)
  证明: MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

Depends on / 依赖: MorphismProperty, MorphismProperty.presheaf_monomorphisms_le_monomorphisms, MorphismProperty.relative_monotone, presheaf_monomorphisms_le_monomorphisms, relative_monotone
-/
lemma presheaf_mono_of_le (hP : P <= MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

/--
lemma `fst'_self_eq_snd` / 引理 `fst'_self_eq_snd`

English:
lemma fst'_self_eq_snd
  statement: (hP : P <= MorphismProperty.monomorphisms C)
  proof: by
  have := P.presheaf_mono_of_le hP hf
  apply yoneda.map_injective
  rw [← cancel_mono f]; rw [(hf.rep.isPullback' f).w]

中文:
引理 fst'_self_eq_snd
  结论: (hP : P <= Morphism命题erty.monomorphisms C)
  证明: by
  have := P.presheaf_mono_of_le hP hf
  apply yoneda.map_injective
  rw [← cancel_mono f]; rw [(hf.rep.isPullback' f).w]

Depends on / 依赖: P.presheaf_mono_of_le, cancel_mono, hf.rep.isPullback, isPullback, map_injective, presheaf_mono_of_le, yoneda, yoneda.map_injective
-/
lemma fst'_self_eq_snd (hP : P <= MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : hf.rep.fst' f = hf.rep.snd f := by
  have := P.presheaf_mono_of_le hP hf
  apply yoneda.map_injective
  rw [← cancel_mono f]; rw [(hf.rep.isPullback' f).w]

/--
lemma `isIso_fst'_self` / 引理 `isIso_fst'_self`

English:
lemma isIso_fst'_self
  statement: (hP : P <= MorphismProperty.monomorphisms C)
  proof: have := P.presheaf_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  Yoneda.fullyFaithful.isIso_of_isIso_map _

中文:
引理 isIso_fst'_self
  结论: (hP : P <= Morphism命题erty.monomorphisms C)
  证明: have := P.presheaf_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  Yoneda.fullyFaithful.isIso_of_isIso_map _

Depends on / 依赖: P.presheaf_mono_of_le, Yoneda, Yoneda.fullyFaithful.isIso_of_isIso_map, fullyFaithful, hf.rep.isPullback, isIso_fst_of_mono, isIso_of_isIso_map, isPullback, presheaf_mono_of_le
-/
lemma isIso_fst'_self (hP : P <= MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : IsIso (hf.rep.fst' f) :=
  have := P.presheaf_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  Yoneda.fullyFaithful.isIso_of_isIso_map _

end

end MorphismProperty

namespace Functor.relativelyRepresentable

section Pullbacks₃
/-
In this section we develop some basic API that help deal with certain triple pullbacks obtained
from morphism `f₁ : F.obj A₁ ⟶ X` which is relatively representable with respect to some functor
`F : C ⥤ D`.

More precisely, given two objects `A₂` and `A₃` in `C`, and two morphisms `f₂ : A₂ ⟶ X` and
`f₃ : A₃ ⟶ X`, we can consider the pullbacks (in `D`) `(A₁ ×_X A₂)` and `(A₁ ×_X A₃)`
(which makes sense as objects in `C` due to `F` being relatively representable).

We can then consider the pullback, in `C`, of these two pullbacks. This is the object
`(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. In this section we develop some basic API for dealing with this
pullback. This is used in `Mathlib/AlgebraicGeometry/Sites/Representability.lean` to show that
representability is Zariski-local.
-/
variable {F : C ⥤ D} [Full F] {A₁ A₂ A₃ : C} {X : D}
  {f₁ : F.obj A₁ ⟶ X} (hf₁ : F.relativelyRepresentable f₁)
  (f₂ : F.obj A₂ ⟶ X) (f₃ : F.obj A₃ ⟶ X)
  [HasPullback (hf₁.fst' f₂) (hf₁.fst' f₃)]

/--
Definition of `pullback₃` / `pullback₃` 的定义

English:
definition pullback₃
  body: Limits.pullback (hf₁.fst' f₂) (hf₁.fst' f₃)

中文:
定义 pullback₃
  定义体: Limits.pullback (hf₁.fst' f₂) (hf₁.fst' f₃)

Depends on / 依赖: Limits, Limits.pullback, pullback
-/
noncomputable def pullback₃ := Limits.pullback (hf₁.fst' f₂) (hf₁.fst' f₃)
/--
Definition of `pullback₃.p₁` / `pullback₃.p₁` 的定义

English:
definition pullback₃.p₁
  signature: : hf₁.pullback₃ f₂ f₃ ⟶ A₁
  body: pullback.fst _ _ ≫ hf₁.fst' f₂

中文:
定义 pullback₃.p₁
  签名: : hf₁.pullback₃ f₂ f₃ ⟶ A₁
  定义体: pullback.fst _ _ ≫ hf₁.fst' f₂

Depends on / 依赖: pullback, pullback.fst
-/
noncomputable def pullback₃.p₁ : hf₁.pullback₃ f₂ f₃ ⟶ A₁ := pullback.fst _ _ ≫ hf₁.fst' f₂
/--
Definition of `pullback₃.p₂` / `pullback₃.p₂` 的定义

English:
definition pullback₃.p₂
  signature: : hf₁.pullback₃ f₂ f₃ ⟶ A₂
  body: pullback.fst _ _ ≫ hf₁.snd f₂

中文:
定义 pullback₃.p₂
  签名: : hf₁.pullback₃ f₂ f₃ ⟶ A₂
  定义体: pullback.fst _ _ ≫ hf₁.snd f₂

Depends on / 依赖: pullback, pullback.fst
-/
noncomputable def pullback₃.p₂ : hf₁.pullback₃ f₂ f₃ ⟶ A₂ := pullback.fst _ _ ≫ hf₁.snd f₂
/--
Definition of `pullback₃.p₃` / `pullback₃.p₃` 的定义

English:
definition pullback₃.p₃
  signature: : hf₁.pullback₃ f₂ f₃ ⟶ A₃
  body: pullback.snd _ _ ≫ hf₁.snd f₃

中文:
定义 pullback₃.p₃
  签名: : hf₁.pullback₃ f₂ f₃ ⟶ A₃
  定义体: pullback.snd _ _ ≫ hf₁.snd f₃

Depends on / 依赖: pullback, pullback.snd
-/
noncomputable def pullback₃.p₃ : hf₁.pullback₃ f₂ f₃ ⟶ A₃ := pullback.snd _ _ ≫ hf₁.snd f₃

/--
Definition of `pullback₃.π` / `pullback₃.π` 的定义

English:
definition pullback₃.π
  signature: : F.obj (pullback₃ hf₁ f₂ f₃) ⟶ X
  body: F.map (p₁ hf₁ f₂ f₃) ≫ f₁

@[reassoc (attr := simp)]

中文:
定义 pullback₃.π
  签名: : F.obj (pullback₃ hf₁ f₂ f₃) ⟶ X
  定义体: F.map (p₁ hf₁ f₂ f₃) ≫ f₁

@[reassoc (attr := simp)]

Depends on / 依赖: F.map
-/
noncomputable def pullback₃.π : F.obj (pullback₃ hf₁ f₂ f₃) ⟶ X :=
  F.map (p₁ hf₁ f₂ f₃) ≫ f₁

@[reassoc (attr := simp)]
/--
lemma `pullback₃.map_p₁_comp` / 引理 `pullback₃.map_p₁_comp`

English:
lemma pullback₃.map_p₁_comp
  statement: F.map (p₁ hf₁ f₂ f₃) ≫ f₁ = π _ _ _
  proof: rfl

中文:
引理 pullback₃.map_p₁_comp
  结论: F.map (p₁ hf₁ f₂ f₃) ≫ f₁ = π _ _ _
  证明: rfl
-/
lemma pullback₃.map_p₁_comp : F.map (p₁ hf₁ f₂ f₃) ≫ f₁ = π _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `pullback₃.map_p₂_comp` / 引理 `pullback₃.map_p₂_comp`

English:
lemma pullback₃.map_p₂_comp
  statement: F.map (p₂ hf₁ f₂ f₃) ≫ f₂ = π _ _ _
  proof: by
  simp [π, p₁, p₂, ← hf₁.w f₂]

中文:
引理 pullback₃.map_p₂_comp
  结论: F.map (p₂ hf₁ f₂ f₃) ≫ f₂ = π _ _ _
  证明: by
  simp [π, p₁, p₂, ← hf₁.w f₂]
-/
lemma pullback₃.map_p₂_comp : F.map (p₂ hf₁ f₂ f₃) ≫ f₂ = π _ _ _ := by
  simp [π, p₁, p₂, ← hf₁.w f₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullback₃.map_p₃_comp` / 引理 `pullback₃.map_p₃_comp`

English:
lemma pullback₃.map_p₃_comp
  statement: F.map (p₃ hf₁ f₂ f₃) ≫ f₃ = π _ _ _
  proof: by
  simp [π, p₁, p₃, ← hf₁.w f₃, pullback.condition]

中文:
引理 pullback₃.map_p₃_comp
  结论: F.map (p₃ hf₁ f₂ f₃) ≫ f₃ = π _ _ _
  证明: by
  simp [π, p₁, p₃, ← hf₁.w f₃, pullback.condition]

Depends on / 依赖: condition, pullback, pullback.condition
-/
lemma pullback₃.map_p₃_comp : F.map (p₃ hf₁ f₂ f₃) ≫ f₃ = π _ _ _ := by
  simp [π, p₁, p₃, ← hf₁.w f₃, pullback.condition]

section

variable [Faithful F] {Z : C} (x₁ : Z ⟶ A₁) (x₂ : Z ⟶ A₂) (x₃ : Z ⟶ A₃)
  (h₁₂ : F.map x₁ ≫ f₁ = F.map x₂ ≫ f₂)
  (h₁₃ : F.map x₁ ≫ f₁ = F.map x₃ ≫ f₃)

/--
Definition of `lift₃` / `lift₃` 的定义

English:
definition lift₃
  signature: : Z ⟶ pullback₃ hf₁ f₂ f₃
  body: pullback.lift (hf₁.lift' x₁ x₂ h₁₂)
    (hf₁.lift' x₁ x₃ h₁₃) (by simp)

中文:
定义 lift₃
  签名: : Z ⟶ pullback₃ hf₁ f₂ f₃
  定义体: pullback.lift (hf₁.lift' x₁ x₂ h₁₂)
    (hf₁.lift' x₁ x₃ h₁₃) (by simp)

Depends on / 依赖: pullback, pullback.lift
-/
noncomputable def lift₃ : Z ⟶ pullback₃ hf₁ f₂ f₃ :=
  pullback.lift (hf₁.lift' x₁ x₂ h₁₂)
    (hf₁.lift' x₁ x₃ h₁₃) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `lift₃_p₁` / 引理 `lift₃_p₁`

English:
lemma lift₃_p₁
  statement: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₁ hf₁ f₂ f₃ = x₁
  proof: by
  simp [lift₃, pullback₃.p₁]

中文:
引理 lift₃_p₁
  结论: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₁ hf₁ f₂ f₃ = x₁
  证明: by
  simp [lift₃, pullback₃.p₁]
-/
lemma lift₃_p₁ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₁ hf₁ f₂ f₃ = x₁ := by
  simp [lift₃, pullback₃.p₁]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `lift₃_p₂` / 引理 `lift₃_p₂`

English:
lemma lift₃_p₂
  statement: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₂ hf₁ f₂ f₃ = x₂
  proof: by
  simp [lift₃, pullback₃.p₂]

中文:
引理 lift₃_p₂
  结论: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₂ hf₁ f₂ f₃ = x₂
  证明: by
  simp [lift₃, pullback₃.p₂]
-/
lemma lift₃_p₂ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₂ hf₁ f₂ f₃ = x₂ := by
  simp [lift₃, pullback₃.p₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `lift₃_p₃` / 引理 `lift₃_p₃`

English:
lemma lift₃_p₃
  statement: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₃ hf₁ f₂ f₃ = x₃
  proof: by
  simp [lift₃, pullback₃.p₃]

中文:
引理 lift₃_p₃
  结论: hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₃ hf₁ f₂ f₃ = x₃
  证明: by
  simp [lift₃, pullback₃.p₃]
-/
lemma lift₃_p₃ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₃ hf₁ f₂ f₃ = x₃ := by
  simp [lift₃, pullback₃.p₃]

end

@[reassoc (attr := simp)]
/--
lemma `pullback₃.fst_fst'_eq_p₁` / 引理 `pullback₃.fst_fst'_eq_p₁`

English:
lemma pullback₃.fst_fst'_eq_p₁
  statement: pullback.fst _ _ ≫ hf₁.fst' f₂ = pullback₃.p₁ hf₁ f₂ f₃
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 pullback₃.fst_fst'_eq_p₁
  结论: pullback.fst _ _ ≫ hf₁.fst' f₂ = pullback₃.p₁ hf₁ f₂ f₃
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma pullback₃.fst_fst'_eq_p₁ : pullback.fst _ _ ≫ hf₁.fst' f₂ = pullback₃.p₁ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/--
lemma `pullback₃.fst_snd_eq_p₂` / 引理 `pullback₃.fst_snd_eq_p₂`

English:
lemma pullback₃.fst_snd_eq_p₂
  statement: pullback.fst _ _ ≫ hf₁.snd f₂ = pullback₃.p₂ hf₁ f₂ f₃
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 pullback₃.fst_snd_eq_p₂
  结论: pullback.fst _ _ ≫ hf₁.snd f₂ = pullback₃.p₂ hf₁ f₂ f₃
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma pullback₃.fst_snd_eq_p₂ : pullback.fst _ _ ≫ hf₁.snd f₂ = pullback₃.p₂ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/--
lemma `pullback₃.snd_snd_eq_p₃` / 引理 `pullback₃.snd_snd_eq_p₃`

English:
lemma pullback₃.snd_snd_eq_p₃
  statement: pullback.snd _ _ ≫ hf₁.snd f₃ = pullback₃.p₃ hf₁ f₂ f₃
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 pullback₃.snd_snd_eq_p₃
  结论: pullback.snd _ _ ≫ hf₁.snd f₃ = pullback₃.p₃ hf₁ f₂ f₃
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma pullback₃.snd_snd_eq_p₃ : pullback.snd _ _ ≫ hf₁.snd f₃ = pullback₃.p₃ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
/--
lemma `pullback₃.snd_fst'_eq_p₁` / 引理 `pullback₃.snd_fst'_eq_p₁`

English:
lemma pullback₃.snd_fst'_eq_p₁
  proof: pullback.condition.symm

中文:
引理 pullback₃.snd_fst'_eq_p₁
  证明: pullback.condition.symm

Depends on / 依赖: condition, pullback, pullback.condition.symm
-/
lemma pullback₃.snd_fst'_eq_p₁ :
    pullback.snd (hf₁.fst' f₂) (hf₁.fst' f₃) ≫ hf₁.fst' f₃ = pullback₃.p₁ hf₁ f₂ f₃ :=
  pullback.condition.symm

set_option backward.isDefEq.respectTransparency.types false in
variable {hf₁ f₂ f₃} in
@[ext]
/--
lemma `pullback₃.hom_ext` / 引理 `pullback₃.hom_ext`

English:
lemma pullback₃.hom_ext
  statement: [Faithful F] {Z : C} {φ φ' : Z ⟶ pullback₃ hf₁ f₂ f₃}
  proof: by
  apply pullback.hom_ext <;> ext <;> simpa

中文:
引理 pullback₃.hom_ext
  结论: [Faithful F] {Z : C} {φ φ' : Z ⟶ pullback₃ hf₁ f₂ f₃}
  证明: by
  apply pullback.hom_ext <;> ext <;> simpa

Depends on / 依赖: hom_ext, pullback, pullback.hom_ext
-/
lemma pullback₃.hom_ext [Faithful F] {Z : C} {φ φ' : Z ⟶ pullback₃ hf₁ f₂ f₃}
    (h₁ : φ ≫ pullback₃.p₁ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₁ hf₁ f₂ f₃)
    (h₂ : φ ≫ pullback₃.p₂ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₂ hf₁ f₂ f₃)
    (h₃ : φ ≫ pullback₃.p₃ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₃ hf₁ f₂ f₃) : φ = φ' := by
  apply pullback.hom_ext <;> ext <;> simpa

end Pullbacks₃

section Diagonal
/-
In this section, we prove a criterion for the diagonal morphisms to be relatively representable.
-/

variable {F : C ⥤ D}
variable [HasBinaryProducts C]
variable [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
variable [Full F]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_diag` / 引理 `of_diag`

English:
lemma of_diag
  statement: {X : D} (h : F.relativelyRepresentable (Limits.diag X))
  proof: by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)] at h
  intro a' g'
  obtain ⟨_, ⟨left⟩⟩ := pullback_map_diagonal_isPullback g g' (terminal.from X)
  let prodMap : F.obj (a ⨯ a') ⟶ X ⨯ X :=
    (preservesLimitIso _ (pair _ _) ≪≫ HasLimit.isoOfNatIso (p

中文:
引理 of_diag
  结论: {X : D} (h : F.relativelyRepresentable (Limits.diag X))
  证明: by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)] at h
  intro a' g'
  obtain ⟨_, ⟨left⟩⟩ := pullback_map_diagonal_isPullback g g' (terminal.from X)
  let prodMap : F.obj (a ⨯ a') ⟶ X ⨯ X :=
    (preservesLimitIso _ (pair _ _) ≪≫ HasLimit.isoOfNatIso (p

Depends on / 依赖: F.obj, HasLimit, HasLimit.isoOfNatIso, IsPullback, IsPullback.of_vert_isIso_mono, Limits, Limits.diag, cat_disch, choose_spec, choose_spec.choose_spec.choose_spec.isLimit, conePointUniqueUpToIso, isLimit, isoOfNatIso, of_vert_isIso_mono, pairComp, pasteHorizIsPullback, pbRepr, preservesLimitIso, prod.map, prodIsoPullback
-/
lemma of_diag {X : D} (h : F.relativelyRepresentable (Limits.diag X))
    ⦃a : C⦄ (g : F.obj a ⟶ X) : F.relativelyRepresentable g := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)] at h
  intro a' g'
  obtain ⟨_, ⟨left⟩⟩ := pullback_map_diagonal_isPullback g g' (terminal.from X)
  let prodMap : F.obj (a ⨯ a') ⟶ X ⨯ X :=
    (preservesLimitIso _ (pair _ _) ≪≫ HasLimit.isoOfNatIso (pairComp _ _ _)).hom ≫ prod.map g g'
  let pbRepr :=
(h prodMap).choose_spec.choose_spec.choose_spec.isLimit'.some.conePointUniqueUpToIso
    pasteHorizIsPullback rfl (IsPullback.of_vert_isIso_mono (snd := pullback.congrHom
      (terminal.comp_from g) (terminal.comp_from g') ≪≫ (prodIsoPullback _ _).symm ≪≫
.hom) (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫ (preservesLimitIso _ (pair _ _)).symm
    ⟨by cat_disch⟩).isLimit'.some left
  exact ⟨_, ⟨_, ⟨_, IsPullback.of_iso_pullback (fst := pbRepr.hom ≫ pullback.fst g g')
    (snd := F.map (Functor.preimage F (pbRepr.hom ≫ pullback.snd g g')))
    ⟨by simp [pullback.condition]⟩ pbRepr (by cat_disch) (by cat_disch)⟩⟩⟩

/--
lemma `toPullbackTerminal` / 引理 `toPullbackTerminal`

English:
lemma toPullbackTerminal
  statement: {X : D} {a : C}
  proof: by
  let pbIso := pullback.congrHom
    (terminal.comp_from _ : (g ≫ pullback.fst _ _) ≫ terminal.from X = terminal.from _)
    (terminal.comp_from _ : (g ≫ pullback.snd _ _) ≫ terminal.from X = terminal.from _) ≪≫
    (prodIsoPullback _ _).symm ≪≫ (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫
   

中文:
引理 toPullbackTerminal
  结论: {X : D} {a : C}
  证明: by
  let pbIso := pullback.congrHom
    (terminal.comp_from _ : (g ≫ pullback.fst _ _) ≫ terminal.from X = terminal.from _)
    (terminal.comp_from _ : (g ≫ pullback.snd _ _) ≫ terminal.from X = terminal.from _) ≪≫
    (prodIsoPullback _ _).symm ≪≫ (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫
   

Depends on / 依赖: pullback, pullback.fst, terminal, terminal.from
-/
lemma toPullbackTerminal {X : D} {a : C}
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    (g : F.obj a ⟶ Limits.pullback (terminal.from X) (terminal.from X)) :
    F.relativelyRepresentable (pullback.lift (f := (g ≫ pullback.fst _ _) ≫ terminal.from X)
        (g := (g ≫ pullback.snd _ _) ≫ terminal.from X) (𝟙 _) (𝟙 _) (by cat_disch)) := by
  let pbIso := pullback.congrHom
    (terminal.comp_from _ : (g ≫ pullback.fst _ _) ≫ terminal.from X = terminal.from _)
    (terminal.comp_from _ : (g ≫ pullback.snd _ _) ≫ terminal.from X = terminal.from _) ≪≫
    (prodIsoPullback _ _).symm ≪≫ (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫
    (preservesLimitIso _ (pair _ _)).symm
  rw [← comp_id (pullback.lift _ _)]; rw [← pbIso.hom_inv_id]; rw [← Category.assoc]
  apply (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _
  exact map_preimage F (_ ≫ pbIso.hom) ▸ map F (F.preimage _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `diag_of_map_from_obj` / 引理 `diag_of_map_from_obj`

English:
lemma diag_of_map_from_obj
  statement: [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  proof: by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)]
  suffices F.relativelyRepresentable (pullback.lift (𝟙 _) (𝟙 _)) from
    (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _ this
  intro a g
  obtain ⟨_, ⟨_, ⟨_, pbRepr⟩⟩⟩ := h (g ≫ 

中文:
引理 diag_of_map_from_obj
  结论: [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  证明: by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)]
  suffices F.relativelyRepresentable (pullback.lift (𝟙 _) (𝟙 _)) from
    (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _ this
  intro a g
  obtain ⟨_, ⟨_, ⟨_, pbRepr⟩⟩⟩ := h (g ≫ 

Depends on / 依赖: F.relativelyRepresentable, IsPullback, IsPullback.of_iso_pullback, Limits, Limits.diag, cat_disch, condition, isoPullback, of_iso_pullback, pbRepr, pbRepr.isoPullback, postcomp, prodIsoPullback, pullback, pullback.condition, pullback.fst, pullback.lift, pullback.snd, pullbackDiagonalMapIdIso, relativelyRepresentable
-/
lemma diag_of_map_from_obj [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    {X : D} (h : forall ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g) :
    F.relativelyRepresentable (Limits.diag X) := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)]
  suffices F.relativelyRepresentable (pullback.lift (𝟙 _) (𝟙 _)) from
    (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _ this
  intro a g
  obtain ⟨_, ⟨_, ⟨_, pbRepr⟩⟩⟩ := h (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
  obtain ⟨_, ⟨bot⟩⟩ := IsPullback.of_iso_pullback ⟨by rw [assoc]; simp [pullback.condition]⟩
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm) rfl rfl
obtain ⟨_, ⟨_, ⟨topMap, top⟩⟩⟩ := (toPullbackTerminal g)
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm).hom ≫ pullback.snd
        (pullback.diagonal (terminal.from X))
        (pullback.map _ _ _ _ _ _ (𝟙 _) (by cat_disch) (by cat_disch))
  have hg : g = pullback.lift (𝟙 _) (𝟙 _) (by cat_disch) ≫ pullback.map
    ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ terminal.from X) _ _
      (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _) (𝟙 _) (by cat_disch) (by cat_disch) := by
    apply Limits.pullback.hom_ext <;> simp
exact hg ▸ ⟨_, ⟨_, ⟨_, IsPullback.of_isLimit pasteVertIsPullback rfl bot
    (map_preimage F topMap ▸ top).flip.isLimit'.some⟩⟩⟩

/--
lemma `diag_iff` / 引理 `diag_iff`

English:
lemma diag_iff
  given: {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  proof: ⟨fun h _ g => of_diag h g, fun h => diag_of_map_from_obj h⟩

中文:
引理 diag_iff
  条件: {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  证明: ⟨fun h _ g => of_diag h g, fun h => diag_of_map_from_obj h⟩

Depends on / 依赖: diag_of_map_from_obj, of_diag
-/
lemma diag_iff {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable (Limits.diag X) ↔
      forall ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g :=
  ⟨fun h _ g => of_diag h g, fun h => diag_of_map_from_obj h⟩

end Diagonal

end Functor.relativelyRepresentable

end CategoryTheory
