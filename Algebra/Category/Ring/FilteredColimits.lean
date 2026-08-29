/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Ring.ULift

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRingCat`.
We show that the colimit of `F ⋙ forget₂ SemiRingCat MonCat` (in `MonCat`)
carries the structure of a semiring, thereby showing that the forgetful functor
`forget₂ SemiRingCat MonCat` preserves filtered colimits.
In particular, this implies that `forget SemiRingCat` preserves filtered colimits.
Similarly for `CommSemiRingCat`, `RingCat` and `CommRingCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max -> max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

-- This instance is needed below in `colimitSemiring`, during the verification of the
-- semiring axioms.
/--
Instance `semiringObj` / 实例 `semiringObj`

English:
instance semiringObj
  signature: (j : J)
  body: inferInstanceAs Semiring (F.obj j)

中文:
实例 semiringObj
  签名: (j : J)
  定义体: inferInstanceAs Semiring (F.obj j)

Depends on / 依赖: F.obj, Semiring
-/
instance semiringObj (j : J) :
    Semiring (((F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⋙ forget MonCat).obj j) :=
inferInstanceAs Semiring (F.obj j)

variable [IsFiltered J]

/--
Definition of `R` / `R` 的定义

English:
abbreviation R
  signature: : MonCat.{max v u}
  body: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

中文:
缩写 R
  签名: : MonCat.{max v u}
  定义体: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

Depends on / 依赖: FilteredColimits, MonCat, MonCat.FilteredColimits.colimit, SemiRingCat, colimit
-/
abbrev R : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `colimitSemiring` / 实例 `colimitSemiring`

English:
instance colimitSemiring
  signature: : Semiring.{max v u} R.{v, u} F
  body: { (R.{v, u} F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u}) with
    mul_zero := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq 

中文:
实例 colimitSemiring
  签名: : Semiring.{max v u} R.{v, u} F
  定义体: { (R.{v, u} F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u}) with
    mul_zero := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq 

Depends on / 依赖: AddCommMonCat, AddCommMonCat.FilteredColimits.colimitAddCommMonoid, CategoryTheory, CategoryTheory.Functor.map_id, FilteredColimits, Functor, Quot.inductionOn, SemiRingCat, colimitAddCommMonoid, colimit_mul_mk_eq, colimit_zero_eq, inductionOn, map_id, mul_zero, zero_mul
-/
instance colimitSemiring : Semiring.{max v u} R.{v, u} F :=
  { (R.{v, u} F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u}) with
    mul_zero := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [mul_zero x]
      rfl
    zero_mul := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [zero_mul x]
      rfl
    left_distrib := fun x y z => by
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [CategoryTheory.Functor.map_id]
      erw [left_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl
    right_distrib := fun x y z => by
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h, colimit_mul_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [CategoryTheory.Functor.map_id]
      erw [right_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl }

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : SemiRingCat.{max v u}
  body: SemiRingCat.of R.{v, u} F

中文:
定义 colimit
  签名: : SemiRingCat.{max v u}
  定义体: SemiRingCat.of R.{v, u} F

Depends on / 依赖: SemiRingCat, SemiRingCat.of
-/
def colimit : SemiRingCat.{max v u} :=
SemiRingCat.of R.{v, u} F

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι :=
    { app := fun j => ofHom
        { ((MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)).ι.app j).hom,
            ((AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)).ι.ap

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι :=
    { app := fun j => ofHom
        { ((MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)).ι.app j).hom,
            ((AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)).ι.ap

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, TopModuleCat, colimit
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun j => ofHom
        { ((MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)).ι.app j).hom,
            ((AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)).ι.app j).hom with }
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget SemiRingCat)).ι.naturality_apply f _ }

namespace colimitCoconeIsColimit

variable {F} (t : Cocone F)

/--
Definition of `descAddMonoidHom` / `descAddMonoidHom` 的定义

English:
definition descAddMonoidHom
  signature: : R F ->+ t.1
  body: ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

中文:
定义 descAddMonoidHom
  签名: : R F ->+ t.1
  定义体: ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

Depends on / 依赖: AddCommMonCat, AddCommMonCat.FilteredColimits.colimitCoconeIsColimit, FilteredColimits, SemiRingCat, colimitCoconeIsColimit, mapCocone
-/
def descAddMonoidHom : R F ->+ t.1 :=
  ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

/--
lemma `descAddMonoidHom_quotMk` / 引理 `descAddMonoidHom_quotMk`

English:
lemma descAddMonoidHom_quotMk
  given: {j : J} (x : F.obj j)
  proof: ConcreteCategory.congr_hom ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

中文:
引理 descAddMonoidHom_quotMk
  条件: {j : J} (x : F.obj j)
  证明: ConcreteCategory.congr_hom ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

Depends on / 依赖: AddCommMonCat, AddCommMonCat.FilteredColimits.colimitCoconeIsColimit, ConcreteCategory, ConcreteCategory.congr_hom, FilteredColimits, SemiRingCat, colimitCoconeIsColimit, congr_hom, congr_map, f.hom, forget, mapCocone
-/
lemma descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

/--
Definition of `descMonoidHom` / `descMonoidHom` 的定义

English:
definition descMonoidHom
  signature: : R F ->* t.1
  body: ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom

中文:
定义 descMonoidHom
  签名: : R F ->* t.1
  定义体: ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom

Depends on / 依赖: FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, mapCocone
-/
def descMonoidHom : R F ->* t.1 :=
  ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom

/--
lemma `descMonoidHom_quotMk` / 引理 `descMonoidHom_quotMk`

English:
lemma descMonoidHom_quotMk
  given: {j : J} (x : F.obj j)
  proof: ConcreteCategory.congr_hom ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

中文:
引理 descMonoidHom_quotMk
  条件: {j : J} (x : F.obj j)
  证明: ConcreteCategory.congr_hom ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, congr_hom, congr_map, forget, mapCocone
-/
lemma descMonoidHom_quotMk {j : J} (x : F.obj j) :
    descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

/--
lemma `descMonoidHom_apply_eq` / 引理 `descMonoidHom_apply_eq`

English:
lemma descMonoidHom_apply_eq
  given: (x : R F)
  proof: by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x]; rw [descAddMonoidHom_quotMk t x]

中文:
引理 descMonoidHom_apply_eq
  条件: (x : R F)
  证明: by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x]; rw [descAddMonoidHom_quotMk t x]

Depends on / 依赖: descAddMonoidHom_quotMk, descMonoidHom_quotMk, f.hom, g.hom
-/
lemma descMonoidHom_apply_eq (x : R F) :
    descMonoidHom t x = descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x]; rw [descAddMonoidHom_quotMk t x]

end colimitCoconeIsColimit

open colimitCoconeIsColimit in
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit colimitCocone.{v, u} F where
  body: ofHom
    { descAddMonoidHom t with
      map_one' := (descMonoidHom_apply_eq t 1).symm.trans (by simp)
      map_mul' x y := by
        change descAddMonoidHom t (x * y) =
          descAddMonoidHom t x * descAddMonoidHom t y
        simp [← descMonoidHom_apply_eq] }
  fac t j := by ext x; exact de

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit colimitCocone.{v, u} F where
  定义体: ofHom
    { descAddMonoidHom t with
      map_one' := (descMonoidHom_apply_eq t 1).symm.trans (by simp)
      map_mul' x y := by
        change descAddMonoidHom t (x * y) =
          descAddMonoidHom t x * descAddMonoidHom t y
        simp [← descMonoidHom_apply_eq] }
  fac t j := by ext x; exact de
-/
def colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F where
  desc t := ofHom
    { descAddMonoidHom t with
      map_one' := (descMonoidHom_apply_eq t 1).symm.trans (by simp)
      map_mul' x y := by
        change descAddMonoidHom t (x * y) =
          descAddMonoidHom t x * descAddMonoidHom t y
        simp [← descMonoidHom_apply_eq] }
  fac t j := by ext x; exact descAddMonoidHom_quotMk t x
  uniq t m hm := by
    ext ⟨j, x⟩
    exact (ConcreteCategory.congr_hom ((forget SemiRingCat).congr_map (hm j)) x).trans
      (descAddMonoidHom_quotMk t x).symm

/--
Instance `forget₂Mon_preservesFilteredColimits` / 实例 `forget₂Mon_preservesFilteredColimits`

English:
instance forget₂Mon_preservesFilteredColimits
  signature: :
  body: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }

中文:
实例 forget₂Mon_preservesFilteredColimits
  签名: :
  定义体: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }

Depends on / 依赖: Category, FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, SemiRingCat, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ SemiRingCat MonCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }

/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: : PreservesFilteredColimits (forget SemiRingCat.{u})
  body: Limits.comp_preservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})

中文:
实例 forget_preservesFilteredColimits
  签名: : PreservesFilteredColimits (forget SemiRingCat.{u})
  定义体: Limits.comp_preservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})

Depends on / 依赖: Limits, Limits.comp_preservesFilteredColimits, MonCat, SemiRingCat, comp_preservesFilteredColimits, f.hom, forget
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget SemiRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})

end

end SemiRingCat.FilteredColimits

namespace CommSemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommSemiRingCat.{max v u})

/--
Definition of `R` / `R` 的定义

English:
abbreviation R
  signature: : SemiRingCat.{max v u}
  body: SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

中文:
缩写 R
  签名: : SemiRingCat.{max v u}
  定义体: SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

Depends on / 依赖: CommSemiRingCat, FilteredColimits, SemiRingCat, SemiRingCat.FilteredColimits.colimit, colimit
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

/--
Instance `colimitCommSemiring` / 实例 `colimitCommSemiring`

English:
instance colimitCommSemiring
  signature: : CommSemiring.{max v u} R.{v, u} F
  body: { (R F).semiring,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

中文:
实例 colimitCommSemiring
  签名: : CommSemiring.{max v u} R.{v, u} F
  定义体: { (R F).semiring,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

Depends on / 依赖: CommMonCat, CommMonCat.FilteredColimits.colimitCommMonoid, CommSemiRingCat, FilteredColimits, colimitCommMonoid, semiring
-/
instance colimitCommSemiring : CommSemiring.{max v u} R.{v, u} F :=
  { (R F).semiring,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : CommSemiRingCat.{max v u}
  body: CommSemiRingCat.of R.{v, u} F

中文:
定义 colimit
  签名: : CommSemiRingCat.{max v u}
  定义体: CommSemiRingCat.of R.{v, u} F

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.of
-/
def colimit : CommSemiRingCat.{max v u} :=
CommSemiRingCat.of R.{v, u} F

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRin

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRin

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRingCat)).ι.naturality_apply f _ }

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit colimitCocone.{v, u} F
  body: isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit colimitCocone.{v, u} F
  定义体: isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))

Depends on / 依赖: CommSemiRingCat, FilteredColimits, SemiRingCat, SemiRingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
def colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))

/--
Instance `forget₂SemiRing_preservesFilteredColimits` / 实例 `forget₂SemiRing_preservesFilteredColimits`

English:
instance forget₂SemiRing_preservesFilteredColimits
  signature: :
  body: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }

中文:
实例 forget₂SemiRing_preservesFilteredColimits
  签名: :
  定义体: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }

Depends on / 依赖: Category, CommSemiRingCat, FilteredColimits, SemiRingCat, SemiRingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }

/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: :
  body: Limits.comp_preservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})

中文:
实例 forget_preservesFilteredColimits
  签名: :
  定义体: Limits.comp_preservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})

Depends on / 依赖: CommSemiRingCat, Limits, Limits.comp_preservesFilteredColimits, SemiRingCat, comp_preservesFilteredColimits, forget
-/
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommSemiRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})

end

end CommSemiRingCat.FilteredColimits

namespace RingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ RingCat.{max v u})

/--
Definition of `R` / `R` 的定义

English:
abbreviation R
  signature: : SemiRingCat.{max v u}
  body: SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

中文:
缩写 R
  签名: : SemiRingCat.{max v u}
  定义体: SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

Depends on / 依赖: FilteredColimits, RingCat, SemiRingCat, SemiRingCat.FilteredColimits.colimit, colimit
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

/--
Instance `colimitRing` / 实例 `colimitRing`

English:
instance colimitRing
  signature: : Ring.{max v u} R.{v, u} F
  body: { (R F).semiring,
    AddCommGrpCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrpCat.{max v u}) with }

中文:
实例 colimitRing
  签名: : Ring.{max v u} R.{v, u} F
  定义体: { (R F).semiring,
    AddCommGrpCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrpCat.{max v u}) with }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitAddCommGroup, FilteredColimits, RingCat, colimitAddCommGroup, semiring
-/
instance colimitRing : Ring.{max v u} R.{v, u} F :=
  { (R F).semiring,
    AddCommGrpCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrpCat.{max v u}) with }

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : RingCat.{max v u}
  body: RingCat.of R.{v, u} F

中文:
定义 colimit
  签名: : RingCat.{max v u}
  定义体: RingCat.of R.{v, u} F

Depends on / 依赖: RingCat, RingCat.of
-/
def colimit : RingCat.{max v u} :=
RingCat.of R.{v, u} F

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality_apply 

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality_apply 

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality_apply f _ }

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit colimitCocone.{v, u} F
  body: isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit colimitCocone.{v, u} F
  定义体: isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))

Depends on / 依赖: FilteredColimits, RingCat, SemiRingCat, SemiRingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
def colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))

/--
Instance `forget₂SemiRing_preservesFilteredColimits` / 实例 `forget₂SemiRing_preservesFilteredColimits`

English:
instance forget₂SemiRing_preservesFilteredColimits
  signature: :
  body: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }

中文:
实例 forget₂SemiRing_preservesFilteredColimits
  签名: :
  定义体: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }

Depends on / 依赖: Category, FilteredColimits, RingCat, SemiRingCat, SemiRingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ RingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesFilteredColimits (forget₂ RingCat AddCommGrpCat.{u})
  body: { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat AddCommGrpCat.{u})) }

中文:
实例 :
  签名: Limits.PreservesFilteredColimits (forget₂ RingCat AddCommGrpCat.{u})
  定义体: { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat AddCommGrpCat.{u})) }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit, FilteredColimits, Limits, Limits.preservesColimit_of_preserves_colimit_cocone, RingCat, RingCat.FilteredColimits.colimitCoconeIsColimit, colimit, colimit.isColimit, colimitCoconeIsColimit, isColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance : Limits.PreservesFilteredColimits (forget₂ RingCat AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ :=
    { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat AddCommGrpCat.{u})) }

/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: : PreservesFilteredColimits (forget RingCat.{u})
  body: Limits.comp_preservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})

中文:
实例 forget_preservesFilteredColimits
  签名: : PreservesFilteredColimits (forget RingCat.{u})
  定义体: Limits.comp_preservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})

Depends on / 依赖: Limits, Limits.comp_preservesFilteredColimits, RingCat, SemiRingCat, comp_preservesFilteredColimits, forget
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget RingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})

end

end RingCat.FilteredColimits

namespace CommRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{max v u})

/--
Definition of `R` / `R` 的定义

English:
abbreviation R
  signature: : RingCat.{max v u}
  body: RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

中文:
缩写 R
  签名: : RingCat.{max v u}
  定义体: RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

Depends on / 依赖: CommRingCat, FilteredColimits, RingCat, RingCat.FilteredColimits.colimit, colimit
-/
abbrev R : RingCat.{max v u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

/--
Instance `colimitCommRing` / 实例 `colimitCommRing`

English:
instance colimitCommRing
  signature: : CommRing.{max v u} R.{v, u} F
  body: { (R.{v, u} F).ring,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

中文:
实例 colimitCommRing
  签名: : CommRing.{max v u} R.{v, u} F
  定义体: { (R.{v, u} F).ring,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

Depends on / 依赖: CommRingCat, CommSemiRingCat, CommSemiRingCat.FilteredColimits.colimitCommSemiring, FilteredColimits, colimitCommSemiring
-/
instance colimitCommRing : CommRing.{max v u} R.{v, u} F :=
  { (R.{v, u} F).ring,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : CommRingCat.{max v u}
  body: CommRingCat.of R.{v, u} F

中文:
定义 colimit
  签名: : CommRingCat.{max v u}
  定义体: CommRingCat.of R.{v, u} F

Depends on / 依赖: CommRingCat, CommRingCat.of
-/
def colimit : CommRingCat.{max v u} :=
CommRingCat.of R.{v, u} F

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality_apply 

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality_apply 

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X => ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality_apply f _ }

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit colimitCocone.{v, u} F
  body: isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit colimitCocone.{v, u} F
  定义体: isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

Depends on / 依赖: CommRingCat, FilteredColimits, RingCat, RingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
def colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

/--
Instance `forget₂Ring_preservesFilteredColimits` / 实例 `forget₂Ring_preservesFilteredColimits`

English:
instance forget₂Ring_preservesFilteredColimits
  signature: :
  body: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }

中文:
实例 forget₂Ring_preservesFilteredColimits
  签名: :
  定义体: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }

Depends on / 依赖: Category, CommRingCat, FilteredColimits, RingCat, RingCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget₂Ring_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommRingCat RingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }

/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: : PreservesFilteredColimits (forget CommRingCat.{u})
  body: Limits.comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

omit [IsFiltered J] in

中文:
实例 forget_preservesFilteredColimits
  签名: : PreservesFilteredColimits (forget CommRingCat.{u})
  定义体: Limits.comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

omit [IsFiltered J] in

Depends on / 依赖: CommRingCat, Limits, Limits.comp_preservesFilteredColimits, ModuleCat, RingCat, TopCat, TopCat.isLimitConeOfForget, comp_preservesFilteredColimits, forget, getLimitCone, isLimit, isLimitConeOfForget, isLimitOfPreserves, limit.isLimit, mapCone, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

omit [IsFiltered J] in
/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  statement: {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
  proof: by
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift Int))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h => ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_i

中文:
引理 nontrivial
  结论: {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
  证明: by
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift Int))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h => ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_i
-/
protected lemma nontrivial {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [forall i, Nontrivial (F.obj i)] {c : Cocone F} (hc : IsColimit c) : Nontrivial c.pt := by
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift Int))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h => ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget _) hc) _ _).mp h
  exact zero_ne_one (((F.map f).hom.map_zero.symm.trans e).trans (F.map f).hom.map_one)

set_option linter.overlappingInstances false in
omit [IsFiltered J] in
instance {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [HasColimit F] [forall i, Nontrivial (F.obj i)] : Nontrivial ↑(Limits.colimit F) :=
  FilteredColimits.nontrivial (getColimitCocone F).2

end

end CommRingCat.FilteredColimits
