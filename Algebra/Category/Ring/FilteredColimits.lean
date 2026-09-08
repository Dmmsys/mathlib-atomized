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

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

-- This instance is needed below in `colimitSemiring`, during the verification of the
-- semiring axioms.
/-
**SemiRingCat.FilteredColimits.semiringObj** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCa
t.FilteredColimits`。
形式化陈述：semiringObj (j : J) : Semiring (((F ⋙ forget₂ SemiRingCat.{max v u} MonCat
) ⋙ forget MonCat).obj j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiringObj (j : J) :
    Semiring (((F ⋙ forget₂ SemiRingCat.{max v u} MonCat) ⋙ forget MonCat).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)

variable [IsFiltered J]

/-- The colimit of `F ⋙ forget₂ SemiRingCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a semiring.
-/
/-
**SemiRingCat.FilteredColimits.R** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemiRingCat.Filter
edColimits`。
形式化陈述：R : MonCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F ⋙ forget₂ SemiRingCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a semiring.
-/
abbrev R : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

set_option backward.isDefEq.respectTransparency false in
/-
**SemiRingCat.FilteredColimits.colimitSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SemiRi
ngCat.FilteredColimits`。
形式化陈述：colimitSemiring : Semiring.{max v u} R.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitSemiring : Semiring.{max v u} <| R.{v, u} F :=
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

/-- The bundled semiring giving the filtered colimit of a diagram. -/
/-
**SemiRingCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `SemiRingCat.Fi
lteredColimits`。
形式化陈述：colimit : SemiRingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled semiring giving the filtered colimit of a diagram.
-/
def colimit : SemiRingCat.{max v u} :=
  SemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit semiring. -/
/-
**SemiRingCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `SemiRing
Cat.FilteredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit semiring.
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

/-- Auxiliary definition for `colimitCoconeIsColimit`. -/
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom** 是 Mathl
ib 中的一个定义，位于命名空间 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit`。
形式化陈述：descAddMonoidHom : R F ->+ t.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `colimitCoconeIsColimit`.
-/
def descAddMonoidHom : R F →+ t.1 :=
  ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom_quotMk** 
是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit`。
形式化陈述：descAddMonoidHom_quotMk {j : J} (x : F.obj j) : descAddMonoidHom t (Quot.m
k _ ⟨j, x⟩) = t.ι.app j x
参数：x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

/-- Auxiliary definition for `colimitCoconeIsColimit`. -/
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom** 是 Mathlib 
中的一个定义，位于命名空间 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit`。
形式化陈述：descMonoidHom : R F ->* t.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `colimitCoconeIsColimit`.
-/
def descMonoidHom : R F →* t.1 :=
  ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom_quotMk** 是 M
athlib 中的一个引理，位于命名空间 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit`。
形式化陈述：descMonoidHom_quotMk {j : J} (x : F.obj j) : descMonoidHom t (Quot.mk _ ⟨j
, x⟩) = t.ι.app j x
参数：x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma descMonoidHom_quotMk {j : J} (x : F.obj j) :
    descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom_apply_eq** 是
 Mathlib 中的一个引理，位于命名空间 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit`。
形式化陈述：descMonoidHom_apply_eq (x : R F) : descMonoidHom t x = descAddMonoidHom t 
x
参数：x : R F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom_quotMk
`：descMonoidHom_quotMk {j : J} (x : F.obj j) : descMonoidHom t (Quot.mk _ ⟨j, x⟩
) = t.ι.app j x
· 使用引理 `SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom_quo
tMk`：descAddMonoidHom_quotMk {j : J} (x : F.obj j) : descAddMonoidHom t (Quot.mk
 _ ⟨j, x⟩) = t.ι.app j x
-/
lemma descMonoidHom_apply_eq (x : R F) :
    descMonoidHom t x = descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x, descAddMonoidHom_quotMk t x]

end colimitCoconeIsColimit

open colimitCoconeIsColimit in
/-- The proposed colimit cocone is a colimit in `SemiRingCat`. -/
/-
**SemiRingCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`SemiRingCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F where desc t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `SemiRingCat`.
-/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
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
/-
**SemiRingCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat.Fil
teredColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ SemiRingCat MonCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }
/-
**SemiRingCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个
实例，位于命名空间 `SemiRingCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget SemiR
ingCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The colimit of `F ⋙ forget₂ CommSemiRingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
/-
**CommSemiRingCat.FilteredColimits.R** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommSemiRingCa
t.FilteredColimits`。
形式化陈述：R : SemiRingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F ⋙ forget₂ CommSemiRingCat SemiRingCat` in the category `SemiRi
ngCat`.
In the following, we will show that this has the structure of a _commutative_ se
miring.
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})
/-
**CommSemiRingCat.FilteredColimits.colimitCommSemiring** 是 Mathlib 中的一个实例，位于命名空间
 `CommSemiRingCat.FilteredColimits`。
形式化陈述：colimitCommSemiring : CommSemiring.{max v u} R.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitCommSemiring : CommSemiring.{max v u} <| R.{v, u} F :=
  { (R F).semiring,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
/-
**CommSemiRingCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `CommSemiRi
ngCat.FilteredColimits`。
形式化陈述：colimit : CommSemiRingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled commutative semiring giving the filtered colimit of a diagram.
-/
def colimit : CommSemiRingCat.{max v u} :=
  CommSemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative semiring. -/
/-
**CommSemiRingCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Comm
SemiRingCat.FilteredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit commutative semiring.
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRingCat)).ι.naturality_apply f _ }

/-- The proposed colimit cocone is a colimit in `CommSemiRingCat`. -/
/-
**CommSemiRingCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命
名空间 `CommSemiRingCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `CommSemiRingCat`.
-/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))
/-
**CommSemiRingCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRin
gCat.FilteredColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }
/-
**CommSemiRingCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 
中的一个实例，位于命名空间 `CommSemiRingCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommS
emiRingCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The colimit of `F ⋙ forget₂ RingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a ring.
-/
/-
**RingCat.FilteredColimits.R** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingCat.FilteredColimi
ts`。
形式化陈述：R : SemiRingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F ⋙ forget₂ RingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a ring.
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})
/-
**RingCat.FilteredColimits.colimitRing** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Filter
edColimits`。
形式化陈述：colimitRing : Ring.{max v u} R.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitRing : Ring.{max v u} <| R.{v, u} F :=
  { (R F).semiring,
    AddCommGrpCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrpCat.{max v u}) with }

/-- The bundled ring giving the filtered colimit of a diagram. -/
/-
**RingCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.FilteredCo
limits`。
形式化陈述：colimit : RingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled ring giving the filtered colimit of a diagram.
-/
def colimit : RingCat.{max v u} :=
  RingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit ring. -/
/-
**RingCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Filt
eredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit ring.
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality_apply f _ }

/-- The proposed colimit cocone is a colimit in `Ring`. -/
/-
**RingCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Rin
gCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `Ring`.
-/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))
/-
**RingCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.FilteredCol
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂SemiRing_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ RingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }
/-
**RingCat.FilteredColimits.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.FilteredColimits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFilteredColimits (forget₂ RingCat AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ :=
    { preservesColimit := fun {F} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat AddCommGrpCat.{u})) }
/-
**RingCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个实例，位
于命名空间 `RingCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget RingC
at.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The colimit of `F ⋙ forget₂ CommRingCat RingCat` in the category `RingCat`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
/-
**CommRingCat.FilteredColimits.R** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommRingCat.Filter
edColimits`。
形式化陈述：R : RingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F ⋙ forget₂ CommRingCat RingCat` in the category `RingCat`.
In the following, we will show that this has the structure of a _commutative_ ri
ng.
-/
abbrev R : RingCat.{max v u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})
/-
**CommRingCat.FilteredColimits.colimitCommRing** 是 Mathlib 中的一个实例，位于命名空间 `CommRi
ngCat.FilteredColimits`。
形式化陈述：colimitCommRing : CommRing.{max v u} R.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitCommRing : CommRing.{max v u} <| R.{v, u} F :=
  { (R.{v, u} F).ring,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
/-
**CommRingCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Fi
lteredColimits`。
形式化陈述：colimit : CommRingCat.{max v u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled commutative ring giving the filtered colimit of a diagram.
-/
def colimit : CommRingCat.{max v u} :=
  CommRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative ring. -/
/-
**CommRingCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommRing
Cat.FilteredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit commutative ring.
-/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality_apply f _ }

/-- The proposed colimit cocone is a colimit in `CommRingCat`. -/
/-
**CommRingCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CommRingCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit colimitCocone.{v, u} F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `CommRingCat`.
-/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))
/-
**CommRingCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.Fil
teredColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Ring_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommRingCat RingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }
/-
**CommRingCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个
实例，位于命名空间 `CommRingCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommR
ingCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget CommRingCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

omit [IsFiltered J] in
/-
**CommRingCat.FilteredColimits.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat
.FilteredColimits`。
形式化陈述：∀ {J : Type v} [inst : CategoryTheory.SmallCategory J] {F : CategoryTheory
.Functor J CommRingCat}   [CategoryTheory.IsFilteredOrEmpty J] [∀ (i : J), Nontr
ivial ↑(F.obj i)] {c : CategoryTheory.Limits.Cocone F}   (hc : CategoryTheory.Li
mits.IsColimit c), Nontrivial ↑c.pt
参数：i : J；F.obj i；hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
protected lemma nontrivial {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [∀ i, Nontrivial (F.obj i)] {c : Cocone F} (hc : IsColimit c) : Nontrivial c.pt := by
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift ℤ))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h ↦ ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget _) hc) _ _).mp h
  exact zero_ne_one (((F.map f).hom.map_zero.symm.trans e).trans (F.map f).hom.map_one)

set_option linter.overlappingInstances false in
omit [IsFiltered J] in
/-
**CommRingCat.FilteredColimits.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.FilteredC
olimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [HasColimit F] [∀ i, Nontrivial (F.obj i)] : Nontrivial ↑(Limits.colimit F) :=
  FilteredColimits.nontrivial (getColimitCocone F).2

end

end CommRingCat.FilteredColimits

