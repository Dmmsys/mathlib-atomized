/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphism is a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `StrongMonoCategory` and `StrongEpiCategory` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {P Q : C}

to_dual_name_hint Epi Mono

/--
Definition of `StrongEpi` / `StrongEpi` 的定义

English:
class StrongEpi
  parameters: (f : P ⟶ Q)
  axioms and operations (2):
    - epi : Epi f
    - llp : forall ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

中文:
类 强满态射
  参数: (f : P ⟶ Q)
  公理与运算 (2 个):
    - epi : 满态射 f
    - llp : 对任意 ⦃X Y : C⦄ (z : X ⟶ Y) [单态射 z], 有LiftingProperty f z
-/
class StrongEpi (f : P ⟶ Q) : Prop where
  /-- The epimorphism condition on `f` -/
  epi : Epi f
  /-- The left lifting property with respect to all monomorphisms -/
  llp : forall ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

/-- A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms. -/
@[to_dual]
/--
Definition of `StrongMono` / `StrongMono` 的定义

English:
class StrongMono
  parameters: (f : P ⟶ Q)
  axioms and operations (2):
    - mono : Mono f
    - rlp : forall ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

中文:
类 强单态射
  参数: (f : P ⟶ Q)
  公理与运算 (2 个):
    - mono : 单态射 f
    - rlp : 对任意 ⦃X Y : C⦄ (z : X ⟶ Y) [满态射 z], 有LiftingProperty z f
-/
class StrongMono (f : P ⟶ Q) : Prop where
  /-- The monomorphism condition on `f` -/
  mono : Mono f
  /-- The right lifting property with respect to all epimorphisms -/
  rlp : forall ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

@[to_dual (reorder := hf (X Y, u v))]
/--
theorem `StrongEpi.mk'` / 定理 `StrongEpi.mk'`

English:
theorem StrongEpi.mk'
  statement: {f : P ⟶ Q} [Epi f]
  proof: inferInstance
  llp {X Y} z hz := ⟨fun {u v} sq => hf X Y z hz u v sq⟩

中文:
定理 强满态射.mk'
  结论: {f : P ⟶ Q} [满态射 f]
  证明: inferInstance
  llp {X Y} z hz := ⟨fun {u v} sq => hf X Y z hz u v sq⟩
-/
theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : forall (X Y : C) (z : X ⟶ Y) (_ : Mono z) (u : P ⟶ X)
      (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) : StrongEpi f where
  epi := inferInstance
  llp {X Y} z hz := ⟨fun {u v} sq => hf X Y z hz u v sq⟩

attribute [instance 100] StrongEpi.epi StrongEpi.llp StrongMono.mono StrongMono.rlp

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
@[to_dual /-- The composition of two strong monomorphisms is a strong monomorphism. -/]
/--
Instance `strongEpi_comp` / 实例 `strongEpi_comp`

English:
instance strongEpi_comp
  signature: [StrongEpi f] [StrongEpi g]
  body: { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }

中文:
实例 strongEpi_comp
  签名: [强满态射 f] [强满态射 g]
  定义体: { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }

Depends on / 依赖: epi_comp, infer_instance, intros
-/
instance strongEpi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
@[to_dual (reorder := f g) (rename := f ↔ g, P ↔ R)
/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/]
/--
theorem `strongEpi_of_strongEpi` / 定理 `strongEpi_of_strongEpi`

English:
theorem strongEpi_of_strongEpi
  given: [StrongEpi (f ≫ g)]
  statement: StrongEpi g
  proof: { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.asso

中文:
定理 strongEpi_of_strongEpi
  条件: [强满态射 (f ≫ g)]
  结论: 强满态射 g
  证明: { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.asso

Depends on / 依赖: Category, Category.assoc, CommSq, CommSq.HasLift.mk, CommSq.fac_right, CommSq.mk, HasLift, cancel_mono, epi_of_epi, fac_right, sq.w
-/
theorem strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.assoc, CommSq.fac_right, sq.w], by simp⟩ }

/-- An isomorphism is in particular a strong epimorphism. -/
@[to_dual /-- An isomorphism is in particular a strong monomorphism. -/]
instance (priority := 100) strongEpi_of_isIso [IsIso f] : StrongEpi f where
  epi := by infer_instance
  llp {_ _} _ := HasLiftingProperty.of_left_iso _ _

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/--
theorem `StrongEpi.of_arrow_iso` / 定理 `StrongEpi.of_arrow_iso`

English:
theorem StrongEpi.of_arrow_iso
  statement: {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  proof: by
    rw [Arrow.iso_w' e]
    infer_instance
  llp := fun {X Y} z => by
    intro
    apply HasLiftingProperty.of_arrow_iso_left e z

@[to_dual]

中文:
定理 强满态射.of_arrow_iso
  结论: {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  证明: by
    rw [Arrow.iso_w' e]
    infer_instance
  llp := fun {X Y} z => by
    intro
    apply HasLiftingProperty.of_arrow_iso_left e z

@[to_dual]

Depends on / 依赖: Arrow.iso_w, HasLiftingProperty, HasLiftingProperty.of_arrow_iso_left, infer_instance, iso_w, of_arrow_iso_left
-/
theorem StrongEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongEpi f] : StrongEpi g where
  epi := by
    rw [Arrow.iso_w' e]
    infer_instance
  llp := fun {X Y} z => by
    intro
    apply HasLiftingProperty.of_arrow_iso_left e z

@[to_dual]
/--
theorem `StrongEpi.iff_of_arrow_iso` / 定理 `StrongEpi.iff_of_arrow_iso`

English:
theorem StrongEpi.iff_of_arrow_iso
  statement: {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  proof: by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

中文:
定理 强满态射.iff_of_arrow_iso
  结论: {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  证明: by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

Depends on / 依赖: StrongEpi, StrongEpi.of_arrow_iso, e.symm, exacts, of_arrow_iso
-/
theorem StrongEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongEpi f ↔ StrongEpi g := by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
@[to_dual /-- A strong monomorphism that is an epimorphism is an isomorphism. -/]
/--
theorem `isIso_of_mono_of_strongEpi` / 定理 `isIso_of_mono_of_strongEpi`

English:
theorem isIso_of_mono_of_strongEpi
  given: (f : P ⟶ Q) [Mono f] [StrongEpi f]
  statement: IsIso f
  proof: ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

中文:
定理 isIso_of_mono_of_strongEpi
  条件: (f : P ⟶ Q) [单态射 f] [强满态射 f]
  结论: 是同构 f
  证明: ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

Depends on / 依赖: CommSq, CommSq.mk
-/
theorem isIso_of_mono_of_strongEpi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

section

variable (C)

/--
Definition of `StrongEpiCategory` / `StrongEpiCategory` 的定义

English:
class StrongEpiCategory
  parameters: : Prop where
  axioms and operations (1):
    - strongEpi_of_epi : forall {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

中文:
类 强满态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - strongEpi_of_epi : 对任意 {X Y : C} (f : X ⟶ Y) [满态射 f], 强满态射 f
-/
class StrongEpiCategory : Prop where
  /-- A strong epi category is a category in which every epimorphism is strong. -/
  strongEpi_of_epi : forall {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

/-- A strong mono category is a category in which every monomorphism is strong. -/
@[to_dual]
/--
Definition of `StrongMonoCategory` / `StrongMonoCategory` 的定义

English:
class StrongMonoCategory
  parameters: : Prop where
  axioms and operations (1):
    - strongMono_of_mono : forall {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

中文:
类 强单态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - strongMono_of_mono : 对任意 {X Y : C} (f : X ⟶ Y) [单态射 f], 强单态射 f
-/
class StrongMonoCategory : Prop where
  /-- A strong mono category is a category in which every monomorphism is strong. -/
  strongMono_of_mono : forall {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

end

@[to_dual]
/--
theorem `strongEpi_of_epi` / 定理 `strongEpi_of_epi`

English:
theorem strongEpi_of_epi
  given: [StrongEpiCategory C] (f : P ⟶ Q) [Epi f]
  statement: StrongEpi f
  proof: StrongEpiCategory.strongEpi_of_epi _

中文:
定理 strongEpi_of_epi
  条件: [强满态射范畴 C] (f : P ⟶ Q) [满态射 f]
  结论: 强满态射 f
  证明: StrongEpiCategory.strongEpi_of_epi _

Depends on / 依赖: StrongEpiCategory, StrongEpiCategory.strongEpi_of_epi, strongEpi_of_epi
-/
theorem strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strongEpi_of_epi _

section

attribute [local instance] strongEpi_of_epi

@[to_dual]
instance (priority := 100) balanced_of_strongEpiCategory [StrongEpiCategory C] : Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_mono_of_strongEpi _

end

end CategoryTheory
