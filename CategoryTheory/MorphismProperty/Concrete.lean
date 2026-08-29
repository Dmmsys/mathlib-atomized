/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Morphism properties defined in concrete categories

In this file, we define the class of morphisms `MorphismProperty.injective`,
`MorphismProperty.surjective`, `MorphismProperty.bijective` in concrete
categories, and show that it is stable under composition and respects isomorphisms.

We introduce type-classes `HasSurjectiveInjectiveFactorization` and
`HasFunctorialSurjectiveInjectiveFactorization` expressing that in a concrete category `C`,
all morphisms can be factored (resp. factored functorially) as a surjective map
followed by an injective map.

-/

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type*}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace MorphismProperty

open Function

/--
Definition of `injective` / `injective` 的定义

English:
definition injective
  signature: : MorphismProperty C
  body: fun _ _ f => Injective f

中文:
定义 injective
  签名: : MorphismProperty C
  定义体: fun _ _ f => Injective f
-/
protected def injective : MorphismProperty C := fun _ _ f => Injective f

/--
Definition of `surjective` / `surjective` 的定义

English:
definition surjective
  signature: : MorphismProperty C
  body: fun _ _ f => Surjective f

中文:
定义 surjective
  签名: : MorphismProperty C
  定义体: fun _ _ f => Surjective f
-/
protected def surjective : MorphismProperty C := fun _ _ f => Surjective f

/--
Definition of `bijective` / `bijective` 的定义

English:
definition bijective
  signature: : MorphismProperty C
  body: fun _ _ f => Bijective f

中文:
定义 bijective
  签名: : MorphismProperty C
  定义体: fun _ _ f => Bijective f
-/
protected def bijective : MorphismProperty C := fun _ _ f => Bijective f

/--
theorem `bijective_eq_sup` / 定理 `bijective_eq_sup`

English:
theorem bijective_eq_sup
  proof: rfl

中文:
定理 bijective_eq_sup
  证明: rfl
-/
theorem bijective_eq_sup :
    MorphismProperty.bijective C = MorphismProperty.injective C ⊓ MorphismProperty.surjective C :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.injective C).IsMultiplicative
  body: by
    delta MorphismProperty.injective
    convert! injective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.injective
    rw [hom_comp]
    exact hg.comp hf

中文:
实例 :
  签名: (MorphismProperty.injective C).是Multiplicative
  定义体: by
    delta MorphismProperty.injective
    convert! injective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.injective
    rw [hom_comp]
    exact hg.comp hf

Depends on / 依赖: MorphismProperty, MorphismProperty.injective, comp_mem, convert, hg.comp, hom_comp, injective, injective_id
-/
instance : (MorphismProperty.injective C).IsMultiplicative where
  id_mem X := by
    delta MorphismProperty.injective
    convert! injective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.injective
    rw [hom_comp]
    exact hg.comp hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.surjective C).IsMultiplicative
  body: by
    delta MorphismProperty.surjective
    convert! surjective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.surjective
    rw [hom_comp]
    exact hg.comp hf

中文:
实例 :
  签名: (MorphismProperty.surjective C).是Multiplicative
  定义体: by
    delta MorphismProperty.surjective
    convert! surjective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.surjective
    rw [hom_comp]
    exact hg.comp hf

Depends on / 依赖: MorphismProperty, MorphismProperty.surjective, comp_mem, convert, hg.comp, hom_comp, surjective, surjective_id
-/
instance : (MorphismProperty.surjective C).IsMultiplicative where
  id_mem X := by
    delta MorphismProperty.surjective
    convert! surjective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.surjective
    rw [hom_comp]
    exact hg.comp hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.bijective C).IsMultiplicative
  body: by
    delta MorphismProperty.bijective
    convert! bijective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.bijective
    rw [hom_comp]
    exact hg.comp hf

中文:
实例 :
  签名: (MorphismProperty.bijective C).是Multiplicative
  定义体: by
    delta MorphismProperty.bijective
    convert! bijective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.bijective
    rw [hom_comp]
    exact hg.comp hf

Depends on / 依赖: MorphismProperty, MorphismProperty.bijective, bijective, bijective_id, comp_mem, convert, hg.comp, hom_comp
-/
instance : (MorphismProperty.bijective C).IsMultiplicative where
  id_mem X := by
    delta MorphismProperty.bijective
    convert! bijective_id
    aesop
  comp_mem f g hf hg := by
    delta MorphismProperty.bijective
    rw [hom_comp]
    exact hg.comp hf

/--
Instance `injective_respectsIso` / 实例 `injective_respectsIso`

English:
instance injective_respectsIso
  signature: : (MorphismProperty.injective C).RespectsIso
  body: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.injective)

中文:
实例 injective_respectsIso
  签名: : (MorphismProperty.injective C).RespectsIso
  定义体: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.injective)

Depends on / 依赖: forget, injective, mapIso, respectsIso_of_isStableUnderComposition, toEquiv, toEquiv.injective
-/
instance injective_respectsIso : (MorphismProperty.injective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.injective)

/--
Instance `surjective_respectsIso` / 实例 `surjective_respectsIso`

English:
instance surjective_respectsIso
  signature: : (MorphismProperty.surjective C).RespectsIso
  body: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.surjective)

中文:
实例 surjective_respectsIso
  签名: : (MorphismProperty.surjective C).RespectsIso
  定义体: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.surjective)

Depends on / 依赖: forget, mapIso, respectsIso_of_isStableUnderComposition, surjective, toEquiv, toEquiv.surjective
-/
instance surjective_respectsIso : (MorphismProperty.surjective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.surjective)

/--
Instance `bijective_respectsIso` / 实例 `bijective_respectsIso`

English:
instance bijective_respectsIso
  signature: : (MorphismProperty.bijective C).RespectsIso
  body: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.bijective)

中文:
实例 bijective_respectsIso
  签名: : (MorphismProperty.bijective C).RespectsIso
  定义体: respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.bijective)

Depends on / 依赖: bijective, forget, mapIso, respectsIso_of_isStableUnderComposition, toEquiv, toEquiv.bijective
-/
instance bijective_respectsIso : (MorphismProperty.bijective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.bijective)

end MorphismProperty

namespace ConcreteCategory

/--
Definition of `HasSurjectiveInjectiveFactorization` / `HasSurjectiveInjectiveFactorization` 的定义

English:
abbreviation HasSurjectiveInjectiveFactorization
  body: (MorphismProperty.surjective C).HasFactorization (MorphismProperty.injective C)

中文:
缩写 HasSurjectiveInjectiveFactorization
  定义体: (MorphismProperty.surjective C).HasFactorization (MorphismProperty.injective C)

Depends on / 依赖: HasFactorization, MorphismProperty, MorphismProperty.injective, MorphismProperty.surjective, injective, surjective
-/
abbrev HasSurjectiveInjectiveFactorization :=
    (MorphismProperty.surjective C).HasFactorization (MorphismProperty.injective C)

/--
Definition of `HasFunctorialSurjectiveInjectiveFactorization` / `HasFunctorialSurjectiveInjectiveFactorization` 的定义

English:
abbreviation HasFunctorialSurjectiveInjectiveFactorization
  body: (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

中文:
缩写 HasFunctorialSurjectiveInjectiveFactorization
  定义体: (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

Depends on / 依赖: HasFunctorialFactorization, MorphismProperty, MorphismProperty.injective, MorphismProperty.surjective, injective, surjective
-/
abbrev HasFunctorialSurjectiveInjectiveFactorization :=
  (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

/--
Definition of `FunctorialSurjectiveInjectiveFactorizationData` / `FunctorialSurjectiveInjectiveFactorizationData` 的定义

English:
abbreviation FunctorialSurjectiveInjectiveFactorizationData
  body: (MorphismProperty.surjective C).FunctorialFactorizationData (MorphismProperty.injective C)

中文:
缩写 FunctorialSurjectiveInjectiveFactorizationData
  定义体: (MorphismProperty.surjective C).FunctorialFactorizationData (MorphismProperty.injective C)

Depends on / 依赖: FunctorialFactorizationData, MorphismProperty, MorphismProperty.injective, MorphismProperty.surjective, injective, surjective
-/
abbrev FunctorialSurjectiveInjectiveFactorizationData :=
  (MorphismProperty.surjective C).FunctorialFactorizationData (MorphismProperty.injective C)

end ConcreteCategory

open ConcreteCategory

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `functorialSurjectiveInjectiveFactorizationData` / `functorialSurjectiveInjectiveFactorizationData` 的定义

English:
definition functorialSurjectiveInjectiveFactorizationData
  signature: :
  body: Set.range f.hom.hom
  Z.map φ := ↾fun y => ⟨φ.right y.1, by obtain ⟨_, x, rfl⟩ := y; exact ⟨φ.left x, congr_hom φ.w x⟩⟩
  i :=
    { app := fun f => ↾fun x => ⟨f.hom x, ⟨x, rfl⟩⟩
      naturality := fun f g φ => by
        ext x
        exact congr_hom φ.w x }
  p :=
    { app := fun _ => ↾fun y => 

中文:
定义 functorialSurjectiveInjectiveFactorizationData
  签名: :
  定义体: Set.range f.hom.hom
  Z.map φ := ↾fun y => ⟨φ.right y.1, by obtain ⟨_, x, rfl⟩ := y; exact ⟨φ.left x, congr_hom φ.w x⟩⟩
  i :=
    { app := fun f => ↾fun x => ⟨f.hom x, ⟨x, rfl⟩⟩
      naturality := fun f g φ => by
        ext x
        exact congr_hom φ.w x }
  p :=
    { app := fun _ => ↾fun y => 

Depends on / 依赖: Set.range, f.hom.hom
-/
def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData (Type u) where
  Z.obj f := Set.range f.hom.hom
  Z.map φ := ↾fun y => ⟨φ.right y.1, by obtain ⟨_, x, rfl⟩ := y; exact ⟨φ.left x, congr_hom φ.w x⟩⟩
  i :=
    { app := fun f => ↾fun x => ⟨f.hom x, ⟨x, rfl⟩⟩
      naturality := fun f g φ => by
        ext x
        exact congr_hom φ.w x }
  p :=
    { app := fun _ => ↾fun y => y.1
      naturality := by intros; rfl; }
  fac := rfl
  hi := by
    rintro f ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  hp f x₁ x₂ h := by
    rw [Subtype.ext_iff]
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFunctorialSurjectiveInjectiveFactorization (Type u)
  body: ⟨functorialSurjectiveInjectiveFactorizationData⟩

中文:
实例 :
  签名: HasFunctorialSurjectiveInjectiveFactorization (类型u)
  定义体: ⟨functorialSurjectiveInjectiveFactorizationData⟩

Depends on / 依赖: functorialSurjectiveInjectiveFactorizationData
-/
instance : HasFunctorialSurjectiveInjectiveFactorization (Type u) where
  nonempty_functorialFactorizationData :=
    ⟨functorialSurjectiveInjectiveFactorizationData⟩

end CategoryTheory
