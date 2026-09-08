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

variable (C : Type u) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace MorphismProperty

open Function

/-- Injectivity (in a concrete category) as a `MorphismProperty` -/
/-
**CategoryTheory.MorphismProperty.injective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     {FC : C →
 C → Type u_1} →       {CC : C → Type u_2} →         [inst_1 : (X Y : C) → FunLi
ke (FC X Y) (CC X) (CC Y)] →           [CategoryTheory.ConcreteCategory C FC] → 
CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Injectivity (in a concrete category) as a `MorphismProperty`
-/
protected def injective : MorphismProperty C := fun _ _ f => Injective f

/-- Surjectivity (in a concrete category) as a `MorphismProperty` -/
/-
**CategoryTheory.MorphismProperty.surjective** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     {FC : C →
 C → Type u_1} →       {CC : C → Type u_2} →         [inst_1 : (X Y : C) → FunLi
ke (FC X Y) (CC X) (CC Y)] →           [CategoryTheory.ConcreteCategory C FC] → 
CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Surjectivity (in a concrete category) as a `MorphismProperty`
-/
protected def surjective : MorphismProperty C := fun _ _ f => Surjective f

/-- Bijectivity (in a concrete category) as a `MorphismProperty` -/
/-
**CategoryTheory.MorphismProperty.bijective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     {FC : C →
 C → Type u_1} →       {CC : C → Type u_2} →         [inst_1 : (X Y : C) → FunLi
ke (FC X Y) (CC X) (CC Y)] →           [CategoryTheory.ConcreteCategory C FC] → 
CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijectivity (in a concrete category) as a `MorphismProperty`
-/
protected def bijective : MorphismProperty C := fun _ _ f => Bijective f
/-
**CategoryTheory.MorphismProperty.bijective_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：bijective_eq_sup : MorphismProperty.bijective C = MorphismProperty.injecti
ve C ⊓ MorphismProperty.surjective C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bijective_eq_sup :
    MorphismProperty.bijective C = MorphismProperty.injective C ⊓ MorphismProperty.surjective C :=
  rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MorphismProperty.injective_respectsIso** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：injective_respectsIso : (MorphismProperty.injective C).RespectsIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeInjective`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C 
→ Type u_2}   [inst_1 : (X Y : C) → FunLike (FC X Y…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance injective_respectsIso : (MorphismProperty.injective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.injective)
/-
**CategoryTheory.MorphismProperty.surjective_respectsIso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：surjective_respectsIso : (MorphismProperty.surjective C).RespectsIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeSurjective`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C
 → Type u_2}   [inst_1 : (X Y : C) → FunLike (FC X Y…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
instance surjective_respectsIso : (MorphismProperty.surjective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.surjective)
/-
**CategoryTheory.MorphismProperty.bijective_respectsIso** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：bijective_respectsIso : (MorphismProperty.bijective C).RespectsIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeBijective`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C 
→ Type u_2}   [inst_1 : (X Y : C) → FunLike (FC X Y…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
instance bijective_respectsIso : (MorphismProperty.bijective C).RespectsIso :=
  respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => ((forget C).mapIso (asIso f)).toEquiv.bijective)

end MorphismProperty

namespace ConcreteCategory

/-- The property that any morphism in a concrete category can be factored as a surjective
map followed by an injective map. -/
/-
**CategoryTheory.ConcreteCategory.HasSurjectiveInjectiveFactorization** 是 Mathli
b 中的一个缩写定义，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：HasSurjectiveInjectiveFactorization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that any morphism in a concrete category can be factored as a surje
ctive
map followed by an injective map.
-/
abbrev HasSurjectiveInjectiveFactorization :=
    (MorphismProperty.surjective C).HasFactorization (MorphismProperty.injective C)

/-- The property that any morphism in a concrete category can be functorially
factored as a surjective map followed by an injective map. -/
/-
**CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization*
* 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：HasFunctorialSurjectiveInjectiveFactorization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that any morphism in a concrete category can be functorially
factored as a surjective map followed by an injective map.
-/
abbrev HasFunctorialSurjectiveInjectiveFactorization :=
  (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

/-- The structure containing the data of a functorial factorization of morphisms as
a surjective map followed by an injective map in a concrete category. -/
/-
**CategoryTheory.ConcreteCategory.FunctorialSurjectiveInjectiveFactorizationData
** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：FunctorialSurjectiveInjectiveFactorizationData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure containing the data of a functorial factorization of morphisms as
a surjective map followed by an injective map in a concrete category.
-/
abbrev FunctorialSurjectiveInjectiveFactorizationData :=
  (MorphismProperty.surjective C).FunctorialFactorizationData (MorphismProperty.injective C)

end ConcreteCategory

open ConcreteCategory

set_option backward.isDefEq.respectTransparency.types false in
/-- In the category of types, any map can be functorially factored as a surjective
map followed by an injective map. -/
/-
**CategoryTheory.functorialSurjectiveInjectiveFactorizationData** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory`。
形式化陈述：functorialSurjectiveInjectiveFactorizationData : FunctorialSurjectiveInjec
tiveFactorizationData (Type u) where Z.obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of types, any map can be functorially factored as a surjective
map followed by an injective map.
-/
def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData (Type u) where
  Z.obj f := Set.range f.hom.hom
  Z.map φ := ↾fun y ↦ ⟨φ.right y.1, by obtain ⟨_, x, rfl⟩ := y; exact ⟨φ.left x, congr_hom φ.w x⟩⟩
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFunctorialSurjectiveInjectiveFactorization (Type u) where
  nonempty_functorialFactorizationData :=
    ⟨functorialSurjectiveInjectiveFactorizationData⟩

end CategoryTheory

