/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Morphisms of sheaves factor as a locally surjective followed by a locally injective morphism

When morphisms in a concrete category `A` factor in a functorial manner as a surjective map
followed by an injective map, we obtain that any morphism of sheaves in `Sheaf J A`
factors in a functorial manner as a locally surjective morphism (which is epi) followed by
a locally injective morphism (which is mono).

Moreover, if we assume that the category of sheaves `Sheaf J A` is balanced
(see `Sites.LeftExact`), then epimorphisms are exactly locally surjective morphisms.

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Category ConcreteCategory CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [J.WEqualsLocallyBijective A]

namespace Sheaf

/-- The class of locally injective morphisms of sheaves, see `Sheaf.IsLocallyInjective`. -/
/-
**CategoryTheory.Sheaf.locallyInjective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Sheaf`。
形式化陈述：locallyInjective : MorphismProperty (Sheaf J A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of locally injective morphisms of sheaves, see `Sheaf.IsLocallyInjecti
ve`.
-/
def locallyInjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallyInjective f

/-- The class of locally surjective morphisms of sheaves, see `Sheaf.IsLocallySurjective`. -/
/-
**CategoryTheory.Sheaf.locallySurjective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sheaf`。
形式化陈述：locallySurjective : MorphismProperty (Sheaf J A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of locally surjective morphisms of sheaves, see `Sheaf.IsLocallySurjec
tive`.
-/
def locallySurjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallySurjective f

section

variable {A}
variable (data : FunctorialSurjectiveInjectiveFactorizationData A) [HasWeakSheafify J A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functorial surjective/injective factorizations of morphisms in a concrete
category `A`, this is the induced functorial locally surjective/locally injective
factorization of morphisms in the category `Sheaf J A`. -/
/-
**CategoryTheory.Sheaf.functorialLocallySurjectiveInjectiveFactorization** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：functorialLocallySurjectiveInjectiveFactorization : (locallySurjective J A
).FunctorialFactorizationData (locallyInjective J A) where Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functorial surjective/injective factorizations of morphisms in a concret
e
category `A`, this is the induced functorial locally surjective/locally injectiv
e
factorization of morphisms in the category `Sheaf J A`.
-/
noncomputable def functorialLocallySurjectiveInjectiveFactorization :
    (locallySurjective J A).FunctorialFactorizationData (locallyInjective J A) where
  Z := (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := whiskerLeft (sheafToPresheaf J A).mapArrow
        (whiskerRight (data.functorCategory Cᵒᵖ).p (presheafToSheaf J A)) ≫
          whiskerLeft Arrow.rightFunc (sheafificationAdjunction J A).counit
  fac := by
    ext f : 2
    dsimp
    simp only [assoc, ← Functor.map_comp_assoc,
      MorphismProperty.FunctorialFactorizationData.fac_app,
      NatIso.isIso_inv_app, IsIso.inv_comp_eq]
    exact (sheafificationAdjunction J A).counit.naturality f.hom
  hi _ := by
    dsimp [locallySurjective]
    rw [← isLocallySurjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.comp_isLocallySurjective_iff, isLocallySurjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallySurjective_of_surjective
    apply (data.functorCategory Cᵒᵖ).hi
  hp _ := by
    dsimp [locallyInjective]
    rw [← isLocallyInjective_sheafToPresheaf_map_iff, Functor.map_comp,
      Presheaf.isLocallyInjective_comp_iff, isLocallyInjective_sheafToPresheaf_map_iff,
      Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallyInjective_of_injective
    apply (data.functorCategory Cᵒᵖ).hp

section

variable (f : Arrow (Sheaf J A))

/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallySurjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hi
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallyInjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hp

variable [J.HasSheafCompose (forget A)]
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply epi_of_isLocallySurjective
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply mono_of_isLocallyInjective

end

/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (locallySurjective J A).HasFunctorialFactorization (locallyInjective J A) where
  nonempty_functorialFactorizationData :=
    ⟨functorialLocallySurjectiveInjectiveFactorization J
      (MorphismProperty.functorialFactorizationData _ _)⟩

end

section

variable {J}
variable [HasSheafify J A] [J.HasSheafCompose (forget A)] [Balanced (Sheaf J A)]
variable {F G : Sheaf J A} (φ : F ⟶ G)

/-
**CategoryTheory.Sheaf.isLocallySurjective_iff_epi'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Sheaf`。
形式化陈述：isLocallySurjective_iff_epi' : IsLocallySurjective φ ↔ Epi φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasFactorizationOfHasFunctorialFacto
rization`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W₁ W₂ 
: CategoryTheory.MorphismProperty C)   [W₁.HasFunctorialFactorization …
· 使用定理 `CategoryTheory.Sheaf.instHasFunctorialFactorizationLocallySurjectiveLoca
llyInjective`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Cate
goryTheory.GrothendieckTopology C) {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.Sheaf.mono_of_isLocallyInjective`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Categor
y.{v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isLocallySurjective_iff_epi' :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mono_of_isLocallyInjective data.p
    have := isIso_of_mono_of_epi data.p
    rw [← data.fac]
    infer_instance

end

end Sheaf

end CategoryTheory

