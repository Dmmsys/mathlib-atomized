/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHaus.Limits
public import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
/-!

# Effective epimorphisms in `CompHaus`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `CompHaus`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `CompHaus` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `CompHaus` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.

## Projects

- Define regular categories, and show that `CompHaus` is regular.
- Define coherent categories, and show that `CompHaus` is actually coherent.

-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace CompHaus

open List in
/-
**CompHaus.effectiveEpi_tfae** 是 Mathlib 中的一个定理，位于命名空间 `CompHaus`。
形式化陈述：effectiveEpi_tfae {B X : CompHaus.{u}} (π : X ⟶ B) : TFAE [ EffectiveEpi π
 , Epi π , Function.Surjective π ]
参数：π : X ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.epi_iff_surjective`：epi_iff_surjective {X Y : CompHaus.{u}} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem effectiveEpi_tfae
    {B X : CompHaus.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 ↔ 3 := epi_iff_surjective π
  tfae_have 3 → 1 := fun hπ ↦ ⟨⟨effectiveEpiStruct π hπ⟩⟩
  tfae_finish
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preregular CompHaus :=
  preregular fun _ _ _ ↦ ((effectiveEpi_tfae _).out 0 2).mp
/-
**CompHaus.** 是 Mathlib 中的一个示例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Precoherent CompHaus.{u} := inferInstance

set_option backward.isDefEq.respectTransparency false in
-- TODO: prove this for `Type*`
open List in
/-
**CompHaus.effectiveEpiFamily_tfae** 是 Mathlib 中的一个定理，位于命名空间 `CompHaus`。
形式化陈述：effectiveEpiFamily_tfae {α : Type} [Finite α] {B : CompHaus.{u}} (X : α ->
 CompHaus.{u}) (π : (a : α) -> (X a ⟶ B)) : TFAE [ EffectiveEpiFamily X π , Epi 
(Sigma.desc π) , forall b : B, exists (a : α) (x : X a), π a x = b ]
参数：X : α -> CompHaus.{u}；π : (a : α) -> (X a ⟶ B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.instHasCoproduct`：∀ {P : TopCat → Prop} {α : Type w} [Finit
e α] (X : α → CompHausLike P) [CompHausLike.HasExplicitFiniteCoproduct X],   Cat
egoryTheory.Limits.…
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompHaus.effectiveEpi_tfae`：effectiveEpi_tfae {B X : CompHaus.{u}} (π : 
X ⟶ B) : TFAE [ EffectiveEpi π , Epi π , Function.Surjective π ]
· 使用定理 `CategoryTheory.instEffectiveEpiDescOfEffectiveEpiFamily`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} (X : α → 
C)   (π : (a : α) → X a ⟶ B) [inst_1 : Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompHaus.epi_iff_surjective`：epi_iff_surjective {X Y : CompHaus.{u}} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom_assoc`：∀
 {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 
: CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 → 2
  | _ => inferInstance
  tfae_have 3 → 2
  | e => by
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 → 3
  | e => by
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    change _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish
/-
**CompHaus.effectiveEpiFamily_of_jointly_surjective** 是 Mathlib 中的一个定理，位于命名空间 `C
ompHaus`。
形式化陈述：effectiveEpiFamily_of_jointly_surjective {α : Type} [Finite α] {B : CompHa
us.{u}} (X : α -> CompHaus.{u}) (π : (a : α) -> (X a ⟶ B)) (surj : forall b : B,
 exists (a : α) (x : X a), π a x = b) : EffectiveEpiFamily X π
参数：X : α -> CompHaus.{u}；π : (a : α) -> (X a ⟶ B)；surj : forall b : B, exists (a
 : α) (x : X a), π a x = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompHausLike.instHasCoproduct`：∀ {P : TopCat → Prop} {α : Type w} [Finit
e α] (X : α → CompHausLike P) [CompHausLike.HasExplicitFiniteCoproduct X],   Cat
egoryTheory.Limits.…
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `CompHaus.effectiveEpiFamily_tfae`：effectiveEpiFamily_tfae {α : Type} [Fi
nite α] {B : CompHaus.{u}} (X : α -> CompHaus.{u}) (π : (a : α) -> (X a ⟶ B)) : 
TFAE [ EffectiveEpiFam…
-/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end CompHaus

