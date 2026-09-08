/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour, Nima Rasekh
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi
public import Mathlib.Topology.Category.Stonean.Limits
/-!

# Effective epimorphisms in `Stonean`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `Stonean`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `Stonean` is `Preregular`
and `Precoherent`.

We also prove that for a finite family of morphisms in `Stonean` with fixed
target, the conditions jointly surjective, jointly epimorphic and effective epimorphic are all
equivalent.
-/

@[expose] public section

universe u

open CategoryTheory Limits CompHausLike

namespace Stonean

open List in
/-
**Stonean.effectiveEpi_tfae** 是 Mathlib 中的一个定理，位于命名空间 `Stonean`。
形式化陈述：effectiveEpi_tfae {B X : Stonean.{u}} (π : X ⟶ B) : TFAE [ EffectiveEpi π 
, Epi π , Function.Surjective π ]
参数：π : X ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Stonean.epi_iff_surjective`：epi_iff_surjective {X Y : Stonean} (f : X ⟶ 
Y) : Epi f ↔ Function.Surjective f
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem effectiveEpi_tfae
    {B X : Stonean.{u}} (π : X ⟶ B) :
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
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toCompHaus.PreservesEffectiveEpis where
  preserves f h :=
    ((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mpr
      (((Stonean.effectiveEpi_tfae f).out 0 2).mp h)
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toCompHaus.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr
      (((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 0 2).mp h)

/--
An effective presentation of an `X : CompHaus` with respect to the inclusion functor from `Stonean`
-/
/-
**Stonean.stoneanToCompHausEffectivePresentation** 是 Mathlib 中的一个定义，位于命名空间 `Ston
ean`。
形式化陈述：stoneanToCompHausEffectivePresentation (X : CompHaus) : Stonean.toCompHaus
.EffectivePresentation X where p
参数：X : CompHaus。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An effective presentation of an `X : CompHaus` with respect to the inclusion fun
ctor from `Stonean`
-/
noncomputable def stoneanToCompHausEffectivePresentation (X : CompHaus) :
    Stonean.toCompHaus.EffectivePresentation X where
  p := X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toCompHaus.EffectivelyEnough where
  presentation X := ⟨stoneanToCompHausEffectivePresentation X⟩
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preregular Stonean := Stonean.toCompHaus.reflects_preregular
/-
**Stonean.** 是 Mathlib 中的一个示例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Precoherent Stonean.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
/-
**Stonean.effectiveEpiFamily_tfae** 是 Mathlib 中的一个定理，位于命名空间 `Stonean`。
形式化陈述：effectiveEpiFamily_tfae {α : Type} [Finite α] {B : Stonean.{u}} (X : α -> 
Stonean.{u}) (π : (a : α) -> (X a ⟶ B)) : TFAE [ EffectiveEpiFamily X π , Epi (S
igma.desc π) , forall b : B, exists (a : α) (x : X a), π a x = b ]
参数：X : α -> Stonean.{u}；π : (a : α) -> (X a ⟶ B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.instHasCoproduct`：∀ {P : TopCat → Prop} {α : Type w} [Finit
e α] (X : α → CompHausLike P) [CompHausLike.HasExplicitFiniteCoproduct X],   Cat
egoryTheory.Limits.…
· 使用定理 `Stonean.instHasPropExtremallyDisconnectedCarrier`：∀ (X : Type u_1) [inst
 : TopologicalSpace X] [ExtremallyDisconnected X],   CompHausLike.HasProp (fun Y
 => ExtremallyDisconnected ↑Y) X
· 使用定理 `Stonean.instExtremallyDisconnectedCarrierToTop`：∀ (X : Stonean), Extrema
llyDisconnected ↑X.toTop
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
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Stonean.effectiveEpi_tfae`：effectiveEpi_tfae {B X : Stonean.{u}} (π : X 
⟶ B) : TFAE [ EffectiveEpi π , Epi π , Function.Surjective π ]
· 使用定理 `CategoryTheory.instEffectiveEpiDescOfEffectiveEpiFamily`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} (X : α → 
C)   (π : (a : α) → X a ⟶ B) [inst_1 : Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `CompHaus.effectiveEpiFamily_tfae`：effectiveEpiFamily_tfae {α : Type} [Fi
nite α] {B : CompHaus.{u}} (X : α -> CompHaus.{u}) (π : (a : α) -> (X a ⟶ B)) : 
TFAE [ EffectiveEpiFam…
· 使用引理 `CategoryTheory.Functor.finite_effectiveEpiFamily_of_map`：finite_effectiv
eEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F] {α : Type} 
[Finite α] {B : C} (X : α -> C) (π : (a : α) …
· 使用定理 `CategoryTheory.instReflectsFiniteEffectiveEpiFamiliesOfReflectsEffective
Epis`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.FinitaryPreExtensive C] {D : Type u_2}   [inst_2 : CategoryTh…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHausLike.instPreservesFiniteCoproductsToCompHausLike`：∀ {P : TopCat 
→ Prop} [CompHausLike.HasExplicitFiniteCoproducts P] {P' : TopCat → Prop}   (h :
 ∀ (X : CompHausLike P), P X.toTop → P' X.toTo…
· 使用定理 `Stonean.instReflectsEffectiveEpisCompHausToCompHaus`：Stonean.toCompHaus.
ReflectsEffectiveEpis
· 使用定理 `CategoryTheory.instPreservesFiniteEffectiveEpiFamiliesOfPreservesEffecti
veEpis`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [Category
Theory.FinitaryPreExtensive C] {D : Type u_2}   [inst_2 : CategoryTh…
· 使用定理 `Stonean.instPreservesEffectiveEpisCompHausToCompHaus`：Stonean.toCompHaus
.PreservesEffectiveEpis
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  | _ => by
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 3 ↔ 1 := by
    erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a ↦ Stonean.toCompHaus.obj (X a)) (fun a ↦ Stonean.toCompHaus.map (π a))).out 2 0 :)]
    exact ⟨fun h ↦ Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
      fun _ ↦ inferInstance⟩
  tfae_finish
/-
**Stonean.effectiveEpiFamily_of_jointly_surjective** 是 Mathlib 中的一个定理，位于命名空间 `St
onean`。
形式化陈述：effectiveEpiFamily_of_jointly_surjective {α : Type} [Finite α] {B : Stonea
n.{u}} (X : α -> Stonean.{u}) (π : (a : α) -> (X a ⟶ B)) (surj : forall b : B, e
xists (a : α) (x : X a), π a x = b) : EffectiveEpiFamily X π
参数：X : α -> Stonean.{u}；π : (a : α) -> (X a ⟶ B)；surj : forall b : B, exists (a 
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
· 使用定理 `Stonean.instHasPropExtremallyDisconnectedCarrier`：∀ (X : Type u_1) [inst
 : TopologicalSpace X] [ExtremallyDisconnected X],   CompHausLike.HasProp (fun Y
 => ExtremallyDisconnected ↑Y) X
· 使用定理 `Stonean.instExtremallyDisconnectedCarrierToTop`：∀ (X : Stonean), Extrema
llyDisconnected ↑X.toTop
· 使用定理 `Stonean.effectiveEpiFamily_tfae`：effectiveEpiFamily_tfae {α : Type} [Fin
ite α] {B : Stonean.{u}} (X : α -> Stonean.{u}) (π : (a : α) -> (X a ⟶ B)) : TFA
E [ EffectiveEpiFamil…
-/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end Stonean

