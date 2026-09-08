/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström.  Following Stenström, one can realize the colon object `r : s` evaluated
at `X : C` as the pullback of `X ⟶ X / r X` along `s (X / r X) ⟶ X / r X`. We encode this
categorically by constructing `Φ : Ψ` as a pullback in the category of endofunctors of the canonical
projection `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_iff` : The morphism `toColon Φ Ψ` is an isomorphism if and only if `Ψ` kills
quotients in the sense that `Φ.quotient ⋙ Ψ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, colon, pullback, torsion theory
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ Ψ : Preradical C)

/-- The cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
/-
**CategoryTheory.Abelian.Preradical.quotient** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Abelian.Preradical`。
形式化陈述：quotient : C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`.
-/
noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

/-- The canonical projection `𝟭 C ⥤ Φ.quotient` where `Φ.quotient` is the cokernel of
`Φ.ι : Φ.r ⟶ 𝟭 C`. -/
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection `𝟭 C ⥤ Φ.quotient` where `Φ.quotient` is the cokernel o
f
`Φ.ι : Φ.r ⟶ 𝟭 C`.
-/
noncomputable def π : 𝟭 C ⟶ Φ.quotient := cokernel.π Φ.ι
  deriving Epi

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_π : Φ.ι ≫ Φ.π = 0 := cokernel.condition _

/-- The canonical cofork `CokernelCofork.ofπ Φ.π Φ.ι_π` exhibits `Φ.π : 𝟭 C ⟶ Φ.quotient` as the
cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
/-
**CategoryTheory.Abelian.Preradical.isColimitCokernelCofork** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ Φ.ι_π)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical cofork `CokernelCofork.ofπ Φ.π Φ.ι_π` exhibits `Φ.π : 𝟭 C ⟶ Φ.quot
ient` as the
cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`.
-/
noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ Φ.ι_π) :=
  cokernelIsCokernel _

/-- The short complex `Φ.r ⟶ 𝟭 C ⟶ Φ.quotient` in the functor category associated to a preradical
`Φ`. -/
@[simps]
/-
**CategoryTheory.Abelian.Preradical.shortComplex** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Abelian.Preradical`。
形式化陈述：shortComplex : ShortComplex (C ⥤ C) where f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Φ.r ⟶ 𝟭 C ⟶ Φ.quotient` in the functor category associated to
 a preradical
`Φ`.
-/
noncomputable def shortComplex : ShortComplex (C ⥤ C) where
  f := Φ.ι
  g := Φ.π

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono Φ.shortComplex.f := by dsimp; infer_instance
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi Φ.shortComplex.g := by dsimp; infer_instance
/-
**CategoryTheory.Abelian.Preradical.shortExact_shortComplex** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：shortExact_shortComplex : Φ.shortComplex.ShortExact where exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.Preradical.instMonoFunctorFShortComplex`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.
Abelian C]   (Φ : CategoryTheory.Abelian.Preradical …
· 使用定理 `CategoryTheory.Abelian.Preradical.instEpiFunctorGShortComplex`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (Φ : CategoryTheory.Abelian.Preradical …
-/
lemma shortExact_shortComplex : Φ.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- The kernel fork `KernelFork.ofι Φ.ι Φ.ι_π` exhibits `Φ.ι : Φ.r ⟶ 𝟭 C` as the kernel
of the canonical projection `Φ.π : 𝟭 C ⟶ Φ.quotient`. -/
/-
**CategoryTheory.Abelian.Preradical.isLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Abelian.Preradical`。
形式化陈述：isLimitKernelFork : IsLimit (KernelFork.ofι _ Φ.ι_π)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Preradical.shortExact_shortComplex`：shortExact_sh
ortComplex : Φ.shortComplex.ShortExact where exact

--- 原说明 ---
The kernel fork `KernelFork.ofι Φ.ι Φ.ι_π` exhibits `Φ.ι : Φ.r ⟶ 𝟭 C` as the ker
nel
of the canonical projection `Φ.π : 𝟭 C ⟶ Φ.quotient`.
-/
noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ Φ.ι_π) :=
  Φ.shortExact_shortComplex.fIsKernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_π_app (X : C) : Φ.ι.app X ≫ Φ.π.app X = 0 := by
  simp [← NatTrans.comp_app]

/-- For `X : C`, the short complex `Φ.r.obj X ⟶ X ⟶ Φ.quotient.obj X` obtained by evaluating
`Φ.shortComplex` at `X`. -/
@[simps]
/-
**CategoryTheory.Abelian.Preradical.shortComplexObj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Abelian.Preradical`。
形式化陈述：shortComplexObj (X : C) : ShortComplex C where f
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `X : C`, the short complex `Φ.r.obj X ⟶ X ⟶ Φ.quotient.obj X` obtained by ev
aluating
`Φ.shortComplex` at `X`.
-/
noncomputable def shortComplexObj (X : C) : ShortComplex C where
  f := Φ.ι.app X
  g := Φ.π.app X
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Mono (Φ.shortComplexObj X).f := by dsimp; infer_instance
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Epi (Φ.shortComplexObj X).g := by dsimp; infer_instance
/-
**CategoryTheory.Abelian.Preradical.shortExact_shortComplexObj** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：shortExact_shortComplexObj (X : C) : (Φ.shortComplexObj X).ShortExact wher
e exact
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.Preradical.shortExact_shortComplex`：shortExact_sh
ortComplex : Φ.shortComplex.ShortExact where exact
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteLimitsFunctorObjEvaluationOfHas
FiniteLimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfH
asFiniteColimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 {K : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Abelian.Preradical.instMonoFShortComplexObj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Abel
ian C]   (Φ : CategoryTheory.Abelian.Preradical …
· 使用定理 `CategoryTheory.Abelian.Preradical.instEpiGShortComplexObj`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   (Φ : CategoryTheory.Abelian.Preradical …
-/
lemma shortExact_shortComplexObj (X : C) : (Φ.shortComplexObj X).ShortExact where
  exact :=
    (ShortComplex.ShortExact.map_of_exact Φ.shortExact_shortComplex ((evaluation C C).obj X)).exact

/-- For `X : C`, the kernel fork `KernelFork.ofι (Φ.ι.app X) (Φ.ι_π_app X)` exhibits
`Φ.ι.app X : Φ.r.obj X ⟶ X` as the kernel of the projection `Φ.π.app X : X ⟶ Φ.quotient.obj X`. -/
/-
**CategoryTheory.Abelian.Preradical.isLimitKernelForkObj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isLimitKernelForkObj (X : C) : IsLimit (KernelFork.ofι _ (Φ.ι_π_app X))
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Preradical.shortExact_shortComplexObj`：shortExact
_shortComplexObj (X : C) : (Φ.shortComplexObj X).ShortExact where exact

--- 原说明 ---
For `X : C`, the kernel fork `KernelFork.ofι (Φ.ι.app X) (Φ.ι_π_app X)` exhibits
`Φ.ι.app X : Φ.r.obj X ⟶ X` as the kernel of the projection `Φ.π.app X : X ⟶ Φ.q
uotient.obj X`.
-/
noncomputable def isLimitKernelForkObj (X : C) : IsLimit (KernelFork.ofι _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplexObj X).fIsKernel

/-- For `X : C`, the cokernel cofork `CokernelCofork.ofπ (Φ.π.app X) (Φ.ι_π_app X)` exhibits
`Φ.π.app X : X ⟶ Φ.quotient.obj X` as the cokernel of `Φ.ι.app X : Φ.r.obj X ⟶ X`. -/
/-
**CategoryTheory.Abelian.Preradical.isColimitCokernelCoforkObj** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isColimitCokernelCoforkObj (X : C) : IsColimit (CokernelCofork.ofπ _ (Φ.ι_
π_app X))
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Preradical.shortExact_shortComplexObj`：shortExact
_shortComplexObj (X : C) : (Φ.shortComplexObj X).ShortExact where exact

--- 原说明 ---
For `X : C`, the cokernel cofork `CokernelCofork.ofπ (Φ.π.app X) (Φ.ι_π_app X)` 
exhibits
`Φ.π.app X : X ⟶ Φ.quotient.obj X` as the cokernel of `Φ.ι.app X : Φ.r.obj X ⟶ X
`.
-/
noncomputable def isColimitCokernelCoforkObj (X : C) :
    IsColimit (CokernelCofork.ofπ _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplexObj X).gIsCokernel

open CategoryTheory.Functor

/-- The colon preradical from Stenström, defined as the pullback of `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient` -/
/-
**CategoryTheory.Abelian.Preradical.colon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.Preradical`。
形式化陈述：colon : Preradical C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colon preradical from Stenström, defined as the pullback of `Φ.π : 𝟭 C ⟶ Φ.q
uotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.
quotient`
-/
noncomputable def colon : Preradical C :=
  MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

/-- The second projection of the pullback defining the colon preradical. -/
/-
**CategoryTheory.Abelian.Preradical.colon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.Preradical`。
形式化陈述：colon : Preradical C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of the pullback defining the colon preradical.
-/
noncomputable def colonπ : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r := pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (colonπ Φ Ψ) := by dsimp [colonπ]; infer_instance
/-
**CategoryTheory.Abelian.Preradical.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
belian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Epi ((colonπ Φ Ψ).app X) := instEpiAppOfFunctor (Φ.colonπ Ψ) X
/-
**CategoryTheory.Abelian.Preradical.isPullback_colon** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.Preradical`。
形式化陈述：isPullback_colon : IsPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π (whiskerLeft 
Φ.quotient Ψ.ι ≫ (rightUnitor _).hom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma isPullback_colon :
    IsPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π
      (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom) :=
  .of_hasPullback _ _
/-
**CategoryTheory.Abelian.Preradical.isPullback_colon_obj** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isPullback_colon_obj (Φ Ψ : Preradical C) (X : C) : IsPullback ((Φ.colon Ψ
).ι.app X) ((Φ.colonπ Ψ).app X) (Φ.π.app X) (Ψ.ι.app (Φ.quotient.obj X))
参数：Φ Ψ : Preradical C；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用引理 `CategoryTheory.Abelian.Preradical.isPullback_colon`：isPullback_colon : I
sPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUni
tor _).hom)
-/
lemma isPullback_colon_obj (Φ Ψ : Preradical C) (X : C) :
    IsPullback ((Φ.colon Ψ).ι.app X) ((Φ.colonπ Ψ).app X)
      (Φ.π.app X) (Ψ.ι.app (Φ.quotient.obj X)) := by
  simpa using (isPullback_colon Φ Ψ).map ((evaluation _ _).obj X)

@[reassoc]
/-
**CategoryTheory.Abelian.Preradical.colon_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colon_ι_app_π_app (Φ Ψ : Preradical C) (X : C) :
    (Φ.colon Ψ).ι.app X ≫ Φ.π.app X = (Φ.colonπ Ψ).app X ≫ Ψ.ι.app (Φ.quotient.obj X) :=
  (isPullback_colon_obj Φ Ψ X).w

/-- There is a morphism `Φ ⟶ (Φ.colon Ψ)` induced by the universal property for the pullback
via `Φ.ι : Φ.r X ⟶ 𝟭 C` and the zero morphism `Φ.r ⟶  Φ.quotient ⋙ Ψ.r`. -/
/-
**CategoryTheory.Abelian.Preradical.toColon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.Preradical`。
形式化陈述：toColon : Φ ⟶ Φ.colon Ψ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Preradical.isPullback_colon`：isPullback_colon : I
sPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUni
tor _).hom)

--- 原说明 ---
There is a morphism `Φ ⟶ (Φ.colon Ψ)` induced by the universal property for the 
pullback
via `Φ.ι : Φ.r X ⟶ 𝟭 C` and the zero morphism `Φ.r ⟶  Φ.quotient ⋙ Ψ.r`.
-/
noncomputable def toColon : Φ ⟶ Φ.colon Ψ :=
  MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.Preradical.toColon_hom_left_colon** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toColon_hom_left_colonπ :
    (toColon Φ Ψ).hom.left ≫ colonπ Φ Ψ = 0 := by
  simp [toColon]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.Preradical.toColon_hom_left_app_colon** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toColon_hom_left_app_colonπ_app (X : C) :
    (toColon Φ Ψ).hom.left.app X ≫ (colonπ Φ Ψ).app X = 0 :=
  NatTrans.congr_app (toColon_hom_left_colonπ Φ Ψ) X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.Preradical.toColon_hom_left_app_colon_** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.Preradical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toColon_hom_left_app_colon_ι_app (X : C) :
    (Φ.toColon Ψ).hom.left.app X ≫ (Φ.colon Ψ).ι.app X = Φ.ι.app X := by
  rw [← NatTrans.comp_app, Over.w]

set_option backward.isDefEq.respectTransparency false in
/-- For `X : C`, the morphism `(toColon Φ Ψ)` is an isomorphism if and only if
`(Ψ.r.obj (Φ.quotient.obj X))` is the zero object. -/
/-
**CategoryTheory.Abelian.Preradical.isIso_toColon_hom_left_app_iff** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Abelian.Preradical`。
形式化陈述：isIso_toColon_hom_left_app_iff {Φ Ψ : Preradical C} {X : C} : IsIso ((toCo
lon Φ Ψ).hom.left.app X) ↔ IsZero (Ψ.r.obj (Φ.quotient.obj X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_epi_eq_zero`：of_epi_eq_zero {X Y : C} (f
 : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y
· 使用定理 `CategoryTheory.Abelian.Preradical.instEpiAppColonπ`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Abelian C]  
 (Φ Ψ : CategoryTheory.Abelian.Preradica…
· 使用定理 `CategoryTheory.Limits.zero_of_epi_comp`：zero_of_epi_comp {X Y Z : C} (f 
: X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Preradical.toColon_hom_left_app_colonπ_app`：toCol
on_hom_left_app_colonπ_app (X : C) : (toColon Φ Ψ).hom.left.app X ≫ (colonπ Φ Ψ)
.app X = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Abelian.Preradical.ι_π_app`：ι_π_app (X : C) : Φ.ι.app X ≫
 Φ.π.app X = 0
· 使用引理 `CategoryTheory.Abelian.Preradical.colon_ι_app_π_app`：colon_ι_app_π_app (
Φ Ψ : Preradical C) (X : C) : (Φ.colon Ψ).ι.app X ≫ Φ.π.app X = (Φ.colonπ Ψ).app
 X ≫ Ψ.ι.app (Φ.quotient.obj X)
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_tgt`：eq_zero_of_tgt {X Y : C} (o
 : IsZero Y) (f : X ⟶ Y) : f = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.Preradical.toColon_hom_left_app_colon_ι_app`：toCo
lon_hom_left_app_colon_ι_app (X : C) : (Φ.toColon Ψ).hom.left.app X ≫ (Φ.colon Ψ
).ι.app X = Φ.ι.app X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
For `X : C`, the morphism `(toColon Φ Ψ)` is an isomorphism if and only if
`(Ψ.r.obj (Φ.quotient.obj X))` is the zero object.
-/
theorem isIso_toColon_hom_left_app_iff {Φ Ψ : Preradical C} {X : C} :
    IsIso ((toColon Φ Ψ).hom.left.app X) ↔ IsZero (Ψ.r.obj (Φ.quotient.obj X)) := by
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero ((colonπ Φ Ψ).app X)
      (zero_of_epi_comp ((toColon Φ Ψ).hom.left.app X) (by simp))
  · obtain ⟨inv, hinv⟩ :=
      KernelFork.IsLimit.lift' (Φ.isLimitKernelForkObj X) ((colon Φ Ψ).ι.app X) (by
        rw [colon_ι_app_π_app, h.eq_zero_of_tgt ((colonπ Φ Ψ).app X), zero_comp])
    dsimp at hinv
    refine ⟨inv, ?_, ?_⟩
    · simp [← cancel_mono (Φ.ι.app X), hinv]
    · simp [← cancel_mono ((Φ.colon Ψ).ι.app X), hinv]

/-- The morphism `(toColon Φ Ψ)` is an isomorphism if and only if `Φ.quotient ⋙ Ψ.r` is the zero
object. -/
/-
**CategoryTheory.Abelian.Preradical.isIso_toColon_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian.Preradical`。
形式化陈述：isIso_toColon_iff {Φ Ψ : Preradical C} : IsIso (toColon Φ Ψ) ↔ IsZero (Φ.q
uotient ⋙ Ψ.r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D] 
  [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.Abelian.Preradical.isIso_toColon_hom_left_app_iff`：isIso_
toColon_hom_left_app_iff {Φ Ψ : Preradical C} {X : C} : IsIso ((toColon Φ Ψ).hom
.left.app X) ↔ IsZero (Ψ.r.obj (Φ.quotient.obj X))

--- 原说明 ---
The morphism `(toColon Φ Ψ)` is an isomorphism if and only if `Φ.quotient ⋙ Ψ.r`
 is the zero
object.
-/
theorem isIso_toColon_iff {Φ Ψ : Preradical C} :
    IsIso (toColon Φ Ψ) ↔ IsZero (Φ.quotient ⋙ Ψ.r) := by
  simpa [MonoOver.isIso_iff_isIso_hom_left, isZero_iff (Φ.quotient ⋙ Ψ.r),
    NatTrans.isIso_iff_isIso_app] using forall_congr' fun x ↦ isIso_toColon_hom_left_app_iff

end Preradical

end CategoryTheory.Abelian

