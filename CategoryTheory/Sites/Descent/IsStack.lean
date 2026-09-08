/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Stacks: effectiveness of descent

Let `C` be a category with a Grothendieck topology `J` and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
In this file, we define the typeclass `F.IsStack J` saying that `F` is a stack for `J`.
(See the terminological note in the file `Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`:
we do not require that the categories `F.obj (.mk (op S))` are groupoids.)

The typeclass `IsStack` extends `IsPrestack`. The effectiveness of descent that
is required for stacks is expressed by saying that the functors `toDescentData`
attached to covering sieves are essentially surjective. Together with the
`IsPrestack` assumption, we get that these functors are actually equivalences of
categories (see `isEquivalence_toDescentData`). Conversely, we provide a
constructor `IsStack.of_isStackFor` which assumes that these functors are
equivalences of categories.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

public section

universe t t' v' v u' u

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
has effective descent for a Grothendieck topology, i.e. is a stack.
(See the terminological note in the introduction of the file
`Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`.) -/
@[stacks 026F]
/-
**CategoryTheory.Pseudofunctor.IsStack** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Pseudofunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat →   
    CategoryTheory.GrothendieckTopology C → Prop
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
has effective descent for a Grothendieck topology, i.e. is a stack.
(See the terminological note in the introduction of the file
`Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`.)
-/
class IsStack (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C) : Prop
    extends F.IsPrestack J where
  essSurj_of_sieve (F) {S : C} (R : Sieve S) (hR : R ∈ J S) :
    (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).EssSurj

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C}

/-- Version of `isStackFor` for a sieve instead of a presieve. -/
/-
**CategoryTheory.Pseudofunctor.isStackFor'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Pseudofunctor`。
形式化陈述：isStackFor' [F.IsStack J] {S : C} (R : Sieve S) (hR : R in J S) : F.IsStac
kFor R.arrows
参数：R : Sieve S；hR : R in J S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.isStackFor_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C]   (F : CategoryTheory.Pseudofunctor (CategoryTheor
y.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用引理 `CategoryTheory.Pseudofunctor.isPrestackFor'`：isPrestackFor' [F.IsPrestac
k J] {S : C} (R : Sieve S) (hR : R in J S) : F.IsPrestackFor R.arrows
· 使用定理 `CategoryTheory.Pseudofunctor.IsStack.toIsPrestack`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C}   {F : CategoryTheory.Pseudofunctor (Categor
yTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
· 使用定理 `CategoryTheory.Pseudofunctor.IsStack.essSurj_of_sieve`：∀ {C : Type u} {i
nst : CategoryTheory.Category.{v, u} C}   (F : CategoryTheory.Pseudofunctor (Cat
egoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…

--- 原说明 ---
Version of `isStackFor` for a sieve instead of a presieve.
-/
lemma isStackFor' [F.IsStack J] {S : C} (R : Sieve S) (hR : R ∈ J S) :
    F.IsStackFor R.arrows := by
  rw [isStackFor_iff]
  have hF := (F.isPrestackFor' _ hR).fullyFaithful
  have := hF.full
  have := hF.faithful
  have := IsStack.essSurj_of_sieve F _ hR
  exact { }
/-
**CategoryTheory.Pseudofunctor.isStackFor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Pseudofunctor`。
形式化陈述：isStackFor [F.IsStack J] {S : C} (R : Presieve S) (hR : Sieve.generate R i
n J S) : F.IsStackFor R
参数：R : Presieve S；hR : Sieve.generate R in J S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.isStackFor'`：isStackFor' [F.IsStack J] {S :
 C} (R : Sieve S) (hR : R in J S) : F.IsStackFor R.arrows
-/
lemma isStackFor [F.IsStack J] {S : C} (R : Presieve S) (hR : Sieve.generate R ∈ J S) :
    F.IsStackFor R := by
  simpa using F.isStackFor' _ hR
/-
**CategoryTheory.Pseudofunctor.isEquivalence_toDescentData** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isEquivalence_toDescentData [F.IsStack J] {ι : Type t} {S : C} {X : ι -> C
} (f : forall i, X i ⟶ S) (hf : Sieve.ofArrows _ f in J S) : (F.toDescentData f)
.IsEquivalence
参数：f : forall i, X i ⟶ S；hf : Sieve.ofArrows _ f in J S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Pseudofunctor.isStackFor_ofArrows_iff`：isStackFor_ofArrow
s_iff : F.IsStackFor (Presieve.ofArrows _ f) ↔ (F.toDescentData f).IsEquivalence
· 使用引理 `CategoryTheory.Pseudofunctor.IsStackFor_generate_iff`：IsStackFor_generat
e_iff (R : Presieve S) : F.IsStackFor (Sieve.generate R).arrows ↔ F.IsStackFor R
· 使用引理 `CategoryTheory.Pseudofunctor.isStackFor`：isStackFor [F.IsStack J] {S : C
} (R : Presieve S) (hR : Sieve.generate R in J S) : F.IsStackFor R
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
-/
lemma isEquivalence_toDescentData [F.IsStack J]
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) :
    (F.toDescentData f).IsEquivalence := by
  rw [← isStackFor_ofArrows_iff, ← IsStackFor_generate_iff]
  exact F.isStackFor _ (by simpa)

variable {F} in
/-
**CategoryTheory.Pseudofunctor.IsStack.of_isStackFor** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Pseudofunctor.IsStack`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTh
eory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat}   {J
 : CategoryTheory.GrothendieckTopology C}, (∀ (S : C), ∀ R ∈ J S, F.IsStackFor R
.arrows) → F.IsStack J
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；∀ (S : C), ∀ R ∈ J S, F.IsStackFor R.arrow
s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.IsPrestack.of_isPrestackFor`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Pseudofunctor (
CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `CategoryTheory.Pseudofunctor.IsStackFor.isPrestackFor`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Pseudofunctor (Cat
egoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Pseudofunctor.isStackFor_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C]   (F : CategoryTheory.Pseudofunctor (CategoryTheor
y.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma IsStack.of_isStackFor
    (hF : ∀ (S : C) (R : Sieve S) (_ : R ∈ J S), F.IsStackFor R.arrows) :
    F.IsStack J where
  toIsPrestack := .of_isPrestackFor (fun _ _ hR ↦ (hF _ _ hR).isPrestackFor)
  essSurj_of_sieve R hR := by
    have := (isStackFor_iff _ _).1 (hF _ _ hR)
    infer_instance

end Pseudofunctor

end CategoryTheory

