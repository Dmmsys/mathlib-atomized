/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generators of the category of homological complexes

Let `c : ComplexShape ι` be a complex shape with no loop.
If a category `C` has a separator, then `HomologicalComplex C c`
has a separating family, and a separator when suitable coproducts exist.

-/

@[expose] public section

universe t w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] {ι : Type w} (c : ComplexShape ι) [c.HasNoLoop]

section

variable [HasZeroMorphisms C] [HasZeroObject C]

variable {α : Type t} {X : α → C} (hX : ObjectProperty.IsSeparating (.ofObj X))

variable (X) in
/-- If `X : α → C` is a separating family, and `c : ComplexShape ι` has no loop,
then this is a separating family indexed by `α × ι` in `HomologicalComplex C c`,
which consists of homological complexes that are nonzero in at most
two (consecutive) degrees. -/
/-
**HomologicalComplex.separatingFamily** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：separatingFamily (j : α × ι) : HomologicalComplex C c
参数：j : α × ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : α → C` is a separating family, and `c : ComplexShape ι` has no loop,
then this is a separating family indexed by `α × ι` in `HomologicalComplex C c`,
which consists of homological complexes that are nonzero in at most
two (consecutive) degrees.
-/
noncomputable def separatingFamily (j : α × ι) : HomologicalComplex C c :=
  evalCompCoyonedaCorepresentative c (X j.1) j.2

set_option backward.isDefEq.respectTransparency false in
include hX in
/-
**HomologicalComplex.isSeparating_separatingFamily** 是 Mathlib 中的一个引理，位于命名空间 `Ho
mologicalComplex`。
形式化陈述：isSeparating_separatingFamily : ObjectProperty.IsSeparating (.ofObj (separ
atingFamily c X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_comp`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (
Type v)} {X : C}   (e : F.CorepresentableBy X) {Y…
· 使用引理 `CategoryTheory.ObjectProperty.ofObj_apply`：ofObj_apply (i : ι) : ofObj X
 (X i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSeparating_separatingFamily :
    ObjectProperty.IsSeparating (.ofObj (separatingFamily c X)) := by
  intro K L f g h
  ext j
  apply hX
  rintro _ ⟨a⟩ p
  have H := evalCompCoyonedaCorepresentable c (X a) j
  apply H.homEquiv.symm.injective
  simpa only [H.homEquiv_symm_comp] using! h _
    (ObjectProperty.ofObj_apply _ ⟨a, j⟩) (H.homEquiv.symm p)

end

variable [HasCoproductsOfShape ι C] [Preadditive C] [HasZeroObject C]

/-
**HomologicalComplex.isSeparator_coproduct_separatingFamily** 是 Mathlib 中的一个引理，位
于命名空间 `HomologicalComplex`。
形式化陈述：isSeparator_coproduct_separatingFamily {X : C} (hX : IsSeparator X) : IsSe
parator (∐ (fun i => separatingFamily c (fun (_ : Unit) => X) ⟨⟨⟩, i⟩))
参数：hX : IsSeparator X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isSeparator_of_isColimit_cofan`：isSeparator_of_isColimit_
cofan {β : Type w} {f : β -> C} (hf : ObjectProperty.IsSeparating (.ofObj f)) {c
 : Cofan f} (hc : IsColimit c) : Is…
· 使用引理 `HomologicalComplex.isSeparating_separatingFamily`：isSeparating_separatin
gFamily : ObjectProperty.IsSeparating (.ofObj (separatingFamily c X))
· 使用定理 `HomologicalComplex.instHasColimit`：∀ {C : Type u_1} {ι : Type u_2} {J : 
Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isSeparator_coproduct_separatingFamily {X : C} (hX : IsSeparator X) :
    IsSeparator (∐ (fun i ↦ separatingFamily c (fun (_ : Unit) ↦ X) ⟨⟨⟩, i⟩)) := by
  let φ (i : ι) := separatingFamily c (fun (_ : Unit) ↦ X) ⟨⟨⟩, i⟩
  refine isSeparator_of_isColimit_cofan
    (isSeparating_separatingFamily c (X := fun (_ : Unit) ↦ X) (by simpa using! hX))
      (c := Cofan.mk (∐ φ) (fun ⟨_, i⟩ ↦ Sigma.ι φ i)) ?_
  exact IsColimit.ofWhiskerEquivalence
    (Discrete.equivalence (Equiv.punitProd.{0} ι).symm) (coproductIsCoproduct φ)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasSeparator C] : HasSeparator (HomologicalComplex C c) :=
  ⟨_, isSeparator_coproduct_separatingFamily c (isSeparator_separator C)⟩

end HomologicalComplex

