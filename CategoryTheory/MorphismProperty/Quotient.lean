/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Classes of morphisms induced on quotient categories

Let `W : MorphismProperty C` and `homRel : HomRel C`. We assume that
`homRel` is stable under pre- and postcomposition. We introduce a property
`W.HasQuotient homRel` expressing that `W` induces a property of
morphisms on the quotient category, i.e. `W f ↔ W g` when `homRel f g` holds.
We denote `W.quotient homRel : MorphismProperty (Quotient homRel)` the
induced property of morphisms: a morphism in `C` satisfies `W` iff
`(Quotient.functor homRel).map f` does.

-/

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category* C]

/-- Let `W : MorphismProperty C` and `homRel : HomRel C`. We say that `W` induces
a class of morphisms on the quotient category by `homRel` if `homRel` is stable under
pre- and postcomposition and if `W f ↔ W g` whenever `homRel f g` hold. -/
/-
**CategoryTheory.MorphismProperty.HasQuotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C →       (homRel : HomRel C) →         [CategoryTh
eory.HomRel.IsStableUnderPrecomp homRel] →           [CategoryTheory.HomRel.IsSt
ableUnderPostcomp homRel] → Prop
参数：homRel : HomRel C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `W : MorphismProperty C` and `homRel : HomRel C`. We say that `W` induces
a class of morphisms on the quotient category by `homRel` if `homRel` is stable 
under
pre- and postcomposition and if `W f ↔ W g` whenever `homRel f g` hold.
-/
class HasQuotient (W : MorphismProperty C) (homRel : HomRel C)
    [HomRel.IsStableUnderPrecomp homRel]
    [HomRel.IsStableUnderPostcomp homRel] : Prop where
  iff (W) : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g → (W f ↔ W g)

variable (W : MorphismProperty C) {homRel : HomRel C}
  [HomRel.IsStableUnderPrecomp homRel]
  [HomRel.IsStableUnderPostcomp homRel]
/-
**CategoryTheory.MorphismProperty.HasQuotient.iff_of_eqvGen** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MorphismProperty.HasQuotient`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Catego
ryTheory.MorphismProperty C)   {homRel : HomRel C} [inst_1 : CategoryTheory.HomR
el.IsStableUnderPrecomp homRel]   [inst_2 : CategoryTheory.HomRel.IsStableUnderP
ostcomp homRel] [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y},   Relation.EqvGe
n homRel f g → (W f ↔ W g)
参数：W : CategoryTheory.MorphismProperty C；W f ↔ W g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasQuotient.iff`：∀ {C : Type u_1} {inst 
: CategoryTheory.Category.{v_1, u_1} C} (W : CategoryTheory.MorphismProperty C) 
  {homRel : HomRel C} {inst_1 : Categ…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
lemma HasQuotient.iff_of_eqvGen [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y}
    (h : Relation.EqvGen (@homRel _ _) f g) : W f ↔ W g := by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

variable (homRel)

/-- The property of morphisms that is induced by `W : MorphismProperty C`
on the quotient category by `homRel : HomRel C` when `W.HasQuotient homRel` holds. -/
@[nolint unusedArguments]
/-
**CategoryTheory.MorphismProperty.quotient** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：quotient [W.HasQuotient homRel] : MorphismProperty (Quotient homRel)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of morphisms that is induced by `W : MorphismProperty C`
on the quotient category by `homRel : HomRel C` when `W.HasQuotient homRel` hold
s.
-/
def quotient [W.HasQuotient homRel] : MorphismProperty (Quotient homRel) :=
  fun ⟨X⟩ ⟨Y⟩ f ↦ ∃ (f' : X ⟶ Y) (_ : W f'), f = (Quotient.functor _).map f'

variable [W.HasQuotient homRel]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.quotient_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：quotient_iff {X Y : C} (f : X ⟶ Y) : W.quotient homRel ((Quotient.functor 
homRel).map f) ↔ W f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.HasQuotient.iff_of_eqvGen`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : CategoryTheory.MorphismPr
operty C)   {homRel : HomRel C} [inst_1 : Categ…
· 使用定理 `CategoryTheory.HomRel.compClosure_eq_self`：compClosure_eq_self : CompClo
sure r = r
· 使用定理 `CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen`：functor_ho
mRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) : (functor r).homRel f g ↔ Re
lation.EqvGen (@HomRel.CompClosure C _ r X Y) f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.homRel_iff`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (F : Categor…
-/
lemma quotient_iff {X Y : C} (f : X ⟶ Y) :
    W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f := by
  refine ⟨fun ⟨f', hf', h⟩ ↦ ?_, fun hf ↦ ⟨f, hf, rfl⟩⟩
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self homRel] at h
  rwa [HasQuotient.iff_of_eqvGen W h]
/-
**CategoryTheory.MorphismProperty.eq_inverseImage_quotientFunctor** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：eq_inverseImage_quotientFunctor : W = (W.quotient homRel).inverseImage (Qu
otient.functor _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.MorphismProperty.quotient_iff`：quotient_iff {X Y : C} (f 
: X ⟶ Y) : W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f
-/
lemma eq_inverseImage_quotientFunctor :
    W = (W.quotient homRel).inverseImage (Quotient.functor _) := by
  ext
  exact (quotient_iff _ _ _).symm

end MorphismProperty

end CategoryTheory

