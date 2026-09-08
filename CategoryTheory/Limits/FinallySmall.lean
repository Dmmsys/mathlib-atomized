/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Logic.Small.Set
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Finally small categories

A category given by `(J : Type u) [Category.{v} J]` is `w`-finally small if there exists a
`FinalModel J : Type w` equipped with `[SmallCategory (FinalModel J)]` and a final functor
`FinalModel J ⥤ J`.

This means that if a category `C` has colimits of size `w` and `J` is `w`-finally small, then
`C` has colimits of shape `J`. In this way, the notion of "finally small" can be seen as a
generalization of the notion of "essentially small" for indexing categories of colimits.

Dually, we have a notion of initially small category.

We show that a finally small category admits a small weakly terminal set, i.e., a small set `s` of
objects such that from every object there is a morphism to a member of `s`. We also show that the
converse holds if `J` is filtered.
-/

@[expose] public section

universe w w' v v₁ u u₁

open CategoryTheory Functor

namespace CategoryTheory

section FinallySmall

variable (J : Type u) [Category.{v} J]

/-- A category is `FinallySmall.{w}` if there is a final functor from a `w`-small category. -/
/-
**CategoryTheory.FinallySmall** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type u) → [CategoryTheory.Category.{v, u} J] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is `FinallySmall.{w}` if there is a final functor from a `w`-small ca
tegory.
-/
class FinallySmall : Prop where
  /-- There is a final functor from a small category. -/
  final_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F

/-- Constructor for `FinallySmall C` from an explicit small category witness. -/
/-
**CategoryTheory.FinallySmall.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fina
llySmall`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {S : Type w} [ins
t_1 : CategoryTheory.SmallCategory S]   (F : CategoryTheory.Functor S J) [F.Fina
l], CategoryTheory.FinallySmall J
参数：F : CategoryTheory.Functor S J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `FinallySmall C` from an explicit small category witness.
-/
theorem FinallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Final F] : FinallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/-- An arbitrarily chosen small model for a finally small category. -/
/-
**CategoryTheory.FinalModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：FinalModel [FinallySmall.{w} J] : Type w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.final_smallCategory`：∀ {J : Type u} {inst : 
CategoryTheory.Category.{v, u} J} [self : CategoryTheory.FinallySmall J], ∃ S x 
F, F.Final

--- 原说明 ---
An arbitrarily chosen small model for a finally small category.
-/
def FinalModel [FinallySmall.{w} J] : Type w :=
  Classical.choose (@FinallySmall.final_smallCategory J _ _)
/-
**CategoryTheory.smallCategoryFinalModel** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：smallCategoryFinalModel [FinallySmall.{w} J] : SmallCategory (FinalModel J
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.final_smallCategory`：∀ {J : Type u} {inst : 
CategoryTheory.Category.{v, u} J} [self : CategoryTheory.FinallySmall J], ∃ S x 
F, F.Final
-/
noncomputable instance smallCategoryFinalModel [FinallySmall.{w} J] :
    SmallCategory (FinalModel J) :=
  Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))

/-- An arbitrarily chosen final functor `FinalModel J ⥤ J`. -/
/-
**CategoryTheory.fromFinalModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.final_smallCategory`：∀ {J : Type u} {inst : 
CategoryTheory.Category.{v, u} J} [self : CategoryTheory.FinallySmall J], ∃ S x 
F, F.Final

--- 原说明 ---
An arbitrarily chosen final functor `FinalModel J ⥤ J`.
-/
noncomputable def fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))
/-
**CategoryTheory.final_fromFinalModel** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`
。
形式化陈述：final_fromFinalModel [FinallySmall.{w} J] : Final (fromFinalModel J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.FinallySmall.final_smallCategory`：∀ {J : Type u} {inst : 
CategoryTheory.Category.{v, u} J} [self : CategoryTheory.FinallySmall J], ∃ S x 
F, F.Final
-/
instance final_fromFinalModel [FinallySmall.{w} J] : Final (fromFinalModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))
/-
**CategoryTheory.finallySmall_of_essentiallySmall** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{
w} J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.mk'`：∀ {J : Type u} [inst : CategoryTheory.C
ategory.{v, u} J] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (F : 
CategoryTheory.Functo…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
theorem finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J :=
  FinallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}
variable {K : Type u₁} [Category.{v₁} K]
/-
**CategoryTheory.finallySmall_of_final_of_finallySmall** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：finallySmall_of_final_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Fi
nal F] : FinallySmall.{w} J
参数：F : K ⥤ J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.mk'`：∀ {J : Type u} [inst : CategoryTheory.C
ategory.{v, u} J] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (F : 
CategoryTheory.Functo…
-/
theorem finallySmall_of_final_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _
/-
**CategoryTheory.finallySmall_of_final_of_essentiallySmall** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：finallySmall_of_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K 
⥤ J) [Final F] : FinallySmall.{w} J
参数：F : K ⥤ J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.finallySmall_of_essentiallySmall`：finallySmall_of_essenti
allySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J
· 使用定理 `CategoryTheory.finallySmall_of_final_of_finallySmall`：finallySmall_of_fi
nal_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] : FinallySmall.{w
} J
-/
theorem finallySmall_of_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Limits.HasTerminal J] : FinallySmall.{w} J :=
  have := Functor.final_const_terminal (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊤_ J))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J' : Type*} [Category* J'] [FinallySmall.{w} J] [FinallySmall.{w'} J'] :
    FinallySmall.{max w w'} (J × J') :=
  finallySmall_of_final_of_essentiallySmall
    ((fromFinalModel.{w} J).prod (fromFinalModel.{w'} J'))

end FinallySmall

section InitiallySmall

variable (J : Type u) [Category.{v} J]

/-- A category is `InitiallySmall.{w}` if there is an initial functor from a `w`-small category. -/
/-
**CategoryTheory.InitiallySmall** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type u) → [CategoryTheory.Category.{v, u} J] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is `InitiallySmall.{w}` if there is an initial functor from a `w`-sma
ll category.
-/
class InitiallySmall : Prop where
  /-- There is an initial functor from a small category. -/
  initial_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F

/-- Constructor for `InitialSmall C` from an explicit small category witness. -/
/-
**CategoryTheory.InitiallySmall.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.In
itiallySmall`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {S : Type w} [ins
t_1 : CategoryTheory.SmallCategory S]   (F : CategoryTheory.Functor S J) [F.Init
ial], CategoryTheory.InitiallySmall J
参数：F : CategoryTheory.Functor S J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `InitialSmall C` from an explicit small category witness.
-/
theorem InitiallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/-- An arbitrarily chosen small model for an initially small category. -/
/-
**CategoryTheory.InitialModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：InitialModel [InitiallySmall.{w} J] : Type w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.initial_smallCategory`：∀ {J : Type u} {ins
t : CategoryTheory.Category.{v, u} J} [self : CategoryTheory.InitiallySmall J], 
∃ S x F, F.Initial

--- 原说明 ---
An arbitrarily chosen small model for an initially small category.
-/
def InitialModel [InitiallySmall.{w} J] : Type w :=
  Classical.choose (@InitiallySmall.initial_smallCategory J _ _)
/-
**CategoryTheory.smallCategoryInitialModel** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：smallCategoryInitialModel [InitiallySmall.{w} J] : SmallCategory (InitialM
odel J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.initial_smallCategory`：∀ {J : Type u} {ins
t : CategoryTheory.Category.{v, u} J} [self : CategoryTheory.InitiallySmall J], 
∃ S x F, F.Initial
-/
noncomputable instance smallCategoryInitialModel [InitiallySmall.{w} J] :
    SmallCategory (InitialModel J) :=
  Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))

/-- An arbitrarily chosen initial functor `InitialModel J ⥤ J`. -/
/-
**CategoryTheory.fromInitialModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.initial_smallCategory`：∀ {J : Type u} {ins
t : CategoryTheory.Category.{v, u} J} [self : CategoryTheory.InitiallySmall J], 
∃ S x F, F.Initial

--- 原说明 ---
An arbitrarily chosen initial functor `InitialModel J ⥤ J`.
-/
noncomputable def fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))
/-
**CategoryTheory.initial_fromInitialModel** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：initial_fromInitialModel [InitiallySmall.{w} J] : Initial (fromInitialMode
l J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.InitiallySmall.initial_smallCategory`：∀ {J : Type u} {ins
t : CategoryTheory.Category.{v, u} J} [self : CategoryTheory.InitiallySmall J], 
∃ S x F, F.Initial
-/
instance initial_fromInitialModel [InitiallySmall.{w} J] : Initial (fromInitialModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))
/-
**CategoryTheory.initiallySmall_of_essentiallySmall** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySma
ll.{w} J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.mk'`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (F 
: CategoryTheory.Functo…
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
theorem initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J :=
  InitiallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}
variable {K : Type u₁} [Category.{v₁} K]
/-
**CategoryTheory.initiallySmall_of_initial_of_initiallySmall** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory`。
形式化陈述：initiallySmall_of_initial_of_initiallySmall [InitiallySmall.{w} K] (F : K 
⥤ J) [Initial F] : InitiallySmall.{w} J
参数：F : K ⥤ J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.mk'`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (F 
: CategoryTheory.Functo…
-/
theorem initiallySmall_of_initial_of_initiallySmall [InitiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _
/-
**CategoryTheory.initiallySmall_of_initial_of_essentiallySmall** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory`。
形式化陈述：initiallySmall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K] (F 
: K ⥤ J) [Initial F] : InitiallySmall.{w} J
参数：F : K ⥤ J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.initiallySmall_of_essentiallySmall`：initiallySmall_of_ess
entiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J
· 使用定理 `CategoryTheory.initiallySmall_of_initial_of_initiallySmall`：initiallySma
ll_of_initial_of_initiallySmall [InitiallySmall.{w} K] (F : K ⥤ J) [Initial F] :
 InitiallySmall.{w} J
-/
theorem initiallySmall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Limits.HasInitial J] : InitiallySmall.{w} J :=
  have := Functor.initial_const_initial (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊥_ J))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} J] [InitiallySmall.{w} J] (X : J) :
    InitiallySmall.{w} (Over X) := by
  have : InitiallySmall.{w} (CostructuredArrow (fromInitialModel.{w} J) X) :=
    initiallySmall_of_essentiallySmall _
  exact initiallySmall_of_initial_of_initiallySmall
    (CostructuredArrow.toOver (fromInitialModel.{w} J) X)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J' : Type*} [Category* J'] [InitiallySmall.{w} J] [InitiallySmall.{w'} J'] :
    InitiallySmall.{max w w'} (J × J') :=
  initiallySmall_of_initial_of_essentiallySmall
    ((fromInitialModel.{w} J).prod (fromInitialModel.{w'} J'))

end InitiallySmall

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type u} [Category.{v} J] [InitiallySmall.{w} J] : FinallySmall.{w} Jᵒᵖ where
  final_smallCategory := ⟨_, _, (fromInitialModel.{w} J).op, inferInstance⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type u} [Category.{v} J] [FinallySmall.{w} J] : InitiallySmall.{w} Jᵒᵖ where
  initial_smallCategory := ⟨_, _, (fromFinalModel.{w} J).op, inferInstance⟩

section WeaklyTerminal

variable (J : Type u) [Category.{v} J]

/-- The converse is true if `J` is filtered, see `finallySmall_of_small_weakly_terminal_set`. -/
/-
**CategoryTheory.FinallySmall.exists_small_weakly_terminal_set** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.FinallySmall`。
形式化陈述：∀ (J : Type u) [inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.F
inallySmall J],   ∃ s, ∃ (_ : Small.{w, u} ↑s), ∀ (i : J), ∃ j ∈ s, Nonempty (i 
⟶ j)
参数：J : Type u；_ : Small.{w, u} ↑s；i : J；i ⟶ j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The converse is true if `J` is filtered, see `finallySmall_of_small_weakly_termi
nal_set`.
-/
theorem FinallySmall.exists_small_weakly_terminal_set [FinallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in
/-
**CategoryTheory.finallySmall_of_small_weakly_terminal_set** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：finallySmall_of_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J
) [Small.{v} s] (hs : forall i, exists j in s, Nonempty (i ⟶ j)) : FinallySmall.
{v} J
参数：s : Set J；hs : forall i, exists j in s, Nonempty (i ⟶ j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.finallySmall_of_final_of_essentiallySmall`：finallySmall_o
f_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F] : Fin
allySmall.{w} J
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
theorem finallySmall_of_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j)) : FinallySmall.{v} J := by
  suffices Functor.Final (ObjectProperty.ι (· ∈ s)) from
    finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· ∈ s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩
/-
**CategoryTheory.finallySmall_iff_exists_small_weakly_terminal_set** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：finallySmall_iff_exists_small_weakly_terminal_set [IsFilteredOrEmpty J] : 
FinallySmall.{v} J ↔ exists (s : Set J) (_ : Small.{v} s), forall i, exists j in
 s, Nonempty (i ⟶ j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.exists_small_weakly_terminal_set`：∀ (J : Typ
e u) [inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.FinallySmall J], 
  ∃ s, ∃ (_ : Small.{w, u} ↑s), ∀ (i : J), ∃ j ∈ s…
· 使用定理 `CategoryTheory.finallySmall_of_small_weakly_terminal_set`：finallySmall_o
f_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s] (hs 
: forall i, exists j in s, Nonempty (i ⟶ j)) :…
-/
theorem finallySmall_iff_exists_small_weakly_terminal_set [IsFilteredOrEmpty J] :
    FinallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'

end WeaklyTerminal

section WeaklyInitial

variable (J : Type u) [Category.{v} J]

/-- The converse is true if `J` is cofiltered, see `initiallySmall_of_small_weakly_initial_set`. -/
/-
**CategoryTheory.InitiallySmall.exists_small_weakly_initial_set** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.InitiallySmall`。
形式化陈述：∀ (J : Type u) [inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.I
nitiallySmall J],   ∃ s, ∃ (_ : Small.{w, u} ↑s), ∀ (i : J), ∃ j ∈ s, Nonempty (
j ⟶ i)
参数：J : Type u；_ : Small.{w, u} ↑s；i : J；j ⟶ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The converse is true if `J` is cofiltered, see `initiallySmall_of_small_weakly_i
nitial_set`.
-/
theorem InitiallySmall.exists_small_weakly_initial_set [InitiallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in
/-
**CategoryTheory.initiallySmall_of_small_weakly_initial_set** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：initiallySmall_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Se
t J) [Small.{v} s] (hs : forall i, exists j in s, Nonempty (j ⟶ i)) : InitiallyS
mall.{v} J
参数：s : Set J；hs : forall i, exists j in s, Nonempty (j ⟶ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered_of_fullyFaithfu
l`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.initiallySmall_of_initial_of_essentiallySmall`：initiallyS
mall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Initia
l F] : InitiallySmall.{w} J
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
theorem initiallySmall_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  suffices Functor.Initial (ObjectProperty.ι (· ∈ s)) from
    initiallySmall_of_initial_of_essentiallySmall (ObjectProperty.ι (· ∈ s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

variable {J} in
/-
**CategoryTheory.initiallySmall_of_essentiallySmall_weakly_initial_objectPropert
y** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：initiallySmall_of_essentiallySmall_weakly_initial_objectProperty [IsCofilt
eredOrEmpty J] (P : ObjectProperty J) [ObjectProperty.EssentiallySmall.{v} P] (h
P : forall i, exists j, P j ∧ Nonempty (j ⟶ i)) : InitiallySmall.{v} J
参数：P : ObjectProperty J；hP : forall i, exists j, P j ∧ Nonempty (j ⟶ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le'`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (P : CategoryTheory.ObjectProp
erty C)   [self : CategoryTheory.ObjectProperty.Essen…
· 使用定理 `CategoryTheory.initiallySmall_of_small_weakly_initial_set`：initiallySmal
l_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s] 
(hs : forall i, exists j in s, Nonempty (j ⟶ i)…
-/
theorem initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    [IsCofilteredOrEmpty J] (P : ObjectProperty J) [ObjectProperty.EssentiallySmall.{v} P]
    (hP : ∀ i, ∃ j, P j ∧ Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  obtain ⟨Q, H, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{v} P
  have : Small.{v} (show Set _ from Q) := by assumption
  refine initiallySmall_of_small_weakly_initial_set Q (fun i ↦ ?_)
  obtain ⟨j, hj, ⟨f⟩⟩ := hP i
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ _ hj
  exact ⟨k, hk, ⟨e.inv ≫ f⟩⟩
/-
**CategoryTheory.initiallySmall_iff_exists_small_weakly_initial_set** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：initiallySmall_iff_exists_small_weakly_initial_set [IsCofilteredOrEmpty J]
 : InitiallySmall.{v} J ↔ exists (s : Set J) (_ : Small.{v} s), forall i, exists
 j in s, Nonempty (j ⟶ i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InitiallySmall.exists_small_weakly_initial_set`：∀ (J : Ty
pe u) [inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J
],   ∃ s, ∃ (_ : Small.{w, u} ↑s), ∀ (i : J), ∃ j ∈…
· 使用定理 `CategoryTheory.initiallySmall_of_small_weakly_initial_set`：initiallySmal
l_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s] 
(hs : forall i, exists j in s, Nonempty (j ⟶ i)…
-/
theorem initiallySmall_iff_exists_small_weakly_initial_set [IsCofilteredOrEmpty J] :
    InitiallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'

end WeaklyInitial

namespace Limits

/-
**CategoryTheory.Limits.hasColimitsOfShape_of_finallySmall** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallyS
mall.{w} J] (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasCo
limitsOfShape J C
参数：J : Type u；C : Type u₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.hasColimitsOfShape_of_final`：hasColimitsOfS
hape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where has_colimi
t
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasColimitsOfShape J C :=
  Final.hasColimitsOfShape_of_final (fromFinalModel J)
/-
**CategoryTheory.Limits.hasLimitsOfShape_of_initiallySmall** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [Initiall
ySmall.{w} J] (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLi
mitsOfShape J C
参数：J : Type u；C : Type u₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.hasLimitsOfShape_of_initial`：hasLimitsOfS
hape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where has_limit
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLimitsOfShape J C :=
  Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

end Limits

end CategoryTheory

