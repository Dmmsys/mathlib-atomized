/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, coproducts,
and composition, with dual statements for the right lifting property.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

/-- Given `T : MorphismProperty C`, this is the class of morphisms that have the
left lifting property (llp) with respect to `T`. -/
/-
**CategoryTheory.MorphismProperty.llp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MorphismProperty`。
形式化陈述：llp : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `T : MorphismProperty C`, this is the class of morphisms that have the
left lifting property (llp) with respect to `T`.
-/
def llp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

/-- Given `T : MorphismProperty C`, this is the class of morphisms that have the
right lifting property (rlp) with respect to `T`. -/
/-
**CategoryTheory.MorphismProperty.rlp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MorphismProperty`。
形式化陈述：rlp : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `T : MorphismProperty C`, this is the class of morphisms that have the
right lifting property (rlp) with respect to `T`.
-/
def rlp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f
/-
**CategoryTheory.MorphismProperty.llp_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：llp_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] : T.llp i
参数：i : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.of_left_iso`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)   [C
ategoryTheory.IsIso i], CategoryThe…
-/
lemma llp_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] :
    T.llp i :=
  fun _ _ _ _ ↦ inferInstance
/-
**CategoryTheory.MorphismProperty.rlp_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：rlp_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : T.rlp f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.of_right_iso`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] {Y X B A : C} (p : X ⟶ Y) (i : A ⟶ B)   [
CategoryTheory.IsIso p], CategoryThe…
-/
lemma rlp_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    T.rlp f :=
  fun _ _ _ _ ↦ inferInstance
/-
**CategoryTheory.MorphismProperty.llp_isStableUnderRetracts** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_isStableUnderRetracts : T.llp.IsStableUnderRetracts where of_retract h
 hg _ _ f hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RetractArrow.leftLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {B A Z W B' A' : C} {f : A ⟶ B} {f' : A'
 ⟶ B'}   (h : CategoryTheory.RetractA…
-/
instance llp_isStableUnderRetracts : T.llp.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    h.leftLiftingProperty f
/-
**CategoryTheory.MorphismProperty.rlp_isStableUnderRetracts** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_isStableUnderRetracts : T.rlp.IsStableUnderRetracts where of_retract h
 hf _ _ g hg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RetractArrow.rightLiftingProperty`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X
' ⟶ Y'}   (h : CategoryTheory.RetractA…
-/
instance rlp_isStableUnderRetracts : T.rlp.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    h.rightLiftingProperty g
/-
**CategoryTheory.MorphismProperty.llp_isStableUnderCobaseChange** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_isStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where of_i
sPushout h hf _ _ g' hg'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.hasLiftingProperty`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {X Y Z W : C} {f : X ⟶ Y} {s : X ⟶ Z} {g : Z
 ⟶ W}   {t : Y ⟶ W},   CategoryTh…
-/
instance llp_isStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    h.hasLiftingProperty g'

open IsPullback in
/-
**CategoryTheory.MorphismProperty.rlp_isStableUnderBaseChange** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_isStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where of_isPul
lback h hf _ _ f' hf'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.hasLiftingProperty`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X Y Z W : C} {f : X ⟶ Y} {s : X ⟶ Z} {g : 
Z ⟶ W}   {t : Y ⟶ W},   CategoryTh…
-/
instance rlp_isStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    h.hasLiftingProperty f'
/-
**CategoryTheory.MorphismProperty.llp_isMultiplicative** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_isMultiplicative : T.llp.IsMultiplicative where id_mem X _ _ p hp
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.of_left_iso`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)   [C
ategoryTheory.IsIso i], CategoryThe…
-/
instance llp_isMultiplicative : T.llp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance
/-
**CategoryTheory.MorphismProperty.rlp_isMultiplicative** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_isMultiplicative : T.rlp.IsMultiplicative where id_mem X _ _ p hp
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.of_right_iso`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] {Y X B A : C} (p : X ⟶ Y) (i : A ⟶ B)   [
CategoryTheory.IsIso p], CategoryThe…
· 使用定理 `CategoryTheory.HasLiftingProperty.of_comp_right`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {Y X X' B A : C} (p : X ⟶ Y) (p' : X' ⟶ 
X) (i : A ⟶ B)   [CategoryTheory.HasL…
-/
instance rlp_isMultiplicative : T.rlp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance
/-
**CategoryTheory.MorphismProperty.llp_isStableUnderCoproductsOfShape** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_isStableUnderCoproductsOfShape (J : Type*) : T.llp.IsStableUnderCoprod
uctsOfShape J
参数：J : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCoproductsOfShape.mk`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C) (J : Type u_1)   [W.RespectsIso],   (∀ (X₁ …
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `CategoryTheory.instHasLiftingPropertyMap_1`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] {J : Type u_2} {A B : J → C}   [inst_1 : Cate
goryTheory.Limits.HasCoproduct A…
-/
instance llp_isStableUnderCoproductsOfShape (J : Type*) :
    T.llp.IsStableUnderCoproductsOfShape J := by
  apply IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j ↦ hf j _ hp
  infer_instance
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderCoproducts.{w} T.llp where
/-
**CategoryTheory.MorphismProperty.rlp_isStableUnderProductsOfShape** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_isStableUnderProductsOfShape (J : Type*) : T.rlp.IsStableUnderProducts
OfShape J
参数：J : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape.mk`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismPr
operty C) (J : Type u_1)   [W.RespectsIso],   (∀ (X₁ …
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `CategoryTheory.instHasLiftingPropertyMap`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {J : Type u_2} {A B : J → C}   [inst_1 : Catego
ryTheory.Limits.HasProduct A] …
-/
instance rlp_isStableUnderProductsOfShape (J : Type*) :
    T.rlp.IsStableUnderProductsOfShape J := by
  apply IsStableUnderProductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j ↦ hf j _ hp
  infer_instance
/-
**CategoryTheory.MorphismProperty.le_llp_iff_le_rlp** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：le_llp_iff_le_rlp (T' : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
参数：T' : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_llp_iff_le_rlp (T' : MorphismProperty C) :
    T ≤ T'.llp ↔ T' ≤ T.rlp :=
  ⟨fun h _ _ _ hp _ _ _ hi ↦ h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp ↦ h _ hp _ hi⟩
/-
**CategoryTheory.MorphismProperty.gc_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：gc_llp_rlp : GaloisConnection (OrderDual.toDual (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
-/
lemma gc_llp_rlp :
    GaloisConnection (OrderDual.toDual (α := MorphismProperty C) ∘ llp)
      (rlp ∘ OrderDual.ofDual) :=
  fun _ _ ↦ le_llp_iff_le_rlp _ _
/-
**CategoryTheory.MorphismProperty.le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：le_llp_rlp : T <= T.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_llp_rlp : T ≤ T.rlp.llp := by
  rw [le_llp_iff_le_rlp]

@[simp]
/-
**CategoryTheory.MorphismProperty.rlp_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：rlp_llp_rlp : T.rlp.llp.rlp = T.rlp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用引理 `CategoryTheory.MorphismProperty.gc_llp_rlp`：gc_llp_rlp : GaloisConnectio
n (OrderDual.toDual (α
-/
lemma rlp_llp_rlp : T.rlp.llp.rlp = T.rlp :=
  gc_llp_rlp.u_l_u_eq_u T

@[simp]
/-
**CategoryTheory.MorphismProperty.llp_rlp_llp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：llp_rlp_llp : T.llp.rlp.llp = T.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用引理 `CategoryTheory.MorphismProperty.gc_llp_rlp`：gc_llp_rlp : GaloisConnectio
n (OrderDual.toDual (α
-/
lemma llp_rlp_llp : T.llp.rlp.llp = T.llp :=
  gc_llp_rlp.l_u_l_eq_l T
/-
**CategoryTheory.MorphismProperty.antitone_rlp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：antitone_rlp : Antitone (rlp : MorphismProperty C -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用引理 `CategoryTheory.MorphismProperty.gc_llp_rlp`：gc_llp_rlp : GaloisConnectio
n (OrderDual.toDual (α
-/
lemma antitone_rlp : Antitone (rlp : MorphismProperty C → _) :=
  fun _ _ h ↦ gc_llp_rlp.monotone_u h
/-
**CategoryTheory.MorphismProperty.antitone_llp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：antitone_llp : Antitone (llp : MorphismProperty C -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `CategoryTheory.MorphismProperty.gc_llp_rlp`：gc_llp_rlp : GaloisConnectio
n (OrderDual.toDual (α
-/
lemma antitone_llp : Antitone (llp : MorphismProperty C → _) :=
  fun _ _ h ↦ gc_llp_rlp.monotone_l h
/-
**CategoryTheory.MorphismProperty.pushouts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：pushouts_le_llp_rlp : T.pushouts <= T.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderCobaseChange_iff_pushouts_l
e`：isStableUnderCobaseChange_iff_pushouts_le : P.IsStableUnderCobaseChange ↔ P.p
ushouts <= P
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_monotone`：pushouts_monotone : M
onotone (pushouts (C
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_rlp`：le_llp_rlp : T <= T.rlp.llp
-/
lemma pushouts_le_llp_rlp : T.pushouts ≤ T.rlp.llp := by
  intro A B i hi
  exact (T.rlp.llp.isStableUnderCobaseChange_iff_pushouts_le).1 inferInstance i
    (pushouts_monotone T.le_llp_rlp _ hi)

@[simp]
/-
**CategoryTheory.MorphismProperty.rlp_pushouts** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：rlp_pushouts : T.pushouts.rlp = T.rlp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `CategoryTheory.MorphismProperty.le_pushouts`：le_pushouts : P <= P.pushou
ts
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_le_llp_rlp`：pushouts_le_llp_rlp
 : T.pushouts <= T.rlp.llp
-/
lemma rlp_pushouts : T.pushouts.rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_pushouts
  · rw [← le_llp_iff_le_rlp]
    exact T.pushouts_le_llp_rlp
/-
**CategoryTheory.MorphismProperty.colimitsOfShape_discrete_le_llp_rlp** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：colimitsOfShape_discrete_le_llp_rlp (J : Type w) : T.colimitsOfShape (Disc
rete J) <= T.rlp.llp
参数：J : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_monotone`：colimitsOfShap
e_monotone {W₁ W₂ : MorphismProperty C} (h : W₁ <= W₂) (J : Type*) [Category* J]
 : W₁.colimitsOfShape J <= W₂.colimitsOfShape …
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_rlp`：le_llp_rlp : T <= T.rlp.llp
-/
lemma colimitsOfShape_discrete_le_llp_rlp (J : Type w) :
    T.colimitsOfShape (Discrete J) ≤ T.rlp.llp := by
  intro A B i hi
  exact MorphismProperty.colimitsOfShape_le _ (colimitsOfShape_monotone T.le_llp_rlp _ _ hi)
/-
**CategoryTheory.MorphismProperty.coproducts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：coproducts_le_llp_rlp : (coproducts.{w} T) <= T.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_iff`：coproducts_iff {X Y : C}
 (f : X ⟶ Y) : coproducts.{w} W f ↔ exists (J : Type w), W.colimitsOfShape (Disc
rete J) f
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_discrete_le_llp_rlp`：col
imitsOfShape_discrete_le_llp_rlp (J : Type w) : T.colimitsOfShape (Discrete J) <
= T.rlp.llp
-/
lemma coproducts_le_llp_rlp : (coproducts.{w} T) ≤ T.rlp.llp := by
  intro A B i hi
  rw [coproducts_iff] at hi
  obtain ⟨J, hi⟩ := hi
  exact T.colimitsOfShape_discrete_le_llp_rlp J _ hi

@[simp]
/-
**CategoryTheory.MorphismProperty.rlp_coproducts** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：rlp_coproducts : (coproducts.{w} T).rlp = T.rlp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `CategoryTheory.MorphismProperty.le_coproducts`：le_coproducts : W <= copr
oducts.{w} W
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_le_llp_rlp`：coproducts_le_llp
_rlp : (coproducts.{w} T) <= T.rlp.llp
-/
lemma rlp_coproducts : (coproducts.{w} T).rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_coproducts
  · rw [← le_llp_iff_le_rlp]
    exact T.coproducts_le_llp_rlp
/-
**CategoryTheory.MorphismProperty.retracts_le_llp_rlp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：retracts_le_llp_rlp : T.retracts <= T.rlp.llp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.MorphismProperty.retracts_monotone`：retracts_monotone : M
onotone (retracts (C
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_rlp`：le_llp_rlp : T <= T.rlp.llp
· 使用引理 `CategoryTheory.MorphismProperty.retracts_le`：retracts_le (P : MorphismPr
operty C) [P.IsStableUnderRetracts] : P.retracts <= P
-/
lemma retracts_le_llp_rlp : T.retracts ≤ T.rlp.llp :=
  le_trans (retracts_monotone T.le_llp_rlp) T.rlp.llp.retracts_le

@[simp]
/-
**CategoryTheory.MorphismProperty.rlp_retracts** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：rlp_retracts : T.retracts.rlp = T.rlp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `CategoryTheory.MorphismProperty.le_retracts`：le_retracts (P : MorphismPr
operty C) : P <= P.retracts
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_iff_le_rlp`：le_llp_iff_le_rlp (T'
 : MorphismProperty C) : T <= T'.llp ↔ T' <= T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.retracts_le_llp_rlp`：retracts_le_llp_rlp
 : T.retracts <= T.rlp.llp
-/
lemma rlp_retracts : T.retracts.rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_retracts
  · rw [← le_llp_iff_le_rlp]
    exact T.retracts_le_llp_rlp
/-
**CategoryTheory.MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rlp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C} (
i : A ⟶ B) (p : X ⟶ Y) : (MorphismProperty.ofHoms (fun (_ : ι) => i)).rlp p ↔ Ha
sLiftingProperty i p
参数：ι : Type*；i : A ⟶ B；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma rlp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun (_ : ι) ↦ i)).rlp p ↔ HasLiftingProperty i p :=
  ⟨fun hp ↦ hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩
/-
**CategoryTheory.MorphismProperty.llp_ofHoms_iff_hasLiftingProperty** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：llp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C} (
i : A ⟶ B) (p : X ⟶ Y) : (MorphismProperty.ofHoms (fun (_ : ι) => p)).llp i ↔ Ha
sLiftingProperty i p
参数：ι : Type*；i : A ⟶ B；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma llp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun (_ : ι) ↦ p)).llp i ↔ HasLiftingProperty i p :=
  ⟨fun hp ↦ hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

end MorphismProperty

/-
**CategoryTheory.Functor.hasLiftingProperty_iff_of_isEquivalence** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   (G : CategoryTheory.Functor C D)
 [G.IsEquivalence] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),   CategoryTheory.HasLi
ftingProperty (G.map i) (G.map p) ↔ CategoryTheory.HasLiftingProperty i p
参数：G : CategoryTheory.Functor C D；i : A ⟶ B；p : X ⟶ Y；G.map i；G.map p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.hasLiftingProperty_iff`：hasLiftingProperty_iff
 (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) : HasLiftingProperty 
(G.map i) p ↔ HasLiftingProperty i (F.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty`：rlp_o
fHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C} (i : A ⟶ B) 
(p : X ⟶ Y) : (MorphismProperty.ofHoms (fun (_ : ι) => …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma Functor.hasLiftingProperty_iff_of_isEquivalence
    {D : Type*} [Category* D] (G : C ⥤ D) [G.IsEquivalence]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) (G.map p) ↔
      HasLiftingProperty i p := by
  #adaptation_note /-- Prior to nightly-2026-05-07, the next three lines were just
  ```
  simp only [dsimp% G.asEquivalence.toAdjunction.hasLiftingProperty_iff,
    ← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  ```
  This is a temporary repair, and authors/maintainers are encouraged to either find a better repair,
  or identify a minimal example of an underlying problem in Lean.
  -/
  change HasLiftingProperty (G.asEquivalence.functor.map i) (G.asEquivalence.functor.map p) ↔ _
  rw [G.asEquivalence.toAdjunction.hasLiftingProperty_iff]
  simp only [← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  exact MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (G.asEquivalence.unitIso.symm.app _)
      (G.asEquivalence.unitIso.symm.app _)
      (G.asEquivalence.unitIso.inv.naturality p).symm)

end CategoryTheory

