/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsLeft P Q`: `P` respects the property `Q` on the left if `P f → P (i ≫ f)` where
  `i` satisfies `Q`.
* `RespectsRight P Q`: `P` respects the property `Q` on the right if `P f → P (f ≫ i)` where
  `i` satisfies `Q`.
* `Respects`: `P` respects `Q` if `P` respects `Q` both on the left and on the right.

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

/-- A `MorphismProperty C` is a class of morphisms between objects in `C`. -/
/-
**CategoryTheory.MorphismProperty** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：MorphismProperty (C : Type u) [CategoryStruct.{v} C]
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MorphismProperty C` is a class of morphisms between objects in `C`.
-/
def MorphismProperty (C : Type u) [CategoryStruct.{v} C] :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

namespace MorphismProperty

section

variable (C : Type u) [CategoryStruct.{v} C]

/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteBooleanAlgebra (MorphismProperty C) where
  le P₁ P₂ := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f → P₂ f
  __ := (inferInstance : CompleteBooleanAlgebra (∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))
/-
**CategoryTheory.MorphismProperty.le_def** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：le_def {P Q : MorphismProperty C} : P <= Q ↔ forall {X Y : C} (f : X ⟶ Y),
 P f -> Q f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {P Q : MorphismProperty C} :
    P ≤ Q ↔ ∀ {X Y : C} (f : X ⟶ Y), P f → Q f := Iff.rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩
/-
**CategoryTheory.MorphismProperty.top_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True := rfl

variable {C}

@[ext]
/-
**CategoryTheory.MorphismProperty.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
MorphismProperty`。
形式化陈述：ext (W W' : MorphismProperty C) (h : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W
' f) : W = W'
参数：W W' : MorphismProperty C；h : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma ext (W W' : MorphismProperty C) (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
    W = W' := by
  funext X Y f
  rw [h]

@[simp]
/-
**CategoryTheory.MorphismProperty.top_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]
/-
**CategoryTheory.MorphismProperty.of_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：of_eq_top {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y) : P f
参数：h : P = ⊤；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma of_eq_top {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y) : P f := by
  simp [h]

@[simp]
/-
**CategoryTheory.MorphismProperty.sup_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：sup_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊔ W') f ↔ W
 f ∨ W' f
参数：W W' : MorphismProperty C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sup_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊔ W') f ↔ W f ∨ W' f :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.MorphismProperty.sSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：sSup_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) : sSup S f ↔
 exists W in S, W f
参数：S : Set (MorphismProperty C)；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sSup_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sSup S f ↔ ∃ W ∈ S, W f := by
  simp +instances [MorphismProperty]

@[simp]
/-
**CategoryTheory.MorphismProperty.iSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：iSup_iff {ι : Sort*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
 iSup W f ↔ exists i, W i f
参数：W : ι -> MorphismProperty C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_iff {ι : Sort*} (W : ι → MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    iSup W f ↔ ∃ i, W i f := by
  simp [← sSup_range]

@[simp]
/-
**CategoryTheory.MorphismProperty.inf_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：inf_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊓ W') f ↔ W
 f ∧ W' f
参数：W W' : MorphismProperty C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inf_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊓ W') f ↔ W f ∧ W' f :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.MorphismProperty.sInf_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：sInf_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) : sInf S f ↔
 forall W in S, W f
参数：S : Set (MorphismProperty C)；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sInf_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sInf S f ↔ ∀ W ∈ S, W f := by
  simp +instances [MorphismProperty]

@[simp]
/-
**CategoryTheory.MorphismProperty.iInf_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：iInf_iff {ι : Type*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
 iInf W f ↔ forall i, W i f
参数：W : ι -> MorphismProperty C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iInf_iff {ι : Type*} (W : ι → MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    iInf W f ↔ ∀ i, W i f := by
  simp [← sInf_range]

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp]
/-
**CategoryTheory.MorphismProperty.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
orphismProperty`。
形式化陈述：op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property in `Cᵒᵖ` associated to a morphism property in `C`
-/
def op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun _ _ f => P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
/-
**CategoryTheory.MorphismProperty.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MorphismProperty`。
形式化陈述：unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C
参数：P : MorphismProperty Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property in `C` associated to a morphism property in `Cᵒᵖ`
-/
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op
/-
**CategoryTheory.MorphismProperty.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：unop_op (P : MorphismProperty C) : P.op.unop = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (P : MorphismProperty C) : P.op.unop = P :=
  rfl
/-
**CategoryTheory.MorphismProperty.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P
参数：P : MorphismProperty Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P :=
  rfl

end

section

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {E : Type*} [Category* E]

/-- The inverse image of a `MorphismProperty D` by a functor `C ⥤ D` -/
/-
**CategoryTheory.MorphismProperty.inverseImage** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C
参数：P : MorphismProperty D；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse image of a `MorphismProperty D` by a functor `C ⥤ D`
-/
def inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun _ _ f =>
  P (F.map f)

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：inverseImage_iff (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) : P.inverseImage F f ↔ P (F.map f)
参数：P : MorphismProperty D；F : C ⥤ D；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inverseImage_iff (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    P.inverseImage F f ↔ P (F.map f) := by rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.op_inverseImage** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：op_inverseImage (P : MorphismProperty D) (F : C ⥤ D) : (P.inverseImage F).
op = P.op.inverseImage F.op
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).op = P.op.inverseImage F.op := rfl

@[gcongr]
/-
**CategoryTheory.MorphismProperty.monotone_inverseImage** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：monotone_inverseImage (F : C ⥤ D) : Monotone (fun P : MorphismProperty D =
> P.inverseImage F)
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_inverseImage (F : C ⥤ D) :
    Monotone (fun P : MorphismProperty D ↦ P.inverseImage F) :=
  fun _ _ h _ _ _ hf ↦ h _ hf

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：inverseImage_id (P : MorphismProperty C) : P.inverseImage (𝟭 C) = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_id (P : MorphismProperty C) : P.inverseImage (𝟭 C) = P :=
  rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_inverseImage** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_inverseImage (P : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
 : (P.inverseImage G).inverseImage F = P.inverseImage (F ⋙ G)
参数：P : MorphismProperty E；F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_inverseImage (P : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E) :
    (P.inverseImage G).inverseImage F = P.inverseImage (F ⋙ G) :=
  rfl

/-- The (strict) image of a `MorphismProperty C` by a functor `C ⥤ D` -/
/-
**CategoryTheory.MorphismProperty.strictMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         Category
Theory.MorphismProperty C → CategoryTheory.Functor C D → CategoryTheory.Morphism
Property D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (strict) image of a `MorphismProperty C` by a functor `C ⥤ D`
-/
inductive strictMap (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D where
  | map {X Y : C} {f : X ⟶ Y} (hf : P f) : strictMap _ _ (F.map f)
/-
**CategoryTheory.MorphismProperty.map_mem_strictMap** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：map_mem_strictMap (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ 
Y) (hf : P f) : (P.strictMap F) (F.map f)
参数：P : MorphismProperty C；F : C ⥤ D；f : X ⟶ Y；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mem_strictMap (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.strictMap F) (F.map f) := ⟨hf⟩

@[gcongr]
/-
**CategoryTheory.MorphismProperty.monotone_strictMap** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：monotone_strictMap (F : C ⥤ D) : Monotone (fun P : MorphismProperty C => P
.strictMap F)
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_strictMap (F : C ⥤ D) : Monotone (fun P : MorphismProperty C ↦ P.strictMap F) :=
  fun _ _ h _ _ _ ⟨hf⟩ ↦ ⟨h _ hf⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：strictMap_id (P : MorphismProperty C) : P.strictMap (𝟭 C) = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
-/
lemma strictMap_id (P : MorphismProperty C) :
    P.strictMap (𝟭 C) = P := by
  ext
  exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_strictMap** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：strictMap_strictMap (P : MorphismProperty C) (F : C ⥤ D) (G : D ⥤ E) : (P.
strictMap F).strictMap G = P.strictMap (F ⋙ G)
参数：P : MorphismProperty C；F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
-/
lemma strictMap_strictMap (P : MorphismProperty C) (F : C ⥤ D) (G : D ⥤ E) :
    (P.strictMap F).strictMap G = P.strictMap (F ⋙ G) := by
  ext
  exact ⟨fun ⟨⟨h⟩⟩ ↦ ⟨h⟩, fun ⟨h⟩ ↦ ⟨⟨h⟩⟩⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_le_iff_le_inverseImage** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：strictMap_le_iff_le_inverseImage (F : C ⥤ D) (P : MorphismProperty C) (P' 
: MorphismProperty D) : P.strictMap F <= P' ↔ P <= P'.inverseImage F
参数：F : C ⥤ D；P : MorphismProperty C；P' : MorphismProperty D。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMap_le_iff_le_inverseImage (F : C ⥤ D) (P : MorphismProperty C)
    (P' : MorphismProperty D) : P.strictMap F ≤ P' ↔ P ≤ P'.inverseImage F :=
  ⟨fun h _ _ _ hf ↦ h _ ⟨hf⟩, fun h _ _ _ ⟨hf⟩ ↦ h _ hf⟩
/-
**CategoryTheory.MorphismProperty.gc_strictMap** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：gc_strictMap (F : C ⥤ D) : GaloisConnection (strictMap · F) (inverseImage 
· F)
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.strictMap_le_iff_le_inverseImage`：strict
Map_le_iff_le_inverseImage (F : C ⥤ D) (P : MorphismProperty C) (P' : MorphismPr
operty D) : P.strictMap F <= P' ↔ P <= P'.inverseImage…
-/
lemma gc_strictMap (F : C ⥤ D) : GaloisConnection (strictMap · F) (inverseImage · F) :=
  strictMap_le_iff_le_inverseImage F
/-
**CategoryTheory.MorphismProperty.le_inverseImage_strictMap** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：le_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) : P <= (P.s
trictMap F).inverseImage F
参数：P : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma le_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) :
    P ≤ (P.strictMap F).inverseImage F :=
  (gc_strictMap F).le_u_l P
/-
**CategoryTheory.MorphismProperty.strictMap_inverseImage_le** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：strictMap_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) : (P.invers
eImage F).strictMap F <= P
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).strictMap F ≤ P :=
  (gc_strictMap F).l_u_le P

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_inverseImage_strictMap** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：strictMap_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) : ((
P.strictMap F).inverseImage F).strictMap F = P.strictMap F
参数：P : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) :
    ((P.strictMap F).inverseImage F).strictMap F = P.strictMap F :=
  (gc_strictMap F).l_u_l_eq_l P

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_strictMap_inverseImage** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_strictMap_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
 ((P.inverseImage F).strictMap F).inverseImage F = P.inverseImage F
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma inverseImage_strictMap_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
    ((P.inverseImage F).strictMap F).inverseImage F = P.inverseImage F :=
  (gc_strictMap F).u_l_u_eq_u P

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_bot** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：strictMap_bot (F : C ⥤ D) : strictMap ⊥ F = ⊥
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_bot (F : C ⥤ D) :
    strictMap ⊥ F = ⊥ :=
  (gc_strictMap F).l_bot

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_strictMap_top** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_strictMap_top (F : C ⥤ D) : (strictMap ⊤ F).inverseImage F = 
⊤
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_top`：u_l_top {l : α -> β} {u : β -> α} (gc : Galois
Connection l u) : u (l ⊤) = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma inverseImage_strictMap_top (F : C ⥤ D) :
    (strictMap ⊤ F).inverseImage F = ⊤ :=
  (gc_strictMap F).u_l_top

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_bot** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：inverseImage_bot (F : C ⥤ D) : inverseImage ⊥ F = ⊥
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_bot (F : C ⥤ D) :
    inverseImage ⊥ F = ⊥ :=
  rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_top** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：inverseImage_top (F : C ⥤ D) : inverseImage ⊤ F = ⊤
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_top (F : C ⥤ D) :
    inverseImage ⊤ F = ⊤ :=
  rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_sup** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：strictMap_sup (F : C ⥤ D) (P P' : MorphismProperty C) : (P ⊔ P').strictMap
 F = P.strictMap F ⊔ P'.strictMap F
参数：F : C ⥤ D；P P' : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_sup (F : C ⥤ D) (P P' : MorphismProperty C) :
    (P ⊔ P').strictMap F = P.strictMap F ⊔ P'.strictMap F :=
  (gc_strictMap F).l_sup

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：strictMap_iSup (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty C) : (⨆ 
i, P i).strictMap F = ⨆ i, (P i).strictMap F
参数：F : C ⥤ D；P : ι -> MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_iSup (F : C ⥤ D) {ι : Type*} (P : ι → MorphismProperty C) :
    (⨆ i, P i).strictMap F = ⨆ i, (P i).strictMap F :=
  (gc_strictMap F).l_iSup

@[simp]
/-
**CategoryTheory.MorphismProperty.strictMap_sSup** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：strictMap_sSup (F : C ⥤ D) (P : Set (MorphismProperty C)) : (sSup P).stric
tMap F = ⨆ P' in P, P'.strictMap F
参数：F : C ⥤ D；P : Set (MorphismProperty C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma strictMap_sSup (F : C ⥤ D) (P : Set (MorphismProperty C)) :
    (sSup P).strictMap F = ⨆ P' ∈ P, P'.strictMap F :=
  (gc_strictMap F).l_sSup

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_inf** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：inverseImage_inf (F : C ⥤ D) (P P' : MorphismProperty D) : (P ⊓ P').invers
eImage F = P.inverseImage F ⊓ P'.inverseImage F
参数：F : C ⥤ D；P P' : MorphismProperty D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma inverseImage_inf (F : C ⥤ D) (P P' : MorphismProperty D) :
    (P ⊓ P').inverseImage F = P.inverseImage F ⊓ P'.inverseImage F :=
  (gc_strictMap F).u_inf

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_iInf** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_iInf (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D) : 
(⨅ i, P i).inverseImage F = ⨅ i, (P i).inverseImage F
参数：F : C ⥤ D；P : ι -> MorphismProperty D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma inverseImage_iInf (F : C ⥤ D) {ι : Type*} (P : ι → MorphismProperty D) :
    (⨅ i, P i).inverseImage F = ⨅ i, (P i).inverseImage F :=
  (gc_strictMap F).u_iInf

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_sInf** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_sInf (F : C ⥤ D) (P : Set (MorphismProperty D)) : (sInf P).in
verseImage F = ⨅ P' in P, P'.inverseImage F
参数：F : C ⥤ D；P : Set (MorphismProperty D)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用引理 `CategoryTheory.MorphismProperty.gc_strictMap`：gc_strictMap (F : C ⥤ D) :
 GaloisConnection (strictMap · F) (inverseImage · F)
-/
lemma inverseImage_sInf (F : C ⥤ D) (P : Set (MorphismProperty D)) :
    (sInf P).inverseImage F = ⨅ P' ∈ P, P'.inverseImage F :=
  (gc_strictMap F).u_sInf

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_sup** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：inverseImage_sup (F : C ⥤ D) (P P' : MorphismProperty D) : (P ⊔ P').invers
eImage F = P.inverseImage F ⊔ P'.inverseImage F
参数：F : C ⥤ D；P P' : MorphismProperty D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_sup (F : C ⥤ D) (P P' : MorphismProperty D) :
    (P ⊔ P').inverseImage F = P.inverseImage F ⊔ P'.inverseImage F :=
  rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_iSup** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_iSup (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D) : 
(⨆ i, P i).inverseImage F = ⨆ i, (P i).inverseImage F
参数：F : C ⥤ D；P : ι -> MorphismProperty D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inverseImage_iSup (F : C ⥤ D) {ι : Type*} (P : ι → MorphismProperty D) :
    (⨆ i, P i).inverseImage F = ⨆ i, (P i).inverseImage F := by
  ext; simp

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_sSup** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_sSup (F : C ⥤ D) (P : Set (MorphismProperty D)) : (sSup P).in
verseImage F = ⨆ P' in P, P'.inverseImage F
参数：F : C ⥤ D；P : Set (MorphismProperty D)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inverseImage_sSup (F : C ⥤ D) (P : Set (MorphismProperty D)) :
    (sSup P).inverseImage F = ⨆ P' ∈ P, P'.inverseImage F := by
  ext; simp

/-- The image (up to isomorphisms) of a `MorphismProperty C` by a functor `C ⥤ D` -/
/-
**CategoryTheory.MorphismProperty.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MorphismProperty`。
形式化陈述：map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D
参数：P : MorphismProperty C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image (up to isomorphisms) of a `MorphismProperty C` by a functor `C ⥤ D`
-/
def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)
/-
**CategoryTheory.MorphismProperty.map_mem_map** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf
 : P f) : (P.map F) (F.map f)
参数：P : MorphismProperty C；F : C ⥤ D；f : X ⟶ Y；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

@[gcongr]
/-
**CategoryTheory.MorphismProperty.monotone_map** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：monotone_map (F : C ⥤ D) : Monotone (map · F)
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_map (F : C ⥤ D) :
    Monotone (map · F) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

@[simp]
/-
**CategoryTheory.MorphismProperty.map_top_eq_top_of_essSurj_of_full** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：map_top_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] : (⊤ : 
MorphismProperty C).map F = ⊤
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_top_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] :
    (⊤ : MorphismProperty C).map F = ⊤ := by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

section

variable (P : MorphismProperty C)

/-- The set in `Set (Arrow C)` which corresponds to `P : MorphismProperty C`. -/
/-
**CategoryTheory.MorphismProperty.toSet** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：toSet : Set (Arrow C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set in `Set (Arrow C)` which corresponds to `P : MorphismProperty C`.
-/
def toSet : Set (Arrow C) := Set.ofPred (fun f ↦ P f.hom)
/-
**CategoryTheory.MorphismProperty.mem_toSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：mem_toSet_iff (f : Arrow C) : f in P.toSet ↔ P f.hom
参数：f : Arrow C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toSet_iff (f : Arrow C) : f ∈ P.toSet ↔ P f.hom := Iff.rfl
/-
**CategoryTheory.MorphismProperty.toSet_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：toSet_iSup {ι : Type*} (W : ι -> MorphismProperty C) : (⨆ i, W i).toSet = 
⋃ i, (W i).toSet
参数：W : ι -> MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toSet_iSup {ι : Type*} (W : ι → MorphismProperty C) :
    (⨆ i, W i).toSet = ⋃ i, (W i).toSet := by
  ext
  simp [mem_toSet_iff]
/-
**CategoryTheory.MorphismProperty.toSet_max** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：toSet_max (W₁ W₂ : MorphismProperty C) : (W₁ ⊔ W₂).toSet = W₁.toSet union 
W₂.toSet
参数：W₁ W₂ : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSet_max (W₁ W₂ : MorphismProperty C) :
    (W₁ ⊔ W₂).toSet = W₁.toSet ∪ W₂.toSet := rfl

/-- The family of morphisms indexed by `P.toSet` which corresponds
to `P : MorphismProperty C`, see `MorphismProperty.ofHoms_homFamily`. -/
/-
**CategoryTheory.MorphismProperty.homFamily** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：homFamily (f : P.toSet) : f.1.left ⟶ f.1.right
参数：f : P.toSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of morphisms indexed by `P.toSet` which corresponds
to `P : MorphismProperty C`, see `MorphismProperty.ofHoms_homFamily`.
-/
def homFamily (f : P.toSet) : f.1.left ⟶ f.1.right := f.1.hom
/-
**CategoryTheory.MorphismProperty.homFamily_apply** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：homFamily_apply (f : P.toSet) : P.homFamily f = f.1.hom
参数：f : P.toSet。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homFamily_apply (f : P.toSet) : P.homFamily f = f.1.hom := rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.homFamily_arrow_mk** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：homFamily_arrow_mk {X Y : C} (f : X ⟶ Y) (hf : P f) : P.homFamily ⟨Arrow.m
k f, hf⟩ = f
参数：f : X ⟶ Y；hf : P f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homFamily_arrow_mk {X Y : C} (f : X ⟶ Y) (hf : P f) :
    P.homFamily ⟨Arrow.mk f, hf⟩ = f := rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.arrow_mk_mem_toSet_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：arrow_mk_mem_toSet_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma arrow_mk_mem_toSet_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f ∈ P.toSet ↔ P f := Iff.rfl
/-
**CategoryTheory.MorphismProperty.of_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：of_eq {X Y : C} {f : X ⟶ Y} (hf : P f) {X' Y' : C} {f' : X' ⟶ Y'} (hX : X 
= X') (hY : Y = Y') (h : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY) : P f'
参数：hf : P f；hX : X = X'；hY : Y = Y'；h : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.arrow_mk_mem_toSet_iff`：arrow_mk_mem_toS
et_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Arrow.mk_eq_mk_iff`：mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶
 Y) (f' : X' ⟶ Y') : Arrow.mk f = Arrow.mk f' ↔ exists (hX : X = X') (hY : Y = Y
'), f = eqToHom hX ≫ f'…
-/
lemma of_eq {X Y : C} {f : X ⟶ Y} (hf : P f)
    {X' Y' : C} {f' : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (h : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY) :
    P f' := by
  rw [← P.arrow_mk_mem_toSet_iff] at hf ⊢
  rwa [(Arrow.mk_eq_mk_iff f' f).2 ⟨hX.symm, hY.symm, h⟩]

end

/-- The class of morphisms given by a family of morphisms `f i : X i ⟶ Y i`. -/
/-
**CategoryTheory.MorphismProperty.ofHoms** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 u_3} → {X Y : ι → C} → ((i : ι) → X i ⟶ Y i) → CategoryTheory.MorphismProperty 
C
参数：(i : ι) → X i ⟶ Y i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms given by a family of morphisms `f i : X i ⟶ Y i`.
-/
inductive ofHoms {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) : MorphismProperty C
  | mk (i : ι) : ofHoms f (f i)
/-
**CategoryTheory.MorphismProperty.ofHoms_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：ofHoms_iff {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} 
(g : A ⟶ B) : ofHoms f g ↔ exists i, Arrow.mk g = Arrow.mk (f i)
参数：f : forall i, X i ⟶ Y i；g : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.arrow_mk_mem_toSet_iff`：arrow_mk_mem_toS
et_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f
-/
lemma ofHoms_iff {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) :
    ofHoms f g ↔ ∃ i, Arrow.mk g = Arrow.mk (f i) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff, h, arrow_mk_mem_toSet_iff]
    constructor

@[simp]
/-
**CategoryTheory.MorphismProperty.ofHoms_homFamily** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：ofHoms_homFamily (P : MorphismProperty C) : ofHoms P.homFamily = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofHoms_homFamily (P : MorphismProperty C) : ofHoms P.homFamily = P := by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : P.toSet)⟩
/-
**CategoryTheory.MorphismProperty.iSup_ofHoms** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：iSup_ofHoms {α : Type*} {ι : α -> Type*} {A B : forall a, ι a -> C} (f : f
orall a, forall i, A a i ⟶ B a i) : ⨆ (a : α), ofHoms (f a) = ofHoms (fun (j : Σ
 (a : α), ι a) => f j.1 j.2)
参数：f : forall a, forall i, A a i ⟶ B a i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_ofHoms {α : Type*} {ι : α → Type*} {A B : ∀ a, ι a → C}
    (f : ∀ a, ∀ i, A a i ⟶ B a i) :
    ⨆ (a : α), ofHoms (f a) = ofHoms (fun (j : Σ (a : α), ι a) ↦ f j.1 j.2) := by
  ext f
  simp [ofHoms_iff]

@[simp]
/-
**CategoryTheory.MorphismProperty.ofHoms_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：ofHoms_le_iff {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) (P : Mo
rphismProperty C) : ofHoms f <= P ↔ forall i, P (f i)
参数：f : forall i, X i ⟶ Y i；P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHoms_le_iff {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) (P : MorphismProperty C) :
    ofHoms f ≤ P ↔ ∀ i, P (f i) :=
  ⟨fun h i ↦ h _ (ofHoms.mk i), fun h _ _ _⟨i⟩ ↦ h i⟩

/-- The class of morphisms containing a single morphism. -/
/-
**CategoryTheory.MorphismProperty.single** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：single {X Y : C} (f : X ⟶ Y) : MorphismProperty C
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms containing a single morphism.
-/
abbrev single {X Y : C} (f : X ⟶ Y) : MorphismProperty C := .ofHoms (fun (_ : Unit) ↦ f)
/-
**CategoryTheory.MorphismProperty.prop_single** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：prop_single {X Y : C} (f : X ⟶ Y) : (single f) f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop_single {X Y : C} (f : X ⟶ Y) : (single f) f := by tauto

@[simp high]
/-
**CategoryTheory.MorphismProperty.single_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：single_le_iff (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : single f <=
 W ↔ W f
参数：W : MorphismProperty C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma single_le_iff (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : single f ≤ W ↔ W f := by
  simp

end

section

variable {C : Type u} [CategoryStruct.{v} C]

/-- A morphism property `P` satisfies `P.RespectsRight Q` if it is stable under post-composition
with morphisms satisfying `Q`, i.e. whenever `P` holds for `f` and `Q` holds for `i` then `P`
holds for `f ≫ i`. -/
/-
**CategoryTheory.MorphismProperty.RespectsRight** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property `P` satisfies `P.RespectsRight Q` if it is stable under post
-composition
with morphisms satisfying `Q`, i.e. whenever `P` holds for `f` and `Q` holds for
 `i` then `P`
holds for `f ≫ i`.
-/
class RespectsRight (P Q : MorphismProperty C) : Prop where
  postcomp {X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f) : P (f ≫ i)

/-- A morphism property `P` satisfies `P.RespectsLeft Q` if it is stable under
pre-composition with morphisms satisfying `Q`, i.e. whenever `P` holds for `f`
and `Q` holds for `i` then `P` holds for `i ≫ f`. -/
/-
**CategoryTheory.MorphismProperty.RespectsLeft** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property `P` satisfies `P.RespectsLeft Q` if it is stable under
pre-composition with morphisms satisfying `Q`, i.e. whenever `P` holds for `f`
and `Q` holds for `i` then `P` holds for `i ≫ f`.
-/
class RespectsLeft (P Q : MorphismProperty C) : Prop where
  precomp {X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f) : P (i ≫ f)

/-- A morphism property `P` satisfies `P.Respects Q` if it is stable under composition on the
left and right by morphisms satisfying `Q`. -/
/-
**CategoryTheory.MorphismProperty.Respects** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.CategoryStruct.{v, u} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property `P` satisfies `P.Respects Q` if it is stable under compositi
on on the
left and right by morphisms satisfying `Q`.
-/
class Respects (P Q : MorphismProperty C) : Prop extends P.RespectsLeft Q, P.RespectsRight Q where
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P Q : MorphismProperty C) [P.RespectsLeft Q] [P.RespectsRight Q] : P.Respects Q where
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P Q : MorphismProperty C) [P.RespectsLeft Q] : P.op.RespectsRight Q.op where
  postcomp i hi f hf := RespectsLeft.precomp (Q := Q) i.unop hi f.unop hf
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P Q : MorphismProperty C) [P.RespectsRight Q] : P.op.RespectsLeft Q.op where
  precomp i hi f hf := RespectsRight.postcomp (Q := Q) i.unop hi f.unop hf
/-
**CategoryTheory.MorphismProperty.RespectsLeft.inf** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.RespectsLeft`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] (P₁ P₂ Q : 
CategoryTheory.MorphismProperty C)   [P₁.RespectsLeft Q] [P₂.RespectsLeft Q], (P
₁ ⊓ P₂).RespectsLeft Q
参数：P₁ P₂ Q : CategoryTheory.MorphismProperty C；P₁ ⊓ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance RespectsLeft.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
    [P₂.RespectsLeft Q] : (P₁ ⊓ P₂).RespectsLeft Q where
  precomp i hi f hf := ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩
/-
**CategoryTheory.MorphismProperty.RespectsLeft.sInf** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.RespectsLeft`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] {W : Set (C
ategoryTheory.MorphismProperty C)}   {Q : CategoryTheory.MorphismProperty C}, (∀
 W' ∈ W, W'.RespectsLeft Q) → (sInf W).RespectsLeft Q
参数：CategoryTheory.MorphismProperty C；∀ W' ∈ W, W'.RespectsLeft Q；sInf W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.sInf_iff`：sInf_iff (S : Set (MorphismPro
perty C)) {X Y : C} (f : X ⟶ Y) : sInf S f ↔ forall W in S, W f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
-/
lemma RespectsLeft.sInf {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
    (h : ∀ W' ∈ W, W'.RespectsLeft Q) : (sInf W).RespectsLeft Q where
  precomp _ hi _ hf := by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' ↦ (h _ hW').precomp _ hi _ (hf _ hW')
/-
**CategoryTheory.MorphismProperty.RespectsLeft.iInf** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.RespectsLeft`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] {ι : Type u
_1}   {W : ι → CategoryTheory.MorphismProperty C} {Q : CategoryTheory.MorphismPr
operty C} [∀ (i : ι), (W i).RespectsLeft Q],   (⨅ i, W i).RespectsLeft Q
参数：i : ι；W i；⨅ i, W i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.sInf`：∀ {C : Type u} [inst 
: CategoryTheory.CategoryStruct.{v, u} C] {W : Set (CategoryTheory.MorphismPrope
rty C)}   {Q : CategoryTheory.MorphismP…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance RespectsLeft.iInf {ι : Type*} {W : ι → MorphismProperty C} {Q : MorphismProperty C}
    [∀ i, (W i).RespectsLeft Q] : (⨅ i, W i).RespectsLeft Q := by
  rw [← sInf_range]
  exact sInf (by simpa)
/-
**CategoryTheory.MorphismProperty.RespectsRight.inf** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.RespectsRight`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] (P₁ P₂ Q : 
CategoryTheory.MorphismProperty C)   [P₁.RespectsRight Q] [P₂.RespectsRight Q], 
(P₁ ⊓ P₂).RespectsRight Q
参数：P₁ P₂ Q : CategoryTheory.MorphismProperty C；P₁ ⊓ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance RespectsRight.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
    [P₂.RespectsRight Q] : (P₁ ⊓ P₂).RespectsRight Q where
  postcomp i hi f hf := ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩
/-
**CategoryTheory.MorphismProperty.RespectsRight.sInf** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.RespectsRight`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] {W : Set (C
ategoryTheory.MorphismProperty C)}   {Q : CategoryTheory.MorphismProperty C}, (∀
 W' ∈ W, W'.RespectsRight Q) → (sInf W).RespectsRight Q
参数：CategoryTheory.MorphismProperty C；∀ W' ∈ W, W'.RespectsRight Q；sInf W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.sInf_iff`：sInf_iff (S : Set (MorphismPro
perty C)) {X Y : C} (f : X ⟶ Y) : sInf S f ↔ forall W in S, W f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
-/
lemma RespectsRight.sInf {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
    (h : ∀ W' ∈ W, W'.RespectsRight Q) : (sInf W).RespectsRight Q where
  postcomp _ hi _ hf := by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' ↦ (h _ hW').postcomp _ hi _ (hf _ hW')
/-
**CategoryTheory.MorphismProperty.RespectsRight.iInf** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.RespectsRight`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] {ι : Type u
_1}   {W : ι → CategoryTheory.MorphismProperty C} {Q : CategoryTheory.MorphismPr
operty C}   [∀ (i : ι), (W i).RespectsRight Q], (⨅ i, W i).RespectsRight Q
参数：i : ι；W i；⨅ i, W i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.sInf`：∀ {C : Type u} [inst
 : CategoryTheory.CategoryStruct.{v, u} C] {W : Set (CategoryTheory.MorphismProp
erty C)}   {Q : CategoryTheory.MorphismP…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance RespectsRight.iInf {ι : Type*} {W : ι → MorphismProperty C} {Q : MorphismProperty C}
    [∀ i, (W i).RespectsRight Q] : (⨅ i, W i).RespectsRight Q := by
  rw [← sInf_range]
  exact sInf (by simpa)

end

section

variable (C : Type u) [Category.{v} C]

/-- The `MorphismProperty C` satisfied by isomorphisms in `C`. -/
/-
**CategoryTheory.MorphismProperty.isomorphisms** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：isomorphisms : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty C` satisfied by isomorphisms in `C`.
-/
abbrev isomorphisms : MorphismProperty C := fun _ _ f => IsIso f

/-- The `MorphismProperty C` satisfied by monomorphisms in `C`. -/
/-
**CategoryTheory.MorphismProperty.monomorphisms** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：monomorphisms : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty C` satisfied by monomorphisms in `C`.
-/
abbrev monomorphisms : MorphismProperty C := fun _ _ f => Mono f

/-- The `MorphismProperty C` satisfied by epimorphisms in `C`. -/
/-
**CategoryTheory.MorphismProperty.epimorphisms** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：epimorphisms : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty C` satisfied by epimorphisms in `C`.
-/
abbrev epimorphisms : MorphismProperty C := fun _ _ f => Epi f

@[simp]
/-
**CategoryTheory.MorphismProperty.op_isomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：op_isomorphisms : (isomorphisms C).op = isomorphisms Cᵒᵖ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
-/
lemma op_isomorphisms : (isomorphisms C).op = isomorphisms Cᵒᵖ := by
  ext
  apply isIso_unop_iff

section

variable {C}

/-- `P` respects isomorphisms, if it respects the morphism property `isomorphisms C`, i.e.
it is stable under pre- and postcomposition with isomorphisms. -/
/-
**CategoryTheory.MorphismProperty.RespectsIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：RespectsIso (P : MorphismProperty C) : Prop
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` respects isomorphisms, if it respects the morphism property `isomorphisms C`
, i.e.
it is stable under pre- and postcomposition with isomorphisms.
-/
abbrev RespectsIso (P : MorphismProperty C) : Prop := P.Respects (isomorphisms C)
/-
**CategoryTheory.MorphismProperty.RespectsIso.inf** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P Q : CategoryTh
eory.MorphismProperty C) [P.RespectsIso]   [Q.RespectsIso], (P ⊓ Q).RespectsIso
参数：P Q : CategoryTheory.MorphismProperty C；P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.inf`：∀ {C : Type u} [inst :
 CategoryTheory.CategoryStruct.{v, u} C] (P₁ P₂ Q : CategoryTheory.MorphismPrope
rty C)   [P₁.RespectsLeft Q] [P₂.Respe…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.inf`：∀ {C : Type u} [inst 
: CategoryTheory.CategoryStruct.{v, u} C] (P₁ P₂ Q : CategoryTheory.MorphismProp
erty C)   [P₁.RespectsRight Q] [P₂.Resp…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
-/
instance RespectsIso.inf (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso] :
    (P ⊓ Q).RespectsIso where

@[deprecated (since := "2026-05-04")] alias inf := RespectsIso.inf
/-
**CategoryTheory.MorphismProperty.RespectsIso.sInf** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : Set (Categor
yTheory.MorphismProperty C)},   (∀ W' ∈ W, W'.RespectsIso) → (sInf W).RespectsIs
o
参数：CategoryTheory.MorphismProperty C；∀ W' ∈ W, W'.RespectsIso；sInf W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.sInf`：∀ {C : Type u} [inst 
: CategoryTheory.CategoryStruct.{v, u} C] {W : Set (CategoryTheory.MorphismPrope
rty C)}   {Q : CategoryTheory.MorphismP…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.sInf`：∀ {C : Type u} [inst
 : CategoryTheory.CategoryStruct.{v, u} C] {W : Set (CategoryTheory.MorphismProp
erty C)}   {Q : CategoryTheory.MorphismP…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
-/
lemma RespectsIso.sInf {W : Set (MorphismProperty C)} (h : ∀ W' ∈ W, W'.RespectsIso) :
    (sInf W).RespectsIso where
  toRespectsLeft := RespectsLeft.sInf (fun W' hW' ↦ (h W' hW').toRespectsLeft)
  toRespectsRight := RespectsRight.sInf (fun W' hW' ↦ (h W' hW').toRespectsRight)
/-
**CategoryTheory.MorphismProperty.RespectsIso.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {W
 : ι → CategoryTheory.MorphismProperty C}   [∀ (i : ι), (W i).RespectsIso], (⨅ i
, W i).RespectsIso
参数：i : ι；W i；⨅ i, W i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.sInf`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {W : Set (CategoryTheory.MorphismProperty C)}
,   (∀ W' ∈ W, W'.RespectsIso) → (sInf…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance RespectsIso.iInf {ι : Type*} {W : ι → MorphismProperty C} [∀ i, (W i).RespectsIso] :
    (⨅ i, W i).RespectsIso := by
  rw [← sInf_range]
  exact sInf (by simpa)
/-
**CategoryTheory.MorphismProperty.RespectsIso.mk** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty C),   (∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (Categ
oryTheory.CategoryStruct.comp e.hom f)) →     (∀ {X Y Z : C} (e : Y ≅ Z) (f : X 
⟶ Y), P f → P (CategoryTheory.CategoryStruct.comp f e.hom)) → P.RespectsIso
参数：P : CategoryTheory.MorphismProperty C；∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), 
P f → P (CategoryTheory.CategoryStruct.comp e.hom f)；∀ {X Y Z : C} (e : Y ≅ Z) (
f : X ⟶ Y), P f → P (CategoryTheory.CategoryStruct.comp f e.hom)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RespectsIso.mk (P : MorphismProperty C)
    (hprecomp : ∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z) (_ : P f), P (e.hom ≫ f))
    (hpostcomp : ∀ {X Y Z : C} (e : Y ≅ Z) (f : X ⟶ Y) (_ : P f), P (f ≫ e.hom)) :
    P.RespectsIso where
  precomp e (_ : IsIso e) f hf := hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf
/-
**CategoryTheory.MorphismProperty.RespectsIso.precomp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty C) [P.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) [CategoryTheory
.IsIso e] (f : Y ⟶ Z), P f → P (CategoryTheory.CategoryStruct.comp e f)
参数：P : CategoryTheory.MorphismProperty C；e : X ⟶ Y；f : Y ⟶ Z；CategoryTheory.Cate
goryStruct.comp e f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
-/
lemma RespectsIso.precomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] (f : Y ⟶ Z) (hf : P f) : P (e ≫ f) :=
  RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RespectsIso (⊤ : MorphismProperty C) where
  precomp _ _ _ _ := trivial
  postcomp _ _ _ _ := trivial
/-
**CategoryTheory.MorphismProperty.RespectsIso.postcomp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty C) [P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) [CategoryTheory
.IsIso e] (f : X ⟶ Y), P f → P (CategoryTheory.CategoryStruct.comp f e)
参数：P : CategoryTheory.MorphismProperty C；e : Y ⟶ Z；f : X ⟶ Y；CategoryTheory.Cate
goryStruct.comp f e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
-/
lemma RespectsIso.postcomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
    [IsIso e] (f : X ⟶ Y) (hf : P f) : P (f ≫ e) :=
  RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf
/-
**CategoryTheory.MorphismProperty.RespectsIso.op** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty C) [P.RespectsIso],   P.op.RespectsIso
参数：P : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.precomp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P
.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) […
-/
instance RespectsIso.op (P : MorphismProperty C) [RespectsIso P] : RespectsIso P.op where
  precomp e (_ : IsIso e) f hf := postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf
/-
**CategoryTheory.MorphismProperty.RespectsIso.unop** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty Cᵒᵖ) [P.RespectsIso],   P.unop.RespectsIso
参数：P : CategoryTheory.MorphismProperty Cᵒᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.precomp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P
.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) […
-/
instance RespectsIso.unop (P : MorphismProperty Cᵒᵖ) [RespectsIso P] : RespectsIso P.unop where
  precomp e (_ : IsIso e) f hf := postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

/-- The closure by isomorphisms of a `MorphismProperty` -/
/-
**CategoryTheory.MorphismProperty.isoClosure** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：isoClosure (P : MorphismProperty C) : MorphismProperty C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure by isomorphisms of a `MorphismProperty`
-/
def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∃ (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)
/-
**CategoryTheory.MorphismProperty.le_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：le_isoClosure (P : MorphismProperty C) : P <= P.isoClosure
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_isoClosure (P : MorphismProperty C) : P ≤ P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.isoClosure_respectsIso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_respectsIso (P : MorphismProperty C) : RespectsIso P.isoClosure
 where precomp
参数：P : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Arrow.w_mk_right_assoc`：∀ {T : Type u} [inst : CategoryTh
eory.Category.{v, u} T] {f : CategoryTheory.Arrow T} {X Y : T} {g : X ⟶ Y}   (sq
 : f ⟶ CategoryTheory.Arrow…
-/
instance isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure where
  precomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩
/-
**CategoryTheory.MorphismProperty.monotone_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：monotone_isoClosure : Monotone (isoClosure (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_isoClosure : Monotone (isoClosure (C := C)) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩
/-
**CategoryTheory.MorphismProperty.cancel_left_of_respectsIso** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {
X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
参数：P : MorphismProperty C；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.precomp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P
.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) […
-/
theorem cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩
/-
**CategoryTheory.MorphismProperty.cancel_right_of_respectsIso** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] 
{X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
参数：P : MorphismProperty C；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
-/
theorem cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩
/-
**CategoryTheory.MorphismProperty.comma_iso_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：comma_iso_iff (P : MorphismProperty C) [P.RespectsIso] {A B : Type*} [Cate
gory* A] [Category* B] {L : A ⥤ C} {R : B ⥤ C} {f g : Comma L R} (e : f ≅ g) : P
 f.hom ↔ P g.hom
参数：P : MorphismProperty C；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Comma.instIsIsoLeft`：∀ {A : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 B]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Comma.inv_left_hom_right`：∀ {B : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} B] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} A]   {T : Type u₃} [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Comma.instIsIsoRight`：∀ {B : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} B] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   {T : Type u₃} [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comma_iso_iff (P : MorphismProperty C) [P.RespectsIso]
    {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ C} {R : B ⥤ C} {f g : Comma L R} (e : f ≅ g) :
    P f.hom ↔ P g.hom := by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]
/-
**CategoryTheory.MorphismProperty.arrow_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C} (e 
: f ≅ g) : P f.hom ↔ P g.hom
参数：P : MorphismProperty C；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comma_iso_iff`：comma_iso_iff (P : Morphi
smProperty C) [P.RespectsIso] {A B : Type*} [Category* A] [Category* B] {L : A ⥤
 C} {R : B ⥤ C} {f g : Comma L R} (…
-/
theorem arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom :=
  P.comma_iso_iff e
/-
**CategoryTheory.MorphismProperty.arrow_mk_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f
 : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g
参数：P : MorphismProperty C；e : Arrow.mk f ≅ Arrow.mk g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_iso_iff`：arrow_iso_iff (P : Morphi
smProperty C) [RespectsIso P] {f g : Arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom
-/
theorem arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  P.arrow_iso_iff e

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.MorphismProperty C),   (∀ (f g : CategoryTheory.Arrow C) (x : f ≅ g), P f.hom
 → P g.hom) → P.RespectsIso
参数：P : CategoryTheory.MorphismProperty C；∀ (f g : CategoryTheory.Arrow C) (x : f
 ≅ g), P f.hom → P g.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp
/-
**CategoryTheory.MorphismProperty.isoClosure_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_eq_iff (P : MorphismProperty C) : P.isoClosure = P ↔ P.Respects
Iso
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
-/
lemma isoClosure_eq_iff (P : MorphismProperty C) :
    P.isoClosure = P ↔ P.RespectsIso := by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP ↦ le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'
/-
**CategoryTheory.MorphismProperty.isoClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] : P.isoClosure
 = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_eq_iff`：isoClosure_eq_iff (P 
: MorphismProperty C) : P.isoClosure = P ↔ P.RespectsIso
-/
lemma isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] :
    P.isoClosure = P := by rwa [isoClosure_eq_iff]

@[simp]
/-
**CategoryTheory.MorphismProperty.isoClosure_isoClosure** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_isoClosure (P : MorphismProperty C) : P.isoClosure.isoClosure =
 P.isoClosure
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_eq_self`：isoClosure_eq_self (
P : MorphismProperty C) [P.RespectsIso] : P.isoClosure = P
-/
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure.isoClosure_eq_self
/-
**CategoryTheory.MorphismProperty.isoClosure_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] : P.isoClosur
e <= Q ↔ P <= Q
参数：P Q : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
· 使用引理 `CategoryTheory.MorphismProperty.monotone_isoClosure`：monotone_isoClosure
 : Monotone (isoClosure (C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_eq_self`：isoClosure_eq_self (
P : MorphismProperty C) [P.RespectsIso] : P.isoClosure = P
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] :
    P.isoClosure ≤ Q ↔ P ≤ Q := by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

section

variable {D : Type*} [Category* D]

/-
**CategoryTheory.MorphismProperty.isoClosure_strictMap_le** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isoClosure_strictMap_le (P : MorphismProperty C) (F : C ⥤ D) : P.isoClosur
e.strictMap F <= (P.strictMap F).isoClosure
参数：P : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoClosure_strictMap_le (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.strictMap F ≤ (P.strictMap F).isoClosure :=
  fun _ _ _ ⟨⟨_, _, _, hf, ⟨i⟩⟩⟩ ↦ ⟨_, _, _, ⟨hf⟩, ⟨F.mapArrow.mapIso i⟩⟩
/-
**CategoryTheory.MorphismProperty.map_eq_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：map_eq_isoClosure (W : MorphismProperty C) (F : C ⥤ D) : W.map F = (W.stri
ctMap F).isoClosure
参数：W : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma map_eq_isoClosure (W : MorphismProperty C) (F : C ⥤ D) :
    W.map F = (W.strictMap F).isoClosure := by
  ext
  refine ⟨fun ⟨_, _, f, hf, hf'⟩ ↦ ⟨_, _, _, ⟨hf⟩, hf'⟩, fun ⟨_, _, f, hf, hf'⟩ ↦ ?_⟩
  obtain ⟨hf⟩ := hf
  exact ⟨_, _, _, hf, hf'⟩
/-
**CategoryTheory.MorphismProperty.map_respectsIso** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) : (P.map F).RespectsI
so
参数：P : MorphismProperty C；F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_isoClosure`：map_eq_isoClosure (W 
: MorphismProperty C) (F : C ⥤ D) : W.map F = (W.strictMap F).isoClosure
-/
instance map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  rw [map_eq_isoClosure]
  infer_instance
/-
**CategoryTheory.MorphismProperty.map_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D) [
RespectsIso Q] : P.map F <= Q ↔ P <= Q.inverseImage F
参数：P : MorphismProperty C；Q : MorphismProperty D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_isoClosure`：map_eq_isoClosure (W 
: MorphismProperty C) (F : C ⥤ D) : W.map F = (W.strictMap F).isoClosure
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_le_iff`：isoClosure_le_iff (P 
Q : MorphismProperty C) [Q.RespectsIso] : P.isoClosure <= Q ↔ P <= Q
· 使用引理 `CategoryTheory.MorphismProperty.strictMap_le_iff_le_inverseImage`：strict
Map_le_iff_le_inverseImage (F : C ⥤ D) (P : MorphismProperty C) (P' : MorphismPr
operty D) : P.strictMap F <= P' ↔ P <= P'.inverseImage…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q] :
    P.map F ≤ Q ↔ P ≤ Q.inverseImage F := by
  rw [map_eq_isoClosure, isoClosure_le_iff, strictMap_le_iff_le_inverseImage]

@[simp]
/-
**CategoryTheory.MorphismProperty.map_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) : P.isoClosure.map F =
 P.map F
参数：P : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_isoClosure`：map_eq_isoClosure (W 
: MorphismProperty C) (F : C ⥤ D) : W.map F = (W.strictMap F).isoClosure
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_le_iff`：isoClosure_le_iff (P 
Q : MorphismProperty C) [Q.RespectsIso] : P.isoClosure <= Q ↔ P <= Q
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_strictMap_le`：isoClosure_stri
ctMap_le (P : MorphismProperty C) (F : C ⥤ D) : P.isoClosure.strictMap F <= (P.s
trictMap F).isoClosure
· 使用引理 `CategoryTheory.MorphismProperty.monotone_map`：monotone_map (F : C ⥤ D) :
 Monotone (map · F)
· 使用引理 `CategoryTheory.MorphismProperty.le_isoClosure`：le_isoClosure (P : Morphi
smProperty C) : P <= P.isoClosure
-/
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply le_antisymm
  · rw [map_eq_isoClosure, map_eq_isoClosure, isoClosure_le_iff]
    exact isoClosure_strictMap_le _ _
  · exact monotone_map _ (le_isoClosure P)
/-
**CategoryTheory.MorphismProperty.map_id_eq_isoClosure** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：map_id_eq_isoClosure (P : MorphismProperty C) : P.map (𝟭 _) = P.isoClosure
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := rfl
/-
**CategoryTheory.MorphismProperty.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：map_id (P : MorphismProperty C) [RespectsIso P] : P.map (𝟭 _) = P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_id_eq_isoClosure`：map_id_eq_isoClosu
re (P : MorphismProperty C) : P.map (𝟭 _) = P.isoClosure
· 使用引理 `CategoryTheory.MorphismProperty.isoClosure_eq_self`：isoClosure_eq_self (
P : MorphismProperty C) [P.RespectsIso] : P.isoClosure = P
-/
lemma map_id (P : MorphismProperty C) [RespectsIso P] :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure, P.isoClosure_eq_self]

@[simp]
/-
**CategoryTheory.MorphismProperty.map_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category* E] (G 
: D ⥤ E) : (P.map F).map G = P.map (F ⋙ G)
参数：P : MorphismProperty C；F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_le_iff`：map_le_iff (P : MorphismProp
erty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q] : P.map F <= Q ↔ P 
<= Q.inverseImage F
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_map`：map_mem_map (P : MorphismPr
operty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.map F) (F.map f)
-/
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)
/-
**CategoryTheory.MorphismProperty.RespectsIso.inverseImage** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   (P : CategoryTheory.MorphismProp
erty D) [P.RespectsIso] (F : CategoryTheory.Functor C D),   (P.inverseImage F).R
espectsIso
参数：P : CategoryTheory.MorphismProperty D；F : CategoryTheory.Functor C D；P.invers
eImage F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
instance RespectsIso.inverseImage (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf
/-
**CategoryTheory.MorphismProperty.map_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) : P.map F
 = P.map G
参数：P : MorphismProperty C；e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices ∀ {F G : C ⥤ D} (_ : F ≅ G), P.map F ≤ P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩
/-
**CategoryTheory.MorphismProperty.map_inverseImage_le** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) : (P.inverseImage
 F).map F <= P.isoClosure
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F ≤ P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩
/-
**CategoryTheory.MorphismProperty.inverseImage_equivalence_inverse_eq_map_functo
r** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_equivalence_inverse_eq_map_functor (P : MorphismProperty D) [
RespectsIso P] (E : C ≌ D) : P.inverseImage E.functor = P.map E.inverse
参数：P : MorphismProperty D；E : C ≌ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.map_le_iff`：map_le_iff (P : MorphismProp
erty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q] : P.map F <= Q ↔ P 
<= Q.inverseImage F
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.inverseImage`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheo
ry.Category.{v_1, u_1} D]   (P : CategoryTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) [RespectsIso P] (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf
/-
**CategoryTheory.MorphismProperty.inverseImage_equivalence_functor_eq_map_invers
e** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_equivalence_functor_eq_map_inverse (Q : MorphismProperty C) [
RespectsIso Q] (E : C ≌ D) : Q.inverseImage E.inverse = Q.map E.functor
参数：Q : MorphismProperty C；E : C ≌ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_equivalence_inverse_eq_map_
functor`：inverseImage_equivalence_inverse_eq_map_functor (P : MorphismProperty D
) [RespectsIso P] (E : C ≌ D) : P.inverseImage E.functor = P.map E.in…
-/
lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) [RespectsIso Q] (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q E.symm
/-
**CategoryTheory.MorphismProperty.map_inverseImage_eq_of_isEquivalence** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：map_inverseImage_eq_of_isEquivalence (P : MorphismProperty D) [P.RespectsI
so] (F : C ⥤ D) [F.IsEquivalence] : (P.inverseImage F).map F = P
参数：P : MorphismProperty D；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_equivalence_inverse_eq_map_
functor`：inverseImage_equivalence_inverse_eq_map_functor (P : MorphismProperty D
) [RespectsIso P] (E : C ≌ D) : P.inverseImage E.functor = P.map E.in…
· 使用引理 `CategoryTheory.MorphismProperty.map_map`：map_map (P : MorphismProperty C
) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) : (P.map F).map G = P.map (F
 ⋙ G)
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_of_iso`：map_eq_of_iso (P : Morphi
smProperty C) {F G : C ⥤ D} (e : F ≅ G) : P.map F = P.map G
· 使用引理 `CategoryTheory.MorphismProperty.map_id`：map_id (P : MorphismProperty C) 
[RespectsIso P] : P.map (𝟭 _) = P
-/
lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]
/-
**CategoryTheory.MorphismProperty.inverseImage_map_eq_of_isEquivalence** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_map_eq_of_isEquivalence (P : MorphismProperty C) [P.RespectsI
so] (F : C ⥤ D) [F.IsEquivalence] : (P.map F).inverseImage F = P
参数：P : MorphismProperty C；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_equivalence_inverse_eq_map_
functor`：inverseImage_equivalence_inverse_eq_map_functor (P : MorphismProperty D
) [RespectsIso P] (E : C ≌ D) : P.inverseImage E.functor = P.map E.in…
· 使用引理 `CategoryTheory.MorphismProperty.map_map`：map_map (P : MorphismProperty C
) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) : (P.map F).map G = P.map (F
 ⋙ G)
· 使用引理 `CategoryTheory.MorphismProperty.map_eq_of_iso`：map_eq_of_iso (P : Morphi
smProperty C) {F G : C ⥤ D} (e : F ≅ G) : P.map F = P.map G
· 使用引理 `CategoryTheory.MorphismProperty.map_id`：map_id (P : MorphismProperty C) 
[RespectsIso P] : P.map (𝟭 _) = P
-/
lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

end

end

section

variable {C}
variable {X Y : C} (f : X ⟶ Y)

@[simp]
/-
**CategoryTheory.MorphismProperty.isomorphisms.iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.isomorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y),   CategoryTheory.MorphismProperty.isomorphisms C f ↔ CategoryTheory.IsIso 
f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isomorphisms.iff : (isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.monomorphisms.iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.monomorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y),   CategoryTheory.MorphismProperty.monomorphisms C f ↔ CategoryTheory.Mono 
f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monomorphisms.iff : (monomorphisms C) f ↔ Mono f := by rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.epimorphisms.iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.epimorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y),   CategoryTheory.MorphismProperty.epimorphisms C f ↔ CategoryTheory.Epi f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem epimorphisms.iff : (epimorphisms C) f ↔ Epi f := by rfl
/-
**CategoryTheory.MorphismProperty.isomorphisms.infer_property** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.isomorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) [hf : CategoryTheory.IsIso f],   CategoryTheory.MorphismProperty.isomorphis
ms C f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isomorphisms.infer_property [hf : IsIso f] : (isomorphisms C) f :=
  hf
/-
**CategoryTheory.MorphismProperty.monomorphisms.infer_property** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.monomorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) [hf : CategoryTheory.Mono f],   CategoryTheory.MorphismProperty.monomorphis
ms C f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monomorphisms.infer_property [hf : Mono f] : (monomorphisms C) f :=
  hf
/-
**CategoryTheory.MorphismProperty.epimorphisms.infer_property** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.epimorphisms`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) [hf : CategoryTheory.Epi f],   CategoryTheory.MorphismProperty.epimorphisms
 C f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem epimorphisms.infer_property [hf : Epi f] : (epimorphisms C) f :=
  hf

end

@[deprecated "Use `op_isomorphisms _` instead." (since := "2026-01-18")]
/-
**CategoryTheory.MorphismProperty.isomorphisms_op** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：isomorphisms_op : (isomorphisms C).op = isomorphisms Cᵒᵖ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.op_isomorphisms`：op_isomorphisms : (isom
orphisms C).op = isomorphisms Cᵒᵖ
-/
lemma isomorphisms_op : (isomorphisms C).op = isomorphisms Cᵒᵖ := op_isomorphisms _
/-
**CategoryTheory.MorphismProperty.RespectsIso.monomorphisms** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.
MorphismProperty.monomorphisms C).RespectsIso
参数：C : Type u；CategoryTheory.MorphismProperty.monomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp
/-
**CategoryTheory.MorphismProperty.RespectsIso.epimorphisms** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.
MorphismProperty.epimorphisms C).RespectsIso
参数：C : Type u；CategoryTheory.MorphismProperty.epimorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp
/-
**CategoryTheory.MorphismProperty.RespectsIso.isomorphisms** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.RespectsIso`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.
MorphismProperty.isomorphisms C).RespectsIso
参数：C : Type u；CategoryTheory.MorphismProperty.isomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

end

/-- If `W₁` and `W₂` are morphism properties on two categories `C₁` and `C₂`,
this is the induced morphism property on `C₁ × C₂`. -/
/-
**CategoryTheory.MorphismProperty.prod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MorphismProperty`。
形式化陈述：prod {C₁ C₂ : Type*} [CategoryStruct C₁] [CategoryStruct C₂] (W₁ : Morphis
mProperty C₁) (W₂ : MorphismProperty C₂) : MorphismProperty (C₁ × C₂)
参数：W₁ : MorphismProperty C₁；W₂ : MorphismProperty C₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W₁` and `W₂` are morphism properties on two categories `C₁` and `C₂`,
this is the induced morphism property on `C₁ × C₂`.
-/
def prod {C₁ C₂ : Type*} [CategoryStruct C₁] [CategoryStruct C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) :
    MorphismProperty (C₁ × C₂) :=
  fun _ _ f => W₁ f.1 ∧ W₂ f.2

/-- If `W j` are morphism properties on categories `C j` for all `j`, this is the
induced morphism property on the category `∀ j, C j`. -/
/-
**CategoryTheory.MorphismProperty.pi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
orphismProperty`。
形式化陈述：pi {J : Type w} {C : J -> Type u} [forall j, Category.{v} (C j)] (W : fora
ll j, MorphismProperty (C j)) : MorphismProperty (forall j, C j)
参数：C j；W : forall j, MorphismProperty (C j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W j` are morphism properties on categories `C j` for all `j`, this is the
induced morphism property on the category `∀ j, C j`.
-/
def pi {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
    (W : ∀ j, MorphismProperty (C j)) : MorphismProperty (∀ j, C j) :=
  fun _ _ f => ∀ j, (W j) (f j)

variable {C} [Category.{v} C]

/-- The morphism property on `J ⥤ C` which is defined objectwise
from `W : MorphismProperty C`. -/
/-
**CategoryTheory.MorphismProperty.functorCategory** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：functorCategory (W : MorphismProperty C) (J : Type*) [Category* J] : Morph
ismProperty (J ⥤ C)
参数：W : MorphismProperty C；J : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property on `J ⥤ C` which is defined objectwise
from `W : MorphismProperty C`.
-/
def functorCategory (W : MorphismProperty C) (J : Type*) [Category* J] :
    MorphismProperty (J ⥤ C) :=
  fun _ _ f => ∀ (j : J), W (f.app j)

/-- Given `W : MorphismProperty C`, this is the morphism property on `Arrow C` of morphisms
whose left and right parts are in `W`. -/
/-
**CategoryTheory.MorphismProperty.arrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：arrow (W : MorphismProperty C) : MorphismProperty (Arrow C)
参数：W : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C`, this is the morphism property on `Arrow C` of mo
rphisms
whose left and right parts are in `W`.
-/
def arrow (W : MorphismProperty C) :
    MorphismProperty (Arrow C) :=
  fun _ _ f => W f.left ∧ W f.right
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty C) [W.RespectsIso] : W.arrow.RespectsIso where
  precomp f (_ : IsIso f) _ h :=
    ⟨RespectsIso.precomp _ _ _ h.1, RespectsIso.precomp _ _ _ h.2⟩
  postcomp f (_ : IsIso f) _ h :=
    ⟨RespectsIso.postcomp _ _ _ h.1, RespectsIso.postcomp _ _ _ h.2⟩

end MorphismProperty

namespace NatTrans

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.isIso_app_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.NatTrans`。
形式化陈述：isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsI
so (α.app X) ↔ IsIso (α.app Y)
参数：α : F ⟶ G；e : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (α.app X) ↔ IsIso (α.app Y) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

end NatTrans

end CategoryTheory

