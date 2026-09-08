/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Categories with classes of fibrations, cofibrations, weak equivalences

We introduce typeclasses `CategoryWithFibrations`, `CategoryWithCofibrations` and
`CategoryWithWeakEquivalences` to express that a category `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" or "weak equivalences".

-/

@[expose] public section

universe v u

namespace HomotopicalAlgebra

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category with fibrations is a category equipped with
a class of morphisms named "fibrations". -/
/-
**HomotopicalAlgebra.CategoryWithFibrations** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homotop
icalAlgebra`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with fibrations is a category equipped with
a class of morphisms named "fibrations".
-/
class CategoryWithFibrations where
  /-- the class of fibrations -/
  fibrations : MorphismProperty C

/-- A category with cofibrations is a category equipped with
a class of morphisms named "cofibrations". -/
/-
**HomotopicalAlgebra.CategoryWithCofibrations** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homot
opicalAlgebra`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with cofibrations is a category equipped with
a class of morphisms named "cofibrations".
-/
class CategoryWithCofibrations where
  /-- the class of cofibrations -/
  cofibrations : MorphismProperty C

/-- A category with weak equivalences is a category equipped with
a class of morphisms named "weak equivalences". -/
/-
**HomotopicalAlgebra.CategoryWithWeakEquivalences** 是 Mathlib 中的一个归纳类型，位于命名空间 `H
omotopicalAlgebra`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with weak equivalences is a category equipped with
a class of morphisms named "weak equivalences".
-/
class CategoryWithWeakEquivalences where
  /-- the class of weak equivalences -/
  weakEquivalences : MorphismProperty C

variable {X Y : C} (f : X ⟶ Y)

section Fib

variable [CategoryWithFibrations C]

/-- The class of fibrations in a category with fibrations. -/
/-
**HomotopicalAlgebra.fibrations** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：fibrations : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of fibrations in a category with fibrations.
-/
def fibrations : MorphismProperty C := CategoryWithFibrations.fibrations

variable {C}

/-- A morphism `f` satisfies `[Fibration f]` if it belongs to `fibrations C`. -/
@[mk_iff]
/-
**HomotopicalAlgebra.Fibration** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (
X ⟶ Y) → [HomotopicalAlgebra.CategoryWithFibrations C] → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` satisfies `[Fibration f]` if it belongs to `fibrations C`.
-/
class Fibration : Prop where
  mem : fibrations C f
/-
**HomotopicalAlgebra.mem_fibrations** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebr
a`。
形式化陈述：mem_fibrations [Fibration f] : fibrations C f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.Fibration.mem`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} {X Y : C} {f : X ⟶ Y}   {inst_1 : HomotopicalAlgebra.Category
WithFibrations C} [sel…
-/
lemma mem_fibrations [Fibration f] : fibrations C f := Fibration.mem

end Fib

section Cof

variable [CategoryWithCofibrations C]

/-- The class of cofibrations in a category with cofibrations. -/
/-
**HomotopicalAlgebra.cofibrations** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra`
。
形式化陈述：cofibrations : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of cofibrations in a category with cofibrations.
-/
def cofibrations : MorphismProperty C := CategoryWithCofibrations.cofibrations

variable {C}

/-- A morphism `f` satisfies `[Cofibration f]` if it belongs to `cofibrations C`. -/
@[mk_iff]
/-
**HomotopicalAlgebra.Cofibration** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomotopicalAlgebra
`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → (X ⟶ Y) → [HomotopicalAlgebra.CategoryWithCofibrations C] → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` satisfies `[Cofibration f]` if it belongs to `cofibrations C`.
-/
class Cofibration : Prop where
  mem : cofibrations C f
/-
**HomotopicalAlgebra.mem_cofibrations** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：mem_cofibrations [Cofibration f] : cofibrations C f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.Cofibration.mem`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} {X Y : C} {f : X ⟶ Y}   {inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C} [s…
-/
lemma mem_cofibrations [Cofibration f] : cofibrations C f := Cofibration.mem

end Cof

section W

variable [CategoryWithWeakEquivalences C]

/-- The class of weak equivalences in a category with weak equivalences. -/
/-
**HomotopicalAlgebra.weakEquivalences** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：weakEquivalences : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of weak equivalences in a category with weak equivalences.
-/
def weakEquivalences : MorphismProperty C := CategoryWithWeakEquivalences.weakEquivalences

variable {C}

/-- A morphism `f` satisfies `[WeakEquivalence f]` if it belongs to `weakEquivalences C`. -/
@[mk_iff]
/-
**HomotopicalAlgebra.WeakEquivalence** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomotopicalAlg
ebra`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → (X ⟶ Y) → [HomotopicalAlgebra.CategoryWithWeakEquivalences C] → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` satisfies `[WeakEquivalence f]` if it belongs to `weakEquivalence
s C`.
-/
class WeakEquivalence : Prop where
  mem : weakEquivalences C f
/-
**HomotopicalAlgebra.mem_weakEquivalences** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra`。
形式化陈述：mem_weakEquivalences [WeakEquivalence f] : weakEquivalences C f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.WeakEquivalence.mem`：∀ {C : Type u} {inst : CategoryT
heory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y}   {inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
-/
lemma mem_weakEquivalences [WeakEquivalence f] : weakEquivalences C f := WeakEquivalence.mem

end W

section TrivFib

variable [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]

/-- A trivial fibration is a morphism that is both a fibration and a weak equivalence. -/
/-
**HomotopicalAlgebra.trivialFibrations** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlg
ebra`。
形式化陈述：trivialFibrations : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial fibration is a morphism that is both a fibration and a weak equivalenc
e.
-/
def trivialFibrations : MorphismProperty C := fibrations C ⊓ weakEquivalences C
/-
**HomotopicalAlgebra.trivialFibrations_sub_fibrations** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra`。
形式化陈述：trivialFibrations_sub_fibrations : trivialFibrations C <= fibrations C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma trivialFibrations_sub_fibrations : trivialFibrations C ≤ fibrations C :=
  fun _ _ _ hf ↦ hf.1
/-
**HomotopicalAlgebra.trivialFibrations_sub_weakEquivalences** 是 Mathlib 中的一个引理，位
于命名空间 `HomotopicalAlgebra`。
形式化陈述：trivialFibrations_sub_weakEquivalences : trivialFibrations C <= weakEquiva
lences C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma trivialFibrations_sub_weakEquivalences : trivialFibrations C ≤ weakEquivalences C :=
  fun _ _ _ hf ↦ hf.2

variable {C}
/-
**HomotopicalAlgebra.mem_trivialFibrations** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra`。
形式化陈述：mem_trivialFibrations [Fibration f] [WeakEquivalence f] : trivialFibration
s C f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.mem_fibrations`：mem_fibrations [Fibration f] : fibrat
ions C f
· 使用引理 `HomotopicalAlgebra.mem_weakEquivalences`：mem_weakEquivalences [WeakEquiv
alence f] : weakEquivalences C f
-/
lemma mem_trivialFibrations [Fibration f] [WeakEquivalence f] :
    trivialFibrations C f :=
  ⟨mem_fibrations f, mem_weakEquivalences f⟩
/-
**HomotopicalAlgebra.mem_trivialFibrations_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：mem_trivialFibrations_iff : trivialFibrations C f ↔ Fibration f ∧ WeakEqui
valence f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.fibration_iff`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Category
WithFibrations C],   H…
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_trivialFibrations_iff :
    trivialFibrations C f ↔ Fibration f ∧ WeakEquivalence f := by
  rw [fibration_iff, weakEquivalence_iff]
  rfl

end TrivFib

section TrivCof

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- A trivial cofibration is a morphism that is both a cofibration and a weak equivalence. -/
/-
**HomotopicalAlgebra.trivialCofibrations** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalA
lgebra`。
形式化陈述：trivialCofibrations : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial cofibration is a morphism that is both a cofibration and a weak equiva
lence.
-/
def trivialCofibrations : MorphismProperty C := cofibrations C ⊓ weakEquivalences C
/-
**HomotopicalAlgebra.trivialCofibrations_sub_cofibrations** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopicalAlgebra`。
形式化陈述：trivialCofibrations_sub_cofibrations : trivialCofibrations C <= cofibratio
ns C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma trivialCofibrations_sub_cofibrations : trivialCofibrations C ≤ cofibrations C :=
  fun _ _ _ hf ↦ hf.1
/-
**HomotopicalAlgebra.trivialCofibrations_sub_weakEquivalences** 是 Mathlib 中的一个引理
，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：trivialCofibrations_sub_weakEquivalences : trivialCofibrations C <= weakEq
uivalences C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma trivialCofibrations_sub_weakEquivalences : trivialCofibrations C ≤ weakEquivalences C :=
  fun _ _ _ hf ↦ hf.2


variable {C}
/-
**HomotopicalAlgebra.mem_trivialCofibrations** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra`。
形式化陈述：mem_trivialCofibrations [Cofibration f] [WeakEquivalence f] : trivialCofib
rations C f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.mem_cofibrations`：mem_cofibrations [Cofibration f] : 
cofibrations C f
· 使用引理 `HomotopicalAlgebra.mem_weakEquivalences`：mem_weakEquivalences [WeakEquiv
alence f] : weakEquivalences C f
-/
lemma mem_trivialCofibrations [Cofibration f] [WeakEquivalence f] :
    trivialCofibrations C f :=
  ⟨mem_cofibrations f, mem_weakEquivalences f⟩
/-
**HomotopicalAlgebra.mem_trivialCofibrations_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：mem_trivialCofibrations_iff : trivialCofibrations C f ↔ Cofibration f ∧ We
akEquivalence f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.cofibration_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C],  …
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_trivialCofibrations_iff :
    trivialCofibrations C f ↔ Cofibration f ∧ WeakEquivalence f := by
  rw [cofibration_iff, weakEquivalence_iff]
  rfl

end TrivCof

section

variable [CategoryWithCofibrations C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithFibrations Cᵒᵖ where
  fibrations := (cofibrations C).op
/-
**HomotopicalAlgebra.fibrations_op** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra
`。
形式化陈述：fibrations_op : fibrations Cᵒᵖ = (cofibrations C).op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fibrations_op : fibrations Cᵒᵖ = (cofibrations C).op := rfl
/-
**HomotopicalAlgebra.cofibrations_eq_unop** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra`。
形式化陈述：cofibrations_eq_unop : cofibrations C = (fibrations Cᵒᵖ).unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cofibrations_eq_unop : cofibrations C = (fibrations Cᵒᵖ).unop := rfl

variable {C}
/-
**HomotopicalAlgebra.fibration_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：fibration_op_iff : Fibration f.op ↔ Cofibration f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fibration_op_iff : Fibration f.op ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]
/-
**HomotopicalAlgebra.cofibration_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra`。
形式化陈述：cofibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : Cofibration f.unop ↔ Fibrat
ion f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cofibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Cofibration f.unop ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Cofibration f] : Fibration f.op := by
  rwa [fibration_op_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Fibration f] : Cofibration f.unop := by
  rwa [cofibration_unop_iff]

end

section

variable [CategoryWithFibrations C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithCofibrations Cᵒᵖ where
  cofibrations := (fibrations C).op
/-
**HomotopicalAlgebra.cofibrations_op** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgeb
ra`。
形式化陈述：cofibrations_op : cofibrations Cᵒᵖ = (fibrations C).op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cofibrations_op : cofibrations Cᵒᵖ = (fibrations C).op := rfl
/-
**HomotopicalAlgebra.fibrations_eq_unop** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAl
gebra`。
形式化陈述：fibrations_eq_unop : fibrations C = (cofibrations Cᵒᵖ).unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fibrations_eq_unop : fibrations C = (cofibrations Cᵒᵖ).unop := rfl

variable {C}
/-
**HomotopicalAlgebra.cofibration_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAl
gebra`。
形式化陈述：cofibration_op_iff : Cofibration f.op ↔ Fibration f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cofibration_op_iff : Cofibration f.op ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]
/-
**HomotopicalAlgebra.fibration_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAl
gebra`。
形式化陈述：fibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : Fibration f.unop ↔ Cofibratio
n f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Fibration f.unop ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fibration f] : Cofibration f.op := by
  rwa [cofibration_op_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Cofibration f] : Fibration f.unop := by
  rwa [fibration_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithWeakEquivalences Cᵒᵖ where
  weakEquivalences := (weakEquivalences C).op
/-
**HomotopicalAlgebra.weakEquivalences_op** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra`。
形式化陈述：weakEquivalences_op : weakEquivalences Cᵒᵖ = (weakEquivalences C).op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weakEquivalences_op : weakEquivalences Cᵒᵖ = (weakEquivalences C).op := rfl
/-
**HomotopicalAlgebra.weakEquivalences_eq_unop** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra`。
形式化陈述：weakEquivalences_eq_unop : weakEquivalences C = (weakEquivalences Cᵒᵖ).uno
p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weakEquivalences_eq_unop : weakEquivalences C = (weakEquivalences Cᵒᵖ).unop := rfl

variable {C}
/-
**HomotopicalAlgebra.weakEquivalences_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra`。
形式化陈述：weakEquivalences_op_iff : WeakEquivalence f.op ↔ WeakEquivalence f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma weakEquivalences_op_iff : WeakEquivalence f.op ↔ WeakEquivalence f := by
  simp [weakEquivalence_iff, weakEquivalences_op]
/-
**HomotopicalAlgebra.weakEquivalences_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：weakEquivalences_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : WeakEquivalence f.unop
 ↔ WeakEquivalence f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `HomotopicalAlgebra.weakEquivalences_op_iff`：weakEquivalences_op_iff : We
akEquivalence f.op ↔ WeakEquivalence f
-/
lemma weakEquivalences_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    WeakEquivalence f.unop ↔ WeakEquivalence f :=
  (weakEquivalences_op_iff f.unop).symm
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WeakEquivalence f] : WeakEquivalence f.op := by
  rwa [weakEquivalences_op_iff]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.unop := by
  rwa [weakEquivalences_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]

/-
**HomotopicalAlgebra.trivialFibrations_op** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra`。
形式化陈述：trivialFibrations_op : trivialFibrations Cᵒᵖ = (trivialCofibrations C).op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialFibrations_op : trivialFibrations Cᵒᵖ = (trivialCofibrations C).op := rfl
/-
**HomotopicalAlgebra.trivialCofibrations_eq_unop** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：trivialCofibrations_eq_unop : trivialCofibrations C = (trivialFibrations C
ᵒᵖ).unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialCofibrations_eq_unop : trivialCofibrations C = (trivialFibrations Cᵒᵖ).unop := rfl

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]

/-
**HomotopicalAlgebra.trivialCofibrations_op** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra`。
形式化陈述：trivialCofibrations_op : trivialCofibrations Cᵒᵖ = (trivialFibrations C).o
p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialCofibrations_op : trivialCofibrations Cᵒᵖ = (trivialFibrations C).op := rfl
/-
**HomotopicalAlgebra.trivialFibrations_eq_unop** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra`。
形式化陈述：trivialFibrations_eq_unop : trivialFibrations C = (trivialCofibrations Cᵒᵖ
).unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivialFibrations_eq_unop : trivialFibrations C = (trivialCofibrations Cᵒᵖ).unop := rfl

end

section ObjectProperty

variable [CategoryWithWeakEquivalences C] {P : ObjectProperty C}

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithWeakEquivalences P.FullSubcategory where
  weakEquivalences := (weakEquivalences C).inverseImage P.ι
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences P.FullSubcategory).HasTwoOutOfThreeProperty :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).HasTwoOutOfThreeProperty
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).IsMultiplicative] :
    (weakEquivalences P.FullSubcategory).IsMultiplicative :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).IsMultiplicative
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).RespectsIso] :
    (weakEquivalences P.FullSubcategory).RespectsIso :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).RespectsIso
/-
**HomotopicalAlgebra.weakEquivalence_iff_of_objectProperty** 是 Mathlib 中的一个引理，位于
命名空间 `HomotopicalAlgebra`。
形式化陈述：weakEquivalence_iff_of_objectProperty {X Y : P.FullSubcategory} (f : X ⟶ Y
) : WeakEquivalence f ↔ WeakEquivalence f.hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma weakEquivalence_iff_of_objectProperty
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.hom := by
  simp only [weakEquivalence_iff]
  rfl
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence f.hom := by
  rwa [← weakEquivalence_iff_of_objectProperty]
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (P.ι.map f) := by
  dsimp
  infer_instance

end ObjectProperty

end HomotopicalAlgebra

