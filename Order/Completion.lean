/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Concept

import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o EReal`.

- Make the `to_dual` tactic work so that some lemmas are created automatically, eg
  `DedekindCut.le_principal_iff` from `DedekindCut.principal_le_iff`.
  See [https://github.com/leanprover-community/mathlib4/pull/37939#discussion_r3328958630]

## Tags

Dedekind completion, Dedekind cut
-/

@[expose] public section

open Concept Set

variable {α β : Type*}

variable (α) in
/-- The **Dedekind-MacNeille completion** of a partial order is the smallest complete lattice that
contains it. We define here the type of Dedekind cuts of `α` as the `Concept` lattice of the `≤`
relation of `α`.

For `A : DedekindCut α`, the sets `A.left` and `A.right` are related by
`upperBounds A.left = A.right` and `lowerBounds A.right = A.left`.

The theorem `DedekindCut.principalEmbedding_trans_factorEmbedding` proves that if `α` is a partial
order and `β` is a complete lattice, any embedding `α ↪o β` factors through `DedekindCut α`. -/
/-
**DedekindCut** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DedekindCut [Preorder α]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Dedekind-MacNeille completion** of a partial order is the smallest complet
e lattice that
contains it. We define here the type of Dedekind cuts of `α` as the `Concept` la
ttice of the `≤`
relation of `α`.

For `A : DedekindCut α`, the sets `A.left` and `A.right` are related by
`upperBounds A.left = A.right` and `lowerBounds A.right = A.left`.

The theorem `DedekindCut.principalEmbedding_trans_factorEmbedding` proves that i
f `α` is a partial
order and `β` is a complete lattice, any embedding `α ↪o β` factors through `Ded
ekindCut α`.
-/
abbrev DedekindCut [Preorder α] := Concept α α (· ≤ ·)

namespace DedekindCut

section Preorder
variable [Preorder α] [Preorder β]

/-- The left set of a Dedekind cut. This is an alias for `Concept.extent`. -/
/-
**DedekindCut.left** 是 Mathlib 中的一个缩写定义，位于命名空间 `DedekindCut`。
形式化陈述：left (A : DedekindCut α) : Set α
参数：A : DedekindCut α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left set of a Dedekind cut. This is an alias for `Concept.extent`.
-/
abbrev left (A : DedekindCut α) : Set α := A.extent

/-- The right set of a Dedekind cut. This is an alias for `Concept.intent`. -/
/-
**DedekindCut.right** 是 Mathlib 中的一个缩写定义，位于命名空间 `DedekindCut`。
形式化陈述：right (A : DedekindCut α) : Set α
参数：A : DedekindCut α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right set of a Dedekind cut. This is an alias for `Concept.intent`.
-/
abbrev right (A : DedekindCut α) : Set α := A.intent

/-- See `DedekindCut.ext'` for a version using the right set instead. -/
/-
**DedekindCut.ext** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {A B : DedekindCut α}, A.left = B.lef
t → A = B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext`：ext (h : c.extent = d.extent) : c = d

--- 原说明 ---
See `DedekindCut.ext'` for a version using the right set instead.
-/
@[ext] theorem ext {A B : DedekindCut α} (h : A.left = B.left) : A = B := Concept.ext h

/-- See `DedekindCut.ext` for a version using the left set instead. -/
/-
**DedekindCut.ext'** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B
参数：h : A.right = B.right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext'`：ext' (h : c.intent = d.intent) : c = d

--- 原说明 ---
See `DedekindCut.ext` for a version using the left set instead.
-/
theorem ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B := Concept.ext' h

@[simp]
/-
**DedekindCut.upperBounds_left** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：upperBounds_left (A : DedekindCut α) : upperBounds A.left = A.right
参数：A : DedekindCut α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
-/
theorem upperBounds_left (A : DedekindCut α) : upperBounds A.left = A.right :=
  A.upperPolar_extent

@[simp]
/-
**DedekindCut.lowerBounds_right** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：lowerBounds_right (A : DedekindCut α) : lowerBounds A.right = A.left
参数：A : DedekindCut α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
-/
theorem lowerBounds_right (A : DedekindCut α) : lowerBounds A.right = A.left :=
  A.lowerPolar_intent
/-
**DedekindCut.image_left_subset_lowerBounds** 是 Mathlib 中的一个定理，位于命名空间 `DedekindC
ut`。
形式化陈述：image_left_subset_lowerBounds {f : α -> β} (hf : Monotone f) (A : Dedekind
Cut α) : f '' A.left subseteq lowerBounds (f '' A.right)
参数：hf : Monotone f；A : DedekindCut α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.rel_extent_intent`：rel_extent_intent {x y} (hx : x in c.extent) 
(hy : y in c.intent) : r x y
-/
theorem image_left_subset_lowerBounds {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.left ⊆ lowerBounds (f '' A.right) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hx hy
/-
**DedekindCut.image_right_subset_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 `Dedekind
Cut`。
形式化陈述：image_right_subset_upperBounds {f : α -> β} (hf : Monotone f) (A : Dedekin
dCut α) : f '' A.right subseteq upperBounds (f '' A.left)
参数：hf : Monotone f；A : DedekindCut α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.rel_extent_intent`：rel_extent_intent {x y} (hx : x in c.extent) 
(hy : y in c.intent) : r x y
-/
theorem image_right_subset_upperBounds {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.right ⊆ upperBounds (f '' A.left) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_extent_intent hy hx

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-preserving,
though it is injective only on partial orders. -/
/-
**DedekindCut.principal** 是 Mathlib 中的一个定义，位于命名空间 `DedekindCut`。
形式化陈述：principal (a : α) : DedekindCut α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-p
reserving,
though it is injective only on partial orders.
-/
def principal (a : α) : DedekindCut α :=
  (Concept.ofObject _ a).copy (Iic a) (Ici a)
    (by ext; simpa [mem_lowerPolar_iff] using! forall_ge_iff_le.symm)
    (by ext; simp)
/-
**DedekindCut.left_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), (DedekindCut.principal a).le
ft = Set.Iic a
参数：a : α；DedekindCut.principal a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem left_principal (a : α) : (principal a).left = Iic a := rfl
/-
**DedekindCut.right_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), (DedekindCut.principal a).ri
ght = Set.Ici a
参数：a : α；DedekindCut.principal a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem right_principal (a : α) : (principal a).right = Ici a := rfl
/-
**DedekindCut.ofObject_eq_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), Concept.ofObject (fun x1 x2 
=> x1 ≤ x2) a = DedekindCut.principal a
参数：a : α；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.copy_eq`：copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he
 hi) : c.copy e i he hi = c
-/
@[simp] theorem ofObject_eq_principal (a : α) : ofObject (· ≤ ·) a = principal a :=
  (copy_eq ..).symm
/-
**DedekindCut.ofAttribute_eq_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), Concept.ofAttribute (fun x1 
x2 => x1 ≤ x2) a = DedekindCut.principal a
参数：a : α；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DedekindCut.ext`：∀ {α : Type u_1} [inst : Preorder α] {A B : DedekindCut
 α}, A.left = B.left → A = B
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Concept.extent_ofAttributes`：∀ {α : Type u_2} {β : Type u_3} (r : α → β 
→ Prop) (t : Set β), (Concept.ofAttributes r t).extent = lowerPolar r t
· 使用定理 `lowerBounds_singleton`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, low
erBounds {a} = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem ofAttribute_eq_principal (a : α) : ofAttribute (· ≤ ·) a = principal a := by
  ext; simp

@[simp]
/-
**DedekindCut.principal_le_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_le_principal {a b : α} : principal a <= principal b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DedekindCut.ofObject_eq_principal`：∀ {α : Type u_1} [inst : Preorder α] 
(a : α), Concept.ofObject (fun x1 x2 => x1 ≤ x2) a = DedekindCut.principal a
· 使用定理 `DedekindCut.ofAttribute_eq_principal`：∀ {α : Type u_1} [inst : Preorder 
α] (a : α), Concept.ofAttribute (fun x1 x2 => x1 ≤ x2) a = DedekindCut.principal
 a
· 使用定理 `Concept.ofObject_le_ofAttribute_iff`：ofObject_le_ofAttribute_iff {a b} :
 ofObject r a <= ofAttribute r b ↔ r a b
-/
theorem principal_le_principal {a b : α} : principal a ≤ principal b ↔ a ≤ b := by
  simpa using ofObject_le_ofAttribute_iff (r := (· ≤ ·)) (a := a)

@[simp]
/-
**DedekindCut.principal_lt_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_lt_principal {a b : α} : principal a < principal b ↔ a < b
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
theorem principal_lt_principal {a b : α} : principal a < principal b ↔ a < b := by
  simp [lt_iff_le_not_ge]
/-
**DedekindCut.principal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `DedekindCut`。
形式化陈述：principal_le_iff {a : α} {c : DedekindCut α} : principal a <= c ↔ a in c.l
eft
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Concept.mem_extent_of_rel_extent`：mem_extent_of_rel_extent [IsTrans α r'
] {x y} (hy : r' y x) (hx : x in c'.extent) : y in c'.extent
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
lemma principal_le_iff {a : α} {c : DedekindCut α} :
    principal a ≤ c ↔ a ∈ c.left := by
  simp only [← extent_subset_extent_iff, left_principal]
  exact ⟨fun h ↦ h self_mem_Iic, fun h y hy ↦ mem_extent_of_rel_extent hy h⟩
/-
**DedekindCut.le_principal_iff** 是 Mathlib 中的一个引理，位于命名空间 `DedekindCut`。
形式化陈述：le_principal_iff {a : α} {c : DedekindCut α} : c <= principal a ↔ a in c.r
ight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `Concept.mem_intent_of_intent_rel`：mem_intent_of_intent_rel [IsTrans α r'
] {x y} (hy : r' x y) (hx : x in c'.intent) : y in c'.intent
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
lemma le_principal_iff {a : α} {c : DedekindCut α} :
    c ≤ principal a ↔ a ∈ c.right := by
  simp only [← intent_subset_intent_iff, right_principal]
  exact ⟨fun h ↦ h self_mem_Ici, fun h _y hy ↦ mem_intent_of_intent_rel hy h⟩

/-- We can never have a computable decidable instance, for the same reason we can't on `Set α`. -/
/-
**DedekindCut.** 是 Mathlib 中的一个实例，位于命名空间 `DedekindCut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can never have a computable decidable instance, for the same reason we can't 
on `Set α`.
-/
noncomputable instance : DecidableLE (DedekindCut α) :=
  Classical.decRel _

end Preorder

section PartialOrder
variable [PartialOrder α]

@[simp]
/-
**DedekindCut.principal_inj** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_inj {a b : α} : principal a = principal b ↔ a = b
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
theorem principal_inj {a b : α} : principal a = principal b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.principal` as an `OrderEmbedding`. -/
@[simps! apply]
/-
**DedekindCut.principalEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `DedekindCut`。
形式化陈述：principalEmbedding : α ↪o DedekindCut α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DedekindCut.principal` as an `OrderEmbedding`.
-/
def principalEmbedding : α ↪o DedekindCut α where
  toFun := principal
  inj' _ _ := principal_inj.1
  map_rel_iff' := principal_le_principal
/-
**DedekindCut.coe_principalEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α], ⇑DedekindCut.principalEmbedding 
= DedekindCut.principal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_principalEmbedding : ⇑(@principalEmbedding α _) = principal := rfl

end PartialOrder

section CompleteLattice
variable [CompleteLattice α] [PartialOrder β]

@[simp]
/-
**DedekindCut.principal_sSup_left** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_sSup_left (A : DedekindCut α) : principal (sSup A.left) = A
参数：A : DedekindCut α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DedekindCut.ext'`：ext' {A B : DedekindCut α} (h : A.right = B.right) : A
 = B
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DedekindCut.right_principal`：∀ {α : Type u_1} [inst : Preorder α] (a : α
), (DedekindCut.principal a).right = Set.Ici a
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `sSup_le_iff`：sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DedekindCut.upperBounds_left`：upperBounds_left (A : DedekindCut α) : upp
erBounds A.left = A.right
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem principal_sSup_left (A : DedekindCut α) : principal (sSup A.left) = A := by
  apply ext'
  ext
  rw [right_principal, mem_Ici, sSup_le_iff, ← upperBounds_left, mem_upperBounds]

@[simp]
/-
**DedekindCut.principal_sInf_right** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_sInf_right (A : DedekindCut α) : principal (sInf A.right) = A
参数：A : DedekindCut α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DedekindCut.ext`：∀ {α : Type u_1} [inst : Preorder α] {A B : DedekindCut
 α}, A.left = B.left → A = B
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DedekindCut.left_principal`：∀ {α : Type u_1} [inst : Preorder α] (a : α)
, (DedekindCut.principal a).left = Set.Iic a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DedekindCut.lowerBounds_right`：lowerBounds_right (A : DedekindCut α) : l
owerBounds A.right = A.left
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem principal_sInf_right (A : DedekindCut α) : principal (sInf A.right) = A := by
  ext
  rw [left_principal, mem_Iic, le_sInf_iff, ← lowerBounds_right, mem_lowerBounds]

/-- Any order embedding `β ↪o α` into a complete lattice `α` factors through `DedekindCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.left)`. Although the construction
`factorEmbedding f A = sInf (f '' A.right)` would also work, these do **not** in general give equal
embeddings. -/
/-
**DedekindCut.factorEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `DedekindCut`。
形式化陈述：factorEmbedding (f : β ↪o α) : DedekindCut β ↪o α
参数：f : β ↪o α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any order embedding `β ↪o α` into a complete lattice `α` factors through `Dedeki
ndCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.left)`. Although
 the construction
`factorEmbedding f A = sInf (f '' A.right)` would also work, these do **not** in
 general give equal
embeddings.
-/
def factorEmbedding (f : β ↪o α) : DedekindCut β ↪o α :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.left)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx
/-
**DedekindCut.factorEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：factorEmbedding_apply (f : β ↪o α) (A : DedekindCut β) : factorEmbedding f
 A = sSup (f '' A.left)
参数：f : β ↪o α；A : DedekindCut β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorEmbedding_apply (f : β ↪o α) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.left) :=
  rfl

@[simp]
/-
**DedekindCut.factorEmbedding_principal** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：factorEmbedding_principal (f : β ↪o α) (x : β) : factorEmbedding f (princi
pal x) = f x
参数：f : β ↪o α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DedekindCut.factorEmbedding_apply`：factorEmbedding_apply (f : β ↪o α) (A
 : DedekindCut β) : factorEmbedding f A = sSup (f '' A.left)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `le_sSup_iff`：le_sSup_iff : a <= sSup s ↔ forall b in upperBounds s, a <=
 b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RelEmbedding.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α →
 α → Prop} {s : β → β → Prop}, EmbeddingLike (r ↪r s) α β
-/
theorem factorEmbedding_principal (f : β ↪o α) (x : β) : factorEmbedding f (principal x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy ↦ hy ?_
  simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
/-
**DedekindCut.principalEmbedding_trans_factorEmbedding** 是 Mathlib 中的一个定理，位于命名空间
 `DedekindCut`。
形式化陈述：principalEmbedding_trans_factorEmbedding (f : β ↪o α) : principalEmbedding
.trans (factorEmbedding f) = f
参数：f : β ↪o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DedekindCut.factorEmbedding_principal`：factorEmbedding_principal (f : β 
↪o α) (x : β) : factorEmbedding f (principal x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Dedekind-MacNeille completion of a partial order is the smallest complete la
ttice containing
it, in the sense that any embedding into any complete lattice factors through it
.
-/
theorem principalEmbedding_trans_factorEmbedding (f : β ↪o α) :
    principalEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- `DedekindCut.principal` as an `OrderIso`.

This provides the second half of the **fundamental theorem of concept lattices**: every complete
lattice is isomorphic to a concept lattice (its own Dedekind completion).

See `Concept.instCompleteLattice` for the first half. -/
@[simps! apply]
/-
**DedekindCut.principalIso** 是 Mathlib 中的一个定义，位于命名空间 `DedekindCut`。
形式化陈述：principalIso : α ≃o DedekindCut α where invFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DedekindCut.principal` as an `OrderIso`.

This provides the second half of the **fundamental theorem of concept lattices**
: every complete
lattice is isomorphic to a concept lattice (its own Dedekind completion).

See `Concept.instCompleteLattice` for the first half.
-/
def principalIso : α ≃o DedekindCut α where
  invFun := factorEmbedding (OrderIso.refl α)
  left_inv x := factorEmbedding_principal _ x
  right_inv x := by simp [factorEmbedding]
  __ := principalEmbedding

set_option backward.isDefEq.respectTransparency false in
/-
**DedekindCut.principalIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principalIso_symm_apply (A : DedekindCut α) : principalIso.symm A = sSup A
.left
参数：A : DedekindCut α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DedekindCut.factorEmbedding_apply`：factorEmbedding_apply (f : β ↪o α) (A
 : DedekindCut β) : factorEmbedding f A = sSup (f '' A.left)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem principalIso_symm_apply (A : DedekindCut α) : principalIso.symm A = sSup A.left :=
  (factorEmbedding_apply ..).trans <| by simp

end CompleteLattice

section LinearOrder
variable [LinearOrder α]

/-
**DedekindCut.** 是 Mathlib 中的一个实例，位于命名空间 `DedekindCut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Total (DedekindCut α) (· ≤ ·) where
  total x y := le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩
/-
**DedekindCut.** 是 Mathlib 中的一个实例，位于命名空间 `DedekindCut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LinearOrder (DedekindCut α) where
  min_def x y := congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

/-- Use `DedekindCut.lt_iff_exists'` for a version with `<` and `≤` swapped -/
/-
**DedekindCut.lt_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：lt_iff_exists {a b : DedekindCut α} : a < b ↔ exists c, a < principal c ∧ 
principal c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.extent_ssubset_extent_iff`：extent_ssubset_extent_iff : c.extent 
⊂ d.extent ↔ c < d
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c

--- 原说明 ---
Use `DedekindCut.lt_iff_exists'` for a version with `<` and `≤` swapped
-/
theorem lt_iff_exists {a b : DedekindCut α} :
    a < b ↔ ∃ c, a < principal c ∧ principal c ≤ b := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hca, hcb⟩ ↦ hca.trans_le hcb⟩
  rw [← extent_ssubset_extent_iff, Set.ssubset_iff_exists] at h
  simpa [← not_le, principal_le_iff, and_comm] using h.2

/-- Variant of `DedekindCut.lt_iff_exists` with `<` and `≤` swapped -/
/-
**DedekindCut.lt_iff_exists'** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：lt_iff_exists' {a b : DedekindCut α} : a < b ↔ exists c, a <= principal c 
∧ principal c < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.intent_ssubset_intent_iff`：intent_ssubset_intent_iff : c.intent 
⊂ d.intent ↔ d < c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c

--- 原说明 ---
Variant of `DedekindCut.lt_iff_exists` with `<` and `≤` swapped
-/
theorem lt_iff_exists' {a b : DedekindCut α} :
    a < b ↔ ∃ c, a ≤ principal c ∧ principal c < b := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hca, hcb⟩ ↦ lt_of_le_of_lt hca hcb⟩
  rw [← intent_ssubset_intent_iff, Set.ssubset_iff_exists] at h
  simpa [← not_le, le_principal_iff] using h.2
/-
**DedekindCut.** 是 Mathlib 中的一个实例，位于命名空间 `DedekindCut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder (DedekindCut α) where
  __ := (inferInstance : LinearOrder _)
  __ := (inferInstance : CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _
/-
**DedekindCut.** 是 Mathlib 中的一个实例，位于命名空间 `DedekindCut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DenselyOrdered α] : DenselyOrdered (DedekindCut α) where
  dense a b h := by
    obtain ⟨c, hac, hcb⟩ := lt_iff_exists.mp h
    obtain ⟨d, had, hdc⟩ := lt_iff_exists'.mp hac
    simp only [principal_lt_principal] at hdc
    obtain ⟨u, _, _⟩ := DenselyOrdered.dense d c hdc
    exact ⟨principal u, had.trans_lt (by simpa), hcb.trans_lt' (by simpa)⟩
/-
**DedekindCut.principal_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：principal_lt_iff {a : α} {c : DedekindCut α} : principal a < c ↔ exists b 
in c.left, a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `DedekindCut.le_principal_iff`：le_principal_iff {a : α} {c : DedekindCut 
α} : c <= principal a ↔ a in c.right
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem principal_lt_iff {a : α} {c : DedekindCut α} :
    principal a < c ↔ ∃ b ∈ c.left, a < b := by
  rw [← not_le, le_principal_iff]
  rw [not_iff_comm, not_exists, ← le_principal_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl
/-
**DedekindCut.lt_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 `DedekindCut`。
形式化陈述：lt_principal_iff {a : α} {c : DedekindCut α} : c < principal a ↔ exists b 
in c.right, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `DedekindCut.principal_le_iff`：principal_le_iff {a : α} {c : DedekindCut 
α} : principal a <= c ↔ a in c.left
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Concept.intent_subset_intent_iff`：intent_subset_intent_iff : c.intent su
bseteq d.intent ↔ d <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_principal_iff {a : α} {c : DedekindCut α} :
    c < principal a ↔ ∃ b ∈ c.right, b < a := by
  rw [← not_le, principal_le_iff]
  rw [not_iff_comm, not_exists, ← principal_le_iff]
  rw [← intent_subset_intent_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

end LinearOrder
end DedekindCut

