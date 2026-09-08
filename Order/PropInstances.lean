/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Disjoint

/-!

# The order on `Prop`

Instances on `Prop` such as `DistribLattice`, `BoundedOrder`, `LinearOrder`.

-/

public section

/-- Propositions form a distributive lattice. -/
/-
**Prop.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instDistribLattice : DistribLattice Prop where sup
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Propositions form a distributive lattice.
-/
instance Prop.instDistribLattice : DistribLattice Prop where
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

/-- Propositions form a bounded order. -/
/-
**Prop.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instBoundedOrder : BoundedOrder Prop where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Propositions form a bounded order.
-/
instance Prop.instBoundedOrder : BoundedOrder Prop where
  top := True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

@[simp]
/-
**Prop.bot_eq_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.bot_eq_false : (⊥ : Prop) = False
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl

@[simp]
/-
**Prop.top_eq_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.top_eq_true : (⊤ : Prop) = True
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl
/-
**Prop.le_total** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.le_total : @Std.Total Prop (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
instance Prop.le_total : @Std.Total Prop (· ≤ ·) :=
  ⟨fun p q => by by_cases h : q <;> simp [h]⟩
/-
**Prop.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.linearOrder : LinearOrder Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical
  exact Lattice.toLinearOrder Prop

@[simp]
/-
**sup_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_Prop_eq : (· ⊔ ·) = (· ∨ ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl

@[simp]
/-
**inf_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_Prop_eq : (· ⊓ ·) = (· ∧ ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl

namespace Pi

variable {ι α : Type*} {α' : ι → Type*} [∀ i, PartialOrder (α' i)]

/-
**Pi.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：disjoint_iff [forall i, OrderBot (α' i)] {f g : forall i, α' i} : Disjoint
 f g ↔ forall i, Disjoint (f i) (g i)
参数：α' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `update_le_iff`：∀ {ι : Type u_1} {π : ι → Type u_4} [inst : DecidableEq ι
] [inst_1 : (i : ι) → Preorder (π i)] {x y : (i : ι) → π i}   {i : ι} {a : π i},
 Fu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} :
    Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  classical
  constructor
  · intro h i x hf hg
    exact (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => bot_le⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => bot_le⟩)).1
  · intro h x hf hg i
    apply h i (hf i) (hg i)
/-
**Pi.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：codisjoint_iff [forall i, OrderTop (α' i)] {f g : forall i, α' i} : Codisj
oint f g ↔ forall i, Codisjoint (f i) (g i)
参数：α' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.disjoint_iff`：disjoint_iff [forall i, OrderBot (α' i)] {f g : forall 
i, α' i} : Disjoint f g ↔ forall i, Disjoint (f i) (g i)
-/
theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} :
    Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
/-
**Pi.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isCompl_iff [forall i, BoundedOrder (α' i)] {f g : forall i, α' i} : IsCom
pl f g ↔ forall i, IsCompl (f i) (g i)
参数：α' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCompl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} :
    IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) : Std.Symm (α := α) ⊤ where
  symm _ _ := id
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) : Std.Symm (α := α) ⊥ where
  symm _ _ := id

@[nontriviality]
/-
**Pi.eq_top_iff_refl_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：eq_top_iff_refl_of_subsingleton [Subsingleton α] {r : α -> α -> Prop} : r 
= ⊤ ↔ Std.Refl r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_top_iff_refl_of_subsingleton [Subsingleton α] {r : α → α → Prop} : r = ⊤ ↔ Std.Refl r :=
  ⟨fun h ↦ ⟨by simp [h]⟩, fun _ ↦ funext₂ <| by simp [rel_of_subsingleton]⟩

@[nontriviality]
/-
**Pi.eq_bot_iff_irrefl_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：eq_bot_iff_irrefl_of_subsingleton [Subsingleton α] {r : α -> α -> Prop} : 
r = ⊥ ↔ Std.Irrefl r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_bot_iff_irrefl_of_subsingleton [Subsingleton α] {r : α → α → Prop} :
    r = ⊥ ↔ Std.Irrefl r :=
  ⟨fun h ↦ ⟨by simp [h]⟩, fun _ ↦ funext₂ <| by simp [not_rel_of_subsingleton]⟩

end Pi

@[simp]
/-
**Prop.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
-/
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le

@[simp]
/-
**Prop.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `forall_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∀ (a : α), 
b) ↔ b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const True

@[simp]
/-
**Prop.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `Prop.disjoint_iff`：Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧
 Q)
· 使用定理 `Prop.codisjoint_iff`：Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔
 P ∨ Q
· 使用定理 `not_iff`：not_iff : ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
-/
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [_root_.isCompl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff]
  by_cases P <;> by_cases Q <;> simp [*]

section decidable_instances

universe u
variable {α : Type u}

/-
**Prop.decidablePredBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.decidablePredBot : DecidablePred (⊥ : α -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.decidablePredBot : DecidablePred (⊥ : α → Prop) := fun _ => instDecidableFalse
/-
**Prop.decidablePredTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.decidablePredTop : DecidablePred (⊤ : α -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.decidablePredTop : DecidablePred (⊤ : α → Prop) := fun _ => instDecidableTrue
/-
**Prop.decidableRelBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.decidableRelBot : DecidableRel (⊥ : α -> α -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.decidableRelBot : DecidableRel (⊥ : α → α → Prop) := fun _ _ => instDecidableFalse
/-
**Prop.decidableRelTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.decidableRelTop : DecidableRel (⊤ : α -> α -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.decidableRelTop : DecidableRel (⊤ : α → α → Prop) := fun _ _ => instDecidableTrue

end decidable_instances

