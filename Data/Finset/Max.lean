/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Maximum and minimum of finite sets
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### max and min of finite sets -/

section MaxMin

variable [LinearOrder α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `WithBot α`. If you want to get an element of `α`, see
`s.max'`. -/
/-
**Finset.max** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [LinearOrder α] → Finset α → WithBot α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s`
 is not empty,
and `⊥` otherwise. It belongs to `WithBot α`. If you want to get an element of `
α`, see
`s.max'`.
-/
protected def max (s : Finset α) : WithBot α :=
  sup s (↑)
/-
**Finset.max_eq_sup_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑) :=
  rfl
/-
**Finset.max_eq_sup_withBot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑)
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑) :=
  rfl

@[simp]
/-
**Finset.max_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_empty : (∅ : Finset α).max = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl

@[simp, grind =]
/-
**Finset.max_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_insert_idem`：fold_insert_idem [DecidableEq α] [hi : Std.Idem
potentOp op] : (insert a s).fold op b f = f a * s.fold op b f
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
-/
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max :=
  fold_insert_idem

@[simp]
/-
**Finset.max_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_singleton {a : α} : Finset.max {a} = (a : WithBot α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.max_insert`：max_insert {a : α} {s : Finset α} : (insert a s).max 
= max ↑a s.max
-/
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_empty_eq]
  exact max_insert
/-
**Finset.max_pair** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：max_pair (a b : α) : Finset.max {a, b} = max (↑a) (↑b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.max_insert`：max_insert {a : α} {s : Finset α} : (insert a s).max 
= max ↑a s.max
· 使用定理 `Finset.max_singleton`：max_singleton {a : α} : Finset.max {a} = (a : With
Bot α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma max_pair (a b : α) :
    Finset.max {a, b} = max (↑a) (↑b) := by
  simp
/-
**Finset.max_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_of_mem {s : Finset α} {a : α} (h : a in s) : exists b : α, s.max = b
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.le_iff_forall`：le_iff_forall : x <= y ↔ forall a : α, x = ↑a -> 
exists b : α, y = ↑b ∧ a <= b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b :=
  let ⟨b, h, _⟩ := WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) _ rfl; ⟨b, h⟩
/-
**Finset.max_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_of_nonempty {s : Finset α} (h : s.Nonempty) : exists a : α, s.max = a
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.max_of_mem`：max_of_mem {s : Finset α} {a : α} (h : a in s) : exis
ts b : α, s.max = b
-/
theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨_, h⟩ := h
  max_of_mem h
/-
**Finset.max_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.max_of_nonempty`：max_of_nonempty {s : Finset α} (h : s.Nonempty) 
: exists a : α, s.max = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Finset.max_empty`：max_empty : (∅ : Finset α).max = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h ↦ s.eq_empty_or_nonempty.elim id fun H ↦ by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h ↦ h.symm ▸ max_empty⟩
/-
**Finset.mem_of_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_max {s : Finset α} : forall {a : α}, s.max = a -> a in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s := by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | _ => grind [WithBot.coe_eq_coe]
/-
**Finset.le_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_max {a : α} {s : Finset α} (as : a in s) : ↑a <= s.max
参数：as : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_max {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as
/-
**Finset.notMem_of_max_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s
参数：h : s.max < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.le_max`：le_max {a : α} {s : Finset α} (as : a in s) : ↑a <= s.max
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem notMem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_ge
/-
**Finset.le_max_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_max_of_eq {s : Finset α} {a b : α} (h₁ : a in s) (h₂ : s.max = b) : a <
= b
参数：h₁ : a in s；h₂ : s.max = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_max`：le_max {a : α} {s : Finset α} (as : a in s) : ↑a <= s.max
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (le_max h₁).trans h₂.le
/-
**Finset.notMem_of_max_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) :
 a ∉ s
参数：h₁ : b < a；h₂ : s.max = ↑b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_of_max_lt_coe`：notMem_of_max_lt_coe {a : α} {s : Finset α}
 (h : s.max < a) : a ∉ s
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem notMem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
  Finset.notMem_of_max_lt_coe <| h₂.trans_lt <| WithBot.coe_lt_coe.mpr h₁
/-
**Finset.max_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_union {s t : Finset α} : (s union t).max = s.max ⊔ t.max
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
-/
theorem max_union {s t : Finset α} : (s ∪ t).max = s.max ⊔ t.max := sup_union

@[gcongr]
/-
**Finset.max_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_mono {s t : Finset α} (st : s subseteq t) : s.max <= t.max
参数：st : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
-/
theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st
/-
**Finset.max_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {M : WithBot α} {s : Finset α}, (∀
 a ∈ s, ↑a ≤ M) → s.max ≤ M
参数：∀ a ∈ s, ↑a ≤ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
-/
protected theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a ∈ s, (a : WithBot α) ≤ M) :
    s.max ≤ M :=
  Finset.sup_le st

@[simp]
/-
**Finset.max_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {m : WithBot α} {s : Finset α}, s.
max ≤ m ↔ ∀ a ∈ s, ↑a ≤ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
-/
protected lemma max_le_iff {m : WithBot α} {s : Finset α} : s.max ≤ m ↔ ∀ a ∈ s, a ≤ m :=
  Finset.sup_le_iff

@[simp]
/-
**Finset.max_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] [inst_1 : OrderTop α] {s : Finset 
α}, s.max = ⊤ ↔ ⊤ ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.sup_eq_top_iff`：∀ {ι : Type u_5} {α : Type u_7} [inst : LinearOrd
er α] [inst_1 : BoundedOrder α] [Nontrivial α] {s : Finset ι}   {f : ι → α}, s.s
up f = ⊤ ↔ …
· 使用定理 `top_nonempty`：∀ (α : Type u_1) [Top α], Nonempty α
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
protected lemma max_eq_top [OrderTop α] {s : Finset α} : s.max = ⊤ ↔ ⊤ ∈ s :=
  Finset.sup_eq_top_iff.trans <| by simp

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `WithTop α`. If you want to get an element of `α`, see
`s.min'`. -/
/-
**Finset.min** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [LinearOrder α] → Finset α → WithTop α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s`
 is not empty,
and `⊤` otherwise. It belongs to `WithTop α`. If you want to get an element of `
α`, see
`s.min'`.
-/
protected def min (s : Finset α) : WithTop α :=
  inf s (↑)
/-
**Finset.min_eq_inf_withTop** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_eq_inf_withTop (s : Finset α) : s.min = inf s (↑)
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_eq_inf_withTop (s : Finset α) : s.min = inf s (↑) :=
  rfl

@[simp]
/-
**Finset.min_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_empty : (∅ : Finset α).min = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl

@[simp]
/-
**Finset.min_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_insert_idem`：fold_insert_idem [DecidableEq α] [hi : Std.Idem
potentOp op] : (insert a s).fold op b f = f a * s.fold op b f
· 使用定理 `instCommutativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve min
· 使用定理 `instAssociativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve min
· 使用定理 `min_idem`：∀ {α : Type u} [inst : LinearOrder α], Std.IdempotentOp min
-/
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem

@[simp]
/-
**Finset.min_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_singleton {a : α} : Finset.min {a} = (a : WithTop α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.min_insert`：min_insert {a : α} {s : Finset α} : (insert a s).min 
= min (↑a) s.min
-/
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) := by
  rw [← insert_empty_eq]
  exact min_insert
/-
**Finset.min_pair** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：min_pair (a b : α) : Finset.min {a, b} = min (↑a) (↑b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.min_insert`：min_insert {a : α} {s : Finset α} : (insert a s).min 
= min (↑a) s.min
· 使用定理 `Finset.min_singleton`：min_singleton {a : α} : Finset.min {a} = (a : With
Top α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma min_pair (a b : α) :
    Finset.min {a, b} = min (↑a) (↑b) := by
  simp
/-
**Finset.min_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_of_mem {s : Finset α} {a : α} (h : a in s) : exists b : α, s.min = b
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.le_iff_forall`：∀ {α : Type u_1} [inst : LE α] {x y : WithTop α},
 y ≤ x ↔ ∀ (a : α), x = ↑a → ∃ b, y = ↑b ∧ b ≤ a
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
-/
theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b :=
  let ⟨b, h, _⟩ := WithTop.le_iff_forall.1 (inf_le (α := WithTop α) h) _ rfl; ⟨b, h⟩
/-
**Finset.min_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_of_nonempty {s : Finset α} (h : s.Nonempty) : exists a : α, s.min = a
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min_of_mem`：min_of_mem {s : Finset α} {a : α} (h : a in s) : exis
ts b : α, s.min = b
-/
theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨_, h⟩ := h
  min_of_mem h

@[simp]
/-
**Finset.min_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ := by
  simp [Finset.min, eq_empty_iff_forall_notMem]
/-
**Finset.mem_of_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_min {s : Finset α} : forall {a : α}, s.min = a -> a in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
-/
theorem mem_of_min {s : Finset α} : ∀ {a : α}, s.min = a → a ∈ s :=
  @mem_of_max αᵒᵈ _ s
/-
**Finset.min_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
参数：as : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
-/
theorem min_le {a : α} {s : Finset α} (as : a ∈ s) : s.min ≤ a :=
  inf_le as
/-
**Finset.notMem_of_coe_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s
参数：h : ↑a < s.min。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem notMem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s :=
  mt min_le h.not_ge
/-
**Finset.min_le_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_le_of_eq {s : Finset α} {a b : α} (h₁ : b in s) (h₂ : s.min = a) : a <
= b
参数：h₁ : b in s；h₂ : s.min = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
-/
theorem min_le_of_eq {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : s.min = a) : a ≤ b :=
  WithTop.coe_le_coe.mp <| h₂.ge.trans (min_le h₁)
/-
**Finset.notMem_of_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) :
 a ∉ s
参数：h₁ : a < b；h₂ : s.min = ↑b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_of_coe_lt_min`：notMem_of_coe_lt_min {a : α} {s : Finset α}
 (h : ↑a < s.min) : a ∉ s
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem notMem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) : a ∉ s :=
  Finset.notMem_of_coe_lt_min <| (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm
/-
**Finset.min_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_union {s t : Finset α} : (s union t).min = s.min ⊓ t.min
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {s₁ s₂ : Finset β} {f : β → α}   [inst_2 : DecidableEq
 β], (…
-/
theorem min_union {s t : Finset α} : (s ∪ t).min = s.min ⊓ t.min := inf_union

@[gcongr]
/-
**Finset.min_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_mono {s t : Finset α} (st : s subseteq t) : t.min <= s.min
参数：st : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] [inst_1 : OrderTop α] {s₁ s₂ : Finset β} {f : β → α},   s₁ ⊆ s₂ → s₂.inf f ≤ 
s₁.in…
-/
theorem min_mono {s t : Finset α} (st : s ⊆ t) : t.min ≤ s.min :=
  inf_mono st
/-
**Finset.le_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {m : WithTop α} {s : Finset α}, (∀
 a ∈ s, m ≤ ↑a) → m ≤ s.min
参数：∀ a ∈ s, m ≤ ↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, a ≤ f b) 
→ a…
-/
protected theorem le_min {m : WithTop α} {s : Finset α} (st : ∀ a : α, a ∈ s → m ≤ a) : m ≤ s.min :=
  Finset.le_inf st

@[simp]
/-
**Finset.le_min_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {m : WithTop α} {s : Finset α}, m 
≤ s.min ↔ ∀ a ∈ s, m ≤ ↑a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_inf_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   a ≤ s.inf f ↔ ∀
 b ∈ s,…
-/
protected theorem le_min_iff {m : WithTop α} {s : Finset α} : m ≤ s.min ↔ ∀ a ∈ s, m ≤ a :=
  Finset.le_inf_iff

@[simp]
/-
**Finset.min_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] [inst_1 : OrderBot α] {s : Finset 
α}, s.min = ⊥ ↔ ⊥ ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.max_eq_top`：∀ {α : Type u_2} [inst : LinearOrder α] [inst_1 : Ord
erTop α] {s : Finset α}, s.max = ⊤ ↔ ⊤ ∈ s
-/
protected theorem min_eq_bot [OrderBot α] {s : Finset α} : s.min = ⊥ ↔ ⊥ ∈ s :=
  Finset.max_eq_top (α := αᵒᵈ)

/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `WithTop α`. -/
/-
**Finset.min'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1

--- 原说明 ---
Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimu
m, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, u
se instead `s.min`,
taking values in `WithTop α`.
-/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id

/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
/-
**Finset.max'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1

--- 原说明 ---
Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximu
m, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, u
se instead `s.max`,
taking values in `WithBot α`.
-/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id

variable (s : Finset α) (H : s.Nonempty) {x : α}
/-
**Finset.min'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty), s
.min' H ∈ s
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_min`：mem_of_min {s : Finset α} : forall {a : α}, s.min = a
 -> a in s
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.coe_inf'`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] {s : Finset β} (H : s.Nonempty) (f : β → α),   ↑(s.inf' H f) = s.inf (WithTop
.some…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by simp only [Finset.min, min', id_eq, coe_inf', Function.comp_def]
/-
**Finset.min'_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (x : α) (H2 : x ∈ s
), s.min' ⋯ ≤ x
参数：s : Finset α；x : α；H2 : x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min_le_of_eq`：min_le_of_eq {s : Finset α} {a b : α} (h₁ : b in s)
 (h₂ : s.min = a) : a <= b
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
-/
theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm
/-
**Finset.le_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_min' (x) (H2 : forall y in s, x <= y) : x <= s.min' H
参数：x；H2 : forall y in s, x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
-/
theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _
/-
**Finset.isLeast_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isLeast_min' : IsLeast (↑s) (s.min' H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
-/
theorem isLeast_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩

@[simp]
/-
**Finset.le_min'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) {x
 : α}, x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b ≤ a ↔ b ∈ lowerBounds s)
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `Finset.isLeast_min'`：isLeast_min' : IsLeast (↑s) (s.min' H)
-/
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
  le_isGLB_iff (isLeast_min' s H).isGLB

/-- `{a}.min' _` is `a`. -/
@[simp]
/-
**Finset.min'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), {a}.min' ⋯ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`{a}.min' _` is `a`.
-/
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']
/-
**Finset.max'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty), s
.max' H ∈ s
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]
/-
**Finset.le_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
参数：x；H2 : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_max_of_eq`：le_max_of_eq {s : Finset α} {a b : α} (h₁ : a in s)
 (h₂ : s.max = b) : a <= b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
-/
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
/-
**Finset.max'_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) (x
 : α), (∀ y ∈ s, y ≤ x) → s.max' H ≤ x
参数：s : Finset α；H : s.Nonempty；x : α；∀ y ∈ s, y ≤ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _
/-
**Finset.isGreatest_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isGreatest_max' : IsGreatest (↑s) (s.max' H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
-/
theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[simp]
/-
**Finset.max'_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) {x
 : α}, s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `Finset.isGreatest_max'`：isGreatest_max' : IsGreatest (↑s) (s.max' H)
-/
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB

@[simp]
/-
**Finset.max'_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) {x
 : α}, s.max' H < x ↔ ∀ y ∈ s, y < x
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩

@[simp]
/-
**Finset.lt_min'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) {x
 : α}, x < s.min' H ↔ ∀ y ∈ s, x < y
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.max'_lt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, s.max' H < x ↔ ∀ y ∈ s, y < x
-/
theorem lt_min'_iff : x < s.min' H ↔ ∀ y ∈ s, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _
/-
**Finset.max'_eq_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty), s
.max' H = s.sup' H id
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
-/
theorem max'_eq_sup' : s.max' H = s.sup' H id := rfl
/-
**Finset.min'_eq_inf'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty), s
.min' H = s.inf' H id
参数：s : Finset α；H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
-/
theorem min'_eq_inf' : s.min' H = s.inf' H id := rfl

/-- `{a}.max' _` is `a`. -/
@[simp]
/-
**Finset.max'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), {a}.max' ⋯ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`{a}.max' _` is `a`.
-/
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']
/-
**Finset.min'_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) (a
 : α), s.min' H = a ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b
参数：s : Finset α；H : s.Nonempty；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.le_min'`：le_min' (x) (H2 : forall y in s, x <= y) : x <= s.min' H
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma min'_eq_iff (a : α) : s.min' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → a ≤ b :=
  ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩), fun h ↦ le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩
/-
**Finset.max'_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) (a
 : α), s.max' H = a ↔ a ∈ s ∧ ∀ b ∈ s, b ≤ a
参数：s : Finset α；H : s.Nonempty；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.max'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
H : s.Nonempty) (x : α), (∀ y ∈ s, y ≤ x) → s.max' H ≤ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma max'_eq_iff (a : α) : s.max' H = a ↔ a ∈ s ∧ ∀ (b : α), b ∈ s → b ≤ a :=
  ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩), fun h ↦ le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩
/-
**Finset.min'_le_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (hs : s.Nonempty), 
s.min' hs ≤ s.max' hs
参数：s : Finset α；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem min'_le_max' (hs : s.Nonempty) : s.min' hs ≤ s.max' hs := min'_le _ _ (max'_mem _ _)
/-
**Finset.min'_lt_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) {i j : α} (H1 : i ∈
 s), j ∈ s → i ≠ j → s.min' ⋯ < s.max' ⋯
参数：s : Finset α；H1 : i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_lt_isLUB_of_ne`：isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB 
s b) {x y} (Hx : x in s) (Hy : y in s) (Hxy : x != y) : a < b
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `Finset.isLeast_min'`：isLeast_min' : IsLeast (↑s) (s.min' H)
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `Finset.isGreatest_max'`：isGreatest_max' : IsGreatest (↑s) (s.max' H)
-/
theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3

/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
/-
**Finset.min'_lt_max'_of_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (h₂ : 1 < s.card), 
s.min' ⋯ < s.max' ⋯
参数：s : Finset α；h₂ : 1 < s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.one_lt_card`：one_lt_card : 1 < #s ↔ exists a in s, exists b in s,
 a != b
· 使用定理 `Finset.min'_lt_max'`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset
 α) {i j : α} (H1 : i ∈ s), j ∈ s → i ≠ j → s.min' ⋯ < s.max' ⋯

--- 原说明 ---
If there's more than 1 element, the min' is less than the max'. An alternate ver
sion of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.1 <| by lia) < s.max' (Finset.card_pos.1 <| by lia) := by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab
/-
**Finset.max'_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s₁ s₂ : Finset α} (h₁ : s₁.Nonemp
ty) (h₂ : s₂.Nonempty),   (s₁ ∪ s₂).max' ⋯ = max (s₁.max' h₁) (s₂.max' h₂)
参数：h₁ : s₁.Nonempty；h₂ : s₂.Nonempty；s₁ ∪ s₂；s₁.max' h₁；s₂.max' h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.N
onempty…
-/
theorem max'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ ∪ s₂).max' (h₁.mono subset_union_left) = s₁.max' h₁ ⊔ s₂.max' h₂ := sup'_union h₁ h₂ id
/-
**Finset.min'_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s₁ s₂ : Finset α} (h₁ : s₁.Nonemp
ty) (h₂ : s₂.Nonempty),   (s₁ ∪ s₂).min' ⋯ = min (s₁.min' h₁) (s₂.min' h₂)
参数：h₁ : s₁.Nonempty；h₂ : s₂.Nonempty；s₁ ∪ s₂；s₁.min' h₁；s₂.min' h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf'_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.N
onempty…
-/
theorem min'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ ∪ s₂).min' (h₁.mono subset_union_left) = s₁.min' h₁ ⊓ s₂.min' h₂ := inf'_union h₁ h₂ id
/-
**Finset.map_ofDual_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max
参数：s : Finset αᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.max_eq_sup_withBot`：max_eq_sup_withBot (s : Finset α) : s.max = s
up s (↑)
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
-/
theorem map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  exact congr_fun WithBot.map_id _
/-
**Finset.map_ofDual_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min
参数：s : Finset αᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.min_eq_inf_withTop`：min_eq_inf_withTop (s : Finset α) : s.min = i
nf s (↑)
· 使用定理 `Finset.inf_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst :
 SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : DecidableEq β]   (s : Finset 
γ) (f …
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithTop.map_id`：∀ {α : Type u_1}, WithTop.map id = id
-/
theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _
/-
**Finset.map_toDual_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.max_eq_sup_withBot`：max_eq_sup_withBot (s : Finset α) : s.max = s
up s (↑)
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
-/
theorem map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  exact congr_fun WithBot.map_id _
/-
**Finset.map_toDual_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.min_eq_inf_withTop`：min_eq_inf_withTop (s : Finset α) : s.min = i
nf s (↑)
· 使用定理 `Finset.inf_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst :
 SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : DecidableEq β]   (s : Finset 
γ) (f …
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithTop.map_id`：∀ {α : Type u_1}, WithTop.map id = id
-/
theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  exact congr_fun WithTop.map_id _
/-
**Finset.ofDual_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) : ofDual (min' s hs) = max'
 (s.image ofDual) (hs.image _)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']
/-
**Finset.ofDual_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) : ofDual (max' s hs) = min'
 (s.image ofDual) (hs.image _)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeInf α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']
/-
**Finset.toDual_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toDual_min' {s : Finset α} (hs : s.Nonempty) : toDual (min' s hs) = max' (
s.image toDual) (hs.image _)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']
/-
**Finset.toDual_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toDual_max' {s : Finset α} (hs : s.Nonempty) : toDual (max' s hs) = min' (
s.image toDual) (hs.image _)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeInf α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']
/-
**Finset.max'_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Finset α} (H : s.Nonempty) 
(hst : s ⊆ t), s.max' H ≤ t.max' ⋯
参数：H : s.Nonempty；hst : s ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))
/-
**Finset.min'_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Finset α} (H : s.Nonempty) 
(hst : s ⊆ t), t.min' ⋯ ≤ s.min' H
参数：H : s.Nonempty；hst : s ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
-/
theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))
/-
**Finset.max'_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a : α) (s : Finset α) (H : s.None
mpty), (insert a s).max' ⋯ = max a (s.max' H)
参数：a : α；s : Finset α；H : s.Nonempty；insert a s；s.max' H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.unique`：∀ {α : Type u_1} [inst : PartialOrder α] {s : Set α} 
{a b : α}, IsGreatest s a → IsGreatest s b → a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Finset.isGreatest_max'`：isGreatest_max' : IsGreatest (↑s) (s.max' H)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `IsGreatest.insert`：∀ {γ : Type u_3} [inst : LinearOrder γ] (a : γ) {b : 
γ} {s : Set γ}, IsGreatest s b → IsGreatest (insert a s) (max a b)
-/
@[simp] theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max a (s.max' H) :=
  (isGreatest_max' _ _).unique <| by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _
/-
**Finset.min'_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a : α) (s : Finset α) (H : s.None
mpty), (insert a s).min' ⋯ = min a (s.min' H)
参数：a : α；s : Finset α；H : s.Nonempty；insert a s；s.min' H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.unique`：IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a
 = b
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Finset.isLeast_min'`：isLeast_min' : IsLeast (↑s) (s.min' H)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `IsLeast.insert`：∀ {γ : Type u_3} [inst : LinearOrder γ] (a : γ) {b : γ} 
{s : Set γ}, IsLeast s b → IsLeast (insert a s) (min a b)
-/
@[simp] theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min a (s.min' H) :=
  (isLeast_min' _ _).unique <| by
    rw [coe_insert]
    exact (isLeast_min' _ _).insert _
/-
**Finset.min'_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a b : α), {a, b}.min' ⋯ = min a b
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.min'_insert`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α) (s :
 Finset α) (H : s.Nonempty), (insert a s).min' ⋯ = min a (s.min' H)
· 使用定理 `Finset.min'_singleton`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), 
{a}.min' ⋯ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma min'_pair (a b : α) :
    min' {a, b} (insert_nonempty _ _) = min a b := by
  simp
/-
**Finset.max'_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (a b : α), {a, b}.max' ⋯ = max a b
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.max'_insert`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α) (s :
 Finset α) (H : s.Nonempty), (insert a s).max' ⋯ = max a (s.max' H)
· 使用定理 `Finset.max'_singleton`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), 
{a}.max' ⋯ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma max'_pair (a b : α) :
    max' {a, b} (insert_nonempty _ _) = max a b := by
  simp
/-
**Finset.lt_max'_of_mem_erase_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) [i
nst_1 : DecidableEq α] {a : α},   a ∈ s.erase (s.max' H) → a < s.max' H
参数：s : Finset α；H : s.Nonempty；s.max' H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) :
    a < s.max' H :=
  lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| notMem_erase _ _
/-
**Finset.min'_lt_of_mem_erase_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty) [i
nst_1 : DecidableEq α] {a : α},   a ∈ s.erase (s.min' H) → s.min' H < a
参数：s : Finset α；H : s.Nonempty；s.min' H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.lt_max'_of_mem_erase_max'`：∀ {α : Type u_2} [inst : LinearOrder α
] (s : Finset α) (H : s.Nonempty) [inst_1 : DecidableEq α] {a : α},   a ∈ s.eras
e (s.max' H) → a < s.m…
-/
theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.min' H)) :
    s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

/-- To rewrite from right to left, use `Monotone.map_finset_max'`. -/
@[simp]
/-
**Finset.max'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LinearOrder α] [inst_1 : LinearOrd
er β] {f : α → β},   Monotone f → ∀ (s : Finset α) (h : (Finset.image f s).Nonem
pty), (Finset.image f s).max' h = f (s.max' ⋯)
参数：s : Finset α；h : (Finset.image f s).Nonempty；Finset.image f s；s.max' ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)

--- 原说明 ---
To rewrite from right to left, use `Monotone.map_finset_max'`.
-/
theorem max'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' h.of_image) := by
  simp only [max', sup'_image]
  exact .symm <| apply_sup'_eq_sup'_comp _ _ fun _ _ ↦ hf.map_max

/-- A version of `Finset.max'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/
/-
**Finset._root_.Monotone.map_finset_max'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Finset.max'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image.
-/
lemma _root_.Monotone.map_finset_max' [LinearOrder β] {f : α → β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.max' h) = (s.image f).max' (h.image f) :=
  .symm <| max'_image hf ..

/-- To rewrite from right to left, use `Monotone.map_finset_min'`. -/
@[simp]
/-
**Finset.min'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LinearOrder α] [inst_1 : LinearOrd
er β] {f : α → β},   Monotone f → ∀ (s : Finset α) (h : (Finset.image f s).Nonem
pty), (Finset.image f s).min' h = f (s.min' ⋯)
参数：s : Finset α；h : (Finset.image f s).Nonempty；Finset.image f s；s.min' ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeInf α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.apply_inf'_eq_inf'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…

--- 原说明 ---
To rewrite from right to left, use `Monotone.map_finset_min'`.
-/
theorem min'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' h.of_image) := by
  simp only [min', inf'_image]
  exact .symm <| apply_inf'_eq_inf'_comp _ _ fun _ _ ↦ hf.map_min

/-- A version of `Finset.min'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image. -/
/-
**Finset._root_.Monotone.map_finset_min'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Finset.min'_image` with LHS and RHS reversed.
Also, this version assumes that `s` is nonempty, not its image.
-/
lemma _root_.Monotone.map_finset_min' [LinearOrder β] {f : α → β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.min' h) = (s.image f).min' (h.image f) :=
  .symm <| min'_image hf ..
/-
**Finset.coe_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
-/
theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id
/-
**Finset.coe_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_inf'`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] {s : Finset β} (H : s.Nonempty) (f : β → α),   ↑(s.inf' H f) = s.inf (WithTop
.some…
-/
theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id
/-
**Finset.max_mem_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_mem_image_coe {s : Finset α} (hs : s.Nonempty) : s.max in (s.image (↑)
 : Finset (WithBot α))
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.coe_max'`：coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs
) = s.max
-/
theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image (↑) : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩
/-
**Finset.min_mem_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_mem_image_coe {s : Finset α} (hs : s.Nonempty) : s.min in (s.image (↑)
 : Finset (WithTop α))
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Finset.coe_min'`：coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs
) = s.min
-/
theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min ∈ (s.image (↑) : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩
/-
**Finset.max_mem_insert_bot_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_mem_insert_bot_image_coe (s : Finset α) : s.max in (insert ⊥ (s.image 
(↑)) : Finset (WithBot α))
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Finset.max_eq_bot`：max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅
· 使用定理 `Finset.max_mem_image_coe`：max_mem_image_coe {s : Finset α} (hs : s.Nonem
pty) : s.max in (s.image (↑) : Finset (WithBot α))
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
-/
theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image (↑)) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe
/-
**Finset.min_mem_insert_top_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_mem_insert_top_image_coe (s : Finset α) : s.min in (insert ⊤ (s.image 
(↑)) : Finset (WithTop α))
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Finset.min_eq_top`：min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅
· 使用定理 `Finset.min_mem_image_coe`：min_mem_image_coe {s : Finset α} (hs : s.Nonem
pty) : s.min in (s.image (↑) : Finset (WithTop α))
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
-/
theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min ∈ (insert ⊤ (s.image (↑)) : Finset (WithTop α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe
/-
**Finset.max'_erase_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {x : α} {s : Finset α} (s0 : (s.er
ase x).Nonempty), (s.erase x).max' s0 ≠ x
参数：s0 : (s.erase x).Nonempty；s.erase x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)
/-
**Finset.min'_erase_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {x : α} {s : Finset α} (s0 : (s.er
ase x).Nonempty), (s.erase x).min' s0 ≠ x
参数：s0 : (s.erase x).Nonempty；s.erase x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
-/
theorem min'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).min' s0 ≠ x :=
  ne_of_mem_erase (min'_mem _ s0)
/-
**Finset.max_erase_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：max_erase_ne_self {s : Finset α} : (s.erase x).max != x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_max'`：coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs
) = s.max
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `Finset.max'_erase_ne_self`：∀ {α : Type u_2} [inst : LinearOrder α] {x : 
α} {s : Finset α} (s0 : (s.erase x).Nonempty), (s.erase x).max' s0 ≠ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.max_empty`：max_empty : (∅ : Finset α).max = ⊥
· 使用定理 `WithBot.bot_ne_coe`：bot_ne_coe : ⊥ != (a : WithBot α)
-/
theorem max_erase_ne_self {s : Finset α} : (s.erase x).max ≠ x := by
  by_cases! s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [s0, max_empty]
    exact WithBot.bot_ne_coe
/-
**Finset.min_erase_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：min_erase_ne_self {s : Finset α} : (s.erase x).min != x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_toDual_min`：map_toDual_min (s : Finset α) : s.min.map toDual 
= (s.image toDual).max
· 使用定理 `Finset.image_erase`：image_erase [DecidableEq α] {f : α -> β} (hf : Injec
tive f) (s : Finset α) (a : α) : (s.erase a).image f = (s.image f).erase (f a)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `WithTop.map_coe`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (a : α), Wi
thTop.map f ↑a = ↑(f a)
· 使用定理 `Finset.max_erase_ne_self`：max_erase_ne_self {s : Finset α} : (s.erase x)
.max != x
-/
theorem min_erase_ne_self {s : Finset α} : (s.erase x).min ≠ x := by
  apply mt (congr_arg (WithTop.map toDual))
  rw [map_toDual_min, image_erase toDual.injective, WithTop.map_coe]
  apply max_erase_ne_self
/-
**Finset.exists_next_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_next_right {x : α} {s : Finset α} (h : exists y in s, x < y) : exis
ts y in s, x < y ∧ forall z in s, x < z -> y <= z
参数：h : exists y in s, x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
-/
theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
  ⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ <| mem_filter.2 ⟨hzs, by simpa⟩⟩
/-
**Finset.exists_next_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_next_left {x : α} {s : Finset α} (h : exists y in s, y < x) : exist
s y in s, y < x ∧ forall z in s, z < x -> z <= y
参数：h : exists y in s, y < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_next_right`：exists_next_right {x : α} {s : Finset α} (h : 
exists y in s, x < y) : exists y in s, x < y ∧ forall z in s, x < z -> y <= z
-/
theorem exists_next_left {x : α} {s : Finset α} (h : ∃ y ∈ s, y < x) :
    ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y :=
  @exists_next_right αᵒᵈ _ x s h

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card t + 1`. -/
/-
**Finset.card_le_of_interleaved** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_of_interleaved {s t : Finset α} (h : forallᵉ (x in s) (y in s), x 
< y -> (forall z in s, z ∉ Set.Ioo x y) -> exists z in t, x < z ∧ z < y) : s.car
d <= t.card + 1
参数：h : forallᵉ (x in s) (y in s), x < y -> (forall z in s, z ∉ Set.Ioo x y) -> e
xists z in t, x < z ∧ z < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_next_right`：exists_next_right {x : α} {s : Finset α} (h : 
exists y in s, x < y) : exists y in s, x < y ∧ forall z in s, x < z -> y <= z
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.lt_inf_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderTop α] {s : Finset ι} {f : ι → α} {a : α},   a < ⊤ → (a < s.inf
 f ↔ ∀ …
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `Finset.insert_subset_insert`：insert_subset_insert (a : α) {s t : Finset 
α} (h : s subseteq t) : insert a s subseteq insert a t
· 使用定理 `Finset.image_subset_image`：image_subset_image {s₁ s₂ : Finset α} (h : s₁
 subseteq s₂) : s₁.image f subseteq s₂.image f
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.min_mem_insert_top_image_coe`：min_mem_insert_top_image_coe (s : F
inset α) : s.min in (insert ⊤ (s.image (↑)) : Finset (WithTop α))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s

--- 原说明 ---
If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card t + 1`
.
-/
theorem card_le_of_interleaved {s t : Finset α}
    (h : ∀ᵉ (x ∈ s) (y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 := by
  replace h : ∀ᵉ (x ∈ s) (y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y := by
    intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
    rcases h x hx a has hxa fun z hzs hz => hz.2.not_ge <| ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
    exact ⟨b, hbt, hxb, hba.trans_le <| ha _ hy hxy⟩
  set f : α → WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x ≤ a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
          WithTop.coe_lt_coe.2 <| hay.trans (by simpa using (mem_filter.1 hb).2)
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ ≤ (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
      card_mono <| image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ ≤ t.card + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card (t \ s) + 1`. -/
/-
**Finset.card_le_sdiff_of_interleaved** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_sdiff_of_interleaved {s t : Finset α} (h : forallᵉ (x in s) (y in 
s), x < y -> (forall z in s, z ∉ Set.Ioo x y) -> exists z in t, x < z ∧ z < y) :
 s.card <= (t \ s).card + 1
参数：h : forallᵉ (x in s) (y in s), x < y -> (forall z in s, z ∉ Set.Ioo x y) -> e
xists z in t, x < z ∧ z < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_of_interleaved`：card_le_of_interleaved {s t : Finset α} (
h : forallᵉ (x in s) (y in s), x < y -> (forall z in s, z ∉ Set.Ioo x y) -> exis
ts z in t, x < z ∧ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t

--- 原说明 ---
If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card (t \ s
) + 1`.
-/
theorem card_le_sdiff_of_interleaved {s t : Finset α}
    (h :
      ∀ᵉ (x ∈ s) (y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

@[deprecated (since := "2026-06-03")]
alias card_le_diff_of_interleaved := card_le_sdiff_of_interleaved

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
/-
**Finset.induction_on_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_max [DecidableEq α] {motive : Finset α -> Prop} (s : Finset α
) (empty : motive ∅) (insert : forall a s, (forall x in s, x < a) -> motive s ->
 motive (insert a s)) : motive s
参数：s : Finset α；empty : motive ∅；insert : forall a s, (forall x in s, x < a) -> 
motive s -> motive (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eraseInduction`：eraseInduction [DecidableEq α] {p : Finset α -> P
rop} (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α
) : p S
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.lt_max'_of_mem_erase_max'`：∀ {α : Type u_2} [inst : LinearOrder α
] (s : Finset α) (H : s.Nonempty) [inst_1 : DecidableEq α] {a : α},   a ∈ s.eras
e (s.max' H) → a < s.m…

--- 原说明 ---
Induction principle for `Finset`s in a linearly ordered type: a predicate is tru
e on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements
 of `s`, `p s`
  implies `p (insert a s)`.
-/
theorem induction_on_max
    [DecidableEq α] {motive : Finset α → Prop} (s : Finset α) (empty : motive ∅)
    (insert : ∀ a s, (∀ x ∈ s, x < a) → motive s → motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact empty
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact insert _ _ (fun x ↦ s.lt_max'_of_mem_erase_max' hne) (ih _ H)

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
/-
**Finset.induction_on_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_min [DecidableEq α] {motive : Finset α -> Prop} (s : Finset α
) (empty : motive ∅) (insert : forall a s, (forall x in s, a < x) -> motive s ->
 motive (insert a s)) : motive s
参数：s : Finset α；empty : motive ∅；insert : forall a s, (forall x in s, a < x) -> 
motive s -> motive (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max`：induction_on_max [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, x < a) …

--- 原说明 ---
Induction principle for `Finset`s in a linearly ordered type: a predicate is tru
e on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of
 `s`, `p s`
  implies `p (insert a s)`.
-/
theorem induction_on_min
    [DecidableEq α] {motive : Finset α → Prop} (s : Finset α) (empty : motive ∅)
    (insert : ∀ a s, (∀ x ∈ s, a < x) → motive s → motive (insert a s)) : motive s :=
  @induction_on_max αᵒᵈ _ _ _ s empty insert

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
/-
**Finset.induction_on_max_value** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_max_value [DecidableEq ι] (f : ι -> α) {motive : Finset ι -> 
Prop} (s : Finset ι) (empty : motive ∅) (insert : forall a s, a ∉ s -> (forall x
 in s, f x <= f a) -> motive s -> motive (insert a s)) : motive s
参数：f : ι -> α；s : Finset ι；empty : motive ∅；insert : forall a s, a ∉ s -> (foral
l x in s, f x <= f a) -> motive s -> motive (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eraseInduction`：eraseInduction [DecidableEq α] {p : Finset α -> P
rop} (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α
) : p S
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s

--- 原说明 ---
Induction principle for `Finset`s in any type from which a given function `f` ma
ps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` deno
ted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`.
-/
theorem induction_on_max_value
    [DecidableEq ι] (f : ι → α) {motive : Finset ι → Prop} (s : Finset ι) (empty : motive ∅)
    (insert : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → motive s → motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, empty]
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine insert _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
/-
**Finset.induction_on_min_value** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_min_value [DecidableEq ι] (f : ι -> α) {motive : Finset ι -> 
Prop} (s : Finset ι) (empty : motive ∅) (insert : forall a s, a ∉ s -> (forall x
 in s, f a <= f x) -> motive s -> motive (insert a s)) : motive s
参数：f : ι -> α；s : Finset ι；empty : motive ∅；insert : forall a s, a ∉ s -> (foral
l x in s, f a <= f x) -> motive s -> motive (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max_value`：induction_on_max_value [DecidableEq ι] (f
 : ι -> α) {motive : Finset ι -> Prop} (s : Finset ι) (empty : motive ∅) (insert
 : forall a s, a ∉ …

--- 原说明 ---
Induction principle for `Finset`s in any type from which a given function `f` ma
ps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` deno
ted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`.
-/
theorem induction_on_min_value
    [DecidableEq ι] (f : ι → α) {motive : Finset ι → Prop} (s : Finset ι) (empty : motive ∅)
    (insert : ∀ a s, a ∉ s → (∀ x ∈ s, f a ≤ f x) → motive s → motive (insert a s)) : motive s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s empty insert

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

/-
**Finset.exists_max_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_max_image (s : Finset β) (f : β -> α) (h : s.Nonempty) : exists x i
n s, forall x' in s, f x' <= f x
参数：s : Finset β；f : β -> α；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.max_of_nonempty`：max_of_nonempty {s : Finset α} (h : s.Nonempty) 
: exists a : α, s.max = a
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_of_max`：mem_of_max {s : Finset α} : forall {a : α}, s.max = a
 -> a in s
· 使用定理 `Finset.le_max_of_eq`：le_max_of_eq {s : Finset α} {a b : α} (h₁ : a in s)
 (h₂ : s.max = b) : a <= b
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩
/-
**Finset.exists_min_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_min_image (s : Finset β) (f : β -> α) (h : s.Nonempty) : exists x i
n s, forall x' in s, f x <= f x'
参数：s : Finset β；f : β -> α；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_max_image`：exists_max_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x' <= f x
-/
theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h

end ExistsMaxMin

/-
**Finset.isGLB_iff_isLeast** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty)
 : IsGLB (s : Set α) i ↔ IsLeast (↑s) i
参数：i : α；s : Finset α；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `IsGreatest.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α) (a : α), IsG
reatest s a = (a ∈ s ∧ a ∈ upperBounds s)
· 使用定理 `IsGLB.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), IsGLB s = IsGrea
test (lowerBounds s)
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `Finset.isLeast_min'`：isLeast_min' : IsLeast (↑s) (s.min' H)
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
-/
theorem isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i := by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))
/-
**Finset.isLUB_iff_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isLUB_iff_isGreatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonemp
ty) : IsLUB (s : Set α) i ↔ IsGreatest (↑s) i
参数：i : α；s : Finset α；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.isGLB_iff_isLeast`：isGLB_iff_isLeast [LinearOrder α] (i : α) (s :
 Finset α) (hs : s.Nonempty) : IsGLB (s : Set α) i ↔ IsLeast (↑s) i
-/
theorem isLUB_iff_isGreatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @isGLB_iff_isLeast αᵒᵈ _ i s hs
/-
**Finset.isGLB_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) 
i) (hs : s.Nonempty) : i in s
参数：s : Finset α；his : IsGLB (s : Set α) i；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.isGLB_iff_isLeast`：isGLB_iff_isLeast [LinearOrder α] (i : α) (s :
 Finset α) (hs : s.Nonempty) : IsGLB (s : Set α) i ↔ IsLeast (↑s) i
-/
theorem isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1
/-
**Finset.isLUB_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isLUB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) 
i) (hs : s.Nonempty) : i in s
参数：s : Finset α；his : IsLUB (s : Set α) i；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.isGLB_mem`：isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his 
: IsGLB (s : Set α) i) (hs : s.Nonempty) : i in s
-/
theorem isLUB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s :=
  @isGLB_mem αᵒᵈ _ i s his hs

end Finset

/-
**Multiset.exists_max_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.exists_max_image {α R : Type*} [LinearOrder R] (f : α -> R) {s : 
Multiset α} (hs : s != 0) : exists y in s, forall z in s, f z <= f y
参数：f : α -> R；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_max_image`：exists_max_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x' <= f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.toFinset_nonempty`：toFinset_nonempty : s.toFinset.Nonempty ↔ s 
!= 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
-/
theorem Multiset.exists_max_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α}
    (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f z ≤ f y := by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz ↦ hy _ (mem_toFinset.mpr hz)⟩
/-
**Multiset.exists_min_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.exists_min_image {α R : Type*} [LinearOrder R] (f : α -> R) {s : 
Multiset α} (hs : s != 0) : exists y in s, forall z in s, f y <= f z
参数：f : α -> R；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_max_image`：Multiset.exists_max_image {α R : Type*} [Line
arOrder R] (f : α -> R) {s : Multiset α} (hs : s != 0) : exists y in s, forall z
 in s, f z <= f…
-/
theorem Multiset.exists_min_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α}
    (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f y ≤ f z :=
  @exists_max_image α Rᵒᵈ _ f s hs
