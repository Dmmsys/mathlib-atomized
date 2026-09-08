/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Theorems about the `Disjoint` relation on `Set`.
-/

public section

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t u s₁ s₂ t₁ t₂ : Set α}


/-! ### Disjointness -/

/-
**Set.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥

--- 原说明 ---
### Disjointness
-/
protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le
/-
**Set.disjoint_iff_inter_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_iff_inter_eq_empty : Disjoint s t ↔ s inter t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
-/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
/-
**Set._root_.Disjoint.inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot

@[grind =]
/-
**Set.disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
-/
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and

alias ⟨_root_.Disjoint.notMem_of_mem_left, _⟩ := disjoint_left
/-
**Set.disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right, _⟩ := disjoint_right
/-
**Set.not_disjoint_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in s ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_disjoint_iff : ¬Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t := by grind
/-
**Set.not_disjoint_iff_nonempty_inter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：not_disjoint_iff_nonempty_inter : ¬ Disjoint s t ↔ (s inter t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
-/
lemma not_disjoint_iff_nonempty_inter : ¬ Disjoint s t ↔ (s ∩ t).Nonempty := not_disjoint_iff

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter
/-
**Set.disjoint_or_nonempty_inter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s inter t).None
mpty
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.1
/-
**Set.disjoint_iff_forall_ne** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_iff_forall_ne : Disjoint s t ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, 
b in t -> a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma disjoint_iff_forall_ne : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ t → a ≠ b := by grind

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne
/-
**Set.disjoint_of_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_of_subset_left (h : s subseteq u) (d : Disjoint u t) : Disjoint s
 t
参数：h : s subseteq u；d : Disjoint u t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
-/
lemma disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t := d.mono_left h
/-
**Set.disjoint_of_subset_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_of_subset_right (h : t subseteq u) (d : Disjoint s u) : Disjoint 
s t
参数：h : t subseteq u；d : Disjoint s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
-/
lemma disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t := d.mono_right h
/-
**Set.disjoint_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (h : Disjoi
nt s₂ t₂) : Disjoint s₁ t₁
参数：hs : s₁ subseteq s₂；ht : t₁ subseteq t₂；h : Disjoint s₂ t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
-/
lemma disjoint_of_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁ :=
  h.mono hs ht

@[simp]
/-
**Set.disjoint_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_union_left : Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sup_left`：disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c
 ∧ Disjoint b c
-/
lemma disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left

@[simp]
/-
**Set.disjoint_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_union_right : Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s 
u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sup_right`：disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a
 b ∧ Disjoint a c
-/
lemma disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right
/-
**Set.disjoint_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s : Set α), Disjoint s ∅
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_right`：disjoint_bot_right : Disjoint a ⊥
-/
@[simp] lemma disjoint_empty (s : Set α) : Disjoint s ∅ := disjoint_bot_right
/-
**Set.empty_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s : Set α), Disjoint ∅ s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
@[simp] lemma empty_disjoint (s : Set α) : Disjoint ∅ s := disjoint_bot_left
/-
**Set.univ_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α}, Disjoint Set.univ s ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_disjoint`：top_disjoint : Disjoint ⊤ a ↔ a = ⊥
-/
@[simp] lemma univ_disjoint : Disjoint univ s ↔ s = ∅ := top_disjoint
/-
**Set.disjoint_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α}, Disjoint s Set.univ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_top`：disjoint_top : Disjoint a ⊤ ↔ a = ⊥
-/
@[simp] lemma disjoint_univ : Disjoint s univ ↔ s = ∅ := disjoint_top
/-
**Set.disjoint_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_range_iff {β γ : Sort*} {x : β -> α} {y : γ -> α} : Disjoint (ran
ge x) (range y) ↔ forall i j, x i != y j
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
theorem disjoint_range_iff {β γ : Sort*} {x : β → α} {y : γ → α} :
    Disjoint (range x) (range y) ↔ ∀ i j, x i ≠ y j := by
  simp [Set.disjoint_iff_forall_ne]

end Set

/-! ### Disjoint sets -/

variable {α : Type*} {s t u : Set α}

namespace Disjoint

/-
**Disjoint.union_left** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s union t) 
u
参数：hs : Disjoint s u；ht : Disjoint t u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_left`：Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint 
b c) : Disjoint (a ⊔ b) c
-/
theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s ∪ t) u :=
  hs.sup_left ht
/-
**Disjoint.union_right** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t union 
u)
参数：ht : Disjoint s t；hu : Disjoint s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.sup_right`：Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoin
t a c) : Disjoint a (b ⊔ c)
-/
theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t ∪ u) :=
  ht.sup_right hu
/-
**Disjoint.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s inter u) t
参数：u : Set α；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.inf_left`：Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ 
c) b
-/
theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) t :=
  h.inf_left _
/-
**Disjoint.inter_left'** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u inter s) t
参数：u : Set α；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.inf_left'`：Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c 
⊓ a) b
-/
theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u ∩ s) t :=
  h.inf_left' _
/-
**Disjoint.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t inter u)
参数：u : Set α；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.inf_right`：Disjoint.inf_right (h : Disjoint a b) : Disjoint a (
b ⊓ c)
-/
theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t ∩ u) :=
  h.inf_right _
/-
**Disjoint.inter_right'** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u inter t)
参数：u : Set α；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.inf_right'`：Disjoint.inf_right' (h : Disjoint a b) : Disjoint a
 (c ⊓ b)
-/
theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u ∩ t) :=
  h.inf_right' _
/-
**Disjoint.subset_left_of_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：subset_left_of_subset_union (h : s subseteq t union u) (hac : Disjoint s u
) : s subseteq t
参数：h : s subseteq t union u；hac : Disjoint s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.left_le_of_le_sup_right`：Disjoint.left_le_of_le_sup_right (h : 
a <= b ⊔ c) (hd : Disjoint a c) : a <= b
-/
theorem subset_left_of_subset_union (h : s ⊆ t ∪ u) (hac : Disjoint s u) : s ⊆ t :=
  hac.left_le_of_le_sup_right h
/-
**Disjoint.subset_right_of_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：subset_right_of_subset_union (h : s subseteq t union u) (hab : Disjoint s 
t) : s subseteq u
参数：h : s subseteq t union u；hab : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.left_le_of_le_sup_left`：Disjoint.left_le_of_le_sup_left (h : a 
<= c ⊔ b) (hd : Disjoint a c) : a <= b
-/
theorem subset_right_of_subset_union (h : s ⊆ t ∪ u) (hab : Disjoint s t) : s ⊆ u :=
  hab.left_le_of_le_sup_left h

end Disjoint

namespace Set

/-
**Set.mem_union_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_union_of_disjoint (h : Disjoint s t) {x : α} : x in s union t ↔ Xor (x
 in s) (x in t)
参数：h : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_union_of_disjoint (h : Disjoint s t) {x : α} : x ∈ s ∪ t ↔ Xor (x ∈ s) (x ∈ t) := by
  grind [Xor]

end Set

