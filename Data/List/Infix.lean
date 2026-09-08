/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Induction
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.List.Basic

/-!
# Prefixes, suffixes, infixes

This file proves properties about
* `List.isPrefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `List.isSuffix`: `l₁` is a suffix of `l₂` if `l₂` ends with `l₁`.
* `List.isInfix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some suffix of `l₂`.
* `List.inits`: The list of prefixes of a list.
* `List.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `Mathlib/Data/List/Defs.lean`.

## Notation

* `l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
* `l₁ <:+ l₂`: `l₁` is a suffix of `l₂`.
* `l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

public section

variable {α β : Type*}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α}

/-! ### prefix, suffix, infix -/

section Fix

/-
**List.IsPrefix.take** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ (n : ℕ), List.take n l₁ <
+: List.take n l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `List.IsPrefix.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l
₂ <+: l₃ → l₁ <+: l₃
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
-/
@[gcongr] lemma IsPrefix.take (h : l₁ <+: l₂) (n : ℕ) : l₁.take n <+: l₂.take n := by
  simpa [prefix_take_iff, Nat.min_le_left] using (take_prefix n l₁).trans h
/-
**List.IsPrefix.drop** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ (n : ℕ), List.drop n l₁ <
+: List.drop n l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.prefix_iff_eq_take`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ ↔ 
l₁ = List.take l₁.length l₂
· 使用定理 `List.drop_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.take j l) = List.take (j - i) (List.drop i l)
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
-/
@[gcongr] lemma IsPrefix.drop (h : l₁ <+: l₂) (n : ℕ) : l₁.drop n <+: l₂.drop n := by
  rw [prefix_iff_eq_take.mp h, drop_take]; apply take_prefix

attribute [gcongr] take_prefix_take_left
/-
**List.isPrefix_append_of_length** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：isPrefix_append_of_length (h : l₁.length <= l₂.length) : l₁ <+: l₂ ++ l₃ ↔
 l₁ <+: l₂
参数：h : l₁.length <= l₂.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prefix_iff_eq_take`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ ↔ 
l₁ = List.take l₁.length l₂
· 使用定理 `List.take_eq_left_iff`：∀ {α : Type u} {x y : List α} {n : ℕ}, List.take 
n (x ++ y) = List.take n x ↔ y = [] ∨ n ≤ x.length
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `List.IsPrefix.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l
₂ <+: l₃ → l₁ <+: l₃
· 使用定理 `List.prefix_append`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁ <+: l₁ ++ l₂
-/
lemma isPrefix_append_of_length (h : l₁.length ≤ l₂.length) : l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂ :=
  ⟨fun h ↦ by rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left_iff]; tauto,
   fun h ↦ h.trans <| l₂.prefix_append l₃⟩
/-
**List.take_isPrefix_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} {m n : ℕ}, List.take m l <+: List.take n l ↔
 m ≤ n ∨ l.length ≤ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
@[simp] lemma take_isPrefix_take {m n : ℕ} : l.take m <+: l.take n ↔ m ≤ n ∨ l.length ≤ n := by
  simp [prefix_take_iff, take_prefix]; omega

@[gcongr]
/-
**List.IsPrefix.flatten** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <+: l₂ → l₁.flatten <+: l₂.fl
atten
参数：List α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatten_append`：∀ {α : Type u_1} {L₁ L₂ : List (List α)}, (L₁ ++ L₂
).flatten = L₁.flatten ++ L₂.flatten
-/
protected theorem IsPrefix.flatten {l₁ l₂ : List (List α)} (h : l₁ <+: l₂) :
    l₁.flatten <+: l₂.flatten := by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
/-
**List.IsPrefix.flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α},   l₁ <+: l₂ → ∀ (f : α →
 List β), List.flatMap f l₁ <+: List.flatMap f l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.flatten`：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <+: 
l₂ → l₁.flatten <+: l₂.flatten
· 使用定理 `List.IsPrefix.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) ⦃l₁ l₂ : 
List α⦄, l₁ <+: l₂ → List.map f l₁ <+: List.map f l₂
-/
protected theorem IsPrefix.flatMap (h : l₁ <+: l₂) (f : α → List β) :
    l₁.flatMap f <+: l₂.flatMap f :=
  (h.map _).flatten

@[gcongr]
/-
**List.IsSuffix.flatten** 是 Mathlib 中的一个定理，位于命名空间 `List.IsSuffix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <:+ l₂ → l₁.flatten <:+ l₂.fl
atten
参数：List α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatten_append`：∀ {α : Type u_1} {L₁ L₂ : List (List α)}, (L₁ ++ L₂
).flatten = L₁.flatten ++ L₂.flatten
-/
protected theorem IsSuffix.flatten {l₁ l₂ : List (List α)} (h : l₁ <:+ l₂) :
    l₁.flatten <:+ l₂.flatten := by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
/-
**List.IsSuffix.flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List.IsSuffix`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α},   l₁ <:+ l₂ → ∀ (f : α →
 List β), List.flatMap f l₁ <:+ List.flatMap f l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.flatten`：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <:+ 
l₂ → l₁.flatten <:+ l₂.flatten
· 使用定理 `List.IsSuffix.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) ⦃l₁ l₂ : 
List α⦄, l₁ <:+ l₂ → List.map f l₁ <:+ List.map f l₂
-/
protected theorem IsSuffix.flatMap (h : l₁ <:+ l₂) (f : α → List β) :
    l₁.flatMap f <:+ l₂.flatMap f :=
  (h.map _).flatten

@[gcongr]
/-
**List.IsInfix.flatten** 是 Mathlib 中的一个定理，位于命名空间 `List.IsInfix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <:+: l₂ → l₁.flatten <:+: l₂.
flatten
参数：List α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.flatten_append`：∀ {α : Type u_1} {L₁ L₂ : List (List α)}, (L₁ ++ L₂
).flatten = L₁.flatten ++ L₂.flatten
-/
protected theorem IsInfix.flatten {l₁ l₂ : List (List α)} (h : l₁ <:+: l₂) :
    l₁.flatten <:+: l₂.flatten := by
  rcases h with ⟨l, l', rfl⟩
  simp

@[gcongr]
/-
**List.IsInfix.flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List.IsInfix`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α},   l₁ <:+: l₂ → ∀ (f : α 
→ List β), List.flatMap f l₁ <:+: List.flatMap f l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsInfix.flatten`：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁ <:+: 
l₂ → l₁.flatten <:+: l₂.flatten
· 使用定理 `List.IsInfix.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) ⦃l₁ l₂ : L
ist α⦄, l₁ <:+: l₂ → List.map f l₁ <:+: List.map f l₂
-/
protected theorem IsInfix.flatMap (h : l₁ <:+: l₂) (f : α → List β) :
    l₁.flatMap f <:+: l₂.flatMap f :=
  (h.map _).flatten
/-
**List.dropSlice_sublist** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：dropSlice_sublist (n m : Nat) (l : List α) : l.dropSlice n m <+ l
参数：n m : Nat；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropSlice_eq`：dropSlice_eq (xs : List α) (n m : Nat) : dropSlice n 
m xs = xs.take n ++ xs.drop (n + m)
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.drop_sublist`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.drop i l
).Sublist l
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
lemma dropSlice_sublist (n m : ℕ) (l : List α) : l.dropSlice n m <+ l :=
  calc
    l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, Nat.add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _
/-
**List.dropSlice_subset** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：dropSlice_subset (n m : Nat) (l : List α) : l.dropSlice n m subseteq l
参数：n m : Nat；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用引理 `List.dropSlice_sublist`：dropSlice_sublist (n m : Nat) (l : List α) : l.d
ropSlice n m <+ l
-/
lemma dropSlice_subset (n m : ℕ) (l : List α) : l.dropSlice n m ⊆ l :=
  (dropSlice_sublist n m l).subset
/-
**List.mem_of_mem_dropSlice** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：mem_of_mem_dropSlice {n m : Nat} {l : List α} {a : α} (h : a in l.dropSlic
e n m) : a in l
参数：h : a in l.dropSlice n m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.dropSlice_subset`：dropSlice_subset (n m : Nat) (l : List α) : l.dro
pSlice n m subseteq l
-/
lemma mem_of_mem_dropSlice {n m : ℕ} {l : List α} {a : α} (h : a ∈ l.dropSlice n m) : a ∈ l :=
  dropSlice_subset n m l h
/-
**List.tail_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_subset (l : List α) : tail l subseteq l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.tail_sublist`：∀ {α : Type u_1} (l : List α), l.tail.Sublist l
-/
theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).subset
/-
**List.mem_of_mem_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_mem_dropLast (h : a in l.dropLast) : a in l
参数：h : a in l.dropLast。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dropLast_subset`：∀ {α : Type u_1} (l : List α), l.dropLast ⊆ l
-/
theorem mem_of_mem_dropLast (h : a ∈ l.dropLast) : a ∈ l :=
  dropLast_subset l h

attribute [gcongr] Sublist.drop
attribute [refl] prefix_refl suffix_refl infix_refl
/-
**List.concat_get_prefix** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：concat_get_prefix {x y : List α} (h : x <+: y) (hl : x.length < y.length) 
: x ++ [y.get ⟨x.length, hl⟩] <+: y
参数：h : x <+: y；hl : x.length < y.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.prefix_iff_eq_take`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ ↔ 
l₁ = List.take l₁.length l₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_concat_get`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.l
ength), (List.take i l).concat l[i] = List.take (i + 1) l
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
theorem concat_get_prefix {x y : List α} (h : x <+: y) (hl : x.length < y.length) :
    x ++ [y.get ⟨x.length, hl⟩] <+: y := by
  use y.drop (x.length + 1)
  nth_rw 1 [List.prefix_iff_eq_take.mp h]
  convert! List.take_append_drop (x.length + 1) y using 2
  rw [← List.take_concat_get, List.concat_eq_append]; rfl
/-
**List.prefix_append_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prefix_append_drop {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₂ = l₁ ++ l₂.drop l
₁.length
参数：h : l₁ <+: l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.prefix_nil`：∀ {α : Type u_1} {l : List α}, l <+: [] ↔ l = []
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_prefix_cons`：∀ {α : Type u_1} {a : α} {l₁ : List α} {b : α} {l
₂ : List α}, a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem prefix_append_drop {l₁ l₂ : List α} (h : l₁ <+: l₂) :
    l₂ = l₁ ++ l₂.drop l₁.length := by
  induction l₂ generalizing l₁ with
  | nil => simp [List.prefix_nil.mp h]
  | cons _ _ ih =>
    cases l₁ with
    | nil => rfl
    | cons =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      simpa using ih h'
/-
**List.decidableInfix** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：decidableInfix [DecidableEq α] : forall l₁ l₂ : List α, Decidable (l₁ <:+:
 l₂) | [], l₂ => isTrue ⟨[], l₂, rfl⟩ | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ =>
 by simp at te | l₁, b :: l₂ => letI
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
  | l₁, b :: l₂ =>
    letI := l₁.decidableInfix l₂
    @decidable_of_decidable_of_iff (l₁ <+: b :: l₂ ∨ l₁ <:+: l₂) _ _
      infix_cons_iff.symm
/-
**List.IsPrefix.reduceOption** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List (Option α)}, l₁ <+: l₂ → l₁.reduceOption <+
: l₂.reduceOption
参数：Option α。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsPrefix.filterMap`：∀ {α : Type u_1} {β : Type u_2} (f : α → Option
 β) ⦃l₁ l₂ : List α⦄,   l₁ <+: l₂ → List.filterMap f l₁ <+: List.filterMap f l₂
-/
protected theorem IsPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id
/-
**List.singleton_infix_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_infix_iff (x : α) (xs : List α) : [x] <:+: xs ↔ x in xs
参数：x : α；xs : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_iff_append`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ s 
t, l = s ++ a :: t
· 使用定理 `List.IsInfix.eq_1`：∀ {α : Type u} (l₁ l₂ : List α), (l₁ <:+: l₂) = ∃ s t
, s ++ l₁ ++ t = l₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_infix_iff (x : α) (xs : List α) :
    [x] <:+: xs ↔ x ∈ xs := by
  rw [List.mem_iff_append, List.IsInfix]
  congr! 4
  simp [eq_comm]

@[simp]
/-
**List.singleton_infix_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_infix_singleton_iff {x y : α} : [x] <:+: [y] ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `List.infix_refl`：∀ {α : Type u_1} (l : List α), l <:+: l
-/
theorem singleton_infix_singleton_iff {x y : α} :
    [x] <:+: [y] ↔ x = y := by
  constructor
  · rintro ⟨_ | _, bs, h⟩ <;> simp_all
  · rintro rfl; rfl
/-
**List.infix_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：infix_singleton_iff (xs : List α) (x : α) : xs <:+: [x] ↔ xs = [] ∨ xs = [
x]
参数：xs : List α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem infix_singleton_iff (xs : List α) (x : α) :
    xs <:+: [x] ↔ xs = [] ∨ xs = [x] := by
  match xs with
  | [] => simp
  | [_] => simp [List.singleton_infix_singleton_iff]
  | _ :: _ :: _ =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · simp
/-
**List.infix_antisymm** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：infix_antisymm {l₁ l₂ : List α} (h₁ : l₁ <:+: l₂) (h₂ : l₂ <:+: l₁) : l₁ =
 l₂
参数：h₁ : l₁ <:+: l₂；h₂ : l₂ <:+: l₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.antisymm`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₂.Sublist l₁ → l₁ = l₂
· 使用定理 `List.IsInfix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁
.Sublist l₂
-/
lemma infix_antisymm {l₁ l₂ : List α} (h₁ : l₁ <:+: l₂) (h₂ : l₂ <:+: l₁) :
    l₁ = l₂ :=
  h₁.sublist.antisymm h₂.sublist
/-
**List.IsPrefix.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.IsPrefix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₂.Nodup → l₁.Nodup
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.IsPrefix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁
.Sublist l₂
-/
protected theorem IsPrefix.nodup {l₁ l₂ : List α} (h : l₁ <+: l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist
/-
**List.IsInfix.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.IsInfix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₂.Nodup → l₁.Nodup
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.IsInfix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁
.Sublist l₂
-/
protected theorem IsInfix.nodup {l₁ l₂ : List α} (h : l₁ <:+: l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist
/-
**List.IsSuffix.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.IsSuffix`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₂.Nodup → l₁.Nodup
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.IsSuffix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
.Sublist l₂
-/
protected theorem IsSuffix.nodup {l₁ l₂ : List α} (h : l₁ <:+ l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (List α) (· <+: ·) where
  refl _ := prefix_rfl
  trans _ _ _ := IsPrefix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (List α) (· <:+ ·) where
  refl _ := suffix_rfl
  trans _ _ _ := IsSuffix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (List α) (· <:+: ·) where
  refl _ := infix_rfl
  trans _ _ _ := IsInfix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
/-
**List.mem_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_inits : forall s t : List α, s in inits t ↔ s <+: t | s, [] => suffice
s s = nil ↔ s <+: nil by simpa only [inits, mem_singleton] ⟨fun h => h.symm ▸ pr
efix_rfl, eq_nil_of_prefix_nil⟩ | s, a :: t => suffices (s = nil ∨ exists l in i
nits t, a :: l = s) ↔ s <+: a :: t by simpa ⟨fun o => match s, o with | _, Or.in
l rfl => ⟨_, rfl⟩ | s, Or.inr ⟨r, hr, hs⟩ => by let ⟨s, ht⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_rfl, eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion rfl (heq_of_eq hr)) fun ba (st : s ++ r ≍ t) =>
          Or.inr <| by rw [eq_of_heq ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, eq_of_heq st⟩, rfl⟩⟩

@[simp]
/-
**List.mem_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s t : List α), s ∈ t.tails ↔ s <:+ t
参数：s t : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton, suffix_nil]
  | s, a :: t => by
    simp only [tails, mem_cons, mem_tails s t]
    exact
      show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
        ⟨fun o =>
          match s, t, o with
          | _, t, Or.inl rfl => suffix_rfl
          | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
          fun e =>
          match s, t, e with
          | _, t, ⟨[], rfl⟩ => Or.inl rfl
          | s, t, ⟨b :: l, he⟩ =>
            List.noConfusion rfl (heq_of_eq he) fun _ lt => Or.inr ⟨l, eq_of_heq lt⟩⟩
/-
**List.inits_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t
 => a :: t
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp
/-
**List.tails_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp

@[simp]
/-
**List.inits_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s t : List α), (s ++ t).inits = s.inits ++ List.map (fun
 l => s ++ l) t.inits.tail
参数：s t : List α；s ++ t；fun l => s ++ l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [inits_append s t, Function.comp_def]

@[simp]
/-
**List.tails_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s t : List α), (s ++ t).tails = List.map (fun l => l ++ 
t) s.tails ++ t.tails.tail
参数：s t : List α；s ++ t；fun l => l ++ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
/-
**List.inits_eq_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α), l.inits = (List.map List.reverse l.reverse.
tails).reverse
参数：l : List α；List.map List.reverse l.reverse.tails。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_inj_left, ← map_reverse]
/-
**List.tails_eq_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α), l.tails = (List.map List.reverse l.reverse.
inits).reverse
参数：l : List α；List.map List.reverse l.reverse.inits。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l]
/-
**List.inits_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.ta
ils)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.tails_eq_inits`：∀ {α : Type u_1} (l : List α), l.tails = (List.map 
List.reverse l.reverse.inits).reverse
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [← map_reverse]
/-
**List.tails_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.in
its)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.inits_eq_tails`：∀ {α : Type u_1} (l : List α), l.inits = (List.map 
List.reverse l.reverse.tails).reverse
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [← map_reverse]
/-
**List.map_reverse_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <
| reverse l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.inits_eq_tails`：∀ {α : Type u_1} (l : List α), l.inits = (List.map 
List.reverse l.reverse.tails).reverse
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [← map_reverse]
/-
**List.map_reverse_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <
| reverse l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.tails_eq_inits`：∀ {α : Type u_1} (l : List α), l.tails = (List.map 
List.reverse l.reverse.inits).reverse
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [← map_reverse]

@[simp]
/-
**List.length_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_tails (l : List α) : length (tails l) = length l + 1
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction l with
  | nil => simp
  | cons x l IH => simpa using IH

@[simp]
/-
**List.length_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_inits (l : List α) : length (inits l) = length l + 1
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.inits_eq_tails`：∀ {α : Type u_1} (l : List α), l.inits = (List.map 
List.reverse l.reverse.tails).reverse
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_tails`：length_tails (l : List α) : length (tails l) = length
 l + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]

@[simp]
/-
**List.getElem_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_tails (l : List α) (n : Nat) (h : n < (tails l).length) : (tails l
)[n] = l.drop n
参数：l : List α；n : Nat；h : n < (tails l).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
-/
theorem getElem_tails (l : List α) (n : Nat) (h : n < (tails l).length) :
    (tails l)[n] = l.drop n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]
/-
**List.get_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_tails (l : List α) (n : Fin (length (tails l))) : (tails l).get n = l.
drop n
参数：l : List α；n : Fin (length (tails l))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_tails`：getElem_tails (l : List α) (n : Nat) (h : n < (tails
 l).length) : (tails l)[n] = l.drop n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_tails (l : List α) (n : Fin (length (tails l))) : (tails l).get n = l.drop n := by
  simp

@[simp]
/-
**List.getElem_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_inits (l : List α) (n : Nat) (h : n < length (inits l)) : (inits l
)[n] = l.take n
参数：l : List α；n : Nat；h : n < length (inits l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
-/
theorem getElem_inits (l : List α) (n : Nat) (h : n < length (inits l)) :
    (inits l)[n] = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]
/-
**List.get_inits** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_inits (l : List α) (n : Fin (length (inits l))) : (inits l).get n = l.
take n
参数：l : List α；n : Fin (length (inits l))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_inits`：getElem_inits (l : List α) (n : Nat) (h : n < length
 (inits l)) : (inits l)[n] = l.take n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_inits (l : List α) (n : Fin (length (inits l))) : (inits l).get n = l.take n := by
  simp
/-
**List.map_inits** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：map_inits {β : Type*} (g : α -> β) : (l.map g).inits = l.inits.map (map g)
参数：g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.inits.eq_1`：∀ {α : Type u_1}, [].inits = [[]]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.inits_append`：∀ {α : Type u_1} (s t : List α), (s ++ t).inits = s.i
nits ++ List.map (fun l => s ++ l) t.inits.tail
-/
lemma map_inits {β : Type*} (g : α → β) : (l.map g).inits = l.inits.map (map g) := by
  induction l using reverseRecOn <;> simp [*]
/-
**List.map_tails** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：map_tails {β : Type*} (g : α -> β) : (l.map g).tails = l.tails.map (map g)
参数：g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.tails.eq_1`：∀ {α : Type u_1}, [].tails = [[]]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.tails_append`：∀ {α : Type u_1} (s t : List α), (s ++ t).tails = Lis
t.map (fun l => l ++ t) s.tails ++ t.tails.tail
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.append_cancel_right_eq`：∀ {α : Type u_1} (as bs cs : List α), (as +
+ bs = cs ++ bs) = (as = cs)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map_tails {β : Type*} (g : α → β) : (l.map g).tails = l.tails.map (map g) := by
  induction l using reverseRecOn <;> simp [*]
/-
**List.take_inits** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：take_inits {n} : (l.take n).inits = l.inits.take (n + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_inits`：length_inits (l : List α) : length (inits l) = length
 l + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `Nat.add_min_add_right`：∀ (a b c : ℕ), min (a + c) (b + c) = min a b + c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `List.getElem_inits`：getElem_inits (l : List α) (n : Nat) (h : n < length
 (inits l)) : (inits l)[n] = l.take n
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `List.length_take_le'`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take 
i l).length ≤ l.length
· 使用定理 `List.getElem_take`：∀ {α : Type u_1} {xs : List α} {j i : ℕ} {h : i < (Li
st.take j xs).length}, (List.take j xs)[i] = xs[i]
· 使用定理 `Nat.min_assoc`：∀ (a b c : ℕ), min (min a b) c = min a (min b c)
-/
lemma take_inits {n} : (l.take n).inits = l.inits.take (n + 1) := by
  apply ext_getElem <;> (simp [take_take] <;> grind)

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

/-
**List.insert_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insert_eq_ite (a : α) (l : List α) : insert a l = if a in l then l else a 
:: l
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem insert_eq_ite (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l := by
  simp only [← elem_iff]
  rfl

@[simp]
/-
**List.suffix_insert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：suffix_insert (a : α) (l : List α) : l <:+ l.insert a
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
-/
theorem suffix_insert (a : α) (l : List α) : l <:+ l.insert a := by
  by_cases h : a ∈ l
  · simp only [insert_of_mem h, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons]
/-
**List.infix_insert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：infix_insert (a : α) (l : List α) : l <:+: l.insert a
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.isInfix`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
 <:+: l₂
· 使用定理 `List.suffix_insert`：suffix_insert (a : α) (l : List α) : l <:+ l.insert 
a
-/
theorem infix_insert (a : α) (l : List α) : l <:+: l.insert a :=
  (suffix_insert a l).isInfix
/-
**List.sublist_insert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_insert (a : α) (l : List α) : l <+ l.insert a
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsSuffix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
.Sublist l₂
· 使用定理 `List.suffix_insert`：suffix_insert (a : α) (l : List α) : l <:+ l.insert 
a
-/
theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).sublist
/-
**List.subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：subset_insert (a : α) (l : List α) : l subseteq l.insert a
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.sublist_insert`：sublist_insert (a : α) (l : List α) : l <+ l.insert
 a
-/
theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).subset

end Insert

end List

