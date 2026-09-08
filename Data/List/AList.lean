/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
module

public import Mathlib.Data.List.Sigma

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `Sigma`: The elements of the list are of type `Sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `AList` structure. This file defines this structure and
provides ways to access, modify, and combine `AList`s.

* `AList.keys` returns a list of keys of the alist.
* `AList.membership` returns membership in the set of keys.
* `AList.erase` removes a certain key.
* `AList.insert` adds a key-value mapping to the list.
* `AList.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/

@[expose] public section


universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-- `AList β` is a key-value map stored as a `List` (i.e. a linked list).
  It is a wrapper around certain `List` functions with the added constraint
  that the list have unique keys. -/
/-
**AList** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AList (key val : Type)
参数：key val : Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AList β` is a key-value map stored as a `List` (i.e. a linked list).
  It is a wrapper around certain `List` functions with the added constraint
  that the list have unique keys.
-/
structure AList (β : α → Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/-- Given `l : List (Sigma β)`, create a term of type `AList β` by removing
entries with duplicate keys. -/
/-
**List.toAList** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.toAList [DecidableEq α] {β : α -> Type v} (l : List (Sigma β)) : ALis
t β where entries
参数：l : List (Sigma β)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodupKeys_dedupKeys`：nodupKeys_dedupKeys (l : List (Sigma β)) : Nod
upKeys (dedupKeys l)

--- 原说明 ---
Given `l : List (Sigma β)`, create a term of type `AList β` by removing
entries with duplicate keys.
-/
def List.toAList [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : AList β where
  entries := _
  nodupKeys := nodupKeys_dedupKeys l

namespace AList

@[ext]
/-
**AList.ext** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = t.entries → s
 = t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext : ∀ {s t : AList β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (AList β) := fun xs ys => by
  rw [AList.ext_iff]; infer_instance

/-! ### keys -/


/-- The list of keys of an association list. -/
/-
**AList.keys** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：keys (s : AList β) : List α
参数：s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list of keys of an association list.
-/
def keys (s : AList β) : List α :=
  s.entries.keys
/-
**AList.keys_nodup** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_nodup (s : AList β) : s.keys.Nodup
参数：s : AList β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem keys_nodup (s : AList β) : s.keys.Nodup :=
  s.nodupKeys

@[simp]
/-
**AList.keys_mk** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_mk (l : List (Sigma β)) (h) : (AList.mk l h).keys = l.keys
参数：l : List (Sigma β)；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_mk (l : List (Sigma β)) (h) : (AList.mk l h).keys = l.keys :=
  rfl

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `a ∈ s` means that `s` has a value associated to the key `a`.
-/
instance : Membership α (AList β) :=
  ⟨fun s a => a ∈ s.keys⟩
/-
**AList.mem_keys** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_keys {a : α} {s : AList β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl
/-
**AList.mem_of_perm** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a in
 s₁ ↔ a in s₂
参数：p : s₁.entries ~ s₂.entries。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff

@[simp]
/-
**AList.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_mk {l : List (Sigma β)} {h} {x : α} : x in AList.mk l h ↔ x in l.keys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {l : List (Sigma β)} {h} {x : α} : x ∈ AList.mk l h ↔ x ∈ l.keys :=
  .rfl

/-! ### empty -/


/-- The empty association list. -/
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty association list.
-/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], nodupKeys_nil⟩⟩
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AList β) :=
  ⟨∅⟩

@[simp]
/-
**AList.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：notMem_empty (a : α) : a ∉ (∅ : AList β)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem notMem_empty (a : α) : a ∉ (∅ : AList β) :=
  not_mem_nil

@[simp]
/-
**AList.empty_entries** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：empty_entries : (∅ : AList β).entries = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_entries : (∅ : AList β).entries = [] :=
  rfl

@[simp]
/-
**AList.keys_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_empty : (∅ : AList β).keys = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_empty : (∅ : AList β).keys = [] :=
  rfl

/-! ### singleton -/


/-- The singleton association list. -/
/-
**AList.singleton** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：singleton (a : α) (b : β a) : AList β
参数：a : α；b : β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton association list.
-/
def singleton (a : α) (b : β a) : AList β :=
  ⟨[⟨a, b⟩], nodupKeys_singleton _⟩

@[simp]
/-
**AList.singleton_entries** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk 
a b]
参数：a : α；b : β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl

@[simp]
/-
**AList.keys_singleton** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a]
参数：a : α；b : β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl

/-! ### lookup -/


section

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
/-
**AList.lookup** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：lookup (a : α) (s : AList β) : Option (β a)
参数：a : α；s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Look up the value associated to a key in an association list.
-/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.dlookup a

@[simp]
/-
**AList.lookup_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_empty (a) : lookup a (∅ : AList β) = none
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl
/-
**AList.lookup_isSome** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_isSome`：dlookup_isSome {a : α} {l : List (Sigma β)} : (dloo
kup a l).isSome ↔ a in l.keys
-/
theorem lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a ∈ s :=
  dlookup_isSome
/-
**AList.lookup_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_eq_none`：dlookup_eq_none {a : α} {l : List (Sigma β)} : dlo
okup a l = none ↔ a ∉ l.keys
-/
theorem lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s :=
  dlookup_eq_none
/-
**AList.mem_lookup_iff** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_lookup_iff {a : α} {b : β a} {s : AList β} : b in lookup a s ↔ Sigma.m
k a b in s.entries
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_iff`：mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma
 β)} (nd : l.NodupKeys) : b in dlookup a l ↔ Sigma.mk a b in l
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem mem_lookup_iff {a : α} {b : β a} {s : AList β} :
    b ∈ lookup a s ↔ Sigma.mk a b ∈ s.entries :=
  mem_dlookup_iff s.nodupKeys
/-
**AList.perm_lookup** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : s₁.l
ookup a = s₂.lookup a
参数：p : s₁.entries ~ s₂.entries。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.perm_dlookup`：perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : 
l₁.NodupKeys) (p : l₁ ~ l₂) : dlookup a l₁ = dlookup a l₂
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.nodupKeys p
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : α) (s : AList β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome

end

/-
**AList.keys_subset_keys_of_entries_subset_entries** 是 Mathlib 中的一个定理，位于命名空间 `AL
ist`。
形式化陈述：keys_subset_keys_of_entries_subset_entries {s₁ s₂ : AList β} (h : s₁.entri
es subseteq s₂.entries) : s₁.keys subseteq s₂.keys
参数：h : s₁.entries subseteq s₂.entries。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AList.lookup_isSome`：lookup_isSome {a : α} {s : AList β} : (s.lookup a).
isSome ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AList.mem_lookup_iff`：mem_lookup_iff {a : α} {b : β a} {s : AList β} : b
 in lookup a s ↔ Sigma.mk a b in s.entries
· 使用定理 `Option.get_mem`：∀ {α : Type u_1} {o : Option α} (h : o.isSome = true), o
.get h ∈ o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AList.mem_keys`：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `Option.isSome_some`：∀ {α : Type u_1} {a : α}, (some a).isSome = true
-/
theorem keys_subset_keys_of_entries_subset_entries
    {s₁ s₂ : AList β} (h : s₁.entries ⊆ s₂.entries) : s₁.keys ⊆ s₂.keys := by
  intro k hk
  let : DecidableEq α := Classical.decEq α
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  rw [← mem_lookup_iff, Option.mem_def] at this
  rw [← mem_keys, ← lookup_isSome, this]
  exact Option.isSome_some

/-! ### replace -/

section
variable [DecidableEq α]

/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
/-
**AList.replace** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：replace (a : α) (b : β a) (s : AList β) : AList β
参数：a : α；b : β a；s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace a key with a given value in an association list.
  If the key is not present it does nothing.
-/
def replace (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩

@[simp]
/-
**AList.keys_replace** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.ke
ys
参数：a : α；b : β a；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.keys_kreplace`：keys_kreplace (a : α) (b : β a) : forall l : List (S
igma β), (kreplace a b l).keys = l.keys
-/
theorem keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _

@[simp]
/-
**AList.mem_replace** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_replace {a a' : α} {b : β a} {s : AList β} : a' in replace a b s ↔ a' 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.mem_keys`：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
· 使用定理 `AList.keys_replace`：keys_replace (a : α) (b : β a) (s : AList β) : (repl
ace a b s).keys = s.keys
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_replace {a a' : α} {b : β a} {s : AList β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]
/-
**AList.perm_replace** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} : s₁.entries ~ s₂.entries
 -> (replace a b s₁).entries ~ (replace a b s₂).entries
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kreplace`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq 
α] {a : α} {b : β a} {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (Li
st.krepl…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.nodupKeys

end

/-- Fold a function over the key-value pairs in the map. -/
/-
**AList.foldl** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：foldl {δ : Type w} (f : δ -> forall a, β a -> δ) (d : δ) (m : AList β) : δ
参数：f : δ -> forall a, β a -> δ；d : δ；m : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fold a function over the key-value pairs in the map.
-/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d

/-! ### erase -/


section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
/-
**AList.erase** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：erase (a : α) (s : AList β) : AList β
参数：a : α；s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Erase a key from the map. If the key is not present, do nothing.
-/
def erase (a : α) (s : AList β) : AList β :=
  ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩

@[simp]
/-
**AList.keys_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a
参数：a : α；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.keys_kerase`：keys_kerase {a} {l : List (Sigma β)} : (kerase a l).ke
ys = l.keys.erase a
-/
theorem keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase

@[simp]
/-
**AList.mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_erase {a a' : α} {s : AList β} : a' in erase a s ↔ a' != a ∧ a' in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.mem_keys`：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
· 使用定理 `AList.keys_erase`：keys_erase (a : α) (s : AList β) : (erase a s).keys = 
s.keys.erase a
· 使用定理 `List.Nodup.mem_erase_iff`：∀ {α : Type u_1} [inst : BEq α] {l : List α} {
b : α} [LawfulBEq α] {a : α}, l.Nodup → (a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `AList.keys_nodup`：keys_nodup (s : AList β) : s.keys.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_erase {a a' : α} {s : AList β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]
/-
**AList.perm_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：perm_erase {a : α} {s₁ s₂ : AList β} : s₁.entries ~ s₂.entries -> (erase a
 s₁).entries ~ (erase a s₂).entries
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kerase`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α]
 {a : α} {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (List.kerase a 
l₁).Pe…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem perm_erase {a : α} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.nodupKeys

@[simp]
/-
**AList.lookup_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_erase (a) (s : AList β) : lookup a (erase a s) = none
参数：a；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_kerase`：dlookup_kerase (a) {l : List (Sigma β)} (nd : l.Nod
upKeys) : dlookup a (kerase a l) = none
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem lookup_erase (a) (s : AList β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.nodupKeys

@[simp]
/-
**AList.lookup_erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_erase_ne {a a'} {s : AList β} (h : a != a') : lookup a (erase a' s)
 = lookup a s
参数：h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_kerase_ne`：dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h
 : a != a') : dlookup a (kerase a' l) = dlookup a l
-/
theorem lookup_erase_ne {a a'} {s : AList β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h
/-
**AList.erase_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a')
.erase a
参数：a a' : α；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `List.kerase_kerase`：kerase_kerase {a a'} {l : List (Sigma β)} : (kerase 
a' l).kerase a = (kerase a l).kerase a'
-/
theorem erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase

/-! ### insert -/


/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
/-
**AList.insert** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：insert (a : α) (b : β a) (s : AList β) : AList β
参数：a : α；b : β a；s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert a key-value pair into an association list and erase any existing pair
  with the same key.
-/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩

@[simp]
/-
**AList.entries_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：entries_insert {a} {b : β a} {s : AList β} : (insert a b s).entries = Sigm
a.mk a b :: kerase a s.entries
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem entries_insert {a} {b : β a} {s : AList β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl
/-
**AList.entries_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：entries_insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) : (insert
 a b s).entries = ⟨a, b⟩ :: s.entries
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.entries_insert`：entries_insert {a} {b : β a} {s : AList β} : (inse
rt a b s).entries = Sigma.mk a b :: kerase a s.entries
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
-/
theorem entries_insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [entries_insert, kerase_of_notMem_keys h]
/-
**AList.insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) : insert a b s = 
⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodupKeys_cons`：nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
 NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `AList.entries_insert_of_notMem`：entries_insert_of_notMem {a} {b : β a} {
s : AList β} (h : a ∉ s) : (insert a b s).entries = ⟨a, b⟩ :: s.entries
-/
theorem insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩ :=
  ext <| entries_insert_of_notMem h

@[simp]
/-
**AList.insert_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_empty (a) (b : β a) : insert a b ∅ = singleton a b
参数：a；b : β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl

@[simp]
/-
**AList.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_insert {a a'} {b' : β a'} (s : AList β) : a in insert a' b' s ↔ a = a'
 ∨ a in s
参数：s : AList β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_keys_kinsert`：mem_keys_kinsert {a a'} {b' : β a'} {l : List (Si
gma β)} : a in (kinsert a' b' l).keys ↔ a = a' ∨ a in l.keys
-/
theorem mem_insert {a a'} {b' : β a'} (s : AList β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert

@[simp]
/-
**AList.keys_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.key
s.erase a
参数：s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.keys_kerase`：keys_kerase {a} {l : List (Sigma β)} : (kerase a l).ke
ys = l.keys.erase a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]
/-
**AList.perm_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) 
: (insert a b s₁).entries ~ (insert a b s₂).entries
参数：p : s₁.entries ~ s₂.entries。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kinsert`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α
] {a : α} {b : β a} {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (Lis
t.kinse…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [entries_insert]; exact p.kinsert s₁.nodupKeys

@[simp]
/-
**AList.lookup_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some
 b
参数：s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup_kinsert`：dlookup_kinsert {a} {b : β a} (l : List (Sigma β))
 : dlookup a (kinsert a b l) = some b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, dlookup_kinsert]

@[simp]
/-
**AList.lookup_insert_ne** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a != a') : lookup a
 (insert a' b' s) = lookup a s
参数：h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_kinsert_ne`：dlookup_kinsert_ne {a a'} {b' : β a'} {l : List
 (Sigma β)} (h : a != a') : dlookup a (kinsert a' b' l) = dlookup a l
-/
theorem lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a ≠ a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h
/-
**AList.lookup_insert_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {l : AList β} {k k'
 : α} {v : β k},   AList.lookup k' (AList.insert k v l) = none ↔ k' ≠ k ∧ AList.
lookup k' l = none
参数：AList.insert k v l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AList.lookup_insert`：lookup_insert {a} {b : β a} (s : AList β) : lookup 
a (insert a b s) = some b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AList.lookup_insert_ne`：lookup_insert_ne {a a'} {b' : β a'} {s : AList β
} (h : a != a') : lookup a (insert a' b' s) = lookup a s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] theorem lookup_insert_eq_none {l : AList β} {k k' : α} {v : β k} :
    (l.insert k v).lookup k' = none ↔ (k' ≠ k) ∧ l.lookup k' = none := by
  by_cases h : k' = k
  · subst h; simp
  · simp_all [lookup_insert_ne h]

@[simp]
/-
**AList.lookup_to_alist** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAList = s.dlookup 
a
参数：s : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodupKeys_dedupKeys`：nodupKeys_dedupKeys (l : List (Sigma β)) : Nod
upKeys (dedupKeys l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toAList.eq_1`：∀ {α : Type u} [inst : DecidableEq α] {β : α → Type v
} (l : List (Sigma β)),   l.toAList = { entries := l.dedupKeys, nodupKeys := ⋯ }
· 使用定理 `AList.lookup.eq_1`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α
] (a : α) (s : AList β),   AList.lookup a s = List.dlookup a s.entries
· 使用定理 `List.dlookup_dedupKeys`：dlookup_dedupKeys (a : α) (l : List (Sigma β)) :
 dlookup a (dedupKeys l) = dlookup a l
-/
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAList = s.dlookup a := by
  rw [List.toAList, lookup, dlookup_dedupKeys]

@[simp]
/-
**AList.insert_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_insert {a} {b b' : β a} (s : AList β) : (s.insert a b).insert a b' 
= s.insert a b'
参数：s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_insert {a} {b b' : β a} (s : AList β) :
    (s.insert a b).insert a b' = s.insert a b' := by
  ext : 1; simp only [AList.entries_insert, List.kerase_cons_eq]
/-
**AList.insert_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a != a
') : ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entri
es
参数：s : AList β；h : a != a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `List.kerase_comm`：kerase_comm (a₁ a₂) (l : List (Sigma β)) : kerase a₂ (
kerase a₁ l) = kerase a₁ (kerase a₂ l)
-/
theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [entries_insert]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply Perm.swap; exact h; exact h.symm]

@[simp]
/-
**AList.insert_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = s
ingleton a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [AList.entries_insert, List.kerase_cons_eq, AList.singleton_entries]

@[simp]
/-
**AList.entries_toAList** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupK
eys xs
参数：xs : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupKeys xs :=
  rfl
/-
**AList.toAList_cons** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) : List.toAList (⟨a, b
⟩ :: xs) = insert a b xs.toAList
参数：a : α；b : β a；xs : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAList (⟨a, b⟩ :: xs) = insert a b xs.toAList :=
  rfl
/-
**AList.mk_cons_eq_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKe
ys) : (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h
⟩
参数：c : Sigma β；l : List (Sigma β)；h : (c :: l).NodupKeys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodupKeys_of_nodupKeys_cons`：nodupKeys_of_nodupKeys_cons {s : Sigma
 β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) : NodupKeys l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `AList.mk.congr_simp`：∀ {α : Type u} {β : α → Type v} (entries entries_1 
: List (Sigma β)) (e_entries : entries = entries_1)   (nodupKeys : entries.Nodup
Keys),   …
· 使用定理 `AList.mk.injEq`：∀ {α : Type u} {β : α → Type v} (entries : List (Sigma β
)) (nodupKeys : entries.NodupKeys) (entries_1 : List (Sigma β))   (nodupKeys_1 :
 ent…
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
· 使用定理 `List.notMem_keys_of_nodupKeys_cons`：notMem_keys_of_nodupKeys_cons {s : S
igma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) : s.1 ∉ l.keys
-/
theorem mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys) :
    (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h⟩ := by
  simpa [insert] using (kerase_of_notMem_keys <| notMem_keys_of_nodupKeys_cons h).symm

/-- Recursion on an `AList`, using `insert`. Use as `induction l`. -/
@[elab_as_elim, induction_eliminator]
/-
**AList.insertRec** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：insertRec {C : AList β -> Sort*} (H0 : C ∅) (IH : forall (a : α) (b : β a)
 (l : AList β), a ∉ l -> C l -> C (l.insert a b)) : forall l : AList β, C l | ⟨[
], _⟩ => H0 | ⟨c :: l, h⟩ => by rw [mk_cons_eq_insert] refine IH _ _ _ ?_ (inser
tRec H0 IH _) exact notMem_keys_of_nodupKeys_cons h  -- Test that the `induction
` tactic works on `insertRec`. example (l : AList β) : True
参数：H0 : C ∅；IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.in
sert a b)。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodupKeys_of_nodupKeys_cons`：nodupKeys_of_nodupKeys_cons {s : Sigma
 β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) : NodupKeys l

--- 原说明 ---
Recursion on an `AList`, using `insert`. Use as `induction l`.
-/
def insertRec {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    ∀ l : AList β, C l
  | ⟨[], _⟩ => H0
  | ⟨c :: l, h⟩ => by
    rw [mk_cons_eq_insert]
    refine IH _ _ _ ?_ (insertRec H0 IH _)
    exact notMem_keys_of_nodupKeys_cons h

-- Test that the `induction` tactic works on `insertRec`.
/-
**AList.** 是 Mathlib 中的一个示例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (l : AList β) : True := by induction l <;> trivial

@[simp]
/-
**AList.insertRec_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insertRec_empty {C : AList β -> Sort*} (H0 : C ∅) (IH : forall (a : α) (b 
: β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) : @insertRec α β _ C H0 
IH ∅ = H0
参数：H0 : C ∅；IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.in
sert a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodupKeys_nil`：nodupKeys_nil : @NodupKeys α β []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.insertRec.eq_1`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] {C : AList β → Sort u_1} (H0 : C ∅)   (IH : (a : α) → (b : β a) → (l : ALis
t β) → a ∉…
-/
theorem insertRec_empty {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    @insertRec α β _ C H0 IH ∅ = H0 := by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insertRec]
/-
**AList.insertRec_insert** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insertRec_insert {C : AList β -> Sort*} (H0 : C ∅) (IH : forall (a : α) (b
 : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) {c : Sigma β} {l : ALis
t β} (h : c.1 ∉ l) : @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l 
h (@insertRec α β _ C H0 IH l)
参数：H0 : C ∅；IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.in
sert a b)；h : c.1 ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodupKeys_cons`：nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
 NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l
· 使用定理 `List.nodupKeys_of_nodupKeys_cons`：nodupKeys_of_nodupKeys_cons {s : Sigma
 β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) : NodupKeys l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.insertRec.eq_2`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] {C : AList β → Sort u_1} (H0 : C ∅)   (IH : (a : α) → (b : β a) → (l : ALis
t β) → a ∉…
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `AList.insert_of_notMem`：insert_of_notMem {a} {b : β a} {s : AList β} (h 
: a ∉ s) : insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩
-/
theorem insertRec_insert {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {c : Sigma β}
    {l : AList β} (h : c.1 ∉ l) :
    @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l h (@insertRec α β _ C H0 IH l) := by
  obtain ⟨l, hl⟩ := l
  suffices @insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩ ≍
      IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩) by
    cases c
    apply eq_of_heq
    convert! this <;> rw [insert_of_notMem h]
  rw [insertRec]
  apply cast_heq
/-
**AList.insertRec_insert_mk** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insertRec_insert_mk {C : AList β -> Sort*} (H0 : C ∅) (IH : forall (a : α)
 (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b)) {a : α} (b : β a) {l
 : AList β} (h : a ∉ l) : @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (
@insertRec α β _ C H0 IH l)
参数：H0 : C ∅；IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.in
sert a b)；b : β a；h : a ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.insertRec_insert`：insertRec_insert {C : AList β -> Sort*} (H0 : C 
∅) (IH : forall (a : α) (b : β a) (l : AList β), a ∉ l -> C l -> C (l.insert a b
)) {c : Sigm…
-/
theorem insertRec_insert_mk {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {a : α} (b : β a)
    {l : AList β} (h : a ∉ l) :
    @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (@insertRec α β _ C H0 IH l) :=
  @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h

/-! ### extract -/


/-- Erase a key from the map, and return the corresponding value, if found. -/
/-
**AList.extract** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：extract (a : α) (s : AList β) : Option (β a) × AList β
参数：a : α；s : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Erase a key from the map, and return the corresponding value, if found.
-/
def extract (a : α) (s : AList β) : Option (β a) × AList β :=
  have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]
/-
**AList.extract_eq_lookup_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s,
 erase a s)
参数：a : α；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kextract_eq_dlookup_kerase`：∀ {α : Type u} {β : α → Type v} [inst :
 DecidableEq α] (a : α) (l : List (Sigma β)),   List.kextract a l = (List.dlooku
p a l, List.kerase a …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AList.mk.congr_simp`：∀ {α : Type u} {β : α → Type v} (entries entries_1 
: List (Sigma β)) (e_entries : entries = entries_1)   (nodupKeys : entries.Nodup
Keys),   …
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s, erase a s) := by
  simp [extract]; constructor <;> rfl

/-! ### union -/


/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
/-
**AList.union** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：union (s₁ s₂ : AList β) : AList β
参数：s₁ s₂ : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : AList β) : AList β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩
/-
**AList.** 是 Mathlib 中的一个实例，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Union (AList β) :=
  ⟨union⟩

@[simp]
/-
**AList.union_entries** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：union_entries {s₁ s₂ : AList β} : (s₁ union s₂).entries = kunion s₁.entrie
s s₂.entries
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_entries {s₁ s₂ : AList β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl

@[simp]
/-
**AList.empty_union** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：empty_union {s : AList β} : (∅ : AList β) union s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
-/
theorem empty_union {s : AList β} : (∅ : AList β) ∪ s = s :=
  ext rfl

@[simp]
/-
**AList.union_empty** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：union_empty {s : AList β} : s union (∅ : AList β) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kunion_nil`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] 
{l : List (Sigma β)}, l.kunion [] = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_empty {s : AList β} : s ∪ (∅ : AList β) = s :=
  ext <| by simp

@[simp]
/-
**AList.mem_union** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_union {a} {s₁ s₂ : AList β} : a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_keys_kunion`：mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} : a i
n (kunion l₁ l₂).keys ↔ a in l₁.keys ∨ a in l₂.keys
-/
theorem mem_union {a} {s₁ s₂ : AList β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion
/-
**AList.perm_union** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries) (p₃₄ : 
s₃.entries ~ s₄.entries) : (s₁ union s₃).entries ~ (s₂ union s₄).entries
参数：p₁₂ : s₁.entries ~ s₂.entries；p₃₄ : s₃.entries ~ s₄.entries。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kunion`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α]
 {l₁ l₂ l₃ l₄ : List (Sigma β)},   l₃.NodupKeys → l₁.Perm l₂ → l₃.Perm l₄ → (l₁.
kunion…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]
/-
**AList.union_erase** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ union s₂) = erase a s₁
 union erase a s₂
参数：a : α；s₁ s₂ : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.kunion_kerase`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq 
α] {a : α} {l₁ l₂ : List (Sigma β)},   (List.kerase a l₁).kunion (List.kerase a 
l₂) = Li…
-/
theorem union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm

@[simp]
/-
**AList.lookup_union_left** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_union_left {a} {s₁ s₂ : AList β} : a in s₁ -> lookup a (s₁ union s₂
) = lookup a s₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_kunion_left`：dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β
)} (h : a in l₁.keys) : dlookup a (kunion l₁ l₂) = dlookup a l₁
-/
theorem lookup_union_left {a} {s₁ s₂ : AList β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  dlookup_kunion_left

@[simp]
/-
**AList.lookup_union_right** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ -> lookup a (s₁ union s₂
) = lookup a s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dlookup_kunion_right`：dlookup_kunion_right {a} {l₁ l₂ : List (Sigma
 β)} (h : a ∉ l₁.keys) : dlookup a (kunion l₁ l₂) = dlookup a l₂
-/
theorem lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  dlookup_kunion_right

-- The corresponding lemma in `simp`-normal form is `lookup_union_eq_some`.
/-
**AList.mem_lookup_union** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} : b in lookup a (s₁ union
 s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_kunion`：mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List 
(Sigma β)} : b in dlookup a (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b
 in dlookup a…
-/
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_dlookup_kunion

@[simp]
/-
**AList.lookup_union_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookup_union_eq_some {a} {b : β a} {s₁ s₂ : AList β} : lookup a (s₁ union 
s₂) = some b ↔ lookup a s₁ = some b ∨ a ∉ s₁ ∧ lookup a s₂ = some b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_kunion`：mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List 
(Sigma β)} : b in dlookup a (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b
 in dlookup a…
-/
theorem lookup_union_eq_some {a} {b : β a} {s₁ s₂ : AList β} :
    lookup a (s₁ ∪ s₂) = some b ↔ lookup a s₁ = some b ∨ a ∉ s₁ ∧ lookup a s₂ = some b :=
  mem_dlookup_kunion
/-
**AList.mem_lookup_union_middle** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} : b in lookup a
 (s₁ union s₃) -> a ∉ s₂ -> b in lookup a (s₁ union s₂ union s₃)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_kunion_middle`：mem_dlookup_kunion_middle {a} {b : β a} 
{l₁ l₂ l₃ : List (Sigma β)} (h₁ : b in dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys 
l₂) : b in dlookup a…
-/
theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_dlookup_kunion_middle
/-
**AList.insert_union** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_union {a} {b : β a} {s₁ s₂ : AList β} : insert a b (s₁ union s₂) = 
insert a b s₁ union s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AList.ext`：∀ {α : Type u} {β : α → Type v} {s t : AList β}, s.entries = 
t.entries → s = t
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.kunion_kerase`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq 
α] {a : α} {l₁ l₂ : List (Sigma β)},   (List.kerase a l₁).kunion (List.kerase a 
l₂) = Li…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insert_union {a} {b : β a} {s₁ s₂ : AList β} :
    insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ := by ext; simp
/-
**AList.union_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：union_assoc {s₁ s₂ s₃ : AList β} : (s₁ union s₂ union s₃).entries ~ (s₁ un
ion (s₂ union s₃)).entries
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.lookup_ext`：lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys
) (nd₁ : l₁.NodupKeys) (h : forall x y, y in l₀.dlookup x ↔ y in l₁.dlookup x) :
 l₀ ~…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem union_assoc {s₁ s₂ s₃ : AList β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])

end

/-! ### disjoint -/


/-- Two associative lists are disjoint if they have no common keys. -/
/-
**AList.Disjoint** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：Disjoint (s₁ s₂ : AList β) : Prop
参数：s₁ s₂ : AList β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two associative lists are disjoint if they have no common keys.
-/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  ∀ k ∈ s₁.keys, k ∉ s₂.keys

variable [DecidableEq α]
/-
**AList.union_comm_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) : (s₁ union 
s₂).entries ~ (s₂ union s₁).entries
参数：h : Disjoint s₁ s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.lookup_ext`：lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys
) (nd₁ : l₁.NodupKeys) (h : forall x y, y in l₀.dlookup x ↔ y in l₁.dlookup x) :
 l₀ ~…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AList.keys.eq_1`：∀ {α : Type u} {β : α → Type v} (s : AList β), s.keys =
 s.entries.keys
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dlookup_isSome`：dlookup_isSome {a : α} {l : List (Sigma β)} : (dloo
kup a l).isSome ↔ a in l.keys
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp only [union_entries, Option.mem_def, dlookup_kunion_eq_some]
      constructor <;> intro h'
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          apply h
          rw [keys, ← List.dlookup_isSome, h']
          exact rfl
        · left
          rw [h'.2]
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          intro h''
          apply h _ h''
          rw [keys, ← List.dlookup_isSome, h']
          exact rfl
        · left
          rw [h'.2])

end AList

