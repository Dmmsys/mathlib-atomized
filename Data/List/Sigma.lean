/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Lookmap
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `List (Sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : Sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `List (Sigma β)` behaves like a key-value store.

## Main Definitions

- `List.keys` extracts the list of keys.
- `List.NodupKeys` determines if the store has duplicate keys.
- `List.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `List.kreplace` replaces the first value with a given key by a given value.
- `List.kerase` removes a value.
- `List.kinsert` inserts a value.
- `List.kunion` computes the union of two stores.
- `List.kextract` returns a value with a given key and the rest of the values.
-/

@[expose] public section

universe u u' v v'

namespace List

variable {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/


/-- List of keys from a list of key-value pairs -/
/-
**List.keys** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：keys : List (Sigma β) -> List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of keys from a list of key-value pairs
-/
def keys : List (Sigma β) → List α :=
  map Sigma.fst

@[simp, grind =]
/-
**List.keys_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：keys_nil : @keys α β [] = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_nil : @keys α β [] = [] :=
  rfl

@[simp, grind =]
/-
**List.keys_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl

@[simp, grind =]
/-
**List.keys_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：keys_append : (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem keys_append : (l₁ ++ l₂).keys = l₁.keys ++ l₂.keys := by
  simp [keys]
/-
**List.mem_keys_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s in l -> s.1 in l.ke
ys
参数：Sigma β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
-/
theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s ∈ l → s.1 ∈ l.keys :=
  mem_map_of_mem
/-
**List.exists_of_mem_keys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_of_mem_keys {a} {l : List (Sigma β)} (h : a in l.keys) : exists b :
 β a, Sigma.mk a b in l
参数：Sigma β；h : a in l.keys。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_of_mem_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} 
{l : List α} {b : α_1}, b ∈ List.map f l → ∃ a ∈ l, f a = b
-/
theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ b : β a, Sigma.mk a b ∈ l := by
  have := exists_of_mem_map h
  grind

@[grind =]
/-
**List.mem_keys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys {a} {l : List (Sigma β)} : a in l.keys ↔ exists b : β a, Sigma.mk
 a b in l
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_of_mem_keys`：exists_of_mem_keys {a} {l : List (Sigma β)} (h 
: a in l.keys) : exists b : β a, Sigma.mk a b in l
· 使用定理 `List.mem_keys_of_mem`：mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)}
 : s in l -> s.1 in l.keys
-/
theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨_, h⟩ => mem_keys_of_mem h⟩
/-
**List.notMem_keys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：notMem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ forall b : β a, Sigma.
mk a b ∉ l
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l := by
  grind
/-
**List.ne_key** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ne_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ forall s : Sigma β, s in l 
-> a != s.1
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ne_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 := by
  grind

/-! ### `NodupKeys` -/


/-- Determines whether the store uses a key several times. -/
@[grind]
/-
**List.NodupKeys** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：NodupKeys (l : List (Sigma β)) : Prop
参数：l : List (Sigma β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determines whether the store uses a key several times.
-/
def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup
/-
**List.nodupKeys_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_iff_pairwise {l} : NodupKeys l ↔ Pairwise (fun s s' : Sigma β =>
 s.1 != s'.1) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
-/
theorem nodupKeys_iff_pairwise {l} : NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map
/-
**List.NodupKeys.pairwise_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l : List (Sigma β)}, l.NodupKeys → List.P
airwise (fun s s' => s.fst ≠ s'.fst) l
参数：Sigma β；fun s s' => s.fst ≠ s'.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodupKeys_iff_pairwise`：nodupKeys_iff_pairwise {l} : NodupKeys l ↔ 
Pairwise (fun s s' : Sigma β => s.1 != s'.1) l
-/
theorem NodupKeys.pairwise_ne {l} (h : NodupKeys l) :
    Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupKeys_iff_pairwise.1 h

@[simp]
/-
**List.nodupKeys_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_nil : @NodupKeys α β []
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodupKeys_nil : @NodupKeys α β [] :=
  Pairwise.nil

@[simp]
/-
**List.nodupKeys_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} : NodupKeys (s :: l) ↔ s
.1 ∉ l.keys ∧ NodupKeys l
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
    NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l := by simp [keys, NodupKeys]
/-
**List.nodupKeys_middle** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_middle {s : Sigma β} : (l₁ ++ s :: l₂).NodupKeys ↔ (s :: (l₁ ++ 
l₂)).NodupKeys
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodupKeys_middle {s : Sigma β} :
    (l₁ ++ s :: l₂).NodupKeys ↔ (s :: (l₁ ++ l₂)).NodupKeys := by
  simp_all [NodupKeys, keys, nodup_middle]
/-
**List.notMem_keys_of_nodupKeys_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：notMem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : Nodu
pKeys (s :: l)) : s.1 ∉ l.keys
参数：Sigma β；h : NodupKeys (s :: l)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    s.1 ∉ l.keys := by grind
/-
**List.nodupKeys_of_nodupKeys_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupK
eys (s :: l)) : NodupKeys l
参数：Sigma β；h : NodupKeys (s :: l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodupKeys_cons`：nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
 NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l
-/
theorem nodupKeys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    NodupKeys l :=
  (nodupKeys_cons.1 h).2
/-
**List.NodupKeys.eq_of_fst_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l : List (Sigma β)},   l.NodupKeys → ∀ {s
 s' : Sigma β}, s ∈ l → s' ∈ l → s.fst = s'.fst → s = s'
参数：Sigma β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.forall_of_forall`：∀ {α : Type u_1} {R : α → α → Prop} {l :
 List α} [Std.Symm R],   (∀ x ∈ l, R x x) → List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l
 → ∀ ⦃y : α⦄, y ∈ l …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodupKeys_iff_pairwise`：nodupKeys_iff_pairwise {l} : NodupKeys l ↔ 
Pairwise (fun s s' : Sigma β => s.1 != s'.1) l
-/
theorem NodupKeys.eq_of_fst_eq {l : List (Sigma β)} (nd : NodupKeys l) {s s' : Sigma β} (h : s ∈ l)
    (h' : s' ∈ l) : s.1 = s'.1 → s = s' :=
  @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') _
    ⟨fun _ _ H h => (H h.symm).symm⟩ (fun _ _ _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun h h' => (h h').elim) _ h _ h'
/-
**List.NodupKeys.eq_of_mk_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {a : α} {b b' : β a} {l : List (Sigma β)},
   l.NodupKeys → ⟨a, b⟩ ∈ l → ⟨a, b'⟩ ∈ l → b = b'
参数：Sigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NodupKeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) (h' : Sigma.mk a b' ∈ l) : b = b' := by
  grind [NodupKeys.eq_of_fst_eq]
/-
**List.nodupKeys_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_singleton (s : Sigma β) : NodupKeys [s]
参数：s : Sigma β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_singleton`：nodup_singleton (a : α) : Nodup [a]
-/
theorem nodupKeys_singleton (s : Sigma β) : NodupKeys [s] :=
  nodup_singleton _
/-
**List.NodupKeys.sublist** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l₁ l₂ : List (Sigma β)}, l₁.Sublist l₂ → 
l₂.NodupKeys → l₁.NodupKeys
参数：Sigma β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
theorem NodupKeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : NodupKeys l₂ → NodupKeys l₁ :=
  Nodup.sublist <| h.map _

@[grind →]
/-
**List.NodupKeys.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l : List (Sigma β)}, l.NodupKeys → l.Nodu
p
参数：Sigma β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
-/
protected theorem NodupKeys.nodup {l : List (Sigma β)} : NodupKeys l → Nodup l :=
  Nodup.of_map _
/-
**List.perm_nodupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : NodupKeys l₁ ↔ Nod
upKeys l₂
参数：Sigma β；h : l₁ ~ l₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : NodupKeys l₁ ↔ NodupKeys l₂ :=
  (h.map _).nodup_iff
/-
**List.nodupKeys_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_flatten {L : List (List (Sigma β))} : NodupKeys (flatten L) ↔ (f
orall l in L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys)
参数：List (Sigma β)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nodupKeys_iff_pairwise`：nodupKeys_iff_pairwise {l} : NodupKeys l ↔ 
Pairwise (fun s s' : Sigma β => s.1 != s'.1) l
· 使用定理 `List.pairwise_flatten`：∀ {α : Type u_1} {R : α → α → Prop} {L : List (Li
st α)},   List.Pairwise R L.flatten ↔ (∀ l ∈ L, List.Pairwise R l) ∧ List.Pairwi
se (fun l₁ …
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem nodupKeys_flatten {L : List (List (Sigma β))} :
    NodupKeys (flatten L) ↔ (∀ l ∈ L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys) := by
  rw [nodupKeys_iff_pairwise, pairwise_flatten, pairwise_map]
  refine and_congr (forall₂_congr fun l _ => by simp [nodupKeys_iff_pairwise]) ?_
  simp [keys, disjoint_iff_ne, Sigma.forall]
/-
**List.nodup_zipIdx_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_zipIdx_map_snd (l : List α) : (l.zipIdx.map Prod.snd).Nodup
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipIdx_map_snd`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.map Pro
d.snd (l.zipIdx i) = List.range' i l.length
-/
theorem nodup_zipIdx_map_snd (l : List α) : (l.zipIdx.map Prod.snd).Nodup := by
  simp [List.nodup_range']
/-
**List.mem_ext** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup) (h : fo
rall x, x in l₀ ↔ x in l₁) : l₀ ~ l₁
参数：Sigma β；nd₀ : l₀.Nodup；nd₁ : l₁.Nodup；h : forall x, x in l₀ ↔ x in l₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
    (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ := by grind [perm_ext_iff_of_nodup]

variable [DecidableEq α] [DecidableEq α']

/-! ### `dlookup` -/

/-- `dlookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
/-
**List.dlookup** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → {β : α → Type v} → [DecidableEq α] → (a : α) → List (Sigma 
β) → Option (β a)
参数：a : α；Sigma β；β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dlookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists.
-/
def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l

@[simp, grind =]
/-
**List.dlookup_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_nil (a : α) : dlookup a [] = @none (β a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dlookup_nil (a : α) : dlookup a [] = @none (β a) :=
  rfl

@[simp, grind =]
/-
**List.dlookup_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b
参数：l；a : α；b : β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl

@[simp, grind =]
/-
**List.dlookup_cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (l : List (Sigma β)
) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s :: l) = List.dlookup a 
l
参数：l : List (Sigma β)；s : Sigma β；s :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem dlookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → dlookup a (s :: l) = dlookup a l
  | ⟨_, _⟩, h => dif_neg h.symm

@[grind =]
/-
**List.dlookup_isSome** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_isSome {a : α} {l : List (Sigma β)} : (dlookup a l).isSome ↔ a in 
l.keys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dlookup_isSome {a : α} {l : List (Sigma β)} : (dlookup a l).isSome ↔ a ∈ l.keys := by
  induction l with
  | nil => simp
  | cons s _ _ => by_cases a = s.fst <;> grind
/-
**List.dlookup_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.
keys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.keys := by
  simp [← dlookup_isSome, Option.isNone_iff_eq_none]
/-
**List.of_mem_dlookup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β)} : b in dlookup a l -
> Sigma.mk a b in l
参数：Sigma β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β)} :
    b ∈ dlookup a l → Sigma.mk a b ∈ l := by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases a = s.fst <;> grind
/-
**List.mem_dlookup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sig
ma.mk a b in l) : b in dlookup a l
参数：Sigma β；nd : l.NodupKeys；h : Sigma.mk a b in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.isSome_iff_exists`：∀ {α : Type u_1} {x : Option α}, x.isSome = tr
ue ↔ ∃ a, x = some a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dlookup_isSome`：dlookup_isSome {a : α} {l : List (Sigma β)} : (dloo
kup a l).isSome ↔ a in l.keys
· 使用定理 `List.mem_keys_of_mem`：mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)}
 : s in l -> s.1 in l.keys
· 使用定理 `List.NodupKeys.eq_of_mk_mem`：∀ {α : Type u} {β : α → Type v} {a : α} {b 
b' : β a} {l : List (Sigma β)},   l.NodupKeys → ⟨a, b⟩ ∈ l → ⟨a, b'⟩ ∈ l → b = b
'
· 使用定理 `List.of_mem_dlookup`：of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β
)} : b in dlookup a l -> Sigma.mk a b in l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sigma.mk a b ∈ l) :
    b ∈ dlookup a l := by
  obtain ⟨b', h'⟩ := Option.isSome_iff_exists.mp (dlookup_isSome.mpr (mem_keys_of_mem h))
  cases nd.eq_of_mk_mem h (of_mem_dlookup h')
  exact h'
/-
**List.map_dlookup_eq_find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_dlookup_eq_find (a : α) (l : List (Sigma β)) : (dlookup a l).map (Sigm
a.mk a) = find? (fun s => a = s.1) l
参数：a : α；l : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_dlookup_eq_find (a : α) (l : List (Sigma β)) :
    (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l := by
  induction l with
  | nil => grind
  | cons s _ _ => by_cases s.fst = a <;> grind
/-
**List.mem_dlookup_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) 
: b in dlookup a l ↔ Sigma.mk a b in l
参数：Sigma β；nd : l.NodupKeys。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.of_mem_dlookup`：of_mem_dlookup {a : α} {b : β a} {l : List (Sigma β
)} : b in dlookup a l -> Sigma.mk a b in l
· 使用定理 `List.mem_dlookup`：mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l
.NodupKeys) (h : Sigma.mk a b in l) : b in dlookup a l
-/
theorem mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) :
    b ∈ dlookup a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_dlookup, mem_dlookup nd⟩
/-
**List.perm_dlookup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁
 ~ l₂) : dlookup a l₁ = dlookup a l₂
参数：a : α；Sigma β；nd₁ : l₁.NodupKeys；p : l₁ ~ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_nodupKeys`：perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l
₂) : NodupKeys l₁ ↔ NodupKeys l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_dlookup_iff`：mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma
 β)} (nd : l.NodupKeys) : b in dlookup a l ↔ Sigma.mk a b in l
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    dlookup a l₁ = dlookup a l₂ := by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  ext b; simp only [← Option.mem_def, mem_dlookup_iff nd₁, mem_dlookup_iff nd₂, p.mem_iff]
/-
**List.lookup_ext** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKe
ys) (h : forall x y, y in l₀.dlookup x ↔ y in l₁.dlookup x) : l₀ ~ l₁
参数：Sigma β；nd₀ : l₀.NodupKeys；nd₁ : l₁.NodupKeys；h : forall x y, y in l₀.dlookup
 x ↔ y in l₁.dlookup x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
    (h : ∀ x y, y ∈ l₀.dlookup x ↔ y ∈ l₁.dlookup x) : l₀ ~ l₁ := by
  grind [_=_ mem_dlookup_iff, mem_ext]
/-
**List.dlookup_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_map (l : List (Sigma β)) {f : α -> α'} (hf : Function.Injective f)
 (g : forall a, β a -> β' (f a)) (a : α) : (l.map (.map f g)).dlookup (f a) = (l
.dlookup a).map (g a)
参数：l : List (Sigma β)；hf : Function.Injective f；g : forall a, β a -> β' (f a)；a 
: α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dlookup_map (l : List (Sigma β))
    {f : α → α'} (hf : Function.Injective f) (g : ∀ a, β a → β' (f a)) (a : α) :
    (l.map (.map f g)).dlookup (f a) = (l.dlookup a).map (g a) := by
  induction l with
  | nil => grind
  | cons s _ _ =>
    have (h : a ≠ s.fst) : ¬ f a = (⟨f s.fst, g s.fst s.snd⟩ : Sigma β').fst := fun he => h <| hf he
    by_cases a = s.fst <;> grind [Sigma.map]
/-
**List.dlookup_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_map (l : List (Sigma β)) {f : α -> α'} (hf : Function.Injective f)
 (g : forall a, β a -> β' (f a)) (a : α) : (l.map (.map f g)).dlookup (f a) = (l
.dlookup a).map (g a)
参数：l : List (Sigma β)；hf : Function.Injective f；g : forall a, β a -> β' (f a)；a 
: α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dlookup_map₁ {β : Type v} (l : List (Σ _ : α, β))
    {f : α → α'} (hf : Function.Injective f) (a : α) :
    (l.map (.map f fun _ => id) : List (Σ _ : α', β)).dlookup (f a) = l.dlookup a := by
  have := dlookup_map (β' := fun _ => β) (f := f) (g := fun _ => id)
  grind [Option.map_id']
/-
**List.dlookup_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_map (l : List (Sigma β)) {f : α -> α'} (hf : Function.Injective f)
 (g : forall a, β a -> β' (f a)) (a : α) : (l.map (.map f g)).dlookup (f a) = (l
.dlookup a).map (g a)
参数：l : List (Sigma β)；hf : Function.Injective f；g : forall a, β a -> β' (f a)；a 
: α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dlookup_map₂ {γ δ : α → Type*} {l : List (Σ a, γ a)} {f : ∀ a, γ a → δ a} (a : α) :
    (l.map (.map id f) : List (Σ a, δ a)).dlookup a = (l.dlookup a).map (f a) :=
  dlookup_map l Function.injective_id _ _

#adaptation_note /-- Before leanprover/lean4#13166
the grind proof here worked, but after changes to the canonicalizer it now times out.
Changes to grind attributes in Batteries in
https://github.com/leanprover-community/batteries/pull/1744
may allow restoring the original proof:
```
  induction l with
  | nil => grind [nodupKeys_nil]
  | cons hd tl =>
    have := dlookup_map₁ tl hf hd.fst
    grind [dlookup_isSome, → notMem_keys_of_nodupKeys_cons, nodupKeys_of_nodupKeys_cons,
      nodupKeys_cons]
```
-/
omit [DecidableEq α] [DecidableEq α'] in
/-
**List.NodupKeys.map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NodupKeys.map₁ {β : Type v} (f : α → α') (hf : Function.Injective f) {l : List (Σ _ : α, β)}
    (nd : l.NodupKeys) : (l.map (.map f fun _ => id) : List (Σ _ : α', β)).NodupKeys := by
  induction l with
  | nil => exact nodupKeys_nil
  | cons hd tl ih =>
    simp only [map_cons, nodupKeys_cons] at nd ⊢
    exact ⟨mt (fun h => by
      simp only [keys, map_map] at h ⊢
      obtain ⟨x, hm, he⟩ := mem_map.mp h
      exact mem_map.mpr ⟨x, hm, hf he⟩) nd.1, ih nd.2⟩

omit [DecidableEq α] in
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_keys {β β' : α → Type*} (f : (a : α) → β a → β' a) (l : List (Σ a, β a)) :
    (l.map (.map id f)).keys = l.keys := by
  induction l <;> grind [Sigma.map]

omit [DecidableEq α] in
/-
**List.NodupKeys.map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NodupKeys.map₂ {β β' : α → Type*} (f : (a : α) → β a → β' a) (l : List (Σ a, β a))
    (nd : l.NodupKeys) : (l.map (.map id f)).NodupKeys := by
  simp_all [NodupKeys, map₂_keys]

@[simp, grind =]
/-
**List.dlookup_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_append (l₁ l₂ : List (Sigma β)) (a : α) : (l₁ ++ l₂).dlookup a = (
l₁.dlookup a).or (l₂.dlookup a)
参数：l₁ l₂ : List (Sigma β)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dlookup_append (l₁ l₂ : List (Sigma β)) (a : α) :
    (l₁ ++ l₂).dlookup a = (l₁.dlookup a).or (l₂.dlookup a) := by
  induction l₁ with
  | nil => rfl
  | cons s _ _ => by_cases a = s.fst <;> grind
/-
**List.sublist_dlookup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_dlookup {l₁ l₂ : List (Sigma β)} {a : α} {b : β a} (nd₂ : l₂.Nodup
Keys) (s : l₁ <+ l₂) (mem : b in l₁.dlookup a) : b in l₂.dlookup a
参数：Sigma β；nd₂ : l₂.NodupKeys；s : l₁ <+ l₂；mem : b in l₁.dlookup a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublist_dlookup {l₁ l₂ : List (Sigma β)} {a : α} {b : β a}
    (nd₂ : l₂.NodupKeys) (s : l₁ <+ l₂) (mem : b ∈ l₁.dlookup a) : b ∈ l₂.dlookup a := by
  grind [Option.mem_def, => perm_dlookup, → Sublist.exists_perm_append]

/-! ### `lookupAll` -/


/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
/-
**List.lookupAll** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → {β : α → Type v} → [DecidableEq α] → (a : α) → List (Sigma 
β) → List (β a)
参数：a : α；Sigma β；β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lookup_all a l` is the list of all values in `l` corresponding to the key `a`.
-/
def lookupAll (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOn h b :: lookupAll a l else lookupAll a l

@[simp]
/-
**List.lookupAll_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookupAll_nil (a : α) : lookupAll a [] = @nil (β a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookupAll_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl

@[simp]
/-
**List.lookupAll_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookupAll_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b ::
 lookupAll a l
参数：l；a : α；b : β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem lookupAll_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl

@[simp]
/-
**List.lookupAll_cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (l : List (Sigma β)
) {a : α} (s : Sigma β),   a ≠ s.fst → List.lookupAll a (s :: l) = List.lookupAl
l a l
参数：l : List (Sigma β)；s : Sigma β；s :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem lookupAll_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l
  | ⟨_, _⟩, h => dif_neg h.symm
/-
**List.lookupAll_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {l : List (
Sigma β)},   List.lookupAll a l = [] ↔ ∀ (b : β a), ⟨a, b⟩ ∉ l
参数：Sigma β；b : β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookupAll_eq_nil {a : α} :
    ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp only [lookupAll_cons_eq, mem_cons, Sigma.mk.inj_iff, heq_eq_eq, true_and, not_or,
        false_iff, not_forall, not_and, not_not, reduceCtorEq]
      use b
      simp
    · simp [h, lookupAll_eq_nil]
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_lookupAll (a : α) : ∀ l : List (Sigma β), head? (lookupAll a l) = dlookup a l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst h; simp
    · rw [lookupAll_cons_ne, dlookup_cons_ne, head?_lookupAll a l] <;> assumption
/-
**List.mem_lookupAll** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {b : β a} {
l : List (Sigma β)},   b ∈ List.lookupAll a l ↔ ⟨a, b⟩ ∈ l
参数：Sigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_lookupAll {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp [*, mem_lookupAll]
    · simp [*, mem_lookupAll]
/-
**List.lookupAll_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (a : α) (l : List (
Sigma β)),   (List.map (Sigma.mk a) (List.lookupAll a l)).Sublist l
参数：a : α；l : List (Sigma β)；List.map (Sigma.mk a) (List.lookupAll a l)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookupAll_sublist (a : α) : ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp only [lookupAll_cons_eq, List.map]
      exact (lookupAll_sublist a l).cons_cons _
    · simp only [ne_eq, h, not_false_iff, lookupAll_cons_ne]
      exact (lookupAll_sublist a l).cons _
/-
**List.lookupAll_length_le_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookupAll_length_le_one (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : l
ength (lookupAll a l) <= 1
参数：a : α；Sigma β；h : l.NodupKeys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.lookupAll_sublist`：∀ {α : Type u} {β : α → Type v} [inst : Decidabl
eEq α] (a : α) (l : List (Sigma β)),   (List.map (Sigma.mk a) (List.lookupAll a 
l)).Sublist …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nodup_replicate`：∀ {α : Type u_1} {n : ℕ} {a : α}, (List.replicate 
n a).Nodup ↔ n ≤ 1
· 使用定理 `List.map_const`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, Li
st.map (Function.const α b) l = List.replicate l.length b
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem lookupAll_length_le_one (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    length (lookupAll a l) ≤ 1 := by
  have := Nodup.sublist ((lookupAll_sublist a l).map _) h
  rw [map_map] at this
  rwa [← nodup_replicate, ← map_const]
/-
**List.lookupAll_eq_dlookup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookupAll_eq_dlookup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : look
upAll a l = (dlookup a l).toList
参数：a : α；Sigma β；h : l.NodupKeys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head?_lookupAll`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (a : α) (l : List (Sigma β)),   (List.lookupAll a l).head? = List.dlookup a
 l
· 使用定理 `List.lookupAll_length_le_one`：lookupAll_length_le_one (a : α) {l : List 
(Sigma β)} (h : l.NodupKeys) : length (lookupAll a l) <= 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.Simproc.add_le_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b ≤ c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem lookupAll_eq_dlookup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    lookupAll a l = (dlookup a l).toList := by
  rw [← head?_lookupAll]
  have h1 := lookupAll_length_le_one a h; revert h1
  rcases lookupAll a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro h1 <;> try rfl
  exact absurd h1 (by simp)
/-
**List.lookupAll_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookupAll_nodup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : (lookupAl
l a l).Nodup
参数：a : α；Sigma β；h : l.NodupKeys。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.lookupAll_eq_dlookup`：lookupAll_eq_dlookup (a : α) {l : List (Sigma
 β)} (h : l.NodupKeys) : lookupAll a l = (dlookup a l).toList
· 使用定理 `Option.toList_nodup`：∀ {α : Type u} (o : Option α), o.toList.Nodup
-/
theorem lookupAll_nodup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : (lookupAll a l).Nodup := by
  (rw [lookupAll_eq_dlookup a h]; apply Option.toList_nodup)
/-
**List.perm_lookupAll** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_lookupAll (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : 
l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂
参数：a : α；Sigma β；nd₁ : l₁.NodupKeys；p : l₁ ~ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.perm_nodupKeys`：perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l
₂) : NodupKeys l₁ ↔ NodupKeys l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.lookupAll_eq_dlookup`：lookupAll_eq_dlookup (a : α) {l : List (Sigma
 β)} (h : l.NodupKeys) : lookupAll a l = (dlookup a l).toList
· 使用定理 `List.perm_dlookup`：perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : 
l₁.NodupKeys) (p : l₁ ~ l₂) : dlookup a l₁ = dlookup a l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem perm_lookupAll (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys)
    (p : l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂ := by
  have nd₂ := (perm_nodupKeys p).mp nd₁
  simp [lookupAll_eq_dlookup, nd₁, nd₂, perm_dlookup a nd₁ p]

/-! ### `kreplace` -/


/-- Replaces the first value with key `a` by `b`. -/
/-
**List.kreplace** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：kreplace (a : α) (b : β a) : List (Sigma β) -> List (Sigma β)
参数：a : α；b : β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replaces the first value with key `a` by `b`.
-/
def kreplace (a : α) (b : β a) : List (Sigma β) → List (Sigma β) :=
  lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none
/-
**List.kreplace_of_forall_not** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)} (H : forall 
b : β a, Sigma.mk a b ∉ l) : kreplace a b l = l
参数：a : α；b : β a；Sigma β；H : forall b : β a, Sigma.mk a b ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.lookmap_of_forall_not`：lookmap_of_forall_not {l : List α} (H : fora
ll a in l, f a = none) : l.lookmap f = l
-/
theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)}
    (H : ∀ b : β a, Sigma.mk a b ∉ l) : kreplace a b l = l :=
  lookmap_of_forall_not _ <| by
    grind
/-
**List.kreplace_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l) (h
 : Sigma.mk a b in l) : kreplace a b l = l
参数：Sigma β；nd : NodupKeys l；h : Sigma.mk a b in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.lookmap_congr`：lookmap_congr {f g : α -> Option α} : forall {l : Li
st α}, (forall a in l, f a = g a) -> l.lookmap f = l.lookmap g | [], _ => rfl | 
a :: l, …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.NodupKeys.eq_of_mk_mem`：∀ {α : Type u} {β : α → Type v} {a : α} {b 
b' : β a} {l : List (Sigma β)},   l.NodupKeys → ⟨a, b⟩ ∈ l → ⟨a, b'⟩ ∈ l → b = b
'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `List.lookmap_id'`：lookmap_id' (h : forall (a), forall b in f a, a = b) (
l : List α) : l.lookmap f = l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) : kreplace a b l = l := by
  refine (lookmap_congr ?_).trans (lookmap_id' (Option.guard fun (s : Sigma β) => a = s.1) ?_ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      simp [nd.eq_of_mk_mem h h']
    · simp_all
    · simp_all
    · rfl
  · simp
/-
**List.keys_kreplace** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：keys_kreplace (a : α) (b : β a) : forall l : List (Sigma β), (kreplace a b
 l).keys = l.keys
参数：a : α；b : β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.lookmap_map_eq`：∀ {α : Type u_1} {β : Type u_2} (f : α → Option α) 
(g : α → β),   (∀ (a b : α), b ∈ f a → g a = g b) → ∀ (l : List α), List.map g (
List.look…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem keys_kreplace (a : α) (b : β a) : ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys :=
  lookmap_map_eq _ _ <| by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩
    dsimp
    split_ifs with h <;> simp +contextual [h]
/-
**List.kreplace_nodupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kreplace_nodupKeys (a : α) (b : β a) {l : List (Sigma β)} : (kreplace a b 
l).NodupKeys ↔ l.NodupKeys
参数：a : α；b : β a；Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.keys_kreplace`：keys_kreplace (a : α) (b : β a) : forall l : List (S
igma β), (kreplace a b l).keys = l.keys
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem kreplace_nodupKeys (a : α) (b : β a) {l : List (Sigma β)} :
    (kreplace a b l).NodupKeys ↔ l.NodupKeys := by simp [NodupKeys, keys_kreplace]
/-
**List.Perm.kreplace** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {b : β a} {
l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (List.kreplace a b l₁).Pe
rm (List.kreplace a b l₂)
参数：Sigma β；List.kreplace a b l₁；List.kreplace a b l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.perm_lookmap`：perm_lookmap (f : α -> Option α) {l₁ l₂ : List α} (H 
: Pairwise (fun a b => forall c in f a, forall d in f b, a = b ∧ c = d) l₁) (p :
 l₁ ~ l…
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `List.NodupKeys.pairwise_ne`：∀ {α : Type u} {β : α → Type v} {l : List (S
igma β)}, l.NodupKeys → List.Pairwise (fun s s' => s.fst ≠ s'.fst) l
-/
theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ <| by
    refine nd.pairwise_ne.imp ?_
    intro x y h z h₁ w h₂
    split_ifs at h₁ h₂ with h_2 h_1 <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim

/-! ### `kerase` -/


/-- Remove the first pair with the key `a`. -/
/-
**List.kerase** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：kerase (a : α) : List (Sigma β) -> List (Sigma β)
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the first pair with the key `a`.
-/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  eraseP fun s => a = s.1

@[simp]
/-
**List.kerase_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_nil {a} : @kerase _ β _ a [] = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl

@[simp]
/-
**List.kerase_cons_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) : kera
se a (s :: l) = l
参数：Sigma β；h : a = s.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `List.eraseP_cons_of_pos`：∀ {α : Type u_1} {a : α} {l : List α} {p : α → 
Bool}, p a = true → List.eraseP p (a :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
-/
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) :
    kerase a (s :: l) = l := by simp [kerase, h]

@[simp]
/-
**List.kerase_cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a != s.1) : ker
ase a (s :: l) = s :: kerase a l
参数：Sigma β；h : a != s.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.eraseP_cons_of_neg`：∀ {α : Type u_1} {a : α} {l : List α} {p : α → 
Bool}, ¬p a = true → List.eraseP p (a :: l) = a :: List.eraseP p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a ≠ s.1) :
    kerase a (s :: l) = s :: kerase a l := by simp [kerase, h]

@[simp]
/-
**List.kerase_of_notMem_keys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_of_notMem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a
 l = l
参数：Sigma β；h : a ∉ l.keys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kerase_of_notMem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]
/-
**List.kerase_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l
参数：a : α；l : List (Sigma β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eraseP_sublist`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, (List
.eraseP p l).Sublist l
-/
theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  eraseP_sublist
/-
**List.kerase_keys_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys subseteq l
.keys
参数：a；l : List (Sigma β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.kerase_sublist`：kerase_sublist (a : α) (l : List (Sigma β)) : keras
e a l <+ l
-/
theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).subset
/-
**List.mem_keys_of_mem_keys_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} : a₁ in (kerase a
₂ l).keys -> a₁ in l.keys
参数：Sigma β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.kerase_keys_subset`：kerase_keys_subset (a) (l : List (Sigma β)) : (
kerase a l).keys subseteq l.keys
-/
theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} :
    a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _
/-
**List.exists_of_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_of_kerase {a : α} {l : List (Sigma β)} (h : a in l.keys) : exists (
b : β a) (l₁ l₂ : List (Sigma β)), a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase
 a l = l₁ ++ l₂
参数：Sigma β；h : a in l.keys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.not_mem_cons_of_ne_of_not_mem`：∀ {α : Type u_1} {a y : α} {l : List
 α}, a ≠ y → a ∉ l → a ∉ y :: l
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a) (l₁ l₂ : List (Sigma β)),
      a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd; rfl, by simp⟩
    · simp only [keys_cons, mem_cons] at h
      rcases h with h | h
      · exact absurd h e
      rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
      exact ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by (rw [h₂]; rfl), by
            simp [e, h₃]⟩

@[simp]
/-
**List.mem_keys_kerase_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ != a₂) : a₁ in 
(kerase a₂ l).keys ↔ a₁ in l.keys
参数：Sigma β；h : a₁ != a₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_keys_of_mem_keys_kerase`：mem_keys_of_mem_keys_kerase {a₁ a₂} {l
 : List (Sigma β)} : a₁ in (kerase a₂ l).keys -> a₁ in l.keys
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.exists_of_kerase`：exists_of_kerase {a : α} {l : List (Sigma β)} (h 
: a in l.keys) : exists (b : β a) (l₁ l₂ : List (Sigma β)), a ∉ l₁.keys ∧ l = l₁
 ++ ⟨a, b⟩ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ ≠ a₂) :
    a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
  (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ ∈ l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]
/-
**List.keys_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.keys.eq_1`：∀ {α : Type u} {β : α → Type v}, List.keys = List.map Si
gma.fst
· 使用定理 `List.kerase.eq_1`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α]
 (a : α), List.kerase a = List.eraseP fun s => decide (a = s.fst)
· 使用定理 `List.erase_eq_eraseP`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), l.erase a = List.eraseP (fun x => a == x) l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.eraseP_map`：∀ {β : Type u_1} {α : Type u_2} {p : α → Bool} {f : β →
 α} {l : List β},   List.eraseP p (List.map f l) = List.map f (List.eraseP (p ∘ 
f) l)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a := by
  rw [keys, kerase, erase_eq_eraseP, eraseP_map, Function.comp_def]
  congr
/-
**List.kerase_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_kerase {a a'} {l : List (Sigma β)} : (kerase a' l).kerase a = (kera
se a l).kerase a'
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem kerase_kerase {a a'} {l : List (Sigma β)} :
    (kerase a' l).kerase a = (kerase a l).kerase a' := by
  by_cases h : a = a'
  · subst a'; rfl
  induction l with
  | nil => rfl
  | cons x xs =>
    by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_cons_ne, *]
/-
**List.NodupKeys.kerase** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l : List (Sigma β)} [inst : DecidableEq α
] (a : α),   l.NodupKeys → (List.kerase a l).NodupKeys
参数：Sigma β；a : α；List.kerase a l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.NodupKeys.sublist`：∀ {α : Type u} {β : α → Type v} {l₁ l₂ : List (S
igma β)}, l₁.Sublist l₂ → l₂.NodupKeys → l₁.NodupKeys
· 使用定理 `List.kerase_sublist`：kerase_sublist (a : α) (l : List (Sigma β)) : keras
e a l <+ l
-/
theorem NodupKeys.kerase (a : α) : NodupKeys l → (kerase a l).NodupKeys :=
  NodupKeys.sublist <| kerase_sublist _ _
/-
**List.Perm.kerase** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {l₁ l₂ : Li
st (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (List.kerase a l₁).Perm (List.keras
e a l₂)
参数：Sigma β；List.kerase a l₁；List.kerase a l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eraseP`：∀ {α : Type u_1} (f : α → Bool) {l₁ l₂ : List α},   Li
st.Pairwise (fun a b => f a = true → f b = true → False) l₁ →     l₁.Perm l₂ → (
List.e…
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodupKeys_iff_pairwise`：nodupKeys_iff_pairwise {l} : NodupKeys l ↔ 
Pairwise (fun s s' : Sigma β => s.1 != s'.1) l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
-/
theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ := by
  apply Perm.eraseP
  apply (nodupKeys_iff_pairwise.1 nd).imp
  intros; simp_all

@[simp]
/-
**List.notMem_keys_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：notMem_keys_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) : a ∉ (kera
se a l).keys
参数：a；Sigma β；nd : l.NodupKeys。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem notMem_keys_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    a ∉ (kerase a l).keys := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [nodupKeys_cons] at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]

@[simp]
/-
**List.dlookup_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) : dlookup a (ke
rase a l) = none
参数：a；Sigma β；nd : l.NodupKeys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dlookup_eq_none`：dlookup_eq_none {a : α} {l : List (Sigma β)} : dlo
okup a l = none ↔ a ∉ l.keys
· 使用定理 `List.notMem_keys_kerase`：notMem_keys_kerase (a) {l : List (Sigma β)} (nd
 : l.NodupKeys) : a ∉ (kerase a l).keys
-/
theorem dlookup_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    dlookup a (kerase a l) = none :=
  dlookup_eq_none.mpr (notMem_keys_kerase a nd)

@[simp]
/-
**List.dlookup_kerase_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a != a') : dlookup a (k
erase a' l) = dlookup a l
参数：Sigma β；h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup.congr_simp`：∀ {α : Type u} {β : α → Type v} {inst : Decidab
leEq α} [inst_1 : DecidableEq α] (a : α) (a_1 a_2 : List (Sigma β)),   a_1 = a_2
 → List.dlook…
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
-/
theorem dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kerase a' l) = dlookup a l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ah, bh⟩ := hd
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · subst h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]
/-
**List.kerase_append_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {l₁ l₂ : Li
st (Sigma β)},   a ∈ l₁.keys → List.kerase a (l₁ ++ l₂) = List.kerase a l₁ ++ l₂
参数：Sigma β；l₁ ++ l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kerase_append_left {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by cases h
  | s :: l₁, l₂, h₁ => by
    if h₂ : a = s.1 then simp [h₂]
    else simp_all [kerase_append_left]
/-
**List.kerase_append_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {l₁ l₂ : Li
st (Sigma β)},   a ∉ l₁.keys → List.kerase a (l₁ ++ l₂) = l₁ ++ List.kerase a l₂
参数：Sigma β；l₁ ++ l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kerase_append_right {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, _ => rfl
  | _ :: l₁, l₂, h => by
    simp only [keys_cons, mem_cons, not_or] at h
    simp [h.1, kerase_append_right h.2]
/-
**List.kerase_comm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kerase_comm (a₁ a₂) (l : List (Sigma β)) : kerase a₂ (kerase a₁ l) = keras
e a₁ (kerase a₂ l)
参数：a₁ a₂；l : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.exists_of_kerase`：exists_of_kerase {a : α} {l : List (Sigma β)} (h 
: a in l.keys) : exists (b : β a) (l₁ l₂ : List (Sigma β)), a ∉ l₁.keys ∧ l = l₁
 ++ ⟨a, b⟩ …
· 使用定理 `List.kerase_append_left`：∀ {α : Type u} {β : α → Type v} [inst : Decidab
leEq α] {a : α} {l₁ l₂ : List (Sigma β)},   a ∈ l₁.keys → List.kerase a (l₁ ++ l
₂) = List.ker…
· 使用定理 `List.kerase_append_right`：∀ {α : Type u} {β : α → Type v} [inst : Decida
bleEq α] {a : α} {l₁ l₂ : List (Sigma β)},   a ∉ l₁.keys → List.kerase a (l₁ ++ 
l₂) = l₁ ++ Li…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_keys_kerase_of_ne`：mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sig
ma β)} (h : a₁ != a₂) : a₁ in (kerase a₂ l).keys ↔ a₁ in l.keys
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.mem_keys_of_mem_keys_kerase`：mem_keys_of_mem_keys_kerase {a₁ a₂} {l
 : List (Sigma β)} : a₁ in (kerase a₂ l).keys -> a₁ in l.keys
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) :
    kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, _ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [kerase_append_left h',
              kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]
/-
**List.sizeOf_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sizeOf_kerase [SizeOf (Sigma β)] (x : α) (xs : List (Sigma β)) : SizeOf.si
zeOf (List.kerase x xs) <= SizeOf.sizeOf xs
参数：Sigma β；x : α；xs : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_of_notMem_keys`：kerase_of_notMem_keys {a} {l : List (Sigma β
)} (h : a ∉ l.keys) : kerase a l = l
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.nil.sizeOf_spec`：∀ {α : Type u} [inst : SizeOf α], sizeOf [] = 1
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.kerase_cons_eq`：kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β
)} (h : a = s.1) : kerase a (s :: l) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.cons.sizeOf_spec`：∀ {α : Type u} [inst : SizeOf α] (head : α) (tail
 : List α), sizeOf (head :: tail) = 1 + sizeOf head + sizeOf tail
· 使用定理 `List.kerase_cons_ne`：kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β
)} (h : a != s.1) : kerase a (s :: l) = s :: kerase a l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem sizeOf_kerase [SizeOf (Sigma β)] (x : α)
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.kerase x xs) ≤ SizeOf.sizeOf xs := by
  induction xs with
  | nil => simp
  | cons y ys => by_cases x = y.1 <;> simp [*]

/-! ### `kinsert` -/


/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
/-
**List.kinsert** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β)
参数：a : α；b : β a；l : List (Sigma β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`.
-/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l

@[simp]
/-
**List.kinsert_def** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ ::
 kerase a l
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl
/-
**List.mem_keys_kinsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} : a in (kinsert a
' b' l).keys ↔ a = a' ∨ a in l.keys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} :
    a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys := by by_cases h : a = a' <;> simp [h]
/-
**List.kinsert_nodupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kinsert_nodupKeys (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys) : 
(kinsert a b l).NodupKeys
参数：a；b : β a；Sigma β；nd : l.NodupKeys。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodupKeys_cons`：nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
 NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l
· 使用定理 `List.notMem_keys_kerase`：notMem_keys_kerase (a) {l : List (Sigma β)} (nd
 : l.NodupKeys) : a ∉ (kerase a l).keys
· 使用定理 `List.NodupKeys.kerase`：∀ {α : Type u} {β : α → Type v} {l : List (Sigma 
β)} [inst : DecidableEq α] (a : α),   l.NodupKeys → (List.kerase a l).NodupKeys
-/
theorem kinsert_nodupKeys (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    (kinsert a b l).NodupKeys :=
  nodupKeys_cons.mpr ⟨notMem_keys_kerase a nd, nd.kerase a⟩
/-
**List.Perm.kinsert** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {b : β a} {
l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (List.kinsert a b l₁).Per
m (List.kinsert a b l₂)
参数：Sigma β；List.kinsert a b l₁；List.kinsert a b l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kerase`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α]
 {a : α} {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (List.kerase a 
l₁).Pe…
-/
theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _
/-
**List.dlookup_kinsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kinsert {a} {b : β a} (l : List (Sigma β)) : dlookup a (kinsert a 
b l) = some b
参数：l : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dlookup_kinsert {a} {b : β a} (l : List (Sigma β)) :
    dlookup a (kinsert a b l) = some b := by
  simp only [kinsert, dlookup_cons_eq]
/-
**List.dlookup_kinsert_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a != a') :
 dlookup a (kinsert a' b' l) = dlookup a l
参数：Sigma β；h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dlookup_kerase_ne`：dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h
 : a != a') : dlookup a (kerase a' l) = dlookup a l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dlookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kinsert a' b' l) = dlookup a l := by simp [h]

/-! ### `kextract` -/


/-- Finds the first entry with a given key `a` and returns its value (as an `Option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
/-
**List.kextract** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：kextract (a : α) : List (Sigma β) -> Option (β a) × List (Sigma β) | [] =>
 (none, []) | s :: l => if h : s.1 = a then (some (Eq.recOn h s.2), l) else let 
(b', l')
参数：a : α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finds the first entry with a given key `a` and returns its value (as an `Option`
 because there
might be no entry with key `a`) alongside with the rest of the entries.
-/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOn h s.2), l)
    else
      let (b', l') := kextract a l
      (b', s :: l')

@[simp]
/-
**List.kextract_eq_dlookup_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (a : α) (l : List (
Sigma β)),   List.kextract a l = (List.dlookup a l, List.kerase a l)
参数：a : α；l : List (Sigma β)；List.dlookup a l, List.kerase a l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kextract_eq_dlookup_kerase (a : α) :
    ∀ l : List (Sigma β), kextract a l = (dlookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp only [kextract]; split_ifs with h
    · subst a'
      simp [kerase]
    · simp [Ne.symm h, kextract_eq_dlookup_kerase a l, kerase]

/-! ### `dedupKeys` -/


/-- Remove entries with duplicate keys from `l : List (Sigma β)`. -/
/-
**List.dedupKeys** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：dedupKeys : List (Sigma β) -> List (Sigma β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove entries with duplicate keys from `l : List (Sigma β)`.
-/
def dedupKeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []
/-
**List.dedupKeys_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) : dedupKeys (x :: l) = k
insert x.1 x.2 (dedupKeys l)
参数：l : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) :
    dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l) :=
  rfl
/-
**List.nodupKeys_dedupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodupKeys_dedupKeys (l : List (Sigma β)) : NodupKeys (dedupKeys l)
参数：l : List (Sigma β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nodup_nil`：∀ {α : Type u_1}, [].Nodup
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.keys_kerase`：keys_kerase {a} {l : List (Sigma β)} : (kerase a l).ke
ys = l.keys.erase a
· 使用定理 `List.Nodup.not_mem_erase`：∀ {α : Type u_1} [inst : BEq α] {l : List α} [
LawfulBEq α] {a : α}, l.Nodup → a ∉ l.erase a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.NodupKeys.kerase`：∀ {α : Type u} {β : α → Type v} {l : List (Sigma 
β)} [inst : DecidableEq α] (a : α),   l.NodupKeys → (List.kerase a l).NodupKeys
-/
theorem nodupKeys_dedupKeys (l : List (Sigma β)) : NodupKeys (dedupKeys l) := by
  dsimp [dedupKeys]
  generalize hl : nil = l'
  have : NodupKeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction l with
  | nil => apply this
  | cons x xs l_ih =>
    cases x
    simp only [foldr_cons, kinsert_def, nodupKeys_cons]
    constructor
    · simp only [keys_kerase]
      apply l_ih.not_mem_erase
    · exact l_ih.kerase _
/-
**List.dlookup_dedupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_dedupKeys (a : α) (l : List (Sigma β)) : dlookup a (dedupKeys l) =
 dlookup a l
参数：a : α；l : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedupKeys_cons`：dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) :
 dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l)
· 使用定理 `List.dlookup_kinsert`：dlookup_kinsert {a} {b : β a} (l : List (Sigma β))
 : dlookup a (kinsert a b l) = some b
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
· 使用定理 `List.dlookup_kinsert_ne`：dlookup_kinsert_ne {a a'} {b' : β a'} {l : List
 (Sigma β)} (h : a != a') : dlookup a (kinsert a' b' l) = dlookup a l
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
-/
theorem dlookup_dedupKeys (a : α) (l : List (Sigma β)) : dlookup a (dedupKeys l) = dlookup a l := by
  induction l with
  | nil => rfl
  | cons l_hd _ l_ih =>
    obtain ⟨a', b⟩ := l_hd
    by_cases h : a = a'
    · subst a'
      rw [dedupKeys_cons, dlookup_kinsert, dlookup_cons_eq]
    · rw [dedupKeys_cons, dlookup_kinsert_ne h, l_ih, dlookup_cons_ne]
      exact h
/-
**List.sizeOf_cons_le_sizeOf_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sizeOf_cons_le_sizeOf_cons {α : Type*} [SizeOf α] {l r : List α} (a : α) (
h : SizeOf.sizeOf l <= SizeOf.sizeOf r) : SizeOf.sizeOf (a :: l) <= SizeOf.sizeO
f (a :: r)
参数：a : α；h : SizeOf.sizeOf l <= SizeOf.sizeOf r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons.sizeOf_spec`：∀ {α : Type u} [inst : SizeOf α] (head : α) (tail
 : List α), sizeOf (head :: tail) = 1 + sizeOf head + sizeOf tail
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
-/
theorem sizeOf_cons_le_sizeOf_cons {α : Type*} [SizeOf α] {l r : List α} (a : α)
    (h : SizeOf.sizeOf l ≤ SizeOf.sizeOf r) :
    SizeOf.sizeOf (a :: l) ≤ SizeOf.sizeOf (a :: r) := by
  rw [cons.sizeOf_spec, cons.sizeOf_spec]
  exact Nat.add_le_add_iff_left.mpr h
/-
**List.sizeOf_dedupKeys** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sizeOf_dedupKeys [SizeOf (Sigma β)] (xs : List (Sigma β)) : SizeOf.sizeOf 
(dedupKeys xs) <= SizeOf.sizeOf xs
参数：Sigma β；xs : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil.sizeOf_spec`：∀ {α : Type u} [inst : SizeOf α], sizeOf [] = 1
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `List.sizeOf_cons_le_sizeOf_cons`：sizeOf_cons_le_sizeOf_cons {α : Type*} 
[SizeOf α] {l r : List α} (a : α) (h : SizeOf.sizeOf l <= SizeOf.sizeOf r) : Siz
eOf.sizeOf (a :: l) <…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `List.sizeOf_kerase`：sizeOf_kerase [SizeOf (Sigma β)] (x : α) (xs : List 
(Sigma β)) : SizeOf.sizeOf (List.kerase x xs) <= SizeOf.sizeOf xs
-/
theorem sizeOf_dedupKeys [SizeOf (Sigma β)]
    (xs : List (Sigma β)) : SizeOf.sizeOf (dedupKeys xs) ≤ SizeOf.sizeOf xs := by
  induction xs with
  | nil => simp [dedupKeys]
  | cons x xs h =>
    simp only [dedupKeys_cons, kinsert_def, Sigma.eta]
    exact sizeOf_cons_le_sizeOf_cons x (le_trans (sizeOf_kerase x.fst xs.dedupKeys) h)

/-! ### `kunion` -/


/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
/-
**List.kunion** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → {β : α → Type v} → [DecidableEq α] → List (Sigma β) → List 
(Sigma β) → List (Sigma β)
参数：Sigma β；Sigma β；Sigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased.
-/
def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)

@[simp]
/-
**List.nil_kunion** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nil_kunion {l : List (Sigma β)} : kunion [] l = l
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl

@[simp]
/-
**List.kunion_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {l : List (Sigma β)
}, l.kunion [] = l
参数：Sigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kunion_nil : ∀ {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by rw [kunion, kerase_nil, kunion_nil]

@[simp]
/-
**List.kunion_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：kunion_cons {s} {l₁ l₂ : List (Sigma β)} : kunion (s :: l₁) l₂ = s :: kuni
on l₁ (kerase s.1 l₂)
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} :
    kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl

@[simp]
/-
**List.mem_keys_kunion** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} : a in (kunion l₁ l₂).keys ↔ 
a in l₁.keys ∨ a in l₂.keys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} :
    a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h]; simp [h, ih]]

@[simp]
/-
**List.kunion_kerase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {a : α} {l₁ l₂ : Li
st (Sigma β)},   (List.kerase a l₁).kunion (List.kerase a l₂) = List.kerase a (l
₁.kunion l₂)
参数：Sigma β；List.kerase a l₁；List.kerase a l₂；l₁.kunion l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kunion_kerase {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by by_cases h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]
/-
**List.NodupKeys.kunion** 是 Mathlib 中的一个定理，位于命名空间 `List.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {l₁ l₂ : List (Sigma β)} [inst : Decidable
Eq α],   l₁.NodupKeys → l₂.NodupKeys → (l₁.kunion l₂).NodupKeys
参数：Sigma β；l₁.kunion l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.NodupKeys.kerase`：∀ {α : Type u} {β : α → Type v} {l : List (Sigma 
β)} [inst : DecidableEq α] (a : α),   l.NodupKeys → (List.kerase a l).NodupKeys
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem NodupKeys.kunion (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) : (kunion l₁ l₂).NodupKeys := by
  induction l₁ generalizing l₂ with
  | nil => simp only [nil_kunion, nd₂]
  | cons s l₁ ih =>
    simp only [nodupKeys_cons] at nd₁
    simp [nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]
/-
**List.Perm.kunion_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {l₁ l₂ : List (Sigm
a β)},   l₁.Perm l₂ → ∀ (l : List (Sigma β)), (l₁.kunion l).Perm (l₂.kunion l)
参数：Sigma β；l : List (Sigma β)；l₁.kunion l；l₂.kunion l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.kerase_comm`：kerase_comm (a₁ a₂) (l : List (Sigma β)) : kerase a₂ (
kerase a₁ l) = kerase a₁ (kerase a₂ l)
-/
theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) :
    kunion l₁ l ~ kunion l₂ l := by
  induction p generalizing l with
  | nil => rfl
  | cons hd _ ih =>
    simp [ih (List.kerase _ _)]
  | swap s₁ s₂ l => simp [kerase_comm, Perm.swap]
  | trans _ _ ih₁₂ ih₂₃ => exact Perm.trans (ih₁₂ l) (ih₂₃ l)
/-
**List.Perm.kunion_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (l : List (Sigma β)
) {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂ → (l.kunion l₁).Perm (l.
kunion l₂)
参数：l : List (Sigma β)；Sigma β；l.kunion l₁；l.kunion l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Perm.kunion_left :
    ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.NodupKeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, _, _, nd₁, p => ((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s
/-
**List.Perm.kunion** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] {l₁ l₂ l₃ l₄ : List
 (Sigma β)},   l₃.NodupKeys → l₁.Perm l₂ → l₃.Perm l₄ → (l₁.kunion l₃).Perm (l₂.
kunion l₄)
参数：Sigma β；l₁.kunion l₃；l₂.kunion l₄。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.kunion_right`：∀ {α : Type u} {β : α → Type v} [inst : Decidabl
eEq α] {l₁ l₂ : List (Sigma β)},   l₁.Perm l₂ → ∀ (l : List (Sigma β)), (l₁.kuni
on l).Perm (…
· 使用定理 `List.Perm.kunion_left`：∀ {α : Type u} {β : α → Type v} [inst : Decidable
Eq α] (l : List (Sigma β)) {l₁ l₂ : List (Sigma β)},   l₁.NodupKeys → l₁.Perm l₂
 → (l.kunio…
-/
theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
    (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)

@[simp]
/-
**List.dlookup_kunion_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a in l₁.keys) : dloo
kup a (kunion l₁ l₂) = dlookup a l₁
参数：Sigma β；h : a in l₁.keys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.kunion_cons`：kunion_cons {s} {l₁ l₂ : List (Sigma β)} : kunion (s :
: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂)
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons s _ ih =>
    simp only [keys_cons, mem_cons] at h
    rcases h with rfl | h <;> obtain ⟨a'⟩ := s
    · simp
    · rw [kunion_cons]
      by_cases h' : a = a'
      · subst h'
        simp
      · simp [h', ih h]

@[simp]
/-
**List.dlookup_kunion_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) : dloo
kup a (kunion l₁ l₂) = dlookup a l₂
参数：Sigma β；h : a ∉ l₁.keys。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.dlookup_kerase_ne`：dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h
 : a != a') : dlookup a (kerase a' l) = dlookup a l
-/
theorem dlookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih => simp_all [not_or]
/-
**List.mem_dlookup_kunion** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} : b in dlookup a
 (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b in dlookup a l₂
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.dlookup_cons_ne`：∀ {α : Type u} {β : α → Type v} [inst : DecidableE
q α] (l : List (Sigma β)) {a : α} (s : Sigma β),   a ≠ s.fst → List.dlookup a (s
 :: l) = L…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.dlookup_kerase_ne`：dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h
 : a != a') : dlookup a (kerase a' l) = dlookup a l
-/
theorem mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ dlookup a (kunion l₁ l₂) ↔ b ∈ dlookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s _ ih =>
    obtain ⟨a'⟩ := s
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · simp [h₁, @ih (kerase a' l₂)]

@[simp]
/-
**List.dlookup_kunion_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dlookup_kunion_eq_some {a} {b : β a} {l₁ l₂ : List (Sigma β)} : dlookup a 
(kunion l₁ l₂) = some b ↔ dlookup a l₁ = some b ∨ a ∉ l₁.keys ∧ dlookup a l₂ = s
ome b
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_kunion`：mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List 
(Sigma β)} : b in dlookup a (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b
 in dlookup a…
-/
theorem dlookup_kunion_eq_some {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    dlookup a (kunion l₁ l₂) = some b ↔
      dlookup a l₁ = some b ∨ a ∉ l₁.keys ∧ dlookup a l₂ = some b :=
  mem_dlookup_kunion
/-
**List.mem_dlookup_kunion_middle** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dlookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)} (h₁ : 
b in dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) : b in dlookup a (kunion (kuni
on l₁ l₂) l₃)
参数：Sigma β；h₁ : b in dlookup a (kunion l₁ l₃)；h₂ : a ∉ keys l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_dlookup_kunion`：mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List 
(Sigma β)} : b in dlookup a (kunion l₁ l₂) ↔ b in dlookup a l₁ ∨ a ∉ l₁.keys ∧ b
 in dlookup a…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `List.mem_keys_kunion`：mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} : a i
n (kunion l₁ l₂).keys ↔ a in l₁.keys ∨ a in l₂.keys
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_dlookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
    (h₁ : b ∈ dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
    b ∈ dlookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_dlookup_kunion.mpr <| Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩

end List

