/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
module

public import Mathlib.Data.List.AList
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Part

/-!
# Finite maps over `Multiset`
-/

@[expose] public section

universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-! ### Multisets of sigma types -/

namespace Multiset

/-- Multiset of keys of an association multiset. -/
/-
**Multiset.keys** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：keys (s : Multiset (Sigma β)) : Multiset α
参数：s : Multiset (Sigma β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiset of keys of an association multiset.
-/
def keys (s : Multiset (Sigma β)) : Multiset α :=
  s.map Sigma.fst

@[simp]
/-
**Multiset.coe_keys** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_keys {l : List (Sigma β)} : keys (l : Multiset (Sigma β)) = (l.keys : 
Multiset α)
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_keys {l : List (Sigma β)} : keys (l : Multiset (Sigma β)) = (l.keys : Multiset α) :=
  rfl

@[simp]
/-
**Multiset.keys_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：keys_zero : keys (0 : Multiset (Sigma β)) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_zero : keys (0 : Multiset (Sigma β)) = 0 := rfl

@[simp]
/-
**Multiset.keys_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：keys_cons {a : α} {b : β a} {s : Multiset (Sigma β)} : keys (⟨a, b⟩ ::ₘ s)
 = a ::ₘ keys s
参数：Sigma β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem keys_cons {a : α} {b : β a} {s : Multiset (Sigma β)} :
    keys (⟨a, b⟩ ::ₘ s) = a ::ₘ keys s := by
  simp [keys]

@[simp]
/-
**Multiset.keys_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：keys_singleton {a : α} {b : β a} : keys ({⟨a, b⟩} : Multiset (Sigma β)) = 
{a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_singleton {a : α} {b : β a} : keys ({⟨a, b⟩} : Multiset (Sigma β)) = {a} := rfl

/-- `NodupKeys s` means that `s` has no duplicate keys. -/
/-
**Multiset.NodupKeys** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：NodupKeys (s : Multiset (Sigma β)) : Prop
参数：s : Multiset (Sigma β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NodupKeys s` means that `s` has no duplicate keys.
-/
def NodupKeys (s : Multiset (Sigma β)) : Prop :=
  Quot.liftOn s List.NodupKeys fun _ _ p => propext <| perm_nodupKeys p

@[simp]
/-
**Multiset.coe_nodupKeys** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_nodupKeys {l : List (Sigma β)} : @NodupKeys α β l ↔ l.NodupKeys
参数：Sigma β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nodupKeys {l : List (Sigma β)} : @NodupKeys α β l ↔ l.NodupKeys :=
  Iff.rfl
/-
**Multiset.nodup_keys** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：nodup_keys {m : Multiset (Σ a, β a)} : m.keys.Nodup ↔ m.NodupKeys
参数：Σ a, β a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nodup_keys {m : Multiset (Σ a, β a)} : m.keys.Nodup ↔ m.NodupKeys := by
  rcases m with ⟨l⟩; rfl

alias ⟨_, NodupKeys.nodup_keys⟩ := nodup_keys
/-
**Multiset.NodupKeys.nodup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.NodupKeys`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {m : Multiset ((a : α) × β a)}, m.NodupKey
s → m.Nodup
参数：(a : α) × β a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.of_map`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f
 : α → β), (Multiset.map f s).Nodup → s.Nodup
· 使用定理 `Multiset.NodupKeys.nodup_keys`：∀ {α : Type u} {β : α → Type v} {m : Mult
iset ((a : α) × β a)}, m.NodupKeys → m.keys.Nodup
-/
protected lemma NodupKeys.nodup {m : Multiset (Σ a, β a)} (h : m.NodupKeys) : m.Nodup :=
  h.nodup_keys.of_map _

end Multiset

/-! ### Finmap -/

/-- `Finmap β` is the type of finite maps over a multiset. It is effectively
  a quotient of `AList β` by permutation of the underlying list. -/
/-
**Finmap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u} → (α → Type v) → Type (max u v)
参数：α → Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finmap β` is the type of finite maps over a multiset. It is effectively
  a quotient of `AList β` by permutation of the underlying list.
-/
structure Finmap (β : α → Type v) : Type max u v where
  /-- The underlying `Multiset` of a `Finmap` -/
  entries : Multiset (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/-- The quotient map from `AList` to `Finmap`. -/
/-
**AList.toFinmap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AList.toFinmap (s : AList β) : Finmap β
参数：s : AList β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys

--- 原说明 ---
The quotient map from `AList` to `Finmap`.
-/
def AList.toFinmap (s : AList β) : Finmap β :=
  ⟨s.entries, s.nodupKeys⟩

-- Setting `priority := high` means that Lean will prefer this notation to the identical one
-- for `Quotient.mk`
local notation:arg "⟦" a "⟧" => AList.toFinmap a

set_option backward.isDefEq.respectTransparency false in
/-
**AList.toFinmap_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AList.toFinmap_eq {s₁ s₂ : AList β} : toFinmap s₁ = toFinmap s₂ ↔ s₁.entri
es ~ s₂.entries
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `Finmap.mk.injEq`：∀ {α : Type u} {β : α → Type v} (entries : Multiset (Si
gma β)) (nodupKeys : entries.NodupKeys)   (entries_1 : Multiset (Sigma β)) (nodu
pKeys…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem AList.toFinmap_eq {s₁ s₂ : AList β} :
    toFinmap s₁ = toFinmap s₂ ↔ s₁.entries ~ s₂.entries := by
  cases s₁
  cases s₂
  simp [AList.toFinmap]

@[simp]
/-
**AList.toFinmap_entries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AList.toFinmap_entries (s : AList β) : ⟦s⟧.entries = s.entries
参数：s : AList β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AList.toFinmap_entries (s : AList β) : ⟦s⟧.entries = s.entries :=
  rfl

/-- Given `l : List (Sigma β)`, create a term of type `Finmap β` by removing
entries with duplicate keys. -/
/-
**List.toFinmap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.toFinmap [DecidableEq α] (s : List (Sigma β)) : Finmap β
参数：s : List (Sigma β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `l : List (Sigma β)`, create a term of type `Finmap β` by removing
entries with duplicate keys.
-/
def List.toFinmap [DecidableEq α] (s : List (Sigma β)) : Finmap β :=
  s.toAList.toFinmap

namespace Finmap

open AList

/-
**Finmap.nodup_entries** 是 Mathlib 中的一个引理，位于命名空间 `Finmap`。
形式化陈述：nodup_entries (f : Finmap β) : f.entries.Nodup
参数：f : Finmap β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.NodupKeys.nodup`：∀ {α : Type u} {β : α → Type v} {m : Multiset 
((a : α) × β a)}, m.NodupKeys → m.Nodup
· 使用定理 `Finmap.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : Finmap β), sel
f.entries.NodupKeys
-/
lemma nodup_entries (f : Finmap β) : f.entries.Nodup := f.nodupKeys.nodup

/-! ### Lifting from AList -/

/-- Lift a permutation-respecting function on `AList` to `Finmap`. -/
/-
**Finmap.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：liftOn {γ} (s : Finmap β) (f : AList β -> γ) (H : forall a b : AList β, a.
entries ~ b.entries -> f a = f b) : γ
参数：s : Finmap β；f : AList β -> γ；H : forall a b : AList β, a.entries ~ b.entries
 -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a permutation-respecting function on `AList` to `Finmap`.
-/
def liftOn {γ} (s : Finmap β) (f : AList β → γ)
    (H : ∀ a b : AList β, a.entries ~ b.entries → f a = f b) : γ := by
  refine
    (Quotient.liftOn s.entries
      (fun (l : List (Sigma β)) => (⟨_, fun nd => f ⟨l, nd⟩⟩ : Part γ))
      (fun l₁ l₂ p => Part.ext' (perm_nodupKeys p) ?_) : Part γ).get ?_
  · exact fun h1 h2 => H _ _ p
  · have := s.nodupKeys
    revert this
    rcases s.entries with ⟨l⟩
    exact id

@[simp]
/-
**Finmap.liftOn_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：liftOn_toFinmap {γ} (s : AList β) (f : AList β -> γ) (H) : liftOn ⟦s⟧ f H 
= f s
参数：s : AList β；f : AList β -> γ；H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem liftOn_toFinmap {γ} (s : AList β) (f : AList β → γ) (H) : liftOn ⟦s⟧ f H = f s := by
  cases s
  rfl

/-- Lift a permutation-respecting function on 2 `AList`s to 2 `Finmap`s. -/
/-
**Finmap.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：liftOn {γ} (s : Finmap β) (f : AList β -> γ) (H : forall a b : AList β, a.
entries ~ b.entries -> f a = f b) : γ
参数：s : Finmap β；f : AList β -> γ；H : forall a b : AList β, a.entries ~ b.entries
 -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a permutation-respecting function on 2 `AList`s to 2 `Finmap`s.
-/
def liftOn₂ {γ} (s₁ s₂ : Finmap β) (f : AList β → AList β → γ)
    (H : ∀ a₁ b₁ a₂ b₂ : AList β,
      a₁.entries ~ a₂.entries → b₁.entries ~ b₂.entries → f a₁ b₁ = f a₂ b₂) : γ :=
  liftOn s₁ (fun l₁ => liftOn s₂ (f l₁) fun _ _ p => H _ _ _ _ (Perm.refl _) p) fun a₁ a₂ p => by
    have H' : f a₁ = f a₂ := funext fun _ => H _ _ _ _ p (Perm.refl _)
    simp only [H']

@[simp]
/-
**Finmap.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：liftOn {γ} (s : Finmap β) (f : AList β -> γ) (H : forall a b : AList β, a.
entries ~ b.entries -> f a = f b) : γ
参数：s : Finmap β；f : AList β -> γ；H : forall a b : AList β, a.entries ~ b.entries
 -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_toFinmap {γ} (s₁ s₂ : AList β) (f : AList β → AList β → γ) (H) :
    liftOn₂ ⟦s₁⟧ ⟦s₂⟧ f H = f s₁ s₂ := rfl

/-! ### Induction -/

@[elab_as_elim]
/-
**Finmap.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：induction_on {C : Finmap β -> Prop} (s : Finmap β) (H : forall a : AList β
, C ⟦a⟧) : C s
参数：s : Finmap β；H : forall a : AList β, C ⟦a⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Induction
-/
theorem induction_on {C : Finmap β → Prop} (s : Finmap β) (H : ∀ a : AList β, C ⟦a⟧) : C s := by
  rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_elim]
/-
**Finmap.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：induction_on {C : Finmap β -> Prop} (s : Finmap β) (H : forall a : AList β
, C ⟦a⟧) : C s
参数：s : Finmap β；H : forall a : AList β, C ⟦a⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem induction_on₂ {C : Finmap β → Finmap β → Prop} (s₁ s₂ : Finmap β)
    (H : ∀ a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂ :=
  induction_on s₁ fun l₁ => induction_on s₂ fun l₂ => H l₁ l₂

@[elab_as_elim]
/-
**Finmap.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：induction_on {C : Finmap β -> Prop} (s : Finmap β) (H : forall a : AList β
, C ⟦a⟧) : C s
参数：s : Finmap β；H : forall a : AList β, C ⟦a⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem induction_on₃ {C : Finmap β → Finmap β → Finmap β → Prop} (s₁ s₂ s₃ : Finmap β)
    (H : ∀ a₁ a₂ a₃ : AList β, C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃⟧) : C s₁ s₂ s₃ :=
  induction_on₂ s₁ s₂ fun l₁ l₂ => induction_on s₃ fun l₃ => H l₁ l₂ l₃

/-! ### extensionality -/

@[ext]
/-
**Finmap.ext** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：∀ {α : Type u} {β : α → Type v} {s t : Finmap β}, s.entries = t.entries → 
s = t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### extensionality
-/
theorem ext : ∀ {s t : Finmap β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr

@[simp]
/-
**Finmap.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：ext_iff' {s t : Finmap β} : s.entries = t.entries ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finmap.ext_iff`：∀ {α : Type u} {β : α → Type v} {s t : Finmap β}, s = t 
↔ s.entries = t.entries
-/
theorem ext_iff' {s t : Finmap β} : s.entries = t.entries ↔ s = t :=
  Finmap.ext_iff.symm

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `a ∈ s` means that `s` has a value associated to the key `a`.
-/
instance : Membership α (Finmap β) :=
  ⟨fun s a => a ∈ s.entries.keys⟩
/-
**Finmap.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_def {a : α} {s : Finmap β} : a in s ↔ a in s.entries.keys
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def {a : α} {s : Finmap β} : a ∈ s ↔ a ∈ s.entries.keys :=
  Iff.rfl

@[simp]
/-
**Finmap.mem_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_toFinmap {a : α} {s : AList β} : a in toFinmap s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toFinmap {a : α} {s : AList β} : a ∈ toFinmap s ↔ a ∈ s :=
  Iff.rfl

/-! ### keys -/

/-- The set of keys of a finite map. -/
/-
**Finmap.keys** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：keys (s : Finmap β) : Finset α
参数：s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of keys of a finite map.
-/
def keys (s : Finmap β) : Finset α :=
  ⟨s.entries.keys, s.nodupKeys.nodup_keys⟩

@[simp]
/-
**Finmap.keys_val** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_val (s : AList β) : (keys ⟦s⟧).val = s.keys
参数：s : AList β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_val (s : AList β) : (keys ⟦s⟧).val = s.keys :=
  rfl

@[simp]
/-
**Finmap.keys_ext** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_ext {s₁ s₂ : AList β} : keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mk.injEq`：∀ {α : Type u_4} (val : Multiset α) (nodup : val.Nodup)
 (val_1 : Multiset α) (nodup_1 : val_1.Nodup),   ({ val := val, nodup := nodup }
 = { …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem keys_ext {s₁ s₂ : AList β} : keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys := by
  simp [keys, AList.keys]
/-
**Finmap.mem_keys** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_keys {a : α} {s : Finmap β} : a in s.keys ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.mem_keys`：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
-/
theorem mem_keys {a : α} {s : Finmap β} : a ∈ s.keys ↔ a ∈ s :=
  induction_on s fun _ => AList.mem_keys

/-! ### empty -/

/-- The empty map. -/
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty map.
-/
instance : EmptyCollection (Finmap β) :=
  ⟨⟨0, nodupKeys_nil⟩⟩
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Finmap β) :=
  ⟨∅⟩

@[simp]
/-
**Finmap.empty_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅ :=
  rfl

@[simp]
/-
**Finmap.toFinmap_nil** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：toFinmap_nil [DecidableEq α] : ([].toFinmap : Finmap β) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinmap_nil [DecidableEq α] : ([].toFinmap : Finmap β) = ∅ :=
  rfl
/-
**Finmap.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：notMem_empty {a : α} : a ∉ (∅ : Finmap β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
-/
theorem notMem_empty {a : α} : a ∉ (∅ : Finmap β) :=
  Multiset.notMem_zero a

@[simp]
/-
**Finmap.keys_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_empty : (∅ : Finmap β).keys = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_empty : (∅ : Finmap β).keys = ∅ :=
  rfl

/-! ### singleton -/

/-- The singleton map. -/
/-
**Finmap.singleton** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：singleton (a : α) (b : β a) : Finmap β
参数：a : α；b : β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton map.
-/
def singleton (a : α) (b : β a) : Finmap β :=
  ⟦AList.singleton a b⟧

@[simp]
/-
**Finmap.keys_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_singleton (a : α) (b : β a) : (singleton a b).keys = {a}
参数：a : α；b : β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = {a} :=
  rfl

@[simp]
/-
**Finmap.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_singleton (x y : α) (b : β y) : x in singleton y b ↔ x = y
参数：x y : α；b : β y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_singleton (x y : α) (b : β y) : x ∈ singleton y b ↔ x = y := by
  simp [singleton, mem_def]

section

variable [DecidableEq α]

/-
**Finmap.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：{α : Type u} → {β : α → Type v} → [DecidableEq α] → [(a : α) → DecidableEq
 (β a)] → DecidableEq (Finmap β)
参数：a : α；β a；Finmap β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [∀ a, DecidableEq (β a)] : DecidableEq (Finmap β)
  | _, _ => decidable_of_iff _ Finmap.ext_iff.symm

/-! ### lookup -/

/-- Look up the value associated to a key in a map. -/
/-
**Finmap.lookup** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：lookup (a : α) (s : Finmap β) : Option (β a)
参数：a : α；s : Finmap β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AList.perm_lookup`：perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries
 ~ s₂.entries) : s₁.lookup a = s₂.lookup a

--- 原说明 ---
Look up the value associated to a key in a map.
-/
def lookup (a : α) (s : Finmap β) : Option (β a) :=
  liftOn s (AList.lookup a) fun _ _ => perm_lookup

@[simp]
/-
**Finmap.lookup_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_toFinmap (a : α) (s : AList β) : lookup a ⟦s⟧ = s.lookup a
参数：a : α；s : AList β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookup_toFinmap (a : α) (s : AList β) : lookup a ⟦s⟧ = s.lookup a :=
  rfl

@[simp]
/-
**Finmap.dlookup_list_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：dlookup_list_toFinmap (a : α) (s : List (Sigma β)) : lookup a s.toFinmap =
 s.dlookup a
参数：a : α；s : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toFinmap.eq_1`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq 
α] (s : List (Sigma β)), s.toFinmap = s.toAList.toFinmap
· 使用定理 `Finmap.lookup_toFinmap`：lookup_toFinmap (a : α) (s : AList β) : lookup a
 ⟦s⟧ = s.lookup a
· 使用定理 `AList.lookup_to_alist`：lookup_to_alist {a} (s : List (Sigma β)) : lookup
 a s.toAList = s.dlookup a
-/
theorem dlookup_list_toFinmap (a : α) (s : List (Sigma β)) : lookup a s.toFinmap = s.dlookup a := by
  rw [List.toFinmap, lookup_toFinmap, lookup_to_alist]

@[simp]
/-
**Finmap.lookup_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_empty (a) : lookup a (∅ : Finmap β) = none
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookup_empty (a) : lookup a (∅ : Finmap β) = none :=
  rfl
/-
**Finmap.lookup_isSome** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_isSome {a : α} {s : Finmap β} : (s.lookup a).isSome ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.lookup_isSome`：lookup_isSome {a : α} {s : AList β} : (s.lookup a).
isSome ↔ a in s
· 使用定理 `AList.perm_lookup`：perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries
 ~ s₂.entries) : s₁.lookup a = s₂.lookup a
-/
theorem lookup_isSome {a : α} {s : Finmap β} : (s.lookup a).isSome ↔ a ∈ s :=
  induction_on s fun _ => AList.lookup_isSome
/-
**Finmap.lookup_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_eq_none {a} {s : Finmap β} : lookup a s = none ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.lookup_eq_none`：lookup_eq_none {a : α} {s : AList β} : lookup a s 
= none ↔ a ∉ s
· 使用定理 `AList.perm_lookup`：perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries
 ~ s₂.entries) : s₁.lookup a = s₂.lookup a
-/
theorem lookup_eq_none {a} {s : Finmap β} : lookup a s = none ↔ a ∉ s :=
  induction_on s fun _ => AList.lookup_eq_none
/-
**Finmap.mem_lookup_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finmap`。
形式化陈述：mem_lookup_iff {s : Finmap β} {a : α} {b : β a} : b in s.lookup a ↔ Sigma.
mk a b in s.entries
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dlookup_iff`：mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma
 β)} (nd : l.NodupKeys) : b in dlookup a l ↔ Sigma.mk a b in l
· 使用定理 `AList.perm_lookup`：perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries
 ~ s₂.entries) : s₁.lookup a = s₂.lookup a
-/
lemma mem_lookup_iff {s : Finmap β} {a : α} {b : β a} :
    b ∈ s.lookup a ↔ Sigma.mk a b ∈ s.entries := by
  rcases s with ⟨⟨l⟩, hl⟩; exact List.mem_dlookup_iff hl
/-
**Finmap.lookup_eq_some_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finmap`。
形式化陈述：lookup_eq_some_iff {s : Finmap β} {a : α} {b : β a} : s.lookup a = b ↔ Sig
ma.mk a b in s.entries
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finmap.mem_lookup_iff`：mem_lookup_iff {s : Finmap β} {a : α} {b : β a} :
 b in s.lookup a ↔ Sigma.mk a b in s.entries
-/
lemma lookup_eq_some_iff {s : Finmap β} {a : α} {b : β a} :
    s.lookup a = b ↔ Sigma.mk a b ∈ s.entries := mem_lookup_iff
/-
**Finmap.sigma_keys_lookup** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (s : Finmap β),   (
s.keys.sigma fun i => (Finmap.lookup i s).toFinset) = { val := s.entries, nodup 
:= ⋯ }
参数：s : Finmap β；s.keys.sigma fun i => (Finmap.lookup i s).toFinset。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `Finmap.nodup_entries`：nodup_entries (f : Finmap β) : f.entries.Nodup
· 使用定理 `Multiset.mem_map_of_mem`：mem_map_of_mem (f : α -> β) {a : α} {s : Multis
et α} (h : a in s) : f a in map f s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
-/
@[simp] lemma sigma_keys_lookup (s : Finmap β) :
    s.keys.sigma (fun i => (s.lookup i).toFinset) = ⟨s.entries, s.nodup_entries⟩ := by
  ext x
  have : x ∈ s.entries → x.1 ∈ s.keys := Multiset.mem_map_of_mem _
  simpa [lookup_eq_some_iff]

@[simp]
/-
**Finmap.lookup_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_singleton_eq {a : α} {b : β a} : (singleton a b).lookup a = some b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.singleton.eq_1`：∀ {α : Type u} {β : α → Type v} (a : α) (b : β a)
, Finmap.singleton a b = (AList.singleton a b).toFinmap
· 使用定理 `Finmap.lookup_toFinmap`：lookup_toFinmap (a : α) (s : AList β) : lookup a
 ⟦s⟧ = s.lookup a
· 使用定理 `AList.singleton.eq_1`：∀ {α : Type u} {β : α → Type v} (a : α) (b : β a),
 AList.singleton a b = { entries := [⟨a, b⟩], nodupKeys := ⋯ }
· 使用定理 `AList.lookup.eq_1`：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α
] (a : α) (s : AList β),   AList.lookup a s = List.dlookup a s.entries
· 使用定理 `List.dlookup_cons_eq`：dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a 
(⟨a, b⟩ :: l) = some b
-/
theorem lookup_singleton_eq {a : α} {b : β a} : (singleton a b).lookup a = some b := by
  rw [singleton, lookup_toFinmap, AList.singleton, AList.lookup, dlookup_cons_eq]
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : α) (s : Finmap β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome
/-
**Finmap.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_iff {a : α} {s : Finmap β} : a in s ↔ exists b, s.lookup a = some b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.mem_keys`：mem_keys {a} {l : List (Sigma β)} : a in l.keys ↔ exists 
b : β a, Sigma.mk a b in l
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.mem_dlookup_iff`：mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma
 β)} (nd : l.NodupKeys) : b in dlookup a l ↔ Sigma.mk a b in l
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
-/
theorem mem_iff {a : α} {s : Finmap β} : a ∈ s ↔ ∃ b, s.lookup a = some b :=
  induction_on s fun s =>
    Iff.trans List.mem_keys <| exists_congr fun _ => (mem_dlookup_iff s.nodupKeys).symm
/-
**Finmap.mem_of_lookup_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_of_lookup_eq_some {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = s
ome b) : a in s
参数：h : s.lookup a = some b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finmap.mem_iff`：mem_iff {a : α} {s : Finmap β} : a in s ↔ exists b, s.lo
okup a = some b
-/
theorem mem_of_lookup_eq_some {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b) : a ∈ s :=
  mem_iff.mpr ⟨_, h⟩
/-
**Finmap.ext_lookup** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：ext_lookup {s₁ s₂ : Finmap β} : (forall x, s₁.lookup x = s₂.lookup x) -> s
₁ = s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.toFinmap_eq`：AList.toFinmap_eq {s₁ s₂ : AList β} : toFinmap s₁ = t
oFinmap s₂ ↔ s₁.entries ~ s₂.entries
· 使用定理 `List.lookup_ext`：lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys
) (nd₁ : l₁.NodupKeys) (h : forall x y, y in l₀.dlookup x ↔ y in l₁.dlookup x) :
 l₀ ~…
· 使用定理 `AList.nodupKeys`：∀ {α : Type u} {β : α → Type v} (self : AList β), self.
entries.NodupKeys
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ext_lookup {s₁ s₂ : Finmap β} : (∀ x, s₁.lookup x = s₂.lookup x) → s₁ = s₂ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ h => by
    simp only [AList.lookup, lookup_toFinmap] at h
    rw [AList.toFinmap_eq]
    apply lookup_ext s₁.nodupKeys s₂.nodupKeys
    intro x y
    rw [h]

/-- An equivalence between `Finmap β` and pairs `(keys : Finset α, lookup : ∀ a, Option (β a))` such
that `(lookup a).isSome ↔ a ∈ keys`. -/
@[simps apply_coe_fst apply_coe_snd]
/-
**Finmap.keysLookupEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：keysLookupEquiv : Finmap β ≃ { f : Finset α × (forall a, Option (β a)) // 
forall i, (f.2 i).isSome ↔ i in f.1 } where toFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.lookup_isSome`：lookup_isSome {a : α} {s : Finmap β} : (s.lookup a
).isSome ↔ a in s

--- 原说明 ---
An equivalence between `Finmap β` and pairs `(keys : Finset α, lookup : ∀ a, Opt
ion (β a))` such
that `(lookup a).isSome ↔ a ∈ keys`.
-/
def keysLookupEquiv :
    Finmap β ≃ { f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1 } where
  toFun s := ⟨(s.keys, fun i => s.lookup i), fun _ => lookup_isSome⟩
  invFun f := mk (f.1.1.sigma fun i => (f.1.2 i).toFinset).val <| by
    refine Multiset.nodup_keys.1 ((Finset.nodup _).map_on ?_)
    simp only [Finset.mem_val, Finset.mem_sigma, Option.mem_toFinset, Option.mem_def]
    rintro ⟨i, x⟩ ⟨_, hx⟩ ⟨j, y⟩ ⟨_, hy⟩ (rfl : i = j)
    simpa using hx.symm.trans hy
  left_inv f := ext <| by simp
  right_inv := fun ⟨(s, f), hf⟩ => by
    dsimp only at hf
    ext
    · simp [keys, Multiset.keys, ← hf, Option.isSome_iff_exists]
    · simp +contextual [lookup_eq_some_iff, ← hf]
/-
**Finmap.keysLookupEquiv_symm_apply_keys** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (f : { f // ∀ (i : 
α), (f.2 i).isSome = true ↔ i ∈ f.1 }),   (Finmap.keysLookupEquiv.symm f).keys =
 (↑f).1
参数：f : { f // ∀ (i : α), (f.2 i).isSome = true ↔ i ∈ f.1 }；Finmap.keysLookupEqui
v.symm f；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Finmap.keysLookupEquiv_apply_coe_fst`：∀ {α : Type u} {β : α → Type v} [i
nst : DecidableEq α] (s : Finmap β), (↑(Finmap.keysLookupEquiv s)).1 = s.keys
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma keysLookupEquiv_symm_apply_keys :
    ∀ f : {f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1},
      (keysLookupEquiv.symm f).keys = f.1.1 :=
  keysLookupEquiv.surjective.forall.2 fun _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_fst]
/-
**Finmap.keysLookupEquiv_symm_apply_lookup** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：∀ {α : Type u} {β : α → Type v} [inst : DecidableEq α] (f : { f // ∀ (i : 
α), (f.2 i).isSome = true ↔ i ∈ f.1 })   (a : α), Finmap.lookup a (Finmap.keysLo
okupEquiv.symm f) = (↑f).2 a
参数：f : { f // ∀ (i : α), (f.2 i).isSome = true ↔ i ∈ f.1 }；a : α；Finmap.keysLook
upEquiv.symm f；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup.congr_simp`：∀ {α : Type u} {β : α → Type v} {inst : Decida
bleEq α} [inst_1 : DecidableEq α] (a : α) (s s_1 : Finmap β),   s = s_1 → Finmap
.lookup a s = …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Finmap.keysLookupEquiv_apply_coe_snd`：∀ {α : Type u} {β : α → Type v} [i
nst : DecidableEq α] (s : Finmap β) (i : α),   (↑(Finmap.keysLookupEquiv s)).2 i
 = Finmap.lookup i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma keysLookupEquiv_symm_apply_lookup :
    ∀ (f : {f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1}) a,
      (keysLookupEquiv.symm f).lookup a = f.1.2 a :=
  keysLookupEquiv.surjective.forall.2 fun _ _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_snd]

/-! ### replace -/

/-- Replace a key with a given value in a finite map.
  If the key is not present it does nothing. -/
/-
**Finmap.replace** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：replace (a : α) (b : β a) (s : Finmap β) : Finmap β
参数：a : α；b : β a；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace a key with a given value in a finite map.
  If the key is not present it does nothing.
-/
def replace (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.replace a b t))
    fun _ _ p => toFinmap_eq.2 <| perm_replace p

@[simp]
/-
**Finmap.replace_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：replace_toFinmap (a : α) (b : β a) (s : AList β) : replace a b ⟦s⟧ = (⟦s.r
eplace a b⟧ : Finmap β)
参数：a : α；b : β a；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.liftOn_toFinmap`：liftOn_toFinmap {γ} (s : AList β) (f : AList β -
> γ) (H) : liftOn ⟦s⟧ f H = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem replace_toFinmap (a : α) (b : β a) (s : AList β) :
    replace a b ⟦s⟧ = (⟦s.replace a b⟧ : Finmap β) := by
  simp [replace]

@[simp]
/-
**Finmap.keys_replace** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_replace (a : α) (b : β a) (s : Finmap β) : (replace a b s).keys = s.k
eys
参数：a : α；b : β a；s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.replace_toFinmap`：replace_toFinmap (a : α) (b : β a) (s : AList β
) : replace a b ⟦s⟧ = (⟦s.replace a b⟧ : Finmap β)
· 使用定理 `AList.keys_replace`：keys_replace (a : α) (b : β a) (s : AList β) : (repl
ace a b s).keys = s.keys
-/
theorem keys_replace (a : α) (b : β a) (s : Finmap β) : (replace a b s).keys = s.keys :=
  induction_on s fun s => by simp

@[simp]
/-
**Finmap.mem_replace** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_replace {a a' : α} {b : β a} {s : Finmap β} : a' in replace a b s ↔ a'
 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finmap.replace_toFinmap`：replace_toFinmap (a : α) (b : β a) (s : AList β
) : replace a b ⟦s⟧ = (⟦s.replace a b⟧ : Finmap β)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_replace {a a' : α} {b : β a} {s : Finmap β} : a' ∈ replace a b s ↔ a' ∈ s :=
  induction_on s fun s => by simp

end

/-! ### foldl -/

/-- Fold a commutative function over the key-value pairs in the map -/
/-
**Finmap.foldl** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：foldl {δ : Type w} (f : δ -> forall a, β a -> δ) (H : forall d a₁ b₁ a₂ b₂
, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) (d : δ) (m : Finmap β) : δ
参数：f : δ -> forall a, β a -> δ；H : forall d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f
 (f d a₂ b₂) a₁ b₁；d : δ；m : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fold a commutative function over the key-value pairs in the map
-/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ)
    (H : ∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) (d : δ) (m : Finmap β) : δ :=
  letI : RightCommutative fun d (s : Sigma β) ↦ f d s.1 s.2 := ⟨fun _ _ _ ↦ H _ _ _ _ _⟩
  m.entries.foldl (fun d s => f d s.1 s.2) d

/-- `any f s` returns `true` iff there exists a value `v` in `s` such that `f v = true`. -/
/-
**Finmap.any** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：any (f : forall x, β x -> Bool) (s : Finmap β) : Bool
参数：f : forall x, β x -> Bool；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`any f s` returns `true` iff there exists a value `v` in `s` such that `f v = tr
ue`.
-/
def any (f : ∀ x, β x → Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x || f y z)
    (fun _ _ _ _ => by simp_rw [Bool.or_assoc, Bool.or_comm, imp_true_iff]) false

/-- `all f s` returns `true` iff `f v = true` for all values `v` in `s`. -/
/-
**Finmap.all** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：all (f : forall x, β x -> Bool) (s : Finmap β) : Bool
参数：f : forall x, β x -> Bool；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`all f s` returns `true` iff `f v = true` for all values `v` in `s`.
-/
def all (f : ∀ x, β x → Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x && f y z)
    (fun _ _ _ _ => by simp_rw [Bool.and_assoc, Bool.and_comm, imp_true_iff]) true

/-! ### erase -/

section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present it does nothing. -/
/-
**Finmap.erase** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：erase (a : α) (s : Finmap β) : Finmap β
参数：a : α；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Erase a key from the map. If the key is not present it does nothing.
-/
def erase (a : α) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.erase a t)) fun _ _ p => toFinmap_eq.2 <| perm_erase p

@[simp]
/-
**Finmap.erase_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：erase_toFinmap (a : α) (s : AList β) : erase a ⟦s⟧ = AList.toFinmap (s.era
se a)
参数：a : α；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.liftOn_toFinmap`：liftOn_toFinmap {γ} (s : AList β) (f : AList β -
> γ) (H) : liftOn ⟦s⟧ f H = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_toFinmap (a : α) (s : AList β) : erase a ⟦s⟧ = AList.toFinmap (s.erase a) := by
  simp [erase]

@[simp]
/-
**Finmap.keys_erase_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_erase_toFinset (a : α) (s : AList β) : keys ⟦s.erase a⟧ = (keys ⟦s⟧).
erase a
参数：a : α；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.keys_kerase`：keys_kerase {a} {l : List (Sigma β)} : (kerase a l).ke
ys = l.keys.erase a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mk.congr_simp`：∀ {α : Type u_4} (val val_1 : Multiset α) (e_val :
 val = val_1) (nodup : val.Nodup),   { val := val, nodup := nodup } = { val := v
al_1, nodu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem keys_erase_toFinset (a : α) (s : AList β) : keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a := by
  simp [Finset.erase, keys, AList.erase, keys_kerase]

@[simp]
/-
**Finmap.keys_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_erase (a : α) (s : Finmap β) : (erase a s).keys = s.keys.erase a
参数：a : α；s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.erase_toFinmap`：erase_toFinmap (a : α) (s : AList β) : erase a ⟦s
⟧ = AList.toFinmap (s.erase a)
· 使用定理 `Finmap.keys_erase_toFinset`：keys_erase_toFinset (a : α) (s : AList β) : 
keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem keys_erase (a : α) (s : Finmap β) : (erase a s).keys = s.keys.erase a :=
  induction_on s fun s => by simp

@[simp]
/-
**Finmap.mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_erase {a a' : α} {s : Finmap β} : a' in erase a s ↔ a' != a ∧ a' in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finmap.erase_toFinmap`：erase_toFinmap (a : α) (s : AList β) : erase a ⟦s
⟧ = AList.toFinmap (s.erase a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_erase {a a' : α} {s : Finmap β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
  induction_on s fun s => by simp
/-
**Finmap.notMem_erase_self** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：notMem_erase_self {a : α} {s : Finmap β} : a ∉ erase a s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.mem_erase`：mem_erase {a a' : α} {s : Finmap β} : a' in erase a s 
↔ a' != a ∧ a' in s
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem notMem_erase_self {a : α} {s : Finmap β} : a ∉ erase a s := by
  rw [mem_erase, not_and_or, not_not]
  left
  rfl

@[simp]
/-
**Finmap.lookup_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_erase (a) (s : Finmap β) : lookup a (erase a s) = none
参数：a；s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.lookup_erase`：lookup_erase (a) (s : AList β) : lookup a (erase a s
) = none
-/
theorem lookup_erase (a) (s : Finmap β) : lookup a (erase a s) = none :=
  induction_on s <| AList.lookup_erase a

@[simp]
/-
**Finmap.lookup_erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_erase_ne {a a'} {s : Finmap β} (h : a != a') : lookup a (erase a' s
) = lookup a s
参数：h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.lookup_erase_ne`：lookup_erase_ne {a a'} {s : AList β} (h : a != a'
) : lookup a (erase a' s) = lookup a s
-/
theorem lookup_erase_ne {a a'} {s : Finmap β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  induction_on s fun _ => AList.lookup_erase_ne h
/-
**Finmap.erase_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：erase_erase {a a' : α} {s : Finmap β} : erase a (erase a' s) = erase a' (e
rase a s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `Finmap.ext`：∀ {α : Type u} {β : α → Type v} {s t : Finmap β}, s.entries 
= t.entries → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.erase_toFinmap`：erase_toFinmap (a : α) (s : AList β) : erase a ⟦s
⟧ = AList.toFinmap (s.erase a)
· 使用定理 `AList.erase_erase`：erase_erase (a a' : α) (s : AList β) : (s.erase a).er
ase a' = (s.erase a').erase a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_erase {a a' : α} {s : Finmap β} : erase a (erase a' s) = erase a' (erase a s) :=
  induction_on s fun s => ext (by simp only [AList.erase_erase, erase_toFinmap])

/-! ### sdiff -/

/-- `sdiff s s'` consists of all key-value pairs from `s` and `s'` where the keys are in `s` or
`s'` but not both. -/
/-
**Finmap.sdiff** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：sdiff (s s' : Finmap β) : Finmap β
参数：s s' : Finmap β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.erase_erase`：erase_erase {a a' : α} {s : Finmap β} : erase a (era
se a' s) = erase a' (erase a s)

--- 原说明 ---
`sdiff s s'` consists of all key-value pairs from `s` and `s'` where the keys ar
e in `s` or
`s'` but not both.
-/
def sdiff (s s' : Finmap β) : Finmap β :=
  s'.foldl (fun s x _ => s.erase x) (fun _ _ _ _ _ => erase_erase) s
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SDiff (Finmap β) :=
  ⟨sdiff⟩

/-! ### insert -/

/-- Insert a key-value pair into a finite map, replacing any existing pair with
  the same key. -/
/-
**Finmap.insert** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：insert (a : α) (b : β a) (s : Finmap β) : Finmap β
参数：a : α；b : β a；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert a key-value pair into a finite map, replacing any existing pair with
  the same key.
-/
def insert (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.insert a b t)) fun _ _ p =>
    toFinmap_eq.2 <| perm_insert p

@[simp]
/-
**Finmap.insert_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：insert_toFinmap (a : α) (b : β a) (s : AList β) : insert a b (AList.toFinm
ap s) = AList.toFinmap (s.insert a b)
参数：a : α；b : β a；s : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.liftOn_toFinmap`：liftOn_toFinmap {γ} (s : AList β) (f : AList β -
> γ) (H) : liftOn ⟦s⟧ f H = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_toFinmap (a : α) (b : β a) (s : AList β) :
    insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b) := by
  simp [insert]
/-
**Finmap.entries_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：entries_insert_of_notMem {a : α} {b : β a} {s : Finmap β} : a ∉ s -> (inse
rt a b s).entries = ⟨a, b⟩ ::ₘ s.entries
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.entries_insert_of_notMem`：entries_insert_of_notMem {a} {b : β a} {
s : AList β} (h : a ∉ s) : (insert a b s).entries = ⟨a, b⟩ :: s.entries
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finmap.mem_toFinmap`：mem_toFinmap {a : α} {s : AList β} : a in toFinmap 
s ↔ a in s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem entries_insert_of_notMem {a : α} {b : β a} {s : Finmap β} :
    a ∉ s → (insert a b s).entries = ⟨a, b⟩ ::ₘ s.entries :=
  induction_on s fun s h => by
    simp [AList.entries_insert_of_notMem (mt mem_toFinmap.1 h), -entries_insert]

@[simp]
/-
**Finmap.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_insert {a a' : α} {b' : β a'} {s : Finmap β} : a in insert a' b' s ↔ a
 = a' ∨ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `AList.mem_insert`：mem_insert {a a'} {b' : β a'} (s : AList β) : a in ins
ert a' b' s ↔ a = a' ∨ a in s
-/
theorem mem_insert {a a' : α} {b' : β a'} {s : Finmap β} : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  induction_on s AList.mem_insert

@[simp]
/-
**Finmap.lookup_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_insert {a} {b : β a} (s : Finmap β) : lookup a (insert a b s) = som
e b
参数：s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup.congr_simp`：∀ {α : Type u} {β : α → Type v} {inst : Decida
bleEq α} [inst_1 : DecidableEq α] (a : α) (s s_1 : Finmap β),   s = s_1 → Finmap
.lookup a s = …
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.lookup_insert`：lookup_insert {a} {b : β a} (s : AList β) : lookup 
a (insert a b s) = some b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lookup_insert {a} {b : β a} (s : Finmap β) : lookup a (insert a b s) = some b :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, AList.lookup_insert]

@[simp]
/-
**Finmap.lookup_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_insert_of_ne {a a'} {b : β a} (s : Finmap β) (h : a' != a) : lookup
 a' (insert a b s) = lookup a' s
参数：s : Finmap β；h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup.congr_simp`：∀ {α : Type u} {β : α → Type v} {inst : Decida
bleEq α} [inst_1 : DecidableEq α] (a : α) (s s_1 : Finmap β),   s = s_1 → Finmap
.lookup a s = …
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.lookup_insert_ne`：lookup_insert_ne {a a'} {b' : β a'} {s : AList β
} (h : a != a') : lookup a (insert a' b' s) = lookup a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lookup_insert_of_ne {a a'} {b : β a} (s : Finmap β) (h : a' ≠ a) :
    lookup a' (insert a b s) = lookup a' s :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, lookup_insert_ne h]

@[simp]
/-
**Finmap.insert_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：insert_insert {a} {b b' : β a} (s : Finmap β) : (s.insert a b).insert a b'
 = s.insert a b'
参数：s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.insert_insert`：insert_insert {a} {b b' : β a} (s : AList β) : (s.i
nsert a b).insert a b' = s.insert a b'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_insert {a} {b b' : β a} (s : Finmap β) :
    (s.insert a b).insert a b' = s.insert a b' :=
  induction_on s fun s => by simp only [insert_toFinmap, AList.insert_insert]
/-
**Finmap.insert_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a != 
a') : (s.insert a b).insert a' b' = (s.insert a' b').insert a b
参数：s : Finmap β；h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AList.insert_insert_of_ne`：insert_insert_of_ne {a a'} {b : β a} {b' : β 
a'} (s : AList β) (h : a != a') : ((s.insert a b).insert a' b').entries ~ ((s.in
sert a' b').ins…
-/
theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a ≠ a') :
    (s.insert a b).insert a' b' = (s.insert a' b').insert a b :=
  induction_on s fun s => by
    simp only [insert_toFinmap, AList.toFinmap_eq, AList.insert_insert_of_ne _ h]
/-
**Finmap.toFinmap_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：toFinmap_cons (a : α) (b : β a) (xs : List (Sigma β)) : List.toFinmap (⟨a,
 b⟩ :: xs) = insert a b xs.toFinmap
参数：a : α；b : β a；xs : List (Sigma β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinmap_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toFinmap (⟨a, b⟩ :: xs) = insert a b xs.toFinmap :=
  rfl
/-
**Finmap.mem_list_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_list_toFinmap (a : α) (xs : List (Sigma β)) : a in xs.toFinmap ↔ exist
s b : β a, Sigma.mk a b in xs
参数：a : α；xs : List (Sigma β)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `or_congr_left`：∀ {a b c : Prop}, (a ↔ b) → (a ∨ c ↔ b ∨ c)
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
-/
theorem mem_list_toFinmap (a : α) (xs : List (Sigma β)) :
    a ∈ xs.toFinmap ↔ ∃ b : β a, Sigma.mk a b ∈ xs := by
  induction xs with
  | nil => simp only [toFinmap_nil, notMem_empty, not_mem_nil, exists_false]
  | cons x xs =>
    obtain ⟨fst_i, snd_i⟩ := x
    simp only [toFinmap_cons, *, exists_or, mem_cons, mem_insert, exists_and_left, Sigma.mk.inj_iff]
    refine (or_congr_left <| and_iff_left_of_imp ?_).symm
    rintro rfl
    simp only [exists_eq, heq_iff_eq]

@[simp]
/-
**Finmap.insert_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = s
ingleton a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.insert_singleton_eq`：insert_singleton_eq {a : α} {b b' : β a} : in
sert a b (singleton a b') = singleton a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b := by
  simp only [singleton, Finmap.insert_toFinmap, AList.insert_singleton_eq]

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
/-
**Finmap.extract** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：extract (a : α) (s : Finmap β) : Option (β a) × Finmap β
参数：a : α；s : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Erase a key from the map, and return the corresponding value, if found.
-/
def extract (a : α) (s : Finmap β) : Option (β a) × Finmap β :=
  (liftOn s fun t => Prod.map id AList.toFinmap (AList.extract a t)) fun s₁ s₂ p => by
    simp [perm_lookup p, toFinmap_eq, perm_erase p]

@[simp]
/-
**Finmap.extract_eq_lookup_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：extract_eq_lookup_erase (a : α) (s : Finmap β) : extract a s = (lookup a s
, erase a s)
参数：a : α；s : Finmap β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AList.extract_eq_lookup_erase`：extract_eq_lookup_erase (a : α) (s : ALis
t β) : extract a s = (lookup a s, erase a s)
· 使用定理 `Finmap.liftOn.congr_simp`：∀ {α : Type u} {β : α → Type v} {γ : Type u_1}
 (s s_1 : Finmap β),   s = s_1 →     ∀ (f f_1 : AList β → γ) (e_f : f = f_1) (H 
: ∀ (a b : ALi…
· 使用定理 `Finmap.liftOn_toFinmap`：liftOn_toFinmap {γ} (s : AList β) (f : AList β -
> γ) (H) : liftOn ⟦s⟧ f H = f s
· 使用定理 `Finmap.erase_toFinmap`：erase_toFinmap (a : α) (s : AList β) : erase a ⟦s
⟧ = AList.toFinmap (s.erase a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extract_eq_lookup_erase (a : α) (s : Finmap β) : extract a s = (lookup a s, erase a s) :=
  induction_on s fun s => by simp [extract]

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two finite maps. It is left-biased: if
there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`. -/
/-
**Finmap.union** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：union (s₁ s₂ : Finmap β) : Finmap β
参数：s₁ s₂ : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s₁ ∪ s₂` is the key-based union of two finite maps. It is left-biased: if
there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : Finmap β) : Finmap β :=
  (liftOn₂ s₁ s₂ fun s₁ s₂ => (AList.toFinmap (s₁ ∪ s₂))) fun _ _ _ _ p₁₃ p₂₄ =>
    toFinmap_eq.mpr <| perm_union p₁₃ p₂₄
/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Union (Finmap β) :=
  ⟨union⟩

@[simp]
/-
**Finmap.mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_union {a} {s₁ s₂ : Finmap β} : a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `AList.mem_union`：mem_union {a} {s₁ s₂ : AList β} : a in s₁ union s₂ ↔ a 
in s₁ ∨ a in s₂
-/
theorem mem_union {a} {s₁ s₂ : Finmap β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_union

@[simp]
/-
**Finmap.union_toFinmap** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) union (toFinmap s₂) = toF
inmap (s₁ union s₂)
参数：s₁ s₂ : AList β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) ∪ (toFinmap s₂) = toFinmap (s₁ ∪ s₂) := by
  simp [(· ∪ ·), union]
/-
**Finmap.keys_union** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：keys_union {s₁ s₂ : Finmap β} : (s₁ union s₂).keys = s₁.keys union s₂.keys
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mk.congr_simp`：∀ {α : Type u_4} (val val_1 : Multiset α) (e_val :
 val = val_1) (nodup : val.Nodup),   { val := val, nodup := nodup } = { val := v
al_1, nodu…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem keys_union {s₁ s₂ : Finmap β} : (s₁ ∪ s₂).keys = s₁.keys ∪ s₂.keys :=
  induction_on₂ s₁ s₂ fun s₁ s₂ => Finset.ext <| by simp [keys]

@[simp]
/-
**Finmap.lookup_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_union_left {a} {s₁ s₂ : Finmap β} : a in s₁ -> lookup a (s₁ union s
₂) = lookup a s₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `AList.lookup_union_left`：lookup_union_left {a} {s₁ s₂ : AList β} : a in 
s₁ -> lookup a (s₁ union s₂) = lookup a s₁
-/
theorem lookup_union_left {a} {s₁ s₂ : Finmap β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_left

@[simp]
/-
**Finmap.lookup_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_union_right {a} {s₁ s₂ : Finmap β} : a ∉ s₁ -> lookup a (s₁ union s
₂) = lookup a s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `AList.lookup_union_right`：lookup_union_right {a} {s₁ s₂ : AList β} : a ∉
 s₁ -> lookup a (s₁ union s₂) = lookup a s₂
-/
theorem lookup_union_right {a} {s₁ s₂ : Finmap β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_right
/-
**Finmap.lookup_union_left_of_not_in** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：lookup_union_left_of_not_in {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂) : lookup a
 (s₁ union s₂) = lookup a s₁
参数：h : a ∉ s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup_union_left`：lookup_union_left {a} {s₁ s₂ : Finmap β} : a i
n s₁ -> lookup a (s₁ union s₂) = lookup a s₁
· 使用定理 `Finmap.lookup_union_right`：lookup_union_right {a} {s₁ s₂ : Finmap β} : a
 ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finmap.lookup_eq_none`：lookup_eq_none {a} {s : Finmap β} : lookup a s = 
none ↔ a ∉ s
-/
theorem lookup_union_left_of_not_in {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂) :
    lookup a (s₁ ∪ s₂) = lookup a s₁ := by
  by_cases h' : a ∈ s₁
  · rw [lookup_union_left h']
  · rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h']

/-- `simp`-normal form of `mem_lookup_union` -/
@[simp]
/-
**Finmap.mem_lookup_union'** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_lookup_union' {a} {b : β a} {s₁ s₂ : Finmap β} : lookup a (s₁ union s₂
) = some b ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `AList.mem_lookup_union`：mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β}
 : b in lookup a (s₁ union s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂

--- 原说明 ---
`simp`-normal form of `mem_lookup_union`
-/
theorem mem_lookup_union' {a} {b : β a} {s₁ s₂ : Finmap β} :
    lookup a (s₁ ∪ s₂) = some b ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union
/-
**Finmap.mem_lookup_union** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_lookup_union {a} {b : β a} {s₁ s₂ : Finmap β} : b in lookup a (s₁ unio
n s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `AList.mem_lookup_union`：mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β}
 : b in lookup a (s₁ union s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂
-/
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : Finmap β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union
/-
**Finmap.mem_lookup_union_middle** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Finmap β} : b in lookup 
a (s₁ union s₃) -> a ∉ s₂ -> b in lookup a (s₁ union s₂ union s₃)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₃`：induction_on₃ {C : Finmap β -> Finmap β -> Finmap 
β -> Prop} (s₁ s₂ s₃ : Finmap β) (H : forall a₁ a₂ a₃ : AList β, C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃
⟧) : C s₁ …
· 使用定理 `AList.mem_lookup_union_middle`：mem_lookup_union_middle {a} {b : β a} {s₁
 s₂ s₃ : AList β} : b in lookup a (s₁ union s₃) -> a ∉ s₂ -> b in lookup a (s₁ u
nion s₂ union s₃)
-/
theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Finmap β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  induction_on₃ s₁ s₂ s₃ fun _ _ _ => AList.mem_lookup_union_middle
/-
**Finmap.insert_union** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：insert_union {a} {b : β a} {s₁ s₂ : Finmap β} : insert a b (s₁ union s₂) =
 insert a b s₁ union s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
· 使用定理 `Finmap.insert_toFinmap`：insert_toFinmap (a : α) (b : β a) (s : AList β) 
: insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b)
· 使用定理 `AList.insert_union`：insert_union {a} {b : β a} {s₁ s₂ : AList β} : inser
t a b (s₁ union s₂) = insert a b s₁ union s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_union {a} {b : β a} {s₁ s₂ : Finmap β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  induction_on₂ s₁ s₂ fun a₁ a₂ => by simp [AList.insert_union]
/-
**Finmap.union_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：union_assoc {s₁ s₂ s₃ : Finmap β} : s₁ union s₂ union s₃ = s₁ union (s₂ un
ion s₃)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₃`：induction_on₃ {C : Finmap β -> Finmap β -> Finmap 
β -> Prop} (s₁ s₂ s₃ : Finmap β) (H : forall a₁ a₂ a₃ : AList β, C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃
⟧) : C s₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
-/
theorem union_assoc {s₁ s₂ s₃ : Finmap β} : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  induction_on₃ s₁ s₂ s₃ fun s₁ s₂ s₃ => by
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_assoc]

@[simp]
/-
**Finmap.empty_union** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：empty_union {s₁ : Finmap β} : ∅ union s₁ = s₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finmap.empty_toFinmap`：empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
· 使用定理 `AList.empty_union`：empty_union {s : AList β} : (∅ : AList β) union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem empty_union {s₁ : Finmap β} : ∅ ∪ s₁ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

@[simp]
/-
**Finmap.union_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：union_empty {s₁ : Finmap β} : s₁ union ∅ = s₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on`：induction_on {C : Finmap β -> Prop} (s : Finmap β) 
(H : forall a : AList β, C ⟦a⟧) : C s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finmap.empty_toFinmap`：empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
· 使用定理 `AList.union_empty`：union_empty {s : AList β} : s union (∅ : AList β) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_empty {s₁ : Finmap β} : s₁ ∪ ∅ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]
/-
**Finmap.erase_union_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：erase_union_singleton (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = s
ome b) : s.erase a union singleton a b = s
参数：a : α；b : β a；s : Finmap β；h : s.lookup a = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.ext_lookup`：ext_lookup {s₁ s₂ : Finmap β} : (forall x, s₁.lookup 
x = s₂.lookup x) -> s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup_union_right`：lookup_union_right {a} {s₁ s₂ : Finmap β} : a
 ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
· 使用定理 `Finmap.notMem_erase_self`：notMem_erase_self {a : α} {s : Finmap β} : a ∉
 erase a s
· 使用定理 `Finmap.lookup_singleton_eq`：lookup_singleton_eq {a : α} {b : β a} : (sin
gleton a b).lookup a = some b
· 使用定理 `Finmap.mem_singleton`：mem_singleton (x y : α) (b : β y) : x in singleton
 y b ↔ x = y
· 使用定理 `Finmap.lookup_union_left_of_not_in`：lookup_union_left_of_not_in {a} {s₁ 
s₂ : Finmap β} (h : a ∉ s₂) : lookup a (s₁ union s₂) = lookup a s₁
· 使用定理 `Finmap.lookup_erase_ne`：lookup_erase_ne {a a'} {s : Finmap β} (h : a != 
a') : lookup a (erase a' s) = lookup a s
-/
theorem erase_union_singleton (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = some b) :
    s.erase a ∪ singleton a b = s :=
  ext_lookup fun x => by
    by_cases h' : x = a
    · subst a
      rw [lookup_union_right notMem_erase_self, lookup_singleton_eq, h]
    · have : x ∉ singleton a b := by rwa [mem_singleton]
      rw [lookup_union_left_of_not_in this, lookup_erase_ne h']

end

/-! ### Disjoint -/

/-- `Disjoint s₁ s₂` holds if `s₁` and `s₂` have no keys in common. -/
/-
**Finmap.Disjoint** 是 Mathlib 中的一个定义，位于命名空间 `Finmap`。
形式化陈述：Disjoint (s₁ s₂ : Finmap β) : Prop
参数：s₁ s₂ : Finmap β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Disjoint s₁ s₂` holds if `s₁` and `s₂` have no keys in common.
-/
def Disjoint (s₁ s₂ : Finmap β) : Prop :=
  ∀ x ∈ s₁, x ∉ s₂
/-
**Finmap.disjoint_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：disjoint_empty (x : Finmap β) : Disjoint ∅ x
参数：x : Finmap β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_empty (x : Finmap β) : Disjoint ∅ x :=
  nofun

@[symm]
/-
**Finmap.Disjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `Finmap.Disjoint`。
形式化陈述：∀ {α : Type u} {β : α → Type v} (x y : Finmap β), x.Disjoint y → y.Disjoin
t x
参数：x y : Finmap β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjoint y x := fun p hy hx => h p hx hy
/-
**Finmap.Disjoint.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finmap.Disjoint`。
形式化陈述：∀ {α : Type u} {β : α → Type v} (x y : Finmap β), x.Disjoint y ↔ y.Disjoin
t x
参数：x y : Finmap β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.Disjoint.symm`：∀ {α : Type u} {β : α → Type v} (x y : Finmap β), 
x.Disjoint y → y.Disjoint x
-/
theorem Disjoint.symm_iff (x y : Finmap β) : Disjoint x y ↔ Disjoint y x :=
  ⟨Disjoint.symm x y, Disjoint.symm y x⟩

section

variable [DecidableEq α]

/-
**Finmap.** 是 Mathlib 中的一个实例，位于命名空间 `Finmap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel (@Disjoint α β) :=
  fun s₁ s₂ ↦ inferInstanceAs <| Decidable (∀ x ∈ s₁, x ∉ s₂)
/-
**Finmap.disjoint_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：disjoint_union_left (x y z : Finmap β) : Disjoint (x union y) z ↔ Disjoint
 x z ∧ Disjoint y z
参数：x y z : Finmap β。
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
theorem disjoint_union_left (x y z : Finmap β) :
    Disjoint (x ∪ y) z ↔ Disjoint x z ∧ Disjoint y z := by
  simp [Disjoint, Finmap.mem_union, or_imp, forall_and]
/-
**Finmap.disjoint_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：disjoint_union_right (x y z : Finmap β) : Disjoint x (y union z) ↔ Disjoin
t x y ∧ Disjoint x z
参数：x y z : Finmap β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.Disjoint.symm_iff`：∀ {α : Type u} {β : α → Type v} (x y : Finmap 
β), x.Disjoint y ↔ y.Disjoint x
· 使用定理 `Finmap.disjoint_union_left`：disjoint_union_left (x y z : Finmap β) : Dis
joint (x union y) z ↔ Disjoint x z ∧ Disjoint y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_union_right (x y z : Finmap β) :
    Disjoint x (y ∪ z) ↔ Disjoint x y ∧ Disjoint x z := by
  rw [Disjoint.symm_iff, disjoint_union_left, Disjoint.symm_iff _ x, Disjoint.symm_iff _ x]
/-
**Finmap.union_comm_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：union_comm_of_disjoint {s₁ s₂ : Finmap β} : Disjoint s₁ s₂ -> s₁ union s₂ 
= s₂ union s₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.induction_on₂`：induction_on₂ {C : Finmap β -> Finmap β -> Prop} (
s₁ s₂ : Finmap β) (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.union_toFinmap`：union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) 
union (toFinmap s₂) = toFinmap (s₁ union s₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AList.union_comm_of_disjoint`：union_comm_of_disjoint {s₁ s₂ : AList β} (
h : Disjoint s₁ s₂) : (s₁ union s₂).entries ~ (s₂ union s₁).entries
-/
theorem union_comm_of_disjoint {s₁ s₂ : Finmap β} : Disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ => by
    intro h
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_comm_of_disjoint h]
/-
**Finmap.union_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：union_cancel {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ 
s₃) : s₁ union s₃ = s₂ union s₃ ↔ s₁ = s₂
参数：h : Disjoint s₁ s₃；h' : Disjoint s₂ s₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finmap.ext_lookup`：ext_lookup {s₁ s₂ : Finmap β} : (forall x, s₁.lookup 
x = s₂.lookup x) -> s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finmap.lookup_union_left_of_not_in`：lookup_union_left_of_not_in {a} {s₁ 
s₂ : Finmap β} (h : a ∉ s₂) : lookup a (s₁ union s₂) = lookup a s₁
· 使用定理 `Finmap.lookup_union_left`：lookup_union_left {a} {s₁ s₂ : Finmap β} : a i
n s₁ -> lookup a (s₁ union s₂) = lookup a s₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finmap.lookup_eq_none`：lookup_eq_none {a} {s : Finmap β} : lookup a s = 
none ↔ a ∉ s
-/
theorem union_cancel {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ s₃) :
    s₁ ∪ s₃ = s₂ ∪ s₃ ↔ s₁ = s₂ :=
  ⟨fun h'' => by
    apply ext_lookup
    intro x
    have : (s₁ ∪ s₃).lookup x = (s₂ ∪ s₃).lookup x := h'' ▸ rfl
    by_cases hs₁ : x ∈ s₁
    · rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this
    · by_cases hs₂ : x ∈ s₂
      · rwa [lookup_union_left_of_not_in (h' _ hs₂), lookup_union_left hs₂] at this
      · rw [lookup_eq_none.mpr hs₁, lookup_eq_none.mpr hs₂], fun h => h ▸ rfl⟩

end

end Finmap

