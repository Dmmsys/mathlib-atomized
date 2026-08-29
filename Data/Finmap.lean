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

variable {α : Type u} {β : α -> Type v}

/-! ### Multisets of sigma types -/

namespace Multiset

/--
Definition of `keys` / `keys` 的定义

English:
definition keys
  signature: (s : Multiset (Sigma β))
  body: s.map Sigma.fst

@[simp]

中文:
定义 keys
  签名: (s : Multiset (依赖和类型 β))
  定义体: s.map Sigma.fst

@[simp]

Depends on / 依赖: Sigma.fst, s.map
-/
def keys (s : Multiset (Sigma β)) : Multiset α :=
  s.map Sigma.fst

@[simp]
/--
theorem `coe_keys` / 定理 `coe_keys`

English:
theorem coe_keys
  given: {l : List (Sigma β)}
  statement: keys (l : Multiset (Sigma β)) = (l.keys : Multiset α)
  proof: rfl

@[simp]

中文:
定理 coe_keys
  条件: {l : 列表 (依赖和类型 β)}
  结论: keys (l : Multiset (依赖和类型 β)) = (l.keys : Multiset α)
  证明: rfl

@[simp]
-/
theorem coe_keys {l : List (Sigma β)} : keys (l : Multiset (Sigma β)) = (l.keys : Multiset α) :=
  rfl

@[simp]
/--
theorem `keys_zero` / 定理 `keys_zero`

English:
theorem keys_zero
  statement: keys (0 : Multiset (Sigma β)) = 0
  proof: rfl

@[simp]

中文:
定理 keys_zero
  结论: keys (0 : Multiset (依赖和类型 β)) = 0
  证明: rfl

@[simp]
-/
theorem keys_zero : keys (0 : Multiset (Sigma β)) = 0 := rfl

@[simp]
/--
theorem `keys_cons` / 定理 `keys_cons`

English:
theorem keys_cons
  given: {a : α} {b : β a} {s : Multiset (Sigma β)}
  proof: by
  simp [keys]

@[simp]

中文:
定理 keys_cons
  条件: {a : α} {b : β a} {s : Multiset (依赖和类型 β)}
  证明: by
  simp [keys]

@[simp]
-/
theorem keys_cons {a : α} {b : β a} {s : Multiset (Sigma β)} :
    keys (⟨a, b⟩ ::ₘ s) = a ::ₘ keys s := by
  simp [keys]

@[simp]
/--
theorem `keys_singleton` / 定理 `keys_singleton`

English:
theorem keys_singleton
  given: {a : α} {b : β a}
  statement: keys ({⟨a, b⟩} : Multiset (Sigma β)) = {a}
  proof: rfl

中文:
定理 keys_singleton
  条件: {a : α} {b : β a}
  结论: keys ({⟨a, b⟩} : Multiset (依赖和类型 β)) = {a}
  证明: rfl
-/
theorem keys_singleton {a : α} {b : β a} : keys ({⟨a, b⟩} : Multiset (Sigma β)) = {a} := rfl

/--
Definition of `NodupKeys` / `NodupKeys` 的定义

English:
definition NodupKeys
  signature: (s : Multiset (Sigma β))
  body: Quot.liftOn s List.NodupKeys fun _ _ p => propext perm_nodupKeys p

@[simp]

中文:
定义 NodupKeys
  签名: (s : Multiset (依赖和类型 β))
  定义体: Quot.liftOn s List.NodupKeys fun _ _ p => propext perm_nodupKeys p

@[simp]

Depends on / 依赖: List.NodupKeys, NodupKeys, Quot.liftOn, liftOn, perm_nodupKeys, propext
-/
def NodupKeys (s : Multiset (Sigma β)) : Prop :=
Quot.liftOn s List.NodupKeys fun _ _ p => propext perm_nodupKeys p

@[simp]
/--
theorem `coe_nodupKeys` / 定理 `coe_nodupKeys`

English:
theorem coe_nodupKeys
  given: {l : List (Sigma β)}
  statement: @NodupKeys α β l ↔ l.NodupKeys
  proof: Iff.rfl

中文:
定理 coe_nodupKeys
  条件: {l : 列表 (依赖和类型 β)}
  结论: @NodupKeys α β l ↔ l.NodupKeys
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_nodupKeys {l : List (Sigma β)} : @NodupKeys α β l ↔ l.NodupKeys :=
  Iff.rfl

/--
lemma `nodup_keys` / 引理 `nodup_keys`

English:
lemma nodup_keys
  given: {m : Multiset (Σ a, β a)}
  statement: m.keys.Nodup ↔ m.NodupKeys
  proof: by
  rcases m with ⟨l⟩; rfl

alias ⟨_, NodupKeys.nodup_keys⟩ := nodup_keys

中文:
引理 nodup_keys
  条件: {m : Multiset (Σ a, β a)}
  结论: m.keys.Nodup ↔ m.NodupKeys
  证明: by
  rcases m with ⟨l⟩; rfl

alias ⟨_, NodupKeys.nodup_keys⟩ := nodup_keys
-/
lemma nodup_keys {m : Multiset (Σ a, β a)} : m.keys.Nodup ↔ m.NodupKeys := by
  rcases m with ⟨l⟩; rfl

alias ⟨_, NodupKeys.nodup_keys⟩ := nodup_keys

/--
lemma `NodupKeys.nodup` / 引理 `NodupKeys.nodup`

English:
lemma NodupKeys.nodup
  given: {m : Multiset (Σ a, β a)} (h : m.NodupKeys)
  statement: m.Nodup
  proof: h.nodup_keys.of_map _

中文:
引理 NodupKeys.nodup
  条件: {m : Multiset (Σ a, β a)} (h : m.NodupKeys)
  结论: m.Nodup
  证明: h.nodup_keys.of_map _
-/
protected lemma NodupKeys.nodup {m : Multiset (Σ a, β a)} (h : m.NodupKeys) : m.Nodup :=
  h.nodup_keys.of_map _

end Multiset

/-! ### Finmap -/

/--
Definition of `Finmap` / `Finmap` 的定义

English:
structure Finmap
  parameters: (β : α -> Type v)
  axioms and operations (2):
    - entries : Multiset (Sigma β)
    - nodupKeys : entries.NodupKeys

中文:
结构 Finmap
  参数: (β : α -> 类型v)
  公理与运算 (2 个):
    - entries : Multiset (依赖和类型 β)
    - nodupKeys : entries.NodupKeys
-/
structure Finmap (β : α -> Type v) : Type max u v where
  /-- The underlying `Multiset` of a `Finmap` -/
  entries : Multiset (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/--
Definition of `AList.toFinmap` / `AList.toFinmap` 的定义

English:
definition AList.toFinmap
  signature: (s : AList β)
  body: ⟨s.entries, s.nodupKeys⟩

中文:
定义 AList.toFinmap
  签名: (s : AList β)
  定义体: ⟨s.entries, s.nodupKeys⟩

Depends on / 依赖: entries, nodupKeys, s.entries, s.nodupKeys
-/
def AList.toFinmap (s : AList β) : Finmap β :=
  ⟨s.entries, s.nodupKeys⟩

-- Setting `priority := high` means that Lean will prefer this notation to the identical one
-- for `Quotient.mk`
local notation:arg "⟦" a "⟧" => AList.toFinmap a

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AList.toFinmap_eq` / 定理 `AList.toFinmap_eq`

English:
theorem AList.toFinmap_eq
  given: {s₁ s₂ : AList β}
  proof: by
  cases s₁
  cases s₂
  simp [AList.toFinmap]

@[simp]

中文:
定理 AList.toFinmap_eq
  条件: {s₁ s₂ : AList β}
  证明: by
  cases s₁
  cases s₂
  simp [AList.toFinmap]

@[simp]

Depends on / 依赖: AList.toFinmap, toFinmap
-/
theorem AList.toFinmap_eq {s₁ s₂ : AList β} :
    toFinmap s₁ = toFinmap s₂ ↔ s₁.entries ~ s₂.entries := by
  cases s₁
  cases s₂
  simp [AList.toFinmap]

@[simp]
/--
theorem `AList.toFinmap_entries` / 定理 `AList.toFinmap_entries`

English:
theorem AList.toFinmap_entries
  given: (s : AList β)
  statement: ⟦s⟧.entries = s.entries
  proof: rfl

中文:
定理 AList.toFinmap_entries
  条件: (s : AList β)
  结论: ⟦s⟧.entries = s.entries
  证明: rfl
-/
theorem AList.toFinmap_entries (s : AList β) : ⟦s⟧.entries = s.entries :=
  rfl

/--
Definition of `List.toFinmap` / `List.toFinmap` 的定义

English:
definition List.toFinmap
  signature: [DecidableEq α] (s : List (Sigma β))
  body: s.toAList.toFinmap

中文:
定义 列表.toFinmap
  签名: [DecidableEq α] (s : 列表 (依赖和类型 β))
  定义体: s.toAList.toFinmap

Depends on / 依赖: s.toAList.toFinmap, toAList, toFinmap
-/
def List.toFinmap [DecidableEq α] (s : List (Sigma β)) : Finmap β :=
  s.toAList.toFinmap

namespace Finmap

open AList

/--
lemma `nodup_entries` / 引理 `nodup_entries`

English:
lemma nodup_entries
  given: (f : Finmap β)
  statement: f.entries.Nodup
  proof: f.nodupKeys.nodup

中文:
引理 nodup_entries
  条件: (f : Finmap β)
  结论: f.entries.Nodup
  证明: f.nodupKeys.nodup

Depends on / 依赖: f.nodupKeys.nodup, nodupKeys
-/
lemma nodup_entries (f : Finmap β) : f.entries.Nodup := f.nodupKeys.nodup

/-! ### Lifting from AList -/

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {γ} (s : Finmap β) (f : AList β -> γ)
  body: by
  refine
    (Quotient.liftOn s.entries
      (fun (l : List (Sigma β)) => (⟨_, fun nd => f ⟨l, nd⟩⟩ : Part γ))
      (fun l₁ l₂ p => Part.ext' (perm_nodupKeys p) ?_) : Part γ).get ?_
  · exact fun h1 h2 => H _ _ p
  · have := s.nodupKeys
    revert this
    rcases s.entries with ⟨l⟩
    exact id

中文:
定义 liftOn
  签名: {γ} (s : Finmap β) (f : AList β -> γ)
  定义体: by
  refine
    (Quotient.liftOn s.entries
      (fun (l : List (Sigma β)) => (⟨_, fun nd => f ⟨l, nd⟩⟩ : Part γ))
      (fun l₁ l₂ p => Part.ext' (perm_nodupKeys p) ?_) : Part γ).get ?_
  · exact fun h1 h2 => H _ _ p
  · have := s.nodupKeys
    revert this
    rcases s.entries with ⟨l⟩
    exact id

Depends on / 依赖: Part.ext, Quotient, Quotient.liftOn, entries, liftOn, nodupKeys, perm_nodupKeys, revert, s.entries, s.nodupKeys
-/
def liftOn {γ} (s : Finmap β) (f : AList β -> γ)
    (H : forall a b : AList β, a.entries ~ b.entries -> f a = f b) : γ := by
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
/--
theorem `liftOn_toFinmap` / 定理 `liftOn_toFinmap`

English:
theorem liftOn_toFinmap
  given: {γ} (s : AList β) (f : AList β -> γ) (H)
  statement: liftOn ⟦s⟧ f H = f s
  proof: by
  cases s
  rfl

中文:
定理 liftOn_toFinmap
  条件: {γ} (s : AList β) (f : AList β -> γ) (H)
  结论: liftOn ⟦s⟧ f H = f s
  证明: by
  cases s
  rfl
-/
theorem liftOn_toFinmap {γ} (s : AList β) (f : AList β -> γ) (H) : liftOn ⟦s⟧ f H = f s := by
  cases s
  rfl

/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: {γ} (s₁ s₂ : Finmap β) (f : AList β -> AList β -> γ)
  body: liftOn s₁ (fun l₁ => liftOn s₂ (f l₁) fun _ _ p => H _ _ _ _ (Perm.refl _) p) fun a₁ a₂ p => by
    have H' : f a₁ = f a₂ := funext fun _ => H _ _ _ _ p (Perm.refl _)
    simp only [H']

@[simp]

中文:
定义 liftOn₂
  签名: {γ} (s₁ s₂ : Finmap β) (f : AList β -> AList β -> γ)
  定义体: liftOn s₁ (fun l₁ => liftOn s₂ (f l₁) fun _ _ p => H _ _ _ _ (Perm.refl _) p) fun a₁ a₂ p => by
    have H' : f a₁ = f a₂ := funext fun _ => H _ _ _ _ p (Perm.refl _)
    simp only [H']

@[simp]

Depends on / 依赖: Perm.refl, liftOn
-/
def liftOn₂ {γ} (s₁ s₂ : Finmap β) (f : AList β -> AList β -> γ)
    (H : forall a₁ b₁ a₂ b₂ : AList β,
      a₁.entries ~ a₂.entries -> b₁.entries ~ b₂.entries -> f a₁ b₁ = f a₂ b₂) : γ :=
  liftOn s₁ (fun l₁ => liftOn s₂ (f l₁) fun _ _ p => H _ _ _ _ (Perm.refl _) p) fun a₁ a₂ p => by
    have H' : f a₁ = f a₂ := funext fun _ => H _ _ _ _ p (Perm.refl _)
    simp only [H']

@[simp]
/--
theorem `liftOn₂_toFinmap` / 定理 `liftOn₂_toFinmap`

English:
theorem liftOn₂_toFinmap
  given: {γ} (s₁ s₂ : AList β) (f : AList β -> AList β -> γ) (H)
  proof: rfl

中文:
定理 liftOn₂_toFinmap
  条件: {γ} (s₁ s₂ : AList β) (f : AList β -> AList β -> γ) (H)
  证明: rfl
-/
theorem liftOn₂_toFinmap {γ} (s₁ s₂ : AList β) (f : AList β -> AList β -> γ) (H) :
    liftOn₂ ⟦s₁⟧ ⟦s₂⟧ f H = f s₁ s₂ := rfl

/-! ### Induction -/

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {C : Finmap β -> Prop} (s : Finmap β) (H : forall a : AList β, C ⟦a⟧)
  statement: C s
  proof: by
  rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_elim]

中文:
定理 induction_on
  条件: {C : Finmap β -> 命题} (s : Finmap β) (H : 对任意 a : AList β, C ⟦a⟧)
  结论: C s
  证明: by
  rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_elim]
-/
theorem induction_on {C : Finmap β -> Prop} (s : Finmap β) (H : forall a : AList β, C ⟦a⟧) : C s := by
  rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {C : Finmap β -> Finmap β -> Prop} (s₁ s₂ : Finmap β)
  proof: induction_on s₁ fun l₁ => induction_on s₂ fun l₂ => H l₁ l₂

@[elab_as_elim]

中文:
定理 induction_on₂
  结论: {C : Finmap β -> Finmap β -> 命题} (s₁ s₂ : Finmap β)
  证明: induction_on s₁ fun l₁ => induction_on s₂ fun l₂ => H l₁ l₂

@[elab_as_elim]

Depends on / 依赖: induction_on
-/
theorem induction_on₂ {C : Finmap β -> Finmap β -> Prop} (s₁ s₂ : Finmap β)
    (H : forall a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂ :=
  induction_on s₁ fun l₁ => induction_on s₂ fun l₂ => H l₁ l₂

@[elab_as_elim]
/--
theorem `induction_on₃` / 定理 `induction_on₃`

English:
theorem induction_on₃
  statement: {C : Finmap β -> Finmap β -> Finmap β -> Prop} (s₁ s₂ s₃ : Finmap β)
  proof: induction_on₂ s₁ s₂ fun l₁ l₂ => induction_on s₃ fun l₃ => H l₁ l₂ l₃

中文:
定理 induction_on₃
  结论: {C : Finmap β -> Finmap β -> Finmap β -> 命题} (s₁ s₂ s₃ : Finmap β)
  证明: induction_on₂ s₁ s₂ fun l₁ l₂ => induction_on s₃ fun l₃ => H l₁ l₂ l₃

Depends on / 依赖: induction_on
-/
theorem induction_on₃ {C : Finmap β -> Finmap β -> Finmap β -> Prop} (s₁ s₂ s₃ : Finmap β)
    (H : forall a₁ a₂ a₃ : AList β, C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃⟧) : C s₁ s₂ s₃ :=
  induction_on₂ s₁ s₂ fun l₁ l₂ => induction_on s₃ fun l₃ => H l₁ l₂ l₃

/-! ### extensionality -/

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall {s t : Finmap β}, s.entries = t.entries -> s = t

中文:
定理 ext
  结论: 对任意 {s t : Finmap β}, s.entries = t.entries -> s = t
-/
theorem ext : forall {s t : Finmap β}, s.entries = t.entries -> s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr

@[simp]
/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  given: {s t : Finmap β}
  statement: s.entries = t.entries ↔ s = t
  proof: Finmap.ext_iff.symm

中文:
定理 ext_iff'
  条件: {s t : Finmap β}
  结论: s.entries = t.entries ↔ s = t
  证明: Finmap.ext_iff.symm

Depends on / 依赖: Finmap, Finmap.ext_iff.symm, ext_iff
-/
theorem ext_iff' {s t : Finmap β} : s.entries = t.entries ↔ s = t :=
  Finmap.ext_iff.symm

/-! ### mem -/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Finmap β)
  body: ⟨fun s a => a in s.entries.keys⟩

中文:
实例 :
  签名: Membership α (Finmap β)
  定义体: ⟨fun s a => a in s.entries.keys⟩

Depends on / 依赖: entries, s.entries.keys
-/
instance : Membership α (Finmap β) :=
  ⟨fun s a => a in s.entries.keys⟩

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  given: {a : α} {s : Finmap β}
  statement: a in s ↔ a in s.entries.keys
  proof: Iff.rfl

@[simp]

中文:
定理 mem_def
  条件: {a : α} {s : Finmap β}
  结论: a in s ↔ a in s.entries.keys
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_def {a : α} {s : Finmap β} : a in s ↔ a in s.entries.keys :=
  Iff.rfl

@[simp]
/--
theorem `mem_toFinmap` / 定理 `mem_toFinmap`

English:
theorem mem_toFinmap
  given: {a : α} {s : AList β}
  statement: a in toFinmap s ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_toFinmap
  条件: {a : α} {s : AList β}
  结论: a in toFinmap s ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toFinmap {a : α} {s : AList β} : a in toFinmap s ↔ a in s :=
  Iff.rfl

/-! ### keys -/

/--
Definition of `keys` / `keys` 的定义

English:
definition keys
  signature: (s : Finmap β)
  body: ⟨s.entries.keys, s.nodupKeys.nodup_keys⟩

@[simp]

中文:
定义 keys
  签名: (s : Finmap β)
  定义体: ⟨s.entries.keys, s.nodupKeys.nodup_keys⟩

@[simp]

Depends on / 依赖: entries, nodupKeys, nodup_keys, s.entries.keys, s.nodupKeys.nodup_keys
-/
def keys (s : Finmap β) : Finset α :=
  ⟨s.entries.keys, s.nodupKeys.nodup_keys⟩

@[simp]
/--
theorem `keys_val` / 定理 `keys_val`

English:
theorem keys_val
  given: (s : AList β)
  statement: (keys ⟦s⟧).val = s.keys
  proof: rfl

@[simp]

中文:
定理 keys_val
  条件: (s : AList β)
  结论: (keys ⟦s⟧).val = s.keys
  证明: rfl

@[simp]
-/
theorem keys_val (s : AList β) : (keys ⟦s⟧).val = s.keys :=
  rfl

@[simp]
/--
theorem `keys_ext` / 定理 `keys_ext`

English:
theorem keys_ext
  given: {s₁ s₂ : AList β}
  statement: keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys
  proof: by
  simp [keys, AList.keys]

中文:
定理 keys_ext
  条件: {s₁ s₂ : AList β}
  结论: keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys
  证明: by
  simp [keys, AList.keys]

Depends on / 依赖: AList.keys
-/
theorem keys_ext {s₁ s₂ : AList β} : keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys := by
  simp [keys, AList.keys]

/--
theorem `mem_keys` / 定理 `mem_keys`

English:
theorem mem_keys
  given: {a : α} {s : Finmap β}
  statement: a in s.keys ↔ a in s
  proof: induction_on s fun _ => AList.mem_keys

中文:
定理 mem_keys
  条件: {a : α} {s : Finmap β}
  结论: a in s.keys ↔ a in s
  证明: induction_on s fun _ => AList.mem_keys

Depends on / 依赖: AList.mem_keys, induction_on, mem_keys
-/
theorem mem_keys {a : α} {s : Finmap β} : a in s.keys ↔ a in s :=
  induction_on s fun _ => AList.mem_keys

/-! ### empty -/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Finmap β)
  body: ⟨⟨0, nodupKeys_nil⟩⟩

中文:
实例 :
  签名: EmptyCollection (Finmap β)
  定义体: ⟨⟨0, nodupKeys_nil⟩⟩

Depends on / 依赖: nodupKeys_nil
-/
instance : EmptyCollection (Finmap β) :=
  ⟨⟨0, nodupKeys_nil⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Finmap β)
  body: ⟨∅⟩

@[simp]

中文:
实例 :
  签名: 可居 (Finmap β)
  定义体: ⟨∅⟩

@[simp]
-/
instance : Inhabited (Finmap β) :=
  ⟨∅⟩

@[simp]
/--
theorem `empty_toFinmap` / 定理 `empty_toFinmap`

English:
theorem empty_toFinmap
  statement: (⟦∅⟧ : Finmap β) = ∅
  proof: rfl

@[simp]

中文:
定理 empty_toFinmap
  结论: (⟦∅⟧ : Finmap β) = ∅
  证明: rfl

@[simp]
-/
theorem empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅ :=
  rfl

@[simp]
/--
theorem `toFinmap_nil` / 定理 `toFinmap_nil`

English:
theorem toFinmap_nil
  given: [DecidableEq α]
  statement: ([].toFinmap : Finmap β) = ∅
  proof: rfl

中文:
定理 toFinmap_nil
  条件: [DecidableEq α]
  结论: ([].toFinmap : Finmap β) = ∅
  证明: rfl
-/
theorem toFinmap_nil [DecidableEq α] : ([].toFinmap : Finmap β) = ∅ :=
  rfl

/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: {a : α}
  statement: a ∉ (∅ : Finmap β)
  proof: Multiset.notMem_zero a

@[simp]

中文:
定理 notMem_empty
  条件: {a : α}
  结论: a ∉ (∅ : Finmap β)
  证明: Multiset.notMem_zero a

@[simp]

Depends on / 依赖: Multiset, Multiset.notMem_zero, notMem_zero
-/
theorem notMem_empty {a : α} : a ∉ (∅ : Finmap β) :=
  Multiset.notMem_zero a

@[simp]
/--
theorem `keys_empty` / 定理 `keys_empty`

English:
theorem keys_empty
  statement: (∅ : Finmap β).keys = ∅
  proof: rfl

中文:
定理 keys_empty
  结论: (∅ : Finmap β).keys = ∅
  证明: rfl
-/
theorem keys_empty : (∅ : Finmap β).keys = ∅ :=
  rfl

/-! ### singleton -/

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α) (b : β a)
  body: ⟦AList.singleton a b⟧

@[simp]

中文:
定义 singleton
  签名: (a : α) (b : β a)
  定义体: ⟦AList.singleton a b⟧

@[simp]

Depends on / 依赖: AList.singleton, singleton
-/
def singleton (a : α) (b : β a) : Finmap β :=
  ⟦AList.singleton a b⟧

@[simp]
/--
theorem `keys_singleton` / 定理 `keys_singleton`

English:
theorem keys_singleton
  given: (a : α) (b : β a)
  statement: (singleton a b).keys = {a}
  proof: rfl

@[simp]

中文:
定理 keys_singleton
  条件: (a : α) (b : β a)
  结论: (singleton a b).keys = {a}
  证明: rfl

@[simp]
-/
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = {a} :=
  rfl

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: (x y : α) (b : β y)
  statement: x in singleton y b ↔ x = y
  proof: by
  simp [singleton, mem_def]

中文:
定理 mem_singleton
  条件: (x y : α) (b : β y)
  结论: x in singleton y b ↔ x = y
  证明: by
  simp [singleton, mem_def]

Depends on / 依赖: mem_def, singleton
-/
theorem mem_singleton (x y : α) (b : β y) : x in singleton y b ↔ x = y := by
  simp [singleton, mem_def]

section

variable [DecidableEq α]

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [forall a, DecidableEq (β a)]

中文:
实例 decidableEq
  签名: [对任意 a, DecidableEq (β a)]
-/
instance decidableEq [forall a, DecidableEq (β a)] : DecidableEq (Finmap β)
  | _, _ => decidable_of_iff _ Finmap.ext_iff.symm

/-! ### lookup -/

/--
Definition of `lookup` / `lookup` 的定义

English:
definition lookup
  signature: (a : α) (s : Finmap β)
  body: liftOn s (AList.lookup a) fun _ _ => perm_lookup

@[simp]

中文:
定义 lookup
  签名: (a : α) (s : Finmap β)
  定义体: liftOn s (AList.lookup a) fun _ _ => perm_lookup

@[simp]

Depends on / 依赖: AList.lookup, liftOn, lookup, perm_lookup
-/
def lookup (a : α) (s : Finmap β) : Option (β a) :=
  liftOn s (AList.lookup a) fun _ _ => perm_lookup

@[simp]
/--
theorem `lookup_toFinmap` / 定理 `lookup_toFinmap`

English:
theorem lookup_toFinmap
  given: (a : α) (s : AList β)
  statement: lookup a ⟦s⟧ = s.lookup a
  proof: rfl

@[simp]

中文:
定理 lookup_toFinmap
  条件: (a : α) (s : AList β)
  结论: lookup a ⟦s⟧ = s.lookup a
  证明: rfl

@[simp]
-/
theorem lookup_toFinmap (a : α) (s : AList β) : lookup a ⟦s⟧ = s.lookup a :=
  rfl

@[simp]
/--
theorem `dlookup_list_toFinmap` / 定理 `dlookup_list_toFinmap`

English:
theorem dlookup_list_toFinmap
  given: (a : α) (s : List (Sigma β))
  statement: lookup a s.toFinmap = s.dlookup a
  proof: by
  rw [List.toFinmap]; rw [lookup_toFinmap]; rw [lookup_to_alist]

@[simp]

中文:
定理 dlookup_list_toFinmap
  条件: (a : α) (s : 列表 (依赖和类型 β))
  结论: lookup a s.toFinmap = s.dlookup a
  证明: by
  rw [List.toFinmap]; rw [lookup_toFinmap]; rw [lookup_to_alist]

@[simp]

Depends on / 依赖: List.toFinmap, lookup_toFinmap, lookup_to_alist, toFinmap
-/
theorem dlookup_list_toFinmap (a : α) (s : List (Sigma β)) : lookup a s.toFinmap = s.dlookup a := by
  rw [List.toFinmap]; rw [lookup_toFinmap]; rw [lookup_to_alist]

@[simp]
/--
theorem `lookup_empty` / 定理 `lookup_empty`

English:
theorem lookup_empty
  given: (a)
  statement: lookup a (∅ : Finmap β) = none
  proof: rfl

中文:
定理 lookup_empty
  条件: (a)
  结论: lookup a (∅ : Finmap β) = none
  证明: rfl
-/
theorem lookup_empty (a) : lookup a (∅ : Finmap β) = none :=
  rfl

/--
theorem `lookup_isSome` / 定理 `lookup_isSome`

English:
theorem lookup_isSome
  given: {a : α} {s : Finmap β}
  statement: (s.lookup a).isSome ↔ a in s
  proof: induction_on s fun _ => AList.lookup_isSome

中文:
定理 lookup_isSome
  条件: {a : α} {s : Finmap β}
  结论: (s.lookup a).isSome ↔ a in s
  证明: induction_on s fun _ => AList.lookup_isSome

Depends on / 依赖: AList.lookup_isSome, induction_on, lookup_isSome
-/
theorem lookup_isSome {a : α} {s : Finmap β} : (s.lookup a).isSome ↔ a in s :=
  induction_on s fun _ => AList.lookup_isSome

/--
theorem `lookup_eq_none` / 定理 `lookup_eq_none`

English:
theorem lookup_eq_none
  given: {a} {s : Finmap β}
  statement: lookup a s = none ↔ a ∉ s
  proof: induction_on s fun _ => AList.lookup_eq_none

中文:
定理 lookup_eq_none
  条件: {a} {s : Finmap β}
  结论: lookup a s = none ↔ a ∉ s
  证明: induction_on s fun _ => AList.lookup_eq_none

Depends on / 依赖: AList.lookup_eq_none, induction_on, lookup_eq_none
-/
theorem lookup_eq_none {a} {s : Finmap β} : lookup a s = none ↔ a ∉ s :=
  induction_on s fun _ => AList.lookup_eq_none

/--
lemma `mem_lookup_iff` / 引理 `mem_lookup_iff`

English:
lemma mem_lookup_iff
  given: {s : Finmap β} {a : α} {b : β a}
  proof: by
  rcases s with ⟨⟨l⟩, hl⟩; exact List.mem_dlookup_iff hl

中文:
引理 mem_lookup_iff
  条件: {s : Finmap β} {a : α} {b : β a}
  证明: by
  rcases s with ⟨⟨l⟩, hl⟩; exact List.mem_dlookup_iff hl

Depends on / 依赖: List.mem_dlookup_iff, mem_dlookup_iff
-/
lemma mem_lookup_iff {s : Finmap β} {a : α} {b : β a} :
    b in s.lookup a ↔ Sigma.mk a b in s.entries := by
  rcases s with ⟨⟨l⟩, hl⟩; exact List.mem_dlookup_iff hl

/--
lemma `lookup_eq_some_iff` / 引理 `lookup_eq_some_iff`

English:
lemma lookup_eq_some_iff
  given: {s : Finmap β} {a : α} {b : β a}
  proof: mem_lookup_iff

中文:
引理 lookup_eq_some_iff
  条件: {s : Finmap β} {a : α} {b : β a}
  证明: mem_lookup_iff

Depends on / 依赖: mem_lookup_iff
-/
lemma lookup_eq_some_iff {s : Finmap β} {a : α} {b : β a} :
    s.lookup a = b ↔ Sigma.mk a b in s.entries := mem_lookup_iff

/--
lemma `sigma_keys_lookup` / 引理 `sigma_keys_lookup`

English:
lemma sigma_keys_lookup
  given: (s : Finmap β)
  proof: by
  ext x
  have : x in s.entries -> x.1 in s.keys := Multiset.mem_map_of_mem _
  simpa [lookup_eq_some_iff]

@[simp]

中文:
引理 sigma_keys_lookup
  条件: (s : Finmap β)
  证明: by
  ext x
  have : x in s.entries -> x.1 in s.keys := Multiset.mem_map_of_mem _
  simpa [lookup_eq_some_iff]

@[simp]
-/
@[simp] lemma sigma_keys_lookup (s : Finmap β) :
    s.keys.sigma (fun i => (s.lookup i).toFinset) = ⟨s.entries, s.nodup_entries⟩ := by
  ext x
  have : x in s.entries -> x.1 in s.keys := Multiset.mem_map_of_mem _
  simpa [lookup_eq_some_iff]

@[simp]
/--
theorem `lookup_singleton_eq` / 定理 `lookup_singleton_eq`

English:
theorem lookup_singleton_eq
  given: {a : α} {b : β a}
  statement: (singleton a b).lookup a = some b
  proof: by
  rw [singleton]; rw [lookup_toFinmap]; rw [AList.singleton]; rw [AList.lookup]; rw [dlookup_cons_eq]

中文:
定理 lookup_singleton_eq
  条件: {a : α} {b : β a}
  结论: (singleton a b).lookup a = some b
  证明: by
  rw [singleton]; rw [lookup_toFinmap]; rw [AList.singleton]; rw [AList.lookup]; rw [dlookup_cons_eq]

Depends on / 依赖: AList.lookup, AList.singleton, dlookup_cons_eq, lookup, lookup_toFinmap, singleton
-/
theorem lookup_singleton_eq {a : α} {b : β a} : (singleton a b).lookup a = some b := by
  rw [singleton]; rw [lookup_toFinmap]; rw [AList.singleton]; rw [AList.lookup]; rw [dlookup_cons_eq]

instance (a : α) (s : Finmap β) : Decidable (a in s) :=
  decidable_of_iff _ lookup_isSome

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {a : α} {s : Finmap β}
  statement: a in s ↔ exists b, s.lookup a = some b
  proof: induction_on s fun s =>
Iff.trans List.mem_keys exists_congr fun _ => (mem_dlookup_iff s.nodupKeys).symm

中文:
定理 mem_iff
  条件: {a : α} {s : Finmap β}
  结论: a in s ↔ 存在 b, s.lookup a = some b
  证明: induction_on s fun s =>
Iff.trans List.mem_keys exists_congr fun _ => (mem_dlookup_iff s.nodupKeys).symm

Depends on / 依赖: Iff.trans, List.mem_keys, exists_congr, induction_on, mem_dlookup_iff, mem_keys, nodupKeys, s.nodupKeys
-/
theorem mem_iff {a : α} {s : Finmap β} : a in s ↔ exists b, s.lookup a = some b :=
  induction_on s fun s =>
Iff.trans List.mem_keys exists_congr fun _ => (mem_dlookup_iff s.nodupKeys).symm

/--
theorem `mem_of_lookup_eq_some` / 定理 `mem_of_lookup_eq_some`

English:
theorem mem_of_lookup_eq_some
  given: {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b)
  statement: a in s
  proof: mem_iff.mpr ⟨_, h⟩

中文:
定理 mem_of_lookup_eq_some
  条件: {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b)
  结论: a in s
  证明: mem_iff.mpr ⟨_, h⟩

Depends on / 依赖: mem_iff, mem_iff.mpr
-/
theorem mem_of_lookup_eq_some {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b) : a in s :=
  mem_iff.mpr ⟨_, h⟩

/--
theorem `ext_lookup` / 定理 `ext_lookup`

English:
theorem ext_lookup
  given: {s₁ s₂ : Finmap β}
  statement: (forall x, s₁.lookup x = s₂.lookup x) -> s₁ = s₂
  proof: induction_on₂ s₁ s₂ fun s₁ s₂ h => by
    simp only [AList.lookup, lookup_toFinmap] at h
    rw [AList.toFinmap_eq]
    apply lookup_ext s₁.nodupKeys s₂.nodupKeys
    intro x y
    rw [h]

中文:
定理 ext_lookup
  条件: {s₁ s₂ : Finmap β}
  结论: (对任意 x, s₁.lookup x = s₂.lookup x) -> s₁ = s₂
  证明: induction_on₂ s₁ s₂ fun s₁ s₂ h => by
    simp only [AList.lookup, lookup_toFinmap] at h
    rw [AList.toFinmap_eq]
    apply lookup_ext s₁.nodupKeys s₂.nodupKeys
    intro x y
    rw [h]

Depends on / 依赖: AList.lookup, AList.toFinmap_eq, lookup, lookup_ext, lookup_toFinmap, nodupKeys, toFinmap_eq
-/
theorem ext_lookup {s₁ s₂ : Finmap β} : (forall x, s₁.lookup x = s₂.lookup x) -> s₁ = s₂ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ h => by
    simp only [AList.lookup, lookup_toFinmap] at h
    rw [AList.toFinmap_eq]
    apply lookup_ext s₁.nodupKeys s₂.nodupKeys
    intro x y
    rw [h]

/-- An equivalence between `Finmap β` and pairs `(keys : Finset α, lookup : ∀ a, Option (β a))` such
that `(lookup a).isSome ↔ a ∈ keys`. -/
@[simps apply_coe_fst apply_coe_snd]
/--
Definition of `keysLookupEquiv` / `keysLookupEquiv` 的定义

English:
definition keysLookupEquiv
  signature: :
  body: ⟨(s.keys, fun i => s.lookup i), fun _ => lookup_isSome⟩
invFun f := mk (f.1.1.sigma fun i => (f.1.2 i).toFinset).val by
    refine Multiset.nodup_keys.1 ((Finset.nodup _).map_on ?_)
    simp only [Finset.mem_val, Finset.mem_sigma, Option.mem_toFinset, Option.mem_def]
    rintro ⟨i, x⟩ ⟨_, hx⟩ ⟨j, y⟩

中文:
定义 keysLookupEquiv
  签名: :
  定义体: ⟨(s.keys, fun i => s.lookup i), fun _ => lookup_isSome⟩
invFun f := mk (f.1.1.sigma fun i => (f.1.2 i).toFinset).val by
    refine Multiset.nodup_keys.1 ((Finset.nodup _).map_on ?_)
    simp only [Finset.mem_val, Finset.mem_sigma, Option.mem_toFinset, Option.mem_def]
    rintro ⟨i, x⟩ ⟨_, hx⟩ ⟨j, y⟩

Depends on / 依赖: lookup, lookup_isSome, s.keys, s.lookup
-/
def keysLookupEquiv :
    Finmap β ≃ { f : Finset α × (forall a, Option (β a)) // forall i, (f.2 i).isSome ↔ i in f.1 } where
  toFun s := ⟨(s.keys, fun i => s.lookup i), fun _ => lookup_isSome⟩
invFun f := mk (f.1.1.sigma fun i => (f.1.2 i).toFinset).val by
    refine Multiset.nodup_keys.1 ((Finset.nodup _).map_on ?_)
    simp only [Finset.mem_val, Finset.mem_sigma, Option.mem_toFinset, Option.mem_def]
    rintro ⟨i, x⟩ ⟨_, hx⟩ ⟨j, y⟩ ⟨_, hy⟩ (rfl : i = j)
    simpa using hx.symm.trans hy
left_inv f := ext by simp
  right_inv := fun ⟨(s, f), hf⟩ => by
    dsimp only at hf
    ext
    · simp [keys, Multiset.keys, ← hf, Option.isSome_iff_exists]
    · simp +contextual [lookup_eq_some_iff, ← hf]

/--
lemma `keysLookupEquiv_symm_apply_keys` / 引理 `keysLookupEquiv_symm_apply_keys`

English:
lemma keysLookupEquiv_symm_apply_keys
  proof: keysLookupEquiv.surjective.forall.2 fun _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_fst]

中文:
引理 keysLookupEquiv_symm_apply_keys
  证明: keysLookupEquiv.surjective.forall.2 fun _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_fst]
-/
@[simp] lemma keysLookupEquiv_symm_apply_keys :
    forall f : {f : Finset α × (forall a, Option (β a)) // forall i, (f.2 i).isSome ↔ i in f.1},
      (keysLookupEquiv.symm f).keys = f.1.1 :=
  keysLookupEquiv.surjective.forall.2 fun _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_fst]

/--
lemma `keysLookupEquiv_symm_apply_lookup` / 引理 `keysLookupEquiv_symm_apply_lookup`

English:
lemma keysLookupEquiv_symm_apply_lookup
  proof: keysLookupEquiv.surjective.forall.2 fun _ _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_snd]

中文:
引理 keysLookupEquiv_symm_apply_lookup
  证明: keysLookupEquiv.surjective.forall.2 fun _ _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_snd]
-/
@[simp] lemma keysLookupEquiv_symm_apply_lookup :
    forall (f : {f : Finset α × (forall a, Option (β a)) // forall i, (f.2 i).isSome ↔ i in f.1}) a,
      (keysLookupEquiv.symm f).lookup a = f.1.2 a :=
  keysLookupEquiv.surjective.forall.2 fun _ _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_snd]

/-! ### replace -/

/--
Definition of `replace` / `replace` 的定义

English:
definition replace
  signature: (a : α) (b : β a) (s : Finmap β)
  body: (liftOn s fun t => AList.toFinmap (AList.replace a b t))
fun _ _ p => toFinmap_eq.2 perm_replace p

@[simp]

中文:
定义 replace
  签名: (a : α) (b : β a) (s : Finmap β)
  定义体: (liftOn s fun t => AList.toFinmap (AList.replace a b t))
fun _ _ p => toFinmap_eq.2 perm_replace p

@[simp]

Depends on / 依赖: AList.replace, AList.toFinmap, liftOn, perm_replace, replace, toFinmap, toFinmap_eq
-/
def replace (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.replace a b t))
fun _ _ p => toFinmap_eq.2 perm_replace p

@[simp]
/--
theorem `replace_toFinmap` / 定理 `replace_toFinmap`

English:
theorem replace_toFinmap
  given: (a : α) (b : β a) (s : AList β)
  proof: by
  simp [replace]

@[simp]

中文:
定理 replace_toFinmap
  条件: (a : α) (b : β a) (s : AList β)
  证明: by
  simp [replace]

@[simp]

Depends on / 依赖: replace
-/
theorem replace_toFinmap (a : α) (b : β a) (s : AList β) :
    replace a b ⟦s⟧ = (⟦s.replace a b⟧ : Finmap β) := by
  simp [replace]

@[simp]
/--
theorem `keys_replace` / 定理 `keys_replace`

English:
theorem keys_replace
  given: (a : α) (b : β a) (s : Finmap β)
  statement: (replace a b s).keys = s.keys
  proof: induction_on s fun s => by simp

@[simp]

中文:
定理 keys_replace
  条件: (a : α) (b : β a) (s : Finmap β)
  结论: (replace a b s).keys = s.keys
  证明: induction_on s fun s => by simp

@[simp]

Depends on / 依赖: induction_on
-/
theorem keys_replace (a : α) (b : β a) (s : Finmap β) : (replace a b s).keys = s.keys :=
  induction_on s fun s => by simp

@[simp]
/--
theorem `mem_replace` / 定理 `mem_replace`

English:
theorem mem_replace
  given: {a a' : α} {b : β a} {s : Finmap β}
  statement: a' in replace a b s ↔ a' in s
  proof: induction_on s fun s => by simp

中文:
定理 mem_replace
  条件: {a a' : α} {b : β a} {s : Finmap β}
  结论: a' in replace a b s ↔ a' in s
  证明: induction_on s fun s => by simp

Depends on / 依赖: induction_on
-/
theorem mem_replace {a a' : α} {b : β a} {s : Finmap β} : a' in replace a b s ↔ a' in s :=
  induction_on s fun s => by simp

end

/-! ### foldl -/

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: {δ : Type w} (f : δ -> forall a, β a -> δ)
  body: letI : RightCommutative fun d (s : Sigma β) => f d s.1 s.2 := ⟨fun _ _ _ => H _ _ _ _ _⟩
  m.entries.foldl (fun d s => f d s.1 s.2) d

中文:
定义 foldl
  签名: {δ : 类型 w} (f : δ -> 对任意 a, β a -> δ)
  定义体: letI : RightCommutative fun d (s : Sigma β) => f d s.1 s.2 := ⟨fun _ _ _ => H _ _ _ _ _⟩
  m.entries.foldl (fun d s => f d s.1 s.2) d

Depends on / 依赖: RightCommutative, entries, m.entries.foldl
-/
def foldl {δ : Type w} (f : δ -> forall a, β a -> δ)
    (H : forall d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) (d : δ) (m : Finmap β) : δ :=
  letI : RightCommutative fun d (s : Sigma β) => f d s.1 s.2 := ⟨fun _ _ _ => H _ _ _ _ _⟩
  m.entries.foldl (fun d s => f d s.1 s.2) d

/--
Definition of `any` / `any` 的定义

English:
definition any
  signature: (f : forall x, β x -> Bool) (s : Finmap β)
  body: s.foldl (fun x y z => x || f y z)
    (fun _ _ _ _ => by simp_rw [Bool.or_assoc, Bool.or_comm, imp_true_iff]) false

中文:
定义 any
  签名: (f : 对任意 x, β x -> 布尔值) (s : Finmap β)
  定义体: s.foldl (fun x y z => x || f y z)
    (fun _ _ _ _ => by simp_rw [Bool.or_assoc, Bool.or_comm, imp_true_iff]) false

Depends on / 依赖: Bool.or_assoc, Bool.or_comm, imp_true_iff, or_assoc, or_comm, s.foldl, simp_rw
-/
def any (f : forall x, β x -> Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x || f y z)
    (fun _ _ _ _ => by simp_rw [Bool.or_assoc, Bool.or_comm, imp_true_iff]) false

/--
Definition of `all` / `all` 的定义

English:
definition all
  signature: (f : forall x, β x -> Bool) (s : Finmap β)
  body: s.foldl (fun x y z => x && f y z)
    (fun _ _ _ _ => by simp_rw [Bool.and_assoc, Bool.and_comm, imp_true_iff]) true

中文:
定义 all
  签名: (f : 对任意 x, β x -> 布尔值) (s : Finmap β)
  定义体: s.foldl (fun x y z => x && f y z)
    (fun _ _ _ _ => by simp_rw [Bool.and_assoc, Bool.and_comm, imp_true_iff]) true

Depends on / 依赖: Bool.and_assoc, Bool.and_comm, and_assoc, and_comm, imp_true_iff, s.foldl, simp_rw
-/
def all (f : forall x, β x -> Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x && f y z)
    (fun _ _ _ _ => by simp_rw [Bool.and_assoc, Bool.and_comm, imp_true_iff]) true

/-! ### erase -/

section

variable [DecidableEq α]

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (a : α) (s : Finmap β)
  body: (liftOn s fun t => AList.toFinmap (AList.erase a t)) fun _ _ p => toFinmap_eq.2 perm_erase p

@[simp]

中文:
定义 erase
  签名: (a : α) (s : Finmap β)
  定义体: (liftOn s fun t => AList.toFinmap (AList.erase a t)) fun _ _ p => toFinmap_eq.2 perm_erase p

@[simp]

Depends on / 依赖: AList.erase, AList.toFinmap, liftOn, perm_erase, toFinmap, toFinmap_eq
-/
def erase (a : α) (s : Finmap β) : Finmap β :=
(liftOn s fun t => AList.toFinmap (AList.erase a t)) fun _ _ p => toFinmap_eq.2 perm_erase p

@[simp]
/--
theorem `erase_toFinmap` / 定理 `erase_toFinmap`

English:
theorem erase_toFinmap
  given: (a : α) (s : AList β)
  statement: erase a ⟦s⟧ = AList.toFinmap (s.erase a)
  proof: by
  simp [erase]

@[simp]

中文:
定理 erase_toFinmap
  条件: (a : α) (s : AList β)
  结论: erase a ⟦s⟧ = AList.toFinmap (s.erase a)
  证明: by
  simp [erase]

@[simp]
-/
theorem erase_toFinmap (a : α) (s : AList β) : erase a ⟦s⟧ = AList.toFinmap (s.erase a) := by
  simp [erase]

@[simp]
/--
theorem `keys_erase_toFinset` / 定理 `keys_erase_toFinset`

English:
theorem keys_erase_toFinset
  given: (a : α) (s : AList β)
  statement: keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a
  proof: by
  simp [Finset.erase, keys, AList.erase, keys_kerase]

@[simp]

中文:
定理 keys_erase_toFinset
  条件: (a : α) (s : AList β)
  结论: keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a
  证明: by
  simp [Finset.erase, keys, AList.erase, keys_kerase]

@[simp]

Depends on / 依赖: AList.erase, Finset, Finset.erase, keys_kerase
-/
theorem keys_erase_toFinset (a : α) (s : AList β) : keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a := by
  simp [Finset.erase, keys, AList.erase, keys_kerase]

@[simp]
/--
theorem `keys_erase` / 定理 `keys_erase`

English:
theorem keys_erase
  given: (a : α) (s : Finmap β)
  statement: (erase a s).keys = s.keys.erase a
  proof: induction_on s fun s => by simp

@[simp]

中文:
定理 keys_erase
  条件: (a : α) (s : Finmap β)
  结论: (erase a s).keys = s.keys.erase a
  证明: induction_on s fun s => by simp

@[simp]

Depends on / 依赖: induction_on
-/
theorem keys_erase (a : α) (s : Finmap β) : (erase a s).keys = s.keys.erase a :=
  induction_on s fun s => by simp

@[simp]
/--
theorem `mem_erase` / 定理 `mem_erase`

English:
theorem mem_erase
  given: {a a' : α} {s : Finmap β}
  statement: a' in erase a s ↔ a' != a ∧ a' in s
  proof: induction_on s fun s => by simp

中文:
定理 mem_erase
  条件: {a a' : α} {s : Finmap β}
  结论: a' in erase a s ↔ a' != a ∧ a' in s
  证明: induction_on s fun s => by simp

Depends on / 依赖: induction_on
-/
theorem mem_erase {a a' : α} {s : Finmap β} : a' in erase a s ↔ a' != a ∧ a' in s :=
  induction_on s fun s => by simp

/--
theorem `notMem_erase_self` / 定理 `notMem_erase_self`

English:
theorem notMem_erase_self
  given: {a : α} {s : Finmap β}
  statement: a ∉ erase a s
  proof: by
  rw [mem_erase]; rw [not_and_or]; rw [not_not]
  left
  rfl

@[simp]

中文:
定理 notMem_erase_self
  条件: {a : α} {s : Finmap β}
  结论: a ∉ erase a s
  证明: by
  rw [mem_erase]; rw [not_and_or]; rw [not_not]
  left
  rfl

@[simp]

Depends on / 依赖: mem_erase, not_and_or, not_not
-/
theorem notMem_erase_self {a : α} {s : Finmap β} : a ∉ erase a s := by
  rw [mem_erase]; rw [not_and_or]; rw [not_not]
  left
  rfl

@[simp]
/--
theorem `lookup_erase` / 定理 `lookup_erase`

English:
theorem lookup_erase
  given: (a) (s : Finmap β)
  statement: lookup a (erase a s) = none
  proof: induction_on s AList.lookup_erase a

@[simp]

中文:
定理 lookup_erase
  条件: (a) (s : Finmap β)
  结论: lookup a (erase a s) = none
  证明: induction_on s AList.lookup_erase a

@[simp]

Depends on / 依赖: AList.lookup_erase, induction_on, lookup_erase
-/
theorem lookup_erase (a) (s : Finmap β) : lookup a (erase a s) = none :=
induction_on s AList.lookup_erase a

@[simp]
/--
theorem `lookup_erase_ne` / 定理 `lookup_erase_ne`

English:
theorem lookup_erase_ne
  given: {a a'} {s : Finmap β} (h : a != a')
  statement: lookup a (erase a' s) = lookup a s
  proof: induction_on s fun _ => AList.lookup_erase_ne h

中文:
定理 lookup_erase_ne
  条件: {a a'} {s : Finmap β} (h : a != a')
  结论: lookup a (erase a' s) = lookup a s
  证明: induction_on s fun _ => AList.lookup_erase_ne h

Depends on / 依赖: AList.lookup_erase_ne, induction_on, lookup_erase_ne
-/
theorem lookup_erase_ne {a a'} {s : Finmap β} (h : a != a') : lookup a (erase a' s) = lookup a s :=
  induction_on s fun _ => AList.lookup_erase_ne h

/--
theorem `erase_erase` / 定理 `erase_erase`

English:
theorem erase_erase
  given: {a a' : α} {s : Finmap β}
  statement: erase a (erase a' s) = erase a' (erase a s)
  proof: induction_on s fun s => ext (by simp only [AList.erase_erase, erase_toFinmap])

中文:
定理 erase_erase
  条件: {a a' : α} {s : Finmap β}
  结论: erase a (erase a' s) = erase a' (erase a s)
  证明: induction_on s fun s => ext (by simp only [AList.erase_erase, erase_toFinmap])

Depends on / 依赖: AList.erase_erase, erase_erase, erase_toFinmap, induction_on
-/
theorem erase_erase {a a' : α} {s : Finmap β} : erase a (erase a' s) = erase a' (erase a s) :=
  induction_on s fun s => ext (by simp only [AList.erase_erase, erase_toFinmap])

/-! ### sdiff -/

/--
Definition of `sdiff` / `sdiff` 的定义

English:
definition sdiff
  signature: (s s' : Finmap β)
  body: s'.foldl (fun s x _ => s.erase x) (fun _ _ _ _ _ => erase_erase) s

中文:
定义 sdiff
  签名: (s s' : Finmap β)
  定义体: s'.foldl (fun s x _ => s.erase x) (fun _ _ _ _ _ => erase_erase) s

Depends on / 依赖: erase_erase, s.erase
-/
def sdiff (s s' : Finmap β) : Finmap β :=
  s'.foldl (fun s x _ => s.erase x) (fun _ _ _ _ _ => erase_erase) s

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SDiff (Finmap β)
  body: ⟨sdiff⟩

中文:
实例 :
  签名: 对称差 (Finmap β)
  定义体: ⟨sdiff⟩
-/
instance : SDiff (Finmap β) :=
  ⟨sdiff⟩

/-! ### insert -/

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (a : α) (b : β a) (s : Finmap β)
  body: (liftOn s fun t => AList.toFinmap (AList.insert a b t)) fun _ _ p =>
toFinmap_eq.2 perm_insert p

@[simp]

中文:
定义 insert
  签名: (a : α) (b : β a) (s : Finmap β)
  定义体: (liftOn s fun t => AList.toFinmap (AList.insert a b t)) fun _ _ p =>
toFinmap_eq.2 perm_insert p

@[simp]

Depends on / 依赖: AList.insert, AList.toFinmap, insert, liftOn, perm_insert, toFinmap, toFinmap_eq
-/
def insert (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.insert a b t)) fun _ _ p =>
toFinmap_eq.2 perm_insert p

@[simp]
/--
theorem `insert_toFinmap` / 定理 `insert_toFinmap`

English:
theorem insert_toFinmap
  given: (a : α) (b : β a) (s : AList β)
  proof: by
  simp [insert]

中文:
定理 insert_toFinmap
  条件: (a : α) (b : β a) (s : AList β)
  证明: by
  simp [insert]

Depends on / 依赖: insert
-/
theorem insert_toFinmap (a : α) (b : β a) (s : AList β) :
    insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b) := by
  simp [insert]

/--
theorem `entries_insert_of_notMem` / 定理 `entries_insert_of_notMem`

English:
theorem entries_insert_of_notMem
  given: {a : α} {b : β a} {s : Finmap β}
  proof: induction_on s fun s h => by
    simp [AList.entries_insert_of_notMem (mt mem_toFinmap.1 h), -entries_insert]

@[simp]

中文:
定理 entries_insert_of_notMem
  条件: {a : α} {b : β a} {s : Finmap β}
  证明: induction_on s fun s h => by
    simp [AList.entries_insert_of_notMem (mt mem_toFinmap.1 h), -entries_insert]

@[simp]

Depends on / 依赖: AList.entries_insert_of_notMem, entries_insert, entries_insert_of_notMem, induction_on, mem_toFinmap
-/
theorem entries_insert_of_notMem {a : α} {b : β a} {s : Finmap β} :
    a ∉ s -> (insert a b s).entries = ⟨a, b⟩ ::ₘ s.entries :=
  induction_on s fun s h => by
    simp [AList.entries_insert_of_notMem (mt mem_toFinmap.1 h), -entries_insert]

@[simp]
/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  given: {a a' : α} {b' : β a'} {s : Finmap β}
  statement: a in insert a' b' s ↔ a = a' ∨ a in s
  proof: induction_on s AList.mem_insert

@[simp]

中文:
定理 mem_insert
  条件: {a a' : α} {b' : β a'} {s : Finmap β}
  结论: a in insert a' b' s ↔ a = a' ∨ a in s
  证明: induction_on s AList.mem_insert

@[simp]

Depends on / 依赖: AList.mem_insert, induction_on, mem_insert
-/
theorem mem_insert {a a' : α} {b' : β a'} {s : Finmap β} : a in insert a' b' s ↔ a = a' ∨ a in s :=
  induction_on s AList.mem_insert

@[simp]
/--
theorem `lookup_insert` / 定理 `lookup_insert`

English:
theorem lookup_insert
  given: {a} {b : β a} (s : Finmap β)
  statement: lookup a (insert a b s) = some b
  proof: induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, AList.lookup_insert]

@[simp]

中文:
定理 lookup_insert
  条件: {a} {b : β a} (s : Finmap β)
  结论: lookup a (insert a b s) = some b
  证明: induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, AList.lookup_insert]

@[simp]

Depends on / 依赖: AList.lookup_insert, induction_on, insert_toFinmap, lookup_insert, lookup_toFinmap
-/
theorem lookup_insert {a} {b : β a} (s : Finmap β) : lookup a (insert a b s) = some b :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, AList.lookup_insert]

@[simp]
/--
theorem `lookup_insert_of_ne` / 定理 `lookup_insert_of_ne`

English:
theorem lookup_insert_of_ne
  given: {a a'} {b : β a} (s : Finmap β) (h : a' != a)
  proof: induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, lookup_insert_ne h]

@[simp]

中文:
定理 lookup_insert_of_ne
  条件: {a a'} {b : β a} (s : Finmap β) (h : a' != a)
  证明: induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, lookup_insert_ne h]

@[simp]

Depends on / 依赖: induction_on, insert_toFinmap, lookup_insert_ne, lookup_toFinmap
-/
theorem lookup_insert_of_ne {a a'} {b : β a} (s : Finmap β) (h : a' != a) :
    lookup a' (insert a b s) = lookup a' s :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, lookup_insert_ne h]

@[simp]
/--
theorem `insert_insert` / 定理 `insert_insert`

English:
theorem insert_insert
  given: {a} {b b' : β a} (s : Finmap β)
  proof: induction_on s fun s => by simp only [insert_toFinmap, AList.insert_insert]

中文:
定理 insert_insert
  条件: {a} {b b' : β a} (s : Finmap β)
  证明: induction_on s fun s => by simp only [insert_toFinmap, AList.insert_insert]

Depends on / 依赖: AList.insert_insert, induction_on, insert_insert, insert_toFinmap
-/
theorem insert_insert {a} {b b' : β a} (s : Finmap β) :
    (s.insert a b).insert a b' = s.insert a b' :=
  induction_on s fun s => by simp only [insert_toFinmap, AList.insert_insert]

/--
theorem `insert_insert_of_ne` / 定理 `insert_insert_of_ne`

English:
theorem insert_insert_of_ne
  given: {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a != a')
  proof: induction_on s fun s => by
    simp only [insert_toFinmap, AList.toFinmap_eq, AList.insert_insert_of_ne _ h]

中文:
定理 insert_insert_of_ne
  条件: {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a != a')
  证明: induction_on s fun s => by
    simp only [insert_toFinmap, AList.toFinmap_eq, AList.insert_insert_of_ne _ h]

Depends on / 依赖: AList.insert_insert_of_ne, AList.toFinmap_eq, induction_on, insert_insert_of_ne, insert_toFinmap, toFinmap_eq
-/
theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a != a') :
    (s.insert a b).insert a' b' = (s.insert a' b').insert a b :=
  induction_on s fun s => by
    simp only [insert_toFinmap, AList.toFinmap_eq, AList.insert_insert_of_ne _ h]

/--
theorem `toFinmap_cons` / 定理 `toFinmap_cons`

English:
theorem toFinmap_cons
  given: (a : α) (b : β a) (xs : List (Sigma β))
  proof: rfl

中文:
定理 toFinmap_cons
  条件: (a : α) (b : β a) (xs : 列表 (依赖和类型 β))
  证明: rfl
-/
theorem toFinmap_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toFinmap (⟨a, b⟩ :: xs) = insert a b xs.toFinmap :=
  rfl

/--
theorem `mem_list_toFinmap` / 定理 `mem_list_toFinmap`

English:
theorem mem_list_toFinmap
  given: (a : α) (xs : List (Sigma β))
  proof: by
  induction xs with
  | nil => simp only [toFinmap_nil, notMem_empty, not_mem_nil, exists_false]
  | cons x xs =>
    obtain ⟨fst_i, snd_i⟩ := x
    simp only [toFinmap_cons, *, exists_or, mem_cons, mem_insert, exists_and_left, Sigma.mk.inj_iff]
    refine (or_congr_left <| and_iff_left_of_imp ?_

中文:
定理 mem_list_toFinmap
  条件: (a : α) (xs : 列表 (依赖和类型 β))
  证明: by
  induction xs with
  | nil => simp only [toFinmap_nil, notMem_empty, not_mem_nil, exists_false]
  | cons x xs =>
    obtain ⟨fst_i, snd_i⟩ := x
    simp only [toFinmap_cons, *, exists_or, mem_cons, mem_insert, exists_and_left, Sigma.mk.inj_iff]
    refine (or_congr_left <| and_iff_left_of_imp ?_

Depends on / 依赖: Sigma.mk.inj_iff, and_iff_left_of_imp, exists_and_left, exists_eq, exists_false, exists_or, fst_i, heq_iff_eq, inj_iff, mem_cons, mem_insert, notMem_empty, not_mem_nil, or_congr_left, snd_i, toFinmap_cons, toFinmap_nil
-/
theorem mem_list_toFinmap (a : α) (xs : List (Sigma β)) :
    a in xs.toFinmap ↔ exists b : β a, Sigma.mk a b in xs := by
  induction xs with
  | nil => simp only [toFinmap_nil, notMem_empty, not_mem_nil, exists_false]
  | cons x xs =>
    obtain ⟨fst_i, snd_i⟩ := x
    simp only [toFinmap_cons, *, exists_or, mem_cons, mem_insert, exists_and_left, Sigma.mk.inj_iff]
    refine (or_congr_left <| and_iff_left_of_imp ?_).symm
    rintro rfl
    simp only [exists_eq, heq_iff_eq]

@[simp]
/--
theorem `insert_singleton_eq` / 定理 `insert_singleton_eq`

English:
theorem insert_singleton_eq
  given: {a : α} {b b' : β a}
  statement: insert a b (singleton a b') = singleton a b
  proof: by
  simp only [singleton, Finmap.insert_toFinmap, AList.insert_singleton_eq]

中文:
定理 insert_singleton_eq
  条件: {a : α} {b b' : β a}
  结论: insert a b (singleton a b') = singleton a b
  证明: by
  simp only [singleton, Finmap.insert_toFinmap, AList.insert_singleton_eq]

Depends on / 依赖: AList.insert_singleton_eq, Finmap, Finmap.insert_toFinmap, insert_singleton_eq, insert_toFinmap, singleton
-/
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b := by
  simp only [singleton, Finmap.insert_toFinmap, AList.insert_singleton_eq]

/-! ### extract -/

/--
Definition of `extract` / `extract` 的定义

English:
definition extract
  signature: (a : α) (s : Finmap β)
  body: (liftOn s fun t => Prod.map id AList.toFinmap (AList.extract a t)) fun s₁ s₂ p => by
    simp [perm_lookup p, toFinmap_eq, perm_erase p]

@[simp]

中文:
定义 extract
  签名: (a : α) (s : Finmap β)
  定义体: (liftOn s fun t => Prod.map id AList.toFinmap (AList.extract a t)) fun s₁ s₂ p => by
    simp [perm_lookup p, toFinmap_eq, perm_erase p]

@[simp]

Depends on / 依赖: AList.extract, AList.toFinmap, Prod.map, extract, liftOn, perm_erase, perm_lookup, toFinmap, toFinmap_eq
-/
def extract (a : α) (s : Finmap β) : Option (β a) × Finmap β :=
  (liftOn s fun t => Prod.map id AList.toFinmap (AList.extract a t)) fun s₁ s₂ p => by
    simp [perm_lookup p, toFinmap_eq, perm_erase p]

@[simp]
/--
theorem `extract_eq_lookup_erase` / 定理 `extract_eq_lookup_erase`

English:
theorem extract_eq_lookup_erase
  given: (a : α) (s : Finmap β)
  statement: extract a s = (lookup a s, erase a s)
  proof: induction_on s fun s => by simp [extract]

中文:
定理 extract_eq_lookup_erase
  条件: (a : α) (s : Finmap β)
  结论: extract a s = (lookup a s, erase a s)
  证明: induction_on s fun s => by simp [extract]

Depends on / 依赖: extract, induction_on
-/
theorem extract_eq_lookup_erase (a : α) (s : Finmap β) : extract a s = (lookup a s, erase a s) :=
  induction_on s fun s => by simp [extract]

/-! ### union -/

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (s₁ s₂ : Finmap β)
  body: (liftOn₂ s₁ s₂ fun s₁ s₂ => (AList.toFinmap (s₁ union s₂))) fun _ _ _ _ p₁₃ p₂₄ =>
toFinmap_eq.mpr perm_union p₁₃ p₂₄

中文:
定义 union
  签名: (s₁ s₂ : Finmap β)
  定义体: (liftOn₂ s₁ s₂ fun s₁ s₂ => (AList.toFinmap (s₁ union s₂))) fun _ _ _ _ p₁₃ p₂₄ =>
toFinmap_eq.mpr perm_union p₁₃ p₂₄

Depends on / 依赖: AList.toFinmap, perm_union, toFinmap, toFinmap_eq, toFinmap_eq.mpr
-/
def union (s₁ s₂ : Finmap β) : Finmap β :=
  (liftOn₂ s₁ s₂ fun s₁ s₂ => (AList.toFinmap (s₁ union s₂))) fun _ _ _ _ p₁₃ p₂₄ =>
toFinmap_eq.mpr perm_union p₁₃ p₂₄

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union (Finmap β)
  body: ⟨union⟩

@[simp]

中文:
实例 :
  签名: 并集 (Finmap β)
  定义体: ⟨union⟩

@[simp]
-/
instance : Union (Finmap β) :=
  ⟨union⟩

@[simp]
/--
theorem `mem_union` / 定理 `mem_union`

English:
theorem mem_union
  given: {a} {s₁ s₂ : Finmap β}
  statement: a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
  proof: induction_on₂ s₁ s₂ fun _ _ => AList.mem_union

@[simp]

中文:
定理 mem_union
  条件: {a} {s₁ s₂ : Finmap β}
  结论: a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂
  证明: induction_on₂ s₁ s₂ fun _ _ => AList.mem_union

@[simp]

Depends on / 依赖: AList.mem_union, mem_union
-/
theorem mem_union {a} {s₁ s₂ : Finmap β} : a in s₁ union s₂ ↔ a in s₁ ∨ a in s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_union

@[simp]
/--
theorem `union_toFinmap` / 定理 `union_toFinmap`

English:
theorem union_toFinmap
  given: (s₁ s₂ : AList β)
  statement: (toFinmap s₁) union (toFinmap s₂) = toFinmap (s₁ union s₂)
  proof: by
  simp [(· union ·), union]

中文:
定理 union_toFinmap
  条件: (s₁ s₂ : AList β)
  结论: (toFinmap s₁) union (toFinmap s₂) = toFinmap (s₁ union s₂)
  证明: by
  simp [(· union ·), union]
-/
theorem union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) union (toFinmap s₂) = toFinmap (s₁ union s₂) := by
  simp [(· union ·), union]

/--
theorem `keys_union` / 定理 `keys_union`

English:
theorem keys_union
  given: {s₁ s₂ : Finmap β}
  statement: (s₁ union s₂).keys = s₁.keys union s₂.keys
  proof: induction_on₂ s₁ s₂ fun s₁ s₂ => Finset.ext by simp [keys]

@[simp]

中文:
定理 keys_union
  条件: {s₁ s₂ : Finmap β}
  结论: (s₁ union s₂).keys = s₁.keys union s₂.keys
  证明: induction_on₂ s₁ s₂ fun s₁ s₂ => Finset.ext by simp [keys]

@[simp]

Depends on / 依赖: Finset, Finset.ext
-/
theorem keys_union {s₁ s₂ : Finmap β} : (s₁ union s₂).keys = s₁.keys union s₂.keys :=
induction_on₂ s₁ s₂ fun s₁ s₂ => Finset.ext by simp [keys]

@[simp]
/--
theorem `lookup_union_left` / 定理 `lookup_union_left`

English:
theorem lookup_union_left
  given: {a} {s₁ s₂ : Finmap β}
  statement: a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁
  proof: induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_left

@[simp]

中文:
定理 lookup_union_left
  条件: {a} {s₁ s₂ : Finmap β}
  结论: a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁
  证明: induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_left

@[simp]

Depends on / 依赖: AList.lookup_union_left, lookup_union_left
-/
theorem lookup_union_left {a} {s₁ s₂ : Finmap β} : a in s₁ -> lookup a (s₁ union s₂) = lookup a s₁ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_left

@[simp]
/--
theorem `lookup_union_right` / 定理 `lookup_union_right`

English:
theorem lookup_union_right
  given: {a} {s₁ s₂ : Finmap β}
  statement: a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
  proof: induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_right

中文:
定理 lookup_union_right
  条件: {a} {s₁ s₂ : Finmap β}
  结论: a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂
  证明: induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_right

Depends on / 依赖: AList.lookup_union_right, lookup_union_right
-/
theorem lookup_union_right {a} {s₁ s₂ : Finmap β} : a ∉ s₁ -> lookup a (s₁ union s₂) = lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_right

/--
theorem `lookup_union_left_of_not_in` / 定理 `lookup_union_left_of_not_in`

English:
theorem lookup_union_left_of_not_in
  given: {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂)
  proof: by
  by_cases h' : a in s₁
  · rw [lookup_union_left h']
  · rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h']

中文:
定理 lookup_union_left_of_not_in
  条件: {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂)
  证明: by
  by_cases h' : a in s₁
  · rw [lookup_union_left h']
  · rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h']

Depends on / 依赖: lookup_eq_none, lookup_eq_none.mpr, lookup_union_left, lookup_union_right
-/
theorem lookup_union_left_of_not_in {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂) :
    lookup a (s₁ union s₂) = lookup a s₁ := by
  by_cases h' : a in s₁
  · rw [lookup_union_left h']
  · rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h']

/-- `simp`-normal form of `mem_lookup_union` -/
@[simp]
/--
theorem `mem_lookup_union'` / 定理 `mem_lookup_union'`

English:
theorem mem_lookup_union'
  given: {a} {b : β a} {s₁ s₂ : Finmap β}
  proof: induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

中文:
定理 mem_lookup_union'
  条件: {a} {b : β a} {s₁ s₂ : Finmap β}
  证明: induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

Depends on / 依赖: AList.mem_lookup_union, mem_lookup_union
-/
theorem mem_lookup_union' {a} {b : β a} {s₁ s₂ : Finmap β} :
    lookup a (s₁ union s₂) = some b ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

/--
theorem `mem_lookup_union` / 定理 `mem_lookup_union`

English:
theorem mem_lookup_union
  given: {a} {b : β a} {s₁ s₂ : Finmap β}
  proof: induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

中文:
定理 mem_lookup_union
  条件: {a} {b : β a} {s₁ s₂ : Finmap β}
  证明: induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

Depends on / 依赖: AList.mem_lookup_union, mem_lookup_union
-/
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : Finmap β} :
    b in lookup a (s₁ union s₂) ↔ b in lookup a s₁ ∨ a ∉ s₁ ∧ b in lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

/--
theorem `mem_lookup_union_middle` / 定理 `mem_lookup_union_middle`

English:
theorem mem_lookup_union_middle
  given: {a} {b : β a} {s₁ s₂ s₃ : Finmap β}
  proof: induction_on₃ s₁ s₂ s₃ fun _ _ _ => AList.mem_lookup_union_middle

中文:
定理 mem_lookup_union_middle
  条件: {a} {b : β a} {s₁ s₂ s₃ : Finmap β}
  证明: induction_on₃ s₁ s₂ s₃ fun _ _ _ => AList.mem_lookup_union_middle

Depends on / 依赖: AList.mem_lookup_union_middle, mem_lookup_union_middle
-/
theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Finmap β} :
    b in lookup a (s₁ union s₃) -> a ∉ s₂ -> b in lookup a (s₁ union s₂ union s₃) :=
  induction_on₃ s₁ s₂ s₃ fun _ _ _ => AList.mem_lookup_union_middle

/--
theorem `insert_union` / 定理 `insert_union`

English:
theorem insert_union
  given: {a} {b : β a} {s₁ s₂ : Finmap β}
  statement: insert a b (s₁ union s₂) = insert a b s₁ union s₂
  proof: induction_on₂ s₁ s₂ fun a₁ a₂ => by simp [AList.insert_union]

中文:
定理 insert_union
  条件: {a} {b : β a} {s₁ s₂ : Finmap β}
  结论: insert a b (s₁ union s₂) = insert a b s₁ union s₂
  证明: induction_on₂ s₁ s₂ fun a₁ a₂ => by simp [AList.insert_union]

Depends on / 依赖: AList.insert_union, insert_union
-/
theorem insert_union {a} {b : β a} {s₁ s₂ : Finmap β} : insert a b (s₁ union s₂) = insert a b s₁ union s₂ :=
  induction_on₂ s₁ s₂ fun a₁ a₂ => by simp [AList.insert_union]

/--
theorem `union_assoc` / 定理 `union_assoc`

English:
theorem union_assoc
  given: {s₁ s₂ s₃ : Finmap β}
  statement: s₁ union s₂ union s₃ = s₁ union (s₂ union s₃)
  proof: induction_on₃ s₁ s₂ s₃ fun s₁ s₂ s₃ => by
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_assoc]

@[simp]

中文:
定理 union_assoc
  条件: {s₁ s₂ s₃ : Finmap β}
  结论: s₁ union s₂ union s₃ = s₁ union (s₂ union s₃)
  证明: induction_on₃ s₁ s₂ s₃ fun s₁ s₂ s₃ => by
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_assoc]

@[simp]

Depends on / 依赖: AList.toFinmap_eq, AList.union_assoc, toFinmap_eq, union_assoc, union_toFinmap
-/
theorem union_assoc {s₁ s₂ s₃ : Finmap β} : s₁ union s₂ union s₃ = s₁ union (s₂ union s₃) :=
  induction_on₃ s₁ s₂ s₃ fun s₁ s₂ s₃ => by
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_assoc]

@[simp]
/--
theorem `empty_union` / 定理 `empty_union`

English:
theorem empty_union
  given: {s₁ : Finmap β}
  statement: ∅ union s₁ = s₁
  proof: induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

@[simp]

中文:
定理 empty_union
  条件: {s₁ : Finmap β}
  结论: ∅ union s₁ = s₁
  证明: induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

@[simp]

Depends on / 依赖: empty_toFinmap, induction_on, union_toFinmap
-/
theorem empty_union {s₁ : Finmap β} : ∅ union s₁ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

@[simp]
/--
theorem `union_empty` / 定理 `union_empty`

English:
theorem union_empty
  given: {s₁ : Finmap β}
  statement: s₁ union ∅ = s₁
  proof: induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

中文:
定理 union_empty
  条件: {s₁ : Finmap β}
  结论: s₁ union ∅ = s₁
  证明: induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

Depends on / 依赖: empty_toFinmap, induction_on, union_toFinmap
-/
theorem union_empty {s₁ : Finmap β} : s₁ union ∅ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

/--
theorem `erase_union_singleton` / 定理 `erase_union_singleton`

English:
theorem erase_union_singleton
  given: (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = some b)
  proof: ext_lookup fun x => by
    by_cases h' : x = a
    · subst a
      rw [lookup_union_right notMem_erase_self]; rw [lookup_singleton_eq]; rw [h]
    · have : x ∉ singleton a b := by rwa [mem_singleton]
      rw [lookup_union_left_of_not_in this]; rw [lookup_erase_ne h']

中文:
定理 erase_union_singleton
  条件: (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = some b)
  证明: ext_lookup fun x => by
    by_cases h' : x = a
    · subst a
      rw [lookup_union_right notMem_erase_self]; rw [lookup_singleton_eq]; rw [h]
    · have : x ∉ singleton a b := by rwa [mem_singleton]
      rw [lookup_union_left_of_not_in this]; rw [lookup_erase_ne h']

Depends on / 依赖: ext_lookup, lookup_erase_ne, lookup_singleton_eq, lookup_union_left_of_not_in, lookup_union_right, mem_singleton, notMem_erase_self, singleton
-/
theorem erase_union_singleton (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = some b) :
    s.erase a union singleton a b = s :=
  ext_lookup fun x => by
    by_cases h' : x = a
    · subst a
      rw [lookup_union_right notMem_erase_self]; rw [lookup_singleton_eq]; rw [h]
    · have : x ∉ singleton a b := by rwa [mem_singleton]
      rw [lookup_union_left_of_not_in this]; rw [lookup_erase_ne h']

end

/-! ### Disjoint -/

/--
Definition of `Disjoint` / `Disjoint` 的定义

English:
definition Disjoint
  signature: (s₁ s₂ : Finmap β)
  body: forall x in s₁, x ∉ s₂

中文:
定义 Disjoint
  签名: (s₁ s₂ : Finmap β)
  定义体: forall x in s₁, x ∉ s₂
-/
def Disjoint (s₁ s₂ : Finmap β) : Prop :=
  forall x in s₁, x ∉ s₂

/--
theorem `disjoint_empty` / 定理 `disjoint_empty`

English:
theorem disjoint_empty
  given: (x : Finmap β)
  statement: Disjoint ∅ x
  proof: nofun

@[symm]

中文:
定理 disjoint_empty
  条件: (x : Finmap β)
  结论: Disjoint ∅ x
  证明: nofun

@[symm]
-/
theorem disjoint_empty (x : Finmap β) : Disjoint ∅ x :=
  nofun

@[symm]
/--
theorem `Disjoint.symm` / 定理 `Disjoint.symm`

English:
theorem Disjoint.symm
  given: (x y : Finmap β) (h : Disjoint x y)
  statement: Disjoint y x
  proof: fun p hy hx => h p hx hy

中文:
定理 Disjoint.symm
  条件: (x y : Finmap β) (h : Disjoint x y)
  结论: Disjoint y x
  证明: fun p hy hx => h p hx hy
-/
theorem Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjoint y x := fun p hy hx => h p hx hy

/--
theorem `Disjoint.symm_iff` / 定理 `Disjoint.symm_iff`

English:
theorem Disjoint.symm_iff
  given: (x y : Finmap β)
  statement: Disjoint x y ↔ Disjoint y x
  proof: ⟨Disjoint.symm x y, Disjoint.symm y x⟩

中文:
定理 Disjoint.symm_iff
  条件: (x y : Finmap β)
  结论: Disjoint x y ↔ Disjoint y x
  证明: ⟨Disjoint.symm x y, Disjoint.symm y x⟩

Depends on / 依赖: Disjoint, Disjoint.symm
-/
theorem Disjoint.symm_iff (x y : Finmap β) : Disjoint x y ↔ Disjoint y x :=
  ⟨Disjoint.symm x y, Disjoint.symm y x⟩

section

variable [DecidableEq α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel (@Disjoint α β)
  body: fun s₁ s₂ => inferInstanceAs Decidable (forall x in s₁, x ∉ s₂)

中文:
实例 :
  签名: DecidableRel (@Disjoint α β)
  定义体: fun s₁ s₂ => inferInstanceAs Decidable (forall x in s₁, x ∉ s₂)

Depends on / 依赖: Decidable
-/
instance : DecidableRel (@Disjoint α β) :=
fun s₁ s₂ => inferInstanceAs Decidable (forall x in s₁, x ∉ s₂)

/--
theorem `disjoint_union_left` / 定理 `disjoint_union_left`

English:
theorem disjoint_union_left
  given: (x y z : Finmap β)
  proof: by
  simp [Disjoint, Finmap.mem_union, or_imp, forall_and]

中文:
定理 disjoint_union_left
  条件: (x y z : Finmap β)
  证明: by
  simp [Disjoint, Finmap.mem_union, or_imp, forall_and]

Depends on / 依赖: Disjoint, Finmap, Finmap.mem_union, forall_and, mem_union, or_imp
-/
theorem disjoint_union_left (x y z : Finmap β) :
    Disjoint (x union y) z ↔ Disjoint x z ∧ Disjoint y z := by
  simp [Disjoint, Finmap.mem_union, or_imp, forall_and]

/--
theorem `disjoint_union_right` / 定理 `disjoint_union_right`

English:
theorem disjoint_union_right
  given: (x y z : Finmap β)
  proof: by
  rw [Disjoint.symm_iff]; rw [disjoint_union_left]; rw [Disjoint.symm_iff _ x]; rw [Disjoint.symm_iff _ x]

中文:
定理 disjoint_union_right
  条件: (x y z : Finmap β)
  证明: by
  rw [Disjoint.symm_iff]; rw [disjoint_union_left]; rw [Disjoint.symm_iff _ x]; rw [Disjoint.symm_iff _ x]

Depends on / 依赖: Disjoint, Disjoint.symm_iff, disjoint_union_left, symm_iff
-/
theorem disjoint_union_right (x y z : Finmap β) :
    Disjoint x (y union z) ↔ Disjoint x y ∧ Disjoint x z := by
  rw [Disjoint.symm_iff]; rw [disjoint_union_left]; rw [Disjoint.symm_iff _ x]; rw [Disjoint.symm_iff _ x]

/--
theorem `union_comm_of_disjoint` / 定理 `union_comm_of_disjoint`

English:
theorem union_comm_of_disjoint
  given: {s₁ s₂ : Finmap β}
  statement: Disjoint s₁ s₂ -> s₁ union s₂ = s₂ union s₁
  proof: induction_on₂ s₁ s₂ fun s₁ s₂ => by
    intro h
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_comm_of_disjoint h]

中文:
定理 union_comm_of_disjoint
  条件: {s₁ s₂ : Finmap β}
  结论: Disjoint s₁ s₂ -> s₁ union s₂ = s₂ union s₁
  证明: induction_on₂ s₁ s₂ fun s₁ s₂ => by
    intro h
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_comm_of_disjoint h]

Depends on / 依赖: AList.toFinmap_eq, AList.union_comm_of_disjoint, toFinmap_eq, union_comm_of_disjoint, union_toFinmap
-/
theorem union_comm_of_disjoint {s₁ s₂ : Finmap β} : Disjoint s₁ s₂ -> s₁ union s₂ = s₂ union s₁ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ => by
    intro h
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_comm_of_disjoint h]

/--
theorem `union_cancel` / 定理 `union_cancel`

English:
theorem union_cancel
  given: {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ s₃)
  proof: ⟨fun h'' => by
    apply ext_lookup
    intro x
    have : (s₁ union s₃).lookup x = (s₂ union s₃).lookup x := h'' ▸ rfl
    by_cases hs₁ : x in s₁
    · rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this
    · by_cases hs₂ : x in s₂
      · rwa [lookup_union_left_of_not_in (h

中文:
定理 union_cancel
  条件: {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ s₃)
  证明: ⟨fun h'' => by
    apply ext_lookup
    intro x
    have : (s₁ union s₃).lookup x = (s₂ union s₃).lookup x := h'' ▸ rfl
    by_cases hs₁ : x in s₁
    · rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this
    · by_cases hs₂ : x in s₂
      · rwa [lookup_union_left_of_not_in (h

Depends on / 依赖: ext_lookup, lookup, lookup_eq_none, lookup_eq_none.mpr, lookup_union_left, lookup_union_left_of_not_in
-/
theorem union_cancel {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ s₃) :
    s₁ union s₃ = s₂ union s₃ ↔ s₁ = s₂ :=
  ⟨fun h'' => by
    apply ext_lookup
    intro x
    have : (s₁ union s₃).lookup x = (s₂ union s₃).lookup x := h'' ▸ rfl
    by_cases hs₁ : x in s₁
    · rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this
    · by_cases hs₂ : x in s₂
      · rwa [lookup_union_left_of_not_in (h' _ hs₂), lookup_union_left hs₂] at this
      · rw [lookup_eq_none.mpr hs₁, lookup_eq_none.mpr hs₂], fun h => h ▸ rfl⟩

end

end Finmap
