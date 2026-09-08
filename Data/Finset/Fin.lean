/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Embedding

/-!
# Finsets in `Fin n`

A few constructions for Finsets in `Fin n`.

## Main declarations

* `Finset.attachFin`: Turns a Finset of naturals strictly less than `n` into a `Finset (Fin n)`.
-/

@[expose] public section


variable {n : ℕ}

namespace Finset

/-- Given a Finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding Finset in `Fin n`
is `s.attachFin h` where `h` is a proof that all elements of `s` are less than `n`. -/
/-
**Finset.attachFin** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：attachFin (s : Finset Nat) {n : Nat} (h : forall m in s, m < n) : Finset (
Fin n)
参数：s : Finset Nat；h : forall m in s, m < n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding Finset 
in `Fin n`
is `s.attachFin h` where `h` is a proof that all elements of `s` are less than `
n`.
-/
def attachFin (s : Finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : Finset (Fin n) :=
  ⟨s.1.pmap (fun a ha ↦ ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ ↦ Fin.val_eq_of_eq⟩

@[simp]
/-
**Finset.mem_attachFin** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_attachFin {s : Finset Nat} (h : forall m in s, m < n) {a : Fin n} : a 
in s.attachFin h ↔ (a : Nat) in s
参数：h : forall m in s, m < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_pmap`：mem_pmap {p : α -> Prop} {f : forall a, p a -> β} {s 
H b} : b in pmap f s H ↔ exists (a : _) (h : a in s), f a (H a h) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.eta`：∀ {n : ℕ} (a : Fin n) (h : ↑a < n), ⟨↑a, h⟩ = a
-/
theorem mem_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) {a : Fin n} :
    a ∈ s.attachFin h ↔ (a : ℕ) ∈ s :=
  ⟨fun h ↦
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h ↦ Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩

@[simp]
/-
**Finset.coe_attachFin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_attachFin {s : Finset Nat} (h : forall m in s, m < n) : (attachFin s h
 : Set (Fin n)) = Fin.val ⁻¹' s
参数：h : forall m in s, m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    (attachFin s h : Set (Fin n)) = Fin.val ⁻¹' s := by
  ext; simp

@[simp]
/-
**Finset.card_attachFin** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_attachFin (s : Finset Nat) (h : forall m in s, m < n) : (s.attachFin 
h).card = s.card
参数：s : Finset Nat；h : forall m in s, m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_pmap`：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (
s H) : card (pmap f s H) = card s
-/
theorem card_attachFin (s : Finset ℕ) (h : ∀ m ∈ s, m < n) :
    (s.attachFin h).card = s.card :=
  Multiset.card_pmap _ _ _

@[simp]
/-
**Finset.image_val_attachFin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_val_attachFin {s : Finset Nat} (h : forall m in s, m < n) : image Fi
n.val (s.attachFin h) = s
参数：h : forall m in s, m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `Finset.coe_attachFin`：coe_attachFin {s : Finset Nat} (h : forall m in s,
 m < n) : (attachFin s h : Set (Fin n)) = Fin.val ⁻¹' s
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
lemma image_val_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    image Fin.val (s.attachFin h) = s := by
  apply coe_injective
  rw [coe_image, coe_attachFin, Set.image_preimage_eq_iff]
  exact fun m hm ↦ ⟨⟨m, h m hm⟩, rfl⟩

@[simp]
/-
**Finset.map_valEmbedding_attachFin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_valEmbedding_attachFin {s : Finset Nat} (h : forall m in s, m < n) : m
ap Fin.valEmbedding (s.attachFin h) = s
参数：h : forall m in s, m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Fin.valEmbedding_apply`：∀ {n : ℕ}, ⇑Fin.valEmbedding = Fin.val
· 使用引理 `Finset.image_val_attachFin`：image_val_attachFin {s : Finset Nat} (h : fo
rall m in s, m < n) : image Fin.val (s.attachFin h) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_valEmbedding_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    map Fin.valEmbedding (s.attachFin h) = s := by
  simp [map_eq_image]

@[simp]
/-
**Finset.attachFin_subset_attachFin_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attachFin_subset_attachFin_iff {s t : Finset Nat} (hs : forall m in s, m <
 n) (ht : forall m in t, m < n) : s.attachFin hs subseteq t.attachFin ht ↔ s sub
seteq t
参数：hs : forall m in s, m < n；ht : forall m in t, m < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_subset_map`：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subs
eteq s₂.map f ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma attachFin_subset_attachFin_iff {s t : Finset ℕ} (hs : ∀ m ∈ s, m < n) (ht : ∀ m ∈ t, m < n) :
    s.attachFin hs ⊆ t.attachFin ht ↔ s ⊆ t := by
  simp [← map_subset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
/-
**Finset.attachFin_subset_attachFin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attachFin_subset_attachFin {s t : Finset Nat} (hst : s subseteq t) (ht : f
orall m in t, m < n) : s.attachFin (fun m hm => ht m (hst hm)) subseteq t.attach
Fin ht
参数：hst : s subseteq t；ht : forall m in t, m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma attachFin_subset_attachFin {s t : Finset ℕ} (hst : s ⊆ t) (ht : ∀ m ∈ t, m < n) :
    s.attachFin (fun m hm ↦ ht m (hst hm)) ⊆ t.attachFin ht := by simpa

@[simp]
/-
**Finset.attachFin_ssubset_attachFin_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attachFin_ssubset_attachFin_iff {s t : Finset Nat} (hs : forall m in s, m 
< n) (ht : forall m in t, m < n) : s.attachFin hs ⊂ t.attachFin ht ↔ s ⊂ t
参数：hs : forall m in s, m < n；ht : forall m in t, m < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_ssubset_map`：map_ssubset_map {s t : Finset α} : s.map f ⊂ t.m
ap f ↔ s ⊂ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.map_valEmbedding_attachFin`：map_valEmbedding_attachFin {s : Finse
t Nat} (h : forall m in s, m < n) : map Fin.valEmbedding (s.attachFin h) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma attachFin_ssubset_attachFin_iff {s t : Finset ℕ} (hs : ∀ m ∈ s, m < n) (ht : ∀ m ∈ t, m < n) :
    s.attachFin hs ⊂ t.attachFin ht ↔ s ⊂ t := by
  simp [← map_ssubset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
/-
**Finset.attachFin_ssubset_attachFin** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attachFin_ssubset_attachFin {s t : Finset Nat} (hst : s ⊂ t) (ht : forall 
m in t, m < n) : s.attachFin (fun m hm => ht m (hst.subset hm)) ⊂ t.attachFin ht
参数：hst : s ⊂ t；ht : forall m in t, m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
lemma attachFin_ssubset_attachFin {s t : Finset ℕ} (hst : s ⊂ t) (ht : ∀ m ∈ t, m < n) :
    s.attachFin (fun m hm ↦ ht m (hst.subset hm)) ⊂ t.attachFin ht := by simpa

end Finset

