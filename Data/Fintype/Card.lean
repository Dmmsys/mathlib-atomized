/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-!
# Cardinalities of finite types

This file defines the cardinality `Fintype.card α` as the number of elements in `(univ : Finset α)`.
We also include some elementary results on the values of `Fintype.card` on specific types.

## Main declarations

* `Fintype.card α`: Cardinality of a fintype. Equal to `Finset.univ.card`.
* `Finite.surjective_of_injective`: an injective function from a finite type to
  itself is also surjective.

-/

@[expose] public section

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
/-
**Fintype.card** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：card (α) [Fintype α] : Nat
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`card α` is the number of elements in `α`, defined when `α` is a fintype.
-/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
/-
**Fintype.subtype_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：subtype_card {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p 
x) : @card { x // p x } (Fintype.subtype s H) = #s
参数：s : Finset α；H : forall x : α, x in s ↔ p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_pmap`：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (
s H) : card (pmap f s H) = card s
-/
theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s :=
  Multiset.card_pmap _ _ _
/-
**Fintype.card_of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_of_subtype {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔
 p x) [Fintype { x // p x }] : card { x // p x } = #s
参数：s : Finset α；H : forall x : α, x in s ↔ p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s := by
  rw [← subtype_card s H]
  congr!

@[simp]
/-
**Fintype.card_ofFinset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) :
 @Fintype.card p (ofFinset s H) = #s
参数：s : Finset α；H : forall x, x in s ↔ x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
-/
theorem card_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Fintype.card p (ofFinset s H) = #s :=
  Fintype.subtype_card s H
/-
**Fintype.card_of_finset'** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_of_finset' {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p)
 [Fintype p] : Fintype.card p = #s
参数：s : Finset α；H : forall x, x in s ↔ x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] :
    Fintype.card p = #s := by rw [← card_ofFinset s H]; congr!

end Fintype

namespace Fintype

/-
**Fintype.ofEquiv_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _
/-
**Fintype.card_congr** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
-/
theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr!

@[congr]
/-
**Fintype.card_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β
参数：h : α = β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])

/-- Note: this lemma is specifically about `Fintype.ofSubsingleton`. For a statement about
arbitrary `Fintype` instances, use either `Fintype.card_le_one_iff_subsingleton` or
`Fintype.card_unique`. -/
/-
**Fintype.card_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingl
eton a) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: this lemma is specifically about `Fintype.ofSubsingleton`. For a statement
 about
arbitrary `Fintype` instances, use either `Fintype.card_le_one_iff_subsingleton`
 or
`Fintype.card_unique`.
-/
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl

@[simp]
/-
**Fintype.card_unique** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fintype.card_ofSubsingleton`：card_ofSubsingleton (a : α) [Subsingleton α
] : @Fintype.card _ (ofSubsingleton a) = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

/-- Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement about
arbitrary `Fintype` instances, use `Fintype.card_eq_zero`. -/
/-
**Fintype.card_ofIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_ofIsEmpty [IsEmpty α] : @Fintype.card α Fintype.ofIsEmpty = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement abou
t
arbitrary `Fintype` instances, use `Fintype.card_eq_zero`.
-/
theorem card_ofIsEmpty [IsEmpty α] : @Fintype.card α Fintype.ofIsEmpty = 0 :=
  rfl

end Fintype

namespace Set

variable {s t : Set α}

-- We use an arbitrary `[Fintype s]` instance here,
-- not necessarily coming from a `[Fintype α]`.
@[simp]
/-
**Set.toFinset_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fint
ype.card s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

end Set

@[simp, grind =]
/-
**Finset.card_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α := rfl
/-
**Finset.eq_univ_of_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : #s = Fintype.card 
α) : s = univ
参数：s : Finset α；hs : #s = Fintype.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : #s = Fintype.card α) :
    s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by rw [hs, Finset.card_univ]
/-
**Finset.card_eq_iff_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : #s = Fintype.card 
α ↔ s = univ
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_card`：Finset.eq_univ_of_card [Fintype α] (s : Finset α
) (hs : #s = Fintype.card α) : s = univ
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : #s = Fintype.card α ↔ s = univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩
/-
**Finset.card_le_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_le_univ [Fintype α] (s : Finset α) : #s <= Fintype.card α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem Finset.card_le_univ [Fintype α] (s : Finset α) : #s ≤ Fintype.card α :=
  card_le_card (subset_univ s)
/-
**Finset.card_lt_univ_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_lt_univ_of_notMem [Fintype α] {s : Finset α} {x : α} (hx : x ∉
 s) : #s < Fintype.card α
参数：hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem Finset.card_lt_univ_of_notMem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    #s < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩
/-
**Finset.card_lt_iff_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) : #s < Fintype.card 
α ↔ s != Finset.univ
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
-/
theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    #s < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)
/-
**Finset.card_compl_lt_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset 
α) : #sᶜ < Fintype.card α ↔ s.Nonempty
参数：s : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.card_lt_iff_ne_univ`：Finset.card_lt_iff_ne_univ [Fintype α] (s : 
Finset α) : #s < Fintype.card α ↔ s != Finset.univ
· 使用定理 `Finset.compl_ne_univ_iff_nonempty`：compl_ne_univ_iff_nonempty (s : Finse
t α) : sᶜ != univ ↔ s.Nonempty
-/
theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    #sᶜ < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty
/-
**Finset.card_univ_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_univ_sdiff [DecidableEq α] [Fintype α] (s : Finset α) : #(univ
 \ s) = Fintype.card α - #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.card_univ_sdiff [DecidableEq α] [Fintype α] (s : Finset α) :
    #(univ \ s) = Fintype.card α - #s := by grind

@[deprecated (since := "2026-06-03")] alias Finset.card_univ_diff := Finset.card_univ_sdiff
/-
**Finset.card_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #sᶜ = Finty
pe.card α - #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_univ_sdiff`：Finset.card_univ_sdiff [DecidableEq α] [Fintype 
α] (s : Finset α) : #(univ \ s) = Fintype.card α - #s
-/
theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #sᶜ = Fintype.card α - #s :=
  Finset.card_univ_sdiff s

@[simp]
/-
**Finset.card_add_card_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #s
 + #sᶜ = Fintype.card α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
-/
theorem Finset.card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    #s + #sᶜ = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

@[simp]
/-
**Finset.card_compl_add_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_compl_add_card [DecidableEq α] [Fintype α] (s : Finset α) : #s
ᶜ + #s = Fintype.card α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Finset.card_add_card_compl`：Finset.card_add_card_compl [DecidableEq α] [
Fintype α] (s : Finset α) : #s + #sᶜ = Fintype.card α
-/
theorem Finset.card_compl_add_card [DecidableEq α] [Fintype α] (s : Finset α) :
    #sᶜ + #s = Fintype.card α := by
  rw [Nat.add_comm, card_add_card_compl]
/-
**Finset.compl_eq_of_disjoint_of_card_add_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.compl_eq_of_disjoint_of_card_add_eq {ι : Type*} [DecidableEq ι] [Fi
ntype ι] {S₁ S₂ : Finset ι} (h : Disjoint S₁ S₂) (h' : S₁.card + S₂.card = Finse
t.card (.univ : Finset ι)) : S₁ᶜ = S₂
参数：h : Disjoint S₁ S₂；h' : S₁.card + S₂.card = Finset.card (.univ : Finset ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : 
s subseteq tᶜ ↔ Disjoint t s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_add_card_compl`：Finset.card_add_card_compl [DecidableEq α] [
Fintype α] (s : Finset α) : #s + #sᶜ = Fintype.card α
-/
theorem Finset.compl_eq_of_disjoint_of_card_add_eq
    {ι : Type*} [DecidableEq ι] [Fintype ι] {S₁ S₂ : Finset ι} (h : Disjoint S₁ S₂)
    (h' : S₁.card + S₂.card = Finset.card (.univ : Finset ι)) :
    S₁ᶜ = S₂ :=
  (Finset.eq_of_subset_of_card_le
    (by rwa [Finset.subset_compl_iff_disjoint_left])
    (by simp [← Nat.add_le_add_iff_left (n := S₁.card), h'])).symm
/-
**Fintype.card_compl_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ :
 Sort _)] : Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s
参数：s : Set α；↥sᶜ : Sort _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
-/
theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)] :
    Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]
/-
**Fintype.card_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] : Fintype.card { 
x // x = y } = 1
参数：y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
-/
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique
/-
**Fintype.card_subtype_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] : Fintype.card {
 x // y = x } = 1
参数：y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
-/
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique
/-
**Fintype.card_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_empty : Fintype.card Empty = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl
/-
**Fintype.card_pempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_pempty : Fintype.card PEmpty = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl
/-
**Fintype.card_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_unit : Fintype.card Unit = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

@[simp]
/-
**Fintype.card_punit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_punit : Fintype.card PUnit = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

@[simp]
/-
**Fintype.card_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_bool : Fintype.card Bool = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

@[simp]
/-
**Fintype.card_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fint
ype.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
/-
**Fintype.card_plift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fint
ype.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
/-
**Fintype.card_orderDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintyp
e.card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl

@[simp]
/-
**Fintype.card_lex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.
card α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl

-- Note: The extra hypothesis `h` is there so that the rewrite lemma applies,
-- no matter what instance of `Fintype (Set.univ : Set α)` is used.
/-
**Fintype.card_setUniv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_setUniv [Fintype α] {h : Fintype (Set.univ : Set α)} : Fintyp
e.card (Set.univ : Set α) = Fintype.card α
参数：Set.univ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_of_finset'`：card_of_finset' {p : Set α} (s : Finset α) (H :
 forall x, x in s ↔ x in p) [Fintype p] : Fintype.card p = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Fintype.card_setUniv [Fintype α] {h : Fintype (Set.univ : Set α)} :
    Fintype.card (Set.univ : Set α) = Fintype.card α := by
  apply Fintype.card_of_finset'
  simp

@[simp]
/-
**Fintype.card_subtype_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_true [Fintype α] {h : Fintype {_a : α // True}} : @Fi
ntype.card {_a // True} h = Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Fintype.card_subtype_true [Fintype α] {h : Fintype {_a : α // True}} :
    @Fintype.card {_a // True} h = Fintype.card α := by
  apply Fintype.card_of_subtype
  simp

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
@[instance_reducible]
/-
**Fintype.sumLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.sumLeft {α β} [Fintype (α oplus β)] : Fintype α
参数：α oplus β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)

--- 原说明 ---
Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable a
s it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty.
-/
noncomputable def Fintype.sumLeft {α β} [Fintype (α ⊕ β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
@[instance_reducible]
/-
**Fintype.sumRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.sumRight {α β} [Fintype (α oplus β)] : Fintype β
参数：α oplus β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)

--- 原说明 ---
Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable a
s it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty.
-/
noncomputable def Fintype.sumRight {α β} [Fintype (α ⊕ β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective
/-
**Finite.exists_univ_list** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.exists_univ_list (α) [Finite α] : exists l : List α, l.Nodup ∧ fora
ll x : α, x in l
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Finset.mem_univ_val`：mem_univ_val : forall x, x in (univ : Finset α).1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Finite.exists_univ_list (α) [Finite α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l := by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩
/-
**List.Nodup.length_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodu
p) : l.length <= Fintype.card α
参数：h : l.Nodup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `List.toFinset_card_of_nodup`：List.toFinset_card_of_nodup {l : List α} (h
 : l.Nodup) : #l.toFinset = l.length
-/
theorem List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length ≤ Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

namespace Fintype

variable [Fintype α] [Fintype β]

/-
**Fintype.card_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_of_injective (f : α -> β) (hf : Function.Injective f) : card α <= 
card β
参数：f : α -> β；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h
/-
**Fintype.not_injective_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：not_injective_of_card_lt (f : α -> β) (h : card β < card α) : ¬Function.In
jective f
参数：f : α -> β；h : card β < card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_le_of_lt`：∀ {a b : ℕ}, a < b → ¬b ≤ a
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
-/
theorem not_injective_of_card_lt (f : α → β) (h : card β < card α) :
    ¬Function.Injective f :=
  Nat.not_le_of_lt h ∘ card_le_of_injective f
/-
**Fintype.card_le_of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_of_embedding (f : α ↪ β) : card α <= card β
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2
/-
**Fintype.card_lt_of_injective_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_lt_of_injective_of_notMem (f : α -> β) (h : Function.Injective f) {b 
: β} (w : b ∉ Set.range f) : card α < card β
参数：f : α -> β；h : Function.Injective f；w : b ∉ Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_lt_univ_of_notMem`：Finset.card_lt_univ_of_notMem [Fintype α]
 {s : Finset α} {x : α} (hx : x ∉ s) : #s < Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem card_lt_of_injective_of_notMem (f : α → β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_notMem (x := b) <| by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

/-- Given an injective map `f : α → β` such that `β` has cardinality one more
than `α`, there exists a unique element of `β` not in the image of `f`. -/
/-
**Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one** 是 Mathlib 
中的一个定理，位于命名空间 `Fintype`。
形式化陈述：existsUnique_notMem_image_of_injective_of_card_eq_add_one [DecidableEq β] 
(f : α -> β) (hf : f.Injective) (h : card β = card α + 1) : exists! x, x ∉ univ.
image f
参数：f : α -> β；hf : f.Injective；h : card β = card α + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one`：existsUniq
ue_notMem_image_of_injOn_of_card_eq_add_one {t : Finset β} [DecidableEq β] (hf :
 Set.InjOn f s) (hf' : Set.MapsTo f s t) (h : #t =…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)

--- 原说明 ---
Given an injective map `f : α → β` such that `β` has cardinality one more
than `α`, there exists a unique element of `β` not in the image of `f`.
-/
theorem existsUnique_notMem_image_of_injective_of_card_eq_add_one [DecidableEq β]
    (f : α → β) (hf : f.Injective) (h : card β = card α + 1) : ∃! x, x ∉ univ.image f := by
    simpa using existsUnique_notMem_image_of_injOn_of_card_eq_add_one
      (s := .univ) (t := .univ) (Set.injOn_of_injective hf) (by simp) (by simpa)
/-
**Fintype.card_lt_of_injective_not_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype
`。
形式化陈述：card_lt_of_injective_not_surjective (f : α -> β) (h : Function.Injective f
) (h' : ¬Function.Surjective f) : card α < card β
参数：f : α -> β；h : Function.Injective f；h' : ¬Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Fintype.card_lt_of_injective_of_notMem`：card_lt_of_injective_of_notMem (
f : α -> β) (h : Function.Injective f) {b : β} (w : b ∉ Set.range f) : card α < 
card β
-/
theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_notMem f h hy
/-
**Fintype.card_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_of_surjective (f : α -> β) (h : Function.Surjective f) : card β <=
 card α
参数：f : α -> β；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surjInv h)

set_option backward.isDefEq.respectTransparency false in
/-
**Fintype.card_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_range_le {α β : Type*} (f : α -> β) [Fintype α] [Fintype (Set.range f
)] : Fintype.card (Set.range f) <= Fintype.card α
参数：f : α -> β；Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem card_range_le {α β : Type*} (f : α → β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩
/-
**Fintype.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_range {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [
Fintype α] [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α
参数：f : F；Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
-/
theorem card_range {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective _ <| EmbeddingLike.injective f
/-
**Fintype.card_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ Is
Empty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]
/-
**Fintype.card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], Fintype.card α = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
-/
@[simp] theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero

/-- A `Fintype` with cardinality zero is equivalent to `Empty`. -/
/-
**Fintype.cardEqZeroEquivEquivEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty)
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A `Fintype` with cardinality zero is equivalent to `Empty`.
-/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm
/-
**Fintype.card_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_pos_iff : 0 < card α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
-/
theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  Nat.pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm
/-
**Fintype.card_pos** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_pos [h : Nonempty α] : 0 < card α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
-/
theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

@[simp]
/-
**Fintype.card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_ne_zero [Nonempty α] : card α != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
-/
theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  _root_.ne_of_gt card_pos
/-
**Fintype.** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : NeZero (card α) := ⟨card_ne_zero⟩
/-
**Fintype.existsUnique_iff_card_one** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：existsUnique_iff_card_one {α} [Fintype α] (p : α -> Prop) [DecidablePred p
] : (exists! a : α, p a) ↔ #{x | p x} = 1
参数：p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem existsUnique_iff_card_one {α} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∃! a : α, p a) ↔ #{x | p x} = 1 := by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff, and_comm,
    mem_filter_univ]

nonrec theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and]
/-
**Fintype.card_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_of_bijective {f : α -> β} (hf : Bijective f) : card α = card β
参数：hf : Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)

end Fintype

namespace Finite

variable [Finite α]

/-
**Finite.surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：surjective_of_injective {f : α -> α} (hinj : Injective f) : Surjective f
参数：hinj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem surjective_of_injective {f : α → α} (hinj : Injective f) : Surjective f := by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
  exact ⟨y, h.2⟩
/-
**Finite.injective_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：injective_iff_surjective {f : α -> α} : Injective f ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.surjective_of_injective`：surjective_of_injective {f : α -> α} (hi
nj : Injective f) : Surjective f
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `Function.leftInverse_of_surjective_of_rightInverse`：∀ {α : Sort u_1} {β 
: Sort u_2} {f : α → β} {g : β → α},   Function.Surjective f → Function.RightInv
erse f g → Function.LeftInverse f g
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
-/
theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩
/-
**Finite.injective_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：injective_iff_bijective {f : α -> α} : Injective f ↔ Bijective f
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
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]
/-
**Finite.surjective_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：surjective_iff_bijective {f : α -> α} : Surjective f ↔ Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]
/-
**Finite.injective_iff_surjective_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：injective_iff_surjective_of_equiv {f : α -> β} (e : α ≃ β) : Injective f ↔
 Surjective f
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem injective_iff_surjective_of_equiv {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

alias ⟨_root_.Function.Injective.bijective_of_finite, _⟩ := injective_iff_bijective

alias ⟨_root_.Function.Surjective.bijective_of_finite, _⟩ := surjective_iff_bijective

alias ⟨_root_.Function.Injective.surjective_of_finite,
    _root_.Function.Surjective.injective_of_finite⟩ :=
  injective_iff_surjective_of_equiv

end Finite

@[simp]
/-
**Fintype.card_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_of_finset'`：card_of_finset' {p : Set α} (s : Finset α) (H :
 forall x, x in s ↔ x in p) [Fintype p] : Fintype.card p = #s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s :=
  @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

/-- We can inflate a set `s` to any bigger size. -/
/-
**Finset.exists_superset_card_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.exists_superset_card_eq [Fintype α] {n : Nat} {s : Finset α} (hsn :
 #s <= n) (hnα : n <= Fintype.card α) : exists t, s subseteq t ∧ #t = n
参数：hsn : #s <= n；hnα : n <= Fintype.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ

--- 原说明 ---
We can inflate a set `s` to any bigger size.
-/
lemma Finset.exists_superset_card_eq [Fintype α] {n : ℕ} {s : Finset α} (hsn : #s ≤ n)
    (hnα : n ≤ Fintype.card α) :
    ∃ t, s ⊆ t ∧ #t = n := by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]
/-
**Fintype.card_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_prop : Fintype.card Prop = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_prop : Fintype.card Prop = 2 :=
  rfl
/-
**set_fintype_card_le_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] : Fintype.car
d s <= Fintype.card α
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
-/
theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype (· ∈ s))
/-
**set_fintype_card_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] : Fintype
.card s = Fintype.card α ↔ s = Set.univ
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `Set.toFinset_inj`：toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s
.toFinset = t.toFinset ↔ s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]
/-
**Fintype.card_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_le [Fintype α] (p : α -> Prop) [Fintype {a // p a}] :
 Fintype.card { x // p x } <= Fintype.card α
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
-/
theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [Fintype {a // p a}] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)
/-
**Fintype.card_subtype_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_lt [Fintype α] {p : α -> Prop} [Fintype {a // p a}] {
x : α} (hx : ¬p x) : Fintype.card { x // p x } < Fintype.card α
参数：hx : ¬p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_lt_of_injective_of_notMem`：card_lt_of_injective_of_notMem (
f : α -> β) (h : Function.Injective f) {b : β} (w : b ∉ Set.range f) : card α < 
card β
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
lemma Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [Fintype {a // p a}] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_notMem (b := x) (↑) Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]
/-
**Fintype.card_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype [Fintype α] (p : α -> Prop) [Fintype {a // p a}] [Dec
idablePred p] : Fintype.card { x // p x } = #{x | p x}
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [Fintype {a // p a}] [DecidablePred p] :
    Fintype.card { x // p x } = #{x | p x} := by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]
/-
**Fintype.card_subtype_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_compl [Fintype α] (p : α -> Prop) [Fintype { x // p x
 }] [Fintype { x // ¬p x }] : Fintype.card { x // ¬p x } = Fintype.card α - Fint
ype.card { x // p x }
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
-/
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ), Set.toFinset_compl,
      Finset.card_compl, Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_ofPred]
/-
**Fintype.card_subtype_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_mono (p q : α -> Prop) (h : p <= q) [Fintype { x // p
 x }] [Fintype { x // q x }] : Fintype.card { x // p x } <= Fintype.card { x // 
q x }
参数：p q : α -> Prop；h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
-/
theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
/-
**Fintype.card_compl_eq_card_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_compl_eq_card_compl [Finite α] (p q : α -> Prop) [Fintype { x
 // p x }] [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }
] (h : Fintype.card { x // p x } = Fintype.card { x // q x }) : Fintype.card { x
 // ¬p x } = Fintype.card { x // ¬q x }
参数：p q : α -> Prop；h : Fintype.card { x // p x } = Fintype.card { x // q x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two subtypes of a fintype have equal cardinality, so do their complements.
-/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]
/-
**Fintype.card_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_quotient_le [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·)
 : α -> α -> Prop)] : Fintype.card (Quotient s) <= Fintype.card α
参数：s : Setoid α；(· ≈ ·) : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
-/
theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ Quotient.mk'_surjective
/-
**univ_eq_singleton_of_card_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α 
= 1) : (univ : Finset α) = {x}
参数：x : α；h : Fintype.card α = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  simp [h]

namespace Finite

variable [Finite α]

/-
**Finite.wellFounded_of_trans_of_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：wellFounded_of_trans_of_irrefl (r : α -> α -> Prop) [IsTrans α r] [Std.Irr
efl r] : WellFounded r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `not_forall_of_exists_not`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, ¬p x) →
 ¬∀ (x : α), p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
-/
theorem wellFounded_of_trans_of_irrefl (r : α → α → Prop) [IsTrans α r] [Std.Irrefl r] :
    WellFounded r := by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
    Finset.card_lt_card <| by
      simp_rw [lt_iff_le_not_ge, Finset.subset_iff, mem_filter_univ]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
  exact Subrelation.wf (this _ _) (measure _).wf

-- See note [lower instance priority]
@[to_dual]
/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) to_wellFoundedLT [Preorder α] : WellFoundedLT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

end Finite

-- Shortcut instances to make sure those are found even in the presence of other instances
-- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/WellFoundedLT.20Prop.20is.20not.20found.20when.20importing.20too.20much
/-
**Bool.instWellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instWellFoundedLT : WellFoundedLT Bool
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
-/
instance Bool.instWellFoundedLT : WellFoundedLT Bool := inferInstance
/-
**Bool.instWellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instWellFoundedGT : WellFoundedGT Bool
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
-/
instance Bool.instWellFoundedGT : WellFoundedGT Bool := inferInstance
/-
**Prop.instWellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instWellFoundedLT : WellFoundedLT Prop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
-/
instance Prop.instWellFoundedLT : WellFoundedLT Prop := inferInstance
/-
**Prop.instWellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instWellFoundedGT : WellFoundedGT Prop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
-/
instance Prop.instWellFoundedGT : WellFoundedGT Prop := inferInstance

section Trunc

/-- A `Fintype` with positive cardinality constructively contains an element.
-/
/-
**truncOfCardPos** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α
参数：h : 0 < Fintype.card α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

end Trunc

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `Fintype.card`).

The major premise is `Fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_elim]
/-
**Fintype.induction_subsingleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.induction_subsingleton_or_nontrivial {P : forall (α) [Fintype α], 
Prop} (α : Type*) [Fintype α] (hbase : forall (α) [Fintype α] [Subsingleton α], 
P α) (hstep : forall (α) [Fintype α] [Nontrivial α], (forall (β) [Fintype β], Fi
ntype.card β < Fintype.card α -> P β) -> P α) : P α
参数：α；α : Type*；hbase : forall (α) [Fintype α] [Subsingleton α], P α；hstep : fora
ll (α) [Fintype α] [Nontrivial α], (forall (β) [Fintype β], Fintype.card β < Fin
type.card α -> P β) -> P α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothes
is for
smaller types (via `Fintype.card`).

The major premise is `Fintype α`, so to use this with the `induction` tactic you
 have to give a name
to that instance and use that name.
-/
theorem Fintype.induction_subsingleton_or_nontrivial {P : ∀ (α) [Fintype α], Prop} (α : Type*)
    [Fintype α] (hbase : ∀ (α) [Fintype α] [Subsingleton α], P α)
    (hstep : ∀ (α) [Fintype α] [Nontrivial α],
      (∀ (β) [Fintype β], Fintype.card β < Fintype.card α → P β) → P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl

section Fin

@[simp]
/-
**Fintype.card_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
-/
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  List.length_finRange
/-
**Fintype.card_fin_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_fin_lt_of_le {m n : Nat} (h : m <= n) : Fintype.card {i : Fin
 n // i < m} = m
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem Fintype.card_fin_lt_of_le {m n : ℕ} (h : m ≤ n) :
    Fintype.card {i : Fin n // i < m} = m := by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ ↦ ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ ↦ ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩ }
/-
**Finset.card_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.card_fin (n : ℕ) : #(univ : Finset (Fin n)) = n := by simp

/-- `Fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
/-
**fin_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fin_injective : Function.Injective Fin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β

--- 原说明 ---
`Fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statem
ent about
equality of types, using it should be avoided if possible.
-/
theorem fin_injective : Function.Injective Fin := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)
/-
**Fin.val_eq_val_of_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.val_eq_val_of_heq {k l : Nat} {i : Fin k} {j : Fin l} (h : i ≍ j) : (i
 : Nat) = (j : Nat)
参数：h : i ≍ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.heq_ext_iff`：∀ {k l : ℕ}, k = l → ∀ {i : Fin k} {j : Fin l}, i ≍ j ↔
 ↑i = ↑j
· 使用定理 `fin_injective`：fin_injective : Function.Injective Fin
· 使用定理 `type_eq_of_heq`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → α = β
-/
theorem Fin.val_eq_val_of_heq {k l : ℕ} {i : Fin k} {j : Fin l} (h : i ≍ j) :
    (i : ℕ) = (j : ℕ) :=
  (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

/-- A reversed version of `Fin.cast_eq_cast` that is easier to rewrite with. -/
/-
**Fin.cast_eq_cast'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.cast_eq_cast' {n m : Nat} (h : Fin n = Fin m) : _root_.cast h = Fin.ca
st (fin_injective h)
参数：h : Fin n = Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fin_injective`：fin_injective : Function.Injective Fin
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A reversed version of `Fin.cast_eq_cast` that is easier to rewrite with.
-/
theorem Fin.cast_eq_cast' {n m : ℕ} (h : Fin n = Fin m) :
    _root_.cast h = Fin.cast (fin_injective h) := by
  cases fin_injective h
  rfl
/-
**card_finset_fin_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_finset_fin_le {n : Nat} (s : Finset (Fin n)) : #s <= n
参数：s : Finset (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
-/
theorem card_finset_fin_le {n : ℕ} (s : Finset (Fin n)) : #s ≤ n := by
  simpa only [Fintype.card_fin] using s.card_le_univ

end Fin

