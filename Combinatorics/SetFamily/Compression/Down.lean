/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : Finset (Finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `Finset.nonMemberSubfamily`: `𝒜.nonMemberSubfamily a` is the subfamily of sets not containing
  `a`.
* `Finset.memberSubfamily`: `𝒜.memberSubfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `Down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `Down.compress a 𝒜` in scope `SetFamily`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

@[expose] public section


variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/-- Elements of `𝒜` that do not contain `a`. -/
/-
**Finset.nonMemberSubfamily** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：a : α；𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements of `𝒜` that do not contain `a`.
-/
def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) := {s ∈ 𝒜 | a ∉ s}

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
/-
**Finset.memberSubfamily** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：a : α；𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that 
do not contain
`a` such that `insert a s ∈ 𝒜`.
-/
def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜 | a ∈ s}.image fun s => erase s a

@[simp]
/-
**Finset.mem_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_nonMemberSubfamily : s in 𝒜.nonMemberSubfamily a ↔ s in 𝒜 ∧ a ∉ s
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
theorem mem_nonMemberSubfamily : s ∈ 𝒜.nonMemberSubfamily a ↔ s ∈ 𝒜 ∧ a ∉ s := by
  simp [nonMemberSubfamily]

@[simp]
/-
**Finset.mem_memberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_memberSubfamily : s in 𝒜.memberSubfamily a ↔ insert a s in 𝒜 ∧ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_memberSubfamily : s ∈ 𝒜.memberSubfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s := by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  rw [insert_erase hs2]
  exact ⟨hs1, notMem_erase _ _⟩
/-
**Finset.nonMemberSubfamily_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonMemberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) : (𝒜 inter ℬ).n
onMemberSubfamily a = 𝒜.nonMemberSubfamily a inter ℬ.nonMemberSubfamily a
参数：a : α；𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_inter_distrib`：filter_inter_distrib (s t : Finset α) : (s 
inter t).filter p = s.filter p inter t.filter p
-/
theorem nonMemberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∩ ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _
/-
**Finset.memberSubfamily_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：memberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) : (𝒜 inter ℬ).memb
erSubfamily a = 𝒜.memberSubfamily a inter ℬ.memberSubfamily a
参数：a : α；𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_inter_distrib`：filter_inter_distrib (s t : Finset α) : (s 
inter t).filter p = s.filter p inter t.filter p
· 使用定理 `Finset.image_inter_of_injOn`：image_inter_of_injOn [DecidableEq α] {f : α
 -> β} (s t : Finset α) (hf : Set.InjOn f (s union t)) : (s inter t).image f = s
.image f inter t.…
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.erase_injOn'`：erase_injOn' (a : α) : { s : Finset α | a in s }.In
jOn fun s => s.erase a
-/
theorem memberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∩ ℬ.memberSubfamily a := by
  unfold memberSubfamily
  rw [filter_inter_distrib, image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  simp
/-
**Finset.nonMemberSubfamily_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonMemberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) : (𝒜 union ℬ).n
onMemberSubfamily a = 𝒜.nonMemberSubfamily a union ℬ.nonMemberSubfamily a
参数：a : α；𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
-/
theorem nonMemberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∪ ℬ.nonMemberSubfamily a :=
  filter_union _ _ _
/-
**Finset.memberSubfamily_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：memberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) : (𝒜 union ℬ).memb
erSubfamily a = 𝒜.memberSubfamily a union ℬ.memberSubfamily a
参数：a : α；𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.image_union`：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Fi
nset α) : (s₁ union s₂).image f = s₁.image f union s₂.image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem memberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∪ ℬ.memberSubfamily a := by
  simp_rw [memberSubfamily, filter_union, image_union]
/-
**Finset.card_memberSubfamily_add_card_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命
名空间 `Finset`。
形式化陈述：card_memberSubfamily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Fins
et α)) : #(𝒜.memberSubfamily a) + #(𝒜.nonMemberSubfamily a) = #𝒜
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.memberSubfamily.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (a 
: α) (𝒜 : Finset (Finset α)),   Finset.memberSubfamily a 𝒜 = Finset.image (fun s
 => s.erase a) ({…
· 使用定理 `Finset.nonMemberSubfamily.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] 
(a : α) (𝒜 : Finset (Finset α)), Finset.nonMemberSubfamily a 𝒜 = {s ∈ 𝒜 | a ∉ s}
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Finset.erase_injOn'`：erase_injOn' (a : α) : { s : Finset α | a in s }.In
jOn fun s => s.erase a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_filter_add_card_filter_not`：card_filter_add_card_filter_not 
(p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : #(s.filter p) +
 #(s.filter fun a => ¬ p a) …
-/
theorem card_memberSubfamily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    #(𝒜.memberSubfamily a) + #(𝒜.nonMemberSubfamily a) = #𝒜 := by
  rw [memberSubfamily, nonMemberSubfamily, card_image_of_injOn]
  · conv_rhs => rw [← card_filter_add_card_filter_not (fun s => (a ∈ s))]
  · apply (erase_injOn' _).mono
    simp
/-
**Finset.memberSubfamily_union_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：memberSubfamily_union_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
 𝒜.memberSubfamily a union 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem memberSubfamily_union_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a ∪ 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a := by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_notMem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a ∈ s
    · exact Or.inl ⟨by rwa [insert_erase ha], notMem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_notMem ha], notMem_erase _ _⟩

@[simp]
/-
**Finset.memberSubfamily_memberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：memberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).memberSubfamily a 
= ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp

@[simp]
/-
**Finset.memberSubfamily_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：memberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).memberSubfam
ily a = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp

@[simp]
/-
**Finset.nonMemberSubfamily_memberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonMemberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).nonMemberSubfam
ily a = 𝒜.memberSubfamily a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonMemberSubfamily_memberSubfamily :
    (𝒜.memberSubfamily a).nonMemberSubfamily a = 𝒜.memberSubfamily a := by
  ext
  simp

@[simp]
/-
**Finset.nonMemberSubfamily_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：nonMemberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).nonMember
Subfamily a = 𝒜.nonMemberSubfamily a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonMemberSubfamily_nonMemberSubfamily :
    (𝒜.nonMemberSubfamily a).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a := by
  ext
  simp
/-
**Finset.memberSubfamily_image_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：memberSubfamily_image_insert (h𝒜 : forall s in 𝒜, a ∉ s) : (𝒜.image <| ins
ert a).memberSubfamily a = 𝒜
参数：h𝒜 : forall s in 𝒜, a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.insert_erase_invOn`：insert_erase_invOn : Set.InvOn (insert a) (fu
n s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s}
-/
lemma memberSubfamily_image_insert (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    (𝒜.image <| insert a).memberSubfamily a = 𝒜 := by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs ↦ ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [← insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]
/-
**Finset.nonMemberSubfamily_image_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {a : α},  
 Finset.nonMemberSubfamily a (Finset.image (insert a) 𝒜) = ∅
参数：Finset α；Finset.image (insert a) 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma nonMemberSubfamily_image_insert : (𝒜.image <| insert a).nonMemberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_notMem]
/-
**Finset.memberSubfamily_image_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {a : α},  
 Finset.memberSubfamily a (Finset.image (fun x => x.erase a) 𝒜) = ∅
参数：Finset α；Finset.image (fun x => x.erase a) 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma memberSubfamily_image_erase : (𝒜.image (erase · a)).memberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_notMem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (notMem_erase _ _)).symm]
/-
**Finset.image_insert_memberSubfamily** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_insert_memberSubfamily (𝒜 : Finset (Finset α)) (a : α) : (𝒜.memberSu
bfamily a).image (insert a) = {s in 𝒜 | a in s}
参数：𝒜 : Finset (Finset α)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
lemma image_insert_memberSubfamily (𝒜 : Finset (Finset α)) (a : α) :
    (𝒜.memberSubfamily a).image (insert a) = {s ∈ 𝒜 | a ∈ s} := by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ ↦ ⟨erase s a, ⟨?_, notMem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `ℬ ∪ {s ∪ {a} | s ∈ 𝒞}` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the
  ground type and `𝒜` and `ℬ` are families of finsets not containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you
  `𝒜 = ℬ ∪ {s ∪ {a} | s ∈ 𝒞}`, so that `ℬ = 𝒜.nonMemberSubfamily` and `𝒞 = 𝒜.memberSubfamily`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.family_induction_on.` -/
@[elab_as_elim]
/-
**Finset.memberFamily_induction_on** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：memberFamily_induction_on {p : Finset (Finset α) -> Prop} (𝒜 : Finset (Fin
set α)) (empty : p ∅) (singleton_empty : p {∅}) (subfamily : forall (a : α) ⦃𝒜 :
 Finset (Finset α)⦄, p (𝒜.nonMemberSubfamily a) -> p (𝒜.memberSubfamily a) -> p 
𝒜) : p 𝒜
参数：Finset α；𝒜 : Finset (Finset α)；empty : p ∅；singleton_empty : p {∅}；subfamily 
: forall (a : α) ⦃𝒜 : Finset (Finset α)⦄, p (𝒜.nonMemberSubfamily a) -> p (𝒜.mem
berSubfamily a) -> p 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subset_singleton_iff'`：subset_singleton_iff' {s : Finset α} {a : 
α} : s subseteq {a} ↔ forall b in s, b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_insert_iff_of_notMem`：subset_insert_iff_of_notMem (h : a ∉
 s) : s subseteq insert a t ↔ s subseteq t
· 使用定理 `Finset.insert_subset_insert_iff`：∀ {α : Type u_1} [inst : DecidableEq α]
 {s t : Finset α} {a : α}, a ∉ s → (insert a s ⊆ insert a t ↔ s ⊆ t)

--- 原说明 ---
Induction principle for finset families. To prove a statement for every finset f
amily,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `ℬ ∪ {s ∪ {a} | s ∈ 𝒞}` assuming the property for `ℬ` and `𝒞`, where `a` is an
 element of the
  ground type and `𝒜` and `ℬ` are families of finsets not containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you
  `𝒜 = ℬ ∪ {s ∪ {a} | s ∈ 𝒞}`, so that `ℬ = 𝒜.nonMemberSubfamily` and `𝒞 = 𝒜.mem
berSubfamily`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n
` elements.

See also `Finset.family_induction_on.`
-/
lemma memberFamily_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.nonMemberSubfamily a) → p (𝒜.memberSubfamily a) → p 𝒜) : p 𝒜 := by
  set u := 𝒜.sup id
  have hu : ∀ s ∈ 𝒜, s ⊆ u := fun s ↦ le_sup (f := id)
  clear_value u
  induction u using Finset.induction generalizing 𝒜 with
  | empty =>
    simp_rw [subset_empty] at hu
    rw [← subset_singleton_iff', subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  | insert a u _ ih =>
    refine subfamily a (ih _ ?_) (ih _ ?_)
    · simp only [mem_nonMemberSubfamily, and_imp]
      exact fun s hs has ↦ (subset_insert_iff_of_notMem has).1 <| hu _ hs
    · simp only [mem_memberSubfamily, and_imp]
      exact fun s hs ha ↦ (insert_subset_insert_iff ha).1 <| hu _ hs

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `{s ∪ {a} | s ∈ 𝒜}` assuming the property for `𝒜` a family of finsets not containing `a`.
* `ℬ ∪ 𝒞` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the ground type and
  `ℬ` is a family of finsets not containing `a` and `𝒞` a family of finsets containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you `𝒜 = ℬ ∪ 𝒞`, so that
  `ℬ = {s ∈ 𝒜 | a ∉ s}` and `𝒞 = {s ∈ 𝒜 | a ∈ s}`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.memberFamily_induction_on.` -/
@[elab_as_elim]
/-
**Finset.family_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {p : Finset (Finset α) → Prop} (𝒜 
: Finset (Finset α)),   p ∅ →     p {∅} →       (∀ (a : α) ⦃𝒜 : Finset (Finset α
)⦄, (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (Finset.image (insert a) 𝒜)) →         (∀ (a : α)
 ⦃𝒜 : Finset (Finset α)⦄, p ({s ∈ 𝒜 | a ∉ s}) → p ({s ∈ 𝒜 | a ∈ s}) → p 𝒜) → p 𝒜
参数：Finset α；𝒜 : Finset (Finset α)；∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄, (∀ s ∈ 𝒜, a
 ∉ s) → p 𝒜 → p (Finset.image (insert a) 𝒜)；∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄, p
 ({s ∈ 𝒜 | a ∉ s}) → p ({s ∈ 𝒜 | a ∈ s}) → p 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.memberFamily_induction_on`：memberFamily_induction_on {p : Finset 
(Finset α) -> Prop} (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {
∅}) (subfamily : foral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.image_insert_memberSubfamily`：image_insert_memberSubfamily (𝒜 : F
inset (Finset α)) (a : α) : (𝒜.memberSubfamily a).image (insert a) = {s in 𝒜 | a
 in s}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Induction principle for finset families. To prove a statement for every finset f
amily,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `{s ∪ {a} | s ∈ 𝒜}` assuming the property for `𝒜` a family of finsets not cont
aining `a`.
* `ℬ ∪ 𝒞` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the 
ground type and
  `ℬ` is a family of finsets not containing `a` and `𝒞` a family of finsets cont
aining `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you `𝒜 = ℬ
 ∪ 𝒞`, so that
  `ℬ = {s ∈ 𝒜 | a ∉ s}` and `𝒞 = {s ∈ 𝒜 | a ∈ s}`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n
` elements.

See also `Finset.memberFamily_induction_on.`
-/
protected lemma family_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (image_insert : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image <| insert a))
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p {s ∈ 𝒜 | a ∉ s} → p {s ∈ 𝒜 | a ∈ s} → p 𝒜) : p 𝒜 := by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ ↦ subfamily a h𝒜₀ ?_
  rw [← image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁

end Finset

open Finset

-- The namespace is here to distinguish from other compressions.
namespace Down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it, when the
resulting Finset is not already in `𝒜`. -/
/-
**Down.compression** 是 Mathlib 中的一个定义，位于命名空间 `Down`。
形式化陈述：compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α)
参数：a : α；𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contai
n it, when the
resulting Finset is not already in `𝒜`.
-/
def compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜 | erase s a ∈ 𝒜}.disjUnion {s ∈ 𝒜.image fun s ↦ erase s a | s ∉ 𝒜} <|
    disjoint_left.2 fun _s h₁ h₂ ↦ (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression

open FinsetFamily

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
/-
**Down.mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `Down`。
形式化陈述：mem_compression : s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a in 𝒜 ∨ s ∉ 𝒜 ∧ insert a 
s in 𝒜
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `or_congr_right`：∀ {b c a : Prop}, (b ↔ c) → (a ∨ b ↔ a ∨ c)
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.erase_ne_self`：erase_ne_self : s.erase a != s ↔ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.insert_ne_self`：insert_ne_self : insert a s != s ↔ a ∉ s

--- 原说明 ---
`a` is in the down-compressed family iff it's in the original and its compressio
n is in the
original, or it's not in the original but it's the compression of something in t
he original.
-/
theorem mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 := by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := s ∉ 𝒜)]
  refine
    or_congr_right
      (and_congr_left fun hs =>
        ⟨?_, fun h => ⟨_, h, erase_insert <| insert_ne_self.1 <| ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]
/-
**Down.erase_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `Down`。
形式化陈述：erase_mem_compression (hs : s in 𝒜) : s.erase a in 𝓓 a 𝒜
参数：hs : s in 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.erase_idem`：erase_idem {a : α} {s : Finset α} : erase (erase s a)
 a = erase s a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.erase_ne_self`：erase_ne_self : s.erase a != s ↔ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem erase_mem_compression (hs : s ∈ 𝒜) : s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine (em _).imp_right fun h => ⟨h, ?_⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
/-
**Down.erase_mem_compression_of_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `Down`
。
形式化陈述：erase_mem_compression_of_mem_compression : s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 
𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.erase_idem`：erase_idem {a : α} {s : Finset α} : erase (erase s a)
 a = erase s a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.insert_ne_self`：insert_ne_self : insert a s != s ↔ a ∉ s
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem]
  refine Or.imp (fun h => ⟨h.2, h.2⟩) fun h => ?_
  rwa [erase_eq_of_notMem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]
/-
**Down.mem_compression_of_insert_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `Down
`。
形式化陈述：mem_compression_of_insert_mem_compression (h : insert a s in 𝓓 a 𝒜) : s in
 𝓓 a 𝒜
参数：h : insert a s in 𝓓 a 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Down.erase_mem_compression_of_mem_compression`：erase_mem_compression_of_
mem_compression : s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 𝒜
-/
theorem mem_compression_of_insert_mem_compression (h : insert a s ∈ 𝓓 a 𝒜) : s ∈ 𝓓 a 𝒜 := by
  by_cases ha : a ∈ s
  · rwa [insert_eq_of_mem ha] at h
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h

/-- Down-compressing a family is idempotent. -/
@[simp]
/-
**Down.compression_idem** 是 Mathlib 中的一个定理，位于命名空间 `Down`。
形式化陈述：compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Down.mem_compression`：mem_compression : s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a 
in 𝒜 ∨ s ∉ 𝒜 ∧ insert a s in 𝒜
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Down.mem_compression_of_insert_mem_compression`：mem_compression_of_inser
t_mem_compression (h : insert a s in 𝓓 a 𝒜) : s in 𝓓 a 𝒜
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Down.erase_mem_compression_of_mem_compression`：erase_mem_compression_of_
mem_compression : s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 𝒜

--- 原说明 ---
Down-compressing a family is idempotent.
-/
theorem compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 := by
  ext s
  refine mem_compression.trans ⟨?_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)

/-- Down-compressing a family doesn't change its size. -/
@[simp]
/-
**Down.card_compression** 是 Mathlib 中的一个定理，位于命名空间 `Down`。
形式化陈述：card_compression (a : α) (𝒜 : Finset (Finset α)) : #(𝓓 a 𝒜) = #𝒜
参数：a : α；𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Down.compression.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (
𝒜 : Finset (Finset α)),   Down.compression a 𝒜 = {s ∈ 𝒜 | s.erase a ∈ 𝒜}.disjUni
on ({s ∈ Fi…
· 使用定理 `Finset.card_disjUnion`：card_disjUnion (s t : Finset α) (h) : #(s.disjUni
on t h) = #s + #t
· 使用定理 `Finset.filter_image`：filter_image {p : β -> Prop} [DecidablePred p] : (s
.image f).filter p = (s.filter fun a => p (f a)).image f
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.erase_injOn'`：erase_injOn' (a : α) : { s : Finset α | a in s }.In
jOn fun s => s.erase a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.disjoint_filter_filter_not`：disjoint_filter_filter_not (s t : Fin
set α) (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : Disjoint
 (s.filter p) (t.filter…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s

--- 原说明 ---
Down-compressing a family doesn't change its size.
-/
theorem card_compression (a : α) (𝒜 : Finset (Finset α)) : #(𝓓 a 𝒜) = #𝒜 := by
  rw [compression, card_disjUnion, filter_image,
    card_image_of_injOn ((erase_injOn' _).mono fun s hs => _), ← card_union_of_disjoint]
  · conv_rhs => rw [← filter_union_filter_not_eq (fun s => (erase s a ∈ 𝒜)) 𝒜]
  · exact disjoint_filter_filter_not 𝒜 𝒜 (fun s => (erase s a ∈ 𝒜))
  intro s hs
  rw [mem_coe, mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_notMem (ne_of_mem_of_not_mem hs.1 hs.2).symm

end Down

