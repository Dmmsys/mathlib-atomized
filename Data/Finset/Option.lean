/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

/-!
# Finite sets in `Option α`

In this file we define

* `Option.toFinset`: construct an empty or singleton `Finset α` from an `Option α`;
* `Finset.insertNone`: given `s : Finset α`, lift it to a finset on `Option α` using `Option.some`
  and then insert `Option.none`;
* `Finset.eraseNone`: given `s : Finset (Option α)`, returns `t : Finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/

@[expose] public section


variable {α β : Type*}

open Function

namespace Option

/-- Construct an empty or singleton finset from an `Option` -/
/-
**Option.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Option`。
形式化陈述：toFinset (o : Option α) : Finset α
参数：o : Option α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an empty or singleton finset from an `Option`
-/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton

@[simp]
/-
**Option.toFinset_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：toFinset_none : none.toFinset = (∅ : Finset α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl

@[simp]
/-
**Option.toFinset_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：toFinset_some {a : α} : (some a).toFinset = {a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl

@[simp]
/-
**Option.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：mem_toFinset {a : α} {o : Option α} : a in o.toFinset ↔ a in o
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem mem_toFinset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
/-
**Option.card_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1
参数：o : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl

end Option

namespace Finset

/-- Given a finset on `α`, lift it to being a finset on `Option α`
using `Option.some` and then insert `Option.none`. -/
/-
**Finset.insertNone** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：insertNone : Finset α ↪o Finset (Option α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset on `α`, lift it to being a finset on `Option α`
using `Option.some` and then insert `Option.none`.
-/
def insertNone : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t => by
    rw [cons_subset_cons, map_subset_map]

@[simp]
/-
**Finset.mem_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {o : Option α}, o ∈ Finset.insertNone s ↔ 
∀ a ∈ o, a ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_insertNone {s : Finset α} : ∀ {o : Option α}, o ∈ insertNone s ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp
/-
**Finset.forall_mem_insertNone** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：forall_mem_insertNone {s : Finset α} {p : Option α -> Prop} : (forall a in
 insertNone s, p a) ↔ p none ∧ forall a in s, p a
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma forall_mem_insertNone {s : Finset α} {p : Option α → Prop} :
    (∀ a ∈ insertNone s, p a) ↔ p none ∧ ∀ a ∈ s, p a := by simp [Option.forall]
/-
**Finset.some_mem_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：some_mem_insertNone {s : Finset α} {a : α} : some a in insertNone s ↔ a in
 s
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
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem some_mem_insertNone {s : Finset α} {a : α} : some a ∈ insertNone s ↔ a ∈ s := by simp
/-
**Finset.none_mem_insertNone** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：none_mem_insertNone {s : Finset α} : none in insertNone s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma none_mem_insertNone {s : Finset α} : none ∈ insertNone s := by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.insertNone_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, (Finset.insertNone s).Nonempty
参数：Finset.insertNone s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.none_mem_insertNone`：none_mem_insertNone {s : Finset α} : none in
 insertNone s
-/
lemma insertNone_nonempty {s : Finset α} : insertNone s |>.Nonempty := ⟨none, none_mem_insertNone⟩

@[simp]
/-
**Finset.card_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insertNone]

/-- Given `s : Finset (Option α)`, `eraseNone s : Finset α` is the set of `x : α` such that
`some x ∈ s`. -/
/-
**Finset.eraseNone** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：eraseNone : Finset (Option α) ->o Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `s : Finset (Option α)`, `eraseNone s : Finset α` is the set of `x : α` su
ch that
`some x ∈ s`.
-/
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]
/-
**Finset.mem_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_eraseNone {s : Finset (Option α)} {x : α} : x in eraseNone s ↔ some x 
in s
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `OrderEmbedding.toOrderHom_coe`：∀ {X : Type u_6} {Y : Type u_7} [inst : P
reorder X] [inst_1 : Preorder Y] (f : X ↪o Y), ⇑f.toOrderHom = ⇑f
· 使用定理 `Equiv.optionIsSomeEquiv_symm_apply_coe`：∀ (α : Type u_4) (x : α), ↑((Equ
iv.optionIsSomeEquiv α).symm x) = some x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x ∈ eraseNone s ↔ some x ∈ s := by
  simp [eraseNone]
/-
**Finset.forall_mem_eraseNone** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：forall_mem_eraseNone {s : Finset (Option α)} {p : Option α -> Prop} : (for
all a in eraseNone s, p a) ↔ forall a : α, (a : Option α) in s -> p a
参数：Option α。
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
lemma forall_mem_eraseNone {s : Finset (Option α)} {p : Option α → Prop} :
    (∀ a ∈ eraseNone s, p a) ↔ ∀ a : α, (a : Option α) ∈ s → p a := by simp
/-
**Finset.eraseNone_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) : eraseNone s
 = s.biUnion Option.toFinset
参数：s : Finset (Option α)。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) :
    eraseNone s = s.biUnion Option.toFinset := by
  ext
  simp

@[simp]
/-
**Finset.eraseNone_map_some** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_map_some (s : Finset α) : eraseNone (s.map Embedding.some) = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_map_some (s : Finset α) : eraseNone (s.map Embedding.some) = s := by
  ext
  simp

@[simp]
/-
**Finset.eraseNone_image_some** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) : eraseNone (
s.image some) = s
参数：Option α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.eraseNone_map_some`：eraseNone_map_some (s : Finset α) : eraseNone
 (s.map Embedding.some) = s
-/
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    eraseNone (s.image some) = s := by simpa only [map_eq_image] using! eraseNone_map_some s

@[simp]
/-
**Finset.coe_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_eraseNone (s : Finset (Option α)) : (eraseNone s : Set α) = some ⁻¹' s
参数：s : Finset (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_eraseNone`：mem_eraseNone {s : Finset (Option α)} {x : α} : x 
in eraseNone s ↔ some x in s
-/
theorem coe_eraseNone (s : Finset (Option α)) : (eraseNone s : Set α) = some ⁻¹' s :=
  Set.ext fun _ => mem_eraseNone

@[simp]
/-
**Finset.eraseNone_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Op
tion α)) : eraseNone (s union t) = eraseNone s union eraseNone t
参数：Option α；s t : Finset (Option α)。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∪ t) = eraseNone s ∪ eraseNone t := by
  ext
  simp

@[simp]
/-
**Finset.eraseNone_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Op
tion α)) : eraseNone (s inter t) = eraseNone s inter eraseNone t
参数：Option α；s t : Finset (Option α)。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    eraseNone (s ∩ t) = eraseNone s ∩ eraseNone t := by
  ext
  simp

@[simp]
/-
**Finset.eraseNone_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_empty : eraseNone (∅ : Finset (Option α)) = ∅
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_empty : eraseNone (∅ : Finset (Option α)) = ∅ := by
  ext
  simp

@[simp]
/-
**Finset.eraseNone_none** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_none : eraseNone ({none} : Finset (Option α)) = ∅
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
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_none : eraseNone ({none} : Finset (Option α)) = ∅ := by
  ext
  simp

@[simp]
/-
**Finset.image_some_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) : (e
raseNone s).image some = s.erase none
参数：Option α；s : Finset (Option α)。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).image some = s.erase none := by ext (_ | x) <;> simp

@[simp]
/-
**Finset.map_some_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) : (era
seNone s).map Embedding.some = s.erase none
参数：Option α；s : Finset (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `Finset.image_some_eraseNone`：image_some_eraseNone [DecidableEq (Option α
)] (s : Finset (Option α)) : (eraseNone s).image some = s.erase none
-/
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    (eraseNone s).map Embedding.some = s.erase none := by
  rw [map_eq_image, Embedding.some_apply, image_some_eraseNone]

@[simp]
/-
**Finset.insertNone_eraseNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) : in
sertNone (eraseNone s) = insert none s
参数：Option α；s : Finset (Option α)。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp

@[simp]
/-
**Finset.eraseNone_insertNone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s := by
  ext
  simp
/-
**Finset.card_eraseNone_eq_card_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eraseNone_eq_card_erase [DecidableEq (Option α)] (s : Finset (Option 
α)) : #s.eraseNone = #(s.erase none)
参数：Option α；s : Finset (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.map_some_eraseNone`：map_some_eraseNone [DecidableEq (Option α)] (
s : Finset (Option α)) : (eraseNone s).map Embedding.some = s.erase none
-/
theorem card_eraseNone_eq_card_erase [DecidableEq (Option α)] (s : Finset (Option α)) :
    #s.eraseNone = #(s.erase none) := by
  rw [← card_map Function.Embedding.some, map_some_eraseNone]
/-
**Finset.card_eraseNone_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eraseNone_le (s : Finset (Option α)) : #s.eraseNone <= #s
参数：s : Finset (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eraseNone_eq_card_erase`：card_eraseNone_eq_card_erase [Decid
ableEq (Option α)] (s : Finset (Option α)) : #s.eraseNone = #(s.erase none)
· 使用定理 `Finset.card_erase_le`：card_erase_le : #(s.erase a) <= #s
-/
theorem card_eraseNone_le (s : Finset (Option α)) : #s.eraseNone ≤ #s := by
  classical
  rw [card_eraseNone_eq_card_erase]
  apply card_erase_le
/-
**Finset.card_eraseNone_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eraseNone_of_mem {s : Finset (Option α)} (h : none in s) : #s.eraseNo
ne = #s - 1
参数：Option α；h : none in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eraseNone_eq_card_erase`：card_eraseNone_eq_card_erase [Decid
ableEq (Option α)] (s : Finset (Option α)) : #s.eraseNone = #(s.erase none)
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
-/
theorem card_eraseNone_of_mem {s : Finset (Option α)} (h : none ∈ s) : #s.eraseNone = #s - 1 := by
  classical rw [card_eraseNone_eq_card_erase, card_erase_of_mem h]
/-
**Finset.card_eraseNone_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eraseNone_of_not_mem {s : Finset (Option α)} (h : none ∉ s) : #s.eras
eNone = #s
参数：Option α；h : none ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eraseNone_eq_card_erase`：card_eraseNone_eq_card_erase [Decid
ableEq (Option α)] (s : Finset (Option α)) : #s.eraseNone = #(s.erase none)
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
-/
theorem card_eraseNone_of_not_mem {s : Finset (Option α)} (h : none ∉ s) : #s.eraseNone = #s := by
  classical rw [card_eraseNone_eq_card_erase, erase_eq_of_notMem h]

end Finset

