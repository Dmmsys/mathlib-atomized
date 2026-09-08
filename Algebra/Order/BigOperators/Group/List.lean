/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Big operators on a list in ordered groups

This file contains the results concerning the interaction of list big operators with ordered
groups/monoids.
-/

public section

variable {ι α M N : Type*}

namespace List
section Monoid
variable [Monoid M]

@[to_additive sum_le_sum]
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Forall₂.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.prod ≤ l₂.prod := by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum /-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
  then `l₁.sum ≤ l₂.sum`.
  One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead of `∀ a ∈ l₂, 0 ≤ a`
  but this lemma is not yet in `mathlib`. -/]
/-
**List.Sublist.prod_le_prod'** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [MulRightMono M] 
[MulLeftMono M] {l₁ l₂ : List M},   l₁.Sublist l₂ → (∀ a ∈ l₂, 1 ≤ a) → l₁.prod 
≤ l₂.prod
参数：∀ a ∈ l₂, 1 ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
lemma Sublist.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.prod ≤ l₂.prod := by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons_cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    grw [ih' h₁.2]

@[to_additive sum_le_sum]
/-
**List.SublistForall** 是 Mathlib 中的一个引理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SublistForall₂.prod_le_prod' [Preorder M]
    [MulRightMono M] [MulLeftMono M]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.prod ≤ l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁

@[to_additive sum_le_sum]
/-
**List.prod_le_prod'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeftMono M] {l : List ι} {
f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).prod <= (l.map g).prod
参数：h : forall i in l, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.prod_le_prod'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 :
 Preorder M] [MulRightMono M] [MulLeftMono M] {l₁ l₂ : List M},   List.Forall₂ (
fun x1 x2 => x1 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod :=
  Forall₂.prod_le_prod' <| by simpa

@[to_additive sum_lt_sum]
/-
**List.prod_lt_prod'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_lt_prod' [Preorder M] [MulLeftStrictMono M] [MulLeftMono M] [MulRight
StrictMono M] [MulRightMono M] {l : List ι} (f g : ι -> M) (h₁ : forall i in l, 
f i <= g i) (h₂ : exists i in l, f i < g i) : (l.map f).prod < (l.map g).prod
参数：f g : ι -> M；h₁ : forall i in l, f i <= g i；h₂ : exists i in l, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用引理 `List.prod_le_prod'`：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeft
Mono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).
prod <= …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma prod_lt_prod' [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    cases h₂
    · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
    · exact mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 ‹_›

@[to_additive]
/-
**List.prod_lt_prod_of_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_lt_prod_of_ne_nil [Preorder M] [MulLeftStrictMono M] [MulLeftMono M] 
[MulRightStrictMono M] [MulRightMono M] {l : List ι} (hl : l != []) (f g : ι -> 
M) (hlt : forall i in l, f i < g i) : (l.map f).prod < (l.map g).prod
参数：hl : l != []；f g : ι -> M；hlt : forall i in l, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_lt_prod'`：prod_lt_prod' [Preorder M] [MulLeftStrictMono M] [Mu
lLeftMono M] [MulRightStrictMono M] [MulRightMono M] {l : List ι} (f g : ι -> M)
 (h₁ : f…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `List.exists_mem_of_ne_nil`：∀ {α : Type u_1} (l : List α), l ≠ [] → ∃ x, 
x ∈ l
-/
lemma prod_lt_prod_of_ne_nil [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]
/-
**List.prod_le_pow_card** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_le_pow_card [Preorder M] [MulRightMono M] [MulLeftMono M] (l : List M
) (n : M) (h : forall x in l, x <= n) : l.prod <= n ^ l.length
参数：l : List M；n : M；h : forall x in l, x <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_id'`：∀ {α : Type u_1} (l : List α), List.map (fun a => a) l = l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用引理 `List.prod_le_prod'`：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeft
Mono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).
prod <= …
-/
lemma prod_le_pow_card [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]
/-
**List.pow_card_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：pow_card_le_prod [Preorder M] [MulRightMono M] [MulLeftMono M] (l : List M
) (n : M) (h : forall x in l, n <= x) : n ^ l.length <= l.prod
参数：l : List M；n : M；h : forall x in l, n <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_le_pow_card`：prod_le_pow_card [Preorder M] [MulRightMono M] [M
ulLeftMono M] (l : List M) (n : M) (h : forall x in l, x <= n) : l.prod <= n ^ l
.length
-/
lemma pow_card_le_prod [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) :
    n ^ l.length ≤ l.prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt]
/-
**List.exists_lt_of_prod_lt'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：exists_lt_of_prod_lt' [LinearOrder M] [MulRightMono M] [MulLeftMono M] {l 
: List ι} (f g : ι -> M) (h : (l.map f).prod < (l.map g).prod) : exists i in l, 
f i < g i
参数：f g : ι -> M；h : (l.map f).prod < (l.map g).prod。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `List.prod_le_prod'`：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeft
Mono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).
prod <= …
-/
lemma exists_lt_of_prod_lt' [LinearOrder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} (f g : ι → M)
    (h : (l.map f).prod < (l.map g).prod) : ∃ i ∈ l, f i < g i := by
  contrapose! h
  exact prod_le_prod' h

@[to_additive exists_le_of_sum_le]
/-
**List.exists_le_of_prod_le'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：exists_le_of_prod_le' [LinearOrder M] [MulLeftStrictMono M] [MulLeftMono M
] [MulRightStrictMono M] [MulRightMono M] {l : List ι} (hl : l != []) (f g : ι -
> M) (h : (l.map f).prod <= (l.map g).prod) : exists x in l, f x <= g x
参数：hl : l != []；f g : ι -> M；h : (l.map f).prod <= (l.map g).prod。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `List.prod_lt_prod_of_ne_nil`：prod_lt_prod_of_ne_nil [Preorder M] [MulLef
tStrictMono M] [MulLeftMono M] [MulRightStrictMono M] [MulRightMono M] {l : List
 ι} (hl : l != []…
-/
lemma exists_le_of_prod_le' [LinearOrder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).prod ≤ (l.map g).prod) : ∃ x ∈ l, f x ≤ g x := by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h

@[to_additive sum_nonneg]
/-
**List.one_le_prod_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：one_le_prod_of_one_le [Preorder M] [MulLeftMono M] {l : List M} (hl₁ : for
all x in l, (1 : M) <= x) : 1 <= l.prod
参数：hl₁ : forall x in l, (1 : M) <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `one_le_mul`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder α
] [MulLeftMono α] {a b : α}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
lemma one_le_prod_of_one_le [Preorder M] [MulLeftMono M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.prod := by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [prod_cons]
    exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive]
/-
**List.max_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：max_prod_le (l : List α) (f g : α -> M) [LinearOrder M] [MulLeftMono M] [M
ulRightMono M] : max (l.map f).prod (l.map g).prod <= (l.map fun i => max (f i) 
(g i)).prod
参数：l : List α；f g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用引理 `List.prod_le_prod'`：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeft
Mono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).
prod <= …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
lemma max_prod_le (l : List α) (f g : α → M) [LinearOrder M]
    [MulLeftMono M] [MulRightMono M] :
    max (l.map f).prod (l.map g).prod ≤ (l.map fun i ↦ max (f i) (g i)).prod := by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

@[to_additive]
/-
**List.prod_min_le** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_min_le [LinearOrder M] [MulLeftMono M] [MulRightMono M] (l : List α) 
(f g : α -> M) : (l.map fun i => min (f i) (g i)).prod <= min (l.map f).prod (l.
map g).prod
参数：l : List α；f g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
· 使用引理 `List.prod_le_prod'`：prod_le_prod' [Preorder M] [MulRightMono M] [MulLeft
Mono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) : (l.map f).
prod <= …
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
lemma prod_min_le [LinearOrder M] [MulLeftMono M]
    [MulRightMono M] (l : List α) (f g : α → M) :
    (l.map fun i ↦ min (f i) (g i)).prod ≤ min (l.map f).prod (l.map g).prod := by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

variable [Preorder M] [CanonicallyOrderedMul M]
/-
**List.monotone_prod_take** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [CanonicallyOrder
edMul M] (L : List M),   Monotone fun i => (List.take i L).prod
参数：L : List M；List.take i L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_take_succ`：prod_take_succ (L : List M) (i : Nat) (p : i < L.le
ngth) : (L.take (i + 1)).prod = (L.take i).prod * L[i]
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
@[to_additive] lemma monotone_prod_take (L : List M) : Monotone fun i ↦ (L.take i).prod := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases lt_or_ge n L.length with h | h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_of_length_le h, take_of_length_le (le_trans h (Nat.le_succ _))]

/-- See also `List.single_le_prod`. -/
@[to_additive /-- See also `List.single_le_sum`. -/]
/-
**List.le_prod_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_prod_of_mem {xs : List M} {x : M} (h₁ : x in xs) : x <= xs.prod
参数：h₁ : x in xs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_mul_left`：∀ {α : Type u} [inst : Mul α] [inst_1 : Preorder α] [Canoni
callyOrderedMul α] {a b c : α}, a ≤ c → a ≤ b * c

--- 原说明 ---
See also `List.single_le_prod`.
-/
theorem le_prod_of_mem {xs : List M} {x : M} (h₁ : x ∈ xs) : x ≤ xs.prod := by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

end Monoid

section
variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
/-
**List.le_prod_of_submultiplicative_on_pred** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：le_prod_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop) (h_one :
 f 1 <= 1) (hp_one : p 1) (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * 
f b) (hp_mul : forall a b, p a -> p b -> p (a * b)) (l : List α) (hpl : forall a
, a in l -> p a) : f l.prod <= (l.map f).prod
参数：f : α -> β；p : α -> Prop；h_one : f 1 <= 1；hp_one : p 1；h_mul : forall a b, p 
a -> p b -> f (a * b) <= f a * f b；hp_mul : forall a b, p a -> p b -> p (a * b)；
l : List α；hpl : forall a, a in l -> p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用引理 `List.prod_induction`：prod_induction (p : M -> Prop) (hom : forall a b, p
 a -> p b -> p (a * b)) (unit : p 1) (base : forall x in l, p x) : p l.prod
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 ≤ 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (l : List α) (hpl : ∀ a, a ∈ l → p a) : f l.prod ≤ (l.map f).prod := by
  induction l with
  | nil => simp [h_one]
  | cons a s ih =>
    have hpla : ∀ x, x ∈ s → p x := fun x hx => hpl x (mem_cons_of_mem _ hx)
    have hp_prod : p s.prod := prod_induction p hp_mul hp_one hpla
    grw [prod_cons, map_cons, prod_cons, h_mul a s.prod (hpl _ mem_cons_self) hp_prod, ih hpla]

@[to_additive le_sum_of_subadditive]
/-
**List.le_prod_of_submultiplicative** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：le_prod_of_submultiplicative (f : α -> β) (h_one : f 1 <= 1) (h_mul : fora
ll a b, f (a * b) <= f a * f b) (l : List α) : f l.prod <= (l.map f).prod
参数：f : α -> β；h_one : f 1 <= 1；h_mul : forall a b, f (a * b) <= f a * f b；l : Li
st α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.le_prod_of_submultiplicative_on_pred`：le_prod_of_submultiplicative_
on_pred (f : α -> β) (p : α -> Prop) (h_one : f 1 <= 1) (hp_one : p 1) (h_mul : 
forall a b, p a -> p b -> f (a …
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma le_prod_of_submultiplicative (f : α → β) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (l : List α) : f l.prod ≤ (l.map f).prod :=
  le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) l (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/-
**List.le_prod_nonempty_of_submultiplicative_on_pred** 是 Mathlib 中的一个引理，位于命名空间 `
List`。
形式化陈述：le_prod_nonempty_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop)
 (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b
, p a -> p b -> p (a * b)) (l : List α) (hl_nonempty : l != []) (hl : forall a, 
a in l -> p a) : f l.prod <= (l.map f).prod
参数：f : α -> β；p : α -> Prop；h_mul : forall a b, p a -> p b -> f (a * b) <= f a *
 f b；hp_mul : forall a b, p a -> p b -> p (a * b)；l : List α；hl_nonempty : l != 
[]；hl : forall a, a in l -> p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用引理 `List.prod_induction_nonempty`：prod_induction_nonempty (p : M -> Prop) (h
om : forall a b, p a -> p b -> p (a * b)) (hl : l != []) (base : forall x in l, 
p x) : p l.prod
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (l : List α) (hl_nonempty : l ≠ []) (hl : ∀ a, a ∈ l → p a) : f l.prod ≤ (l.map f).prod := by
  induction l with
  | nil => simp at hl_nonempty
  | cons a l ih =>
    rw [prod_cons, map_cons, prod_cons]
    by_cases hl_empty : l = []
    · simp [hl_empty]
    have hla_restrict : ∀ x, x ∈ l → p x := fun x hx => hl x (mem_cons_of_mem _ hx)
    have hp_sup : p l.prod := prod_induction_nonempty p hp_mul hl_empty hla_restrict
    have hp_a : p a := hl a mem_cons_self
    grw [h_mul a _ hp_a hp_sup, ← ih hl_empty hla_restrict]

@[to_additive le_sum_nonempty_of_subadditive]
/-
**List.le_prod_nonempty_of_submultiplicative** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：le_prod_nonempty_of_submultiplicative (f : α -> β) (h_mul : forall a b, f 
(a * b) <= f a * f b) (l : List α) (hs_nonempty : l != ∅) : f l.prod <= (l.map f
).prod
参数：f : α -> β；h_mul : forall a b, f (a * b) <= f a * f b；l : List α；hs_nonempty 
: l != ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.le_prod_nonempty_of_submultiplicative_on_pred`：le_prod_nonempty_of_
submultiplicative_on_pred (f : α -> β) (p : α -> Prop) (h_mul : forall a b, p a 
-> p b -> f (a * b) <= f a * f b) (hp_mu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma le_prod_nonempty_of_submultiplicative (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (l : List α) (hs_nonempty : l ≠ ∅) : f l.prod ≤ (l.map f).prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) l
    hs_nonempty (by simp)

end

-- TODO: develop theory of tropical rings
/-
**List.sum_le_foldr_max** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sum_le_foldr_max [AddZeroClass M] [Zero N] [LinearOrder N] (f : M -> N) (h
0 : f 0 <= 0) (hadd : forall x y, f (x + y) <= max (f x) (f y)) (l : List M) : f
 l.sum <= (l.map f).foldr max 0
参数：f : M -> N；h0 : f 0 <= 0；hadd : forall x y, f (x + y) <= max (f x) (f y)；l : 
List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma sum_le_foldr_max [AddZeroClass M] [Zero N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.sum ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simpa using h0
  | cons hd tl IH =>
    simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
    exact (hadd _ _).trans (max_le_max le_rfl IH)

@[to_additive sum_pos]
/-
**List.one_lt_prod_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_3} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMon
oid M] (l : List M),   (∀ x ∈ l, 1 < x) → l ≠ [] → 1 < l.prod
参数：l : List M；∀ x ∈ l, 1 < x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_prod_of_one_lt [CommMonoid M] [Preorder M] [IsOrderedMonoid M] :
    ∀ l : List M, (∀ x ∈ l, (1 : M) < x) → l ≠ [] → 1 < l.prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, _ => by
    simp only [forall_eq_or_imp, List.mem_cons] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt _ (l.cons_ne_nil b))
    grind

/-- See also `List.le_prod_of_mem`. -/
@[to_additive /-- See also `List.le_sum_of_mem`. -/]
/-
**List.single_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：single_le_prod [CommMonoid M] [Preorder M] [IsOrderedMonoid M] {l : List M
} (hl₁ : forall x in l, (1 : M) <= x) : forall x in l, x <= l.prod
参数：hl₁ : forall x in l, (1 : M) <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `List.one_le_prod_of_one_le`：one_le_prod_of_one_le [Preorder M] [MulLeftM
ono M] {l : List M} (hl₁ : forall x in l, (1 : M) <= x) : 1 <= l.prod
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_mul_of_one_le_of_le`：le_mul_of_one_le_of_le [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b <= c) : b <= a * c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
See also `List.le_prod_of_mem`.
-/
lemma single_le_prod [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
/-
**List.all_one_of_le_one_le_of_prod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：all_one_of_le_one_le_of_prod_eq_one [CommMonoid M] [PartialOrder M] [IsOrd
eredMonoid M] {l : List M} (hl₁ : forall x in l, (1 : M) <= x) (hl₂ : l.prod = 1
) {x : M} (hx : x in l) : x = 1
参数：hl₁ : forall x in l, (1 : M) <= x；hl₂ : l.prod = 1；hx : x in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `List.single_le_prod`：single_le_prod [CommMonoid M] [Preorder M] [IsOrder
edMonoid M] {l : List M} (hl₁ : forall x in l, (1 : M) <= x) : forall x in l, x 
<= l.prod
-/
lemma all_one_of_le_one_le_of_prod_eq_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)
/-
**List.prod_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_3} [inst : CommMonoid M] [inst_1 : PartialOrder M] [IsOrdere
dMonoid M] [CanonicallyOrderedMul M]   {l : List M}, l.prod = 1 ↔ ∀ x ∈ l, x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.all_one_of_le_one_le_of_prod_eq_one`：all_one_of_le_one_le_of_prod_e
q_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] {l : List M} (hl₁ : fo
rall x in l, (1 : M) <= x) (hl…
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_replicate_iff`：∀ {α : Type u_1} {a : α} {n : ℕ} {l : List α}, l 
= List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
@[to_additive] lemma prod_eq_one_iff [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
     [CanonicallyOrderedMul M] {l : List M} : l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le, fun h => by
    rw [List.eq_replicate_iff.2 ⟨_, h⟩, prod_replicate, one_pow]
    · exact (length l)
    · rfl⟩

section ProdSum

variable {α β : Type*} [Monoid α] [AddMonoid β] [Preorder β] [AddLeftMono β]
  (l : List α) (f : α → β)

/-
**List.apply_prod_le_sum_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a *
 b) <= f a + f b) : f l.prod <= (l.map f).sum
参数：h_one : f 1 <= 0；h_mul : forall (a b : α), f (a * b) <= f a + f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem apply_prod_le_sum_map (h_one : f 1 ≤ 0) (h_mul : ∀ (a b : α), f (a * b) ≤ f a + f b) :
    f l.prod ≤ (l.map f).sum := by
  induction l with
  | nil => simp [h_one]
  | cons hd tl IH => grw [prod_cons, h_mul, IH]; simp
/-
**List.sum_map_le_apply_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_map_le_apply_prod (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + 
f b <= f (a * b)) : (l.map f).sum <= f l.prod
参数：h_one : 0 <= f 1；h_mul : forall (a b : α), f a + f b <= f (a * b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_
mul : forall (a b : α), f (a * b) <= f a + f b) : f l.prod <= (l.map f).sum
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
-/
theorem sum_map_le_apply_prod (h_one : 0 ≤ f 1) (h_mul : ∀ (a b : α), f a + f b ≤ f (a * b)) :
    (l.map f).sum ≤ f l.prod :=
  apply_prod_le_sum_map (β := βᵒᵈ) l f h_one h_mul

end ProdSum

end List

