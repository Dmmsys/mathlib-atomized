/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Multiset.Fold

/-!
# Big operators on a multiset in ordered groups

This file contains the results concerning the interaction of multiset big operators with ordered
groups.
-/

public section

assert_not_exists MonoidWithZero

variable {ι α β : Type*}

namespace Multiset
section OrderedCommMonoid
variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
/-
**Multiset.one_le_prod_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：one_le_prod_of_one_le [MulLeftMono α] : (forall x in s, (1 : α) <= x) -> 1
 <= s.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.one_le_prod_of_one_le`：one_le_prod_of_one_le [Preorder M] [MulLeftM
ono M] {l : List M} (hl₁ : forall x in l, (1 : M) <= x) : 1 <= l.prod
-/
lemma one_le_prod_of_one_le [MulLeftMono α] : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]
/-
**Multiset.single_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：single_le_prod [IsOrderedMonoid α] : (forall x in s, (1 : α) <= x) -> fora
ll x in s, x <= s.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.single_le_prod`：single_le_prod [CommMonoid M] [Preorder M] [IsOrder
edMonoid M] {l : List M} (hl₁ : forall x in l, (1 : M) <= x) : forall x in l, x 
<= l.prod
-/
lemma single_le_prod [IsOrderedMonoid α] : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]
/-
**Multiset.prod_le_pow_card** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_le_pow_card [MulLeftMono α] (s : Multiset α) (n : α) (h : forall x in
 s, x <= n) : s.prod <= n ^ card s
参数：s : Multiset α；n : α；h : forall x in s, x <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.prod_le_pow_card`：prod_le_pow_card [Preorder M] [MulRightMono M] [M
ulLeftMono M] (l : List M) (n : M) (h : forall x in l, x <= n) : l.prod <= n ^ l
.length
-/
lemma prod_le_pow_card [MulLeftMono α] (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) :
    s.prod ≤ n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
/-
**Multiset.all_one_of_le_one_le_of_prod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Multis
et`。
形式化陈述：all_one_of_le_one_le_of_prod_eq_one {α : Type*} [CommMonoid α] [PartialOrd
er α] [IsOrderedMonoid α] {s : Multiset α} : (forall x in s, (1 : α) <= x) -> s.
prod = 1 -> forall x in s, x = (1 : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `List.all_one_of_le_one_le_of_prod_eq_one`：all_one_of_le_one_le_of_prod_e
q_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] {l : List M} (hl₁ : fo
rall x in l, (1 : M) <= x) (hl…
-/
lemma all_one_of_le_one_le_of_prod_eq_one {α : Type*} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] {s : Multiset α} :
    (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]
/-
**Multiset.prod_le_prod_of_rel_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_le_prod_of_rel_le [MulLeftMono α] (h : s.Rel (· <= ·) t) : s.prod <= 
t.prod
参数：h : s.Rel (· <= ·) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
lemma prod_le_prod_of_rel_le [MulLeftMono α] (h : s.Rel (· ≤ ·) t) : s.prod ≤ t.prod := by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]
/-
**Multiset.prod_map_le_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_le_prod_map [MulLeftMono α] {s : Multiset ι} (f : ι -> α) (g : ι 
-> α) (h : forall i, i in s -> f i <= g i) : (s.map f).prod <= (s.map g).prod
参数：f : ι -> α；g : ι -> α；h : forall i, i in s -> f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_le_prod_of_rel_le`：prod_le_prod_of_rel_le [MulLeftMono α] 
(h : s.Rel (· <= ·) t) : s.prod <= t.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_map`：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ}
 {g : β -> δ} : Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
· 使用定理 `Multiset.rel_refl_of_refl_on`：rel_refl_of_refl_on {m : Multiset α} {r : 
α -> α -> Prop} : (forall x in m, r x x) -> Rel r m m
-/
lemma prod_map_le_prod_map [MulLeftMono α] {s : Multiset ι} (f : ι → α) (g : ι → α)
    (h : ∀ i, i ∈ s → f i ≤ g i) : (s.map f).prod ≤ (s.map g).prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h

@[to_additive]
/-
**Multiset.prod_map_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_le_prod [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> f x
 <= x) : (s.map f).prod <= s.prod
参数：f : α -> α；h : forall x, x in s -> f x <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_le_prod_of_rel_le`：prod_le_prod_of_rel_le [MulLeftMono α] 
(h : s.Rel (· <= ·) t) : s.prod <= t.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_map_left`：rel_map_left {s : Multiset γ} {f : γ -> α} : fora
ll {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t
· 使用定理 `Multiset.rel_refl_of_refl_on`：rel_refl_of_refl_on {m : Multiset α} {r : 
α -> α -> Prop} : (forall x in m, r x x) -> Rel r m m
-/
lemma prod_map_le_prod [MulLeftMono α] (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) :
    (s.map f).prod ≤ s.prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h

@[to_additive]
/-
**Multiset.prod_le_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_le_prod_map [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> x <
= f x) : s.prod <= (s.map f).prod
参数：f : α -> α；h : forall x, x in s -> x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_map_le_prod`：prod_map_le_prod [MulLeftMono α] (f : α -> α)
 (h : forall x, x in s -> f x <= x) : (s.map f).prod <= s.prod
-/
lemma prod_le_prod_map [MulLeftMono α] (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) :
    s.prod ≤ (s.map f).prod :=
  prod_map_le_prod (α := αᵒᵈ) f h

@[to_additive card_nsmul_le_sum]
/-
**Multiset.pow_card_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：pow_card_le_prod [MulLeftMono α] (h : forall x in s, a <= x) : a ^ card s 
<= s.prod
参数：h : forall x in s, a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.map_const`：map_const (s : Multiset α) (b : β) : map (const α b)
 s = replicate (card s) b
· 使用引理 `Multiset.prod_map_le_prod`：prod_map_le_prod [MulLeftMono α] (f : α -> α)
 (h : forall x, x in s -> f x <= x) : (s.map f).prod <= s.prod
-/
lemma pow_card_le_prod [MulLeftMono α] (h : ∀ x ∈ s, a ≤ x) : a ^ card s ≤ s.prod := by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact prod_map_le_prod _ h

end OrderedCommMonoid

section
variable [CommMonoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
/-
**Multiset.le_prod_of_submultiplicative_on_pred** 是 Mathlib 中的一个引理，位于命名空间 `Multi
set`。
形式化陈述：le_prod_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop) (h_one :
 f 1 <= 1) (hp_one : p 1) (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * 
f b) (hp_mul : forall a b, p a -> p b -> p (a * b)) (s : Multiset α) (hps : fora
ll a, a in s -> p a) : f s.prod <= (s.map f).prod
参数：f : α -> β；p : α -> Prop；h_one : f 1 <= 1；hp_one : p 1；h_mul : forall a b, p 
a -> p b -> f (a * b) <= f a * f b；hp_mul : forall a b, p a -> p b -> p (a * b)；
s : Multiset α；hps : forall a, a in s -> p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.le_prod_of_submultiplicative_on_pred`：le_prod_of_submultiplicative_
on_pred (f : α -> β) (p : α -> Prop) (h_one : f 1 <= 1) (hp_one : p 1) (h_mul : 
forall a b, p a -> p b -> f (a …
-/
lemma le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 ≤ 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative_on_pred f p h_one hp_one h_mul hp_mul (by simpa)]

@[to_additive le_sum_of_subadditive]
/-
**Multiset.le_prod_of_submultiplicative** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_prod_of_submultiplicative (f : α -> β) (h_one : f 1 <= 1) (h_mul : fora
ll a b, f (a * b) <= f a * f b) (s : Multiset α) : f s.prod <= (s.map f).prod
参数：f : α -> β；h_one : f 1 <= 1；h_mul : forall a b, f (a * b) <= f a * f b；s : Mu
ltiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.le_prod_of_submultiplicative`：le_prod_of_submultiplicative (f : α -
> β) (h_one : f 1 <= 1) (h_mul : forall a b, f (a * b) <= f a * f b) (l : List α
) : f l.prod <= (l.map …
-/
lemma le_prod_of_submultiplicative (f : α → β) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative f h_one h_mul]

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/-
**Multiset.le_prod_nonempty_of_submultiplicative_on_pred** 是 Mathlib 中的一个引理，位于命名
空间 `Multiset`。
形式化陈述：le_prod_nonempty_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop)
 (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b
, p a -> p b -> p (a * b)) (s : Multiset α) (hs_nonempty : s != ∅) (hs : forall 
a, a in s -> p a) : f s.prod <= (s.map f).prod
参数：f : α -> β；p : α -> Prop；h_mul : forall a b, p a -> p b -> f (a * b) <= f a *
 f b；hp_mul : forall a b, p a -> p b -> p (a * b)；s : Multiset α；hs_nonempty : s
 != ∅；hs : forall a, a in s -> p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.le_prod_nonempty_of_submultiplicative_on_pred`：le_prod_nonempty_of_
submultiplicative_on_pred (f : α -> β) (p : α -> Prop) (h_mul : forall a b, p a 
-> p b -> f (a * b) <= f a * f b) (hp_mu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hs_nonempty : s ≠ ∅) (hs : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l =>
    simp [l.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul
      (by simpa using hs_nonempty) (by simpa)]

@[to_additive le_sum_nonempty_of_subadditive]
/-
**Multiset.le_prod_nonempty_of_submultiplicative** 是 Mathlib 中的一个引理，位于命名空间 `Mult
iset`。
形式化陈述：le_prod_nonempty_of_submultiplicative (f : α -> β) (h_mul : forall a b, f 
(a * b) <= f a * f b) (s : Multiset α) (hs_nonempty : s != ∅) : f s.prod <= (s.m
ap f).prod
参数：f : α -> β；h_mul : forall a b, f (a * b) <= f a * f b；s : Multiset α；hs_nonem
pty : s != ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `List.le_prod_nonempty_of_submultiplicative`：le_prod_nonempty_of_submulti
plicative (f : α -> β) (h_mul : forall a b, f (a * b) <= f a * f b) (l : List α)
 (hs_nonempty : l != ∅) : f l.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma le_prod_nonempty_of_submultiplicative (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (s : Multiset α) (hs_nonempty : s ≠ ∅) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_nonempty_of_submultiplicative f h_mul (by simpa using hs_nonempty)]

end

section OrderedCancelCommMonoid
variable [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] [MulLeftStrictMono α]
  {s : Multiset ι} {f g : ι → α}

@[to_additive sum_lt_sum]
/-
**Multiset.prod_lt_prod'** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_lt_prod' (hle : forall i in s, f i <= g i) (hlt : exists i in s, f i 
< g i) : (s.map f).prod < (s.map g).prod
参数：hle : forall i in s, f i <= g i；hlt : exists i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_lt_prod'`：prod_lt_prod' [Preorder M] [MulLeftStrictMono M] [Mu
lLeftMono M] [MulRightStrictMono M] [MulRightMono M] {l : List ι} (f g : ι -> M)
 (h₁ : f…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
-/
lemma prod_lt_prod' (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

@[to_additive sum_lt_sum_of_nonempty]
/-
**Multiset.prod_lt_prod_of_nonempty'** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_lt_prod_of_nonempty' (hs : s != ∅) (hfg : forall i in s, f i < g i) :
 (s.map f).prod < (s.map g).prod
参数：hs : s != ∅；hfg : forall i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用引理 `Multiset.prod_lt_prod'`：prod_lt_prod' (hle : forall i in s, f i <= g i) 
(hlt : exists i in s, f i < g i) : (s.map f).prod < (s.map g).prod
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma prod_lt_prod_of_nonempty' (hs : s ≠ ∅) (hfg : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

end OrderedCancelCommMonoid

section CanonicallyOrderedMul
variable [CommMonoid α] {m : Multiset α} {a : α}

/-
**Multiset.prod_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] {m : Multiset α} [inst_1 : PartialO
rder α] [CanonicallyOrderedMul α]   [IsOrderedMonoid α], m.prod = 1 ↔ ∀ x ∈ m, x
 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.prod_eq_one_iff`：∀ {M : Type u_3} [inst : CommMonoid M] [inst_1 : P
artialOrder M] [IsOrderedMonoid M] [CanonicallyOrderedMul M]   {l : List M}, l.p
rod = 1 ↔ …
-/
@[to_additive] lemma prod_eq_one_iff [PartialOrder α] [CanonicallyOrderedMul α]
    [IsOrderedMonoid α] : m.prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
  Quotient.inductionOn m fun l ↦ by simpa using List.prod_eq_one_iff
/-
**Multiset.le_prod_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] {m : Multiset α} {a : α},   a ∈ m →
 ∀ [inst_1 : Preorder α] [CanonicallyOrderedMul α], a ≤ m.prod
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `le_mul_right`：∀ {α : Type u} [inst : Mul α] [inst_1 : Preorder α] [Canon
icallyOrderedMul α] {a b c : α}, a ≤ b → a ≤ b * c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma le_prod_of_mem (ha : a ∈ m) [Preorder α] [CanonicallyOrderedMul α] :
    a ≤ m.prod := by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)

end CanonicallyOrderedMul

/-
**Multiset.max_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：max_le_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset
 α) (n : α) (h : forall x in l, x <= n) : l.fold max ⊥ <= n
参数：l : Multiset α；n : α；h : forall x in l, x <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `List.max_le_of_forall_le`：max_le_of_forall_le (l : List α) (a : α) (h : 
forall x in l, x <= a) : l.foldr max ⊥ <= a
-/
lemma max_le_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset α)
    (n : α) (h : ∀ x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n := by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

@[to_additive]
/-
**Multiset.max_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：max_prod_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {s : Multis
et ι} {f g : ι -> α} : max (s.map f).prod (s.map g).prod <= (s.map fun i => max 
(f i) (g i)).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.max_prod_le`：max_prod_le (l : List α) (f g : α -> M) [LinearOrder M
] [MulLeftMono M] [MulRightMono M] : max (l.map f).prod (l.map g).prod <= (l.map
 fun i…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma max_prod_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    max (s.map f).prod (s.map g).prod ≤ (s.map fun i ↦ max (f i) (g i)).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

@[to_additive]
/-
**Multiset.prod_min_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_min_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] {s : Multis
et ι} {f g : ι -> α} : (s.map fun i => min (f i) (g i)).prod <= min (s.map f).pr
od (s.map g).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_min_le`：prod_min_le [LinearOrder M] [MulLeftMono M] [MulRightM
ono M] (l : List α) (f g : α -> M) : (l.map fun i => min (f i) (g i)).prod <= mi
n (l.m…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma prod_min_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι → α} :
    (s.map fun i ↦ min (f i) (g i)).prod ≤ min (s.map f).prod (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le
/-
**Multiset.abs_sum_le_sum_abs** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：abs_sum_le_sum_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
 {s : Multiset α} : |s.sum| <= (s.map abs).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_sum_of_subadditive`：∀ {α : Type u_2} {β : Type u_3} [inst : 
AddCommMonoid α] [inst_1 : AddCommMonoid β] [inst_2 : Preorder β]   [IsOrderedAd
dMonoid β] (f : α → …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
-/
lemma abs_sum_le_sum_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Multiset α} :
    |s.sum| ≤ (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero.le abs_add_le s

section ProdSum

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β] (m : Multiset α) (f : α → β)

/-
**Multiset.apply_prod_le_sum_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a *
 b) <= f a + f b) : f m.prod <= (m.map f).sum
参数：h_one : f 1 <= 0；h_mul : forall (a b : α), f (a * b) <= f a + f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_
mul : forall (a b : α), f (a * b) <= f a + f b) : f l.prod <= (l.map f).sum
-/
lemma apply_prod_le_sum_map (h_one : f 1 ≤ 0) (h_mul : ∀ (a b : α), f (a * b) ≤ f a + f b) :
    f m.prod ≤ (m.map f).sum := by
  induction m using Quotient.inductionOn with
  | h l => simp [l.apply_prod_le_sum_map _ h_one h_mul]
/-
**Multiset.sum_map_le_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sum_map_le_apply_prod (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + 
f b <= f (a * b)) : (m.map f).sum <= f m.prod
参数：h_one : 0 <= f 1；h_mul : forall (a b : α), f a + f b <= f (a * b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0)
 (h_mul : forall (a b : α), f (a * b) <= f a + f b) : f m.prod <= (m.map f).sum
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
-/
lemma sum_map_le_apply_prod (h_one : 0 ≤ f 1) (h_mul : ∀ (a b : α), f a + f b ≤ f (a * b)) :
    (m.map f).sum ≤ f m.prod :=
  m.apply_prod_le_sum_map (β := βᵒᵈ) f h_one h_mul

end ProdSum

end Multiset

