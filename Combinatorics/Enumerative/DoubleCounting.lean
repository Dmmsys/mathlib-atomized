/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Double counting

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : Finset α` and `t : Finset β` by the minimum/maximum of edges over all `a ∈ s` times the
size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartiteBelow`: `s.bipartiteBelow r b` are the elements of `s` below `b` w.r.t. `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartiteAbove`: `t.bipartite_Above r a` are the elements of `t` above `a` w.r.t. `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
bipartite simple graph `G : SimpleGraph V`, see `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.
-/

@[expose] public section

assert_not_exists Field

open Finset Function Relator

variable {R α β : Type*}

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

/-- Elements of `s` which are "below" `b` according to relation `r`. -/
/-
**Finset.bipartiteBelow** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：bipartiteBelow : Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements of `s` which are "below" `b` according to relation `r`.
-/
def bipartiteBelow : Finset α := {a ∈ s | r a b}

/-- Elements of `t` which are "above" `a` according to relation `r`. -/
/-
**Finset.bipartiteAbove** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：bipartiteAbove : Finset β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements of `t` which are "above" `a` according to relation `r`.
-/
def bipartiteAbove : Finset β := {b ∈ t | r a b}
/-
**Finset.bipartiteBelow_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a := rfl
/-
**Finset.bipartiteAbove_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b := rfl

@[simp, norm_cast]
/-
**Finset.coe_bipartiteBelow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_bipartiteBelow : s.bipartiteBelow r b = ({a in s | r a b} : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
-/
theorem coe_bipartiteBelow : s.bipartiteBelow r b = ({a ∈ s | r a b} : Set α) := coe_filter _ _

@[simp, norm_cast]
/-
**Finset.coe_bipartiteAbove** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_bipartiteAbove : t.bipartiteAbove r a = ({b in t | r a b} : Set β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
-/
theorem coe_bipartiteAbove : t.bipartiteAbove r a = ({b ∈ t | r a b} : Set β) := coe_filter _ _

variable {s t a b}

@[simp]
/-
**Finset.mem_bipartiteBelow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_bipartiteBelow {a : α} : a in s.bipartiteBelow r b ↔ a in s ∧ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem mem_bipartiteBelow {a : α} : a ∈ s.bipartiteBelow r b ↔ a ∈ s ∧ r a b := mem_filter

@[simp]
/-
**Finset.mem_bipartiteAbove** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_bipartiteAbove {b : β} : b in t.bipartiteAbove r a ↔ b in t ∧ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem mem_bipartiteAbove {b : β} : b ∈ t.bipartiteAbove r a ↔ b ∈ t ∧ r a b := mem_filter

@[to_additive]
/-
**Finset.prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow** 是 Mathlib 中的一个定理
，位于命名空间 `Finset`。
形式化陈述：prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow [CommMonoid R] (f : α
 -> β -> R) [forall a b, Decidable (r a b)] : ∏ a in s, ∏ b in t.bipartiteAbove 
r a, f a b = ∏ b in t, ∏ a in s.bipartiteBelow r b, f a b
参数：f : α -> β -> R；r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_filter`：prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι
 -> M) : ∏ a in s with p a, f a = ∏ a in s, if p a then f a else 1
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
-/
theorem prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
    [CommMonoid R] (f : α → β → R) [∀ a b, Decidable (r a b)] :
    ∏ a ∈ s, ∏ b ∈ t.bipartiteAbove r a, f a b = ∏ b ∈ t, ∏ a ∈ s.bipartiteBelow r b, f a b := by
  simp_rw [bipartiteAbove, bipartiteBelow, prod_filter]
  exact prod_comm
/-
**Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow** 是 Mathlib 中的一个定理，位
于命名空间 `Finset`。
形式化陈述：sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable 
(r a b)] : (∑ a in s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bipartiteBelow r 
b)
参数：r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow`：∀ {R : Type u_1
} {α : Type u_2} {β : Type u_3} (r : α → β → Prop) {s : Finset α} {t : Finset β}
 [inst : AddCommMonoid R]   (f : α → β → R) […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, #(t.bipartiteAbove r a)) = ∑ b ∈ t, #(s.bipartiteBelow r b) := by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
/-
**Finset.card_nsmul_le_card_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_nsmul_le_card_nsmul [forall a b, Decidable (r a b)] (hm : forall a in
 s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t, #(s.bipartiteBelow r b) <
= n) : #s • m <= #t • n
参数：r a b；hm : forall a in s, m <= #(t.bipartiteAbove r a)；hn : forall b in t, #(
s.bipartiteBelow r b) <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`：sum_card_bipa
rtiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] : (∑ a in 
s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bip…
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of 
edges while the RHS
is an upper bound.
-/
theorem card_nsmul_le_card_nsmul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s • m ≤ #t • n :=
  calc
    _ ≤ ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
/-
**Finset.card_nsmul_le_card_nsmul'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_nsmul_le_card_nsmul' [forall a b, Decidable (r a b)] (hn : forall b i
n t, n <= #(s.bipartiteBelow r b)) (hm : forall a in s, #(t.bipartiteAbove r a) 
<= m) : #t • n <= #s • m
参数：r a b；hn : forall b in t, n <= #(s.bipartiteBelow r b)；hm : forall a in s, #(
t.bipartiteAbove r a) <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_le_card_nsmul`：card_nsmul_le_card_nsmul [forall a b, D
ecidable (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : foral
l b in t, #(s.biparti…

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of 
edges while the RHS
is an upper bound.
-/
theorem card_nsmul_le_card_nsmul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t • n ≤ #s • m :=
  card_nsmul_le_card_nsmul (swap r) hn hm

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] (r : α → β → Prop)
  {s : Finset α} {t : Finset β} (a b) {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
/-
**Finset.card_nsmul_lt_card_nsmul_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：card_nsmul_lt_card_nsmul_of_lt_of_le [forall a b, Decidable (r a b)] (hs :
 s.Nonempty) (hm : forall a in s, m < #(t.bipartiteAbove r a)) (hn : forall b in
 t, #(s.bipartiteBelow r b) <= n) : #s • m < #t • n
参数：r a b；hs : s.Nonempty；hm : forall a in s, m < #(t.bipartiteAbove r a)；hn : fo
rall b in t, #(s.bipartiteBelow r b) <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.sum_lt_sum_of_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → 
M} {s : Finset ι} […
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`：sum_card_bipa
rtiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] : (∑ a in 
s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bip…
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the num
ber of edges while
the RHS is an upper bound.
-/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hm : ∀ a ∈ s, m < #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s • m < #t • n :=
  calc
    _ = ∑ _a ∈ s, m := by rw [sum_const]
    _ < ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
/-
**Finset.card_nsmul_lt_card_nsmul_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：card_nsmul_lt_card_nsmul_of_le_of_lt [forall a b, Decidable (r a b)] (ht :
 t.Nonempty) (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b i
n t, #(s.bipartiteBelow r b) < n) : #s • m < #t • n
参数：r a b；ht : t.Nonempty；hm : forall a in s, m <= #(t.bipartiteAbove r a)；hn : f
orall b in t, #(s.bipartiteBelow r b) < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`：sum_card_bipa
rtiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] : (∑ a in 
s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bip…
· 使用定理 `Finset.sum_lt_sum_of_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → 
M} {s : Finset ι} […
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of 
edges while the RHS
is a strict upper bound.
-/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) < n) : #s • m < #t • n :=
  calc
    _ ≤ ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b ∈ t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
/-
**Finset.card_nsmul_lt_card_nsmul_of_lt_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：card_nsmul_lt_card_nsmul_of_lt_of_le' [forall a b, Decidable (r a b)] (ht 
: t.Nonempty) (hn : forall b in t, n < #(s.bipartiteBelow r b)) (hm : forall a i
n s, #(t.bipartiteAbove r a) <= m) : #t • n < #s • m
参数：r a b；ht : t.Nonempty；hn : forall b in t, n < #(s.bipartiteBelow r b)；hm : fo
rall a in s, #(t.bipartiteAbove r a) <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_lt_card_nsmul_of_lt_of_le`：card_nsmul_lt_card_nsmul_of
_lt_of_le [forall a b, Decidable (r a b)] (hs : s.Nonempty) (hm : forall a in s,
 m < #(t.bipartiteAbove r a)) (hn…

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the num
ber of edges while
the RHS is an upper bound.
-/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le' [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hn : ∀ b ∈ t, n < #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
/-
**Finset.card_nsmul_lt_card_nsmul_of_le_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：card_nsmul_lt_card_nsmul_of_le_of_lt' [forall a b, Decidable (r a b)] (hs 
: s.Nonempty) (hn : forall b in t, n <= #(s.bipartiteBelow r b)) (hm : forall a 
in s, #(t.bipartiteAbove r a) < m) : #t • n < #s • m
参数：r a b；hs : s.Nonempty；hn : forall b in t, n <= #(s.bipartiteBelow r b)；hm : f
orall a in s, #(t.bipartiteAbove r a) < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_lt_card_nsmul_of_le_of_lt`：card_nsmul_lt_card_nsmul_of
_le_of_lt [forall a b, Decidable (r a b)] (ht : t.Nonempty) (hm : forall a in s,
 m <= #(t.bipartiteAbove r a)) (h…

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of 
edges while the RHS
is a strict upper bound.
-/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt' [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) < m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm

end StrictOrderedSemiring

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
/-
**Finset.card_mul_le_card_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_le_card_mul [forall a b, Decidable (r a b)] (hm : forall a in s, 
m <= #(t.bipartiteAbove r a)) (hn : forall b in t, #(s.bipartiteBelow r b) <= n)
 : #s * m <= #t * n
参数：r a b；hm : forall a in s, m <= #(t.bipartiteAbove r a)；hn : forall b in t, #(
s.bipartiteBelow r b) <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_le_card_nsmul`：card_nsmul_le_card_nsmul [forall a b, D
ecidable (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : foral
l b in t, #(s.biparti…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
**Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of 
edges while the RHS
is an upper bound.
-/
theorem card_mul_le_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s * m ≤ #t * n :=
  card_nsmul_le_card_nsmul _ hm hn
/-
**Finset.card_mul_le_card_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_le_card_mul' [forall a b, Decidable (r a b)] (hn : forall b in t,
 n <= #(s.bipartiteBelow r b)) (hm : forall a in s, #(t.bipartiteAbove r a) <= m
) : #t * n <= #s * m
参数：r a b；hn : forall b in t, n <= #(s.bipartiteBelow r b)；hm : forall a in s, #(
t.bipartiteAbove r a) <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_nsmul_le_card_nsmul'`：card_nsmul_le_card_nsmul' [forall a b,
 Decidable (r a b)] (hn : forall b in t, n <= #(s.bipartiteBelow r b)) (hm : for
all a in s, #(t.bipart…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem card_mul_le_card_mul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t * n ≤ #s * m :=
  card_nsmul_le_card_nsmul' _ hn hm
/-
**Finset.card_mul_eq_card_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_eq_card_mul [forall a b, Decidable (r a b)] (hm : forall a in s, 
#(t.bipartiteAbove r a) = m) (hn : forall b in t, #(s.bipartiteBelow r b) = n) :
 #s * m = #t * n
参数：r a b；hm : forall a in s, #(t.bipartiteAbove r a) = m；hn : forall b in t, #(s
.bipartiteBelow r b) = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.card_mul_le_card_mul`：card_mul_le_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t
, #(s.bipartiteBe…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_mul_le_card_mul'`：card_mul_le_card_mul' [forall a b, Decidab
le (r a b)] (hn : forall b in t, n <= #(s.bipartiteBelow r b)) (hm : forall a in
 s, #(t.bipartiteA…
-/
theorem card_mul_eq_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) = m)
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) = n) : #s * m = #t * n :=
  (card_mul_le_card_mul _ (fun a ha ↦ (hm a ha).ge) fun b hb ↦ (hn b hb).le).antisymm <|
    card_mul_le_card_mul' _ (fun a ha ↦ (hn a ha).ge) fun b hb ↦ (hm b hb).le
/-
**Finset.card_le_card_of_forall_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_of_forall_subsingleton (hs : forall a in s, exists b, b in t 
∧ r a b) (ht : forall b in t, ({ a in s | r a b } : Set α).Subsingleton) : #s <=
 #t
参数：hs : forall a in s, exists b, b in t ∧ r a b；ht : forall b in t, ({ a in s | 
r a b } : Set α).Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.card_mul_le_card_mul`：card_mul_le_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t
, #(s.bipartiteBe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_bipartiteAbove`：coe_bipartiteAbove : t.bipartiteAbove r a = (
{b in t | r a b} : Set β)
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem card_le_card_of_forall_subsingleton (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
    rw [← mul_one #s, ← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h ↦ card_pos.2 (by
        rw [← coe_nonempty, coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h ↦ card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))
/-
**Finset.card_le_card_of_forall_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：card_le_card_of_forall_subsingleton' (ht : forall b in t, exists a, a in s
 ∧ r a b) (hs : forall a in s, ({ b in t | r a b } : Set β).Subsingleton) : #t <
= #s
参数：ht : forall b in t, exists a, a in s ∧ r a b；hs : forall a in s, ({ b in t | 
r a b } : Set β).Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_of_forall_subsingleton`：card_le_card_of_forall_subsi
ngleton (hs : forall a in s, exists b, b in t ∧ r a b) (ht : forall b in t, ({ a
 in s | r a b } : Set α).Subsing…
-/
theorem card_le_card_of_forall_subsingleton' (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b)
    (hs : ∀ a ∈ s, ({ b ∈ t | r a b } : Set β).Subsingleton) : #t ≤ #s :=
  card_le_card_of_forall_subsingleton (swap r) ht hs

/-- Given a finite collection of finite subsets $B_1, \ldots, B_k$
and, for every $x \in \bigcup_i B_i$, let $C_x$ be the set of indices
of the $B_i$'s that contain $x$.  Then, $\sum_i |B_i| = \sum_x |C_x|$. -/
/-
**Finset.sum_card_eq_sum_biUnion_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_card_eq_sum_biUnion_card [Fintype α] [DecidableEq α] [DecidableEq β] (
B : α -> Finset β) (s : Finset α) : ∑ j in s, #(B j) = ∑ x in s.biUnion B, #{j |
 j in s ∧ x in B j}
参数：B : α -> Finset β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`：sum_card_bipa
rtiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] : (∑ a in 
s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bip…

--- 原说明 ---
Given a finite collection of finite subsets $B_1, \ldots, B_k$
and, for every $x \in \bigcup_i B_i$, let $C_x$ be the set of indices
of the $B_i$'s that contain $x$.  Then, $\sum_i |B_i| = \sum_x |C_x|$.
-/
lemma sum_card_eq_sum_biUnion_card [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (s : Finset α) :
    ∑ j ∈ s, #(B j) = ∑ x ∈ s.biUnion B, #{j | j ∈ s ∧ x ∈ B j} := by
  convert sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x ∈ B j)
  · grind [bipartiteAbove]
  · grind [bipartiteBelow]

end Bipartite

end Finset

namespace Fintype

variable [Fintype α] [Fintype β] {r : α → β → Prop}

/-
**Fintype.card_le_card_of_leftTotal_unique** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) : 
Fintype.card α <= Fintype.card β
参数：h₁ : LeftTotal r；h₂ : LeftUnique r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_of_forall_subsingleton`：card_le_card_of_forall_subsi
ngleton (hs : forall a in s, exists b, b in t ∧ r a b) (ht : forall b in t, ({ a
 in s | r a b } : Set α).Subsing…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) :
    Fintype.card α ≤ Fintype.card β :=
  card_le_card_of_forall_subsingleton r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ ↦ h₂ ha₁.2 ha₂.2
/-
**Fintype.card_le_card_of_rightTotal_unique** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r)
 : Fintype.card β <= Fintype.card α
参数：h₁ : RightTotal r；h₂ : RightUnique r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_of_forall_subsingleton'`：card_le_card_of_forall_subs
ingleton' (ht : forall b in t, exists a, a in s ∧ r a b) (hs : forall a in s, ({
 b in t | r a b } : Set β).Subsin…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r) :
    Fintype.card β ≤ Fintype.card α :=
  card_le_card_of_forall_subsingleton' r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ ↦ h₂ ha₁.2 ha₂.2

end Fintype

