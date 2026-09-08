/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Multiset.OrderedMonoid
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Big operators on a finset in ordered groups

This file contains the results concerning the interaction of finset big operators with ordered
groups/monoids.
-/

public section

assert_not_exists Ring

open Function

variable {ι α β M N G k R : Type*}

namespace Finset

section OrderedCommMonoid

variable [CommMonoid M] [CommMonoid N] [Preorder N]

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x ∈ s, g x) ≤ ∏ x ∈ s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/-
**Finset.le_prod_nonempty_of_submultiplicative_on_pred** 是 Mathlib 中的一个定理，位于命名空间
 `Finset`。
形式化陈述：le_prod_nonempty_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -
> N) (p : M -> Prop) (h_mul : forall x y, p x -> p y -> f (x * y) <= f x * f y) 
(hp_mul : forall x y, p x -> p y -> p (x * y)) (g : ι -> M) (s : Finset ι) (hs_n
onempty : s.Nonempty) (hs : forall i in s, p (g i)) : f (∏ i in s, g i) <= ∏ i i
n s, f (g i)
参数：f : M -> N；p : M -> Prop；h_mul : forall x y, p x -> p y -> f (x * y) <= f x *
 f y；hp_mul : forall x y, p x -> p y -> p (x * y)；g : ι -> M；s : Finset ι；hs_non
empty : s.Nonempty；hs : forall i in s, p (g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Multiset.le_prod_nonempty_of_submultiplicative_on_pred`：le_prod_nonempty
_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop) (h_mul : forall a b, 
p a -> p b -> f (a * b) <= f a * f b) (hp_mu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.forall_mem_map_iff`：forall_mem_map_iff {f : α -> β} {p : β -> P
rop} {s : Multiset α} : (forall y in s.map f, p y) ↔ forall x in s, p (f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t

--- 原说明 ---
Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` b
e a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let
 `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x ∈ s, g x) ≤ ∏ x ∈ s, f (g x)`.
-/
theorem le_prod_nonempty_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  simp

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let
`f : M → N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let
`g i`, `i ∈ s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
/-
**Finset.le_prod_nonempty_of_submultiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：le_prod_nonempty_of_submultiplicative [IsOrderedMonoid N] (f : M -> N) (h_
mul : forall x y, f (x * y) <= f x * f y) {s : Finset ι} (hs : s.Nonempty) (g : 
ι -> M) : f (∏ i in s, g i) <= ∏ i in s, f (g i)
参数：f : M -> N；h_mul : forall x y, f (x * y) <= f x * f y；hs : s.Nonempty；g : ι -
> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_prod_nonempty_of_submultiplicative_on_pred`：le_prod_nonempty_o
f_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop) (h_
mul : forall x y, p x -> p y -> f (x * y) …
· 使用定理 `trivial`：True

--- 原说明 ---
If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i
`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (
g i)`.
-/
theorem le_prod_nonempty_of_submultiplicative [IsOrderedMonoid N] (f : M → N)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) {s : Finset ι} (hs : s.Nonempty) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ ↦ True) (fun x y _ _ ↦ h_mul x y)
    (fun _ _ _ _ ↦ trivial) g s hs fun _ _ ↦ trivial

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
/-
**Finset.le_prod_of_submultiplicative_on_pred** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：le_prod_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -> N) (p :
 M -> Prop) (h_one : f 1 <= 1) (h_mul : forall x y, p x -> p y -> f (x * y) <= f
 x * f y) (hp_mul : forall x y, p x -> p y -> p (x * y)) (g : ι -> M) {s : Finse
t ι} (hs : forall i in s, p (g i)) : f (∏ i in s, g i) <= ∏ i in s, f (g i)
参数：f : M -> N；p : M -> Prop；h_one : f 1 <= 1；h_mul : forall x y, p x -> p y -> f
 (x * y) <= f x * f y；hp_mul : forall x y, p x -> p y -> p (x * y)；g : ι -> M；hs
 : forall i in s, p (g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.le_prod_nonempty_of_submultiplicative_on_pred`：le_prod_nonempty_o
f_submultiplicative_on_pred [IsOrderedMonoid N] (f : M -> N) (p : M -> Prop) (h_
mul : forall x y, p x -> p y -> f (x * y) …

--- 原说明 ---
Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` b
e a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of e
lements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`.
-/
theorem le_prod_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M → N) (p : M → Prop)
    (h_one : f 1 ≤ 1) (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y)
    (hp_mul : ∀ x y, p x → p y → p (x * y)) (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs

/-- Let `{x | p x}` be a subsemigroup of a commutative additive monoid `M`. Let `f : M → N` be a map
such that `f 0 = 0` and `f` is subadditive on `{x | p x}`, i.e. `p x → p y → f (x + y) ≤ f x + f y`.
Let `g i`, `i ∈ s`, be a finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ x ∈ s, g x) ≤ ∑ x ∈ s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
/-
**Finset.le_prod_of_submultiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_prod_of_submultiplicative [IsOrderedMonoid N] (f : M -> N) (h_one : f 1
 <= 1) (h_mul : forall x y, f (x * y) <= f x * f y) (s : Finset ι) (g : ι -> M) 
: f (∏ i in s, g i) <= ∏ i in s, f (g i)
参数：f : M -> N；h_one : f 1 <= 1；h_mul : forall x y, f (x * y) <= f x * f y；s : Fi
nset ι；g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Multiset.le_prod_of_submultiplicative`：le_prod_of_submultiplicative (f :
 α -> β) (h_one : f 1 <= 1) (h_mul : forall a b, f (a * b) <= f a * f b) (s : Mu
ltiset α) : f s.prod <= (s.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t

--- 原说明 ---
If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 
1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s
, f (g i)`.
-/
theorem le_prod_of_submultiplicative [IsOrderedMonoid N] (f : M → N) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) (by simp)

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y`, `f 0 = 0`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variable {f g : ι → N} {s t : Finset ι}

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i`. -/
@[to_additive (attr := gcongr) sum_le_sum]
/-
**Finset.prod_le_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod' [MulLeftMono N] (h : forall i in s, f i <= g i) : ∏ i in s, 
f i <= ∏ i in s, g i
参数：h : forall i in s, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_map_le_prod_map`：prod_map_le_prod_map [MulLeftMono α] {s :
 Multiset ι} (f : ι -> α) (g : ι -> α) (h : forall i, i in s -> f i <= g i) : (s
.map f).prod <= (s.…

--- 原说明 ---
In an ordered commutative monoid, if each factor `f i` of one finite product is 
less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i`.
-/
theorem prod_le_prod' [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
  Multiset.prod_map_le_prod_map f g h

attribute [bound] sum_le_sum

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. -/
add_decl_doc sum_le_sum

/-- A finite product of monotone functions is monotone. -/
@[to_additive finsetSum /-- A finite sum of monotone functions is monotone. -/]
/-
**Finset._root_.Monotone.finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of monotone functions is monotone.
-/
theorem _root_.Monotone.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ]
    {f : ι → γ → N} (hf : ∀ i ∈ s, Monotone (f i)) :
    Monotone fun x ↦ ∏ i ∈ s, f i x :=
  fun _ _ hab ↦ Finset.prod_le_prod' fun i hi ↦ hf i hi hab

/-- A finite product of functions monotone on `u` is monotone on `u`. -/
@[to_additive finsetSum /-- A finite sum of functions monotone on `u` is monotone on `u`. -/]
/-
**Finset._root_.MonotoneOn.finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of functions monotone on `u` is monotone on `u`.
-/
theorem _root_.MonotoneOn.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
    {f : ι → γ → N} (hf : ∀ i ∈ s, MonotoneOn (f i) u) :
    MonotoneOn (fun x ↦ ∏ i ∈ s, f i x) u :=
  fun _ ha _ hb hab ↦ Finset.prod_le_prod' fun i hi ↦ hf i hi ha hb hab

/-- A finite product of antitone functions is antitone. -/
@[to_additive finsetSum /-- A finite sum of antitone functions is antitone. -/]
/-
**Finset._root_.Antitone.finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of antitone functions is antitone.
-/
theorem _root_.Antitone.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ]
    {f : ι → γ → N} (hf : ∀ i ∈ s, Antitone (f i)) :
    Antitone fun x ↦ ∏ i ∈ s, f i x :=
  fun _ _ hab ↦ Finset.prod_le_prod' fun i hi ↦ hf i hi hab

/-- A finite product of functions antitone on `u` is antitone on `u`. -/
@[to_additive finsetSum /-- A finite sum of functions antitone on `u` is antitone on `u`. -/]
/-
**Finset._root_.AntitoneOn.finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of functions antitone on `u` is antitone on `u`.
-/
theorem _root_.AntitoneOn.finsetProd' [MulLeftMono N] {γ : Type*} [Preorder γ] {u : Set γ}
    {f : ι → γ → N} (hf : ∀ i ∈ s, AntitoneOn (f i) u) :
    AntitoneOn (fun x ↦ ∏ i ∈ s, f i x) u :=
  fun _ ha _ hb hab ↦ Finset.prod_le_prod' fun i hi ↦ hf i hi ha hb hab

@[to_additive sum_nonneg]
/-
**Finset.one_le_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 <= f i) : 1 <= ∏ i in s
, f i
参数：h : forall i in s, 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
-/
theorem one_le_prod' [MulLeftMono N] (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)

@[to_additive Finset.sum_nonneg']
/-
**Finset.one_le_prod''** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_le_prod'' [MulLeftMono N] (h : forall i : ι, 1 <= f i) : 1 <= ∏ i in s
, f i
参数：h : forall i : ι, 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
-/
theorem one_le_prod'' [MulLeftMono N] (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.one_le_prod' fun i _ ↦ h i

@[to_additive sum_nonpos]
/-
**Finset.prod_le_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_one' [MulLeftMono N] (h : forall i in s, f i <= 1) : ∏ i in s, f i
 <= 1
参数：h : forall i in s, f i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem prod_le_one' [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])

@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
/-
**Finset.prod_le_prod_of_subset_of_one_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s subseteq t) (hf :
 forall i in t, i ∉ s -> 1 <= f i) : ∏ i in s, f i <= ∏ i in t, f i
参数：h : s subseteq t；hf : forall i in t, i ∉ s -> 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
-/
theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]

@[to_additive]
/-
**Finset.prod_le_prod_of_subset_of_le_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_subset_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoi
d N] [Preorder N] {f : ι -> N} {s t : Finset ι} [MulLeftMono N] (h : s subseteq 
t) (hf : forall i in t, i ∉ s -> f i <= 1) : ∏ i in t, f i <= ∏ i in s, f i
参数：h : s subseteq t；hf : forall i in t, i ∉ s -> f i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
-/
theorem prod_le_prod_of_subset_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} {s t : Finset ι} [MulLeftMono N] (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf

@[to_additive sum_mono_set_of_nonneg]
/-
**Finset.prod_mono_set_of_one_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mono_set_of_one_le' [MulLeftMono N] (hf : forall x, 1 <= f x) : Monot
one fun s => ∏ x in s, f x
参数：hf : forall x, 1 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
-/
theorem prod_mono_set_of_one_le' [MulLeftMono N] (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x

@[to_additive]
/-
**Finset.prod_anti_set_of_le_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_anti_set_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Pre
order N] {f : ι -> N} [MulLeftMono N] (hf : forall (x : ι), f x <= 1) : Antitone
 fun (s : Finset ι) => ∏ x in s, f x
参数：hf : forall (x : ι), f x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_le_one'`：prod_le_prod_of_subset_of_le_o
ne' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N] {f : ι -> N} {s t 
: Finset ι} [MulLeftMono N] (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_anti_set_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} [MulLeftMono N] (hf : ∀ (x : ι), f x ≤ 1) :
    Antitone fun (s : Finset ι) => ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_le_one' hst (by simp [hf])

@[to_additive sum_le_univ_sum_of_nonneg]
/-
**Finset.prod_le_univ_prod_of_one_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_univ_prod_of_one_le' [MulLeftMono N] [Fintype ι] {s : Finset ι} (w
 : forall x, 1 <= f x) : ∏ x in s, f x <= ∏ x, f x
参数：w : forall x, 1 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem prod_le_univ_prod_of_one_le' [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a

@[to_additive sum_eq_zero_iff_of_nonneg]
/-
**Finset.prod_eq_one_iff_of_one_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_one_iff_of_one_le' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [P
artialOrder N] {f : ι -> N} {s : Finset ι} [MulLeftMono N] : (forall i in s, 1 <
= f i) -> ((∏ i in s, f i) = 1 ↔ forall i in s, f i = 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `mul_eq_one_iff_of_one_le`：mul_eq_one_iff_of_one_le [MulLeftMono α] [MulR
ightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_eq_one_iff_of_one_le' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.notMem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff_of_one_le (H _ <| mem_insert_self _ _) (one_le_prod' this),
      forall_mem_insert, ih this]

@[to_additive sum_pos_iff_of_nonneg]
/-
**Finset.one_lt_prod_iff_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_lt_prod_iff_of_one_le {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Pa
rtialOrder N] {f : ι -> N} {s : Finset ι} [MulLeftMono N] (hf : forall x in s, 1
 <= f x) : 1 < ∏ x in s, f x ↔ exists x in s, 1 < f x
参数：hf : forall x in s, 1 <= f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finset.prod_eq_one_iff_of_one_le'`：prod_eq_one_iff_of_one_le' {ι : Type 
u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} 
[MulLeftMono N] : (fora…
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_lt_prod_iff_of_one_le {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, 1 ≤ f x) :
    1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x := by
  have hsum : 1 ≤ ∏ x ∈ s, f x := one_le_prod' hf
  rw [hsum.lt_iff_ne', Ne, prod_eq_one_iff_of_one_le' hf, not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

@[to_additive sum_eq_zero_iff_of_nonpos]
/-
**Finset.prod_eq_one_iff_of_le_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_one_iff_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [P
artialOrder N] {f : ι -> N} {s : Finset ι} [MulLeftMono N] : (forall i in s, f i
 <= 1) -> ((∏ i in s, f i) = 1 ↔ forall i in s, f i = 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_one_iff_of_one_le'`：prod_eq_one_iff_of_one_le' {ι : Type 
u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} 
[MulLeftMono N] : (fora…
-/
theorem prod_eq_one_iff_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

@[to_additive]
/-
**Finset.prod_lt_one_iff_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_lt_one_iff_of_le_one {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Pa
rtialOrder N] {f : ι -> N} {s : Finset ι} [MulLeftMono N] (hf : forall x in s, f
 x <= 1) : ∏ x in s, f x < 1 ↔ exists x in s, f x < 1
参数：hf : forall x in s, f x <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.one_lt_prod_iff_of_one_le`：one_lt_prod_iff_of_one_le {ι : Type u_
1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} [M
ulLeftMono N] (hf : fo…
-/
lemma prod_lt_one_iff_of_le_one {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, f x ≤ 1) :
    ∏ x ∈ s, f x < 1 ↔ ∃ x ∈ s, f x < 1 :=
  one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

@[to_additive single_le_sum]
/-
**Finset.single_le_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：single_le_prod' [MulLeftMono N] (hf : forall i in s, 1 <= f i) {a} (h : a 
in s) : f a <= ∏ x in s, f x
参数：hf : forall i in s, 1 <= f i；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
-/
theorem single_le_prod' [MulLeftMono N] (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) :
    f a ≤ ∏ x ∈ s, f x :=
  calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi

@[to_additive]
/-
**Finset.mul_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_le_prod [MulLeftMono N] {i j : ι} (hf : forall i in s, 1 <= f i) (hi :
 i in s) (hj : j in s) (hne : i != j) : f i * f j <= ∏ k in s, f k
参数：hf : forall i in s, 1 <= f i；hi : i in s；hj : j in s；hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma mul_le_prod [MulLeftMono N] {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s)
    (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k :=
  calc
    f i * f j = ∏ k ∈ .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k ∈ s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]
/-
**Finset.prod_le_pow_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : 
forall x in s, f x <= n) : s.prod f <= n ^ #s
参数：s : Finset ι；f : ι -> N；n : N；h : forall x in s, f x <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Multiset.prod_le_pow_card`：prod_le_pow_card [MulLeftMono α] (s : Multise
t α) (n : α) (h : forall x in s, x <= n) : s.prod <= n ^ card s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

@[to_additive card_nsmul_le_sum]
/-
**Finset.pow_card_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pow_card_le_prod [MulLeftMono N] (s : Finset ι) (f : ι -> N) (n : N) (h : 
forall x in s, n <= f x) : n ^ #s <= s.prod f
参数：s : Finset ι；f : ι -> N；n : N；h : forall x in s, n <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_pow_card`：prod_le_pow_card [MulLeftMono N] (s : Finset ι)
 (f : ι -> N) (n : N) (h : forall x in s, f x <= n) : s.prod f <= n ^ #s
-/
theorem pow_card_le_prod [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ #s ≤ s.prod f := Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h
/-
**Finset.card_biUnion_le_card_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι -> Finset β
) (n : Nat) (h : forall a in s, #(f a) <= n) : #(s.biUnion f) <= #s * n
参数：s : Finset ι；f : ι -> Finset β；n : Nat；h : forall a in s, #(f a) <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, #(f a) ≤ n) : #(s.biUnion f) ≤ #s * n :=
  card_biUnion_le.trans <| sum_le_card_nsmul _ _ _ h

variable {ι' : Type*} [DecidableEq ι']

@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
/-
**Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'** 是 Mathlib 中的一个定理，位于命名空间 
`Finset`。
形式化陈述：prod_fiberwise_le_prod_of_one_le_prod_fiber' [MulLeftMono N] {t : Finset ι
'} {g : ι -> ι'} {f : ι -> N} (h : forall y ∉ t, (1 : N) <= ∏ x in s with g x = 
y, f x) : (∏ y in t, ∏ x in s with g x = y, f x) <= ∏ x in s, f x
参数：h : forall y ∉ t, (1 : N) <= ∏ x in s with g x = y, f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用引理 `Finset.prod_fiberwise_of_maps_to`：prod_fiberwise_of_maps_to {g : ι -> κ}
 (h : forall i in s, g i in t) (f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f
 i = ∏ i in s, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' [MulLeftMono N] {t : Finset ι'} {g : ι → ι'}
    {f : ι → N} (h : ∀ y ∉ t, (1 : N) ≤ ∏ x ∈ s with g x = y, f x) :
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤ ∏ x ∈ s, f x :=
  calc
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤
        ∏ y ∈ t ∪ s.image g, ∏ x ∈ s with g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ ↦ h y
    _ = ∏ x ∈ s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _

@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
/-
**Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'** 是 Mathlib 中的一个定理，位于命名空间 
`Finset`。
形式化陈述：prod_le_prod_fiberwise_of_prod_fiber_le_one' [MulLeftMono N] {t : Finset ι
'} {g : ι -> ι'} {f : ι -> N} (h : forall y ∉ t, ∏ x in s with g x = y, f x <= 1
) : ∏ x in s, f x <= ∏ y in t, ∏ x in s with g x = y, f x
参数：h : forall y ∉ t, ∏ x in s with g x = y, f x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'`：prod_fiberwise_le_p
rod_of_one_le_prod_fiber' [MulLeftMono N] {t : Finset ι'} {g : ι -> ι'} {f : ι -
> N} (h : forall y ∉ t, (1 : N) <= ∏ x in…
-/
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' [MulLeftMono N] {t : Finset ι'} {g : ι → ι'}
    {f : ι → N} (h : ∀ y ∉ t, ∏ x ∈ s with g x = y, f x ≤ 1) :
    ∏ x ∈ s, f x ≤ ∏ y ∈ t, ∏ x ∈ s with g x = y, f x :=
  prod_fiberwise_le_prod_of_one_le_prod_fiber' (N := Nᵒᵈ) h

@[to_additive]
/-
**Finset.prod_image_le_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_image_le_of_one_le [MulLeftMono N] {g : ι -> ι'} {f : ι' -> N} (hf : 
forall u in s.image g, 1 <= f u) : ∏ u in s.image g, f u <= ∏ u in s, f (g u)
参数：hf : forall u in s.image g, 1 <= f u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_comp`：prod_comp [DecidableEq κ] (f : κ -> M) (g : ι -> κ) : 
∏ a in s, f (g a) = ∏ b in s.image g, f b ^ #{a in s | g a = b}
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用引理 `le_self_pow`：le_self_pow (ha : 1 <= a) (hn : n != 0) : a <= a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
lemma prod_image_le_of_one_le [MulLeftMono N]
    {g : ι → ι'} {f : ι' → N} (hf : ∀ u ∈ s.image g, 1 ≤ f u) :
    ∏ u ∈ s.image g, f u ≤ ∏ u ∈ s, f (g u) := by
  rw [prod_comp f g]
  refine prod_le_prod' fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  apply le_self_pow (hf a hag)
  rw [← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

end OrderedCommMonoid

section ProdSum

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  (s : Finset ι) {f : ι → α} (g : α → β)

/-
**Finset.apply_prod_le_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_prod_le_sum_apply (h_one : g 1 <= 0) (h_mul : forall (a b : α), g (a
 * b) <= g a + g b) : g (∏ x in s, f x) <= ∑ x in s, g (f x)
参数：h_one : g 1 <= 0；h_mul : forall (a b : α), g (a * b) <= g a + g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Multiset.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0)
 (h_mul : forall (a b : α), f (a * b) <= f a + f b) : f m.prod <= (m.map f).sum
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Finset.sum_map_val`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] (s : Finset ι) (f : ι → M),   (Multiset.map f s.val).sum = ∑ a ∈ s, f a
-/
theorem apply_prod_le_sum_apply (h_one : g 1 ≤ 0) (h_mul : ∀ (a b : α), g (a * b) ≤ g a + g b) :
    g (∏ x ∈ s, f x) ≤ ∑ x ∈ s, g (f x) := by
  refine (Multiset.apply_prod_le_sum_map _ _ h_one h_mul).trans_eq ?_
  rw [Multiset.map_map, Function.comp_def, Finset.sum_map_val]
/-
**Finset.sum_apply_le_apply_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_apply_le_apply_prod (h_one : 0 <= g 1) (h_mul : forall (a b : α), g a 
+ g b <= g (a * b)) : ∑ x in s, g (f x) <= g (∏ x in s, f x)
参数：h_one : 0 <= g 1；h_mul : forall (a b : α), g a + g b <= g (a * b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_prod_le_sum_apply`：apply_prod_le_sum_apply (h_one : g 1 <= 
0) (h_mul : forall (a b : α), g (a * b) <= g a + g b) : g (∏ x in s, f x) <= ∑ x
 in s, g (f x)
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
-/
theorem sum_apply_le_apply_prod (h_one : 0 ≤ g 1) (h_mul : ∀ (a b : α), g a + g b ≤ g (a * b)) :
    ∑ x ∈ s, g (f x) ≤ g (∏ x ∈ s, f x) :=
  s.apply_prod_le_sum_apply (β := βᵒᵈ) g h_one h_mul

end ProdSum

@[to_additive]
/-
**Finset.max_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：max_prod_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι ->
 M} {s : Finset ι} : max (s.prod f) (s.prod g) <= s.prod (fun i => max (f i) (g 
i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.max_prod_le`：max_prod_le [CommMonoid α] [LinearOrder α] [IsOrde
redMonoid α] {s : Multiset ι} {f g : ι -> α} : max (s.map f).prod (s.map g).prod
 <= (s.map…
-/
lemma max_prod_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι → M} {s : Finset ι} :
    max (s.prod f) (s.prod g) ≤ s.prod (fun i ↦ max (f i) (g i)) :=
  Multiset.max_prod_le

@[to_additive]
/-
**Finset.prod_min_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_min_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι ->
 M} {s : Finset ι} : s.prod (fun i => min (f i) (g i)) <= min (s.prod f) (s.prod
 g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_min_le`：prod_min_le [CommMonoid α] [LinearOrder α] [IsOrde
redMonoid α] {s : Multiset ι} {f g : ι -> α} : (s.map fun i => min (f i) (g i)).
prod <= mi…
-/
lemma prod_min_le [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] {f g : ι → M} {s : Finset ι} :
    s.prod (fun i ↦ min (f i) (g i)) ≤ min (s.prod f) (s.prod g) :=
  Multiset.prod_min_le
/-
**Finset.abs_sum_le_sum_abs** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：abs_sum_le_sum_abs {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrdered
AddMonoid G] (f : ι -> G) (s : Finset ι) : |∑ i in s, f i| <= ∑ i in s, |f i|
参数：f : ι -> G；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
-/
theorem abs_sum_le_sum_abs {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (f : ι → G) (s : Finset ι) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := le_sum_of_subadditive _ abs_zero.le abs_add_le s f
/-
**Finset.abs_sum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：abs_sum_of_nonneg {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMon
o G] {f : ι -> G} {s : Finset ι} (hf : forall i in s, 0 <= f i) : |∑ i in s, f i
| = ∑ i in s, f i
参数：hf : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
-/
theorem abs_sum_of_nonneg {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
    {f : ι → G} {s : Finset ι}
    (hf : ∀ i ∈ s, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]
/-
**Finset.abs_sum_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：abs_sum_of_nonneg' {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMo
no G] {f : ι -> G} {s : Finset ι} (hf : forall i, 0 <= f i) : |∑ i in s, f i| = 
∑ i in s, f i
参数：hf : forall i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Finset.sum_nonneg'`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoi
d N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ (i :
 ι), 0 ≤…
-/
theorem abs_sum_of_nonneg' {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
    {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]

section CommMonoid
variable [CommMonoid α] [LE α] [MulLeftMono α] {s : Finset ι} {f : ι → α}

@[to_additive (attr := simp)]
/-
**Finset.mulLECancellable_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulLECancellable_prod : MulLECancellable (∏ i in s, f i) ↔ forall ⦃i⦄, i i
n s -> MulLECancellable (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma mulLECancellable_prod :
    MulLECancellable (∏ i ∈ s, f i) ↔ ∀ ⦃i⦄, i ∈ s → MulLECancellable (f i) := by
  induction s using Finset.cons_induction <;> simp [*]

end CommMonoid

section Pigeonhole

variable [DecidableEq β]

/-
**Finset.card_le_mul_card_image_of_maps_to** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_mul_card_image_of_maps_to {f : α -> β} {s : Finset α} {t : Finset 
β} (Hf : forall a in s, f a in t) (n : Nat) (hn : forall b in t, #{a in s | f a 
= b} <= n) : #s <= n * #t
参数：Hf : forall a in s, f a in t；n : Nat；hn : forall b in t, #{a in s | f a = b} 
<= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #t :=
  calc
    #s = ∑ b ∈ t, #{a ∈ s | f a = b} := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _b ∈ t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]
/-
**Finset.card_le_mul_card_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_mul_card_image {f : α -> β} (s : Finset α) (n : Nat) (hn : forall 
b in s.image f, #{a in s | f a = b} <= n) : #s <= n * #(s.image f)
参数：s : Finset α；n : Nat；hn : forall b in s.image f, #{a in s | f a = b} <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_mul_card_image_of_maps_to`：card_le_mul_card_image_of_maps
_to {f : α -> β} {s : Finset α} {t : Finset β} (Hf : forall a in s, f a in t) (n
 : Nat) (hn : forall b in t, #…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem card_le_mul_card_image {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, #{a ∈ s | f a = b} ≤ n) : #s ≤ n * #(s.image f) :=
  card_le_mul_card_image_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn
/-
**Finset.mul_card_image_le_card_of_maps_to** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_card_image_le_card_of_maps_to {f : α -> β} {s : Finset α} {t : Finset 
β} (Hf : forall a in s, f a in t) (n : Nat) (hn : forall b in t, n <= #{a in s |
 f a = b}) : n * #t <= #s
参数：Hf : forall a in s, f a in t；n : Nat；hn : forall b in t, n <= #{a in s | f a 
= b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
-/
theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ b ∈ t, n ≤ #{a ∈ s | f a = b}) :
    n * #t ≤ #s :=
  calc
    n * #t = ∑ _a ∈ t, n := by simp [mul_comm]
    _ ≤ ∑ b ∈ t, #{a ∈ s | f a = b} := sum_le_sum hn
    _ = #s := by rw [← card_eq_sum_card_fiberwise Hf]
/-
**Finset.mul_card_image_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_card_image_le_card {f : α -> β} (s : Finset α) (n : Nat) (hn : forall 
b in s.image f, n <= #{a in s | f a = b}) : n * #(s.image f) <= #s
参数：s : Finset α；n : Nat；hn : forall b in s.image f, n <= #{a in s | f a = b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mul_card_image_le_card_of_maps_to`：mul_card_image_le_card_of_maps
_to {f : α -> β} {s : Finset α} {t : Finset β} (Hf : forall a in s, f a in t) (n
 : Nat) (hn : forall b in t, n…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem mul_card_image_le_card {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ b ∈ s.image f, n ≤ #{a ∈ s | f a = b}) : n * #(s.image f) ≤ #s :=
  mul_card_image_le_card_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn

end Pigeonhole

section DoubleCounting

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

/-- If every element belongs to at most `n` Finsets, then the sum of their sizes is at most `n`
times how many they are. -/
/-
**Finset.sum_card_inter_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_card_inter_le (h : forall a in s, #{b in B | a in b} <= n) : (∑ t in B
, #(s inter t)) <= #s * n
参数：h : forall a in s, #{b in B | a in b} <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If every element belongs to at most `n` Finsets, then the sum of their sizes is 
at most `n`
times how many they are.
-/
theorem sum_card_inter_le (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} ≤ n) : (∑ t ∈ B, #(s ∩ t)) ≤ #s * n := by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

/-- If every element belongs to at most `n` Finsets, then the sum of their sizes is at most `n`
times how many they are. -/
/-
**Finset.sum_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_card_le [Fintype α] (h : forall a, #{b in B | a in b} <= n) : ∑ s in B
, #s <= Fintype.card α * n
参数：h : forall a, #{b in B | a in b} <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_card_inter_le`：sum_card_inter_le (h : forall a in s, #{b in B
 | a in b} <= n) : (∑ t in B, #(s inter t)) <= #s * n

--- 原说明 ---
If every element belongs to at most `n` Finsets, then the sum of their sizes is 
at most `n`
times how many they are.
-/
lemma sum_card_le [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} ≤ n) : ∑ s ∈ B, #s ≤ Fintype.card α * n :=
  calc
    ∑ s ∈ B, #s = ∑ s ∈ B, #(univ ∩ s) := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := sum_card_inter_le fun a _ ↦ h a

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
/-
**Finset.le_sum_card_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sum_card_inter (h : forall a in s, n <= #{b in B | a in b}) : #s * n <=
 ∑ t in B, #(s inter t)
参数：h : forall a in s, n <= #{b in B | a in b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…

--- 原说明 ---
If every element belongs to at least `n` Finsets, then the sum of their sizes is
 at least `n`
times how many they are.
-/
theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ #{b ∈ B | a ∈ b}) : #s * n ≤ ∑ t ∈ B, #(s ∩ t) := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
/-
**Finset.le_sum_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sum_card [Fintype α] (h : forall a, n <= #{b in B | a in b}) : Fintype.
card α * n <= ∑ s in B, #s
参数：h : forall a, n <= #{b in B | a in b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_card_inter`：le_sum_card_inter (h : forall a in s, n <= #{b
 in B | a in b}) : #s * n <= ∑ t in B, #(s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If every element belongs to at least `n` Finsets, then the sum of their sizes is
 at least `n`
times how many they are.
-/
theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ #{b ∈ B | a ∈ b}) :
    Fintype.card α * n ≤ ∑ s ∈ B, #s :=
  calc
    Fintype.card α * n ≤ ∑ s ∈ B, #(univ ∩ s) := le_sum_card_inter fun a _ ↦ h a
    _ = ∑ s ∈ B, #s := by simp_rw [univ_inter]

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
/-
**Finset.sum_card_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_card_inter (h : forall a in s, #{b in B | a in b} = n) : (∑ t in B, #(
s inter t)) = #s * n
参数：h : forall a in s, #{b in B | a in b} = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.sum_card_inter_le`：sum_card_inter_le (h : forall a in s, #{b in B
 | a in b} <= n) : (∑ t in B, #(s inter t)) <= #s * n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.le_sum_card_inter`：le_sum_card_inter (h : forall a in s, n <= #{b
 in B | a in b}) : #s * n <= ∑ t in B, #(s inter t)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
If every element belongs to exactly `n` Finsets, then the sum of their sizes is 
`n` times how
many they are.
-/
theorem sum_card_inter (h : ∀ a ∈ s, #{b ∈ B | a ∈ b} = n) :
    (∑ t ∈ B, #(s ∩ t)) = #s * n :=
  (sum_card_inter_le fun a ha ↦ (h a ha).le).antisymm (le_sum_card_inter fun a ha ↦ (h a ha).ge)

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
/-
**Finset.sum_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_card [Fintype α] (h : forall a, #{b in B | a in b} = n) : ∑ s in B, #s
 = Fintype.card α * n
参数：h : forall a, #{b in B | a in b} = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_card_inter`：sum_card_inter (h : forall a in s, #{b in B | a i
n b} = n) : (∑ t in B, #(s inter t)) = #s * n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If every element belongs to exactly `n` Finsets, then the sum of their sizes is 
`n` times how
many they are.
-/
theorem sum_card [Fintype α] (h : ∀ a, #{b ∈ B | a ∈ b} = n) :
    ∑ s ∈ B, #s = Fintype.card α * n := by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ ↦ h a, univ_inter]
/-
**Finset.card_le_card_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_biUnion {s : Finset ι} {f : ι -> Finset α} (hs : (s : Set ι).
PairwiseDisjoint f) (hf : forall i in s, (f i).Nonempty) : #s <= #(s.biUnion f)
参数：hs : (s : Set ι).PairwiseDisjoint f；hf : forall i in s, (f i).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
-/
theorem card_le_card_biUnion {s : Finset ι} {f : ι → Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : ∀ i ∈ s, (f i).Nonempty) : #s ≤ #(s.biUnion f) := by
  rw [card_biUnion hs, card_eq_sum_ones]
  exact sum_le_sum fun i hi ↦ (hf i hi).card_pos
/-
**Finset.card_le_card_biUnion_add_card_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι -> Finset α} (hs
 : (s : Set ι).PairwiseDisjoint f) : #s <= #(s.biUnion f) + #{i in s | f i = ∅}
参数：hs : (s : Set ι).PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_filter_add_card_filter_not`：card_filter_add_card_filter_not 
(p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : #(s.filter p) +
 #(s.filter fun a => ¬ p a) …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.card_le_card_biUnion`：card_le_card_biUnion {s : Finset ι} {f : ι 
-> Finset α} (hs : (s : Set ι).PairwiseDisjoint f) (hf : forall i in s, (f i).No
nempty) : #s <= #…
· 使用定理 `Set.PairwiseDisjoint.subset`：∀ {α : Type u_1} {ι : Type u_4} [inst : Par
tialOrder α] [inst_1 : OrderBot α] {s t : Set ι} {f : ι → α},   t.PairwiseDisjoi
nt f → s ⊆ t → s.…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `Finset.biUnion_subset_biUnion_of_subset_left`：biUnion_subset_biUnion_of_
subset_left (t : α -> Finset β) (h : s₁ subseteq s₂) : s₁.biUnion t subseteq s₂.
biUnion t
-/
theorem card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι → Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + #{i ∈ s | f i = ∅} := by
  rw [← Finset.card_filter_add_card_filter_not fun i ↦ f i = ∅, add_comm]
  grw [card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi ↦
    nonempty_of_ne_empty (mem_filter.1 hi).2, filter_subset]
/-
**Finset.card_le_card_biUnion_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_biUnion_add_one {s : Finset ι} {f : ι -> Finset α} (hf : Inje
ctive f) (hs : (s : Set ι).PairwiseDisjoint f) : #s <= #(s.biUnion f) + 1
参数：hf : Injective f；hs : (s : Set ι).PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.card_le_card_biUnion_add_card_fiber`：card_le_card_biUnion_add_car
d_fiber {s : Finset ι} {f : ι -> Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
 : #s <= #(s.biUnion f) + #{i in…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_le_card_biUnion_add_one {s : Finset ι} {f : ι → Finset α} (hf : Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + 1 := by
  grw [card_le_card_biUnion_add_card_fiber hs,
    card_le_one.2 fun _ hi _ hj ↦ hf <| (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm]

end DoubleCounting

section CanonicallyOrderedMul

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

/-- In a canonically-ordered monoid, a product bounds each of its terms.

See also `Finset.single_le_prod'`. -/
@[to_additive /-- In a canonically-ordered additive monoid, a sum bounds each of its terms.

See also `Finset.single_le_sum`. -/]
/-
**Finset.single_le_prod_of_canonicallyOrdered** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：single_le_prod_of_canonicallyOrdered {i : ι} (hi : i in s) : f i <= ∏ j in
 s, f j
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedMul.toIsOrderedMonoid`：CanonicallyOrderedMul.toIsOrder
edMonoid [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid
 α where mul_le_mul_left _ _
· 使用定理 `Finset.single_le_prod'`：single_le_prod' [MulLeftMono N] (hf : forall i i
n s, 1 <= f i) {a} (h : a in s) : f a <= ∏ x in s, f x
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
lemma single_le_prod_of_canonicallyOrdered {i : ι} (hi : i ∈ s) :
    f i ≤ ∏ j ∈ s, f j :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  single_le_prod' (fun _ _ ↦ one_le) hi

@[to_additive sum_le_sum_of_subset]
/-
**Finset.prod_le_prod_of_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_subset' (h : s subseteq t) : ∏ x in s, f x <= ∏ x in t, f 
x
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedMul.toIsOrderedMonoid`：CanonicallyOrderedMul.toIsOrder
edMonoid [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid
 α where mul_le_mul_left _ _
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
theorem prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ ↦ one_le

@[to_additive sum_mono_set]
/-
**Finset.prod_mono_set'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mono_set' (f : ι -> M) : Monotone fun s => ∏ x in s, f x
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedMul.toIsOrderedMonoid`：CanonicallyOrderedMul.toIsOrder
edMonoid [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid
 α where mul_le_mul_left _ _
· 使用定理 `Finset.prod_le_prod_of_subset'`：prod_le_prod_of_subset' (h : s subseteq 
t) : ∏ x in s, f x <= ∏ x in t, f x
-/
theorem prod_mono_set' (f : ι → M) : Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hs ↦
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  prod_le_prod_of_subset' hs

@[to_additive sum_le_sum_of_ne_zero]
/-
**Finset.prod_le_prod_of_ne_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_ne_one' (h : forall x in s, f x != 1 -> x in t) : ∏ x in s
, f x <= ∏ x in t, f x
参数：h : forall x in s, f x != 1 -> x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedMul.toIsOrderedMonoid`：CanonicallyOrderedMul.toIsOrder
edMonoid [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid
 α where mul_le_mul_left _ _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
· 使用定理 `mul_le_of_le_one_of_le`：mul_le_of_le_one_of_le [MulRightMono α] {a b c :
 α} (ha : a <= 1) (hbc : b <= c) : a * b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Finset.prod_le_one'`：prod_le_one' [MulLeftMono N] (h : forall i in s, f 
i <= 1) : ∏ i in s, f i <= 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.prod_le_prod_of_subset'`：prod_le_prod_of_subset' (h : s subseteq 
t) : ∏ x in s, f x <= ∏ x in t, f x
-/
theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  classical calc
    ∏ x ∈ s, f x = (∏ x ∈ s with f x = 1, f x) * ∏ x ∈ s with f x ≠ 1, f x := by
      rw [← prod_union, filter_union_filter_not_eq]
      exact disjoint_filter.2 fun _ _ h n_h ↦ n_h h
    _ ≤ ∏ x ∈ t, f x :=
      mul_le_of_le_one_of_le
        (prod_le_one' <| by simp only [mem_filter, and_imp]; exact fun _ _ ↦ le_of_eq)
        (prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp])

@[to_additive sum_pos_iff]
/-
**Finset.one_lt_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_lt_prod_iff {ι M : Type*} [CommMonoid M] [PartialOrder M] [Canonically
OrderedMul M] {f : ι -> M} {s : Finset ι} : 1 < ∏ x in s, f x ↔ exists x in s, 1
 < f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedMul.toIsOrderedMonoid`：CanonicallyOrderedMul.toIsOrder
edMonoid [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid
 α where mul_le_mul_left _ _
· 使用引理 `Finset.one_lt_prod_iff_of_one_le`：one_lt_prod_iff_of_one_le {ι : Type u_
1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} [M
ulLeftMono N] (hf : fo…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
lemma one_lt_prod_iff {ι M : Type*} [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M]
    {f : ι → M} {s : Finset ι} : 1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x :=
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  Finset.one_lt_prod_iff_of_one_le <| fun _ _ => one_le

/-- In a canonically-ordered monoid, if `S'` is contained in `(S.erase d) ∪ {d'}` and
`f d' < f d` for some `d ∈ S`, then the product of `f` over `S'` is strictly less than over `S`. -/
@[to_additive /-- In a canonically-ordered additive monoid, if `S'` is contained in
`(S.erase d) ∪ {d'}` and `f d' < f d` for some `d ∈ S`, then the sum of `f` over `S'` is
strictly less than over `S`. -/]
/-
**Finset.prod_lt_prod_of_subset_erase_union_singleton** 是 Mathlib 中的一个引理，位于命名空间 
`Finset`。
形式化陈述：prod_lt_prod_of_subset_erase_union_singleton {ι M : Type*} [DecidableEq ι]
 [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M] [MulLeftStrictMono M]
 {S S' : Finset ι} {f : ι -> M} {d d' : ι} (hd_mem : d in S) (hS' : S' subseteq 
S.erase d union {d'}) (hlt : f d' < f d) : ∏ x in S', f x < ∏ x in S, f x
参数：hd_mem : d in S；hS' : S' subseteq S.erase d union {d'}；hlt : f d' < f d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.prod_le_prod_of_subset'`：prod_le_prod_of_subset' (h : s subseteq 
t) : ∏ x in s, f x <= ∏ x in t, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
lemma prod_lt_prod_of_subset_erase_union_singleton {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    [PartialOrder M] [CanonicallyOrderedMul M] [MulLeftStrictMono M] {S S' : Finset ι} {f : ι → M}
    {d d' : ι} (hd_mem : d ∈ S) (hS' : S' ⊆ S.erase d ∪ {d'}) (hlt : f d' < f d) :
    ∏ x ∈ S', f x < ∏ x ∈ S, f x := by
  have hd_not : d ∉ S' := fun hd ↦ (Finset.mem_union.mp (hS' hd)).elim
    (fun h ↦ (Finset.mem_erase.mp h).1 rfl)
    (fun h ↦ hlt.ne' (congrArg f (Finset.mem_singleton.mp h)))
  by_cases hd'S : d' ∈ S
  · calc ∏ x ∈ S', f x
        ≤ ∏ x ∈ S.erase d, f x := Finset.prod_le_prod_of_subset' (fun x hx ↦
          Finset.mem_erase.mpr ⟨fun h ↦ hd_not (h ▸ hx),
            match Finset.mem_union.mp (hS' hx) with
            | .inl h => Finset.mem_of_mem_erase h
            | .inr h => Finset.mem_singleton.mp h ▸ hd'S⟩)
      _ < (∏ x ∈ S.erase d, f x) * f d :=
          lt_mul_of_one_lt_right' _ (one_le.trans_lt hlt)
      _ = ∏ x ∈ S, f x := Finset.prod_erase_mul S f hd_mem
  · calc ∏ x ∈ S', f x
        ≤ ∏ x ∈ S.erase d ∪ {d'}, f x := Finset.prod_le_prod_of_subset' hS'
      _ = (∏ x ∈ S.erase d, f x) * f d' := by
          rw [Finset.prod_union (Finset.disjoint_singleton_right.mpr
            (fun h ↦ hd'S (Finset.mem_of_mem_erase h))), Finset.prod_singleton]
      _ < (∏ x ∈ S.erase d, f x) * f d := mul_lt_mul_right hlt _
      _ = ∏ x ∈ S, f x := Finset.prod_erase_mul S f hd_mem

end CanonicallyOrderedMul

section OrderedCancelCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

@[to_additive sum_lt_sum]
/-
**Finset.prod_lt_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_lt_prod' [MulLeftStrictMono M] (hle : forall i in s, f i <= g i) (hlt
 : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s, g i
参数：hle : forall i in s, f i <= g i；hlt : exists i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_lt_prod'`：prod_lt_prod' (hle : forall i in s, f i <= g i) 
(hlt : exists i in s, f i < g i) : (s.map f).prod < (s.map g).prod
-/
theorem prod_lt_prod' [MulLeftStrictMono M] (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod' hle hlt

/-- In an ordered commutative monoid, if each factor `f i` of one nontrivial finite product is
strictly less than the corresponding factor `g i` of another nontrivial finite product, then
`s.prod f < s.prod g`. -/
@[to_additive (attr := gcongr) sum_lt_sum_of_nonempty]
/-
**Finset.prod_lt_prod_of_nonempty'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_lt_prod_of_nonempty' [MulLeftStrictMono M] (hs : s.Nonempty) (hlt : f
orall i in s, f i < g i) : ∏ i in s, f i < ∏ i in s, g i
参数：hs : s.Nonempty；hlt : forall i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_lt_prod_of_nonempty'`：prod_lt_prod_of_nonempty' (hs : s !=
 ∅) (hfg : forall i in s, f i < g i) : (s.map f).prod < (s.map g).prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In an ordered commutative monoid, if each factor `f i` of one nontrivial finite 
product is
strictly less than the corresponding factor `g i` of another nontrivial finite p
roduct, then
`s.prod f < s.prod g`.
-/
theorem prod_lt_prod_of_nonempty' [MulLeftStrictMono M] (hs : s.Nonempty)
  (hlt : ∀ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt

/-- In an ordered additive commutative monoid, if each summand `f i` of one nontrivial finite sum is
strictly less than the corresponding summand `g i` of another nontrivial finite sum, then
`s.sum f < s.sum g`. -/
add_decl_doc sum_lt_sum_of_nonempty

@[to_additive sum_lt_sum_of_subset]
/-
**Finset.prod_lt_prod_of_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_lt_prod_of_subset' [MulLeftStrictMono M] (h : s subseteq t) {i : ι} (
ht : i in t) (hs : i ∉ s) (hlt : 1 < f i) (hle : forall j in t, j ∉ s -> 1 <= f 
j) : ∏ j in s, f j < ∏ j in t, f j
参数：h : s subseteq t；ht : i in t；hs : i ∉ s；hlt : 1 < f i；hle : forall j in t, j 
∉ s -> 1 <= f j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `lt_mul_of_one_lt_left'`：lt_mul_of_one_lt_left' [MulRightStrictMono α] (a
 : α) {b : α} (h : 1 < b) : a < b * a
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_lt_prod_of_subset' [MulLeftStrictMono M] (h : s ⊆ t) {i : ι} (ht : i ∈ t)
  (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : ∏ j ∈ s, f j < ∏ j ∈ t, f j := by
  classical calc
    ∏ j ∈ s, f j < ∏ j ∈ insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j ∈ s, f j) hlt
    _ ≤ ∏ j ∈ t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2

@[to_additive single_lt_sum]
/-
**Finset.single_lt_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：single_lt_prod' [MulLeftStrictMono M] {i j : ι} (hij : j != i) (hi : i in 
s) (hj : j in s) (hlt : 1 < f j) (hle : forall k in s, k != i -> 1 <= f k) : f i
 < ∏ k in s, f k
参数：hij : j != i；hi : i in s；hj : j in s；hlt : 1 < f j；hle : forall k in s, k != 
i -> 1 <= f k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.prod_lt_prod_of_subset'`：prod_lt_prod_of_subset' [MulLeftStrictMo
no M] (h : s subseteq t) {i : ι} (ht : i in t) (hs : i ∉ s) (hlt : 1 < f i) (hle
 : forall j in t, j …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem single_lt_prod' [MulLeftStrictMono M] {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s)
    (hlt : 1 < f j) (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k ∈ s, f k :=
  calc
    f i = ∏ k ∈ {i}, f k := by rw [prod_singleton]
    _ < ∏ k ∈ s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki ↦ hle k hks (mt mem_singleton.2 hki)

@[to_additive sum_pos]
/-
**Finset.one_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_lt_prod [MulLeftStrictMono M] (h : forall i in s, 1 < f i) (hs : s.Non
empty) : 1 < ∏ i in s, f i
参数：h : forall i in s, 1 < f i；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.prod_lt_prod_of_nonempty'`：prod_lt_prod_of_nonempty' [MulLeftStri
ctMono M] (hs : s.Nonempty) (hlt : forall i in s, f i < g i) : ∏ i in s, f i < ∏
 i in s, g i
-/
theorem one_lt_prod [MulLeftStrictMono M] (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) :
    1 < ∏ i ∈ s, f i :=
  lt_of_le_of_lt (by rw [prod_const_one]) <| prod_lt_prod_of_nonempty' hs h

@[to_additive]
/-
**Finset.prod_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_lt_one [MulLeftStrictMono M] (h : forall i in s, f i < 1) (hs : s.Non
empty) : ∏ i in s, f i < 1
参数：h : forall i in s, f i < 1；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.prod_lt_prod_of_nonempty'`：prod_lt_prod_of_nonempty' [MulLeftStri
ctMono M] (hs : s.Nonempty) (hlt : forall i in s, f i < g i) : ∏ i in s, f i < ∏
 i in s, g i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_lt_one [MulLeftStrictMono M] (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) :
    ∏ i ∈ s, f i < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])

@[to_additive sum_pos']
/-
**Finset.one_lt_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_lt_prod' [MulLeftStrictMono M] (h : forall i in s, 1 <= f i) (hs : exi
sts i in s, 1 < f i) : 1 < ∏ i in s, f i
参数：h : forall i in s, 1 <= f i；hs : exists i in s, 1 < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_lt_prod'`：prod_lt_prod' [MulLeftStrictMono M] (hle : forall 
i in s, f i <= g i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s,
 g i
-/
theorem one_lt_prod' [MulLeftStrictMono M] (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) :
    1 < ∏ i ∈ s, f i :=
  prod_const_one.symm.trans_lt <| prod_lt_prod' h hs

@[to_additive]
/-
**Finset.prod_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_lt_one' [MulLeftStrictMono M] (h : forall i in s, f i <= 1) (hs : exi
sts i in s, f i < 1) : ∏ i in s, f i < 1
参数：h : forall i in s, f i <= 1；hs : exists i in s, f i < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_lt_prod'`：prod_lt_prod' [MulLeftStrictMono M] (hle : forall 
i in s, f i <= g i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s,
 g i
-/
theorem prod_lt_one' [MulLeftStrictMono M] (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) :
    ∏ i ∈ s, f i < 1 :=
  prod_const_one.le.trans_lt' <| prod_lt_prod' h hs

@[to_additive]
/-
**Finset.prod_eq_prod_iff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_iff_of_le {ι M : Type*} [CommMonoid M] [PartialOrder M] [IsOr
deredCancelMonoid M] {s : Finset ι} {f g : ι -> M} (h : forall i in s, f i <= g 
i) : ((∏ i in s, f i) = ∏ i in s, g i) ↔ forall i in s, f i = g i
参数：h : forall i in s, f i <= g i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `mul_eq_mul_iff_eq_and_eq`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Part
ialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α] {a b c d : α},   a ≤ c 
→ b ≤ d → (a *…
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
-/
theorem prod_eq_prod_iff_of_le {ι M : Type*} [CommMonoid M] [PartialOrder M]
  [IsOrderedCancelMonoid M] {s : Finset ι} {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i ∈ s, f i) = ∏ i ∈ s, g i) ↔ ∀ i ∈ s, f i = g i := by
  classical
    revert h
    refine Finset.induction_on s (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.notMem_empty _ h),
      fun _ ↦ rfl⟩) fun a s ha ih H ↦ ?_
    specialize ih fun i ↦ H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.forall_mem_insert, ← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i ↦ H i ∘ Finset.mem_insert_of_mem)
/-
**Finset.prod_sdiff_le_prod_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {f : ι → M}   {s t : Finset ι} [inst_3 : DecidableEq
 ι], ∏ i ∈ s \ t, f i ≤ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_sdiff_inter`：disjoint_sdiff_inter (s t : Finset α) : Dis
joint (s \ t) (s inter t)
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma prod_sdiff_le_prod_sdiff [DecidableEq ι] :
    ∏ i ∈ s \ t, f i ≤ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← mul_le_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s
/-
**Finset.prod_sdiff_lt_prod_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_9} {M : Type u_10} [inst : CommMonoid M] [inst_1 : PartialOr
der M] [IsOrderedCancelMonoid M]   [inst_3 : DecidableEq ι] {s t : Finset ι} {f 
: ι → M},   ∏ i ∈ s \ t, f i < ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i < ∏ i ∈ t, f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_sdiff_inter`：disjoint_sdiff_inter (s t : Finset α) : Dis
joint (s \ t) (s inter t)
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma prod_sdiff_lt_prod_sdiff {ι M : Type*} [CommMonoid M] [PartialOrder M]
  [IsOrderedCancelMonoid M] [DecidableEq ι] {s t : Finset ι} {f : ι → M} :
    ∏ i ∈ s \ t, f i < ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i < ∏ i ∈ t, f i := by
  rw [← mul_lt_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter]
  simpa only [inter_comm] using disjoint_sdiff_inter t s

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [CommMonoid M] [LinearOrder M] {f g : ι → M} {s t : Finset ι}

@[to_additive exists_lt_of_sum_lt]
/-
**Finset.exists_lt_of_prod_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_lt_of_prod_lt' [MulLeftMono M] (Hlt : ∏ i in s, f i < ∏ i in s, g i
) : exists i in s, f i < g i
参数：Hlt : ∏ i in s, f i < ∏ i in s, g i。
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
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
-/
theorem exists_lt_of_prod_lt' [MulLeftMono M] (Hlt : ∏ i ∈ s, f i < ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i < g i := by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle

variable [IsOrderedCancelMonoid M]

@[to_additive exists_le_of_sum_le]
/-
**Finset.exists_le_of_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i in s, f i <= ∏ i in s, 
g i) : exists i in s, f i <= g i
参数：hs : s.Nonempty；Hle : ∏ i in s, f i <= ∏ i in s, g i。
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
· 使用定理 `Finset.prod_lt_prod_of_nonempty'`：prod_lt_prod_of_nonempty' [MulLeftStri
ctMono M] (hs : s.Nonempty) (hlt : forall i in s, f i < g i) : ∏ i in s, f i < ∏
 i in s, g i
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
-/
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
/-
**Finset.exists_one_lt_of_prod_one_of_exists_ne_one'** 是 Mathlib 中的一个定理，位于命名空间 `
Finset`。
形式化陈述：exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι -> M) (h₁ : ∏ i in s, f
 i = 1) (h₂ : exists i in s, f i != 1) : exists i in s, 1 < f i
参数：f : ι -> M；h₁ : ∏ i in s, f i = 1；h₂ : exists i in s, f i != 1。
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
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Finset.prod_lt_prod'`：prod_lt_prod' [MulLeftStrictMono M] (hle : forall 
i in s, f i <= g i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s,
 g i
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : ∏ i ∈ s, f i = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    ∏ j ∈ s, f j < ∏ j ∈ s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one

end LinearOrderedCancelCommMonoid

/-
**Finset.apply_sup_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_sup_le_sum [SemilatticeSup α] [OrderBot α] [AddCommMonoid β] [Preord
er β] [AddLeftMono β] {f : α -> β} (zero : f ⊥ = 0) (ih : forall {s t}, f (s ⊔ t
) <= f s + f t) {s : ι -> α} (t : Finset ι) : f (t.sup s) <= ∑ i in t, f (s i)
参数：zero : f ⊥ = 0；ih : forall {s t}, f (s ⊔ t) <= f s + f t；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem apply_sup_le_sum [SemilatticeSup α] [OrderBot α]
    [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : α → β} (zero : f ⊥ = 0) (ih : ∀ {s t}, f (s ⊔ t) ≤ f s + f t)
    {s : ι → α} (t : Finset ι) :
    f (t.sup s) ≤ ∑ i ∈ t, f (s i) := by
  classical
  refine t.induction_on zero.le fun i t it h ↦ ?_
  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)
/-
**Finset.apply_union_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_union_le_sum [AddCommMonoid β] [Preorder β] [AddLeftMono β] {f : Set
 α -> β} (zero : f ∅ = 0) (ih : forall {s t}, f (s union t) <= f s + f t) {s : ι
 -> Set α} (t : Finset ι) : f (⋃ i in t, s i) <= ∑ i in t, f (s i)
参数：zero : f ∅ = 0；ih : forall {s t}, f (s union t) <= f s + f t；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_le_sum`：apply_sup_le_sum [SemilatticeSup α] [OrderBot α
] [AddCommMonoid β] [Preorder β] [AddLeftMono β] {f : α -> β} (zero : f ⊥ = 0) (
ih : forall {…
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
-/
theorem apply_union_le_sum [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : Set α → β} (zero : f ∅ = 0) (ih : ∀ {s t}, f (s ∪ t) ≤ f s + f t)
    {s : ι → Set α} (t : Finset ι) :
    f (⋃ i ∈ t, s i) ≤ ∑ i ∈ t, f (s i) :=
  Finset.sup_set_eq_biUnion t s ▸ t.apply_sup_le_sum zero (by simpa)
/-
**Finset.sum_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_le_one_iff {s : Finset α} {f : α -> Nat} : ∑ x in s, f x <= 1 ↔ forall
 x y, x in s -> y in s -> f x != 0 -> f y != 0 -> x = y ∧ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.sum_mono_set`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] (f : ι → M),   Monotone fu
n s => ∑ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem sum_le_one_iff {s : Finset α} {f : α → ℕ} :
    ∑ x ∈ s, f x ≤ 1 ↔ ∀ x y, x ∈ s → y ∈ s → f x ≠ 0 → f y ≠ 0 → x = y ∧ f x = 1 := by
  classical
  refine ⟨fun h x y hsx hsy hfx hfy ↦ ?_, fun h ↦ ?_⟩
  · replace h := (sum_mono_set f (show {x, y} ⊆ s by grind)).trans h
    grind
  · by_cases! hx : ∃ x ∈ s, f x ≠ 0
    · obtain ⟨x, hsx, hfx⟩ := hx
      have hs : ∀ y ∈ s \ {x}, f y = 0 := by grind
      simp [← sum_sdiff (singleton_subset_iff.2 hsx), sum_congr rfl hs, (h x x hsx hsx hfx hfx).2]
    · simp [sum_congr rfl hx]

end Finset

namespace Fintype
section OrderedCommMonoid
variable [Fintype ι] [CommMonoid M] [Preorder M] [MulLeftMono M] {f : ι → M}

@[to_additive (attr := mono) sum_mono]
/-
**Fintype.prod_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_mono' : Monotone fun f : ι -> M => ∏ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
-/
theorem prod_mono' : Monotone fun f : ι → M ↦ ∏ i, f i := fun _ _ hfg ↦
  Finset.prod_le_prod' fun x _ ↦ hfg x

@[to_additive sum_nonneg]
/-
**Fintype.one_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：one_le_prod (hf : 1 <= f) : 1 <= ∏ i, f i
参数：hf : 1 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
-/
lemma one_le_prod (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod' fun _ _ ↦ hf _
/-
**Fintype.prod_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [inst_1 : CommMonoid M]
 [inst_2 : Preorder M] [MulLeftMono M]   {f : ι → M}, f ≤ 1 → ∏ i, f i ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_one'`：prod_le_one' [MulLeftMono N] (h : forall i in s, f 
i <= 1) : ∏ i in s, f i <= 1
-/
@[to_additive] lemma prod_le_one (hf : f ≤ 1) : ∏ i, f i ≤ 1 := Finset.prod_le_one' fun _ _ ↦ hf _

@[to_additive]
/-
**Fintype.prod_eq_one_iff_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_eq_one_iff_of_one_le {ι M : Type*} [Fintype ι] [CommMonoid M] [Partia
lOrder M] [MulLeftMono M] {f : ι -> M} (hf : 1 <= f) : ∏ i, f i = 1 ↔ f = 1
参数：hf : 1 <= f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.prod_eq_one_iff_of_one_le'`：prod_eq_one_iff_of_one_le' {ι : Type 
u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} 
[MulLeftMono N] : (fora…
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prod_eq_one_iff_of_one_le {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
    [MulLeftMono M] {f : ι → M} (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_one_le' fun i _ ↦ hf i).trans <| by simp [funext_iff]

@[to_additive]
/-
**Fintype.prod_eq_one_iff_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_eq_one_iff_of_le_one {ι M : Type*} [Fintype ι] [CommMonoid M] [Partia
lOrder M] [MulLeftMono M] {f : ι -> M} (hf : f <= 1) : ∏ i, f i = 1 ↔ f = 1
参数：hf : f <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.prod_eq_one_iff_of_le_one'`：prod_eq_one_iff_of_le_one' {ι : Type 
u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N] {f : ι -> N} {s : Finset ι} 
[MulLeftMono N] : (fora…
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prod_eq_one_iff_of_le_one {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
    [MulLeftMono M] {f : ι → M} (hf : f ≤ 1) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_le_one' fun i _ ↦ hf i).trans <| by simp [funext_iff]

end OrderedCommMonoid

section OrderedCancelCommMonoid
variable [Fintype ι] [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M] {f : ι → M}

@[to_additive sum_strictMono]
/-
**Fintype.prod_strictMono'** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_strictMono' : StrictMono fun f : ι -> M => ∏ x, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `Finset.prod_lt_prod'`：prod_lt_prod' [MulLeftStrictMono M] (hle : forall 
i in s, f i <= g i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s,
 g i
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem prod_strictMono' : StrictMono fun f : ι → M ↦ ∏ x, f x :=
  fun _ _ hfg ↦
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ ↦ hle i) ⟨i, Finset.mem_univ i, hlt⟩

@[to_additive sum_pos]
/-
**Fintype.one_lt_prod** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i
参数：hf : 1 < f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.one_lt_prod'`：one_lt_prod' [MulLeftStrictMono M] (h : forall i in
 s, 1 <= f i) (hs : exists i in s, 1 < f i) : 1 < ∏ i in s, f i
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
lemma one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i :=
  Finset.one_lt_prod' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

@[to_additive]
/-
**Fintype.prod_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_lt_one (hf : f < 1) : ∏ i, f i < 1
参数：hf : f < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_lt_one'`：prod_lt_one' [MulLeftStrictMono M] (h : forall i in
 s, f i <= 1) (hs : exists i in s, f i < 1) : ∏ i in s, f i < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
lemma prod_lt_one (hf : f < 1) : ∏ i, f i < 1 :=
  Finset.prod_lt_one' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]
/-
**Fintype.one_lt_prod_iff_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：one_lt_prod_iff_of_one_le (hf : 1 <= f) : 1 < ∏ i, f i ↔ 1 < f
参数：hf : 1 <= f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma one_lt_prod_iff_of_one_le (hf : 1 ≤ f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]
/-
**Fintype.prod_lt_one_iff_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_lt_one_iff_of_le_one (hf : f <= 1) : ∏ i, f i < 1 ↔ f < 1
参数：hf : f <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma prod_lt_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

end OrderedCancelCommMonoid
end Fintype

namespace Multiset

/-
**Multiset.finsetSum_eq_sup_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：finsetSum_eq_sup_iff_disjoint [DecidableEq α] {i : Finset β} {f : β -> Mul
tiset α} : i.sum f = i.sup f ↔ forall x in i, forall y in i, x != y -> Disjoint 
(f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Multiset.add_eq_union_left_of_le`：add_eq_union_left_of_le [DecidableEq α
] {s t u : Multiset α} (h : t <= s) : u + s = u union t ↔ Disjoint u s ∧ s = t
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Multiset.le_sum_of_mem`：∀ {α : Type u_2} [inst : AddCommMonoid α] {m : M
ultiset α} {a : α},   a ∈ m → ∀ [inst_1 : Preorder α] [CanonicallyOrderedAdd α],
 a ≤ m.sum
· 使用定理 `Multiset.mem_map_of_mem`：mem_map_of_mem (f : α -> β) {a : α} {s : Multis
et α} (h : a in s) : f a in map f s
· 使用定理 `Multiset.instCanonicallyOrderedAdd`：∀ {α : Type u_1}, CanonicallyOrdered
Add (Multiset α)
-/
theorem finsetSum_eq_sup_iff_disjoint [DecidableEq α] {i : Finset β} {f : β → Multiset α} :
    i.sum f = i.sup f ↔ ∀ x ∈ i, ∀ y ∈ i, x ≠ y → Disjoint (f x) (f y) := by
  induction i using Finset.cons_induction_on with
  | empty =>
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero]
  | cons z i hz hr =>
    simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne, not_true_eq_false, IsEmpty.forall_iff, true_and,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (H : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp +contextual only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finsetSum_left, ← disjoint_finsetSum_right, disjoint_comm, ← and_assoc,
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))

@[deprecated (since := "2026-04-08")]
alias finset_sum_eq_sup_iff_disjoint := finsetSum_eq_sup_iff_disjoint
/-
**Multiset.sup_powerset_len** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_powerset_len [DecidableEq α] (x : Multiset α) : (Finset.sup (Finset.ra
nge (card x + 1)) fun k => x.powersetCard k) = x.powerset
参数：x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind.eq_1`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (f : 
α → Multiset β), s.bind f = (Multiset.map f s).join
· 使用定理 `Multiset.join.eq_1`：∀ {α : Type u_1}, Multiset.join = Multiset.sum
· 使用定理 `Finset.range_val`：range_val (n : Nat) : (range n).1 = Multiset.range n
· 使用定理 `Finset.sum_eq_multiset_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddC
ommMonoid M] (s : Finset ι) (f : ι → M),   ∑ x ∈ s, f x = (Multiset.map f s.val)
.sum
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.finsetSum_eq_sup_iff_disjoint`：finsetSum_eq_sup_iff_disjoint [D
ecidableEq α] {i : Finset β} {f : β -> Multiset α} : i.sum f = i.sup f ↔ forall 
x in i, forall y in i, x != …
· 使用定理 `Multiset.pairwise_disjoint_powersetCard`：pairwise_disjoint_powersetCard 
(s : Multiset α) : _root_.Pairwise fun i j => Disjoint (s.powersetCard i) (s.pow
ersetCard j)
· 使用定理 `Multiset.bind_powerset_len`：bind_powerset_len {α : Type*} (S : Multiset 
α) : (bind (Multiset.range (card S + 1)) fun k => S.powersetCard k) = S.powerset
-/
theorem sup_powerset_len [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finsetSum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)
/-
**Multiset.card_le_card_toFinset_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset
`。
形式化陈述：card_le_card_toFinset_add_one_iff [DecidableEq α] {m : Multiset α} : m.car
d <= m.toFinset.card + 1 ↔ forall x y, 1 < m.count x -> 1 < m.count y -> x = y ∧
 m.count x = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_sum_count_eq`：toFinset_sum_count_eq (s : Multiset ι) :
 ∑ a in s.toFinset, s.count a = card s
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用引理 `Finset.sum_tsub_distrib`：sum_tsub_distrib (s : Finset ι) {f g : ι -> M} 
(hfg : forall x in s, g x <= f x) : ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x 
in s, g x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_le_one_iff`：sum_le_one_iff {s : Finset α} {f : α -> Nat} : ∑ 
x in s, f x <= 1 ↔ forall x y, x in s -> y in s -> f x != 0 -> f y != 0 -> x = y
 ∧ f x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.one_le_count_iff_mem`：one_le_count_iff_mem {a : α} {s : Multise
t α} : 1 <= count a s ↔ a in s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem card_le_card_toFinset_add_one_iff [DecidableEq α] {m : Multiset α} :
    m.card ≤ m.toFinset.card + 1 ↔
      ∀ x y, 1 < m.count x → 1 < m.count y → x = y ∧ m.count x = 2 := by
  rw [← m.toFinset_sum_count_eq, m.toFinset.card_eq_sum_ones, ← tsub_le_iff_left,
    ← Finset.sum_tsub_distrib _ (by simp [one_le_count_iff_mem]), Finset.sum_le_one_iff]
  simp only [← pos_iff_ne_zero, Nat.sub_pos_iff_lt, mem_toFinset, Nat.pred_eq_succ_iff]
  exact ⟨fun h x y hx hy ↦ h x y (one_le_count_iff_mem.mp hx.le)
    (one_le_count_iff_mem.mp hy.le) hx hy, fun h x y _ _ hx hy ↦ h x y hx hy⟩

end Multiset

