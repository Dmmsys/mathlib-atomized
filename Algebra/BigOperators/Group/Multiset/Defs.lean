/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the Cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {F ι M N : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

/-- Product of a multiset given a commutative monoid structure on `M`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      /-- Sum of a multiset given a commutative additive monoid structure on `M`.
      `sum {a, b, c} = a + b + c` -/]
/-
**Multiset.prod** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：prod : Multiset M -> M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod : Multiset M → M :=
  foldr (· * ·) 1

@[to_additive]
/-
**Multiset.prod_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_foldr (s : Multiset M) : prod s = foldr (· * ·) 1 s
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_eq_foldr (s : Multiset M) :
    prod s = foldr (· * ·) 1 s :=
  rfl

@[to_additive]
/-
**Multiset.prod_eq_foldl** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_foldl (s : Multiset M) : prod s = foldl (· * ·) 1 s
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instRightCommutativeOfLeftCommutative`：∀ {α : Sort u} {β : Sort v} {f : 
α → β → β} [h : LeftCommutative f], RightCommutative fun x y => f y x
· 使用定理 `instRightCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → 
α → α} [hc : Std.Commutative f] [ha : Std.Associative f], RightCommutative f
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `Multiset.foldr_swap`：foldr_swap (f : α -> β -> β) [LeftCommutative f] (b
 : β) (s : Multiset α) : foldr f b s = foldl (fun x y => f y x) b s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.foldl.congr_simp`：∀ {α : Type u_1} {β : Type v} (f f_1 : β → α 
→ β) (e_f : f = f_1) [inst : RightCommutative f] (b b_1 : β),   b = b_1 → ∀ (s s
_1 : Multiset α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_foldl (s : Multiset M) :
    prod s = foldl (· * ·) 1 s :=
  (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]
/-
**Multiset.prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_coe (l : List M) : prod ↑l = l.prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe (l : List M) : prod ↑l = l.prod := rfl

@[to_additive (attr := simp)]
/-
**Multiset.prod_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_toList (s : Multiset M) : s.toList.prod = s.prod
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
-/
theorem prod_toList (s : Multiset M) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp, grind =)]
/-
**Multiset.prod_map_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_toList (s : Multiset ι) (f : ι -> M) : (s.toList.map f).prod = (s
.map f).prod
参数：s : Multiset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
-/
theorem prod_map_toList (s : Multiset ι) (f : ι → M) : (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, coe_toList]

@[to_additive (attr := simp, grind =)]
/-
**Multiset.prod_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_zero : @prod M _ 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_zero : @prod M _ 0 = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Multiset.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
参数：a : M；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.foldr_cons`：foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (fol
dr f b s)
-/
theorem prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _

@[to_additive (attr := simp)]
/-
**Multiset.prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_singleton (a : M) : prod {a} = a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_singleton (a : M) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, prod_zero]

@[to_additive]
/-
**Multiset.prod_pair** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.insert_eq_cons`：insert_eq_cons (a : α) (s : Multiset α) : inser
t a s = a ::ₘ s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]

@[to_additive (attr := simp)]
/-
**Multiset.prod_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_replicate (n : Nat) (a : M) : (replicate n a).prod = a ^ n
参数：n : Nat；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

@[to_additive]
/-
**Multiset.pow_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_eq`：filter_eq (s : Multiset α) (b : α) : s.filter (Eq b)
 = replicate (count b s) b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
-/
theorem pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, prod_replicate]

@[to_additive]
/-
**Multiset.prod_hom_rel** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom_rel (s : Multiset ι) {r : M -> N -> Prop} {f : ι -> M} {g : ι -> 
N} (h₁ : r 1 1) (h₂ : forall ⦃a b c⦄, r b c -> r (f a * b) (g a * c)) : r (s.map
 f).prod (s.map g).prod
参数：s : Multiset ι；h₁ : r 1 1；h₂ : forall ⦃a b c⦄, r b c -> r (f a * b) (g a * c)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.prod_hom_rel`：prod_hom_rel (l : List ι) {r : M -> N -> Prop} {f : ι
 -> M} {g : ι -> N} (h₁ : r 1 1) (h₂ : forall ⦃i a b⦄, r a b -> r (f i * a) (g i
 * b)) …
-/
theorem prod_hom_rel (s : Multiset ι) {r : M → N → Prop} {f : ι → M} {g : ι → N}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
/-
**Multiset.prod_map_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_one : prod (m.map fun _ => (1 : M)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem prod_map_one : prod (m.map fun _ => (1 : M)) = 1 := by
  rw [map_const', prod_replicate, one_pow]

@[to_additive]
/-
**Multiset.prod_induction** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_induction (p : M -> Prop) (s : Multiset M) (p_mul : forall a b, p a -
> p b -> p (a * b)) (p_one : p 1) (p_s : forall a in s, p a) : p s.prod
参数：p : M -> Prop；s : Multiset M；p_mul : forall a b, p a -> p b -> p (a * b)；p_on
e : p 1；p_s : forall a in s, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_eq_foldr`：prod_eq_foldr (s : Multiset M) : prod s = foldr 
(· * ·) 1 s
· 使用定理 `Multiset.foldr_induction`：foldr_induction (f : α -> α -> α) [LeftCommuta
tive f] (x : α) (p : α -> Prop) (s : Multiset α) (p_f : forall a b, p a -> p b -
> p (f a b)) (…
-/
theorem prod_induction (p : M → Prop) (s : Multiset M) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]
/-
**Multiset.prod_induction_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_induction_nonempty (p : M -> Prop) (p_mul : forall a b, p a -> p b ->
 p (a * b)) (hs : s != ∅) (p_s : forall a in s, p a) : p s.prod
参数：p : M -> Prop；p_mul : forall a b, p a -> p b -> p (a * b)；hs : s != ∅；p_s : f
orall a in s, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
theorem prod_induction_nonempty (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

end CommMonoid

end Multiset

