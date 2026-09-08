/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in ordered rings

This file contains the results concerning the interaction of finset big operators with ordered
rings.

In particular, this file contains the standard form of the Cauchy-Schwarz inequality, as well as
some of its immediate consequences.
-/

public section

variable {ι R S : Type*}

namespace Finset

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}

/-
**Finset.sum_sq_le_sq_sum_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_sq_le_sq_sum_of_nonneg (hf : forall i in s, 0 <= f i) : ∑ i in s, f i 
^ 2 <= (∑ i in s, f i) ^ 2
参数：hf : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
-/
lemma sum_sq_le_sq_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

end OrderedSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι → R} {s t : Finset ι}

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `OrderedCommSemiring`. -/
/-
**Finset.prod_add_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_add_prod_le {i : ι} {f g h : ι -> R} (hi : i in s) (h2i : g i + h i <
= f i) (hgf : forall j in s, j != i -> g j <= f j) (hhf : forall j in s, j != i 
-> h j <= f j) (hg : forall i in s, 0 <= g i) (hh : forall i in s, 0 <= h i) : (
(∏ i in s, g i) + ∏ i in s, h i) <= ∏ i in s, f i
参数：hi : i in s；h2i : g i + h i <= f i；hgf : forall j in s, j != i -> g j <= f j；
hhf : forall j in s, j != i -> h j <= f j；hg : forall i in s, 0 <= g i；hh : fora
ll i in s, 0 <= h i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at leas
t the
  sum of the products of `g` and `h`. This is the version for `OrderedCommSemiri
ng`.
-/
lemma prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji ↦ le_trans (hg j hj) (hgf j hj hji)
/-
**Finset.le_prod_of_submultiplicative_on_pred_of_nonneg** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] 
(f : M -> R) (p : M -> Prop) (h_nonneg : forall a, 0 <= f a) (h_one : f 1 <= 1) 
(h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b,
 p a -> p b -> p (a * b)) (s : Finset ι) (g : ι -> M) (hps : forall a, a in s ->
 p (g a)) : f (∏ i in s, g i) <= ∏ i in s, f (g i)
参数：f : M -> R；p : M -> Prop；h_nonneg : forall a, 0 <= f a；h_one : f 1 <= 1；h_mul
 : forall a b, p a -> p b -> f (a * b) <= f a * f b；hp_mul : forall a b, p a -> 
p b -> p (a * b)；s : Finset ι；g : ι -> M；hps : forall a, a in s -> p (g a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg`：Multiset.le_pro
d_of_submultiplicative_on_pred_of_nonneg (f : α -> β) (p : α -> Prop) (h0 : fora
ll a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : f…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
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
-/
theorem le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] (f : M → R)
    (p : M → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Finset ι) (g : ι → M) (hps : ∀ a, a ∈ s → p (g a)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi
/-
**Finset.le_prod_of_submultiplicative_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finse
t`。
形式化陈述：le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M] (f : M -
> R) (h_nonneg : forall a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : forall x y : M,
 f (x * y) <= f x * f y) (s : Finset ι) (g : ι -> M) : f (∏ i in s, g i) <= ∏ i 
in s, f (g i)
参数：f : M -> R；h_nonneg : forall a, 0 <= f a；h_one : f 1 <= 1；h_mul : forall x y 
: M, f (x * y) <= f x * f y；s : Finset ι；g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_prod_of_submultiplicative_of_nonneg`：Multiset.le_prod_of_sub
multiplicative_of_nonneg (f : α -> β) (h0 : forall a, 0 <= f a) (h_one : f 1 <= 
1) (h_mul : forall a b, f (a * b) <= …
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
-/
theorem le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M]
    (f : M → R) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

end OrderedCommSemiring

/-
**Finset.sum_mul_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing
 R] [ExistsAddOfLE R] (s : Finset ι) (f : ι -> R) : ∑ i in s, f i * f i = 0 ↔ fo
rall i in s, f i = 0
参数：s : Finset ι；f : ι -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) : ∑ i ∈ s, f i * f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _]
  simp
/-
**Finset.abs_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset 
ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι → R) :
    |∏ x ∈ s, f x| = ∏ x ∈ s, |f x| :=
  map_prod absHom _ _

@[simp, norm_cast]
/-
**Finset.PNat.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset.PNat`。
形式化陈述：∀ {ι : Type u_4} (f : ι → ℕ+) (s : Finset ι), ↑(∏ i ∈ s, f i) = ∏ i ∈ s, ↑
(f i)
参数：f : ι → ℕ+；s : Finset ι；∏ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem PNat.coe_prod {ι : Type*} (f : ι → ℕ+) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : ℕ) :=
  map_prod PNat.coeMonoidHom _ _

section CanonicallyOrderedAdd
variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  {f g h : ι → R} {s : Finset ι} {i : ι}

/-- Note that the name is to match `CanonicallyOrderedAdd.mul_pos`. -/
/-
**Finset._root_.CanonicallyOrderedAdd.prod_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the name is to match `CanonicallyOrderedAdd.mul_pos`.
-/
@[simp] lemma _root_.CanonicallyOrderedAdd.prod_pos [NoZeroDivisors R] [Nontrivial R] :
    0 < ∏ i ∈ s, f i ↔ (∀ i ∈ s, (0 : R) < f i) :=
  CanonicallyOrderedAdd.multiset_prod_pos.trans Multiset.forall_mem_map_iff

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `CanonicallyOrderedAdd`.
-/
/-
**Finset.prod_add_prod_le'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_add_prod_le' (hi : i in s) (h2i : g i + h i <= f i) (hgf : forall j i
n s, j != i -> g j <= f j) (hhf : forall j in s, j != i -> h j <= f j) : ((∏ i i
n s, g i) + ∏ i in s, h i) <= ∏ i in s, f i
参数：hi : i in s；h2i : g i + h i <= f i；hgf : forall j in s, j != i -> g j <= f j；
hhf : forall j in s, j != i -> h j <= f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MulLeftMono.toPosMulMono`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero
 α] [inst_2 : Preorder α] [MulLeftMono α], PosMulMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at leas
t the
  sum of the products of `g` and `h`. This is the version for `CanonicallyOrdere
dAdd`.
-/
lemma prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  grw [← h2i, right_distrib]
  gcongr with j hj j hj <;> simp_all

end CanonicallyOrderedAdd

/-! ### Named inequalities -/

/-- **Cauchy-Schwarz inequality** for finsets.

This is written in terms of sequences `f`, `g`, and `r`, where `r` is usually a stand-in for
`√(f i * g i)`. See `sum_mul_sq_le_sq_mul_sq` for the more usual form in terms of squared
sequences. -/
/-
**Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_sq_le_sum_mul_sum_of_sq_le_mul [CommSemiring R] [LinearOrder R] [IsStr
ictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) {r f g : ι -> R} (hf : forall
 i in s, 0 <= f i) (hg : forall i in s, 0 <= g i) (ht : forall i in s, r i ^ 2 <
= f i * g i) : (∑ i in s, r i) ^ 2 <= (∑ i in s, f i) * ∑ i in s, g i
参数：s : Finset ι；hf : forall i in s, 0 <= f i；hg : forall i in s, 0 <= g i；ht : f
orall i in s, r i ^ 2 <= f i * g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_of_mul_le_mul_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : 
Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLE α],   a * b ≤ a * c →
 0 < a → b ≤ c
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets.

This is written in terms of sequences `f`, `g`, and `r`, where `r` is usually a 
stand-in for
`√(f i * g i)`. See `sum_mul_sq_le_sq_mul_sq` for the more usual form in terms o
f squared
sequences.
-/
lemma sum_sq_le_sum_mul_sum_of_sq_le_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (ht : ∀ i ∈ s, r i ^ 2 ≤ f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  obtain h | h := (sum_nonneg hg).eq_or_lt'
  · have ht' : ∑ i ∈ s, r i = 0 := sum_eq_zero fun i hi ↦ by
      simpa [(sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
    rw [h, ht']
    simp
  · refine le_of_mul_le_mul_of_pos_left
      (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
    calc
      _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
          simp_rw [mul_assoc, ← mul_sum, ← sum_mul]; ring
      _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
          gcongr with i hi
          have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 ≤
              (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by
            grw [mul_mul_mul_comm, ← mul_pow, mul_assoc, mul_pow, ht i hi]
            exact sq_nonneg _
          refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_le_mul
            (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
          repeat rw [mul_assoc]
      _ = _ := by simp_rw [sum_add_distrib, ← sum_mul]; ring

@[deprecated sum_sq_le_sum_mul_sum_of_sq_le_mul (since := "2026-05-12")]
/-
**Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStr
ictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) {r f g : ι -> R} (hf : forall
 i in s, 0 <= f i) (hg : forall i in s, 0 <= g i) (ht : forall i in s, r i ^ 2 =
 f i * g i) : (∑ i in s, r i) ^ 2 <= (∑ i in s, f i) * ∑ i in s, g i
参数：s : Finset ι；hf : forall i in s, 0 <= f i；hg : forall i in s, 0 <= g i；ht : f
orall i in s, r i ^ 2 = f i * g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`：sum_sq_le_sum_mul_sum_of_sq_l
e_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
 (s : Finset ι) {r f g : ι -> R…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg (fun i hi => (ht i hi).le)

/-- **Cauchy-Schwarz inequality** for finsets, squared version. -/
/-
**Finset.sum_mul_sq_le_sq_mul_sq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedR
ing R] [ExistsAddOfLE R] (s : Finset ι) (f g : ι -> R) : (∑ i in s, f i * g i) ^
 2 <= (∑ i in s, f i ^ 2) * ∑ i in s, g i ^ 2
参数：s : Finset ι；f g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`：sum_sq_le_sum_mul_sum_of_sq_l
e_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
 (s : Finset ι) {r f g : ι -> R…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets, squared version.
-/
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ (mul_pow ..).le)

/-- **Sedrakyan's lemma**, aka **Titu's lemma** or **Engel's form**.

This is a specialization of the Cauchy-Schwarz inequality with the sequences `f n / √(g n)` and
`√(g n)`, though here it is proven without relying on square roots. -/
/-
**Finset.sq_sum_div_le_sum_sq_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRin
g R] [ExistsAddOfLE R] (s : Finset ι) (f : ι -> R) {g : ι -> R} (hg : forall i i
n s, 0 < g i) : (∑ i in s, f i) ^ 2 / ∑ i in s, g i <= ∑ i in s, f i ^ 2 / g i
参数：s : Finset ι；f : ι -> R；hg : forall i in s, 0 < g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用引理 `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`：sum_sq_le_sum_mul_sum_of_sq_l
e_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
 (s : Finset ι) {r f g : ι -> R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
**Sedrakyan's lemma**, aka **Titu's lemma** or **Engel's form**.

This is a specialization of the Cauchy-Schwarz inequality with the sequences `f 
n / √(g n)` and
`√(g n)`, though here it is proven without relying on square roots.
-/
theorem sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) {g : ι → R} (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by
  have hg' : ∀ i ∈ s, 0 ≤ g i := fun i hi ↦ (hg i hi).le
  have H : ∀ i ∈ s, 0 ≤ f i ^ 2 / g i := fun i hi ↦ div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (sum_sq_le_sum_mul_sum_of_sq_le_mul _ H hg' fun i hi ↦ ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

end Finset

/-! ### Absolute values -/

section AbsoluteValue

/-
**AbsoluteValue.sum_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AbsoluteValue.sum_le [Semiring R] [Semiring S] [PartialOrder S] [IsOrdered
Ring S] (abv : AbsoluteValue R S) (s : Finset ι) (f : ι -> R) : abv (∑ i in s, f
 i) <= ∑ i in s, abv (f i)
参数：abv : AbsoluteValue R S；s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
-/
lemma AbsoluteValue.sum_le [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _).le abv.add_le _ _
/-
**IsAbsoluteValue.abv_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAbsoluteValue.abv_sum [Semiring R] [Semiring S] [PartialOrder S] [IsOrde
redRing S] (abv : R -> S) [IsAbsoluteValue abv] (f : ι -> R) (s : Finset ι) : ab
v (∑ i in s, f i) <= ∑ i in s, abv (f i)
参数：abv : R -> S；f : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AbsoluteValue.sum_le`：AbsoluteValue.sum_le [Semiring R] [Semiring S] [Pa
rtialOrder S] [IsOrderedRing S] (abv : AbsoluteValue R S) (s : Finset ι) (f : ι 
-> R) : ab…
-/
lemma IsAbsoluteValue.abv_sum [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  map_prod abv f s
/-
**IsAbsoluteValue.map_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [CommRing S] [Lin
earOrder S] [IsStrictOrderedRing S] (abv : R -> S) [IsAbsoluteValue abv] (f : ι 
-> R) (s : Finset ι) : abv (∏ i in s, f i) = ∏ i in s, abv (f i)
参数：abv : R -> S；f : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_prod`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [
inst : CommSemiring R] [Nontrivial R] [inst_2 : CommRing S]   [inst_3 : LinearOr
der S] [IsSt…
-/
lemma IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

end AbsoluteValue

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

alias ⟨_, prod_ne_zero⟩ := prod_ne_zero_iff

attribute [local instance] monadLiftOptionMetaM in
/-- The `positivity` extension which proves that `∏ i ∈ s, f i` is nonnegative if `f` is, and
positive if each `f i` is.

TODO: The following example does not work
```
example (s : Finset ℕ) (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ s.prod f := by positivity
```
because `compareHyp` can't look for assumptions behind binders.
-/
@[positivity Finset.prod _ _]
meta def evalFinsetProd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@Finset.prod $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := Expr.betaRev f #[i]
    let rbody ← core zα pα body
    let _instαmon ← synthInstanceQ q(CommMonoidWithZero $α)
    -- Try to show that the product is positive
    let p_pos : Option Q(0 < $e) ← do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulStrictMono $α) | pure none
      let .some _instαnontriv ← trySynthInstanceQ q(Nontrivial $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      pure <| some q(prod_pos fun i _ ↦ $pr i)
    if let some p_pos := p_pos then return .positive p_pos
    -- Try to show that the product is nonnegative
    let p_nonneg : Option Q(0 ≤ $e) ← do
      let some pbody := rbody.toNonneg
        | pure none -- Fail if the body is not provably nonnegative
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulMono $α) | pure none
      assertInstancesCommute
      pure <| some q(prod_nonneg fun i _ ↦ $pr i)
    if let some p_nonneg := p_nonneg then return .nonnegative p_nonneg
    -- Fall back to showing that the product is nonzero
    let pbody ← rbody.toNonzero
    let pr : Q(∀ i, $f i ≠ 0) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
    -- TODO(https://github.com/leanprover-community/quote4/issues/38):
    -- We must name the following, else `assertInstancesCommute` loops.
    let _instαnontriv ← synthInstanceQ q(Nontrivial $α)
    let _instαnozerodiv ← synthInstanceQ q(NoZeroDivisors $α)
    assertInstancesCommute
    return .nonzero q(prod_ne_zero fun i _ ↦ $pr i)

end Mathlib.Meta.Positivity

