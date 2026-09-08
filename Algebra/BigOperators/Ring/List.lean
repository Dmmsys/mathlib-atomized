/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Big operators on a list in rings

This file contains the results concerning the interaction of list big operators with rings.
-/

public section

open MulOpposite List

variable {ι κ M M₀ R : Type*}

namespace Commute
variable [NonUnitalNonAssocSemiring R]

/-
**Commute.list_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：list_sum_right (a : R) (l : List R) (h : forall b in l, Commute a b) : Com
mute a l.sum
参数：a : R；l : List R；h : forall b in l, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.zero_right`：zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `Commute.add_right`：add_right [Distrib R] {a b c : R} : Commute a b -> Co
mmute a c -> Commute a (b + c)
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
lemma list_sum_right (a : R) (l : List R) (h : ∀ b ∈ l, Commute a b) : Commute a l.sum := by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj ↦ h _ <| mem_cons_of_mem _ hj)
/-
**Commute.list_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：list_sum_left (b : R) (l : List R) (h : forall a in l, Commute a b) : Comm
ute l.sum b
参数：b : R；l : List R；h : forall a in l, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `Commute.list_sum_right`：list_sum_right (a : R) (l : List R) (h : forall 
b in l, Commute a b) : Commute a l.sum
-/
lemma list_sum_left (b : R) (l : List R) (h : ∀ a ∈ l, Commute a b) : Commute l.sum b :=
  ((Commute.list_sum_right _ _) fun _x hx ↦ (h _ hx).symm).symm

end Commute

namespace List
section HasDistribNeg
variable [Monoid M] [HasDistribNeg M]

@[simp]
/-
**List.prod_map_neg** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_neg (l : List M) : (l.map Neg.neg).prod = (-1) ^ l.length * l.pro
d
参数：l : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Commute.neg_one_left`：neg_one_left (a : R) : Commute (-1) a
-/
lemma prod_map_neg (l : List M) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

end HasDistribNeg

section MonoidWithZero
variable [MonoidWithZero M₀] {l : List M₀}

/-- If zero is an element of a list `l`, then `List.prod l = 0`. If the domain is a nontrivial
monoid with zero with no zero divisors, then this implication becomes an `iff`, see
`List.prod_eq_zero_iff`. -/
/-
**List.prod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] {l : List M₀}, 0 ∈ l → l.prod
 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If zero is an element of a list `l`, then `List.prod l = 0`. If the domain is a 
nontrivial
monoid with zero with no zero divisors, then this implication becomes an `iff`, 
see
`List.prod_eq_zero_iff`.
-/
lemma prod_eq_zero : ∀ {l : List M₀}, (0 : M₀) ∈ l → l.prod = 0
  -- |  absurd h (not_mem_nil _)
  | a :: l, h => by
    rw [prod_cons]
    rcases mem_cons.1 h with ha | hl
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (prod_eq_zero hl)]

variable [Nontrivial M₀] [NoZeroDivisors M₀]

/-- Product of elements of a list `l` equals zero if and only if `0 ∈ l`. See also
`List.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
/-
**List.prod_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] [Nontrivial M₀] [NoZeroDiviso
rs M₀] {l : List M₀}, l.prod = 0 ↔ 0 ∈ l
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of elements of a list `l` equals zero if and only if `0 ∈ l`. See also
`List.prod_eq_zero` for an implication that needs weaker typeclass assumptions.
-/
@[simp] lemma prod_eq_zero_iff : ∀ {l : List M₀}, l.prod = 0 ↔ (0 : M₀) ∈ l
  | [] => by simp
  | a :: l => by rw [prod_cons, mul_eq_zero, prod_eq_zero_iff, mem_cons, eq_comm]
/-
**List.prod_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod != 0
参数：hL : (0 : M₀) ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.prod_eq_zero_iff`：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] [Non
trivial M₀] [NoZeroDivisors M₀] {l : List M₀}, l.prod = 0 ↔ 0 ∈ l
-/
lemma prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod ≠ 0 := mt prod_eq_zero_iff.1 hL

end MonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] (l : List ι) (f : ι → R) (r : R)

/-
**List.sum_map_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sum_map_mul_left : (l.map fun b => r * f b).sum = r * (l.map f).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sum_map_hom`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst :
 AddMonoid M] [inst_1 : AddMonoid N] (L : List ι) (f : ι → M)   {G : Type u_8} [
inst_2…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma sum_map_mul_left : (l.map fun b ↦ r * f b).sum = r * (l.map f).sum :=
  sum_map_hom l f <| AddMonoidHom.mulLeft r
/-
**List.sum_map_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sum_map_mul_right : (l.map fun b => f b * r).sum = (l.map f).sum * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sum_map_hom`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst :
 AddMonoid M] [inst_1 : AddMonoid N] (L : List ι) (f : ι → M)   {G : Type u_8} [
inst_2…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma sum_map_mul_right : (l.map fun b ↦ f b * r).sum = (l.map f).sum * r :=
  sum_map_hom l f <| AddMonoidHom.mulRight r

end NonUnitalNonAssocSemiring

/-
**List.dvd_sum** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：dvd_sum [NonUnitalSemiring R] {a} {l : List R} (h : forall x in l, a ∣ x) 
: a ∣ l.sum
参数：h : forall x in l, a ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
lemma dvd_sum [NonUnitalSemiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum := by
  induction l with
  | nil => exact dvd_zero _
  | cons x l ih =>
    rw [List.sum_cons]
    exact dvd_add (h _ mem_cons_self) (ih fun x hx ↦ h x (mem_cons_of_mem _ hx))
/-
**List.sum_zipWith_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {ι : Type u_1} {κ : Type u_2} {R : Type u_5} [inst : NonUnitalNonAssocSe
miring R] (f : ι → κ → R) (a : R)   (l₁ : List ι) (l₂ : List κ), (List.zipWith (
fun i j => a * f i j) l₁ l₂).sum = a * (List.zipWith f l₁ l₂).sum
参数：f : ι → κ → R；a : R；l₁ : List ι；l₂ : List κ；List.zipWith (fun i j => a * f i 
j) l₁ l₂；List.zipWith f l₁ l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sum_zipWith_distrib_left [NonUnitalNonAssocSemiring R] (f : ι → κ → R) (a : R) :
    ∀ (l₁ : List ι) (l₂ : List κ),
      (zipWith (fun i j ↦ a * f i j) l₁ l₂).sum = a * (zipWith f l₁ l₂).sum
  | [], _ => by simp
  | _, [] => by simp
  | i :: l₁, j :: l₂ => by simp [sum_zipWith_distrib_left, mul_add]

end List

