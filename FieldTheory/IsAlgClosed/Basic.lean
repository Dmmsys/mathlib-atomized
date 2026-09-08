/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Localization.Integral

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `IsAlgClosed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
  polynomial in `k` splits.

- `IsAlgClosure R K` is the typeclass saying `K` is an algebraic closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  algebraically closed and algebraic over `R`

- `IsAlgClosed.lift` is a map from an algebraic extension `L` of `R`, into any algebraically
  closed extension of `R`.

- `IsAlgClosure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## Tags

algebraic closure, algebraically closed

## Main results

- `IsAlgClosure.of_splits`: if `K / k` is algebraic, and every monic irreducible polynomial over
  `k` splits in `K`, then `K` is algebraically closed (in fact an algebraic closure of `k`).
  For the stronger fact that only requires every such polynomial has a root in `K`,
  see `IsAlgClosure.of_exists_root`.

  Reference: <https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosure.pdf>, Theorem 2

-/

@[expose] public section

universe u v w

open Module Polynomial

variable (k : Type u) [Field k]

/-- An algebraically closed field is one where every polynomial splits. Equivalently, all
non-constant polynomials have a root. See `IsAlgClosed.exists_root` and
`IsAlgClosed.of_exists_root`. -/
@[stacks 09GR "The definition of `IsAlgClosed` in mathlib is 09GR (4)"]
/-
**IsAlgClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u) → [Field k] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebraically closed field is one where every polynomial splits. Equivalently
, all
non-constant polynomials have a root. See `IsAlgClosed.exists_root` and
`IsAlgClosed.of_exists_root`.
-/
class IsAlgClosed : Prop where
  splits : ∀ p : k[X], p.Splits

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed. -/
/-
**IsAlgClosed.splits_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgClosed.splits_domain {k K : Type*} [Field k] [IsAlgClosed k] [Field K
] {f : k ->+* K} (p : k[X]) : (p.map f).Splits
参数：p : k[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraic
ally closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K}
    (p : k[X]) : (p.map f).Splits :=
  (IsAlgClosed.splits p).map f

namespace IsAlgClosed

variable {k}

/--
If `k` is algebraically closed, then every nonconstant polynomial has a root.
-/
@[stacks 09GR "(4) ⟹ (3)"]
/-
**IsAlgClosed.exists_root** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree != 0) : exists x, Is
Root p x
参数：p : k[X]；hp : p.degree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
If `k` is algebraically closed, then every nonconstant polynomial has a root.
-/
theorem exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) : ∃ x, IsRoot p x :=
  (IsAlgClosed.splits p).exists_eval_eq_zero hp
/-
**IsAlgClosed.exists_pow_nat_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : Nat} (hn : 0 < n) : exists 
z, z ^ n = x
参数：x : k；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x := by
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz
/-
**IsAlgClosed.exists_eq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：exists_eq_mul_self [IsAlgClosed k] (x : k) : exists z, x = z * z
参数：x : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsAlgClosed.exists_pow_nat_eq`：exists_pow_nat_eq [IsAlgClosed k] (x : k)
 {n : Nat} (hn : 0 < n) : exists z, z ^ n = x
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩
/-
**IsAlgClosed.roots_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p = Polynomia
l.C (p.coeff 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
-/
theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz
/-
**IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsA
lgClosed`。
形式化陈述：roots_eq_zero_iff_natDegree_eq_zero [IsAlgClosed k] {p : k[X]} : p.roots =
 0 ↔ p.natDegree = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.roots_eq_zero_iff`：roots_eq_zero_iff [IsAlgClosed k] {p : k[
X]} : p.roots = 0 ↔ p = Polynomial.C (p.coeff 0)
· 使用定理 `Polynomial.eq_C_coeff_zero_iff_natDegree_eq_zero`：eq_C_coeff_zero_iff_na
tDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0
-/
theorem roots_eq_zero_iff_natDegree_eq_zero [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p.natDegree = 0 :=
  roots_eq_zero_iff.trans eq_C_coeff_zero_iff_natDegree_eq_zero
/-
**IsAlgClosed.roots_eq_zero_iff_degree_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgCl
osed`。
形式化陈述：roots_eq_zero_iff_degree_nonpos [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔
 p.degree <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero`：roots_eq_zero_iff_natDe
gree_eq_zero [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p.natDegree = 0
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
-/
theorem roots_eq_zero_iff_degree_nonpos [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p.degree ≤ 0 :=
  roots_eq_zero_iff_natDegree_eq_zero.trans natDegree_eq_zero_iff_degree_le_zero
/-
**IsAlgClosed.card_roots_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：card_roots_eq_natDegree [IsAlgClosed k] {p : k[X]} : p.roots.card = p.natD
egree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.exists_prod_multiset_X_sub_C_mul`：exists_prod_multiset_X_sub_
C_mul (p : R[X]) : exists q, (p.roots.map fun a => X - C a).prod * q = p ∧ Multi
set.card p.roots + q.natDegree = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero`：roots_eq_zero_iff_natDe
gree_eq_zero [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p.natDegree = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_roots_eq_natDegree [IsAlgClosed k] {p : k[X]} : p.roots.card = p.natDegree := by
  have ⟨_, _, hdeg, hroots⟩ := exists_prod_multiset_X_sub_C_mul p
  simp [← hdeg, roots_eq_zero_iff_natDegree_eq_zero.mp hroots]
/-
**IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero** 是 Mathlib 中的
一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [Semirin
g A] [Field B] [IsAlgClosed B] {f : A ->+* B} {p : A[X]} (hf : f p.leadingCoeff 
!= 0) : (p.map f).roots.card = p.natDegree
参数：hf : f p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.card_roots_eq_natDegree`：card_roots_eq_natDegree [IsAlgClose
d k] {p : k[X]} : p.roots.card = p.natDegree
· 使用定理 `Polynomial.natDegree_map_of_leadingCoeff_ne_zero`：natDegree_map_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : natDegree (p.map
 f) = natDegree p
-/
theorem card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] {f : A →+* B} {p : A[X]} (hf : f p.leadingCoeff ≠ 0) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_of_leadingCoeff_ne_zero _ hf ▸ card_roots_eq_natDegree
/-
**IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff** 是 Mathlib 中的一
个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：card_roots_map_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [Semiring
 A] [Field B] [IsAlgClosed B] (f : A ->+* B) {p : A[X]} (h : IsUnit p.leadingCoe
ff) : (p.map f).roots.card = p.natDegree
参数：f : A ->+* B；h : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.card_roots_eq_natDegree`：card_roots_eq_natDegree [IsAlgClose
d k] {p : k[X]} : p.roots.card = p.natDegree
· 使用定理 `Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff`：natDegree_map_eq_of_
isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp : IsUnit p.leadingCoeff) :
 (p.map f).natDegree = p.natDegree
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem card_roots_map_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] (f : A →+* B) {p : A[X]} (h : IsUnit p.leadingCoeff) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_eq_of_isUnit_leadingCoeff f h ▸ card_roots_eq_natDegree
/-
**IsAlgClosed.card_roots_map_eq_natDegree_of_injective** 是 Mathlib 中的一个定理，位于命名空间
 `IsAlgClosed`。
形式化陈述：card_roots_map_eq_natDegree_of_injective {A B : Type*} [Semiring A] [Field
 B] [IsAlgClosed B] {f : A ->+* B} (p : A[X]) (hf : Function.Injective f) : (p.m
ap f).roots.card = p.natDegree
参数：p : A[X]；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.card_roots_eq_natDegree`：card_roots_eq_natDegree [IsAlgClose
d k] {p : k[X]} : p.roots.card = p.natDegree
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
-/
theorem card_roots_map_eq_natDegree_of_injective {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] {f : A →+* B} (p : A[X]) (hf : Function.Injective f) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_eq_of_injective hf _ ▸ card_roots_eq_natDegree
/-
**IsAlgClosed.card_roots_map_eq_natDegree_from_simpleRing** 是 Mathlib 中的一个定理，位于命
名空间 `IsAlgClosed`。
形式化陈述：card_roots_map_eq_natDegree_from_simpleRing {A B : Type*} [Ring A] [IsSimp
leRing A] [Field B] [IsAlgClosed B] (f : A ->+* B) (p : A[X]) : (p.map f).roots.
card = p.natDegree
参数：f : A ->+* B；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.card_roots_eq_natDegree`：card_roots_eq_natDegree [IsAlgClose
d k] {p : k[X]} : p.roots.card = p.natDegree
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem card_roots_map_eq_natDegree_from_simpleRing {A B : Type*} [Ring A] [IsSimpleRing A]
    [Field B] [IsAlgClosed B] (f : A →+* B) (p : A[X]) : (p.map f).roots.card = p.natDegree :=
  natDegree_map f ▸ card_roots_eq_natDegree
/-
**IsAlgClosed.card_aroots_eq_natDegree_of_leadingCoeff_ne_zero** 是 Mathlib 中的一个定
理，位于命名空间 `IsAlgClosed`。
形式化陈述：card_aroots_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [CommRing A
] [Field B] [IsAlgClosed B] [Algebra A B] {p : A[X]} (hf : algebraMap A B p.lead
ingCoeff != 0) : (p.aroots B).card = p.natDegree
参数：hf : algebraMap A B p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero`：card_ro
ots_map_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [Semiring A] [Field B
] [IsAlgClosed B] {f : A ->+* B} {p : A[X]} (hf : f p…
-/
theorem card_aroots_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [CommRing A] [Field B]
    [IsAlgClosed B] [Algebra A B] {p : A[X]} (hf : algebraMap A B p.leadingCoeff ≠ 0) :
    (p.aroots B).card = p.natDegree :=
  card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hf
/-
**IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff** 是 Mathlib 中的一个定理
，位于命名空间 `IsAlgClosed`。
形式化陈述：card_aroots_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [CommRing A]
 [Field B] [IsAlgClosed B] [Algebra A B] {p : A[X]} (h : IsUnit p.leadingCoeff) 
: (p.aroots B).card = p.natDegree
参数：h : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff`：card_roo
ts_map_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [Semiring A] [Field B] 
[IsAlgClosed B] (f : A ->+* B) {p : A[X]} (h : IsUni…
-/
theorem card_aroots_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [CommRing A] [Field B]
    [IsAlgClosed B] [Algebra A B] {p : A[X]} (h : IsUnit p.leadingCoeff) :
    (p.aroots B).card = p.natDegree :=
  card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ h
/-
**IsAlgClosed.card_aroots_eq_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：card_aroots_eq_natDegree {A B : Type*} [CommRing A] [Field B] [IsAlgClosed
 B] [Algebra A B] [FaithfulSMul A B] {p : A[X]} : (p.aroots B).card = p.natDegre
e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.card_roots_map_eq_natDegree_of_injective`：card_roots_map_eq_
natDegree_of_injective {A B : Type*} [Semiring A] [Field B] [IsAlgClosed B] {f :
 A ->+* B} (p : A[X]) (hf : Function.Injec…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem card_aroots_eq_natDegree {A B : Type*} [CommRing A] [Field B] [IsAlgClosed B] [Algebra A B]
    [FaithfulSMul A B] {p : A[X]} : (p.aroots B).card = p.natDegree :=
  card_roots_map_eq_natDegree_of_injective _ <| FaithfulSMul.algebraMap_injective _ _
/-
**IsAlgClosed.dvd_iff_roots_le_roots** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：dvd_iff_roots_le_roots [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (hq : q 
!= 0) : p ∣ q ↔ p.roots <= q.roots
参数：hp : p != 0；hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.dvd_iff_roots_le_roots`：∀ {R : Type u_1} [inst : Field
 R] {f g : Polynomial R}, f.Splits → f ≠ 0 → g ≠ 0 → (f ∣ g ↔ f.roots ≤ g.roots)
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
-/
theorem dvd_iff_roots_le_roots [IsAlgClosed k] {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    p ∣ q ↔ p.roots ≤ q.roots :=
  Splits.dvd_iff_roots_le_roots (splits _) hp hq
/-
**IsAlgClosed.associated_iff_roots_eq_roots** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClos
ed`。
形式化陈述：associated_iff_roots_eq_roots [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (
hq : q != 0) : Associated p q ↔ p.roots = q.roots
参数：hp : p != 0；hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Associated.roots_eq`：∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDoma
in R] {p q : Polynomial R}, Associated p q → p.roots = q.roots
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAlgClosed.dvd_iff_roots_le_roots`：dvd_iff_roots_le_roots [IsAlgClosed 
k] {p q : k[X]} (hp : p != 0) (hq : q != 0) : p ∣ q ↔ p.roots <= q.roots
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem associated_iff_roots_eq_roots [IsAlgClosed k] {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    Associated p q ↔ p.roots = q.roots :=
  ⟨Associated.roots_eq, fun h ↦ associated_of_dvd_dvd
    (dvd_iff_roots_le_roots hp hq |>.mpr <| le_of_eq h)
    (dvd_iff_roots_le_roots hq hp |>.mpr <| le_of_eq h.symm)⟩
/-
**IsAlgClosed.exists_eval** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eval₂_eq_zero_of_injective {R : Type*} [Semiring R] [IsAlgClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩
/-
**IsAlgClosed.exists_eval** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eval₂_eq_zero {R : Type*} [Ring R] [IsSimpleRing R] [IsAlgClosed k] (f : R →+* k)
    (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective _ f.injective _ hp

variable (k)
/-
**IsAlgClosed.exists_aeval_eq_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsAlg
Closed`。
形式化陈述：exists_aeval_eq_zero_of_injective {R : Type*} [CommSemiring R] [IsAlgClose
d k] [Algebra R k] (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp :
 p.degree != 0) : exists x : k, aeval x p = 0
参数：hinj : Function.Injective (algebraMap R k)；p : R[X]；hp : p.degree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_eval₂_eq_zero_of_injective`：exists_eval₂_eq_zero_of_i
njective {R : Type*} [Semiring R] [IsAlgClosed k] (f : R ->+* k) (hf : Function.
Injective f) (p : R[X]) (hp : p.deg…
-/
theorem exists_aeval_eq_zero_of_injective {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree ≠ 0) :
    ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp
/-
**IsAlgClosed.exists_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：exists_aeval_eq_zero {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra
 R k] [FaithfulSMul R k] (p : R[X]) (hp : p.degree != 0) : exists x : k, p.aeval
 x = 0
参数：p : R[X]；hp : p.degree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_aeval_eq_zero_of_injective`：exists_aeval_eq_zero_of_i
njective {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k] (hinj : Func
tion.Injective (algebraMap R k)) (p…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem exists_aeval_eq_zero {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
    [FaithfulSMul R k] (p : R[X]) (hp : p.degree ≠ 0) : ∃ x : k, p.aeval x = 0 :=
  exists_aeval_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) _ hp

/--
If every nonconstant polynomial over `k` has a root, then `k` is algebraically closed.
-/
@[stacks 09GR "(3) ⟹ (4)"]
/-
**IsAlgClosed.of_exists_root** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：of_exists_root (H : forall p : k[X], p.Monic -> Irreducible p -> exists x,
 p.eval x = 0) : IsAlgClosed k
参数：H : forall p : k[X], p.Monic -> Irreducible p -> exists x, p.eval x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.irreducible_mul_leadingCoeff_inv`：irreducible_mul_leadingCoef
f_inv {p : K[X]} : Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Polynomial.Splits.of_degree_eq_one`：∀ {R : Type u_1} [inst : DivisionSem
iring R] {f : Polynomial R}, f.degree = 1 → f.Splits
· 使用引理 `Polynomial.degree_eq_one_of_irreducible_of_root`：degree_eq_one_of_irredu
cible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) : degree p = 1
· 使用定理 `IsUnit.splits`：∀ {R : Type u_1} [inst : Semiring R] [NoZeroDivisors R] {
f : Polynomial R}, IsUnit f → f.Splits
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u

--- 原说明 ---
If every nonconstant polynomial over `k` has a root, then `k` is algebraically c
losed.
-/
theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → ∃ x, p.eval x = 0) :
    IsAlgClosed k := by
  replace H (p : k[X]) (hp : Irreducible p) : ∃ x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp)
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p ↦ ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf ↦ ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)
/-
**IsAlgClosed.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：of_ringEquiv (k' : Type u) [Field k'] (e : k ≃+* k') [IsAlgClosed k] : IsA
lgClosed k'
参数：k' : Type u；e : k ≃+* k'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
（共 42 条，此处仅展示前 30 条）
-/
theorem of_ringEquiv (k' : Type u) [Field k'] (e : k ≃+* k')
    [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/--
If `k` is algebraically closed, then every irreducible polynomial over `k` is linear.
-/
@[stacks 09GR "(4) ⟹ (2)"]
/-
**IsAlgClosed.degree_eq_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClose
d`。
形式化陈述：degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible 
p) : p.degree = 1
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.degree_eq_one_of_irreducible`：∀ {R : Type u_1} [inst :
 Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree = 1
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
If `k` is algebraically closed, then every irreducible polynomial over `k` is li
near.
-/
theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  (IsAlgClosed.splits p).degree_eq_one_of_irreducible hp
/-
**IsAlgClosed.algebraMap_bijective_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsAl
gClosed`。
形式化陈述：algebraMap_bijective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDom
ain K] [hk : IsAlgClosed k] [Algebra k K] [Algebra.IsIntegral k K] : Function.Bi
jective (algebraMap k K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsAlgClosed.degree_eq_one_of_irreducible`：degree_eq_one_of_irreducible [
IsAlgClosed k] {p : k[X]} (hp : Irreducible p) : p.degree = 1
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_add`：aeval_add : aeval x (p + q) = aeval x p + aeval x 
q
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.eq_X_add_C_of_degree_eq_one`：eq_X_add_C_of_degree_eq_one (h :
 degree p = 1) : p = C p.leadingCoeff * X + C (p.coeff 0)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem algebraMap_bijective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] [Algebra.IsIntegral k K] :
    Function.Bijective (algebraMap k K) := by
  refine ⟨RingHom.injective _, fun x ↦ ⟨-(minpoly k x).coeff 0, ?_⟩⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm
/-
**IsAlgClosed.ringHom_bijective_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgCl
osed`。
形式化陈述：ringHom_bijective_of_isIntegral {k K : Type*} [Field k] [CommRing K] [IsDo
main K] [IsAlgClosed k] (f : k ->+* K) (hf : f.IsIntegral) : Function.Bijective 
f
参数：f : k ->+* K；hf : f.IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
-/
theorem ringHom_bijective_of_isIntegral {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    [IsAlgClosed k] (f : k →+* K) (hf : f.IsIntegral) : Function.Bijective f :=
  let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_bijective_of_isIntegral

end IsAlgClosed

/-- If `k` is algebraically closed, `K / k` is a field extension, `L / k` is an intermediate field
which is algebraic, then `L` is equal to `k`. A corollary of
`IsAlgClosed.algebraMap_surjective_of_isAlgebraic`. -/
@[stacks 09GQ "The result is the definition of algebraically closedness in Stacks Project. \
This statement is 09GR (4) ⟹ (1)."]
/-
**IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Fiel
d k] [Field K] [IsAlgClosed k] [Algebra k K] (L : IntermediateField k K) [Algebr
a.IsAlgebraic k L] : L = ⊥
参数：L : IntermediateField k K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsAlgClosed.algebraMap_bijective_of_isIntegral`：algebraMap_bijective_of_
isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K] [hk : IsAlgClosed k] [A
lgebra k K] [Algebra.IsIntegral k K]…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] (L : IntermediateField k K) [Algebra.IsAlgebraic k L] :
    L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩
/-
**Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K : Type v) [Field 
K] [IsAlgClosed K] [Algebra k K] (p q : k[X]) : IsCoprime p q ↔ forall a : K, ae
val a p != 0 ∨ aeval a q != 0
参数：K : Type v；p q : k[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.aeval_ne_zero_of_isCoprime`：aeval_ne_zero_of_isCoprime {R} [C
ommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S] {p q : R[X]} (h : IsCop
rime p q) (s : S) : aeval s…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `isCoprime_of_dvd`：isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0)
) (H : forall z in nonunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Polynomial.degree_pos_of_ne_zero_of_nonunit`：degree_pos_of_ne_zero_of_no
nunit (hp0 : p != 0) (hp : ¬IsUnit p) : 0 < degree p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
（共 35 条，此处仅展示前 30 条）
-/
lemma Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K : Type v) [Field K] [IsAlgClosed K]
    [Algebra k K] (p q : k[X]) : IsCoprime p q ↔ ∀ a : K, aeval a p ≠ 0 ∨ aeval a q ≠ 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hu h0 => ?_⟩
  · replace h := h 0
    contrapose! h
    rw [h.left, h.right, map_zero, and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
    obtain ⟨a, ha : _ = _⟩ := IsAlgClosed.exists_root (x.map <| algebraMap k K) <| by
      simpa only [degree_map] using (ne_of_lt <| degree_pos_of_ne_zero_of_nonunit h0 hu).symm
    exact not_and_or.mpr (h a) (by simp_rw [map_mul, ← eval_map_algebraMap, ha, zero_mul, true_and])

/-- Typeclass for an extension being an algebraic closure. -/
@[stacks 09GS]
/-
**IsAlgClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (K : Type v) → [inst : CommRing R] → [inst_1 : Field K] →
 [inst_2 : Algebra R K] → [Module.IsTorsionFree R K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for an extension being an algebraic closure.
-/
class IsAlgClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [IsTorsionFree R K] : Prop where
  isAlgClosed : IsAlgClosed K
  isAlgebraic : Algebra.IsAlgebraic R K

attribute [instance] IsAlgClosure.isAlgebraic
/-
**isAlgClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] : IsAlgClosure k K ↔
 IsAlgClosed K ∧ Algebra.IsAlgebraic k K
参数：K : Type v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsAlgClosure.isAlgClosed`：∀ (R : Type u) {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `IsAlgClosure.isAlgebraic`：∀ {R : Type u} {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.isAlgebraic
  splits' _ := (IsAlgClosure.isAlgClosed R).splits _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : Algebra.IsSeparable R K :=
  ⟨fun _ => (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable⟩
/-
**IsAlgClosed.instIsAlgClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsAlgClosed.instIsAlgClosure (F : Type*) [Field F] [IsAlgClosed F] : IsAlg
Closure F F where isAlgClosed
参数：F : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance IsAlgClosed.instIsAlgClosure (F : Type*) [Field F] [IsAlgClosed F] : IsAlgClosure F F where
  isAlgClosed := ‹_›
  isAlgebraic := .of_finite F F
/-
**IsAlgClosure.of_splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgClosure.of_splits {R K} [CommRing R] [IsDomain R] [Field K] [Algebra 
R K] [Algebra.IsIntegral R K] [IsTorsionFree R K] (h : forall p : R[X], p.Monic 
-> Irreducible p -> (p.map (algebraMap R K)).Splits) : IsAlgClosure R K where is
Algebraic
参数：h : forall p : R[X], p.Monic -> Irreducible p -> (p.map (algebraMap R K)).Spl
its。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `Irreducible.exists_dvd_monic_irreducible_of_isIntegral`：Irreducible.exis
ts_dvd_monic_irreducible_of_isIntegral {K L : Type*} [CommRing K] [IsDomain K] [
Field L] [Algebra K L] [Algebra.IsIntegral K…
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem IsAlgClosure.of_splits {R K} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [Algebra.IsIntegral R K] [IsTorsionFree R K]
    (h : ∀ p : R[X], p.Monic → Irreducible p → (p.map (algebraMap R K)).Splits) :
    IsAlgClosure R K where
  isAlgebraic := inferInstance
  isAlgClosed := .of_exists_root _ fun _p _ p_irred ↦
    have ⟨g, monic, irred, dvd⟩ := p_irred.exists_dvd_monic_irreducible_of_isIntegral (K := R)
    ((h g monic irred).of_dvd (map_monic_ne_zero monic) dvd).exists_eval_eq_zero <|
      degree_ne_of_natDegree_ne p_irred.natDegree_pos.ne'

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M]

/-
**IsAlgClosed.eval_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosed`。
形式化陈述：eval_surjective {p : M[X]} (hp : p.natDegree != 0) : Function.Surjective p
.eval
参数：hp : p.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_sub_C`：degree_sub_C (hp : 0 < degree p) : degree (p - 
C a) = degree p
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem eval_surjective {p : M[X]} (hp : p.natDegree ≠ 0) : Function.Surjective p.eval :=
  fun x ↦ by
    rw [← Nat.pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at hp
    have ⟨y, hy⟩ := (IsAlgClosed.splits (p - C x)).exists_eval_eq_zero <| by
      simpa only [degree_sub_C hp] using hp.ne'
    exact ⟨y, by simpa [eval_sub, sub_eq_zero] using hy⟩

/-- If E/L/K is a tower of field extensions with E/L algebraic, and if M is an algebraically
  closed extension of K, then any embedding of L/K into M/K extends to an embedding of E/K.
  Known as the extension lemma in https://math.stackexchange.com/a/687914. -/
/-
**IsAlgClosed.surjective_domRestrict_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `I
sAlgClosed`。
形式化陈述：surjective_domRestrict_of_isAlgebraic {E : Type*} [Field E] [Algebra K E] 
[Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic L E] : Function.Surject
ive fun φ : E ->ₐ[K] M => φ.domRestrict L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_splits'`：exists_algHom_of_splits' (hK
 : forall s : E, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) : exis
ts φ : E ->ₐ[F] K, φ.domRestrict…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
If E/L/K is a tower of field extensions with E/L algebraic, and if M is an algeb
raically
  closed extension of K, then any embedding of L/K into M/K extends to an embedd
ing of E/K.
  Known as the extension lemma in https://math.stackexchange.com/a/687914.
-/
theorem surjective_domRestrict_of_isAlgebraic {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.domRestrict L :=
  fun f ↦ IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s ↦ ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isAlgebraic := surjective_domRestrict_of_isAlgebraic

variable [Algebra.IsAlgebraic K L] (K L M)

/-- Less general version of `lift`. -/
/-
**IsAlgClosed.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Less general version of `lift`.
-/
private noncomputable def liftAux : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsIntegral.isIntegral x, splits _⟩)
    (IntermediateField.adjoin_univ K L)

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M]
  [IsTorsionFree R S] [IsTorsionFree R M] [Algebra.IsAlgebraic R S]

variable {M}
/-
**IsAlgClosed.FractionRing.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance FractionRing.isAlgebraic :
    letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  let : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  let : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  exact ⟨fun _ ↦ (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
    (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
@[stacks 09GU, no_expose]
/-
**IsAlgClosed.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosed`。
形式化陈述：lift : S ->ₐ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R.
-/
noncomputable def lift : S →ₐ[R] M := by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S →ₐ[FractionRing R] M := liftAux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)
/-
**IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `
IsAlgClosed`。
形式化陈述：nonempty_algEquiv_or_of_finrank_eq_two {F F' : Type*} (E : Type*) [Field F
] [Field F'] [Field E] [Algebra F F'] [Algebra F E] [Algebra.IsAlgebraic F E] [I
sAlgClosed F'] (h : Module.finrank F F' = 2) : Nonempty (E ≃ₐ[F] F) ∨ Nonempty (
E ≃ₐ[F] F')
参数：E : Type*；h : Module.finrank F F' = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Subalgebra.isSimpleOrder_of_finrank`：Subalgebra.isSimpleOrder_of_finrank
 (hr : finrank F E = 2) : IsSimpleOrder (Subalgebra F E)
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem nonempty_algEquiv_or_of_finrank_eq_two {F F' : Type*} (E : Type*)
    [Field F] [Field F'] [Field E] [Algebra F F'] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed F'] (h : Module.finrank F F' = 2) :
    Nonempty (E ≃ₐ[F] F) ∨ Nonempty (E ≃ₐ[F] F') := by
  have emb : E →ₐ[F] F' := lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]
/-
**IsAlgClosed.** 是 Mathlib 中的一个实例，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100) perfectRing (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
  PerfectRing.ofSurjective k p fun _ => IsAlgClosed.exists_pow_nat_eq _ <| NeZero.pos p
/-
**IsAlgClosed.** 是 Mathlib 中的一个实例，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100) perfectField [IsAlgClosed k] : PerfectField k := by
  obtain _ | ⟨p, _, _⟩ := CharP.exists' k
  exacts [.ofCharZero, PerfectRing.toPerfectField k p]

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
/-
**IsAlgClosed.** 是 Mathlib 中的一个实例，位于命名空间 `IsAlgClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K 
= n`
-/
instance (priority := 500) {K : Type*} [Field K] [IsAlgClosed K] : Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K
  set f := (X : K[X]) ^ (n + 1) - 1
  have hfsep : Separable f := separable_X_pow_sub_C 1 (by simp [n]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    rw [card_rootSet_eq_natDegree hfsep (IsAlgClosed.splits_domain _)]
    unfold f
    rw [← C_1, natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

end IsAlgClosed

namespace IsAlgClosure

section

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra R M] [IsTorsionFree R M] [IsAlgClosure R M]
variable [Algebra R L] [IsTorsionFree R L] [IsAlgClosure R L]

attribute [local instance] IsAlgClosure.isAlgClosed in
/-- A (random) isomorphism between two algebraic closures of `R`. -/
@[stacks 09GV]
/-
**IsAlgClosure.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosure`。
形式化陈述：equiv : L ≃ₐ[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosure.isAlgClosed`：∀ (R : Type u) {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `IsAlgClosure.isAlgebraic`：∀ {R : Type u} {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…

--- 原说明 ---
A (random) isomorphism between two algebraic closures of `R`.
-/
noncomputable def equiv : L ≃ₐ[R] M :=
  AlgEquiv.ofBijective _ (IsAlgClosure.isAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : L →ₐ[R] M)
    (IsAlgClosed.lift : M →ₐ[R] L)).1

end

variable (K : Type*) (J : Type*) (R : Type u) (S : Type*) (L : Type v) (M : Type w)
  [Field K] [Field J] [CommRing R] [CommRing S] [Field L] [Field M]
  [Algebra R M] [IsTorsionFree R M] [IsAlgClosure R M] [Algebra K M] [IsAlgClosure K M]
  [Algebra S L] [IsTorsionFree S L] [IsAlgClosure S L]

section EquivOfAlgebraic

variable [Algebra R S] [Algebra R L] [IsScalarTower R S L]
variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

/-- If `J` is an algebraic extension of `K` and `L` is an algebraic closure of `J`, then it is
  also an algebraic closure of `K`. -/
/-
**IsAlgClosure.ofAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosure`。
形式化陈述：ofAlgebraic [Algebra.IsAlgebraic K J] : IsAlgClosure K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsAlgClosure.isAlgClosed`：∀ (R : Type u) {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsAlgClosure.isAlgebraic`：∀ {R : Type u} {K : Type v} {inst : CommRing R
} {inst_1 : Field K} {inst_2 : Algebra R K}   {inst_3 : Module.IsTorsionFree R K
} [self : IsAl…

--- 原说明 ---
If `J` is an algebraic extension of `K` and `L` is an algebraic closure of `J`, 
then it is
  also an algebraic closure of `K`.
-/
theorem ofAlgebraic [Algebra.IsAlgebraic K J] : IsAlgClosure K L :=
  ⟨IsAlgClosure.isAlgClosed J, .trans K J L⟩

/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
/-
**IsAlgClosure.equivOfAlgebraic'** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosure`。
形式化陈述：equivOfAlgebraic' [IsDomain R] [IsDomain S] [IsTorsionFree R S] [Algebra.I
sAlgebraic R L] : L ≃ₐ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (random) isomorphism between an algebraic closure of `R` and an algebraic clos
ure of
  an algebraic extension of `R`
-/
noncomputable def equivOfAlgebraic' [IsDomain R] [IsDomain S] [IsTorsionFree R S]
    [Algebra.IsAlgebraic R L] : L ≃ₐ[R] M := by
  have : IsTorsionFree R L := .trans_faithfulSMul R S L
  have : IsAlgClosure R L :=
    { isAlgClosed := IsAlgClosure.isAlgClosed S
      isAlgebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _

/-- A (random) isomorphism between an algebraic closure of `K` and an algebraic closure
  of an algebraic extension of `K` -/
/-
**IsAlgClosure.equivOfAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosure`。
形式化陈述：equivOfAlgebraic [Algebra.IsAlgebraic K J] : L ≃ₐ[K] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (random) isomorphism between an algebraic closure of `K` and an algebraic clos
ure
  of an algebraic extension of `K`
-/
noncomputable def equivOfAlgebraic [Algebra.IsAlgebraic K J] : L ≃ₐ[K] M :=
  have := Algebra.IsAlgebraic.trans K J L
  equivOfAlgebraic' K J _ _

end EquivOfAlgebraic

section EquivOfEquiv

variable {R S} [IsDomain R] [IsDomain S]

/-- Used in the definition of `equivOfEquiv` -/
/-
**IsAlgClosure.equivOfEquivAux** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosure`。
形式化陈述：equivOfEquivAux (hSR : S ≃+* R) : { e : L ≃+* M // e.toRingHom.comp (algeb
raMap S L) = (algebraMap R M).comp hSR.toRingHom }
参数：hSR : S ≃+* R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Used in the definition of `equivOfEquiv`
-/
noncomputable def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } := by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L := .of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.isAlgebraic.extendScalars
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  change equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]

/-- Algebraic closure of isomorphic fields are isomorphic -/
/-
**IsAlgClosure.equivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsAlgClosure`。
形式化陈述：equivOfEquiv (hSR : S ≃+* R) : L ≃+* M
参数：hSR : S ≃+* R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebraic closure of isomorphic fields are isomorphic
-/
noncomputable def equivOfEquiv (hSR : S ≃+* R) : L ≃+* M :=
  equivOfEquivAux L M hSR

@[simp]
/-
**IsAlgClosure.equivOfEquiv_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClos
ure`。
形式化陈述：equivOfEquiv_comp_algebraMap (hSR : S ≃+* R) : (↑(equivOfEquiv L M hSR) : 
L ->+* M).comp (algebraMap S L) = (algebraMap R M).comp hSR
参数：hSR : S ≃+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem equivOfEquiv_comp_algebraMap (hSR : S ≃+* R) :
    (↑(equivOfEquiv L M hSR) : L →+* M).comp (algebraMap S L) = (algebraMap R M).comp hSR :=
  (equivOfEquivAux L M hSR).2

@[simp]
/-
**IsAlgClosure.equivOfEquiv_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClosure`。
形式化陈述：equivOfEquiv_algebraMap (hSR : S ≃+* R) (s : S) : equivOfEquiv L M hSR (al
gebraMap S L s) = algebraMap R M (hSR s)
参数：hSR : S ≃+* R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `IsAlgClosure.equivOfEquiv_comp_algebraMap`：equivOfEquiv_comp_algebraMap 
(hSR : S ≃+* R) : (↑(equivOfEquiv L M hSR) : L ->+* M).comp (algebraMap S L) = (
algebraMap R M).comp hSR
-/
theorem equivOfEquiv_algebraMap (hSR : S ≃+* R) (s : S) :
    equivOfEquiv L M hSR (algebraMap S L s) = algebraMap R M (hSR s) :=
  RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s

@[simp]
/-
**IsAlgClosure.equivOfEquiv_symm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgClos
ure`。
形式化陈述：equivOfEquiv_symm_algebraMap (hSR : S ≃+* R) (r : R) : (equivOfEquiv L M h
SR).symm (algebraMap R M r) = algebraMap S L (hSR.symm r)
参数：hSR : S ≃+* R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `IsAlgClosure.equivOfEquiv_algebraMap`：equivOfEquiv_algebraMap (hSR : S ≃
+* R) (s : S) : equivOfEquiv L M hSR (algebraMap S L s) = algebraMap R M (hSR s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivOfEquiv_symm_algebraMap (hSR : S ≃+* R) (r : R) :
    (equivOfEquiv L M hSR).symm (algebraMap R M r) = algebraMap S L (hSR.symm r) :=
  (equivOfEquiv L M hSR).injective (by simp)

@[simp]
/-
**IsAlgClosure.equivOfEquiv_symm_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsAl
gClosure`。
形式化陈述：equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) : ((equivOfEquiv L M hSR
).symm : M ->+* L).comp (algebraMap R M) = (algebraMap S L).comp hSR.symm
参数：hSR : S ≃+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `IsAlgClosure.equivOfEquiv_symm_algebraMap`：equivOfEquiv_symm_algebraMap 
(hSR : S ≃+* R) (r : R) : (equivOfEquiv L M hSR).symm (algebraMap R M r) = algeb
raMap S L (hSR.symm r)
-/
theorem equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) :
    ((equivOfEquiv L M hSR).symm : M →+* L).comp (algebraMap R M) =
      (algebraMap S L).comp hSR.symm :=
  RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)

end EquivOfEquiv

end IsAlgClosure

section Algebra.IsAlgebraic

variable {F K : Type*} (A : Type*) [Field F] [Field K] [Field A] [Algebra F K] [Algebra F A]
  [Algebra.IsAlgebraic F K]

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebraic extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`. -/
/-
**Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly [IsAlgClosed A] (x : K) 
: (Set.range fun ψ : K ->ₐ[F] A => ψ x) = (minpoly F x).rootSet A
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits`：Algebra.IsA
lgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} (L : Type*) [Fiel
d F] [Field K] [Field L] [Algebra F L] [Algebra F…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebrai
c extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A`
 are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`.
-/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly [IsAlgClosed A] (x : K) :
    (Set.range fun ψ : K →ₐ[F] A ↦ ψ x) = (minpoly F x).rootSet A :=
  range_eval_eq_rootSet_minpoly_of_splits A (fun _ ↦ IsAlgClosed.splits _) x

/-- All `F`-embeddings of a field `K` into another field `A` factor through any intermediate
field of `A/F` in which the minimal polynomial of elements of `K` splits. -/
@[simps]
/-
**IntermediateField.algHomEquivAlgHomOfSplits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IntermediateField.algHomEquivAlgHomOfSplits (L : IntermediateField F A) (h
L : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) : (K ->ₐ[F] L) ≃ 
(K ->ₐ[F] A) where toFun
参数：L : IntermediateField F A；hL : forall x : K, ((minpoly F x).map (algebraMap F
 L)).Splits。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All `F`-embeddings of a field `K` into another field `A` factor through any inte
rmediate
field of `A/F` in which the minimal polynomial of elements of `K` splits.
-/
def IntermediateField.algHomEquivAlgHomOfSplits (L : IntermediateField F A)
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    (K →ₐ[F] L) ≃ (K →ₐ[F] A) where
  toFun := L.val.comp
  invFun f := f.codRestrict _ fun x ↦
    ((Algebra.IsIntegral.isIntegral x).map f).mem_intermediateField_of_minpoly_splits <| by
      rw [minpoly.algHom_eq f f.injective]; exact hL x
/-
**IntermediateField.algHomEquivAlgHomOfSplits_apply_apply** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：IntermediateField.algHomEquivAlgHomOfSplits_apply_apply (L : IntermediateF
ield F A) (hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) (f : 
K ->ₐ[F] L) (x : K) : algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x
)
参数：L : IntermediateField F A；hL : forall x : K, ((minpoly F x).map (algebraMap F
 L)).Splits；f : K ->ₐ[F] L；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IntermediateField.algHomEquivAlgHomOfSplits_apply_apply (L : IntermediateField F A)
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) (f : K →ₐ[F] L) (x : K) :
    algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

/-- All `F`-embeddings of a field `K` into another field `A` factor through any subextension
of `A/F` in which the minimal polynomial of elements of `K` splits. -/
/-
**Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (L : Type*) [Field L] [Algeb
ra F L] [Algebra L A] [IsScalarTower F L A] (hL : forall x : K, ((minpoly F x).m
ap (algebraMap F L)).Splits) : (K ->ₐ[F] L) ≃ (K ->ₐ[F] A)
参数：L : Type*；hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
All `F`-embeddings of a field `K` into another field `A` factor through any sube
xtension
of `A/F` in which the minimal polynomial of elements of `K` splits.
-/
noncomputable def Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    (K →ₐ[F] L) ≃ (K →ₐ[F] A) :=
  (AlgEquiv.refl.arrowCongr (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L A))).trans <|
    IntermediateField.algHomEquivAlgHomOfSplits A (IsScalarTower.toAlgHom F L A).fieldRange
    fun x ↦ Splits.of_algHom (hL x) (AlgHom.rangeRestrict _)
/-
**Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply (L : Type*) [Fie
ld L] [Algebra F L] [Algebra L A] [IsScalarTower F L A] (hL : forall x : K, ((mi
npoly F x).map (algebraMap F L)).Splits) (f : K ->ₐ[F] L) (x : K) : Algebra.IsAl
gebraic.algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x)
参数：L : Type*；hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits；f : 
K ->ₐ[F] L；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) (f : K →ₐ[F] L) (x : K) :
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

end Algebra.IsAlgebraic

/-- Over an algebraically closed field of characteristic zero a necessary and sufficient condition
for the set of roots of a nonzero polynomial `f` to be a subset of the set of roots of `g` is that
`f` divides `f.derivative * g`. Over an integral domain, this is a sufficient but not necessary
condition. See `isRoot_of_isRoot_of_dvd_derivative_mul` -/
/-
**Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul {K : Type*} [Field K] [
IsAlgClosed K] [CharZero K] {f g : K[X]} (hf0 : f != 0) : (forall x, IsRoot f x 
-> IsRoot g x) ↔ f ∣ f.derivative * g
参数：hf0 : f != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.eq_C_of_derivative_eq_zero`：eq_C_of_derivative_eq_zero (h : d
erivative p = 0) : p = C (p.coeff 0)
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsAlgClosed.dvd_iff_roots_le_roots`：dvd_iff_roots_le_roots [IsAlgClosed 
k] {p q : k[X]} (hp : p != 0) (hq : q != 0) : p ∣ q ↔ p.roots <= q.roots
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.rootMultiplicity_mul`：rootMultiplicity_mul {p q : R[X]} {x : 
R} (hpq : p * q != 0) : rootMultiplicity x (p * q) = rootMultiplicity x p + root
Multiplicity x q
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.rootMultiplicity_pos`：rootMultiplicity_pos {p : R[X]} (hp : p
 != 0) {x : R} : 0 < rootMultiplicity x p ↔ IsRoot p x
· 使用定理 `Polynomial.derivative_rootMultiplicity_of_root`：derivative_rootMultiplic
ity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) : p.derivative.ro
otMultiplicity t = p.rootMultiplicit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Over an algebraically closed field of characteristic zero a necessary and suffic
ient condition
for the set of roots of a nonzero polynomial `f` to be a subset of the set of ro
ots of `g` is that
`f` divides `f.derivative * g`. Over an integral domain, this is a sufficient bu
t not necessary
condition. See `isRoot_of_isRoot_of_dvd_derivative_mul`
-/
theorem Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] {f g : K[X]} (hf0 : f ≠ 0) :
    (∀ x, IsRoot f x → IsRoot g x) ↔ f ∣ f.derivative * g := by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg : f.derivative * g ≠ 0 := mul_ne_zero hdf0 hg0
  classical rw [IsAlgClosed.dvd_iff_roots_le_roots hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ ≤ rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]
