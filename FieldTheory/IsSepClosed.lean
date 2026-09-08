/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Separably Closed Field

In this file we define the typeclass for separably closed fields and separable closures,
and prove some of their properties.

## Main Definitions

- `IsSepClosed k` is the typeclass saying `k` is a separably closed field, i.e. every separable
  polynomial in `k` splits.

- `IsSepClosure k K` is the typeclass saying `K` is a separable closure of `k`, where `k` is a
  field. This means that `K` is separably closed and separable over `k`.

- `IsSepClosed.lift` is a map from a separable extension `L` of `K`, into any separably
  closed extension `M` of `K`.

- `IsSepClosure.equiv` is a proof that any two separable closures of the
  same field are isomorphic.

- `IsSepClosure.isAlgClosure_of_perfectField`, `IsSepClosure.of_isAlgClosure_of_perfectField`:
  if `k` is a perfect field, then its separable closure coincides with its algebraic closure.

## Tags

separable closure, separably closed

## Related

- `separableClosure`: maximal separable subextension of `K/k`, consisting of all elements of `K`
  which are separable over `k`.

- `separableClosure.isSepClosure`: if `K` is a separably closed field containing `k`, then the
  maximal separable subextension of `K/k` is a separable closure of `k`.

- In particular, a separable closure (`SeparableClosure`) exists.

- `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`: an algebraic extension of a separably
  closed field is purely inseparable.

-/

@[expose] public section

universe u v w

open Polynomial

variable (k : Type u) [Field k] (K : Type v) [Field K]

/-- Typeclass for separably closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsSepClosed.splits_codomain` and `IsSepClosed.splits_domain`.
-/
/-
**IsSepClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u) → [Field k] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for separably closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsSepClosed.splits_codomain` and `IsSepClosed.splits_domain`.
-/
class IsSepClosed : Prop where
  splits_of_separable : ∀ p : k[X], p.Separable → p.Splits

/-- An algebraically closed field is also separably closed. -/
/-
**IsSepClosed.of_isAlgClosed** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsSepClosed.of_isAlgClosed [IsAlgClosed k] : IsSepClosed k
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
An algebraically closed field is also separably closed.
-/
instance IsSepClosed.of_isAlgClosed [IsAlgClosed k] : IsSepClosed k :=
  ⟨fun p _ ↦ IsAlgClosed.splits p⟩

variable {k} {K}

/-- Every separable polynomial splits in the field extension `f : k →+* K` if `K` is
separably closed.

See also `IsSepClosed.splits_domain` for the case where `k` is separably closed.
-/
/-
**IsSepClosed.splits_codomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSepClosed.splits_codomain [IsSepClosed K] {f : k ->+* K} (p : k[X]) (h :
 p.Separable) : (p.map f).Splits
参数：p : k[X]；h : p.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosed.splits_of_separable`：∀ {k : Type u} {inst : Field k} [self :
 IsSepClosed k] (p : Polynomial k), p.Separable → p.Splits
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…

--- 原说明 ---
Every separable polynomial splits in the field extension `f : k →+* K` if `K` is
separably closed.

See also `IsSepClosed.splits_domain` for the case where `k` is separably closed.
-/
theorem IsSepClosed.splits_codomain [IsSepClosed K] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : (p.map f).Splits :=
  IsSepClosed.splits_of_separable (p.map f) (Separable.map h)

/-- Every separable polynomial splits in the field extension `f : k →+* K` if `k` is
separably closed.

See also `IsSepClosed.splits_codomain` for the case where `k` is separably closed.
-/
/-
**IsSepClosed.splits_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSepClosed.splits_domain [IsSepClosed k] {f : k ->+* K} (p : k[X]) (h : p
.Separable) : (p.map f).Splits
参数：p : k[X]；h : p.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `IsSepClosed.splits_of_separable`：∀ {k : Type u} {inst : Field k} [self :
 IsSepClosed k] (p : Polynomial k), p.Separable → p.Splits

--- 原说明 ---
Every separable polynomial splits in the field extension `f : k →+* K` if `k` is
separably closed.

See also `IsSepClosed.splits_codomain` for the case where `k` is separably close
d.
-/
theorem IsSepClosed.splits_domain [IsSepClosed k] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : (p.map f).Splits :=
  (IsSepClosed.splits_of_separable _ h).map f

namespace IsSepClosed

/-
**IsSepClosed.exists_root** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：exists_root [IsSepClosed k] (p : k[X]) (hp : p.degree != 0) (hsep : p.Sepa
rable) : exists x, IsRoot p x
参数：p : k[X]；hp : p.degree != 0；hsep : p.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `IsSepClosed.splits_of_separable`：∀ {k : Type u} {inst : Field k} [self :
 IsSepClosed k] (p : Polynomial k), p.Separable → p.Splits
-/
theorem exists_root [IsSepClosed k] (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, IsRoot p x :=
  (IsSepClosed.splits_of_separable p hsep).exists_eval_eq_zero hp

/-- If `n ≥ 2` equals zero in a separably closed field `k`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`. -/
/-
**IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空
间 `IsSepClosed`。
形式化陈述：exists_root_C_mul_X_pow_add_C_mul_X_add_C [IsSepClosed k] {n : Nat} (a b c
 : k) (hn : (n : k) = 0) (hn' : 2 <= n) (hb : b != 0) : exists x, a * x ^ n + b 
* x + c = 0
参数：a b c : k；hn : (n : k) = 0；hn' : 2 <= n；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C`：separable_C_mul_X_po
w_add_C_mul_X_add_C {n : Nat} (a b c : R) (hn : (n : R) = 0) (hb : IsUnit b) : (
C a * X ^ n + C b * X + C c).Separable
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `IsSepClosed.exists_root`：exists_root [IsSepClosed k] (p : k[X]) (hp : p.
degree != 0) (hsep : p.Separable) : exists x, IsRoot p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x

--- 原说明 ---
If `n ≥ 2` equals zero in a separably closed field `k`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`.
-/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C
    [IsSepClosed k] {n : ℕ} (a b c : k) (hn : (n : k) = 0) (hn' : 2 ≤ n) (hb : b ≠ 0) :
    ∃ x, a * x ^ n + b * x + c = 0 := by
  let f : k[X] := C a * X ^ n + C b * X + C c
  -- Specify `n := 0` below, otherwise Lean unfolds `0` to `Zero.zero`.
  have hdeg : f.degree ≠ 0 := degree_ne_of_natDegree_ne (n := 0) <| by
    have : C 0 * X ^ n + C b * X = 0 * X ^ n + C b * X := by grind
    by_cases ha : a = 0
    · grind [zero_add]
    · grind [natDegree_add_eq_left_of_natDegree_lt]
  have hsep : f.Separable := separable_C_mul_X_pow_add_C_mul_X_add_C a b c hn hb.isUnit
  obtain ⟨x, hx⟩ := exists_root f hdeg hsep
  exact ⟨x, by simpa [f] using hx⟩

/-- If a separably closed field `k` is of characteristic `p`, `n ≥ 2` is such that `p ∣ n`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`. -/
/-
**IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'** 是 Mathlib 中的一个定理，位于命名
空间 `IsSepClosed`。
形式化陈述：exists_root_C_mul_X_pow_add_C_mul_X_add_C' [IsSepClosed k] (p n : Nat) (a 
b c : k) [CharP k p] (hn : p ∣ n) (hn' : 2 <= n) (hb : b != 0) : exists x, a * x
 ^ n + b * x + c = 0
参数：p n : Nat；a b c : k；hn : p ∣ n；hn' : 2 <= n；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C`：exists_root_C_mul
_X_pow_add_C_mul_X_add_C [IsSepClosed k] {n : Nat} (a b c : k) (hn : (n : k) = 0
) (hn' : 2 <= n) (hb : b != 0) : exists x, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x

--- 原说明 ---
If a separably closed field `k` is of characteristic `p`, `n ≥ 2` is such that `
p ∣ n`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`.
-/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C'
    [IsSepClosed k] (p n : ℕ) (a b c : k) [CharP k p] (hn : p ∣ n) (hn' : 2 ≤ n) (hb : b ≠ 0) :
    ∃ x, a * x ^ n + b * x + c = 0 :=
  exists_root_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff k p n).2 hn) hn' hb

variable (k) in
/-- A separably closed perfect field is also algebraically closed. -/
/-
**IsSepClosed.** 是 Mathlib 中的一个实例，位于命名空间 `IsSepClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A separably closed perfect field is also algebraically closed.
-/
instance (priority := 100) isAlgClosed_of_perfectField [IsSepClosed k] [PerfectField k] :
    IsAlgClosed k :=
  IsAlgClosed.of_exists_root k fun p _ h ↦ exists_root p ((degree_pos_of_irreducible h).ne')
    (PerfectField.separable_of_irreducible h)
/-
**IsSepClosed.exists_pow_nat_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：exists_pow_nat_eq [IsSepClosed k] (x : k) (n : Nat) [hn : NeZero (n : k)] 
: exists z, z ^ n = x
参数：x : k；n : Nat；n : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsSepClosed.exists_root`：exists_root [IsSepClosed k] (p : k[X]) (hp : p.
degree != 0) (hsep : p.Separable) : exists x, IsRoot p x
· 使用定理 `Polynomial.separable_X_pow_sub_C`：separable_X_pow_sub_C {n : Nat} (a : F
) (hn : (n : F) != 0) (ha : a != 0) : Separable (X ^ n - C a)
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
theorem exists_pow_nat_eq [IsSepClosed k] (x : k) (n : ℕ) [hn : NeZero (n : k)] :
    ∃ z, z ^ n = x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn'.ne']⟩
  · obtain ⟨z, hz⟩ := exists_root _ this <| separable_X_pow_sub_C x hn.out hx
    use z
    simpa [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def, sub_eq_zero] using hz
/-
**IsSepClosed.exists_eq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：exists_eq_mul_self [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)] : exists 
z, x = z * z
参数：x : k；2 : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsSepClosed.exists_pow_nat_eq`：exists_pow_nat_eq [IsSepClosed k] (x : k)
 (n : Nat) [hn : NeZero (n : k)] : exists z, z ^ n = x
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem exists_eq_mul_self [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)] : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩
/-
**IsSepClosed.roots_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) : p.root
s = 0 ↔ p = Polynomial.C (p.coeff 0)
参数：hsep : p.Separable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `IsSepClosed.exists_root`：exists_root [IsSepClosed k] (p : k[X]) (hp : p.
degree != 0) (hsep : p.Separable) : exists x, IsRoot p x
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
theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz
/-
**IsSepClosed.exists_eval** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eval₂_eq_zero_of_injective {k : Type*} [CommSemiring k] [IsSepClosed K] (f : k →+* K)
    (hf : Function.Injective f) (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩
/-
**IsSepClosed.exists_eval** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eval₂_eq_zero {k : Type*} [CommRing k] [IsSimpleRing k] [IsSepClosed K] (f : k →+* K)
    (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective _ f.injective _ hp hsep

variable (K)
/-
**IsSepClosed.exists_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：exists_aeval_eq_zero {k : Type*} [CommSemiring k] [IsSepClosed K] [Algebra
 k K] [FaithfulSMul k K] (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable) : 
exists x : K, p.aeval x = 0
参数：p : k[X]；hp : p.degree != 0；hsep : p.Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosed.exists_eval₂_eq_zero_of_injective`：exists_eval₂_eq_zero_of_i
njective {k : Type*} [CommSemiring k] [IsSepClosed K] (f : k ->+* K) (hf : Funct
ion.Injective f) (p : k[X]) (hp : p…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem exists_aeval_eq_zero {k : Type*} [CommSemiring k] [IsSepClosed K] [Algebra k K]
    [FaithfulSMul k K] (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x : K, p.aeval x = 0 :=
  exists_eval₂_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) p hp hsep

variable (k) {K}
/-
**IsSepClosed.of_exists_root** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：of_exists_root (H : forall p : k[X], p.Monic -> Irreducible p -> Separable
 p -> exists x, p.eval x = 0) : IsSepClosed k
参数：H : forall p : k[X], p.Monic -> Irreducible p -> Separable p -> exists x, p.e
val x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.irreducible_mul_leadingCoeff_inv`：irreducible_mul_leadingCoef
f_inv {p : K[X]} : Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p
· 使用定理 `Polynomial.Separable.mul_unit`：∀ {R : Type u} [inst : CommSemiring R] {f
 g : Polynomial R}, f.Separable → IsUnit g → (f * g).Separable
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.instIsLocalHomRingHomC`：∀ {R : Type u_1} [inst : CommRing R],
 IsLocalHom Polynomial.C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_factors`：dvd_of_mem_factors {p a : 
α} (h : p in factors a) : p ∣ a
· 使用定理 `Polynomial.Splits.of_degree_eq_one`：∀ {R : Type u_1} [inst : DivisionSem
iring R] {f : Polynomial R}, f.degree = 1 → f.Splits
（共 33 条，此处仅展示前 30 条）
-/
theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → Separable p → ∃ x, p.eval x = 0) :
    IsSepClosed k := by
  replace H (p : k[X]) (hp : Irreducible p) (hs : Separable p) : ∃ x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp) (hs.mul_unit (by aesop))
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p hp ↦ ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf ↦ ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h (hp.of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hf))
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)
/-
**IsSepClosed.degree_eq_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClose
d`。
形式化陈述：degree_eq_one_of_irreducible [IsSepClosed k] {p : k[X]} (hp : Irreducible 
p) (hsep : p.Separable) : p.degree = 1
参数：hp : Irreducible p；hsep : p.Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.degree_eq_one_of_irreducible`：∀ {R : Type u_1} [inst :
 Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree = 1
· 使用定理 `IsSepClosed.splits_of_separable`：∀ {k : Type u} {inst : Field k} [self :
 IsSepClosed k] (p : Polynomial k), p.Separable → p.Splits
-/
theorem degree_eq_one_of_irreducible [IsSepClosed k] {p : k[X]}
    (hp : Irreducible p) (hsep : p.Separable) : p.degree = 1 :=
  (IsSepClosed.splits_of_separable p hsep).degree_eq_one_of_irreducible hp

variable (K)
/-
**IsSepClosed.algebraMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsSepClosed`。
形式化陈述：algebraMap_surjective [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k
 K] : Function.Surjective (algebraMap k K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `IsSepClosed.degree_eq_one_of_irreducible`：degree_eq_one_of_irreducible [
IsSepClosed k] {p : k[X]} (hp : Irreducible p) (hsep : p.Separable) : p.degree =
 1
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
theorem algebraMap_surjective
    [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (Algebra.IsSeparable.isIntegral k x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm
/-
**IsSepClosed.algebraMap_bijective** 是 Mathlib 中的一个引理，位于命名空间 `IsSepClosed`。
形式化陈述：algebraMap_bijective [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k 
K] : Function.Bijective (algebraMap k K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSepClosed.algebraMap_surjective`：algebraMap_surjective [IsSepClosed k]
 [Algebra k K] [Algebra.IsSeparable k K] : Function.Surjective (algebraMap k K)
-/
lemma algebraMap_bijective [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Bijective (algebraMap k K) :=
  ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective _ _⟩

end IsSepClosed

/-- If `k` is separably closed, `K / k` is a field extension, `L / k` is an intermediate field
which is separable, then `L` is equal to `k`. A corollary of `IsSepClosed.algebraMap_surjective`. -/
/-
**IntermediateField.eq_bot_of_isSepClosed_of_isSeparable** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：IntermediateField.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Al
gebra k K] (L : IntermediateField k K) [Algebra.IsSeparable k L] : L = ⊥
参数：L : IntermediateField k K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `IsSepClosed.algebraMap_surjective`：algebraMap_surjective [IsSepClosed k]
 [Algebra k K] [Algebra.IsSeparable k K] : Function.Surjective (algebraMap k K)
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

--- 原说明 ---
If `k` is separably closed, `K / k` is a field extension, `L / k` is an intermed
iate field
which is separable, then `L` is equal to `k`. A corollary of `IsSepClosed.algebr
aMap_surjective`.
-/
theorem IntermediateField.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Algebra k K]
    (L : IntermediateField k K) [Algebra.IsSeparable k L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

variable (k) (K)

/-- Typeclass for an extension being a separable closure. -/
/-
**IsSepClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u) → [inst : Field k] → (K : Type v) → [inst_1 : Field K] → [Alg
ebra k K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for an extension being a separable closure.
-/
class IsSepClosure [Algebra k K] : Prop where
  sep_closed : IsSepClosed K
  separable : Algebra.IsSeparable k K

/-- A separably closed field is its separable closure. -/
/-
**IsSepClosure.self_of_isSepClosed** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A separably closed field is its separable closure.
-/
instance IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k :=
  ⟨by assumption, Algebra.isSeparable_self k⟩

/-- If `K` is perfect and is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is perfect and is a separable closure of `k`,
then it is also an algebraic closure of `k`.
-/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField_top
    [Algebra k K] [IsSepClosure k K] [PerfectField K] : IsAlgClosure k K :=
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  ⟨inferInstance, IsSepClosure.separable.isAlgebraic⟩

/-- If `k` is perfect, `K` is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `k` is perfect, `K` is a separable closure of `k`,
then it is also an algebraic closure of `k`.
-/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField
    [Algebra k K] [IsSepClosure k K] [PerfectField k] : IsAlgClosure k K :=
  have halg : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  haveI := halg.perfectField; inferInstance

/-- If `k` is perfect, `K` is an algebraic closure of `k`,
then it is also a separable closure of `k`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `k` is perfect, `K` is an algebraic closure of `k`,
then it is also a separable closure of `k`.
-/
instance (priority := 100) IsSepClosure.of_isAlgClosure_of_perfectField
    [Algebra k K] [IsAlgClosure k K] [PerfectField k] : IsSepClosure k K :=
  ⟨haveI := IsAlgClosure.isAlgClosed (R := k) (K := K); inferInstance,
    (IsAlgClosure.isAlgebraic (R := k) (K := K)).isSeparable_of_perfectField⟩

variable {k} {K}
/-
**isSepClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSepClosure_iff [Algebra k K] : IsSepClosure k K ↔ IsSepClosed K ∧ Algebr
a.IsSeparable k K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosure.sep_closed`：∀ (k : Type u) {inst : Field k} {K : Type v} {i
nst_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   IsSepClosed
 K
· 使用定理 `IsSepClosure.separable`：∀ {k : Type u} {inst : Field k} {K : Type v} {in
st_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   Algebra.IsSe
parable k K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isSepClosure_iff [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ Algebra.IsSeparable k K :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsSepClosure

/-
**IsSepClosure.isSeparable** 是 Mathlib 中的一个实例，位于命名空间 `IsSepClosure`。
形式化陈述：isSeparable [Algebra k K] [IsSepClosure k K] : Algebra.IsSeparable k K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosure.separable`：∀ {k : Type u} {inst : Field k} {K : Type v} {in
st_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   Algebra.IsSe
parable k K
-/
instance isSeparable [Algebra k K] [IsSepClosure k K] : Algebra.IsSeparable k K :=
  IsSepClosure.separable
/-
**IsSepClosure.** 是 Mathlib 中的一个实例，位于命名空间 `IsSepClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isGalois [Algebra k K] [IsSepClosure k K] : IsGalois k K where
  to_isSeparable := IsSepClosure.separable
  to_normal.toIsAlgebraic := inferInstance
  to_normal.splits' x := (IsSepClosure.sep_closed k).splits_codomain _
    (Algebra.IsSeparable.isSeparable k x)

end IsSepClosure

namespace IsSepClosed

variable {K : Type u} (L : Type v) {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsSepClosed M]

/-
**IsSepClosed.surjective_domRestrict_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `I
sSepClosed`。
形式化陈述：surjective_domRestrict_of_isSeparable {E : Type*} [Field E] [Algebra K E] 
[Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] : Function.Surject
ive fun φ : E ->ₐ[K] M => φ.domRestrict L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_splits'`：exists_algHom_of_splits' (hK
 : forall s : E, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) : exis
ts φ : E ->ₐ[F] K, φ.domRestrict…
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `IsSepClosed.splits_codomain`：IsSepClosed.splits_codomain [IsSepClosed K]
 {f : k ->+* K} (p : k[X]) (h : p.Separable) : (p.map f).Splits
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
-/
theorem surjective_domRestrict_of_isSeparable {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.domRestrict L :=
  fun f ↦ IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s ↦ ⟨Algebra.IsSeparable.isIntegral L s,
      IsSepClosed.splits_codomain _ <| Algebra.IsSeparable.isSeparable L s⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isSeparable := surjective_domRestrict_of_isSeparable

variable [Algebra.IsSeparable K L] {L}

/-- A (random) homomorphism from a separable extension L of K into a separably
  closed extension M of K. -/
noncomputable irreducible_def lift : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsSeparable.isIntegral K x,
      splits_codomain _ (Algebra.IsSeparable.isSeparable K x)⟩)
    (IntermediateField.adjoin_univ K L)

end IsSepClosed

namespace IsSepClosure

variable (K : Type u) [Field K] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra K M] [IsSepClosure K M]
variable [Algebra K L] [IsSepClosure K L]

attribute [local instance] IsSepClosure.sep_closed in
/-- A (random) isomorphism between two separable closures of `K`. -/
/-
**IsSepClosure.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsSepClosure`。
形式化陈述：equiv : L ≃ₐ[K] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosure.sep_closed`：∀ (k : Type u) {inst : Field k} {K : Type v} {i
nst_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   IsSepClosed
 K

--- 原说明 ---
A (random) isomorphism between two separable closures of `K`.
-/
noncomputable def equiv : L ≃ₐ[K] M :=
  AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L →ₐ[K] M) (IsSepClosed.lift : M →ₐ[K] L)).1

end IsSepClosure

section separableClosure

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- If `E` is normal over `F`, then the separable closure of `F` in `E` is Galois (i.e.
normal and separable) over `F`. -/
@[stacks 0EXK]
/-
**separableClosure.isGalois** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：separableClosure.isGalois [Normal F E] : IsGalois F (separableClosure F E)
 where to_isSeparable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separableClosure.normalClosure_eq_self`：separableClosure.normalClosure_e
q_self : normalClosure F (separableClosure F E) E = separableClosure F E

--- 原说明 ---
If `E` is normal over `F`, then the separable closure of `F` in `E` is Galois (i
.e.
normal and separable) over `F`.
-/
instance separableClosure.isGalois [Normal F E] : IsGalois F (separableClosure F E) where
  to_isSeparable := separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

/-- If `E / F` is a field extension and `E` is separably closed, then the separable closure
of `F` in `E` is equal to `F` if and only if `F` is separably closed. -/
/-
**IsSepClosed.separableClosure_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSepClosed.separableClosure_eq_bot_iff [IsSepClosed E] : separableClosure
 F E = ⊥ ↔ IsSepClosed F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> Separable p -> exists x, p.eval x = 0) : IsSepClosed k
· 使用定理 `IsSepClosed.exists_aeval_eq_zero`：exists_aeval_eq_zero {k : Type*} [Comm
Semiring k] [IsSepClosed K] [Algebra k K] [FaithfulSMul k K] (p : k[X]) (hp : p.
degree != 0) (hsep : p…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IntermediateField.eq_bot_of_isSepClosed_of_isSeparable`：IntermediateFiel
d.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Algebra k K] (L : Interm
ediateField k K) [Algebra.IsSeparable k L] :…

--- 原说明 ---
If `E / F` is a field extension and `E` is separably closed, then the separable 
closure
of `F` in `E` is equal to `F` if and only if `F` is separably closed.
-/
theorem IsSepClosed.separableClosure_eq_bot_iff [IsSepClosed E] :
    separableClosure F E = ⊥ ↔ IsSepClosed F := by
  refine ⟨fun h ↦ IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (hsep.of_dvd <| minpoly.dvd _ x hx)
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- If `E` is separably closed, then the separable closure of `F` in `E` is an absolute
separable closure of `F`. -/
/-
**separableClosure.isSepClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableC
losure F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSepClosed.separableClosure_eq_bot_iff`：IsSepClosed.separableClosure_eq
_bot_iff [IsSepClosed E] : separableClosure F E = ⊥ ↔ IsSepClosed F
· 使用定理 `separableClosure.separableClosure_eq_bot`：separableClosure.separableClos
ure_eq_bot : separableClosure (separableClosure F E) E = ⊥

--- 原说明 ---
If `E` is separably closed, then the separable closure of `F` in `E` is an absol
ute
separable closure of `F`.
-/
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) :=
  ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩

/-- The absolute separable closure is defined to be the relative separable closure inside the
algebraic closure. It is indeed a separable closure (`IsSepClosure`) by
`separableClosure.isSepClosure`, and it is Galois (`IsGalois`) by `separableClosure.isGalois`
or `IsSepClosure.isGalois`, and every separable extension embeds into it (`IsSepClosed.lift`). -/
/-
**SeparableClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeparableClosure : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute separable closure is defined to be the relative separable closure i
nside the
algebraic closure. It is indeed a separable closure (`IsSepClosure`) by
`separableClosure.isSepClosure`, and it is Galois (`IsGalois`) by `separableClos
ure.isGalois`
or `IsSepClosure.isGalois`, and every separable extension embeds into it (`IsSep
Closed.lift`).
-/
abbrev SeparableClosure : Type _ := separableClosure F (AlgebraicClosure F)
/-
**SeparableClosure.isSepClosed** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparableClosure.isSepClosed : IsSepClosed (SeparableClosure F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSepClosure.sep_closed`：∀ (k : Type u) {inst : Field k} {K : Type v} {i
nst_1 : Field K} {inst_2 : Algebra k K} [self : IsSepClosure k K],   IsSepClosed
 K
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance SeparableClosure.isSepClosed : IsSepClosed (SeparableClosure F) :=
  (inferInstance : IsSepClosure F (SeparableClosure F)).sep_closed

end separableClosure

