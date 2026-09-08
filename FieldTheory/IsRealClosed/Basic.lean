/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# Real Closed Field

A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.

A real closed field is an algebraic generalisation of the real numbers.

In this file we define real closed fields and prove some of their properties.

TODO (Artie Khovanov) : equivalent conditions for a real field to be real closed
TODO (Artie Khovanov) : real numbers, real algebraic numbers, hyperreals form a real closed field

## Main Definitions

- `IsRealClosed R` is the typeclass saying `R` is a real closed field.

## Tags

real closed, rcf

-/

public section

open Polynomial

/--
A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.
-/
/-
**IsRealClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Field R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field `R` is real closed if all of the following hold:
1. `R` is real (that is, `-1` is not a sum of squares in `R`).
2. for every `x` in `R`, one of `x` or `-x` is a square.
3. every odd-degree polynomial over `R` has a root in `R`.
-/
class IsRealClosed (R : Type*) [Field R] : Prop extends IsSemireal R where
  isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x)
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

attribute [aesop 90% forward] IsRealClosed.isSquare_or_isSquare_neg

namespace IsRealClosed

universe u

variable {R : Type u} [Field R]

/-
**IsRealClosed.of_linearOrderedField** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`。
形式化陈述：of_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R] (isSquare_of
_nonneg : forall {x : R}, 0 <= x -> IsSquare x) (exists_isRoot_of_odd_natDegree 
: forall {f : R[X]}, Odd f.natDegree -> exists x, f.IsRoot x) : IsRealClosed R w
here isSquare_or_isSquare_neg {x}
参数：isSquare_of_nonneg : forall {x : R}, 0 <= x -> IsSquare x；exists_isRoot_of_od
d_natDegree : forall {f : R[X]}, Odd f.natDegree -> exists x, f.IsRoot x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsSemirealOfIsStrictOrderedRingOfExistsAddOfLE`：∀ (R : Type u_1) [in
st : Semiring R] [inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE
 R], IsSemireal R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem of_linearOrderedField [LinearOrder R] [IsStrictOrderedRing R]
    (isSquare_of_nonneg : ∀ {x : R}, 0 ≤ x → IsSquare x)
    (exists_isRoot_of_odd_natDegree : ∀ {f : R[X]}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed R where
  isSquare_or_isSquare_neg {x} := by
    rcases le_total x 0 with (neg | pos)
    · exact .inr <| isSquare_of_nonneg (neg_nonneg_of_nonpos neg)
    · exact .inl <| isSquare_of_nonneg pos
  exists_isRoot_of_odd_natDegree := exists_isRoot_of_odd_natDegree

variable [IsRealClosed R]

@[aesop 50%]
/-
**IsRealClosed._root_.IsSquare.of_not_isSquare_neg** 是 Mathlib 中的一个定理，位于命名空间 `Is
RealClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSquare.of_not_isSquare_neg {x : R} (hx : ¬ IsSquare (-x)) : IsSquare x := by aesop

@[aesop 80%]
/-
**IsRealClosed.isSquare_neg_of_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClo
sed`。
形式化陈述：isSquare_neg_of_not_isSquare {x : R} (hx : ¬ IsSquare x) : IsSquare (-x)
参数：hx : ¬ IsSquare x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `IsRealClosed.isSquare_or_isSquare_neg`：∀ {R : Type u_1} {inst : Field R}
 [self : IsRealClosed R] (x : R), IsSquare x ∨ IsSquare (-x)
-/
theorem isSquare_neg_of_not_isSquare {x : R} (hx : ¬ IsSquare x) : IsSquare (-x) := by aesop
/-
**IsRealClosed.exists_eq_pow_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`。
形式化陈述：exists_eq_pow_of_odd (x : R) {n : Nat} (hn : Odd n) : exists r, x = r ^ n
参数：x : R；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRealClosed.exists_isRoot_of_odd_natDegree`：∀ {R : Type u_1} {inst : Fi
eld R} [self : IsRealClosed R] {f : Polynomial R}, Odd f.natDegree → ∃ x, f.IsRo
ot x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `instCharZeroOfIsSemireal`：∀ (R : Type u_1) [inst : NonAssocRing R] [IsSe
mireal R], CharZero R
· 使用定理 `IsRealClosed.toIsSemireal`：∀ {R : Type u_1} {inst : Field R} [self : IsR
ealClosed R], IsSemireal R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
（共 61 条，此处仅展示前 30 条）
-/
theorem exists_eq_pow_of_odd (x : R) {n : ℕ} (hn : Odd n) : ∃ r, x = r ^ n := by
  rcases exists_isRoot_of_odd_natDegree (f := X ^ n - C x) (by simp [hn]) with ⟨r, hr⟩
  exact ⟨r, by linear_combination - (by simpa using hr : r ^ n - x = 0)⟩
/-
**IsRealClosed.exists_eq_zpow_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`。
形式化陈述：exists_eq_zpow_of_odd (x : R) {k : Int} (hk : Odd k) : exists r, x = r ^ k
参数：x : R；hk : Odd k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `IsRealClosed.exists_eq_pow_of_odd`：exists_eq_pow_of_odd (x : R) {n : Nat
} (hn : Odd n) : exists r, x = r ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem exists_eq_zpow_of_odd (x : R) {k : ℤ} (hk : Odd k) : ∃ r, x = r ^ k := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using exists_eq_pow_of_odd x (by simpa using hk)
  · rcases exists_eq_pow_of_odd x (by simpa using hk) with ⟨r, hr⟩
    exact ⟨r⁻¹, by simpa using hr⟩
/-
**IsRealClosed.exists_eq_pow_of_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed
`。
形式化陈述：exists_eq_pow_of_isSquare {x : R} (hx : IsSquare x) {n : Nat} (hn : n != 0
) : exists r, x = r ^ n
参数：hx : IsSquare x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `IsRealClosed.isSquare_or_isSquare_neg`：∀ {R : Type u_1} {inst : Field R}
 [self : IsRealClosed R] (x : R), IsSquare x ∨ IsSquare (-x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IsRealClosed.exists_eq_pow_of_odd`：exists_eq_pow_of_odd (x : R) {n : Nat
} (hn : Odd n) : exists r, x = r ^ n
-/
theorem exists_eq_pow_of_isSquare {x : R} (hx : IsSquare x) {n : ℕ} (hn : n ≠ 0) :
    ∃ r, x = r ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rcases Nat.even_or_odd n with (even | odd)
    · rcases even with ⟨m, hm⟩
      rcases hx with ⟨s, hs⟩
      rcases isSquare_or_isSquare_neg s with (h | h) <;>
        rcases ih m (by lia) h (by lia) with ⟨r, hr⟩ <;>
        exact ⟨r, by simp [hm, pow_add, ← hr, hs]⟩
    · exact exists_eq_pow_of_odd x odd
/-
**IsRealClosed.exists_eq_zpow_of_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClose
d`。
形式化陈述：exists_eq_zpow_of_isSquare {x : R} (hx : IsSquare x) {k : Int} (hk : k != 
0) : exists r, x = r ^ k
参数：hx : IsSquare x；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `IsRealClosed.exists_eq_pow_of_isSquare`：exists_eq_pow_of_isSquare {x : R
} (hx : IsSquare x) {n : Nat} (hn : n != 0) : exists r, x = r ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem exists_eq_zpow_of_isSquare {x : R} (hx : IsSquare x) {k : ℤ} (hk : k ≠ 0) :
    ∃ r, x = r ^ k := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using exists_eq_pow_of_isSquare hx (by simpa using hk)
  · rcases exists_eq_pow_of_isSquare hx (by simpa using hk) with ⟨r, hr⟩
    exact ⟨r⁻¹, by simpa using hr⟩

section LinearOrderedField

variable [LinearOrder R] [IsStrictOrderedRing R]

/-
**IsRealClosed.nonneg_iff_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`。
形式化陈述：nonneg_iff_isSquare {x : R} : 0 <= x ↔ IsSquare x where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `nonpos_of_neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddLeftMono α] {a : α}, 0 ≤ -a → a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsSquare.nonneg`：IsSquare.nonneg [Semiring R] [LinearOrder R] [ExistsAdd
OfLE R] [PosMulMono R] [AddLeftMono R] {x : R} (h : IsSquare x) : 0 <= x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsRealClosed.isSquare_or_isSquare_neg`：∀ {R : Type u_1} {inst : Field R}
 [self : IsRealClosed R] (x : R), IsSquare x ∨ IsSquare (-x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem nonneg_iff_isSquare {x : R} : 0 ≤ x ↔ IsSquare x where
  mp h := by
    suffices IsSquare (-x) → x = 0 by aesop
    exact fun hc ↦ le_antisymm (nonpos_of_neg_nonneg (IsSquare.nonneg hc)) h
  mpr := IsSquare.nonneg

alias ⟨_root_.IsSquare.of_nonneg, _⟩ := nonneg_iff_isSquare
/-
**IsRealClosed.exists_eq_pow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`。
形式化陈述：exists_eq_pow_of_nonneg {x : R} (hx : 0 <= x) {n : Nat} (hn : n != 0) : ex
ists r, x = r ^ n
参数：hx : 0 <= x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRealClosed.exists_eq_pow_of_isSquare`：exists_eq_pow_of_isSquare {x : R
} (hx : IsSquare x) {n : Nat} (hn : n != 0) : exists r, x = r ^ n
· 使用定理 `IsSquare.of_nonneg`：∀ {R : Type u} [inst : Field R] [IsRealClosed R] [in
st_2 : LinearOrder R] [IsStrictOrderedRing R] {x : R},   0 ≤ x → IsSquare x
-/
theorem exists_eq_pow_of_nonneg {x : R} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : ∃ r, x = r ^ n :=
  exists_eq_pow_of_isSquare (.of_nonneg hx) hn
/-
**IsRealClosed.exists_eq_zpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `IsRealClosed`
。
形式化陈述：exists_eq_zpow_of_nonneg {x : R} (hx : 0 <= x) {k : Int} (hk : k != 0) : e
xists r, x = r ^ k
参数：hx : 0 <= x；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRealClosed.exists_eq_zpow_of_isSquare`：exists_eq_zpow_of_isSquare {x :
 R} (hx : IsSquare x) {k : Int} (hk : k != 0) : exists r, x = r ^ k
· 使用定理 `IsSquare.of_nonneg`：∀ {R : Type u} [inst : Field R] [IsRealClosed R] [in
st_2 : LinearOrder R] [IsStrictOrderedRing R] {x : R},   0 ≤ x → IsSquare x
-/
theorem exists_eq_zpow_of_nonneg {x : R} (hx : 0 ≤ x) {k : ℤ} (hk : k ≠ 0) : ∃ r, x = r ^ k :=
  exists_eq_zpow_of_isSquare (.of_nonneg hx) hk

end LinearOrderedField

end IsRealClosed

