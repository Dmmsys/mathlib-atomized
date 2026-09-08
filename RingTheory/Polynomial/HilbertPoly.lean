/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Hilbert polynomials

In this file, we formalise the following statement: if `F` is a field with characteristic `0`, then
given any `p : F[X]` and `d : ℕ`, there exists some `h : F[X]` such that for any large enough
`n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
This `h` is unique and is denoted as `Polynomial.hilbertPoly p d`.

For example, given `d : ℕ`, the power series expansion of `1/(1 - X)ᵈ⁺¹` in `F[X]`
is `Σₙ ((d + n).choose d)Xⁿ`, which equals `Σₙ ((n + 1)···(n + d)/d!)Xⁿ` and hence
`Polynomial.hilbertPoly (1 : F[X]) (d + 1)` is the polynomial `(X + 1)···(X + d)/d!`. Note that
if `d! = 0` in `F`, then the polynomial `(X + 1)···(X + d)/d!` no longer works, so we do not want
`d!` to be divisible by the characteristic of `F`. As `Polynomial.hilbertPoly` may take any
`p : F[X]` and `d : ℕ` as its inputs, it is necessary for us to assume that `CharZero F`.

## Main definitions

* `Polynomial.hilbertPoly p d`. Given a field `F`, a polynomial `p : F[X]` and a natural number `d`,
  if `F` is of characteristic `0`, then `Polynomial.hilbertPoly p d : F[X]` is the polynomial whose
  value at `n` equals the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.

## TODO

* Hilbert polynomials of finitely generated graded modules over Noetherian rings.
-/

@[expose] public section

open Nat PowerSeries

variable (F : Type*) [Field F]

namespace Polynomial

/--
For any field `F` and natural numbers `d` and `k`, `Polynomial.preHilbertPoly F d k`
is defined as `(d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))`.
This is the most basic form of Hilbert polynomials. `Polynomial.preHilbertPoly ℚ d 0`
is exactly the Hilbert polynomial of the polynomial ring `ℚ[X_0,...,X_d]` viewed as
a graded module over itself. In fact, `Polynomial.preHilbertPoly F d k` is the
same as `Polynomial.hilbertPoly ((X : F[X]) ^ k) (d + 1)` for any field `F` and
`d k : ℕ` (see the lemma `Polynomial.hilbertPoly_X_pow_succ`). See also the lemma
`Polynomial.preHilbertPoly_eq_choose_sub_add`, which states that if `CharZero F`,
then for any `d k n : ℕ` with `k ≤ n`, `(Polynomial.preHilbertPoly F d k).eval (n : F)`
equals `(n - k + d).choose d`.
-/
/-
**Polynomial.preHilbertPoly** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：preHilbertPoly (d k : Nat) : F[X]
参数：d k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any field `F` and natural numbers `d` and `k`, `Polynomial.preHilbertPoly F 
d k`
is defined as `(d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) 
+ 1))`.
This is the most basic form of Hilbert polynomials. `Polynomial.preHilbertPoly ℚ
 d 0`
is exactly the Hilbert polynomial of the polynomial ring `ℚ[X_0,...,X_d]` viewed
 as
a graded module over itself. In fact, `Polynomial.preHilbertPoly F d k` is the
same as `Polynomial.hilbertPoly ((X : F[X]) ^ k) (d + 1)` for any field `F` and
`d k : ℕ` (see the lemma `Polynomial.hilbertPoly_X_pow_succ`). See also the lemm
a
`Polynomial.preHilbertPoly_eq_choose_sub_add`, which states that if `CharZero F`
,
then for any `d k n : ℕ` with `k ≤ n`, `(Polynomial.preHilbertPoly F d k).eval (
n : F)`
equals `(n - k + d).choose d`.
-/
noncomputable def preHilbertPoly (d k : ℕ) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))
/-
**Polynomial.natDegree_preHilbertPoly** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_preHilbertPoly [CharZero F] (d k : Nat) : (preHilbertPoly F d k)
.natDegree = d
参数：d k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Polynomial.preHilbertPoly.eq_1`：∀ (F : Type u_1) [inst : Field F] (d k :
 ℕ),   Polynomial.preHilbertPoly F d k = (↑d.factorial)⁻¹ • (ascPochhammer F d).
comp (Polynomial.X -…
· 使用引理 `Polynomial.natDegree_smul`：natDegree_smul {S : Type*} [Semiring S] [IsDo
main S] [Module S R] [Module.IsTorsionFree S R] {a : S} (ha : a != 0) : (a • p).
natDegree = p.n…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ascPochhammer_natDegree`：ascPochhammer_natDegree (n : Nat) [NoZeroDiviso
rs S] [Nontrivial S] : (ascPochhammer S n).natDegree = n
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `add_comm_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c :
 α), a - b + c = a + (c - b)
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma natDegree_preHilbertPoly [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).natDegree = d := by
  have hne : (d ! : F) ≠ 0 := by norm_cast; positivity
  rw [preHilbertPoly, natDegree_smul _ (inv_ne_zero hne), natDegree_comp, ascPochhammer_natDegree,
    add_comm_sub, ← C_1, ← map_sub, natDegree_add_C, natDegree_X, mul_one]
/-
**Polynomial.coeff_preHilbertPoly_self** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_preHilbertPoly_self [CharZero F] (d k : Nat) : (preHilbertPoly F d k
).coeff d = (d ! : F)⁻¹
参数：d k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用引理 `Polynomial.natDegree_preHilbertPoly`：natDegree_preHilbertPoly [CharZero 
F] (d k : Nat) : (preHilbertPoly F d k).natDegree = d
· 使用引理 `Polynomial.natDegree_smul`：natDegree_smul {S : Type*} [Semiring S] [IsDo
main S] [Module S R] [Module.IsTorsionFree S R] {a : S} (ha : a != 0) : (a • p).
natDegree = p.n…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_comp`：leadingCoeff_comp (hq : natDegree q != 0) 
: leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `monic_ascPochhammer`：monic_ascPochhammer (n : Nat) [Nontrivial S] [NoZer
oDivisors S] : Monic ascPochhammer S n
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
（共 32 条，此处仅展示前 30 条）
-/
lemma coeff_preHilbertPoly_self [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).coeff d = (d ! : F)⁻¹ := by
  delta preHilbertPoly
  have hne : (d ! : F) ≠ 0 := by norm_cast; positivity
  have heq : d = ((ascPochhammer F d).comp (X - C (k : F) + 1)).natDegree :=
    (natDegree_preHilbertPoly F d k).symm.trans (natDegree_smul _ (inv_ne_zero hne))
  nth_rw 3 [heq]
  calc
  _ = (d ! : F)⁻¹ • ((ascPochhammer F d).comp (X - C ((k : F) - 1))).leadingCoeff := by
    simp only [sub_add, ← C_1, ← map_sub, coeff_smul, coeff_natDegree]
  _ = (d ! : F)⁻¹ := by
    simp only [leadingCoeff_comp (ne_of_eq_of_ne (natDegree_X_sub_C _) one_ne_zero), Monic.def.1
      (monic_ascPochhammer _ _), leadingCoeff_X_sub_C, one_pow, smul_eq_mul, mul_one]
/-
**Polynomial.leadingCoeff_preHilbertPoly** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_preHilbertPoly [CharZero F] (d k : Nat) : (preHilbertPoly F d
 k).leadingCoeff = (d ! : F)⁻¹
参数：d k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用引理 `Polynomial.natDegree_preHilbertPoly`：natDegree_preHilbertPoly [CharZero 
F] (d k : Nat) : (preHilbertPoly F d k).natDegree = d
· 使用引理 `Polynomial.coeff_preHilbertPoly_self`：coeff_preHilbertPoly_self [CharZer
o F] (d k : Nat) : (preHilbertPoly F d k).coeff d = (d ! : F)⁻¹
-/
lemma leadingCoeff_preHilbertPoly [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).leadingCoeff = (d ! : F)⁻¹ := by
  rw [leadingCoeff, natDegree_preHilbertPoly, coeff_preHilbertPoly_self]
/-
**Polynomial.preHilbertPoly_eq_choose_sub_add** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：preHilbertPoly_eq_choose_sub_add [CharZero F] (d : Nat) {k n : Nat} (hkn :
 k <= n) : (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d
参数：d : Nat；hkn : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ascPochhammer_nat_eq_natCast_ascFactorial`：ascPochhammer_nat_eq_natCast_
ascFactorial (S : Type*) [Semiring S] (n k : Nat) : (ascPochhammer S k).eval (n 
: S) = n.ascFactorial k
· 使用定理 `Nat.ascFactorial_eq_factorial_mul_choose`：ascFactorial_eq_factorial_mul_
choose (n k : Nat) : (n + 1).ascFactorial k = k ! * (n + k).choose k
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
（共 49 条，此处仅展示前 30 条）
-/
lemma preHilbertPoly_eq_choose_sub_add [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n) :
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d := by
  have : (d ! : F) ≠ 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    simp [field, ascFactorial_eq_factorial_mul_choose]

variable {F}

/--
`Polynomial.hilbertPoly p 0 = 0`; for any `d : ℕ`, `Polynomial.hilbertPoly p (d + 1)`
is defined as `∑ i ∈ p.support, (p.coeff i) • Polynomial.preHilbertPoly F d i`. If
`M` is a graded module whose Poincaré series can be written as `p(X)/(1 - X)ᵈ` for some
`p : ℚ[X]` with integer coefficients, then `Polynomial.hilbertPoly p d` is the Hilbert
polynomial of `M`. See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`,
which says that `PowerSeries.coeff F n (p * PowerSeries.invOneSubPow F d)` equals
`(Polynomial.hilbertPoly p d).eval (n : F)` for any large enough `n : ℕ`.
-/
/-
**Polynomial.hilbertPoly** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{F : Type u_1} → [inst : Field F] → Polynomial F → ℕ → Polynomial F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.hilbertPoly p 0 = 0`; for any `d : ℕ`, `Polynomial.hilbertPoly p (d 
+ 1)`
is defined as `∑ i ∈ p.support, (p.coeff i) • Polynomial.preHilbertPoly F d i`. 
If
`M` is a graded module whose Poincaré series can be written as `p(X)/(1 - X)ᵈ` f
or some
`p : ℚ[X]` with integer coefficients, then `Polynomial.hilbertPoly p d` is the H
ilbert
polynomial of `M`. See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_ev
al`,
which says that `PowerSeries.coeff F n (p * PowerSeries.invOneSubPow F d)` equal
s
`(Polynomial.hilbertPoly p d).eval (n : F)` for any large enough `n : ℕ`.
-/
noncomputable def hilbertPoly (p : F[X]) : (d : ℕ) → F[X]
  | 0 => 0
  | d + 1 => ∑ i ∈ p.support, (p.coeff i) • preHilbertPoly F d i
/-
**Polynomial.hilbertPoly_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_zero_left (d : Nat) : hilbertPoly (0 : F[X]) d = 0
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
lemma hilbertPoly_zero_left (d : ℕ) : hilbertPoly (0 : F[X]) d = 0 := by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]
/-
**Polynomial.hilbertPoly_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_zero_right (p : F[X]) : hilbertPoly p 0 = 0
参数：p : F[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hilbertPoly_zero_right (p : F[X]) : hilbertPoly p 0 = 0 := rfl
/-
**Polynomial.hilbertPoly_succ** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_succ (p : F[X]) (d : Nat) : hilbertPoly p (d + 1) = ∑ i in p.s
upport, (p.coeff i) • preHilbertPoly F d i
参数：p : F[X]；d : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hilbertPoly_succ (p : F[X]) (d : ℕ) :
    hilbertPoly p (d + 1) = ∑ i ∈ p.support, (p.coeff i) • preHilbertPoly F d i := rfl
/-
**Polynomial.hilbertPoly_X_pow_succ** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_X_pow_succ (d k : Nat) : hilbertPoly ((X : F[X]) ^ k) (d + 1) 
= preHilbertPoly F d k
参数：d k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.support_X_pow`：support_X_pow [Nontrivial R] (n : Nat) : (X ^ 
n : R[X]).support = singleton n
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hilbertPoly_X_pow_succ (d k : ℕ) :
    hilbertPoly ((X : F[X]) ^ k) (d + 1) = preHilbertPoly F d k := by
  delta hilbertPoly; simp
/-
**Polynomial.hilbertPoly_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_add_left (p q : F[X]) (d : Nat) : hilbertPoly (p + q) d = hilb
ertPoly p d + hilbertPoly q d
参数：p q : F[X]；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Polynomial.sum_add_index`：sum_add_index {S : Type*} [AddCommMonoid S] (p
 q : R[X]) (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) (h_add : forall a b₁ b
₂, f a (b₁ + b…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
lemma hilbertPoly_add_left (p q : F[X]) (d : ℕ) :
    hilbertPoly (p + q) d = hilbertPoly p d + hilbertPoly q d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [add_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _]
      exact sum_add_index _ _ _ (fun _ => zero_smul ..) (fun _ _ _ => add_smul ..)
/-
**Polynomial.hilbertPoly_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_smul (a : F) (p : F[X]) (d : Nat) : hilbertPoly (a • p) d = a 
• hilbertPoly p d
参数：a : F；p : F[X]；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Polynomial.smul_sum`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} {
T : Type u_2} [inst_1 : AddCommMonoid S] [inst_2 : DistribSMul T S]   (p : Polyn
omial R) …
· 使用定理 `Polynomial.sum_smul_index'`：sum_smul_index' {S T : Type*} [DistribSMul T
 R] [AddCommMonoid S] (p : R[X]) (b : T) (f : Nat -> R -> S) (hf : forall i, f i
 0 = 0) : (b • p…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma hilbertPoly_smul (a : F) (p : F[X]) (d : ℕ) :
    hilbertPoly (a • p) d = a • hilbertPoly p d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [smul_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _, ← sum_def _ fun _ r => r • _, Polynomial.smul_sum,
        sum_smul_index' _ _ _ fun i => zero_smul F (preHilbertPoly F d i)]
      simp only [smul_assoc]

variable (F) in
/--
The function that sends any `p : F[X]` to `Polynomial.hilbertPoly p d` is an `F`-linear map from
`F[X]` to `F[X]`.
-/
/-
**Polynomial.hilbertPoly_linearMap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_linearMap (d : Nat) : F[X] ->ₗ[F] F[X] where toFun p
参数：d : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.hilbertPoly_add_left`：hilbertPoly_add_left (p q : F[X]) (d : 
Nat) : hilbertPoly (p + q) d = hilbertPoly p d + hilbertPoly q d
· 使用引理 `Polynomial.hilbertPoly_smul`：hilbertPoly_smul (a : F) (p : F[X]) (d : Na
t) : hilbertPoly (a • p) d = a • hilbertPoly p d

--- 原说明 ---
The function that sends any `p : F[X]` to `Polynomial.hilbertPoly p d` is an `F`
-linear map from
`F[X]` to `F[X]`.
-/
noncomputable def hilbertPoly_linearMap (d : ℕ) : F[X] →ₗ[F] F[X] where
  toFun p := hilbertPoly p d
  map_add' p q := hilbertPoly_add_left p q d
  map_smul' r p := hilbertPoly_smul r p d

variable [CharZero F]

/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbertPoly p d).eval (n : F)` equals the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
/-
**Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：coeff_mul_invOneSubPow_eq_hilbertPoly_eval {p : F[X]} (d : Nat) {n : Nat} 
(hn : p.natDegree < n) : (p * invOneSubPow F d : F⟦X⟧).coeff n = (hilbertPoly p 
d).eval (n : F)
参数：d : Nat；hn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.invOneSubPow_zero`：invOneSubPow_zero : invOneSubPow S 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Polynomial.preHilbertPoly_eq_choose_sub_add`：preHilbertPoly_eq_choose_su
b_add [CharZero F] (d : Nat) {k n : Nat} (hkn : k <= n) : (preHilbertPoly F d k)
.eval (n : F) = (n - k + d).choos…
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos`：invOneSubP
ow_val_eq_mk_sub_one_add_choose_of_pos (h : 0 < d) : (invOneSubPow S d).val = (m
k fun n => Nat.choose (d - 1 + n) (d - 1) : S⟦X⟧)
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Finset.sum_subset_zero_on_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ 
: Finset ι} [inst : AddCommMonoid M] {f g : ι → M} [inst_1 : DecidableEq ι],   s
₁ ⊆ s₂ → (∀ x ∈ s₂ \ …
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The key property of Hilbert polynomials. If `F` is a field with characteristic `
0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbertPoly p d).eval (
n : F)` equals the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    {p : F[X]} (d : ℕ) {n : ℕ} (hn : p.natDegree < n) :
    (p * invOneSubPow F d : F⟦X⟧).coeff n = (hilbertPoly p d).eval (n : F) := by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finsetSum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_le (i : p.support) : (i : ℕ) ≤ n :=
        le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 i.2) hn.le
      have h (i : p.support) : eval ↑n (preHilbertPoly F d ↑i) = (n + d - ↑i).choose d := by
        rw [preHilbertPoly_eq_choose_sub_add _ _ (h_le i), Nat.sub_add_comm (h_le i)]
      simp_rw [h]
      rw [Finset.sum_coe_sort _ (fun x => (p.coeff ↑x) * (_ + d - ↑x).choose _),
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      symm
      refine Finset.sum_subset_zero_on_sdiff (fun s hs ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · rw [Finset.mem_range_succ_iff]
        exact h_le ⟨s, hs⟩
      · simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx
        rw [hx.2, zero_mul]
      · rw [add_comm, Nat.add_sub_assoc (h_le ⟨x, hx⟩), succ_eq_add_one, add_tsub_cancel_right]

/--
The polynomial satisfying the key property of `Polynomial.hilbertPoly p d` is unique.
-/
/-
**Polynomial.existsUnique_hilbertPoly** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：existsUnique_hilbertPoly (p : F[X]) (d : Nat) : exists! h : F[X], exists N
 : Nat, forall n > N, (p * invOneSubPow F d : F⟦X⟧).coeff n = h.eval (n : F)
参数：p : F[X]；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`：coeff_mul_invOneS
ubPow_eq_hilbertPoly_eval {p : F[X]} (d : Nat) {n : Nat} (hn : p.natDegree < n) 
: (p * invOneSubPow F d : F⟦X⟧).coeff n = (…
· 使用定理 `Polynomial.eq_of_infinite_eval_eq`：eq_of_infinite_eval_eq (p q : R[X]) (
h : Set.Infinite { x | eval x p = eval x q }) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Set.Ioi_infinite`：Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The polynomial satisfying the key property of `Polynomial.hilbertPoly p d` is un
ique.
-/
theorem existsUnique_hilbertPoly (p : F[X]) (d : ℕ) :
    ∃! h : F[X], ∃ N : ℕ, ∀ n > N,
      (p * invOneSubPow F d : F⟦X⟧).coeff n = h.eval (n : F) := by
  use hilbertPoly p d; constructor
  · use p.natDegree
    exact fun n => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPoly p d)
    apply ((Set.Ioi_infinite (max N p.natDegree)).image cast_injective.injOn).mono
    rintro x ⟨n, hn, rfl⟩
    simp only [Set.mem_Ioi, sup_lt_iff, Set.mem_ofPred_eq] at hn ⊢
    rw [← coeff_mul_invOneSubPow_eq_hilbertPoly_eval d hn.2, hhN n hn.1]

/--
If `h : F[X]` and there exists some `N : ℕ` such that for any number `n : ℕ` bigger than `N`
we have `PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F)`, then `h` is exactly
`Polynomial.hilbertPoly p d`.
-/
/-
**Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：eq_hilbertPoly_of_forall_coeff_eq_eval {p h : F[X]} {d : Nat} (N : Nat) (h
hN : forall n > N, PowerSeries.coeff (R
参数：N : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Polynomial.existsUnique_hilbertPoly`：existsUnique_hilbertPoly (p : F[X])
 (d : Nat) : exists! h : F[X], exists N : Nat, forall n > N, (p * invOneSubPow F
 d : F⟦X⟧).coeff n = h.ev…
· 使用定理 `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`：coeff_mul_invOneS
ubPow_eq_hilbertPoly_eval {p : F[X]} (d : Nat) {n : Nat} (hn : p.natDegree < n) 
: (p * invOneSubPow F d : F⟦X⟧).coeff n = (…

--- 原说明 ---
If `h : F[X]` and there exists some `N : ℕ` such that for any number `n : ℕ` big
ger than `N`
we have `PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F)`, then `h
` is exactly
`Polynomial.hilbertPoly p d`.
-/
theorem eq_hilbertPoly_of_forall_coeff_eq_eval
    {p h : F[X]} {d : ℕ} (N : ℕ) (hhN : ∀ n > N,
    PowerSeries.coeff (R := F) n (p * invOneSubPow F d) = h.eval (n : F)) :
    h = hilbertPoly p d :=
  ExistsUnique.unique (existsUnique_hilbertPoly p d) ⟨N, hhN⟩
    ⟨p.natDegree, fun _ x => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d x⟩
/-
**Polynomial.hilbertPoly_mul_one_sub_succ** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：hilbertPoly_mul_one_sub_succ (p : F[X]) (d : Nat) : hilbertPoly (p * (1 - 
X)) (d + 1) = hilbertPoly p d
参数：p : F[X]；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval`：eq_hilbertPoly_of_for
all_coeff_eq_eval {p h : F[X]} {d : Nat} (N : Nat) (hhN : forall n > N, PowerSer
ies.coeff (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.coe_sub`：coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries
 R) = p - q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coe_one`：coe_one : ((1 : R[X]) : PowerSeries R) = 1
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val`：on
e_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (e : Nat) : (1 - X) ^ e *
 (invOneSubPow S (d + e)).val = (invOneSubPow S d).val
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.coe_mul`：coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
· 使用定理 `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`：coeff_mul_invOneS
ubPow_eq_hilbertPoly_eval {p : F[X]} (d : Nat) {n : Nat} (hn : p.natDegree < n) 
: (p * invOneSubPow F d : F⟦X⟧).coeff n = (…
-/
lemma hilbertPoly_mul_one_sub_succ (p : F[X]) (d : ℕ) :
    hilbertPoly (p * (1 - X)) (d + 1) = hilbertPoly p d := by
  apply eq_hilbertPoly_of_forall_coeff_eq_eval (p * (1 - X)).natDegree
  intro n hn
  have heq : 1 - PowerSeries.X = ((1 - X : F[X]) : F⟦X⟧) := by simp only [coe_sub, coe_one, coe_X]
  rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val F d 1, pow_one, ← mul_assoc, heq,
    ← coe_mul, coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hn]
/-
**Polynomial.hilbertPoly_mul_one_sub_pow_add** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：hilbertPoly_mul_one_sub_pow_add (p : F[X]) (d e : Nat) : hilbertPoly (p * 
(1 - X) ^ e) (d + e) = hilbertPoly p d
参数：p : F[X]；d e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `Polynomial.hilbertPoly_mul_one_sub_succ`：hilbertPoly_mul_one_sub_succ (p
 : F[X]) (d : Nat) : hilbertPoly (p * (1 - X)) (d + 1) = hilbertPoly p d
-/
lemma hilbertPoly_mul_one_sub_pow_add (p : F[X]) (d e : ℕ) :
    hilbertPoly (p * (1 - X) ^ e) (d + e) = hilbertPoly p d := by
  induction e with
  | zero => simp
  | succ e he => rw [pow_add, pow_one, ← mul_assoc, ← add_assoc, hilbertPoly_mul_one_sub_succ, he]
/-
**Polynomial.hilbertPoly_eq_zero_of_le_rootMultiplicity_one** 是 Mathlib 中的一个引理，位
于命名空间 `Polynomial`。
形式化陈述：hilbertPoly_eq_zero_of_le_rootMultiplicity_one {p : F[X]} {d : Nat} (hdp :
 d <= p.rootMultiplicity 1) : hilbertPoly p d = 0
参数：hdp : d <= p.rootMultiplicity 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.hilbertPoly_zero_left`：hilbertPoly_zero_left (d : Nat) : hilb
ertPoly (0 : F[X]) d = 0
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `Polynomial.hilbertPoly_mul_one_sub_pow_add`：hilbertPoly_mul_one_sub_pow_
add (p : F[X]) (d e : Nat) : hilbertPoly (p * (1 - X) ^ e) (d + e) = hilbertPoly
 p d
· 使用定理 `Polynomial.hilbertPoly.eq_1`：∀ {F : Type u_1} [inst : Field F] (p : Poly
nomial F), p.hilbertPoly 0 = 0
-/
lemma hilbertPoly_eq_zero_of_le_rootMultiplicity_one
    {p : F[X]} {d : ℕ} (hdp : d ≤ p.rootMultiplicity 1) :
    hilbertPoly p d = 0 := by
  by_cases hp : p = 0
  · rw [hp, hilbertPoly_zero_left]
  · rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
    have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
      simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
      exact hq1.trans (mul_comm _ _)
    rw [heq, ← zero_add d, ← Nat.sub_add_cancel hdp, pow_add (1 - X), ← mul_assoc,
      hilbertPoly_mul_one_sub_pow_add, hilbertPoly]
/-
**Polynomial.natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt** 是 Mathlib
 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt {p : F[X]} {d : Na
t} (hp : p != 0) (hpd : p.rootMultiplicity 1 < d) : (hilbertPoly p d).natDegree 
= d - p.rootMultiplicity 1 - 1
参数：hp : p != 0；hpd : p.rootMultiplicity 1 < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Polynomial.hilbertPoly_mul_one_sub_pow_add`：hilbertPoly_mul_one_sub_pow_
add (p : F[X]) (d e : Nat) : hilbertPoly (p * (1 - X) ^ e) (d + e) = hilbertPoly
 p d
· 使用定理 `Nat.le_sub_of_add_le'`：∀ {n k m : ℕ}, m + n ≤ k → n ≤ k - m
· 使用定理 `Nat.add_one_le_of_lt`：∀ {n m : ℕ}, n < m → n + 1 ≤ m
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用引理 `Polynomial.natDegree_sum_le_of_forall_le`：natDegree_sum_le_of_forall_le 
{n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n) : natDegree 
(∑ i in s, f i) <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.natDegree_smul_le`：natDegree_smul_le {S : Type*} [SMulZeroCla
ss S R] (a : S) (p : R[X]) : natDegree (a • p) <= natDegree p
· 使用引理 `Polynomial.natDegree_preHilbertPoly`：natDegree_preHilbertPoly [CharZero 
F] (d k : Nat) : (preHilbertPoly F d k).natDegree = d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用引理 `Polynomial.coeff_preHilbertPoly_self`：coeff_preHilbertPoly_self [CharZer
o F] (d k : Nat) : (preHilbertPoly F d k).coeff d = (d ! : F)⁻¹
（共 47 条，此处仅展示前 30 条）
-/
theorem natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt
    {p : F[X]} {d : ℕ} (hp : p ≠ 0) (hpd : p.rootMultiplicity 1 < d) :
    (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
  have heq : p = q * (-1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
    simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
    exact hq1.trans (mul_comm _ _)
  nth_rw 1 [heq, ← Nat.sub_add_cancel (le_of_lt hpd), hilbertPoly_mul_one_sub_pow_add,
    ← Nat.sub_add_cancel (Nat.le_sub_of_add_le' <| add_one_le_of_lt hpd)]
  delta hilbertPoly
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_sum_le_of_forall_le _ _ <| fun _ _ => ?_
    apply le_trans (natDegree_smul_le _ _)
    rw [natDegree_preHilbertPoly]
  · have : (fun (x : ℕ) (a : F) => a) = fun x a => a * 1 ^ x := by simp only [one_pow, mul_one]
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_preHilbertPoly_self,
      ← Finset.sum_mul, ← sum_def _ (fun _ a => a), this, ← eval_eq_sum, eval_mul, eval_pow,
      eval_neg, eval_one, _root_.mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq,
      false_and, or_false, inv_eq_zero, cast_eq_zero, not_or]
    exact ⟨(not_iff_not.2 dvd_iff_isRoot).1 hq2, factorial_ne_zero _⟩
/-
**Polynomial.natDegree_hilbertPoly_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_hilbertPoly_of_ne_zero {p : F[X]} {d : Nat} (hh : hilbertPoly p 
d != 0) : (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1
参数：hh : hilbertPoly p d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.hilbertPoly_zero_left`：hilbertPoly_zero_left (d : Nat) : hilb
ertPoly (0 : F[X]) d = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `Polynomial.hilbertPoly_eq_zero_of_le_rootMultiplicity_one`：hilbertPoly_e
q_zero_of_le_rootMultiplicity_one {p : F[X]} {d : Nat} (hdp : d <= p.rootMultipl
icity 1) : hilbertPoly p d = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Polynomial.natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt`：natD
egree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt {p : F[X]} {d : Nat} (hp : p
 != 0) (hpd : p.rootMultiplicity 1 < d) : (hilbertPoly p…
-/
theorem natDegree_hilbertPoly_of_ne_zero
    {p : F[X]} {d : ℕ} (hh : hilbertPoly p d ≠ 0) :
    (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  have hp : p ≠ 0 := by
    intro h
    rw [h] at hh
    exact hh (hilbertPoly_zero_left d)
  have hpd : p.rootMultiplicity 1 < d := by
    by_contra h
    exact hh (hilbertPoly_eq_zero_of_le_rootMultiplicity_one <| not_lt.1 h)
  exact natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp hpd

end Polynomial

