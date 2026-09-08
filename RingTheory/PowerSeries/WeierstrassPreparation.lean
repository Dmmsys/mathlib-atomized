/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.PowerSeries.CoeffMulMem
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!

# Weierstrass preparation theorem for power series over a complete local ring

In this file we define Weierstrass division, Weierstrass factorization, and prove
Weierstrass preparation theorem.

We assume that a ring is adic complete with respect to some ideal.
If such ideal is a maximal ideal, then by `isLocalRing_of_isAdicComplete_maximal`,
such ring has only one maximal ideal, and hence it is a complete local ring.

## Main definitions

- `PowerSeries.IsWeierstrassDivisionAt f g q r I`: let `f` and `g` be power series over `A`, `I` be
  an ideal of `A`, this is a `Prop` which asserts that a power series
  `q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
  image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
  it's mathematically not considered).

- `PowerSeries.IsWeierstrassDivision`: version of `PowerSeries.IsWeierstrassDivisionAt`
  for local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassDivisorAt g I`: let `g` be a power series over `A`, `I` be an ideal of
  `A`, this is a `Prop` which asserts that the `n`-th coefficient
  of `g` is a unit, where `n` is the order of the image of `g` in `(A / I)⟦X⟧`
  (defined to be zero if such image is zero, in which case it's mathematically not considered).

  This property guarantees that if the `A` is `I`-adic complete, then `g` can be used as a divisor
  in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`).

- `PowerSeries.IsWeierstrassDivisor`: version of `PowerSeries.IsWeierstrassDivisorAt` for
  local rings with respect to its maximal ideal.

- `PowerSeries.IsWeierstrassFactorizationAt g f h I`: for a power series `g` over `A` and
  an ideal `I` of `A`, this is a `Prop` which asserts that `f` is a distinguished polynomial at `I`,
  `h` is a formal power series over `A` that is a unit and such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization`: version of `PowerSeries.IsWeierstrassFactorizationAt`
  for local rings with respect to its maximal ideal.

## Main results

- `PowerSeries.exists_isWeierstrassDivision`: **Weierstrass division**
  ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be power series
  over a complete local ring, such that the image of `g` in the residue field is not zero.
  Let `n` be the order of the image of `g` in the residue field. Then there exists a power series
  `q` and a polynomial `r` of degree `< n`, such that `f = g * q + r`.

- `PowerSeries.IsWeierstrassDivision.elim`,
  `PowerSeries.IsWeierstrassDivision.unique`: `q` and `r` in the Weierstrass division are unique.

- `PowerSeries.exists_isWeierstrassFactorization`: **Weierstrass preparation theorem**
  ([washington_cyclotomic], Theorem 7.3): let `g` be a power series
  over a complete local ring, such that its image in the residue field is
  not zero. Then there exists a distinguished polynomial `f` and a power series `h`
  which is a unit, such that `g = f * h`.

- `PowerSeries.IsWeierstrassFactorization.elim`,
  `PowerSeries.IsWeierstrassFactorization.unique`: `f` and `h` in Weierstrass preparation
  theorem are unique.

- `Polynomial.IsDistinguishedAt.algEquivQuotient`: a distinguished polynomial `g` induces a
  natural isomorphism `A[X] / (g) ≃ₐ[A] A⟦X⟧ / (g)`.

- `PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient`: a Weierstrass factorization
  `g = f * h` induces a natural isomorphism `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)`.

- `PowerSeries.algEquivQuotientWeierstrassDistinguished`:
  if `g` is a power series over a complete local ring,
  such that its image in the residue field is not zero, then there is a natural isomorphism
  `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished g`.

## References

- [Washington, Lawrence C. *Introduction to cyclotomic fields.*][washington_cyclotomic]

-/

@[expose] public section

open scoped Polynomial

namespace PowerSeries

variable {A : Type*} [CommRing A]

/-!

## Weierstrass division

-/

section IsWeierstrassDivisionAt

variable (f g q : A⟦X⟧) (r : A[X]) (I : Ideal A)

/-- Let `f`, `g` be power series over `A`, `I` be an ideal of `A`,
`PowerSeries.IsWeierstrassDivisionAt f g q r I` is a `Prop` which asserts that a power series
`q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered). -/
@[mk_iff]
/-
**PowerSeries.IsWeierstrassDivisionAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `PowerSeries`。
形式化陈述：{A : Type u_1} → [inst : CommRing A] → PowerSeries A → PowerSeries A → Pow
erSeries A → Polynomial A → Ideal A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f`, `g` be power series over `A`, `I` be an ideal of `A`,
`PowerSeries.IsWeierstrassDivisionAt f g q r I` is a `Prop` which asserts that a
 power series
`q` and a polynomial `r` of degree `< n` satisfy `f = g * q + r`, where `n` is t
he order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which
 case
it's mathematically not considered).
-/
structure IsWeierstrassDivisionAt : Prop where
  degree_lt : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat
  eq_mul_add : f = g * q + r

/-- Version of `PowerSeries.IsWeierstrassDivisionAt` for local rings with respect to
its maximal ideal. -/
/-
**PowerSeries.IsWeierstrassDivision** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：IsWeierstrassDivision [IsLocalRing A] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `PowerSeries.IsWeierstrassDivisionAt` for local rings with respect to
its maximal ideal.
-/
abbrev IsWeierstrassDivision [IsLocalRing A] : Prop :=
  f.IsWeierstrassDivisionAt g q r (IsLocalRing.maximalIdeal A)
/-
**PowerSeries.isWeierstrassDivisionAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：isWeierstrassDivisionAt_zero : IsWeierstrassDivisionAt 0 g 0 0 I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isWeierstrassDivisionAt_zero : IsWeierstrassDivisionAt 0 g 0 0 I := by
  constructor
  · rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · simp

variable {f g q r I}

namespace IsWeierstrassDivisionAt

/-
**PowerSeries.IsWeierstrassDivisionAt.coeff_f_sub_r_mem** 是 Mathlib 中的一个定理，位于命名空
间 `PowerSeries.IsWeierstrassDivisionAt`。
形式化陈述：coeff_f_sub_r_mem (H : f.IsWeierstrassDivisionAt g q r I) {i : Nat} (hi : 
i < (g.map (Ideal.Quotient.mk I)).order.toNat) : coeff i (f - r : A⟦X⟧) in I
参数：H : f.IsWeierstrassDivisionAt g q r I；hi : i < (g.map (Ideal.Quotient.mk I)).
order.toNat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal`：coeff_mul_mem_i
deal_of_coeff_left_mem_ideal (hf : forall i <= n, coeff i f in I) : forall i <= 
n, coeff i (f * g) in I
· 使用定理 `PowerSeries.coeff_of_lt_order_toNat`：coeff_of_lt_order_toNat (n : Nat) (
h : n < φ.order.toNat) : coeff n φ = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `PowerSeries.coeff_map`：coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ
) = f (coeff n φ)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeff_f_sub_r_mem (H : f.IsWeierstrassDivisionAt g q r I)
    {i : ℕ} (hi : i < (g.map (Ideal.Quotient.mk I)).order.toNat) :
    coeff i (f - r : A⟦X⟧) ∈ I := by
  replace H := H.2
  rw [← sub_eq_iff_eq_add] at H
  rw [H]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal i (fun j hj ↦ ?_) i le_rfl
  have := coeff_of_lt_order_toNat _ (lt_of_le_of_lt hj hi)
  rwa [coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at this
/-
**PowerSeries.IsWeierstrassDivisionAt.add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
.IsWeierstrassDivisionAt`。
形式化陈述：add {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I) (H' : f'.IsWeierstr
assDivisionAt g q' r' I) : (f + f').IsWeierstrassDivisionAt g (q + q') (r + r') 
I
参数：H : f.IsWeierstrassDivisionAt g q r I；H' : f'.IsWeierstrassDivisionAt g q' r'
 I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_lt_iff`：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `Polynomial.coe_add`：coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem add {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I)
    (H' : f'.IsWeierstrassDivisionAt g q' r' I) :
    (f + f').IsWeierstrassDivisionAt g (q + q') (r + r') I :=
  ⟨(Polynomial.degree_add_le _ _).trans_lt (sup_lt_iff.2 ⟨H.degree_lt, H'.degree_lt⟩), by
    rw [H.eq_mul_add, H'.eq_mul_add, Polynomial.coe_add]; ring⟩
/-
**PowerSeries.IsWeierstrassDivisionAt.smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s.IsWeierstrassDivisionAt`。
形式化陈述：smul (H : f.IsWeierstrassDivisionAt g q r I) (a : A) : (a • f).IsWeierstra
ssDivisionAt g (a • q) (a • r) I
参数：H : f.IsWeierstrassDivisionAt g q r I；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Polynomial.coe_mul`：coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
· 使用定理 `Polynomial.coe_C`：coe_C (a : R) : ((C a : R[X]) : PowerSeries R) = Power
Series.C a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul (H : f.IsWeierstrassDivisionAt g q r I) (a : A) :
    (a • f).IsWeierstrassDivisionAt g (a • q) (a • r) I :=
  ⟨(Polynomial.degree_smul_le a _).trans_lt H.degree_lt, by
    simp [H.eq_mul_add, Algebra.smul_def, mul_add, mul_left_comm]⟩

end IsWeierstrassDivisionAt

end IsWeierstrassDivisionAt

section IsWeierstrassDivisorAt

variable (g : A⟦X⟧) (I : Ideal A)

/-- `PowerSeries.IsWeierstrassDivisorAt g I` is a `Prop` which asserts that the `n`-th coefficient
of `g` is a unit, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which case
it's mathematically not considered).

This property guarantees that if the ring is `I`-adic complete, then `g` can be used as a divisor
in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`). -/
/-
**PowerSeries.IsWeierstrassDivisorAt** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：IsWeierstrassDivisorAt : Prop
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
`PowerSeries.IsWeierstrassDivisorAt g I` is a `Prop` which asserts that the `n`-
th coefficient
of `g` is a unit, where `n` is the order of the
image of `g` in `(A / I)⟦X⟧` (defined to be zero if such image is zero, in which
 case
it's mathematically not considered).

This property guarantees that if the ring is `I`-adic complete, then `g` can be 
used as a divisor
in Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisi
onAt_div_mod`).
-/
def IsWeierstrassDivisorAt : Prop :=
  IsUnit (coeff (g.map (Ideal.Quotient.mk I)).order.toNat g)

/-- Version of `PowerSeries.IsWeierstrassDivisorAt` for local rings with respect to
its maximal ideal. -/
/-
**PowerSeries.IsWeierstrassDivisor** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：IsWeierstrassDivisor [IsLocalRing A] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `PowerSeries.IsWeierstrassDivisorAt` for local rings with respect to
its maximal ideal.
-/
abbrev IsWeierstrassDivisor [IsLocalRing A] : Prop :=
  g.IsWeierstrassDivisorAt (IsLocalRing.maximalIdeal A)

variable {g} in
/-- If `g` is a power series over a local ring such that
its image in the residue field is not zero, then `g` can be used as a Weierstrass divisor. -/
/-
**PowerSeries.IsWeierstrassDivisor.of_map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries.IsWeierstrassDivisor`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {g : PowerSeries A} [inst_1 : IsLocal
Ring A],   (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0 → g.IsWeierstrassDivi
sor
参数：PowerSeries.map (IsLocalRing.residue A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisor.eq_1`：∀ {A : Type u_1} [inst : CommRing
 A] (g : PowerSeries A) [inst_1 : IsLocalRing A],   g.IsWeierstrassDivisor = g.I
sWeierstrassDivisorAt (IsLo…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_1`：∀ {A : Type u_1} [inst : CommRi
ng A] (g : PowerSeries A) (I : Ideal A),   g.IsWeierstrassDivisorAt I = IsUnit (
(PowerSeries.coeff ((PowerSer…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.notMem_maximalIdeal`：notMem_maximalIdeal {x : R} : x ∉ maxim
alIdeal R ↔ IsUnit x
· 使用定理 `PowerSeries.coeff_order`：coeff_order (h : φ != 0) : coeff φ.order.toNat 
φ != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `PowerSeries.coeff_map`：coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ
) = f (coeff n φ)
· 使用引理 `IsLocalRing.residue_eq_zero_iff`：residue_eq_zero_iff (x : R) : residue R
 x = 0 ↔ x in maximalIdeal R

--- 原说明 ---
If `g` is a power series over a local ring such that
its image in the residue field is not zero, then `g` can be used as a Weierstras
s divisor.
-/
theorem IsWeierstrassDivisor.of_map_ne_zero [IsLocalRing A]
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : g.IsWeierstrassDivisor := by
  rw [IsWeierstrassDivisor, IsWeierstrassDivisorAt, ← IsLocalRing.notMem_maximalIdeal]
  have h := coeff_order hg
  contrapose h
  rwa [coeff_map, IsLocalRing.residue_eq_zero_iff]
/-
**PowerSeries._root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt** 是 Mat
hlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) (hI : I ≠ ⊤) : IsWeierstrassDivisorAt g I := by
  have : g.natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map g 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  simp [IsWeierstrassDivisorAt, ← this, H.monic.leadingCoeff]
/-
**PowerSeries._root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt'** 是 Ma
thlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt' {g : A[X]} {I : Ideal A}
    (H : g.IsDistinguishedAt I) [IsHausdorff I A] : IsWeierstrassDivisorAt g I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsHausdorff ⊤ A›.subsingleton
    exact isUnit_of_subsingleton _
  exact H.isWeierstrassDivisorAt hI
/-
**PowerSeries.coeff_trunc_order_mem** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coeff_trunc_order_mem (i : ℕ) :
    (g.trunc (g.map (Ideal.Quotient.mk I)).order.toNat).coeff i ∈ I := by
  rw [coeff_trunc]
  split_ifs with h
  · simpa [← RingHom.mem_ker] using coeff_of_lt_order_toNat _ h
  · exact zero_mem _

namespace IsWeierstrassDivisorAt

variable {g I} (H : g.IsWeierstrassDivisorAt I)
include H

/-
**PowerSeries.IsWeierstrassDivisorAt.isUnit_shift** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries.IsWeierstrassDivisorAt`。
形式化陈述：isUnit_shift : IsUnit mk fun i => coeff (i + (g.map (Ideal.Quotient.mk I))
.order.toNat) g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem isUnit_shift : IsUnit <| mk fun i ↦
    coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g := by
  simpa [isUnit_iff_constantCoeff]

/-- The inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.seq** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.
IsWeierstrassDivisorAt`。
形式化陈述：{A : Type u_1} →   [inst : CommRing A] →     {g : PowerSeries A} → {I : Id
eal A} → g.IsWeierstrassDivisorAt I → PowerSeries A → ℕ → PowerSeries A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inductively constructed sequence `qₖ` in the proof of Weierstrass division.
-/
noncomputable def seq (H : g.IsWeierstrassDivisorAt I) (f : A⟦X⟧) : ℕ → A⟦X⟧
  | 0 => 0
  | k + 1 =>
    H.seq f k + (mk fun i ↦ coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat)
      (f - g * H.seq f k)) * H.isUnit_shift.unit⁻¹

variable (a : A) (f f' : A⟦X⟧)
/-
**PowerSeries.IsWeierstrassDivisorAt.coeff_seq_mem** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries.IsWeierstrassDivisorAt`。
形式化陈述：coeff_seq_mem (k : Nat) {i : Nat} (hi : i >= (g.map (Ideal.Quotient.mk I))
.order.toNat) : coeff i (f - g * H.seq f k) in I ^ k
参数：k : Nat；hi : i >= (g.map (Ideal.Quotient.mk I)).order.toNat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isUnit_shift`：isUnit_shift : IsUnit m
k fun i => coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.seq.eq_2`：∀ {A : Type u_1} [inst : Co
mmRing A] {g : PowerSeries A} {I : Ideal A} (H : g.IsWeierstrassDivisorAt I)   (
f : PowerSeries A) (k : ℕ),   H.s…
· 使用引理 `PowerSeries.eq_X_pow_mul_shift_add_trunc`：eq_X_pow_mul_shift_add_trunc (
n : Nat) (f : R⟦X⟧) : f = X ^ n * (mk fun i => coeff (i + n) f) + (f.trunc n : R
⟦X⟧)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 88 条，此处仅展示前 30 条）
-/
theorem coeff_seq_mem (k : ℕ) {i : ℕ} (hi : i ≥ (g.map (Ideal.Quotient.mk I)).order.toNat) :
    coeff i (f - g * H.seq f k) ∈ I ^ k := by
  induction k generalizing hi i with
  | zero => simp
  | succ k hq =>
    rw [seq]
    set q := H.seq f k
    set s := f - g * q
    set n := (g.map (Ideal.Quotient.mk I)).order.toNat
    have hs := s.eq_X_pow_mul_shift_add_trunc n
    set s₀ := s.trunc n
    set s₁ := PowerSeries.mk fun i ↦ coeff (i + n) s
    set q' := q + s₁ * H.isUnit_shift.unit⁻¹
    have key : f - g * q' = (s₀ : A⟦X⟧) - (g.trunc n : A⟦X⟧) * s₁ * H.isUnit_shift.unit⁻¹ := by
      trans s + g * (q - q')
      · simp_rw [s]; ring
      simp_rw [q']
      rw [sub_add_cancel_left, mul_neg, ← mul_assoc, mul_right_comm]
      nth_rw 1 [g.eq_X_pow_mul_shift_add_trunc n]
      rw [add_mul, mul_assoc, IsUnit.mul_val_inv, hs]
      ring
    rw [key, map_sub, Polynomial.coeff_coe, coeff_trunc, if_neg hi.not_gt, zero_sub, neg_mem_iff,
      pow_succ']
    refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i ↦ ?_) i
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
      (by simp [n, g.coeff_trunc_order_mem]) (fun i ↦ ?_) i
    rw [coeff_mk]
    exact hq (by simp)
/-
**PowerSeries.IsWeierstrassDivisorAt.coeff_seq_succ_sub_seq_mem** 是 Mathlib 中的一个
定理，位于命名空间 `PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：coeff_seq_succ_sub_seq_mem (k i : Nat) : coeff i (H.seq f (k + 1) - H.seq 
f k) in I ^ k
参数：k i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isUnit_shift`：isUnit_shift : IsUnit m
k fun i => coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.seq.eq_2`：∀ {A : Type u_1} [inst : Co
mmRing A] {g : PowerSeries A} {I : Ideal A} (H : g.IsWeierstrassDivisorAt I)   (
f : PowerSeries A) (k : ℕ),   H.s…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal'`：coeff_mul_mem_
ideal_of_coeff_left_mem_ideal' (hf : forall i, coeff i f in I) : forall i, coeff
 i (f * g) in I
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.coeff_seq_mem`：coeff_seq_mem (k : Nat
) {i : Nat} (hi : i >= (g.map (Ideal.Quotient.mk I)).order.toNat) : coeff i (f -
 g * H.seq f k) in I ^ k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem coeff_seq_succ_sub_seq_mem (k i : ℕ) :
    coeff i (H.seq f (k + 1) - H.seq f k) ∈ I ^ k := by
  rw [seq, add_sub_cancel_left]
  refine coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i ↦ ?_) i
  rw [coeff_mk]
  exact H.coeff_seq_mem f k (by simp)

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.seq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：seq_zero : H.seq f 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_zero : H.seq f 0 = 0 := rfl
/-
**PowerSeries.IsWeierstrassDivisorAt.seq_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSer
ies.IsWeierstrassDivisorAt`。
形式化陈述：seq_one : H.seq f 1 = (PowerSeries.mk fun i => coeff (i + (g.map (Ideal.Qu
otient.mk I)).order.toNat) f) * H.isUnit_shift.unit⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isUnit_shift`：isUnit_shift : IsUnit m
k fun i => coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seq_one : H.seq f 1 = (PowerSeries.mk fun i ↦ coeff
    (i + (g.map (Ideal.Quotient.mk I)).order.toNat) f) * H.isUnit_shift.unit⁻¹ := by
  simp_rw [seq, mul_zero, zero_add, sub_zero]

/-- The (bundled version of) coefficient of the limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.divCoeff** 是 Mathlib 中的一个定义，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：divCoeff [IsPrecomplete I A] (i : Nat)
参数：i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (bundled version of) coefficient of the limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division.
-/
noncomputable def divCoeff [IsPrecomplete I A] (i : ℕ) :=
  Classical.indefiniteDescription _ <| IsPrecomplete.prec' (I := I)
    (fun k ↦ coeff i (H.seq f k)) fun {m} {n} hn ↦ by
      induction n, hn using Nat.le_induction with
      | base => rw [SModEq.def]
      | succ n hn ih =>
        refine ih.trans (SModEq.symm ?_)
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
        exact Ideal.pow_le_pow_right hn (H.coeff_seq_succ_sub_seq_mem f n i)

/-- The limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.div** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.
IsWeierstrassDivisorAt`。
形式化陈述：div [IsPrecomplete I A] : A⟦X⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit `q` of the
inductively constructed sequence `qₖ` in the proof of Weierstrass division.
-/
noncomputable def div [IsPrecomplete I A] : A⟦X⟧ := PowerSeries.mk fun i ↦ (H.divCoeff f i).1
/-
**PowerSeries.IsWeierstrassDivisorAt.coeff_div** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries.IsWeierstrassDivisorAt`。
形式化陈述：coeff_div [IsPrecomplete I A] (i : Nat) : coeff i (H.div f) = (H.divCoeff 
f i).1
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_div [IsPrecomplete I A] (i : ℕ) : coeff i (H.div f) = (H.divCoeff f i).1 := by
  simp [div]
/-
**PowerSeries.IsWeierstrassDivisorAt.coeff_div_sub_seq_mem** 是 Mathlib 中的一个定理，位于
命名空间 `PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：coeff_div_sub_seq_mem [IsPrecomplete I A] (k i : Nat) : coeff i (H.div f -
 (H.seq f k)) in I ^ k
参数：k i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.coeff_div`：coeff_div [IsPrecomplete I
 A] (i : Nat) : coeff i (H.div f) = (H.divCoeff f i).1
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coeff_div_sub_seq_mem [IsPrecomplete I A] (k i : ℕ) :
    coeff i (H.div f - (H.seq f k)) ∈ I ^ k := by
  simpa [coeff_div, SModEq.sub_mem] using ((H.divCoeff f i).2 k).symm

/-- The remainder `r` in the proof of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.mod** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.
IsWeierstrassDivisorAt`。
形式化陈述：mod [IsPrecomplete I A] : A[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The remainder `r` in the proof of Weierstrass division.
-/
noncomputable def mod [IsPrecomplete I A] : A[X] :=
  (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

/-- If the ring is `I`-adic complete, then `g` can be used as a divisor in Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod** 是 Mathlib
 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivi
sionAt g (H.div f) (H.mod f) I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsHausdorff.subsingleton`：∀ {R : Type u_1} [inst : CommRing R] {M : Type
 u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsHausdorff ⊤ M 
→ Subsingleton…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `PowerSeries.isWeierstrassDivisionAt_zero`：isWeierstrassDivisionAt_zero :
 IsWeierstrassDivisionAt 0 g 0 0 I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.degree_trunc_lt`：degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f
).degree < n
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod.eq_1`：∀ {A : Type u_1} [inst : Co
mmRing A] {g : PowerSeries A} {I : Ideal A} (H : g.IsWeierstrassDivisorAt I)   (
f : PowerSeries A) [inst_1 : IsPr…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `IsHausdorff.haus'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} {M
 : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Is
Hausdor…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SModEq.zero`：zero : x ≡ 0 [SMOD U] ↔ x in U
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If the ring is `I`-adic complete, then `g` can be used as a divisor in Weierstra
ss division.
-/
theorem isWeierstrassDivisionAt_div_mod [IsAdicComplete I A] :
    f.IsWeierstrassDivisionAt g (H.div f) (H.mod f) I := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · have := ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    rw [Subsingleton.elim f 0, Subsingleton.elim (H.div 0) 0, Subsingleton.elim (H.mod 0) 0]
    exact g.isWeierstrassDivisionAt_zero _
  constructor
  · exact degree_trunc_lt _ _
  · rw [mod, add_comm, ← sub_eq_iff_eq_add]
    ext i
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hi
    · rfl
    refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, show f - g * H.div f =
      f - g * (H.seq f k) - g * (H.div f - (H.seq f k)) by ring, map_sub]
    exact Ideal.sub_mem _ (H.coeff_seq_mem f k (not_lt.1 hi)) <|
      coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (H.coeff_div_sub_seq_mem f k) i

/-- If `g * q = r` for some power series `q` and some polynomial `r` whose degree is `< n`,
then `q` and `r` are all zero. This implies the uniqueness of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.eq_zero_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间
 `PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：eq_zero_of_mul_eq [IsHausdorff I A] {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree
 < (g.map (Ideal.Quotient.mk I)).order.toNat) (heq : g * q = r) : q = 0 ∧ r = 0
参数：hdeg : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat；heq : g * q = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PowerSeries.eq_X_pow_mul_shift_add_trunc`：eq_X_pow_mul_shift_add_trunc (
n : Nat) (f : R⟦X⟧) : f = X ^ n * (mk fun i => coeff (i + n) f) + (f.trunc n : R
⟦X⟧)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`：coeff_mul_
mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coeff i f in I) (hg 
: forall i <= n, coeff i g in J) : forall i <= n, …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `PowerSeries.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : 
coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `_private.Mathlib.RingTheory.PowerSeries.WeierstrassPreparation.0.PowerSe
ries.coeff_trunc_order_mem`：∀ {A : Type u_1} [inst : CommRing A] (g : PowerSerie
s A) (I : Ideal A) (i : ℕ),   ((PowerSeries.trunc ((PowerSeries.map (Ideal.Quoti
ent.mk I…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isUnit_shift`：isUnit_shift : IsUnit m
k fun i => coeff (i + (g.map (Ideal.Quotient.mk I)).order.toNat) g
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If `g * q = r` for some power series `q` and some polynomial `r` whose degree is
 `< n`,
then `q` and `r` are all zero. This implies the uniqueness of Weierstrass divisi
on.
-/
theorem eq_zero_of_mul_eq [IsHausdorff I A]
    {q : A⟦X⟧} {r : A[X]} (hdeg : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q = r) : q = 0 ∧ r = 0 := by
  suffices ∀ k i, coeff i q ∈ I ^ k by
    have hq : q = 0 := by
      ext i
      refine IsHausdorff.haus' (I := I) _ fun k ↦ ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact this _ _
    rw [hq, mul_zero, Eq.comm, Polynomial.coe_eq_zero_iff] at heq
    exact ⟨hq, heq⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [g.eq_X_pow_mul_shift_add_trunc (g.map (Ideal.Quotient.mk I)).order.toNat] at heq
    have h1 : ∀ i, coeff i r ∈ I ^ (k + 1) := fun i ↦ by
      rcases lt_or_ge i (g.map (Ideal.Quotient.mk I)).order.toNat with hi | hi
      · rw [← heq, pow_succ']
        refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i (fun j hj ↦ ?_)
          (fun j _ ↦ ih j) i le_rfl
        rw [map_add, Polynomial.coeff_coe]
        refine Ideal.add_mem _ ?_ (g.coeff_trunc_order_mem I j)
        simp_rw [coeff_X_pow_mul', if_neg (lt_of_le_of_lt hj hi).not_ge, zero_mem]
      simp_rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by simpa)), zero_mem]
    rw [add_mul, mul_comm (X ^ _), ← eq_sub_iff_add_eq] at heq
    replace heq := congr(H.isUnit_shift.unit⁻¹ * $heq)
    rw [← mul_assoc, ← mul_assoc, IsUnit.val_inv_mul, one_mul] at heq
    intro i
    rw [← coeff_X_pow_mul _ (g.map (Ideal.Quotient.mk I)).order.toNat i, heq]
    refine coeff_mul_mem_ideal_of_coeff_right_mem_ideal' (fun i ↦ ?_) _
    rw [map_sub]
    refine Ideal.sub_mem _ (h1 _) ?_
    rw [pow_succ']
    refine coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (fun i ↦ ?_) ih _
    simp_rw [Polynomial.coeff_coe, g.coeff_trunc_order_mem]

/-- If `g * q + r = g * q' + r'` for some power series `q`, `q'` and some polynomials `r`, `r'`
whose degrees are `< n`, then `q = q'` and `r = r'` are all zero.
This implies the uniqueness of Weierstrass division. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add** 是 Mathlib 中的一个定理
，位于命名空间 `PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：eq_of_mul_add_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr
 : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'.degree < (g.m
ap (Ideal.Quotient.mk I)).order.toNat) (heq : g * q + r = g * q' + r') : q = q' 
∧ r = r'
参数：hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat；hr' : r'.degree < (
g.map (Ideal.Quotient.mk I)).order.toNat；heq : g * q + r = g * q' + r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.coe_sub`：coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries
 R) = p - q
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `g * q + r = g * q' + r'` for some power series `q`, `q'` and some polynomial
s `r`, `r'`
whose degrees are `< n`, then `q = q'` and `r = r'` are all zero.
This implies the uniqueness of Weierstrass division.
-/
theorem eq_of_mul_add_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (hr' : r'.degree < (g.map (Ideal.Quotient.mk I)).order.toNat)
    (heq : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  replace heq : g * (q - q') = ↑(r' - r) := by
    rw [← eq_sub_iff_add_eq] at heq
    rw [Polynomial.coe_sub, mul_sub, heq]
    ring
  have h := H.eq_zero_of_mul_eq (lt_of_le_of_lt (r'.degree_sub_le r) (max_lt hr' hr)) heq
  simp_rw [sub_eq_zero] at h
  exact ⟨h.1, h.2.symm⟩

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.div_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSer
ies.IsWeierstrassDivisorAt`。
形式化陈述：div_add [IsAdicComplete I A] : H.div (f + f') = H.div f + H.div f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.add`：add {f' q' r'} (H : f.IsWeierst
rassDivisionAt g q r I) (H' : f'.IsWeierstrassDivisionAt g q' r' I) : (f + f').I
sWeierstrassDivisionAt g (q +…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
-/
theorem div_add [IsAdicComplete I A] : H.div (f + f') = H.div f + H.div f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.div_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：div_smul [IsAdicComplete I A] : H.div (a • f) = a • H.div f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.smul`：smul (H : f.IsWeierstrassDivis
ionAt g q r I) (a : A) : (a • f).IsWeierstrassDivisionAt g (a • q) (a • r) I
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
-/
theorem div_smul [IsAdicComplete I A] : H.div (a • f) = a • H.div f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).1

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：div_zero [IsAdicComplete I A] : H.div 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.div_smul`：div_smul [IsAdicComplete I 
A] : H.div (a • f) = a • H.div f
-/
theorem div_zero [IsAdicComplete I A] : H.div 0 = 0 := by
  simpa using H.div_smul 0 0

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.mod_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSer
ies.IsWeierstrassDivisorAt`。
形式化陈述：mod_add [IsAdicComplete I A] : H.mod (f + f') = H.mod f + H.mod f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.add`：add {f' q' r'} (H : f.IsWeierst
rassDivisionAt g q r I) (H' : f'.IsWeierstrassDivisionAt g q' r' I) : (f + f').I
sWeierstrassDivisionAt g (q +…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
-/
theorem mod_add [IsAdicComplete I A] : H.mod (f + f') = H.mod f + H.mod f' := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).add (H.isWeierstrassDivisionAt_div_mod f')
  have H2 := H.isWeierstrassDivisionAt_div_mod (f + f')
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.mod_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：mod_smul [IsAdicComplete I A] : H.mod (a • f) = a • H.mod f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.smul`：smul (H : f.IsWeierstrassDivis
ionAt g q r I) (a : A) : (a • f).IsWeierstrassDivisionAt g (a • q) (a • r) I
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
-/
theorem mod_smul [IsAdicComplete I A] : H.mod (a • f) = a • H.mod f := by
  have H1 := (H.isWeierstrassDivisionAt_div_mod f).smul a
  have H2 := H.isWeierstrassDivisionAt_div_mod (a • f)
  exact (H.eq_of_mul_add_eq_mul_add H2.degree_lt H1.degree_lt
    (H2.eq_mul_add.symm.trans H1.eq_mul_add)).2

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.mod_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassDivisorAt`。
形式化陈述：mod_zero [IsAdicComplete I A] : H.mod 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod.congr_simp`：∀ {A : Type u_1} [ins
t : CommRing A] {g g_1 : PowerSeries A} (e_g : g = g_1) {I I_1 : Ideal A} (e_I :
 I = I_1)   (H : g.IsWeierstrassDivisor…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod_smul`：mod_smul [IsAdicComplete I 
A] : H.mod (a • f) = a • H.mod f
-/
theorem mod_zero [IsAdicComplete I A] : H.mod 0 = 0 := by
  simpa using H.mod_smul 0 0

/-- The remainder map `PowerSeries.IsWeierstrassDivisorAt.mod` induces a linear map
`A⟦X⟧ / (g) →ₗ[A] A[X]`. -/
/-
**PowerSeries.IsWeierstrassDivisorAt.mod'** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries
.IsWeierstrassDivisorAt`。
形式化陈述：mod' [IsAdicComplete I A] : A⟦X⟧ ⧸ Ideal.span {g} ->ₗ[A] A[X] where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The remainder map `PowerSeries.IsWeierstrassDivisorAt.mod` induces a linear map
`A⟦X⟧ / (g) →ₗ[A] A[X]`.
-/
noncomputable def mod' [IsAdicComplete I A] : A⟦X⟧ ⧸ Ideal.span {g} →ₗ[A] A[X] where
  toFun := Quotient.lift (fun f ↦ H.mod f) fun f f' hf ↦ by
    have hf := (Submodule.quotientRel_def (p := Ideal.span {g})).mp hf
    rw [Ideal.mem_span_singleton'] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨hf1, hf2⟩ := H.isWeierstrassDivisionAt_div_mod f
    obtain ⟨hf'1, hf'2⟩ := H.isWeierstrassDivisionAt_div_mod f'
    rw [eq_sub_iff_add_eq, hf2, hf'2, ← add_assoc, mul_comm, ← mul_add] at ha
    exact (H.eq_of_mul_add_eq_mul_add hf'1 hf1 ha).2.symm
  map_add' f f' := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨f', rfl⟩ := Ideal.Quotient.mk_surjective f'
    exact H.mod_add f f'
  map_smul' a f := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    exact H.mod_smul a f

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.mod'_mk_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `P
owerSeries.IsWeierstrassDivisorAt`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {g : PowerSeries A} {I : Ideal A} (H 
: g.IsWeierstrassDivisorAt I)   [inst_1 : IsAdicComplete I A] {f : PowerSeries A
}, H.mod' ((Ideal.Quotient.mk (Ideal.span {g})) f) = H.mod f
参数：H : g.IsWeierstrassDivisorAt I；(Ideal.Quotient.mk (Ideal.span {g})) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem mod'_mk_eq_mod [IsAdicComplete I A] {f : A⟦X⟧} :
    H.mod' (Ideal.Quotient.mk _ f) = H.mod f := rfl
/-
**PowerSeries.IsWeierstrassDivisorAt.div_coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：div_coe_eq_zero [IsAdicComplete I A] {r : A[X]} (hr : r.degree < (g.map (I
deal.Quotient.mk I)).order.toNat) : H.div r = 0
参数：hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem div_coe_eq_zero [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.div r = 0 := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).1
/-
**PowerSeries.IsWeierstrassDivisorAt.mod_coe_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：mod_coe_eq_self [IsAdicComplete I A] {r : A[X]} (hr : r.degree < (g.map (I
deal.Quotient.mk I)).order.toNat) : H.mod r = r
参数：hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mod_coe_eq_self [IsAdicComplete I A] {r : A[X]}
    (hr : r.degree < (g.map (Ideal.Quotient.mk I)).order.toNat) : H.mod r = r := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivisionAt_div_mod r
  exact (H.eq_of_mul_add_eq_mul_add (q := H.div r) (q' := 0) h1 hr (by simpa using h2.symm)).2

@[simp]
/-
**PowerSeries.IsWeierstrassDivisorAt.mk_mod'_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.IsWeierstrassDivisorAt`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {g : PowerSeries A} {I : Ideal A} (H 
: g.IsWeierstrassDivisorAt I)   [inst_1 : IsAdicComplete I A] {f : PowerSeries A
 ⧸ Ideal.span {g}},   (Ideal.Quotient.mk (Ideal.span {g})) ↑(H.mod' f) = f
参数：H : g.IsWeierstrassDivisorAt I；Ideal.Quotient.mk (Ideal.span {g})；H.mod' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod'_mk_eq_mod`：∀ {A : Type u_1} [ins
t : CommRing A] {g : PowerSeries A} {I : Ideal A} (H : g.IsWeierstrassDivisorAt 
I)   [inst_1 : IsAdicComplete I A] {f :…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
-/
theorem mk_mod'_eq_self [IsAdicComplete I A] {f : A⟦X⟧ ⧸ Ideal.span {g}} :
    Ideal.Quotient.mk _ (H.mod' f : A⟦X⟧) = f := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mod'_mk_eq_mod, Eq.comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
  use H.div f
  rw [eq_sub_iff_add_eq, mul_comm, (H.isWeierstrassDivisionAt_div_mod f).2.symm]

end IsWeierstrassDivisorAt

section Equiv

variable {g : A[X]} {I : Ideal A} (H : g.IsDistinguishedAt I) [IsAdicComplete I A]
include H

/-- A distinguished polynomial `g` induces a natural isomorphism `A[X] / (g) ≃ₐ[A] A⟦X⟧ / (g)`. -/
@[simps! apply symm_apply]
/-
**PowerSeries._root_.Polynomial.IsDistinguishedAt.algEquivQuotient** 是 Mathlib 中
的一个定义，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distinguished polynomial `g` induces a natural isomorphism `A[X] / (g) ≃ₐ[A] A
⟦X⟧ / (g)`.
-/
noncomputable def _root_.Polynomial.IsDistinguishedAt.algEquivQuotient :
    (A[X] ⧸ Ideal.span {g}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)} where
  __ := Ideal.quotientMapₐ _ (Polynomial.coeToPowerSeries.algHom A) fun a ha ↦ by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [Ideal.mem_comap, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
      map_id, id_eq, Ideal.mem_span_singleton']
    exact ⟨b, by simp [← hb]⟩
  invFun := Ideal.Quotient.mk _ ∘ H.isWeierstrassDivisorAt'.mod'
  left_inv f := by
    rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton A[X] := inferInstance
      have : Subsingleton (A[X] ⧸ Ideal.span {g}) := Quot.Subsingleton
      exact Subsingleton.elim _ _
    have hI : I ≠ ⊤ := by
      rintro rfl
      exact not_subsingleton _ ‹IsAdicComplete ⊤ A›.toIsHausdorff.subsingleton
    have := Ideal.Quotient.nontrivial_iff.mpr hI
    obtain ⟨f, hfdeg, rfl⟩ : ∃ r : A[X], r.degree < g.degree ∧ Ideal.Quotient.mk _ r = f := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
      refine ⟨f %ₘ g, Polynomial.degree_modByMonic_lt f H.monic, ?_⟩
      rw [Eq.comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
      exact ⟨f /ₘ g, by rw [Polynomial.modByMonic_eq_sub_mul_div]; ring⟩
    have h1 : g.degree = ((g : A⟦X⟧).map (Ideal.Quotient.mk I)).order.toNat := by
      convert!
        H.degree_eq_coe_lift_order_map g 1 (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one])
          (by simp)
      exact (ENat.lift_eq_toNat_of_lt_top _).symm
    dsimp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
    exact ⟨0, by simp [H.isWeierstrassDivisorAt'.mod_coe_eq_self (hfdeg.trans_eq h1)]⟩
  right_inv f := by exact H.isWeierstrassDivisorAt'.mk_mod'_eq_self

end Equiv

end IsWeierstrassDivisorAt

section IsLocalRing

variable [IsLocalRing A] (a : A) (f f' g : A⟦X⟧)

variable {g} in
/-- **Weierstrass division** ([washington_cyclotomic], Proposition 7.2): let `f`, `g` be
power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the image of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degree `< n`, such that
`f = g * q + r`. -/
/-
**PowerSeries.exists_isWeierstrassDivision** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：exists_isWeierstrassDivision [IsAdicComplete (IsLocalRing.maximalIdeal A) 
A] (hg : g.map (IsLocalRing.residue A) != 0) : exists q r, f.IsWeierstrassDivisi
on g q r
参数：IsLocalRing.maximalIdeal A；hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I

--- 原说明 ---
**Weierstrass division** ([washington_cyclotomic], Proposition 7.2): let `f`, `g
` be
power series over a complete local ring, such that
the image of `g` in the residue field is not zero. Let `n` be the order of the i
mage of `g` in the
residue field. Then there exists a power series `q` and a polynomial `r` of degr
ee `< n`, such that
`f = g * q + r`.
-/
theorem exists_isWeierstrassDivision [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hg : g.map (IsLocalRing.residue A) ≠ 0) : ∃ q r, f.IsWeierstrassDivision g q r :=
  ⟨_, _, (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f⟩

-- Unfortunately there is no Unicode subscript `w`.

/-- The quotient `q` in Weierstrass division, denoted by `f /ʷ g`. Note that when the image of
`g` in the residue field is zero, this is defined to be zero. -/
/-
**PowerSeries.weierstrassDiv** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassDiv [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A⟦X⟧
参数：IsLocalRing.maximalIdeal A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…

--- 原说明 ---
The quotient `q` in Weierstrass division, denoted by `f /ʷ g`. Note that when th
e image of
`g` in the residue field is zero, this is defined to be zero.
-/
noncomputable def weierstrassDiv [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A⟦X⟧ :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).div f
  else
    0

/-- The remainder `r` in Weierstrass division, denoted by `f %ʷ g`. Note that when the image of
`g` in the residue field is zero, this is defined to be zero. -/
/-
**PowerSeries.weierstrassMod** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassMod [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A[X]
参数：IsLocalRing.maximalIdeal A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…

--- 原说明 ---
The remainder `r` in Weierstrass division, denoted by `f %ʷ g`. Note that when t
he image of
`g` in the residue field is zero, this is defined to be zero.
-/
noncomputable def weierstrassMod [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : A[X] :=
  open scoped Classical in
  if hg : g.map (IsLocalRing.residue A) ≠ 0 then
    (IsWeierstrassDivisor.of_map_ne_zero hg).mod f
  else
    0

@[inherit_doc]
infixl:70 " /ʷ " => weierstrassDiv

@[inherit_doc]
infixl:70 " %ʷ " => weierstrassMod

@[simp]
/-
**PowerSeries.weierstrassDiv_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassDiv_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
 f /ʷ 0 = 0
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.weierstrassDiv.eq_1`：∀ {A : Type u_1} [inst : CommRing A] [i
nst_1 : IsLocalRing A] (f g : PowerSeries A)   [inst_2 : IsPrecomplete (IsLocalR
ing.maximalIdeal A) A…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem weierstrassDiv_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f /ʷ 0 = 0 := by
  rw [weierstrassDiv, dif_neg (by simp)]

alias weierstrassDiv_zero := weierstrassDiv_zero_right

@[simp]
/-
**PowerSeries.weierstrassMod_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassMod_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
 f %ʷ 0 = 0
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.weierstrassMod.eq_1`：∀ {A : Type u_1} [inst : CommRing A] [i
nst_1 : IsLocalRing A] (f g : PowerSeries A)   [inst_2 : IsPrecomplete (IsLocalR
ing.maximalIdeal A) A…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem weierstrassMod_zero_right [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : f %ʷ 0 = 0 := by
  rw [weierstrassMod, dif_neg (by simp)]

alias weierstrassMod_zero := weierstrassMod_zero_right
/-
**PowerSeries.degree_weierstrassMod_lt** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：degree_weierstrassMod_lt [IsPrecomplete (IsLocalRing.maximalIdeal A) A] : 
(f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat
参数：IsLocalRing.maximalIdeal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.weierstrassMod.eq_1`：∀ {A : Type u_1} [inst : CommRing A] [i
nst_1 : IsLocalRing A] (f g : PowerSeries A)   [inst_2 : IsPrecomplete (IsLocalR
ing.maximalIdeal A) A…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `PowerSeries.degree_trunc_lt`：degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f
).degree < n
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
-/
theorem degree_weierstrassMod_lt [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    (f %ʷ g).degree < (g.map (IsLocalRing.residue A)).order.toNat := by
  rw [weierstrassMod]
  split_ifs with hg
  · exact degree_trunc_lt _ _
  · nontriviality A
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _

section

variable {g} (hg : g.map (IsLocalRing.residue A) ≠ 0)
include hg

/-
**PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod** 是 Mathlib 中的
一个定理，位于命名空间 `PowerSeries`。
形式化陈述：isWeierstrassDivision_weierstrassDiv_weierstrassMod [IsAdicComplete (IsLoc
alRing.maximalIdeal A) A] : f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g)
参数：IsLocalRing.maximalIdeal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `PowerSeries.IsWeierstrassDivision.congr_simp`：∀ {A : Type u_1} [inst : C
ommRing A] (f f_1 : PowerSeries A),   f = f_1 →     ∀ (g g_1 : PowerSeries A),  
     g = g_1 →         ∀ (q q_1 : …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
-/
theorem isWeierstrassDivision_weierstrassDiv_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f.IsWeierstrassDivision g (f /ʷ g) (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact (IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f
/-
**PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod** 是 Mathlib 中的一个定理，位于命名空间
 `PowerSeries`。
形式化陈述：eq_mul_weierstrassDiv_add_weierstrassMod [IsAdicComplete (IsLocalRing.maxi
malIdeal A) A] : f = g * (f /ʷ g) + (f %ʷ g)
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.isWeierstrassDivisionAt_div_mod`：isWe
ierstrassDivisionAt_div_mod [IsAdicComplete I A] : f.IsWeierstrassDivisionAt g (
H.div f) (H.mod f) I
-/
theorem eq_mul_weierstrassDiv_add_weierstrassMod
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    f = g * (f /ʷ g) + (f %ʷ g) := by
  simp_rw [weierstrassDiv, weierstrassMod, dif_pos hg]
  exact ((IsWeierstrassDivisor.of_map_ne_zero hg).isWeierstrassDivisionAt_div_mod f).2

variable {f} in
/-- The quotient `q` and the remainder `r` in the Weierstrass division are unique.

This result is stated using two `PowerSeries.IsWeierstrassDivision` assertions, and only requires
the ring being Hausdorff with respect to the maximal ideal. If you want `q` and `r` equal to
`f /ʷ g` and `f %ʷ g`, use `PowerSeries.IsWeierstrassDivision.unique`
instead, which requires the ring being complete with respect to the maximal ideal. -/
/-
**PowerSeries.IsWeierstrassDivision.elim** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.
IsWeierstrassDivision`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {f g : Power
Series A},   (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0 →     ∀ [IsHausdorf
f (IsLocalRing.maximalIdeal A) A] {q q' : PowerSeries A} {r r' : Polynomial A}, 
      f.IsWeierstrassDivision g q r → f.IsWeierstrassDivision g q' r' → q = q' ∧
 r = r'
参数：PowerSeries.map (IsLocalRing.residue A)；IsLocalRing.maximalIdeal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.eq_of_mul_add_eq_mul_add`：eq_of_mul_a
dd_eq_mul_add [IsHausdorff I A] {q q' : A⟦X⟧} {r r' : A[X]} (hr : r.degree < (g.
map (Ideal.Quotient.mk I)).order.toNat) (hr' : r'…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…

--- 原说明 ---
The quotient `q` and the remainder `r` in the Weierstrass division are unique.

This result is stated using two `PowerSeries.IsWeierstrassDivision` assertions, 
and only requires
the ring being Hausdorff with respect to the maximal ideal. If you want `q` and 
`r` equal to
`f /ʷ g` and `f %ʷ g`, use `PowerSeries.IsWeierstrassDivision.unique`
instead, which requires the ring being complete with respect to the maximal idea
l.
-/
theorem IsWeierstrassDivision.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q q' : A⟦X⟧} {r r' : A[X]}
    (H : f.IsWeierstrassDivision g q r) (H2 : f.IsWeierstrassDivision g q' r') : q = q' ∧ r = r' :=
  (IsWeierstrassDivisor.of_map_ne_zero hg).eq_of_mul_add_eq_mul_add H.1 H2.1 (H.2.symm.trans H2.2)

/-- If `q` and `r` are quotient and remainder in the Weierstrass division `0 / g`, then they are
equal to `0`. -/
/-
**PowerSeries.IsWeierstrassDivision.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeri
es.IsWeierstrassDivision`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g : PowerSe
ries A},   (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0 →     ∀ [IsHausdorff 
(IsLocalRing.maximalIdeal A) A] {q : PowerSeries A} {r : Polynomial A},       Po
werSeries.IsWeierstrassDivision 0 g q r → q = 0 ∧ r = 0
参数：PowerSeries.map (IsLocalRing.residue A)；IsLocalRing.maximalIdeal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivision.elim`：∀ {A : Type u_1} [inst : CommRin
g A] [inst_1 : IsLocalRing A] {f g : PowerSeries A},   (PowerSeries.map (IsLocal
Ring.residue A)) g ≠ 0 →    …
· 使用定理 `PowerSeries.isWeierstrassDivisionAt_zero`：isWeierstrassDivisionAt_zero :
 IsWeierstrassDivisionAt 0 g 0 0 I

--- 原说明 ---
If `q` and `r` are quotient and remainder in the Weierstrass division `0 / g`, t
hen they are
equal to `0`.
-/
theorem IsWeierstrassDivision.eq_zero [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : IsWeierstrassDivision 0 g q r) : q = 0 ∧ r = 0 :=
  H.elim hg (g.isWeierstrassDivisionAt_zero _)

variable {f} in
/-- If `q` and `r` are quotient and remainder in the Weierstrass division `f / g`, then they are
equal to `f /ʷ g` and `f %ʷ g`. -/
/-
**PowerSeries.IsWeierstrassDivision.unique** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s.IsWeierstrassDivision`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {f g : Power
Series A},   (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0 →     ∀ [inst_2 : I
sAdicComplete (IsLocalRing.maximalIdeal A) A] {q : PowerSeries A} {r : Polynomia
l A},       f.IsWeierstrassDivision g q r → q = f /ʷ g ∧ r = f %ʷ g
参数：PowerSeries.map (IsLocalRing.residue A)；IsLocalRing.maximalIdeal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivision.elim`：∀ {A : Type u_1} [inst : CommRin
g A] [inst_1 : IsLocalRing A] {f g : PowerSeries A},   (PowerSeries.map (IsLocal
Ring.residue A)) g ≠ 0 →    …
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod`：isWeier
strassDivision_weierstrassDiv_weierstrassMod [IsAdicComplete (IsLocalRing.maxima
lIdeal A) A] : f.IsWeierstrassDivision g (f /ʷ g) (f …

--- 原说明 ---
If `q` and `r` are quotient and remainder in the Weierstrass division `f / g`, t
hen they are
equal to `f /ʷ g` and `f %ʷ g`.
-/
theorem IsWeierstrassDivision.unique [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {q : A⟦X⟧} {r : A[X]}
    (H : f.IsWeierstrassDivision g q r) : q = f /ʷ g ∧ r = f %ʷ g :=
  H.elim hg (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hg)

end

@[simp]
/-
**PowerSeries.add_weierstrassDiv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：add_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : (f + 
f') /ʷ g = f /ʷ g + f' /ʷ g
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.div_add`：div_add [IsAdicComplete I A]
 : H.div (f + f') = H.div f + H.div f'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem add_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') /ʷ g = f /ʷ g + f' /ʷ g := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
/-
**PowerSeries.smul_weierstrassDiv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：smul_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : (a •
 f) /ʷ g = a • (f /ʷ g)
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.div_smul`：div_smul [IsAdicComplete I 
A] : H.div (a • f) = a • H.div f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_weierstrassDiv [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) /ʷ g = a • (f /ʷ g) := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

@[simp]
/-
**PowerSeries.weierstrassDiv_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassDiv_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
 0 /ʷ g = 0
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.div_zero`：div_zero [IsAdicComplete I 
A] : H.div 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem weierstrassDiv_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 /ʷ g = 0 := by
  simp_rw [weierstrassDiv]
  split_ifs <;> simp

alias zero_weierstrassDiv := weierstrassDiv_zero_left

@[simp]
/-
**PowerSeries.add_weierstrassMod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：add_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : (f + 
f') %ʷ g = f %ʷ g + f' %ʷ g
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod_add`：mod_add [IsAdicComplete I A]
 : H.mod (f + f') = H.mod f + H.mod f'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem add_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (f + f') %ʷ g = f %ʷ g + f' %ʷ g := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
/-
**PowerSeries.smul_weierstrassMod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：smul_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : (a •
 f) %ʷ g = a • (f %ʷ g)
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod_smul`：mod_smul [IsAdicComplete I 
A] : H.mod (a • f) = a • H.mod f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_weierstrassMod [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    (a • f) %ʷ g = a • (f %ʷ g) := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

@[simp]
/-
**PowerSeries.weierstrassMod_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassMod_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
 0 %ʷ g = 0
参数：IsLocalRing.maximalIdeal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassDivisor.of_map_ne_zero`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} [inst_1 : IsLocalRing A],   (PowerSeries.map (
IsLocalRing.residue A)) g ≠ 0 → g.IsW…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.IsWeierstrassDivisorAt.mod_zero`：mod_zero [IsAdicComplete I 
A] : H.mod 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem weierstrassMod_zero_left [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : 0 %ʷ g = 0 := by
  simp_rw [weierstrassMod]
  split_ifs <;> simp

alias zero_weierstrassMod := weierstrassMod_zero_left

end IsLocalRing

/-!

## Weierstrass preparation theorem

-/

/-- If `f` is a polynomial over `A`, `g` and `h` are power series over `A`,
then `PowerSeries.IsWeierstrassFactorizationAt g f h I` is a `Prop` which asserts that `f` is
distinguished at `I`, `h` is a unit, such that `g = f * h`. -/
@[mk_iff]
/-
**PowerSeries.IsWeierstrassFactorizationAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `PowerSer
ies`。
形式化陈述：{A : Type u_1} → [inst : CommRing A] → PowerSeries A → Polynomial A → Powe
rSeries A → Ideal A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a polynomial over `A`, `g` and `h` are power series over `A`,
then `PowerSeries.IsWeierstrassFactorizationAt g f h I` is a `Prop` which assert
s that `f` is
distinguished at `I`, `h` is a unit, such that `g = f * h`.
-/
structure IsWeierstrassFactorizationAt (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) (I : Ideal A) : Prop where
  isDistinguishedAt : f.IsDistinguishedAt I
  isUnit : IsUnit h
  eq_mul : g = f * h

/-- Version of `PowerSeries.IsWeierstrassFactorizationAt` for local rings with respect to
its maximal ideal. -/
/-
**PowerSeries.IsWeierstrassFactorization** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSerie
s`。
形式化陈述：IsWeierstrassFactorization (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [IsLocalRing A
] : Prop
参数：g : A⟦X⟧；f : A[X]；h : A⟦X⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `PowerSeries.IsWeierstrassFactorizationAt` for local rings with respe
ct to
its maximal ideal.
-/
abbrev IsWeierstrassFactorization (g : A⟦X⟧) (f : A[X]) (h : A⟦X⟧) [IsLocalRing A] : Prop :=
  g.IsWeierstrassFactorizationAt f h (IsLocalRing.maximalIdeal A)

namespace IsWeierstrassFactorizationAt

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} {I : Ideal A} (H : g.IsWeierstrassFactorizationAt f h I)
include H

/-
**PowerSeries.IsWeierstrassFactorizationAt.map_ne_zero_of_ne_top** 是 Mathlib 中的一
个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorizationAt`。
形式化陈述：map_ne_zero_of_ne_top (hI : I != ⊤) : g.map (Ideal.Quotient.mk I) != 0
参数：hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.polynomial_map_coe`：polynomial_map_coe {U V : Type*} [CommSem
iring U] [CommSemiring V] {φ : U ->+* V} {f : Polynomial U} : Polynomial.map φ f
 = PowerSeries.map …
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `Polynomial.IsDistinguishedAt.monic`：∀ {R : Type u_1} [inst : CommRing R]
 {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Monic
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
-/
theorem map_ne_zero_of_ne_top (hI : I ≠ ⊤) : g.map (Ideal.Quotient.mk I) ≠ 0 := by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [congr(map (Ideal.Quotient.mk I) $(H.eq_mul)), map_mul, ← Polynomial.polynomial_map_coe, ne_eq,
    (H.isUnit.map _).mul_left_eq_zero]
  exact_mod_cast f.map_monic_ne_zero (f := Ideal.Quotient.mk I) H.isDistinguishedAt.monic
/-
**PowerSeries.IsWeierstrassFactorizationAt.degree_eq_coe_lift_order_map_of_ne_to
p** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorizationAt`。
形式化陈述：degree_eq_coe_lift_order_map_of_ne_top (hI : I != ⊤) : f.degree = (g.map (
Ideal.Quotient.mk I)).order.lift (order_finite_iff_ne_zero.2 (H.map_ne_zero_of_n
e_top hI))
参数：hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.IsDistinguishedAt.degree_eq_coe_lift_order_map`：degree_eq_coe
_lift_order_map (distinguish : g.IsDistinguishedAt I) (notMem : PowerSeries.cons
tantCoeff h ∉ I) (eq : f = g * h) : g.degree = …
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.isUnit_iff_constantCoeff`：isUnit_iff_constantCoeff {φ : R⟦X⟧
} : IsUnit φ ↔ IsUnit (constantCoeff φ)
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
-/
theorem degree_eq_coe_lift_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.degree = (g.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (H.map_ne_zero_of_ne_top hI)) := by
  refine H.isDistinguishedAt.degree_eq_coe_lift_order_map g h ?_ H.eq_mul
  contrapose hI
  exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_iff_constantCoeff.1 H.isUnit)
/-
**PowerSeries.IsWeierstrassFactorizationAt.natDegree_eq_toNat_order_map_of_ne_to
p** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorizationAt`。
形式化陈述：natDegree_eq_toNat_order_map_of_ne_top (hI : I != ⊤) : f.natDegree = (g.ma
p (Ideal.Quotient.mk I)).order.toNat
参数：hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.map_ne_zero_of_ne_top`：map_ne_z
ero_of_ne_top (hI : I != ⊤) : g.map (Ideal.Quotient.mk I) != 0
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.degree_eq_coe_lift_order_map_of
_ne_top`：degree_eq_coe_lift_order_map_of_ne_top (hI : I != ⊤) : f.degree = (g.ma
p (Ideal.Quotient.mk I)).order.lift (order_finite_iff_ne_zero.2 (H.ma…
· 使用定理 `ENat.lift_eq_toNat_of_lt_top`：lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x
 < ⊤) : x.lift hx = x.toNat
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
-/
theorem natDegree_eq_toNat_order_map_of_ne_top (hI : I ≠ ⊤) :
    f.natDegree = (g.map (Ideal.Quotient.mk I)).order.toNat := by
  rw [Polynomial.natDegree, H.degree_eq_coe_lift_order_map_of_ne_top hI,
    ENat.lift_eq_toNat_of_lt_top]
  exact WithBot.unbotD_coe _ _

/-- If `g = f * h` is a Weierstrass factorization, then there is a
natural isomorphism `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)`. -/
@[simps! apply]
/-
**PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient** 是 Mathlib 中的一个定义，位
于命名空间 `PowerSeries.IsWeierstrassFactorizationAt`。
形式化陈述：algEquivQuotient [IsAdicComplete I A] : (A[X] ⧸ Ideal.span {f}) ≃ₐ[A] A⟦X⟧
 ⧸ Ideal.span {g}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…

--- 原说明 ---
If `g = f * h` is a Weierstrass factorization, then there is a
natural isomorphism `A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)`.
-/
noncomputable def algEquivQuotient [IsAdicComplete I A] :
    (A[X] ⧸ Ideal.span {f}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {g} :=
  H.isDistinguishedAt.algEquivQuotient.trans <| Ideal.quotientEquivAlgOfEq A <|
    by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

@[simp]
/-
**PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient_symm_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorizationAt`。
形式化陈述：algEquivQuotient_symm_apply [IsAdicComplete I A] (x : A⟦X⟧ ⧸ Ideal.span {g
}) : H.algEquivQuotient.symm x = Ideal.Quotient.mk _ (H.isDistinguishedAt.isWeie
rstrassDivisorAt'.mod' <| Ideal.quotientEquivAlgOfEq A (by rw [H.eq_mul, Ideal.s
pan_singleton_mul_right_unit H.isUnit]) x)
参数：x : A⟦X⟧ ⧸ Ideal.span {g}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.IsDistinguishedAt.isWeierstrassDivisorAt'`：∀ {A : Type u_1} [
inst : CommRing A] {g : Polynomial A} {I : Ideal A},   g.IsDistinguishedAt I → ∀
 [IsHausdorff I A], (↑g).IsWeierstrassDivi…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientEquivAlgOfEq_symm`：quotientEquivAlgOfEq_symm {I J : Ideal 
A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) : (quotientEquivAlgOfEq R₁ h).symm 
= quotientEquivAlgOfE…
· 使用定理 `Polynomial.IsDistinguishedAt.algEquivQuotient_symm_apply`：∀ {A : Type u_
1} [inst : CommRing A] {g : Polynomial A} {I : Ideal A} (H : g.IsDistinguishedAt
 I)   [inst_1 : IsAdicComplete I A] (a : Power…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivQuotient_symm_apply [IsAdicComplete I A] (x : A⟦X⟧ ⧸ Ideal.span {g}) :
    H.algEquivQuotient.symm x = Ideal.Quotient.mk _
      (H.isDistinguishedAt.isWeierstrassDivisorAt'.mod' <| Ideal.quotientEquivAlgOfEq A
        (by rw [H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]) x) := by
  simp [algEquivQuotient]
/-
**PowerSeries.IsWeierstrassFactorizationAt.mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries.IsWeierstrassFactorizationAt`。
形式化陈述：mul {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizatio
nAt f' h' I) : (g * g').IsWeierstrassFactorizationAt (f * f') (h * h') I
参数：H' : g'.IsWeierstrassFactorizationAt f' h' I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.IsDistinguishedAt.mul`：mul {f f' : R[X]} {I : Ideal R} (hf : 
f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) : (f * f').IsDistinguished
At I
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `Polynomial.coe_mul`：coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem mul {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) :
    (g * g').IsWeierstrassFactorizationAt (f * f') (h * h') I :=
  ⟨H.isDistinguishedAt.mul H'.isDistinguishedAt, H.isUnit.mul H'.isUnit, by
    rw [H.eq_mul, H'.eq_mul, Polynomial.coe_mul]; ring⟩
/-
**PowerSeries.IsWeierstrassFactorizationAt.smul** 是 Mathlib 中的一个定理，位于命名空间 `Power
Series.IsWeierstrassFactorizationAt`。
形式化陈述：smul {a : A} (ha : IsUnit a) : (a • g).IsWeierstrassFactorizationAt f (a •
 h) I
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul {a : A} (ha : IsUnit a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I := by
  refine ⟨H.isDistinguishedAt, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (ha.map _).mul H.isUnit
  · simp [H.eq_mul]

end IsWeierstrassFactorizationAt

variable [IsLocalRing A]

namespace IsWeierstrassFactorization

variable {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
include H

/-
**PowerSeries.IsWeierstrassFactorization.map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries.IsWeierstrassFactorization`。
形式化陈述：map_ne_zero : g.map (IsLocalRing.residue A) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.map_ne_zero_of_ne_top`：map_ne_z
ero_of_ne_top (hI : I != ⊤) : g.map (Ideal.Quotient.mk I) != 0
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem map_ne_zero : g.map (IsLocalRing.residue A) ≠ 0 :=
  H.map_ne_zero_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)
/-
**PowerSeries.IsWeierstrassFactorization.degree_eq_coe_lift_order_map** 是 Mathli
b 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorization`。
形式化陈述：degree_eq_coe_lift_order_map : f.degree = (g.map (IsLocalRing.residue A)).
order.lift (order_finite_iff_ne_zero.2 H.map_ne_zero)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.degree_eq_coe_lift_order_map_of
_ne_top`：degree_eq_coe_lift_order_map_of_ne_top (hI : I != ⊤) : f.degree = (g.ma
p (Ideal.Quotient.mk I)).order.lift (order_finite_iff_ne_zero.2 (H.ma…
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem degree_eq_coe_lift_order_map : f.degree = (g.map (IsLocalRing.residue A)).order.lift
    (order_finite_iff_ne_zero.2 H.map_ne_zero) :=
  H.degree_eq_coe_lift_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)
/-
**PowerSeries.IsWeierstrassFactorization.natDegree_eq_toNat_order_map** 是 Mathli
b 中的一个定理，位于命名空间 `PowerSeries.IsWeierstrassFactorization`。
形式化陈述：natDegree_eq_toNat_order_map : f.natDegree = (g.map (IsLocalRing.residue A
)).order.toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.natDegree_eq_toNat_order_map_of
_ne_top`：natDegree_eq_toNat_order_map_of_ne_top (hI : I != ⊤) : f.natDegree = (g
.map (Ideal.Quotient.mk I)).order.toNat
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem natDegree_eq_toNat_order_map :
    f.natDegree = (g.map (IsLocalRing.residue A)).order.toNat :=
  H.natDegree_eq_toNat_order_map_of_ne_top (Ideal.IsMaximal.ne_top inferInstance)

end IsWeierstrassFactorization

/-
**PowerSeries.IsWeierstrassDivision.isUnit_of_map_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `PowerSeries.IsWeierstrassDivision`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g q : Power
Series A} {r : Polynomial A},   (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0 
→     (PowerSeries.X ^ ((PowerSeries.map (IsLocalRing.residue A)) g).order.toNat
).IsWeierstrassDivision g q r → IsUnit q
参数：PowerSeries.map (IsLocalRing.residue A)；PowerSeries.X ^ ((PowerSeries.map (Is
LocalRing.residue A)) g).order.toNat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.isUnit_iff_constantCoeff`：isUnit_iff_constantCoeff {φ : R⟦X⟧
} : IsUnit φ ↔ IsUnit (constantCoeff φ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalRing.instIsLocalHomResidueFieldRingHomResidue`：∀ (R : Type u_1) [
inst : CommRing R] [inst_1 : IsLocalRing R], IsLocalHom (IsLocalRing.residue R)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `PowerSeries.coeff_map`：coeff_map (n : Nat) (φ : R⟦X⟧) : coeff n (map f φ
) = f (coeff n φ)
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0
· 使用定理 `ENat.lt_lift_iff`：∀ {x : ℕ} {n : ℕ∞} {h : n < ⊤}, x < n.lift h ↔ ↑x < n
· 使用定理 `ENat.lift_eq_toNat_of_lt_top`：lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x
 < ⊤) : x.lift hx = x.toNat
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_congr`：∀ {A : Type u_1} [inst : AddC
ancelMonoid A] [inst_1 : Finset.HasAntidiagonal A] {p q : A × A} {n : A},   p ∈ 
Finset.HasAntidiagonal.antidiag…
（共 46 条，此处仅展示前 30 条）
-/
theorem IsWeierstrassDivision.isUnit_of_map_ne_zero
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    IsUnit q := by
  obtain ⟨H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat, H2⟩ := H
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  replace H2 := congr(coeff n (($H2).map (IsLocalRing.residue A)))
  simp_rw [map_pow, map_X, coeff_X_pow_self, map_add, map_mul, coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt H1, map_zero, add_zero] at H2
  rw [isUnit_iff_constantCoeff, ← isUnit_map_iff (IsLocalRing.residue A)]
  rw [coeff_mul, ← Finset.sum_subset (s₁ := {(n, 0)}) (by simp) (fun p hp hnotMem ↦ ?_),
    Finset.sum_singleton, coeff_map, coeff_map, coeff_zero_eq_constantCoeff, mul_comm] at H2
  · exact .of_mul_eq_one _ H2.symm
  · rw [coeff_of_lt_order p.1 ?_]
    · rw [zero_mul]
    · rw [← ENat.lt_lift_iff (h := order_finite_iff_ne_zero.2 hg), ENat.lift_eq_toNat_of_lt_top]
      refine (Finset.HasAntidiagonal.antidiagonal.fst_le hp).lt_of_ne ?_
      contrapose hnotMem
      rwa [Finset.mem_singleton, Finset.HasAntidiagonal.antidiagonal_congr hp (by simp)]
/-
**PowerSeries.IsWeierstrassDivision.isWeierstrassFactorization** 是 Mathlib 中的一个定
理，位于命名空间 `PowerSeries.IsWeierstrassDivision`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g q : Power
Series A} {r : Polynomial A}   (hg : (PowerSeries.map (IsLocalRing.residue A)) g
 ≠ 0)   (H : (PowerSeries.X ^ ((PowerSeries.map (IsLocalRing.residue A)) g).orde
r.toNat).IsWeierstrassDivision g q r),   g.IsWeierstrassFactorization (Polynomia
l.X ^ ((PowerSeries.map (IsLocalRing.residue A)) g).order.toNat - r) ↑⋯.unit⁻¹
参数：hg : (PowerSeries.map (IsLocalRing.residue A)) g ≠ 0；H : (PowerSeries.X ^ ((P
owerSeries.map (IsLocalRing.residue A)) g).order.toNat).IsWeierstrassDivision g 
q r；Polynomial.X ^ ((PowerSeries.map (IsLocalRing.residue A)) g).order.toNat - r
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.degree_lt`：∀ {A : Type u_1} [inst : 
CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWeie
rstrassDivisionAt g q r I → r.degre…
· 使用定理 `PowerSeries.IsWeierstrassDivision.isUnit_of_map_ne_zero`：∀ {A : Type u_1
} [inst : CommRing A] [inst_1 : IsLocalRing A] {g q : PowerSeries A} {r : Polyno
mial A},   (PowerSeries.map (IsLocalRing.resi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.coeff_f_sub_r_mem`：coeff_f_sub_r_mem
 (H : f.IsWeierstrassDivisionAt g q r I) {i : Nat} (hi : i < (g.map (Ideal.Quoti
ent.mk I)).order.toNat) : coeff i (f - r : …
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.Monic.sub_of_left`：∀ {R : Type u} [inst : Ring R] {p q : Poly
nomial R}, p.Monic → q.degree < p.degree → (p - q).Monic
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `PowerSeries.IsWeierstrassDivisionAt.eq_mul_add`：∀ {A : Type u_1} [inst :
 CommRing A] {f g q : PowerSeries A} {r : Polynomial A} {I : Ideal A},   f.IsWei
erstrassDivisionAt g q r I → f = g *…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
（共 40 条，此处仅展示前 30 条）
-/
theorem IsWeierstrassDivision.isWeierstrassFactorization
    {g q : A⟦X⟧} {r : A[X]} (hg : g.map (IsLocalRing.residue A) ≠ 0)
    (H : (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g q r) :
    g.IsWeierstrassFactorization
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - r)
      ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹ := by
  have H1 : r.degree < (g.map (IsLocalRing.residue A)).order.toNat := H.1
  set n := (g.map (IsLocalRing.residue A)).order.toNat
  set f := Polynomial.X ^ n - r
  replace H1 : r.degree < (Polynomial.X (R := A) ^ n).degree := by rwa [Polynomial.degree_X_pow]
  have hfdeg : f.natDegree = n := by
    suffices f.degree = n by rw [Polynomial.natDegree, this]; rfl
    rw [Polynomial.degree_sub_eq_left_of_degree_lt H1, Polynomial.degree_X_pow]
  refine ⟨⟨⟨fun {i} hi ↦ ?_⟩, .sub_of_left (Polynomial.monic_X_pow _) H1⟩, Units.isUnit _, ?_⟩
  · rw [hfdeg] at hi
    simp_rw [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff]
    have := H.coeff_f_sub_r_mem hi
    rwa [map_sub, coeff_X_pow, if_neg hi.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe] at this
  · have := congr($(H.2) * ↑(H.isUnit_of_map_ne_zero hg).unit⁻¹)
    rw [add_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, ← sub_eq_iff_eq_add] at this
    simp_rw [← this, f, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, sub_mul]
/-
**PowerSeries.IsWeierstrassFactorization.isWeierstrassDivision** 是 Mathlib 中的一个定
理，位于命名空间 `PowerSeries.IsWeierstrassFactorization`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g : PowerSe
ries A} {f : Polynomial A} {h : PowerSeries A}   (H : g.IsWeierstrassFactorizati
on f h),   (PowerSeries.X ^ ((PowerSeries.map (IsLocalRing.residue A)) g).order.
toNat).IsWeierstrassDivision g (↑⋯.unit⁻¹)     (Polynomial.X ^ ((PowerSeries.map
 (IsLocalRing.residue A)) g).order.toNat - f)
参数：H : g.IsWeierstrassFactorization f h；PowerSeries.X ^ ((PowerSeries.map (IsLoc
alRing.residue A)) g).order.toNat；↑⋯.unit⁻¹；Polynomial.X ^ ((PowerSeries.map (Is
LocalRing.residue A)) g).order.toNat - f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0
· 使用定理 `PowerSeries.IsWeierstrassFactorization.map_ne_zero`：map_ne_zero : g.map 
(IsLocalRing.residue A) != 0
· 使用定理 `PowerSeries.IsWeierstrassFactorization.degree_eq_coe_lift_order_map`：deg
ree_eq_coe_lift_order_map : f.degree = (g.map (IsLocalRing.residue A)).order.lif
t (order_finite_iff_ne_zero.2 H.map_ne_zero)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENat.lift_eq_toNat_of_lt_top`：lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x
 < ⊤) : x.lift hx = x.toNat
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.IsDistinguishedAt.monic`：∀ {R : Type u_1} [inst : CommRing R]
 {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Monic
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Polynomial.coe_sub`：coe_sub (p q : R[X]) : ((p - q : R[X]) : PowerSeries
 R) = p - q
· 使用定理 `Polynomial.coe_pow`：coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R)
 = (φ : PowerSeries R) ^ n
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem IsWeierstrassFactorization.isWeierstrassDivision
    {g : A⟦X⟧} {f : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorization f h) :
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).IsWeierstrassDivision g ↑H.isUnit.unit⁻¹
      (Polynomial.X ^ (g.map (IsLocalRing.residue A)).order.toNat - f) := by
  set n := (g.map (IsLocalRing.residue A)).order.toNat with hn
  constructor
  · refine (Polynomial.degree_sub_lt_left ?_ (Polynomial.monic_X_pow n).ne_zero ?_).trans_eq
      (by simpa)
    · simp_rw [H.degree_eq_coe_lift_order_map, Polynomial.degree_X_pow, n,
        ENat.lift_eq_toNat_of_lt_top]
    · rw [(Polynomial.monic_X_pow n).leadingCoeff, H.isDistinguishedAt.monic.leadingCoeff]
  · simp_rw [H.eq_mul, mul_assoc, IsUnit.mul_val_inv, mul_one, Polynomial.coe_sub,
      Polynomial.coe_pow, Polynomial.coe_X, add_sub_cancel]

/-- The `f` and `h` in the Weierstrass preparation theorem are unique.

This result is stated using two `PowerSeries.IsWeierstrassFactorization` assertions, and only
requires the ring being Hausdorff with respect to the maximal ideal. If you want `f` and `h` equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`,
use `PowerSeries.IsWeierstrassFactorization.unique` instead, which requires the ring being
complete with respect to the maximal ideal. -/
/-
**PowerSeries.IsWeierstrassFactorization.elim** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.IsWeierstrassFactorization`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] [IsHausdorff
 (IsLocalRing.maximalIdeal A) A]   {g : PowerSeries A} {f f' : Polynomial A} {h 
h' : PowerSeries A},   g.IsWeierstrassFactorization f h → g.IsWeierstrassFactori
zation f' h' → f = f' ∧ h = h'
参数：IsLocalRing.maximalIdeal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.IsWeierstrassDivision.elim`：∀ {A : Type u_1} [inst : CommRin
g A] [inst_1 : IsLocalRing A] {f g : PowerSeries A},   (PowerSeries.map (IsLocal
Ring.residue A)) g ≠ 0 →    …
· 使用定理 `PowerSeries.IsWeierstrassFactorization.map_ne_zero`：map_ne_zero : g.map 
(IsLocalRing.residue A) != 0
· 使用定理 `PowerSeries.IsWeierstrassFactorization.isWeierstrassDivision`：∀ {A : Typ
e u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g : PowerSeries A} {f : Pol
ynomial A} {h : PowerSeries A}   (H : g.IsWeierstr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `f` and `h` in the Weierstrass preparation theorem are unique.

This result is stated using two `PowerSeries.IsWeierstrassFactorization` asserti
ons, and only
requires the ring being Hausdorff with respect to the maximal ideal. If you want
 `f` and `h` equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`,
use `PowerSeries.IsWeierstrassFactorization.unique` instead, which requires the 
ring being
complete with respect to the maximal ideal.
-/
theorem IsWeierstrassFactorization.elim [IsHausdorff (IsLocalRing.maximalIdeal A) A]
    {g : A⟦X⟧} {f f' : A[X]} {h h' : A⟦X⟧} (H : g.IsWeierstrassFactorization f h)
    (H2 : g.IsWeierstrassFactorization f' h') : f = f' ∧ h = h' := by
  obtain ⟨h1, h2⟩ := H.isWeierstrassDivision.elim H.map_ne_zero H2.isWeierstrassDivision
  rw [← Units.ext_iff, inv_inj, Units.ext_iff] at h1
  exact ⟨by simpa using h2, h1⟩

section IsAdicComplete

variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {a : A} {g g' : A⟦X⟧} {f : A[X]} {h : A⟦X⟧}

/-- **Weierstrass preparation theorem** ([washington_cyclotomic], Theorem 7.3):
let `g` be a power series over a complete local ring,
such that its image in the residue field is not zero. Then there exists a distinguished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`. -/
/-
**PowerSeries.exists_isWeierstrassFactorization** 是 Mathlib 中的一个定理，位于命名空间 `Power
Series`。
形式化陈述：exists_isWeierstrassFactorization (hg : g.map (IsLocalRing.residue A) != 0
) : exists f h, g.IsWeierstrassFactorization f h
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.exists_isWeierstrassDivision`：exists_isWeierstrassDivision [
IsAdicComplete (IsLocalRing.maximalIdeal A) A] (hg : g.map (IsLocalRing.residue 
A) != 0) : exists q r, f.IsWei…
· 使用定理 `PowerSeries.IsWeierstrassDivision.isUnit_of_map_ne_zero`：∀ {A : Type u_1
} [inst : CommRing A] [inst_1 : IsLocalRing A] {g q : PowerSeries A} {r : Polyno
mial A},   (PowerSeries.map (IsLocalRing.resi…
· 使用定理 `PowerSeries.IsWeierstrassDivision.isWeierstrassFactorization`：∀ {A : Typ
e u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] {g q : PowerSeries A} {r : P
olynomial A}   (hg : (PowerSeries.map (IsLocalRing…

--- 原说明 ---
**Weierstrass preparation theorem** ([washington_cyclotomic], Theorem 7.3):
let `g` be a power series over a complete local ring,
such that its image in the residue field is not zero. Then there exists a distin
guished
polynomial `f` and a power series `h` which is a unit, such that `g = f * h`.
-/
theorem exists_isWeierstrassFactorization (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    ∃ f h, g.IsWeierstrassFactorization f h := by
  obtain ⟨q, r, H⟩ :=
    (X ^ (g.map (IsLocalRing.residue A)).order.toNat).exists_isWeierstrassDivision hg
  exact ⟨_, _, H.isWeierstrassFactorization hg⟩

variable (g) in
/-- The `f` in the Weierstrass preparation theorem. -/
/-
**PowerSeries.weierstrassDistinguished** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) != 0) : A[X]
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h

--- 原说明 ---
The `f` in the Weierstrass preparation theorem.
-/
noncomputable def weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) ≠ 0) : A[X] :=
  (g.exists_isWeierstrassFactorization hg).choose

variable (g) in
/-- The `h` in the Weierstrass preparation theorem. -/
/-
**PowerSeries.weierstrassUnit** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassUnit (hg : g.map (IsLocalRing.residue A) != 0) : A⟦X⟧
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h

--- 原说明 ---
The `h` in the Weierstrass preparation theorem.
-/
noncomputable def weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) : A⟦X⟧ :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose
/-
**PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUni
t** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg : 
g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization (g.weierstras
sDistinguished hg) (g.weierstrassUnit hg)
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h
-/
theorem isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g.IsWeierstrassFactorization (g.weierstrassDistinguished hg) (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec

/-- If `g` is a power series over a complete local ring,
such that its image in the residue field is not zero, then there is a natural isomorphism
`A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished g`. -/
/-
**PowerSeries.algEquivQuotientWeierstrassDistinguished** 是 Mathlib 中的一个缩写定义，位于命名
空间 `PowerSeries`。
形式化陈述：algEquivQuotientWeierstrassDistinguished (hg : g.map (IsLocalRing.residue 
A) != 0)
参数：hg : g.map (IsLocalRing.residue A) != 0。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…

--- 原说明 ---
If `g` is a power series over a complete local ring,
such that its image in the residue field is not zero, then there is a natural is
omorphism
`A[X] / (f) ≃ₐ[A] A⟦X⟧ / (g)` where `f` is `PowerSeries.weierstrassDistinguished
 g`.
-/
noncomputable abbrev algEquivQuotientWeierstrassDistinguished
    (hg : g.map (IsLocalRing.residue A) ≠ 0) :=
  (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg).algEquivQuotient
/-
**PowerSeries.isDistinguishedAt_weierstrassDistinguished** 是 Mathlib 中的一个定理，位于命名
空间 `PowerSeries`。
形式化陈述：isDistinguishedAt_weierstrassDistinguished (hg : g.map (IsLocalRing.residu
e A) != 0) : (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maxi
malIdeal A)
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isDistinguishedAt`：∀ {A : Type 
u_1} [inst : CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries
 A} {I : Ideal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isDistinguishedAt_weierstrassDistinguished (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    (g.weierstrassDistinguished hg).IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isDistinguishedAt
/-
**PowerSeries.isUnit_weierstrassUnit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：isUnit_weierstrassUnit (hg : g.map (IsLocalRing.residue A) != 0) : IsUnit 
(g.weierstrassUnit hg)
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.isUnit`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isUnit_weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    IsUnit (g.weierstrassUnit hg) :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.isUnit
/-
**PowerSeries.eq_weierstrassDistinguished_mul_weierstrassUnit** 是 Mathlib 中的一个定理
，位于命名空间 `PowerSeries`。
形式化陈述：eq_weierstrassDistinguished_mul_weierstrassUnit (hg : g.map (IsLocalRing.r
esidue A) != 0) : g = g.weierstrassDistinguished hg * g.weierstrassUnit hg
参数：hg : g.map (IsLocalRing.residue A) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.eq_mul`：∀ {A : Type u_1} [inst 
: CommRing A] {g : PowerSeries A} {f : Polynomial A} {h : PowerSeries A} {I : Id
eal A},   g.IsWeierstrassFactorizatio…
· 使用定理 `PowerSeries.exists_isWeierstrassFactorization`：exists_isWeierstrassFacto
rization (hg : g.map (IsLocalRing.residue A) != 0) : exists f h, g.IsWeierstrass
Factorization f h
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem eq_weierstrassDistinguished_mul_weierstrassUnit (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    g = g.weierstrassDistinguished hg * g.weierstrassUnit hg :=
  (g.exists_isWeierstrassFactorization hg).choose_spec.choose_spec.eq_mul

/-- The `f` and `h` in Weierstrass preparation theorem are equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`. -/
/-
**PowerSeries.IsWeierstrassFactorization.unique** 是 Mathlib 中的一个定理，位于命名空间 `Power
Series.IsWeierstrassFactorization`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : IsLocalRing A] [inst_2 : Is
AdicComplete (IsLocalRing.maximalIdeal A) A]   {g : PowerSeries A} {f : Polynomi
al A} {h : PowerSeries A},   g.IsWeierstrassFactorization f h →     ∀ (hg : (Pow
erSeries.map (IsLocalRing.residue A)) g ≠ 0),       f = g.weierstrassDistinguish
ed hg ∧ h = g.weierstrassUnit hg
参数：IsLocalRing.maximalIdeal A；hg : (PowerSeries.map (IsLocalRing.residue A)) g ≠
 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.IsWeierstrassFactorization.elim`：∀ {A : Type u_1} [inst : Co
mmRing A] [inst_1 : IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] 
  {g : PowerSeries A} {f f' : Pol…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…

--- 原说明 ---
The `f` and `h` in Weierstrass preparation theorem are equal
to `PowerSeries.weierstrassDistinguished` and `PowerSeries.weierstrassUnit`.
-/
theorem IsWeierstrassFactorization.unique
    (H : g.IsWeierstrassFactorization f h) (hg : g.map (IsLocalRing.residue A) ≠ 0) :
    f = g.weierstrassDistinguished hg ∧ h = g.weierstrassUnit hg :=
  H.elim (g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg)

@[simp]
/-
**PowerSeries.weierstrassDistinguished_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：weierstrassDistinguished_mul (hg : (g * g').map (IsLocalRing.residue A) !=
 0) : (g * g').weierstrassDistinguished hg = g.weierstrassDistinguished (fun h =
> hg (by simp [h])) * g'.weierstrassDistinguished (fun h => hg (by simp [h]))
参数：hg : (g * g').map (IsLocalRing.residue A) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PowerSeries.IsWeierstrassFactorization.elim`：∀ {A : Type u_1} [inst : Co
mmRing A] [inst_1 : IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] 
  {g : PowerSeries A} {f f' : Pol…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.mul`：mul {g' : A⟦X⟧} {f' : A[X]
} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) : (g * g').IsWeiers
trassFactorizationAt (f * f') (h *…
-/
theorem weierstrassDistinguished_mul (hg : (g * g').map (IsLocalRing.residue A) ≠ 0) :
    (g * g').weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h ↦ hg (by simp [h])) *
        g'.weierstrassDistinguished (fun h ↦ hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).1

@[simp]
/-
**PowerSeries.weierstrassUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassUnit_mul (hg : (g * g').map (IsLocalRing.residue A) != 0) : (g 
* g').weierstrassUnit hg = g.weierstrassUnit (fun h => hg (by simp [h])) * g'.we
ierstrassUnit (fun h => hg (by simp [h]))
参数：hg : (g * g').map (IsLocalRing.residue A) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.IsWeierstrassFactorization.elim`：∀ {A : Type u_1} [inst : Co
mmRing A] [inst_1 : IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] 
  {g : PowerSeries A} {f f' : Pol…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.mul`：mul {g' : A⟦X⟧} {f' : A[X]
} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) : (g * g').IsWeiers
trassFactorizationAt (f * f') (h *…
-/
theorem weierstrassUnit_mul (hg : (g * g').map (IsLocalRing.residue A) ≠ 0) :
    (g * g').weierstrassUnit hg =
      g.weierstrassUnit (fun h ↦ hg (by simp [h])) *
        g'.weierstrassUnit (fun h ↦ hg (by simp [h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H' := g'.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [h]))
  have H'' := (g * g').isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  exact (H''.elim (H.mul H')).2

@[simp]
/-
**PowerSeries.weierstrassDistinguished_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeri
es`。
形式化陈述：weierstrassDistinguished_smul (hg : (a • g).map (IsLocalRing.residue A) !=
 0) : (a • g).weierstrassDistinguished hg = g.weierstrassDistinguished (fun h =>
 hg (by simp [Algebra.smul_def, h]))
参数：hg : (a • g).map (IsLocalRing.residue A) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.map_C`：map_C (r : R) : map f (C r) = C (f r)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PowerSeries.IsWeierstrassFactorization.elim`：∀ {A : Type u_1} [inst : Co
mmRing A] [inst_1 : IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] 
  {g : PowerSeries A} {f f' : Pol…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.smul`：smul {a : A} (ha : IsUnit
 a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I
-/
theorem weierstrassDistinguished_smul (hg : (a • g).map (IsLocalRing.residue A) ≠ 0) :
    (a • g).weierstrassDistinguished hg =
      g.weierstrassDistinguished (fun h ↦ hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a ≠ 0 := fun h ↦ hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).1

@[simp]
/-
**PowerSeries.weierstrassUnit_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：weierstrassUnit_smul (hg : (a • g).map (IsLocalRing.residue A) != 0) : (a 
• g).weierstrassUnit hg = a • g.weierstrassUnit (fun h => hg (by simp [Algebra.s
mul_def, h]))
参数：hg : (a • g).map (IsLocalRing.residue A) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.map_C`：map_C (r : R) : map f (C r) = C (f r)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstr
assUnit`：isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit (hg
 : g.map (IsLocalRing.residue A) != 0) : g.IsWeierstrassFactorization…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.IsWeierstrassFactorization.elim`：∀ {A : Type u_1} [inst : Co
mmRing A] [inst_1 : IsLocalRing A] [IsHausdorff (IsLocalRing.maximalIdeal A) A] 
  {g : PowerSeries A} {f f' : Pol…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `PowerSeries.IsWeierstrassFactorizationAt.smul`：smul {a : A} (ha : IsUnit
 a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I
-/
theorem weierstrassUnit_smul (hg : (a • g).map (IsLocalRing.residue A) ≠ 0) :
    (a • g).weierstrassUnit hg =
      a • g.weierstrassUnit (fun h ↦ hg (by simp [Algebra.smul_def, h])) := by
  have H := g.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (fun h ↦ hg (by simp [Algebra.smul_def, h]))
  have H' := (a • g).isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hg
  have ha : IsLocalRing.residue A a ≠ 0 := fun h ↦ hg (by simp [Algebra.smul_def, h])
  exact (H'.elim (H.smul (by simpa using ha))).2

end IsAdicComplete

end PowerSeries

