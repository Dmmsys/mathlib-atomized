/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Basis
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!

# Ideal norms

This file defines the absolute ideal norm `Ideal.absNorm (I : Ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

* `Submodule.cardQuot (S : Submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
  This maps `⊥` to `0` and `⊤` to `1`.
* `Ideal.absNorm (I : Ideal R)`: the absolute ideal norm, defined as
  the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## Main results

* `map_mul Ideal.absNorm`: multiplicativity of the ideal norm is bundled in
  the definition of `Ideal.absNorm`
* `Ideal.natAbs_det_basis_change`: the ideal norm is given by the determinant
  of the basis change matrix
* `Ideal.absNorm_span_singleton`: the ideal norm of a principal ideal is the
  norm of its generator
-/

@[expose] public section

open Module
open scoped nonZeroDivisors

section abs_norm

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `Ideal.absNorm`.
-/
/-
**Submodule.cardQuot** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：cardQuot (S : Submodule R M) : Nat
参数：S : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `Ideal.absNorm`.
-/
noncomputable def cardQuot (S : Submodule R M) : ℕ :=
  AddSubgroup.index S.toAddSubgroup
/-
**Submodule.cardQuot_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：cardQuot_apply (S : Submodule R M) : cardQuot S = Nat.card (M ⧸ S)
参数：S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cardQuot_apply (S : Submodule R M) : cardQuot S = Nat.card (M ⧸ S) := by
  rfl

variable (R M)

@[simp]
/-
**Submodule.cardQuot_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：cardQuot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubgroup.index_bot`：∀ {G : Type u_1} [inst : AddGroup G], ⊥.index = N
at.card G
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
theorem cardQuot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite

@[simp]
/-
**Submodule.cardQuot_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：cardQuot_top : cardQuot (⊤ : Submodule R M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.index_top`：∀ {G : Type u_1} [inst : AddGroup G], ⊤.index = 1
-/
theorem cardQuot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top

variable {R M}

@[simp]
/-
**Submodule.cardQuot_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：cardQuot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddSubgroup.index_eq_one`：∀ {G : Type u_1} [inst : AddGroup G] {H : AddS
ubgroup G}, H.index = 1 ↔ H = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cardQuot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])

end

end Submodule

section RingOfIntegers

variable {S : Type*} [CommRing S]

open Submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
/-
**cardQuot_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardQuot_mul_of_coprime {I J : Ideal S} (coprime : IsCoprime I J) : cardQu
ot (I * J) = cardQuot I * cardQuot J
参数：coprime : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.cardQuot_apply`：cardQuot_apply (S : Submodule R M) : cardQuot 
S = Nat.card (M ⧸ S)
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β

--- 原说明 ---
Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
theorem cardQuot_mul_of_coprime
    {I J : Ideal S} (coprime : IsCoprime I J) : cardQuot (I * J) = cardQuot I * cardQuot J := by
  rw [cardQuot_apply, cardQuot_apply, cardQuot_apply,
    Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv,
    Nat.card_prod]

/-- If the `d` from `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
/-
**Ideal.mul_add_mem_pow_succ_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : Nat} (a d d' e e' : S) (
a_mem : a in P ^ i) (e_mem : e in P ^ (i + 1)) (e'_mem : e' in P ^ (i + 1)) (h :
 d - d' in P) : a * d + e - (a * d' + e') in P ^ (i + 1)
参数：P : Ideal S；a d d' e e' : S；a_mem : a in P ^ i；e_mem : e in P ^ (i + 1)；e'_me
m : e' in P ^ (i + 1)；h : d - d' in P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If the `d` from `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1
-/
theorem Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
    (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1)) (h : d - d' ∈ P) :
    a * d + e - (a * d' + e') ∈ P ^ (i + 1) := by
  have : a * d - a * d' ∈ P ^ (i + 1) := by
    simp only [← mul_sub]
    exact Ideal.mul_mem_mul a_mem h
  convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  ring

section PPrime

variable {P : Ideal S} [P_prime : P.IsPrime]

/-- If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`Ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
/-
**Ideal.exists_mul_add_mem_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP : P != ⊥) {i : 
Nat} (a c : S) (a_mem : a in P ^ i) (a_notMem : a ∉ P ^ (i + 1)) (c_mem : c in P
 ^ i) : exists d : S, exists e in P ^ (i + 1), a * d + e = c
参数：hP : P != ⊥；a c : S；a_mem : a in P ^ i；a_notMem : a ∉ P ^ (i + 1)；c_mem : c i
n P ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.eq_prime_pow_of_succ_lt_of_le`：eq_prime_pow_of_succ_lt_of_le {P I 
: Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥) {i : Nat} (hlt : P ^ (i + 1) < I)
 (hle : I <= P ^ i) : I =…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ideal.pow_succ_lt_pow`：pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrim
e] (hP : P != ⊥) (i : Nat) : P ^ (i + 1) < P ^ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton_sup`：mem_span_singleton_sup {x y : α} {I : Idea
l α} : x in Ideal.span {y} ⊔ I ↔ exists a : α, exists b in I, a * y + b = x

--- 原说明 ---
If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`Ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`
.
Inspired by [Neukirch], proposition 6.1
-/
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP : P ≠ ⊥)
    {i : ℕ} (a c : S) (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
    ∃ d : S, ∃ e ∈ P ^ (i + 1), a * d + e = c := by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1) by
    rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact Ideal.mem_span_singleton_sup.mp c_mem
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
      (Ideal.pow_succ_lt_pow hP i).le)).symm
  contrapose a_notMem with this
  rw [this]
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
/-
**Ideal.mem_prime_of_mul_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime
 : P.IsPrime] (hP : P != ⊥) {i : Nat} {a b : S} (a_notMem : a ∉ P ^ (i + 1)) (ab
_mem : a * b in P ^ (i + 1)) : b in P
参数：hP : P != ⊥；a_notMem : a ∉ P ^ (i + 1)；ab_mem : a * b in P ^ (i + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `prime_pow_succ_dvd_mul`：prime_pow_succ_dvd_mul {p x y : M} (h : Prime p)
 {i : Nat} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime]
    (hP : P ≠ ⊥) {i : ℕ} {a b : S} (a_notMem : a ∉ P ^ (i + 1)) (ab_mem : a * b ∈ P ^ (i + 1)) :
    b ∈ P := by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem

/-- The choice of `d` in `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
/-
**Ideal.mul_add_mem_pow_succ_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP : P != ⊥) {i : 
Nat} (a d d' e e' : S) (a_notMem : a ∉ P ^ (i + 1)) (e_mem : e in P ^ (i + 1)) (
e'_mem : e' in P ^ (i + 1)) (h : a * d + e - (a * d' + e') in P ^ (i + 1)) : d -
 d' in P
参数：hP : P != ⊥；a d d' e e' : S；a_notMem : a ∉ P ^ (i + 1)；e_mem : e in P ^ (i + 
1)；e'_mem : e' in P ^ (i + 1)；h : a * d + e - (a * d' + e') in P ^ (i + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The choice of `d` in `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1
-/
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP : P ≠ ⊥)
    {i : ℕ} (a d d' e e' : S)
    (a_notMem : a ∉ P ^ (i + 1)) (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
    (h : a * d + e - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P := by
  have h' : a * (d - d') ∈ P ^ (i + 1) := by
    convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
/-
**cardQuot_pow_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardQuot_pow_of_prime [IsDedekindDomain S] (hP : P != ⊥) {i : Nat} : cardQ
uot (P ^ i) = cardQuot P ^ i
参数：hP : P != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Submodule.cardQuot_top`：cardQuot_top : cardQuot (⊤ : Submodule R M) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.pow_succ_lt_pow`：pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrim
e] (hP : P != ⊥) (i : Nat) : P ^ (i + 1) < P ^ i
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `Ideal.mul_add_mem_pow_succ_inj`：Ideal.mul_add_mem_pow_succ_inj (P : Idea
l S) {i : Nat} (a d d' e e' : S) (a_mem : a in P ^ i) (e_mem : e in P ^ (i + 1))
 (e'_mem : e' in P ^…
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mul_add_mem_pow_succ_unique`：Ideal.mul_add_mem_pow_succ_unique [Is
DedekindDomain S] (hP : P != ⊥) {i : Nat} (a d d' e e' : S) (a_notMem : a ∉ P ^ 
(i + 1)) (e_mem : e in …
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Multiplicity of the ideal norm, for powers of prime ideals.
-/
theorem cardQuot_pow_of_prime [IsDedekindDomain S] (hP : P ≠ ⊥) {i : ℕ} :
    cardQuot (P ^ i) = cardQuot P ^ i := by
  induction i with
  | zero => simp
  | succ i ih => ?_
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P by
    rw [pow_succ' (cardQuot P), ← ih, cardQuot_apply (P ^ i.succ), ←
      card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le, cardQuot_apply (P ^ i),
      cardQuot_apply P, Nat.card_congr hquot]
  choose a a_mem a_notMem using SetLike.exists_of_lt this
  choose f g hg hf using fun c (hc : c ∈ P ^ i) =>
    Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_notMem hc
  choose k hk_mem hk_eq using fun c' (hc' : c' ∈ map (mkQ (P ^ i.succ)) (P ^ i)) =>
    Submodule.mem_map.mp hc'
  refine Equiv.ofBijective (fun c' => Quotient.mk'' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨?_, ?_⟩
  · rintro ⟨c₁', hc₁'⟩ ⟨c₂', hc₂'⟩ h
    rw [Subtype.mk_eq_mk, ← hk_eq _ hc₁', ← hk_eq _ hc₂', mkQ_apply, mkQ_apply,
      Submodule.Quotient.eq, ← hf _ (hk_mem _ hc₁'), ← hf _ (hk_mem _ hc₂')]
    refine Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) ?_
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk''_eq_mk,
      Submodule.Quotient.eq] using h
  · intro d'
    induction d' using Quotient.inductionOn with | _ d
    have hd' := (mem_map (f := mkQ (P ^ i.succ))).mpr ⟨a * d, Ideal.mul_mem_right d _ a_mem, rfl⟩
    refine ⟨⟨_, hd'⟩, ?_⟩
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq]
    refine
      Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_notMem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
    rw [hf, add_zero]
    exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')

end PPrime

/-- Multiplicativity of the ideal norm in number rings. -/
/-
**cardQuot_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardQuot_mul [IsDedekindDomain S] [Module.Free Int S] (I J : Ideal S) : ca
rdQuot (I * J) = cardQuot I * cardQuot J
参数：I J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_surjective`：of_surjective {α β} [Infinite β] (f : α -> β) (h
f : Surjective f) : Infinite α
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `UniqueFactorizationMonoid.multiplicative_of_coprime`：multiplicative_of_c
oprime (f : α -> β) (a b : α) (h0 : f 0 = 0) (h1 : forall {x y}, IsUnit y -> f (
x * y) = f x * f y) (hpr : forall {p} (i …
· 使用定理 `Submodule.cardQuot_bot`：cardQuot_bot [Infinite M] : cardQuot (⊥ : Submod
ule R M) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.cardQuot_top`：cardQuot_top : cardQuot (⊤ : Submodule R M) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `cardQuot_pow_of_prime`：cardQuot_pow_of_prime [IsDedekindDomain S] (hP : 
P != ⊥) {i : Nat} : cardQuot (P ^ i) = cardQuot P ^ i
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `cardQuot_mul_of_coprime`：cardQuot_mul_of_coprime {I J : Ideal S} (coprim
e : IsCoprime I J) : cardQuot (I * J) = cardQuot I * cardQuot J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isCoprime_iff_sup_eq`：isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J
 = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
Multiplicativity of the ideal norm in number rings.
-/
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free ℤ S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  have : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i hI =>
        have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
        cardQuot_pow_of_prime hI.ne_zero)
      fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.isUnit_iff.mp
          (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

/-- The absolute norm of the ideal `I : Ideal R` is the cardinality of the quotient `R ⧸ I`. -/
/-
**Ideal.absNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.absNorm [IsDedekindDomain S] [Module.Free Int S] : Ideal S ->*₀ Nat 
where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute norm of the ideal `I : Ideal R` is the cardinality of the quotient 
`R ⧸ I`.
-/
noncomputable def Ideal.absNorm [IsDedekindDomain S] [Module.Free ℤ S] :
    Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := by rw [cardQuot_mul]
  map_one' := by rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    have : Infinite S := Module.Free.infinite ℤ S
    rw [Ideal.zero_eq_bot, cardQuot_bot]

namespace Ideal

variable [IsDedekindDomain S] [Module.Free ℤ S]

/-
**Ideal.absNorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_apply (I : Ideal S) : absNorm I = cardQuot I
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem absNorm_apply (I : Ideal S) : absNorm I = cardQuot I := rfl
/-
**Ideal.absNorm_eq_index** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：absNorm_eq_index (I : Ideal S) : absNorm I = I.toAddSubgroup.index
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma absNorm_eq_index (I : Ideal S) : absNorm I = I.toAddSubgroup.index := rfl

@[simp]
/-
**Ideal.absNorm_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_bot : absNorm (⊥ : Ideal S) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem absNorm_bot : absNorm (⊥ : Ideal S) = 0 := by rw [← Ideal.zero_eq_bot, map_zero]

@[simp]
/-
**Ideal.absNorm_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_top : absNorm (⊤ : Ideal S) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem absNorm_top : absNorm (⊤ : Ideal S) = 1 := by rw [← Ideal.one_eq_top, map_one]

@[simp]
/-
**Ideal.absNorm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_eq_one_iff {I : Ideal S} : absNorm I = 1 ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_apply`：absNorm_apply (I : Ideal S) : absNorm I = cardQuot 
I
· 使用定理 `Submodule.cardQuot_eq_one_iff`：cardQuot_eq_one_iff {P : Submodule R M} :
 cardQuot P = 1 ↔ P = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem absNorm_eq_one_iff {I : Ideal S} : absNorm I = 1 ↔ I = ⊤ := by
  rw [absNorm_apply, cardQuot_eq_one_iff]
/-
**Ideal.absNorm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_ne_zero_iff (I : Ideal S) : Ideal.absNorm I != 0 ↔ Finite (S ⧸ I)
参数：I : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `AddSubgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_3} {inst : AddGroup
 G} {H : AddSubgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `AddSubgroup.finiteIndex_of_finite_quotient`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [Finite (G ⧸ H)], H.FiniteIndex
-/
theorem absNorm_ne_zero_iff (I : Ideal S) : Ideal.absNorm I ≠ 0 ↔ Finite (S ⧸ I) :=
  ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩
/-
**Ideal.absNorm_dvd_absNorm_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_dvd_absNorm_of_le {I J : Ideal S} (h : J <= I) : Ideal.absNorm I ∣
 Ideal.absNorm J
参数：h : J <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
-/
theorem absNorm_dvd_absNorm_of_le {I J : Ideal S} (h : J ≤ I) : Ideal.absNorm I ∣ Ideal.absNorm J :=
  map_dvd absNorm (dvd_iff_le.mpr h)
/-
**Ideal.irreducible_of_irreducible_absNorm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：irreducible_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.
absNorm I)) : Irreducible I
参数：hI : Irreducible (Ideal.absNorm I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irreducible
 p ↔ ¬IsUnit p ∧ ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem irreducible_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    Irreducible I :=
  irreducible_iff.mpr
    ⟨fun h =>
      hI.not_isUnit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
      by
      rintro a b rfl
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (map_mul absNorm a b)⟩
/-
**Ideal.isPrime_of_irreducible_absNorm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absN
orm I)) : I.IsPrime
参数：hI : Irreducible (Ideal.absNorm I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
· 使用定理 `Ideal.irreducible_of_irreducible_absNorm`：irreducible_of_irreducible_abs
Norm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) : Irreducible I
-/
theorem isPrime_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    I.IsPrime :=
  isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))
/-
**Ideal.prime_of_irreducible_absNorm_span** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_of_irreducible_absNorm_span {a : S} (ha : a != 0) (hI : Irreducible 
(Ideal.absNorm (Ideal.span ({a} : Set S)))) : Prime a
参数：ha : a != 0；hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set S)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Ideal.isPrime_of_irreducible_absNorm`：isPrime_of_irreducible_absNorm {I 
: Ideal S} (hI : Irreducible (Ideal.absNorm I)) : I.IsPrime
-/
theorem prime_of_irreducible_absNorm_span {a : S} (ha : a ≠ 0)
    (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set S)))) : Prime a :=
  (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)
/-
**Ideal.absNorm_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I
参数：I : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_apply`：absNorm_apply (I : Ideal S) : absNorm I = cardQuot 
I
· 使用定理 `Submodule.cardQuot.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R]
 [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (S : Submodule R M), S
.cardQuot = S…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Ideal.Quotient.index_eq_zero`：Ideal.Quotient.index_eq_zero (I : Ideal R)
 : (↑I.toAddSubgroup.index : R ⧸ I) = 0
-/
theorem absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) ∈ I := by
  rw [absNorm_apply, cardQuot, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    Quotient.index_eq_zero]
/-
**Ideal.span_singleton_absNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_singleton_absNorm_le (I : Ideal S) : Ideal.span {(Ideal.absNorm I : S
)} <= I
参数：I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.absNorm_mem`：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I
-/
theorem span_singleton_absNorm_le (I : Ideal S) : Ideal.span {(Ideal.absNorm I : S)} ≤ I := by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]
/-
**Ideal.span_singleton_absNorm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_singleton_absNorm {I : Ideal S} (hI : (Ideal.absNorm I).Prime) : Idea
l.span (singleton (Ideal.absNorm I : Int)) = I.comap (algebraMap Int S)
参数：hI : (Ideal.absNorm I).Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.isPrime_of_irreducible_absNorm`：isPrime_of_irreducible_absNorm {I 
: Ideal S} (hI : Irreducible (Ideal.absNorm I)) : I.IsPrime
· 使用定理 `Nat.irreducible_iff_nat_prime`：irreducible_iff_nat_prime (a : Nat) : Irr
educible a ↔ Nat.Prime a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `algebraMap_int_eq`：algebraMap_int_eq : algebraMap Int R = Int.castRingHo
m R
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Ideal.absNorm_mem`：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I
-/
theorem span_singleton_absNorm {I : Ideal S} (hI : (Ideal.absNorm I).Prime) :
    Ideal.span (singleton (Ideal.absNorm I : ℤ)) = I.comap (algebraMap ℤ S) := by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : ℤ))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap ℤ S)).ne_top
  · rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
    exact absNorm_mem I
  · rw [Ne, span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hI.ne_zero

variable [Module.Finite ℤ S]

/-- Let `e : S ≃ I` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the norm of `I` is given by taking the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result. -/
/-
**Ideal.natAbs_det_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：natAbs_det_equiv (I : Ideal S) {E : Type*} [EquivLike E S I] [AddEquivClas
s E S I] (e : E) : Int.natAbs (LinearMap.det ((Submodule.subtype I).restrictScal
ars Int ∘ₗ AddMonoidHom.toIntLinearMap (e : S ->+ I))) = Ideal.absNorm I
参数：I : Ideal S；e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.natAbs_det_equiv`：Submodule.natAbs_det_equiv (N : Submodule In
t M) {E : Type*} [EquivLike E M N] [AddEquivClass E M N] (e : E) : Int.natAbs (L
inearMap.det (N.…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Let `e : S ≃ I` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the norm of `I` is given by taking the determ
inant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result.
-/
theorem natAbs_det_equiv (I : Ideal S) {E : Type*} [EquivLike E S I] [AddEquivClass E S I] (e : E) :
    Int.natAbs
        (LinearMap.det
          ((Submodule.subtype I).restrictScalars ℤ ∘ₗ AddMonoidHom.toIntLinearMap (e : S →+ I))) =
      Ideal.absNorm I := by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  · subst hI
    have : (1 : S) ≠ 0 := one_ne_zero
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    contradiction
  exact Submodule.natAbs_det_equiv (I.restrictScalars ℤ) e

/-- Let `b` be a basis for `S` over `ℤ` and `bI` a basis for `I` over `ℤ` of the same dimension.
Then an alternative way to compute the norm of `I` is given by taking the determinant of `bI`
over `b`. -/
/-
**Ideal.natAbs_det_basis_change** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis
 ι Int S) (I : Ideal S) (bI : Basis ι Int I) : (b.det ((↑) ∘ bI)).natAbs = Ideal
.absNorm I
参数：b : Basis ι Int S；I : Ideal S；bI : Basis ι Int I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.natAbs_det_basis_change`：Submodule.natAbs_det_basis_change {ι 
: Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int M) (N : Submodule Int M) (
bN : Basis ι Int N) : (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Let `b` be a basis for `S` over `ℤ` and `bI` a basis for `I` over `ℤ` of the sam
e dimension.
Then an alternative way to compute the norm of `I` is given by taking the determ
inant of `bI`
over `b`.
-/
theorem natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ S)
    (I : Ideal S) (bI : Basis ι ℤ I) : (b.det ((↑) ∘ bI)).natAbs = Ideal.absNorm I :=
  Submodule.natAbs_det_basis_change b (I.restrictScalars ℤ) bI

@[simp]
/-
**Ideal.absNorm_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_span_singleton (r : S) : absNorm (span ({r} : Set S)) = (Algebra.n
orm Int r).natAbs
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.span_zero`：span_zero : span (0 : Set α) = ⊥
· 使用定理 `Ideal.absNorm_bot`：absNorm_bot : absNorm (⊥ : Ideal S) = 0
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
· 使用定理 `LinearMap.det_zero''`：LinearMap.det_zero'' {R M : Type*} [CommRing R] [A
ddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Nontrivial M]
 : LinearM…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.natAbs_det_equiv`：natAbs_det_equiv (I : Ideal S) {E : Type*} [Equi
vLike E S I] [AddEquivClass E S I] (e : E) : Int.natAbs (LinearMap.det ((Submodu
le.subtype I…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Ideal.basisSpanSingleton_apply`：basisSpanSingleton_apply (b : Basis ι R 
S) {x : S} (hx : x != 0) (i : ι) : (basisSpanSingleton b hx i : S) = x * b i
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem absNorm_span_singleton (r : S) :
    absNorm (span ({r} : Set S)) = (Algebra.norm ℤ r).natAbs := by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · simp only [hr, Ideal.span_zero, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, map_zero, Int.natAbs_zero]
  let b := Module.Free.chooseBasis ℤ S
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
  congr
  refine b.ext fun i => ?_
  simp
/-
**Ideal.absNorm_span_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：absNorm_span_natCast (n : Nat) : (span {(n : S)}).absNorm = n ^ Module.fin
rank Int S
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Algebra.norm_natCast`：∀ (R : Type u_1) {S : Type u_2} [inst : CommRing R
] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (n : ℕ),   (Algebra
.norm R) ↑…
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma absNorm_span_natCast (n : ℕ) : (span {(n : S)}).absNorm = n ^ Module.finrank ℤ S := by
  simp [absNorm_span_singleton, Algebra.norm_natCast]
/-
**Ideal.absNorm_dvd_norm_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_dvd_norm_of_mem {I : Ideal S} {x : S} (h : x in I) : ↑(Ideal.absNo
rm I) ∣ Algebra.norm Int x
参数：h : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Ideal.absNorm_dvd_absNorm_of_le`：absNorm_dvd_absNorm_of_le {I J : Ideal 
S} (h : J <= I) : Ideal.absNorm I ∣ Ideal.absNorm J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
-/
theorem absNorm_dvd_norm_of_mem {I : Ideal S} {x : S} (h : x ∈ I) :
    ↑(Ideal.absNorm I) ∣ Algebra.norm ℤ x := by
  rw [← Int.dvd_natAbs, ← absNorm_span_singleton x, Int.natCast_dvd_natCast]
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)

@[simp]
/-
**Ideal.absNorm_span_insert** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_span_insert (r : S) (s : Set S) : absNorm (span (insert r s)) ∣ gc
d (absNorm (span s)) (Algebra.norm Int r).natAbs
参数：r : S；s : Set S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_gcd_iff`：dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b
 ∧ a ∣ c
· 使用定理 `Ideal.absNorm_dvd_absNorm_of_le`：absNorm_dvd_absNorm_of_le {I J : Ideal 
S} (h : J <= I) : Ideal.absNorm I ∣ Ideal.absNorm J
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem absNorm_span_insert (r : S) (s : Set S) :
    absNorm (span (insert r s)) ∣ gcd (absNorm (span s)) (Algebra.norm ℤ r).natAbs :=
  (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩
/-
**Ideal.absNorm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_eq_zero_iff {I : Ideal S} : Ideal.absNorm I = 0 ↔ I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Algebra.norm_eq_zero_iff`：norm_eq_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x = 0 ↔ x = 0
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Ideal.absNorm_dvd_absNorm_of_le`：absNorm_dvd_absNorm_of_le {I J : Ideal 
S} (h : J <= I) : Ideal.absNorm I ∣ Ideal.absNorm J
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.absNorm_bot`：absNorm_bot : absNorm (⊥ : Ideal S) = 0
-/
theorem absNorm_eq_zero_iff {I : Ideal S} : Ideal.absNorm I = 0 ↔ I = ⊥ := by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intro x hx
    rw [mem_bot, ← Algebra.norm_eq_zero_iff (R := ℤ), ← Int.natAbs_eq_zero,
      ← Ideal.absNorm_span_singleton, ← zero_dvd_iff, ← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_iff_mem]
  · rintro rfl
    exact absNorm_bot
/-
**Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：absNorm_ne_zero_iff_mem_nonZeroDivisors {I : Ideal S} : absNorm I != 0 ↔ I
 in (Ideal S)⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem absNorm_ne_zero_iff_mem_nonZeroDivisors {I : Ideal S} :
    absNorm I ≠ 0 ↔ I ∈ (Ideal S)⁰ := by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]
/-
**Ideal.absNorm_pos_iff_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_pos_iff_mem_nonZeroDivisors {I : Ideal S} : 0 < absNorm I ↔ I in (
Ideal S)⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors`：absNorm_ne_zero_iff_mem_n
onZeroDivisors {I : Ideal S} : absNorm I != 0 ↔ I in (Ideal S)⁰
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem absNorm_pos_iff_mem_nonZeroDivisors {I : Ideal S} :
    0 < absNorm I ↔ I ∈ (Ideal S)⁰ := by
  rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors, Nat.pos_iff_ne_zero]
/-
**Ideal.absNorm_ne_zero_of_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_ne_zero_of_nonZeroDivisors (I : (Ideal S)⁰) : absNorm (I : Ideal S
) != 0
参数：I : (Ideal S)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors`：absNorm_ne_zero_iff_mem_n
onZeroDivisors {I : Ideal S} : absNorm I != 0 ↔ I in (Ideal S)⁰
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem absNorm_ne_zero_of_nonZeroDivisors (I : (Ideal S)⁰) : absNorm (I : Ideal S) ≠ 0 :=
  absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
/-
**Ideal.absNorm_pos_of_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：absNorm_pos_of_nonZeroDivisors (I : (Ideal S)⁰) : 0 < absNorm (I : Ideal S
)
参数：I : (Ideal S)⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.absNorm_pos_iff_mem_nonZeroDivisors`：absNorm_pos_iff_mem_nonZeroDi
visors {I : Ideal S} : 0 < absNorm I ↔ I in (Ideal S)⁰
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem absNorm_pos_of_nonZeroDivisors (I : (Ideal S)⁰) : 0 < absNorm (I : Ideal S) :=
  absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
/-
**Ideal.finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：finiteIndex {I : Ideal S} (hI : I != ⊥) : I.toAddSubgroup.FiniteIndex
参数：hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.finiteIndex_iff`：∀ {G : Type u_1} [inst : AddGroup G] {H : A
ddSubgroup G}, H.FiniteIndex ↔ H.index ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.absNorm_eq_index`：absNorm_eq_index (I : Ideal S) : absNorm I = I.t
oAddSubgroup.index
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.absNorm_eq_zero_iff`：absNorm_eq_zero_iff {I : Ideal S} : Ideal.abs
Norm I = 0 ↔ I = ⊥
-/
lemma finiteIndex {I : Ideal S} (hI : I ≠ ⊥) : I.toAddSubgroup.FiniteIndex := by
  rwa [AddSubgroup.finiteIndex_iff, ← absNorm_eq_index, Ne, absNorm_eq_zero_iff]

open AddSubgroup in
/-
**Ideal.isFiniteRelIndex** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isFiniteRelIndex {I : Ideal S} (hI : I != ⊥) (J : Ideal S) : I.toAddSubgro
up.IsFiniteRelIndex J.toAddSubgroup
参数：hI : I != ⊥；J : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.finiteIndex`：finiteIndex {I : Ideal S} (hI : I != ⊥) : I.toAddSubg
roup.FiniteIndex
· 使用定理 `AddSubgroup.isFiniteRelIndex_of_finiteIndex`：∀ {G : Type u_1} [inst : Ad
dGroup G] {H K : AddSubgroup G} [h : H.FiniteIndex], H.IsFiniteRelIndex K
-/
lemma isFiniteRelIndex {I : Ideal S} (hI : I ≠ ⊥) (J : Ideal S) :
    I.toAddSubgroup.IsFiniteRelIndex J.toAddSubgroup := by
  have := finiteIndex hI
  exact isFiniteRelIndex_of_finiteIndex

/-- The norm of a maximal ideal is a prime power.
The prime is `(P.under ℤ).absNorm` and the exponent is `(P.under ℤ).inertialDeg P`.
See `Ideal.absNorm_pow_inertiaDeg`. -/
/-
**Ideal.exists_prime_and_absNorm_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_prime_and_absNorm_eq_pow (P : Ideal S) [P.IsMaximal] : exists p n, 
0 < n ∧ ↑p in P ∧ p.Prime ∧ P.absNorm = p ^ n
参数：P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.Free.instIsTorsionFree`：∀ (R : Type u) (M : Type v) [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R 
M], Module.IsTorsio…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用引理 `CharZero.of_isAddTorsionFree`：CharZero.of_isAddTorsionFree [Nontrivial M
] [IsAddTorsionFree M] : CharZero R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Submodule.finiteQuotientOfFreeOfRankEq`：finiteQuotientOfFreeOfRankEq [Mo
dule.Free Int M] [Module.Finite Int M] (N : Submodule Int M) (h : Module.finrank
 Int N = Module.finrank Int …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.finrank_eq_finrank`：Ideal.finrank_eq_finrank [Finite ι] (b : Basis
 ι R S) (I : Ideal S) (hI : I != ⊥) : Module.finrank R (restrictScalars R I) = M
odule.finrank …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.IsMaximal.ne_bot_of_isIntegral_int`：Ideal.IsMaximal.ne_bot_of_isIn
tegral_int [CharZero R] [Algebra.IsIntegral Int R] (I : Ideal R) [I.IsMaximal] :
 I != ⊥
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Ideal.absNorm_mem`：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I

--- 原说明 ---
The norm of a maximal ideal is a prime power.
The prime is `(P.under ℤ).absNorm` and the exponent is `(P.under ℤ).inertialDeg 
P`.
See `Ideal.absNorm_pow_inertiaDeg`.
-/
lemma exists_prime_and_absNorm_eq_pow (P : Ideal S) [P.IsMaximal] :
    ∃ p n, 0 < n ∧ ↑p ∈ P ∧ p.Prime ∧ P.absNorm = p ^ n := by
  have : IsAddTorsionFree S := .of_isTorsionFree ℤ _
  have := CharZero.of_isAddTorsionFree S S
  have : Finite (S ⧸ P) := Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars ℤ)
    (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
      (Ideal.IsMaximal.ne_bot_of_isIntegral_int P))
  cases nonempty_fintype (S ⧸ P)
  let := Ideal.Quotient.field P
  obtain ⟨p, hpR⟩ := CharP.exists (S ⧸ P)
  obtain ⟨n, hp, e⟩ := FiniteField.card (S ⧸ P) p
  have hP : P.absNorm = p ^ (n : ℕ) := (Nat.card_eq_fintype_card.trans e:)
  refine ⟨p, n, n.2, ?_, hp, hP⟩
  rw [← Ideal.IsPrime.pow_mem_iff_mem (I := P) inferInstance _ n.pos, ← Nat.cast_pow, ← hP]
  exact P.absNorm_mem
/-
**Ideal.exists_isMaximal_dvd_of_dvd_absNorm** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_isMaximal_dvd_of_dvd_absNorm {p : Int} (hp : Prime p) (I : Ideal S)
 (hI : p ∣ I.absNorm) : exists P : Ideal S, P.IsMaximal ∧ P.under Int = .span {p
} ∧ P ∣ I
参数：hp : Prime p；I : Ideal S；hI : p ∣ I.absNorm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.Free.instIsTorsionFree`：∀ (R : Type u) (M : Type v) [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R 
M], Module.IsTorsio…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用引理 `CharZero.of_isAddTorsionFree`：CharZero.of_isAddTorsionFree [Nontrivial M
] [IsAddTorsionFree M] : CharZero R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `UniqueFactorizationMonoid.induction_on_prime`：induction_on_prime {P : α 
-> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x) (h₃ : forall a 
p : α, a != 0 -> Prime p -> P a ->…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.exists_ideal_over_maximal_of_isIntegral`：exists_ideal_over_maximal
_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [P_max : IsMaximal P] (hP 
: RingHom.ker (algebraMap R S) <= P…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Prime.not_dvd_one`：not_dvd_one : ¬p ∣ 1
· 使用定理 `Ideal.absNorm_top`：absNorm_top : absNorm (⊤ : Ideal S) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 55 条，此处仅展示前 30 条）
-/
lemma exists_isMaximal_dvd_of_dvd_absNorm
    {p : ℤ} (hp : Prime p) (I : Ideal S) (hI : p ∣ I.absNorm) :
    ∃ P : Ideal S, P.IsMaximal ∧ P.under ℤ = .span {p} ∧ P ∣ I := by
  have : IsAddTorsionFree S := .of_isTorsionFree ℤ _
  have := CharZero.of_isAddTorsionFree S S
  have hpMax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (Ideal.span {p})
      (fun x ↦ by simp +contextual)
    exact ⟨Q, hQ, e, dvd_zero _⟩
  | h₂ I hI' =>
    obtain rfl : I = ⊤ := by simpa using hI'
    cases hp.not_dvd_one (by simpa using hI)
  | h₃ I P hI' hP IH =>
    simp only [_root_.map_mul, Nat.cast_mul, hp.dvd_mul] at hI
    cases hI with
    | inr h =>
      obtain ⟨Q, h₁, h₂, h₃⟩ := IH h
      exact ⟨Q, h₁, h₂, dvd_mul_of_dvd_right h₃ _⟩
    | inl hI =>
      have := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      refine ⟨P, this, (hpMax.eq_of_le (by simpa using this.ne_top) ?_).symm, dvd_mul_right _ _⟩
      obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      rw [H, Nat.cast_pow, dvd_prime_pow (Nat.prime_iff_prime_int.mp hq)] at hI
      obtain ⟨m, hmn, hp⟩ := hI
      rw [Ideal.span_singleton_le_iff_mem]
      have : m ≠ 0 := fun h ↦ hpMax.ne_top (Ideal.span_singleton_eq_top.mpr (by simpa [h] using hp))
      exact Ideal.mem_of_dvd _ hp.symm.dvd (Ideal.pow_mem_of_mem _ (by simpa) _ this.bot_lt)

/-- A version that takes a natural number and `Nat.Prime`. -/
/-
**Ideal.exists_isMaximal_dvd_of_dvd_absNorm'** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_isMaximal_dvd_of_dvd_absNorm' {p : Nat} (hp : p.Prime) (I : Ideal S
) (hI : p ∣ I.absNorm) : exists P : Ideal S, P.IsMaximal ∧ P.under Int = .span {
(p : Int)} ∧ P ∣ I
参数：hp : p.Prime；I : Ideal S；hI : p ∣ I.absNorm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_isMaximal_dvd_of_dvd_absNorm`：exists_isMaximal_dvd_of_dvd_a
bsNorm {p : Int} (hp : Prime p) (I : Ideal S) (hI : p ∣ I.absNorm) : exists P : 
Ideal S, P.IsMaximal ∧ P.under …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.prime_iff_natAbs_prime`：prime_iff_natAbs_prime {k : Int} : Prime k ↔
 Nat.Prime k.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A version that takes a natural number and `Nat.Prime`.
-/
lemma exists_isMaximal_dvd_of_dvd_absNorm'
    {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : p ∣ I.absNorm) :
    ∃ P : Ideal S, P.IsMaximal ∧ P.under ℤ = .span {(p : ℤ)} ∧ P ∣ I :=
  exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
    (by exact_mod_cast hI)
/-
**Ideal.finite_setOfPred_absNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finite_setOfPred_absNorm_eq [CharZero S] (n : Nat) : {I : Ideal S | Ideal.
absNorm I = n}.Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.absNorm_ne_zero_iff`：absNorm_ne_zero_iff (I : Ideal S) : Ideal.abs
Norm I != 0 ↔ Finite (S ⧸ I)
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用引理 `Ideal.comap_map_mk`：comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I <
= J) : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J
· 使用定理 `Ideal.span_singleton_absNorm_le`：span_singleton_absNorm_le (I : Ideal S)
 : Ideal.span {(Ideal.absNorm I : S)} <= I
-/
theorem finite_setOfPred_absNorm_eq [CharZero S] (n : ℕ) :
    {I : Ideal S | Ideal.absNorm I = n}.Finite := by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · simp only [hn, absNorm_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.finite_singleton]
  · let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
    refine Set.Finite.of_finite_image (f := f) ?_ ?_
    · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
        let g := ((↑) : Ideal (S ⧸ @Ideal.span S _ {↑n}) → Set (S ⧸ @Ideal.span S _ {↑n}))
        refine Set.Finite.of_finite_image (f := g) ?_ SetLike.coe_injective.injOn
        exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      rw [← absNorm_ne_zero_iff, absNorm_span_singleton]
      simpa only [Ne, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff, Nat.cast_eq_zero] using
        ne_of_gt hn
    · intro I hI J hJ h
      rw [← comap_map_mk (span_singleton_absNorm_le I), ← hI.symm, ←
        comap_map_mk (span_singleton_absNorm_le J), ← hJ.symm]
      congr

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_eq := finite_setOfPred_absNorm_eq
/-
**Ideal.finite_setOfPred_absNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finite_setOfPred_absNorm_le [CharZero S] (n : Nat) : {I : Ideal S | Ideal.
absNorm I <= n}.Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Ideal.finite_setOfPred_absNorm_eq`：finite_setOfPred_absNorm_eq [CharZero
 S] (n : Nat) : {I : Ideal S | Ideal.absNorm I = n}.Finite
-/
theorem finite_setOfPred_absNorm_le [CharZero S] (n : ℕ) :
    {I : Ideal S | Ideal.absNorm I ≤ n}.Finite := by
  rw [show {I : Ideal S | Ideal.absNorm I ≤ n} =
    (⋃ i ∈ Set.Icc 0 n, {I : Ideal S | Ideal.absNorm I = i}) by ext; simp]
  refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOfPred_absNorm_eq i)

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_le := finite_setOfPred_absNorm_le
/-
**Ideal.finite_setOfPred_absNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finite_setOfPred_absNorm_le [CharZero S] (n : Nat) : {I : Ideal S | Ideal.
absNorm I <= n}.Finite
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Ideal.finite_setOfPred_absNorm_eq`：finite_setOfPred_absNorm_eq [CharZero
 S] (n : Nat) : {I : Ideal S | Ideal.absNorm I = n}.Finite
-/
theorem finite_setOfPred_absNorm_le₀ [CharZero S] (n : ℕ) :
    {I : (Ideal S)⁰ | Ideal.absNorm (I : Ideal S) ≤ n}.Finite := by
  have : Finite {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I ↦ absNorm I ≤ n)).symm

@[deprecated (since := "2026-07-09")]
alias finite_setOf_absNorm_le₀ := finite_setOfPred_absNorm_le₀
/-
**Ideal.card_norm_le_eq_card_norm_le_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：card_norm_le_eq_card_norm_le_add_one (n : Nat) [CharZero S] : Nat.card {I 
: Ideal S // absNorm I <= n} = Nat.card {I : (Ideal S)⁰ // absNorm (I : Ideal S)
 <= n} + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Ideal.finite_setOfPred_absNorm_le`：finite_setOfPred_absNorm_le [CharZero
 S] (n : Nat) : {I : Ideal S | Ideal.absNorm I <= n}.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.disjoint_iff`：disjoint_iff [forall i, OrderBot (α' i)] {f g : forall 
i, α' i} : Disjoint f g ↔ forall i, Disjoint (f i) (g i)
· 使用定理 `Prop.disjoint_iff`：Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧
 Q)
· 使用定理 `Nat.card_sum`：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Na
t.card α + Nat.card β
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors`：absNorm_ne_zero_iff_mem_n
onZeroDivisors {I : Ideal S} : absNorm I != 0 ↔ I in (Ideal S)⁰
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Ideal.absNorm_eq_zero_iff`：absNorm_eq_zero_iff {I : Ideal S} : Ideal.abs
Norm I = 0 ↔ I = ⊥
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem card_norm_le_eq_card_norm_le_add_one (n : ℕ) [CharZero S] :
    Nat.card {I : Ideal S // absNorm I ≤ n} =
      Nat.card {I : (Ideal S)⁰ // absNorm (I : Ideal S) ≤ n} + 1 := by
  classical
  have : Finite {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  have : Finite {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ I ∈ (Ideal S)⁰)
    (fun I ↦ absNorm I ≤ n))]
  let e : {I : Ideal S // absNorm I ≤ n} ≃ {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} ⊕
      {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I ≤ n} := by
    refine (Equiv.subtypeEquivRight ?_).trans (subtypeOrEquiv _ _ ?_)
    · intro _
      simp_rw [← or_and_right, em, true_and]
    · exact Pi.disjoint_iff.mpr fun I ↦ Prop.disjoint_iff.mpr (by tauto)
  simp_rw [Nat.card_congr e, Nat.card_sum, add_right_inj]
  conv_lhs =>
    enter [1, 1, I]
    rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors, ne_eq, not_not, and_iff_left_iff_imp.mpr
      (fun h ↦ by rw [h]; exact Nat.zero_le n), absNorm_eq_zero_iff]
  rw [Nat.card_unique]
/-
**Ideal.norm_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：norm_dvd_iff {x : S} (hx : Prime (Algebra.norm Int x)) {y : Int} : Algebra
.norm Int x ∣ y ↔ x ∣ y
参数：hx : Prime (Algebra.norm Int x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.span_singleton_absNorm`：span_singleton_absNorm {I : Ideal S} (hI :
 (Ideal.absNorm I).Prime) : Ideal.span (singleton (Ideal.absNorm I : Int)) = I.c
omap (algebraMap I…
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Int.prime_iff_natAbs_prime`：prime_iff_natAbs_prime {k : Int} : Prime k ↔
 Nat.Prime k.natAbs
· 使用定理 `Int.natAbs_dvd`：∀ {a b : ℤ}, ↑a.natAbs ∣ b ↔ a ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_dvd_iff {x : S} (hx : Prime (Algebra.norm ℤ x)) {y : ℤ} :
    Algebra.norm ℤ x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x), ← eq_intCast (algebraMap ℤ S), ← Ideal.mem_comap,
    ← Ideal.span_singleton_absNorm, Ideal.mem_span_singleton, Ideal.absNorm_span_singleton,
    Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

end Ideal

end RingOfIntegers

section Int

open Ideal

@[simp]
/-
**Int.ideal_span_absNorm_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.ideal_span_absNorm_eq_self (J : Ideal Int) : span {(absNorm J : Int)} 
= J
参数：J : Ideal Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `Algebra.norm_self`：norm_self : Algebra.norm R = MonoidHom.id R
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Ideal.span_singleton_abs`：span_singleton_abs [LinearOrder α] : span {|x|
} = span {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Int.ideal_span_absNorm_eq_self (J : Ideal ℤ) :
    span {(absNorm J : ℤ)} = J := by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp

@[simp]
/-
**Int.prime_absNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.prime_absNorm (J : Ideal Int) : (absNorm J).Prime ↔ Prime J
参数：J : Ideal Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.norm_self`：norm_self : Algebra.norm R = MonoidHom.id R
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Int.prime_absNorm (J : Ideal ℤ) :
    (absNorm J).Prime ↔ Prime J := by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp [prime_span_singleton_iff, prime_iff_natAbs_prime]

end Int

end abs_norm

