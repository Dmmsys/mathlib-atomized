/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PerfectClosure

/-!

# `IsPerfectClosure` predicate

This file contains `IsPerfectClosure` which asserts that `L` is a perfect closure of `K` under a
ring homomorphism `i : K →+* L`, as well as its basic properties.

## Main definitions

- `pNilradical`: given a natural number `p`, the `p`-nilradical of a ring is defined to be the
  nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
  (`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
  `x ^ p ^ n = 0` for some `n` (`mem_pNilradical`).

- `IsPRadical`: a ring homomorphism `i : K →+* L` of characteristic `p` rings is called `p`-radical,
  if or any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`,
  and the kernel of `i` is contained in the `p`-nilradical of `K`.
  A generalization of purely inseparable extension for fields.

- `IsPerfectClosure`: if `i : K →+* L` is `p`-radical ring homomorphism, then it makes `L` a
  perfect closure of `K`, if `L` is perfect.

  Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
  that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
  `PerfectRing` which has `ExpChar` as a prerequisite.

- `PerfectRing.lift`: if a `p`-radical ring homomorphism `K →+* L` is given, `M` is a perfect ring,
  then any ring homomorphism `K →+* M` can be lifted to `L →+* M`.
  This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`.

- `PerfectRing.liftEquiv`: `K →+* M` is in one-to-one correspondence with `L →+* M`,
  given by `PerfectRing.lift`. This generalizes `PerfectClosure.lift`.

- `IsPerfectClosure.equiv`: perfect closures of a ring are isomorphic.

## Main results

- `IsPRadical.trans`: composition of `p`-radical ring homomorphisms is also `p`-radical.

- `PerfectClosure.isPRadical`: the absolute perfect closure `PerfectClosure` is a `p`-radical
  extension over the base ring, in particular, it is a perfect closure of the base ring.

- `IsPRadical.isPurelyInseparable`, `IsPurelyInseparable.isPRadical`: `p`-radical and
  purely inseparable are equivalent for fields.

- The (relative) perfect closure `perfectClosure` is a perfect closure
  (inferred from `IsPurelyInseparable.isPRadical` automatically by Lean).

## Tags

perfect ring, perfect closure, purely inseparable

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

/-- Given a natural number `p`, the `p`-nilradical of a ring is defined to be the
nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
(`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
`x ^ p ^ n = 0` for some `n` (`mem_pNilradical`). -/
/-
**pNilradical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pNilradical (R : Type*) [CommSemiring R] (p : Nat) : Ideal R
参数：R : Type*；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural number `p`, the `p`-nilradical of a ring is defined to be the
nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero 
ideal if `p ≤ 1`
(`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x
` such that
`x ^ p ^ n = 0` for some `n` (`mem_pNilradical`).
-/
def pNilradical (R : Type*) [CommSemiring R] (p : ℕ) : Ideal R := if 1 < p then nilradical R else ⊥
/-
**pNilradical_le_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_le_nilradical {R : Type*} [CommSemiring R] {p : Nat} : pNilrad
ical R p <= nilradical R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pNilradical.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ), pNil
radical R p = if 1 < p then nilradical R else ⊥
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem pNilradical_le_nilradical {R : Type*} [CommSemiring R] {p : ℕ} :
    pNilradical R p ≤ nilradical R := by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]
/-
**pNilradical_eq_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : Nat} (hp : 1 <
 p) : pNilradical R p = nilradical R
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pNilradical.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ), pNil
radical R p = if 1 < p then nilradical R else ⊥
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : ℕ} (hp : 1 < p) :
    pNilradical R p = nilradical R := by rw [pNilradical, if_pos hp]
/-
**pNilradical_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : Nat} (hp : ¬ 1 < p) :
 pNilradical R p = ⊥
参数：hp : ¬ 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pNilradical.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ), pNil
radical R p = if 1 < p then nilradical R else ⊥
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : ℕ} (hp : ¬ 1 < p) :
    pNilradical R p = ⊥ := by rw [pNilradical, if_neg hp]
/-
**pNilradical_eq_bot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p : Nat} (hp : p <= 1) :
 pNilradical R p = ⊥
参数：hp : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pNilradical_eq_bot`：pNilradical_eq_bot {R : Type*} [CommSemiring R] {p :
 Nat} (hp : ¬ 1 < p) : pNilradical R p = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p : ℕ} (hp : p ≤ 1) :
    pNilradical R p = ⊥ := pNilradical_eq_bot (not_lt.2 hp)
/-
**pNilradical_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_prime {R : Type*} [CommSemiring R] {p : Nat} (hp : p.Prime) : 
pNilradical R p = nilradical R
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pNilradical_eq_nilradical`：pNilradical_eq_nilradical {R : Type*} [CommSe
miring R] {p : Nat} (hp : 1 < p) : pNilradical R p = nilradical R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem pNilradical_prime {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) :
    pNilradical R p = nilradical R := pNilradical_eq_nilradical hp.one_lt
/-
**pNilradical_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_one {R : Type*} [CommSemiring R] : pNilradical R 1 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pNilradical_eq_bot'`：pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p
 : Nat} (hp : p <= 1) : pNilradical R p = ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem pNilradical_one {R : Type*} [CommSemiring R] :
    pNilradical R 1 = ⊥ := pNilradical_eq_bot' rfl.le
/-
**mem_pNilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} {x : R} : x in pNil
radical R p ↔ exists n : Nat, x ^ p ^ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pNilradical_eq_nilradical`：pNilradical_eq_nilradical {R : Type*} [CommSe
miring R] {p : Nat} (hp : 1 < p) : pNilradical R p = nilradical R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pNilradical_eq_bot`：pNilradical_eq_bot {R : Type*} [CommSemiring R] {p :
 Nat} (hp : ¬ 1 < p) : pNilradical R p = ⊥
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `subsingleton_of_zero_eq_one`：∀ {M₀ : Type u_1} [inst : MulZeroOneClass M
₀], 0 = 1 → Subsingleton M₀
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem mem_pNilradical {R : Type*} [CommSemiring R] {p : ℕ} {x : R} :
    x ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = 0 := by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ ↦ ⟨n, ?_⟩, fun ⟨n, h⟩ ↦ ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le), pow_add, h, mul_zero]
  rw [pNilradical_eq_bot hp, Ideal.mem_bot]
  refine ⟨fun h ↦ ⟨0, by rw [pow_zero, pow_one, h]⟩, fun ⟨n, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hp) with hp | hp
  · by_cases hn : n = 0
    · rwa [hn, pow_zero, pow_one] at h
    rw [hp, zero_pow hn, pow_zero] at h
    subsingleton [subsingleton_of_zero_eq_one h.symm]
  rwa [hp, one_pow, pow_one] at h
/-
**sub_mem_pNilradical_iff_pow_expChar_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_mem_pNilradical_iff_pow_expChar_pow_eq {R : Type*} [CommRing R] {p : N
at} [ExpChar R p] {x y : R} : x - y in pNilradical R p ↔ exists n : Nat, x ^ p ^
 n = y ^ p ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `sub_pow_expChar_pow`：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n -
 y ^ p ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_mem_pNilradical_iff_pow_expChar_pow_eq {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    {x y : R} : x - y ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = y ^ p ^ n := by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]
/-
**pow_expChar_pow_inj_of_pNilradical_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_expChar_pow_inj_of_pNilradical_eq_bot (R : Type*) [CommRing R] (p : Na
t) [ExpChar R p] (h : pNilradical R p = ⊥) (n : Nat) : Function.Injective fun x 
: R => x ^ p ^ n
参数：R : Type*；p : Nat；h : pNilradical R p = ⊥；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_mem_pNilradical_iff_pow_expChar_pow_eq`：sub_mem_pNilradical_iff_pow_
expChar_pow_eq {R : Type*} [CommRing R] {p : Nat} [ExpChar R p] {x y : R} : x - 
y in pNilradical R p ↔ exists n …
-/
theorem pow_expChar_pow_inj_of_pNilradical_eq_bot (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]
    (h : pNilradical R p = ⊥) (n : ℕ) : Function.Injective fun x : R ↦ x ^ p ^ n := fun _ _ H ↦
  sub_eq_zero.1 <| Ideal.mem_bot.1 <| h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩
/-
**pNilradical_eq_bot_of_frobenius_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pNilradical_eq_bot_of_frobenius_inj (R : Type*) [CommSemiring R] (p : Nat)
 [ExpChar R p] (h : Function.Injective (frobenius R p)) : pNilradical R p = ⊥
参数：R : Type*；p : Nat；h : Function.Injective (frobenius R p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_pNilradical`：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} 
{x : R} : x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `coe_iterateFrobenius`：coe_iterateFrobenius : iterateFrobenius R p n = (f
robenius R p)^[n]
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem pNilradical_eq_bot_of_frobenius_inj (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    (h : Function.Injective (frobenius R p)) : pNilradical R p = ⊥ := bot_unique fun x ↦ by
  rw [mem_pNilradical, Ideal.mem_bot]
  exact fun ⟨n, _⟩ ↦ h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])
/-
**PerfectRing.pNilradical_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PerfectRing.pNilradical_eq_bot (R : Type*) [CommSemiring R] (p : Nat) [Exp
Char R p] [PerfectRing R p] : pNilradical R p = ⊥
参数：R : Type*；p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pNilradical_eq_bot_of_frobenius_inj`：pNilradical_eq_bot_of_frobenius_inj
 (R : Type*) [CommSemiring R] (p : Nat) [ExpChar R p] (h : Function.Injective (f
robenius R p)) : pNilradi…
· 使用定理 `injective_frobenius`：injective_frobenius : Injective (frobenius R p)
-/
theorem PerfectRing.pNilradical_eq_bot (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    [PerfectRing R p] : pNilradical R p = ⊥ :=
  pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

section IsPerfectClosure

variable {K L M N : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (f : L →+* M) (p : ℕ)

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it is called
`p`-radical if the following conditions are satisfied:

- For any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`.
- The kernel of `i` is contained in the `p`-nilradical of `K`.

It is a generalization of purely inseparable extension for fields. -/
@[mk_iff]
/-
**IsPRadical** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{K : Type u_1} → {L : Type u_2} → [inst : CommSemiring K] → [inst_1 : Comm
Semiring L] → (K →+* L) → ℕ → Prop
参数：K →+* L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it is 
called
`p`-radical if the following conditions are satisfied:

- For any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contain
ed in `K`.
- The kernel of `i` is contained in the `p`-nilradical of `K`.

It is a generalization of purely inseparable extension for fields.
-/
class IsPRadical : Prop where
  pow_mem' : ∀ x : L, ∃ (n : ℕ) (y : K), i y = x ^ p ^ n
  ker_le' : RingHom.ker i ≤ pNilradical K p
/-
**IsPRadical.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPRadical.pow_mem [IsPRadical i p] (x : L) : exists (n : Nat) (y : K), i 
y = x ^ p ^ n
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.pow_mem'`：∀ {K : Type u_1} {L : Type u_2} {inst : CommSemirin
g K} {inst_1 : CommSemiring L} {i : K →+* L} {p : ℕ}   [self : IsPRadical i p] (
x : L), ∃…
-/
theorem IsPRadical.pow_mem [IsPRadical i p] (x : L) :
    ∃ (n : ℕ) (y : K), i y = x ^ p ^ n := pow_mem' x
/-
**IsPRadical.ker_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPRadical.ker_le [IsPRadical i p] : RingHom.ker i <= pNilradical K p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.ker_le'`：∀ {K : Type u_1} {L : Type u_2} {inst : CommSemiring
 K} {inst_1 : CommSemiring L} {i : K →+* L} {p : ℕ}   [self : IsPRadical i p], R
ingHom.k…
-/
theorem IsPRadical.ker_le [IsPRadical i p] :
    RingHom.ker i ≤ pNilradical K p := ker_le'
/-
**IsPRadical.comap_pNilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPRadical.comap_pNilradical [IsPRadical i p] : (pNilradical L p).comap i 
= pNilradical K p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_pNilradical`：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} 
{x : R} : x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `IsPRadical.ker_le`：IsPRadical.ker_le [IsPRadical i p] : RingHom.ker i <=
 pNilradical K p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem IsPRadical.comap_pNilradical [IsPRadical i p] :
    (pNilradical L p).comap i = pNilradical K p := by
  refine le_antisymm (fun x h ↦ mem_pNilradical.2 ?_) (fun x h ↦ ?_)
  · obtain ⟨n, h⟩ := mem_pNilradical.1 <| Ideal.mem_comap.1 h
    obtain ⟨m, h⟩ := mem_pNilradical.1 <| ker_le i p ((map_pow i x _).symm ▸ h)
    exact ⟨n + m, by rwa [pow_add, pow_mul]⟩
  simp only [Ideal.mem_comap, mem_pNilradical] at h ⊢
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simpa only [map_pow, map_zero] using congr(i $h)⟩

variable (K) in
/-
**IsPRadical.of_id** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsPRadical.of_id : IsPRadical (RingHom.id K) p where pow_mem' x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
instance IsPRadical.of_id : IsPRadical (RingHom.id K) p where
  pow_mem' x := ⟨0, x, by simp⟩
  ker_le' x h := by convert! Ideal.zero_mem _

/-- Composition of `p`-radical ring homomorphisms is also `p`-radical. -/
/-
**IsPRadical.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPRadical.trans [IsPRadical i p] [IsPRadical f p] : IsPRadical (f.comp i)
 p where pow_mem' x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.pow_mem`：IsPRadical.pow_mem [IsPRadical i p] (x : L) : exists
 (n : Nat) (y : K), i y = x ^ p ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsPRadical.comap_pNilradical`：IsPRadical.comap_pNilradical [IsPRadical i
 p] : (pNilradical L p).comap i = pNilradical K p
· 使用定理 `IsPRadical.ker_le`：IsPRadical.ker_le [IsPRadical i p] : RingHom.ker i <=
 pNilradical K p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…

--- 原说明 ---
Composition of `p`-radical ring homomorphisms is also `p`-radical.
-/
theorem IsPRadical.trans [IsPRadical i p] [IsPRadical f p] :
    IsPRadical (f.comp i) p where
  pow_mem' x := by
    obtain ⟨n, y, hy⟩ := pow_mem f p x
    obtain ⟨m, z, hz⟩ := pow_mem i p y
    exact ⟨n + m, z, by rw [RingHom.comp_apply, hz, map_pow, hy, pow_add, pow_mul]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at h
    simpa only [← Ideal.mem_comap, comap_pNilradical] using ker_le f p h

/-- If `i : K →+* L` is a `p`-radical ring homomorphism, then it makes `L` a perfect closure
of `K`, if `L` is perfect.
In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`).

Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
`PerfectRing` which has `ExpChar` as a prerequisite. -/
@[nolint unusedArguments]
/-
**IsPerfectClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsPerfectClosure [ExpChar L p] [PerfectRing L p]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i : K →+* L` is a `p`-radical ring homomorphism, then it makes `L` a perfect
 closure
of `K`, if `L` is perfect.
In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`).

Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is prese
nt. A caveat is
that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is simil
ar to
`PerfectRing` which has `ExpChar` as a prerequisite.
-/
abbrev IsPerfectClosure [ExpChar L p] [PerfectRing L p] := IsPRadical i p

/-- If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings, such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`. -/
/-
**RingHom.pNilradical_le_ker_of_perfectRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.pNilradical_le_ker_of_perfectRing [ExpChar L p] [PerfectRing L p] 
: pNilradical K p <= RingHom.ker i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_pNilradical`：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} 
{x : R} : x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iterateFrobeniusEquiv_apply`：∀ (R : Type u_1) (p n : ℕ) [inst : CommSemi
ring R] [inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (iterateFro
beniusEquiv R p n…
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…

--- 原说明 ---
If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings,
 such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`.
-/
theorem RingHom.pNilradical_le_ker_of_perfectRing [ExpChar L p] [PerfectRing L p] :
    pNilradical K p ≤ RingHom.ker i := fun x h ↦ by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

variable [ExpChar L p] in
/-
**IsPerfectClosure.ker_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPerfectClosure.ker_eq [PerfectRing L p] [IsPerfectClosure i p] : RingHom
.ker i = pNilradical K p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsPRadical.ker_le'`：∀ {K : Type u_1} {L : Type u_2} {inst : CommSemiring
 K} {inst_1 : CommSemiring L} {i : K →+* L} {p : ℕ}   [self : IsPRadical i p], R
ingHom.k…
· 使用定理 `RingHom.pNilradical_le_ker_of_perfectRing`：RingHom.pNilradical_le_ker_of
_perfectRing [ExpChar L p] [PerfectRing L p] : pNilradical K p <= RingHom.ker i
-/
theorem IsPerfectClosure.ker_eq [PerfectRing L p] [IsPerfectClosure i p] :
    RingHom.ker i = pNilradical K p :=
  IsPRadical.ker_le'.antisymm (i.pNilradical_le_ker_of_perfectRing p)

namespace PerfectRing

/- NOTE: To define `PerfectRing.lift_aux`, only the `IsPRadical.pow_mem` is required, but not
`IsPRadical.ker_le`. But in order to use typeclass, here we require the whole `IsPRadical`. -/

variable [ExpChar M p] [PerfectRing M p] [IsPRadical i p]

/-
**PerfectRing.lift_aux** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^ p ^ y.1
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.pow_mem`：IsPRadical.pow_mem [IsPRadical i p] (x : L) : exists
 (n : Nat) (y : K), i y = x ^ p ^ n
-/
theorem lift_aux (x : L) : ∃ y : ℕ × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical (in fact only the `IsPRadical.pow_mem` is required) and `M` is a perfect ring,
then one can define a map `L → M` which maps an element `x` of `L` to `y ^ (p ^ -n)` if
`x ^ (p ^ n)` is equal to some element `y` of `K`. -/
/-
**PerfectRing.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `PerfectRing`。
形式化陈述：liftAux (x : L) : M
参数：x : L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_aux`：lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^
 p ^ y.1

--- 原说明 ---
If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` 
rings, such that
`i` is `p`-radical (in fact only the `IsPRadical.pow_mem` is required) and `M` i
s a perfect ring,
then one can define a map `L → M` which maps an element `x` of `L` to `y ^ (p ^ 
-n)` if
`x ^ (p ^ n)` is equal to some element `y` of `K`.
-/
def liftAux (x : L) : M := (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
  (j (Classical.choose (lift_aux i p x)).2)

@[simp]
/-
**PerfectRing.liftAux_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftAux_self_apply [ExpChar L p] [PerfectRing L p] (x : L) : liftAux i i p
 x = x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_aux`：lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^
 p ^ y.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.liftAux.eq_1`：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3}
 [inst : CommSemiring K] [inst_1 : CommSemiring L]   [inst_2 : CommSemiring M] (
i : K →+* L) (…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用定理 `iterateFrobeniusEquiv_apply`：∀ (R : Type u_1) (p n : ℕ) [inst : CommSemi
ring R] [inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (iterateFro
beniusEquiv R p n…
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem liftAux_self_apply [ExpChar L p] [PerfectRing L p] (x : L) : liftAux i i p x = x := by
  rw [liftAux, Classical.choose_spec (lift_aux i p x), ← iterateFrobenius_def,
    ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

@[simp]
/-
**PerfectRing.liftAux_self** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftAux_self [ExpChar L p] [PerfectRing L p] : liftAux i i p = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PerfectRing.liftAux_self_apply`：liftAux_self_apply [ExpChar L p] [Perfec
tRing L p] (x : L) : liftAux i i p x = x
-/
theorem liftAux_self [ExpChar L p] [PerfectRing L p] : liftAux i i p = id :=
  funext (liftAux_self_apply i p)

@[simp]
/-
**PerfectRing.liftAux_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftAux_id_apply (x : K) : liftAux (RingHom.id K) j p x = j x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_aux`：lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^
 p ^ y.1
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.liftAux.eq_1`：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3}
 [inst : CommSemiring K] [inst_1 : CommSemiring L]   [inst_2 : CommSemiring M] (
i : K →+* L) (…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用定理 `iterateFrobeniusEquiv_apply`：∀ (R : Type u_1) (p n : ℕ) [inst : CommSemi
ring R] [inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (iterateFro
beniusEquiv R p n…
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem liftAux_id_apply (x : K) : liftAux (RingHom.id K) j p x = j x := by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux, this, map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply,
    RingEquiv.symm_apply_apply]

@[simp]
/-
**PerfectRing.liftAux_id** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftAux_id : liftAux (RingHom.id K) j p = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PerfectRing.liftAux_id_apply`：liftAux_id_apply (x : K) : liftAux (RingHo
m.id K) j p x = j x
-/
theorem liftAux_id : liftAux (RingHom.id K) j p = j := funext (liftAux_id_apply j p)

end PerfectRing

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M] [CommRing N]
  (i : K →+* L) (j : K →+* M) (k : K →+* N) (f : L →+* M) (g : L →+* N)
  (p : ℕ) [ExpChar M p]


namespace IsPRadical

/-- If `i : K →+* L` is `p`-radical, then for any ring `M` of exponential characteristic `p` whose
`p`-nilradical is zero, the map `(L →+* M) → (K →+* M)` induced by `i` is injective. -/
/-
**IsPRadical.injective_comp_of_pNilradical_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsP
Radical`。
形式化陈述：injective_comp_of_pNilradical_eq_bot [IsPRadical i p] (h : pNilradical M p
 = ⊥) : Function.Injective fun f : L ->+* M => f.comp i
参数：h : pNilradical M p = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsPRadical.pow_mem`：IsPRadical.pow_mem [IsPRadical i p] (x : L) : exists
 (n : Nat) (y : K), i y = x ^ p ^ n
· 使用定理 `pow_expChar_pow_inj_of_pNilradical_eq_bot`：pow_expChar_pow_inj_of_pNilra
dical_eq_bot (R : Type*) [CommRing R] (p : Nat) [ExpChar R p] (h : pNilradical R
 p = ⊥) (n : Nat) : Function.In…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `i : K →+* L` is `p`-radical, then for any ring `M` of exponential characteri
stic `p` whose
`p`-nilradical is zero, the map `(L →+* M) → (K →+* M)` induced by `i` is inject
ive.
-/
theorem injective_comp_of_pNilradical_eq_bot [IsPRadical i p] (h : pNilradical M p = ⊥) :
    Function.Injective fun f : L →+* M ↦ f.comp i := fun f g heq ↦ by
  ext x
  obtain ⟨n, y, hx⟩ := IsPRadical.pow_mem i p x
  apply_fun _ using pow_expChar_pow_inj_of_pNilradical_eq_bot M p h n
  simpa only [← map_pow, ← hx] using! congr($(heq) y)

variable (M)

/-- If `i : K →+* L` is `p`-radical, then for any reduced ring `M` of exponential characteristic
`p`, the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`
and a generalization of `IsPurelyInseparable.injective_comp_algebraMap`. -/
/-
**IsPRadical.injective_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsPRadical`。
形式化陈述：injective_comp [IsPRadical i p] [IsReduced M] : Function.Injective fun f :
 L ->+* M => f.comp i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.injective_comp_of_pNilradical_eq_bot`：injective_comp_of_pNilr
adical_eq_bot [IsPRadical i p] (h : pNilradical M p = ⊥) : Function.Injective fu
n f : L ->+* M => f.comp i
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pNilradical_le_nilradical`：pNilradical_le_nilradical {R : Type*} [CommSe
miring R] {p : Nat} : pNilradical R p <= nilradical R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `nilradical_eq_zero`：nilradical_eq_zero (R : Type*) [CommSemiring R] [IsR
educed R] : nilradical R = 0

--- 原说明 ---
If `i : K →+* L` is `p`-radical, then for any reduced ring `M` of exponential ch
aracteristic
`p`, the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`
and a generalization of `IsPurelyInseparable.injective_comp_algebraMap`.
-/
theorem injective_comp [IsPRadical i p] [IsReduced M] :
    Function.Injective fun f : L →+* M ↦ f.comp i :=
  injective_comp_of_pNilradical_eq_bot i p <| bot_unique <|
    pNilradical_le_nilradical.trans (nilradical_eq_zero M).le

/-- If `i : K →+* L` is `p`-radical, then for any perfect ring `M` of exponential characteristic
`p`, the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`. -/
/-
**IsPRadical.injective_comp_of_perfect** 是 Mathlib 中的一个定理，位于命名空间 `IsPRadical`。
形式化陈述：injective_comp_of_perfect [IsPRadical i p] [PerfectRing M p] : Function.In
jective fun f : L ->+* M => f.comp i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.injective_comp_of_pNilradical_eq_bot`：injective_comp_of_pNilr
adical_eq_bot [IsPRadical i p] (h : pNilradical M p = ⊥) : Function.Injective fu
n f : L ->+* M => f.comp i
· 使用定理 `PerfectRing.pNilradical_eq_bot`：PerfectRing.pNilradical_eq_bot (R : Type
*) [CommSemiring R] (p : Nat) [ExpChar R p] [PerfectRing R p] : pNilradical R p 
= ⊥

--- 原说明 ---
If `i : K →+* L` is `p`-radical, then for any perfect ring `M` of exponential ch
aracteristic
`p`, the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`.
-/
theorem injective_comp_of_perfect [IsPRadical i p] [PerfectRing M p] :
    Function.Injective fun f : L →+* M ↦ f.comp i :=
  injective_comp_of_pNilradical_eq_bot i p (PerfectRing.pNilradical_eq_bot M p)

end IsPRadical

namespace PerfectRing

variable [ExpChar K p] [PerfectRing M p] [IsPRadical i p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux` is well-defined. -/
/-
**PerfectRing.liftAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftAux_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) : liftAux i 
j p x = (iterateFrobeniusEquiv M p n).symm (j y)
参数：x : L；n : Nat；y : K；h : i y = x ^ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_aux`：lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^
 p ^ y.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.liftAux.eq_1`：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3}
 [inst : CommSemiring K] [inst_1 : CommSemiring L]   [inst_2 : CommSemiring M] (
i : K →+* L) (…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_pNilradical`：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} 
{x : R} : x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0
· 使用定理 `IsPRadical.ker_le`：IsPRadical.ker_le [IsPRadical i p] : RingHom.ker i <=
 pNilradical K p
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iterateFrobeniusEquiv_add_apply`：iterateFrobeniusEquiv_add_apply (x : R)
 : iterateFrobeniusEquiv R p (m + n) x = iterateFrobeniusEquiv R p m (iterateFro
beniusEquiv R p n x)
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iterateFrobeniusEquiv_def`：iterateFrobeniusEquiv_def (x : R) : iterateFr
obeniusEquiv R p n x = x ^ p ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `sub_pow_expChar_pow`：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n -
 y ^ p ^ n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` 
rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux` is wel
l-defined.
-/
theorem liftAux_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    liftAux i j p x = (iterateFrobeniusEquiv M p n).symm (j y) := by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p x)
  set n' := (Classical.choose (lift_aux i p x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul, mul_comm, pow_mul, ← h', ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker] at h
  obtain ⟨m, h⟩ := mem_pNilradical.1 (IsPRadical.ker_le i p h)
  refine (iterateFrobeniusEquiv M p (m + n + n')).injective ?_
  conv_lhs => rw [iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply]
  rw [add_assoc, add_comm n n', ← add_assoc,
    iterateFrobeniusEquiv_add_apply (m := m + n'), RingEquiv.apply_symm_apply,
    iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def,
    ← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub,
    add_comm m, add_comm m, pow_add, pow_mul, pow_add, pow_mul, ← sub_pow_expChar_pow, h, map_zero]

variable [ExpChar L p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux`
is a ring homomorphism. This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`. -/
/-
**PerfectRing.lift** 是 Mathlib 中的一个定义，位于命名空间 `PerfectRing`。
形式化陈述：lift : L ->+* M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` 
rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux`
is a ring homomorphism. This is similar to `IsAlgClosed.lift` and `IsSepClosed.l
ift`.
-/
def lift : L →+* M where
  toFun := liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
      liftAux_apply i j p (x1 * x2) (n1 + n2) (y1 ^ p ^ n2 * y2 ^ p ^ n1) (by rw [map_mul,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, mul_pow]),
      map_mul, map_pow, map_pow, map_mul, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply, add_comm n1, iterateFrobeniusEquiv_symm_add_apply,
      ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]
  map_zero' := by simp [liftAux_apply i j p 0 0 0 (by rw [pow_zero, pow_one, map_zero])]
  map_add' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
      liftAux_apply i j p (x1 + x2) (n1 + n2) (y1 ^ p ^ n2 + y2 ^ p ^ n1) (by rw [map_add,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, add_pow_expChar_pow]),
      map_add, map_pow, map_pow, map_add, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply, add_comm n1, iterateFrobeniusEquiv_symm_add_apply,
      ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]
/-
**PerfectRing.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) : lift i j p x 
= (iterateFrobeniusEquiv M p n).symm (j y)
参数：x : L；n : Nat；y : K；h : i y = x ^ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.liftAux_apply`：liftAux_apply (x : L) (n : Nat) (y : K) (h : 
i y = x ^ p ^ n) : liftAux i j p x = (iterateFrobeniusEquiv M p n).symm (j y)
-/
theorem lift_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    lift i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  liftAux_apply i j p _ _ _ h

@[simp]
/-
**PerfectRing.lift_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_comp_apply (x : K) : lift i j p (i x) = j x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.lift_apply`：lift_apply (x : L) (n : Nat) (y : K) (h : i y = 
x ^ p ^ n) : lift i j p x = (iterateFrobeniusEquiv M p n).symm (j y)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `iterateFrobeniusEquiv_zero`：iterateFrobeniusEquiv_zero : iterateFrobeniu
sEquiv R p 0 = RingEquiv.refl R
-/
theorem lift_comp_apply (x : K) : lift i j p (i x) = j x := by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero, pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]
/-
**PerfectRing.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_comp : (lift i j p).comp i = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PerfectRing.lift_comp_apply`：lift_comp_apply (x : K) : lift i j p (i x) 
= j x
-/
theorem lift_comp : (lift i j p).comp i = j := RingHom.ext (lift_comp_apply i j p)
/-
**PerfectRing.lift_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_self_apply [PerfectRing L p] (x : L) : lift i i p x = x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.liftAux_self_apply`：liftAux_self_apply [ExpChar L p] [Perfec
tRing L p] (x : L) : liftAux i i p x = x
-/
theorem lift_self_apply [PerfectRing L p] (x : L) : lift i i p x = x := liftAux_self_apply i p x

@[simp]
/-
**PerfectRing.lift_self** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_self [PerfectRing L p] : lift i i p = RingHom.id L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PerfectRing.liftAux_self_apply`：liftAux_self_apply [ExpChar L p] [Perfec
tRing L p] (x : L) : liftAux i i p x = x
-/
theorem lift_self [PerfectRing L p] : lift i i p = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p)
/-
**PerfectRing.lift_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_id_apply (x : K) : lift (RingHom.id K) j p x = j x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.liftAux_id_apply`：liftAux_id_apply (x : K) : liftAux (RingHo
m.id K) j p x = j x
-/
theorem lift_id_apply (x : K) : lift (RingHom.id K) j p x = j x := liftAux_id_apply j p x

@[simp]
/-
**PerfectRing.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_id : lift (RingHom.id K) j p = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PerfectRing.liftAux_id_apply`：liftAux_id_apply (x : K) : liftAux (RingHo
m.id K) j p x = j x
-/
theorem lift_id : lift (RingHom.id K) j p = j := RingHom.ext (liftAux_id_apply j p)

@[simp]
/-
**PerfectRing.comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：comp_lift : lift i (f.comp i) p = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.injective_comp_of_perfect`：injective_comp_of_perfect [IsPRadi
cal i p] [PerfectRing M p] : Function.Injective fun f : L ->+* M => f.comp i
· 使用定理 `PerfectRing.lift_comp`：lift_comp : (lift i j p).comp i = j
-/
theorem comp_lift : lift i (f.comp i) p = f :=
  IsPRadical.injective_comp_of_perfect _ i p (lift_comp i _ p)
/-
**PerfectRing.comp_lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：comp_lift_apply (x : L) : lift i (f.comp i) p x = f x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.comp_lift`：comp_lift : lift i (f.comp i) p = f
-/
theorem comp_lift_apply (x : L) : lift i (f.comp i) p x = f x := congr($(comp_lift i f p) x)

variable (M) in
/-- If `i : K →+* L` is a homomorphism of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring of characteristic `p`,
then `K →+* M` is in one-to-one correspondence with
`L →+* M`, given by `PerfectRing.lift`. This generalizes `PerfectClosure.lift`. -/
/-
**PerfectRing.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv : (K ->+* M) ≃ (L ->+* M) where toFun j
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_comp`：lift_comp : (lift i j p).comp i = j
· 使用定理 `PerfectRing.comp_lift`：comp_lift : lift i (f.comp i) p = f

--- 原说明 ---
If `i : K →+* L` is a homomorphism of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring of characteristic `p`,
then `K →+* M` is in one-to-one correspondence with
`L →+* M`, given by `PerfectRing.lift`. This generalizes `PerfectClosure.lift`.
-/
def liftEquiv : (K →+* M) ≃ (L →+* M) where
  toFun j := lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p
/-
**PerfectRing.liftEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_apply : liftEquiv M i p j = lift i j p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftEquiv_apply : liftEquiv M i p j = lift i j p := rfl
/-
**PerfectRing.liftEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_symm_apply : (liftEquiv M i p).symm f = f.comp i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem liftEquiv_symm_apply : (liftEquiv M i p).symm f = f.comp i := rfl
/-
**PerfectRing.liftEquiv_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_id_apply : liftEquiv M (RingHom.id K) p j = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_id`：lift_id : lift (RingHom.id K) j p = j
-/
theorem liftEquiv_id_apply : liftEquiv M (RingHom.id K) p j = j :=
  lift_id j p

@[simp]
/-
**PerfectRing.liftEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_id : liftEquiv M (RingHom.id K) p = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `PerfectRing.liftEquiv_id_apply`：liftEquiv_id_apply : liftEquiv M (RingHo
m.id K) p j = j
-/
theorem liftEquiv_id : liftEquiv M (RingHom.id K) p = Equiv.refl _ :=
  Equiv.ext (liftEquiv_id_apply · p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPRadical j p]

@[simp]
/-
**PerfectRing.lift_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_comp_lift : (lift j k p).comp (lift i j p) = lift i k p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.injective_comp_of_perfect`：injective_comp_of_perfect [IsPRadi
cal i p] [PerfectRing M p] : Function.Injective fun f : L ->+* M => f.comp i
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.lift_comp_apply`：lift_comp_apply (x : K) : lift i j p (i x) 
= j x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PerfectRing.lift_comp`：lift_comp : (lift i j p).comp i = j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_lift : (lift j k p).comp (lift i j p) = lift i k p :=
  IsPRadical.injective_comp_of_perfect _ i p (by ext; simp)

@[simp]
/-
**PerfectRing.lift_comp_lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_comp_lift_apply (x : L) : lift j k p (lift i j p x) = lift i k p x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.lift_comp_lift`：lift_comp_lift : (lift j k p).comp (lift i j
 p) = lift i k p
-/
theorem lift_comp_lift_apply (x : L) : lift j k p (lift i j p x) = lift i k p x :=
  congr($(lift_comp_lift i j k p) x)
/-
**PerfectRing.lift_comp_lift_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRin
g`。
形式化陈述：lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) : lift j i p (lift 
i j p x) = x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.lift_comp_lift_apply`：lift_comp_lift_apply (x : L) : lift j 
k p (lift i j p x) = lift i k p x
· 使用定理 `PerfectRing.lift_self_apply`：lift_self_apply [PerfectRing L p] (x : L) :
 lift i i p x = x
-/
theorem lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p (lift i j p x) = x := by
  rw [lift_comp_lift_apply, lift_self_apply]
/-
**PerfectRing.lift_comp_lift_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_comp_lift_eq_id [PerfectRing L p] : (lift j i p).comp (lift i j p) = 
RingHom.id L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PerfectRing.lift_comp_lift_apply_eq_self`：lift_comp_lift_apply_eq_self [
PerfectRing L p] (x : L) : lift j i p (lift i j p x) = x
-/
theorem lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p).comp (lift i j p) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p)

end comp

section liftEquiv_comp

variable [ExpChar N p] [IsPRadical g p] [IsPRadical (g.comp i) p]

@[simp]
/-
**PerfectRing.lift_lift** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_lift : lift g (lift i j p) p = lift (g.comp i) j p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPRadical.injective_comp_of_perfect`：injective_comp_of_perfect [IsPRadi
cal i p] [PerfectRing M p] : Function.Injective fun f : L ->+* M => f.comp i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PerfectRing.lift_comp`：lift_comp : (lift i j p).comp i = j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_lift : lift g (lift i j p) p = lift (g.comp i) j p := by
  refine IsPRadical.injective_comp_of_perfect _ (g.comp i) p ?_
  simp_rw [← RingHom.comp_assoc _ _ (lift g _ p), lift_comp]
/-
**PerfectRing.lift_lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：lift_lift_apply (x : N) : lift g (lift i j p) p x = lift (g.comp i) j p x
参数：x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectRing.lift_lift`：lift_lift : lift g (lift i j p) p = lift (g.comp 
i) j p
-/
theorem lift_lift_apply (x : N) : lift g (lift i j p) p x = lift (g.comp i) j p x :=
  congr($(lift_lift i j g p) x)

@[simp]
/-
**PerfectRing.liftEquiv_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_comp_apply : liftEquiv M g p (liftEquiv M i p j) = liftEquiv M (
g.comp i) p j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_lift`：lift_lift : lift g (lift i j p) p = lift (g.comp 
i) j p
-/
theorem liftEquiv_comp_apply :
    liftEquiv M g p (liftEquiv M i p j) = liftEquiv M (g.comp i) p j := lift_lift i j g p

@[simp]
/-
**PerfectRing.liftEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `PerfectRing`。
形式化陈述：liftEquiv_trans : (liftEquiv M i p).trans (liftEquiv M g p) = liftEquiv M 
(g.comp i) p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `PerfectRing.liftEquiv_comp_apply`：liftEquiv_comp_apply : liftEquiv M g p
 (liftEquiv M i p j) = liftEquiv M (g.comp i) p j
-/
theorem liftEquiv_trans :
    (liftEquiv M i p).trans (liftEquiv M g p) = liftEquiv M (g.comp i) p :=
  Equiv.ext (liftEquiv_comp_apply i · g p)

end liftEquiv_comp

end PerfectRing

namespace IsPerfectClosure

variable [ExpChar K p] [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p] [PerfectRing M p]
  [IsPerfectClosure j p]

/-- If `L` and `M` are both perfect closures of `K`, then there is a ring isomorphism `L ≃+* M`.
This is similar to `IsAlgClosure.equiv` and `IsSepClosure.equiv`. -/
/-
**IsPerfectClosure.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv : L ≃+* M where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_comp_lift_apply_eq_self`：lift_comp_lift_apply_eq_self [
PerfectRing L p] (x : L) : lift j i p (lift i j p x) = x

--- 原说明 ---
If `L` and `M` are both perfect closures of `K`, then there is a ring isomorphis
m `L ≃+* M`.
This is similar to `IsAlgClosure.equiv` and `IsSepClosure.equiv`.
-/
def equiv : L ≃+* M where
  __ := PerfectRing.lift i j p
  invFun := PerfectRing.liftAux j i p
  left_inv := PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := PerfectRing.lift_comp_lift_apply_eq_self j i p
/-
**IsPerfectClosure.equiv_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv_toRingHom : (equiv i j p).toRingHom = PerfectRing.lift i j p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_toRingHom : (equiv i j p).toRingHom = PerfectRing.lift i j p := rfl

@[simp]
/-
**IsPerfectClosure.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv_symm : (equiv i j p).symm = equiv j i p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_symm : (equiv i j p).symm = equiv j i p := rfl
/-
**IsPerfectClosure.equiv_symm_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClos
ure`。
形式化陈述：equiv_symm_toRingHom : (equiv i j p).symm.toRingHom = PerfectRing.lift j i
 p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_symm_toRingHom :
    (equiv i j p).symm.toRingHom = PerfectRing.lift j i p := rfl
/-
**IsPerfectClosure.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) : equiv i j p 
x = (iterateFrobeniusEquiv M p n).symm (j y)
参数：x : L；n : Nat；y : K；h : i y = x ^ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.liftAux_apply`：liftAux_apply (x : L) (n : Nat) (y : K) (h : 
i y = x ^ p ^ n) : liftAux i j p x = (iterateFrobeniusEquiv M p n).symm (j y)
-/
theorem equiv_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    equiv i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  PerfectRing.liftAux_apply i j p _ _ _ h
/-
**IsPerfectClosure.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`
。
形式化陈述：equiv_symm_apply (x : M) (n : Nat) (y : K) (h : j y = x ^ p ^ n) : (equiv 
i j p).symm x = (iterateFrobeniusEquiv L p n).symm (i y)
参数：x : M；n : Nat；y : K；h : j y = x ^ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPerfectClosure.equiv_symm`：equiv_symm : (equiv i j p).symm = equiv j i
 p
· 使用定理 `IsPerfectClosure.equiv_apply`：equiv_apply (x : L) (n : Nat) (y : K) (h :
 i y = x ^ p ^ n) : equiv i j p x = (iterateFrobeniusEquiv M p n).symm (j y)
-/
theorem equiv_symm_apply (x : M) (n : ℕ) (y : K) (h : j y = x ^ p ^ n) :
    (equiv i j p).symm x = (iterateFrobeniusEquiv L p n).symm (i y) := by
  rw [equiv_symm, equiv_apply j i p _ _ _ h]
/-
**IsPerfectClosure.equiv_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`
。
形式化陈述：equiv_self_apply (x : L) : equiv i i p x = x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.liftAux_self_apply`：liftAux_self_apply [ExpChar L p] [Perfec
tRing L p] (x : L) : liftAux i i p x = x
-/
theorem equiv_self_apply (x : L) : equiv i i p x = x :=
  PerfectRing.liftAux_self_apply i p x

@[simp]
/-
**IsPerfectClosure.equiv_self** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv_self : equiv i i p = RingEquiv.refl L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `IsPerfectClosure.equiv_self_apply`：equiv_self_apply (x : L) : equiv i i 
p x = x
-/
theorem equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

@[simp]
/-
**IsPerfectClosure.equiv_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`
。
形式化陈述：equiv_comp_apply (x : K) : equiv i j p (i x) = j x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_comp_apply`：lift_comp_apply (x : K) : lift i j p (i x) 
= j x
-/
theorem equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  PerfectRing.lift_comp_apply i j p x

@[simp]
/-
**IsPerfectClosure.equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`。
形式化陈述：equiv_comp : RingHom.comp (equiv i j p) i = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsPerfectClosure.equiv_comp_apply`：equiv_comp_apply (x : K) : equiv i j 
p (i x) = j x
-/
theorem equiv_comp : RingHom.comp (equiv i j p) i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPerfectClosure k p]

@[simp]
/-
**IsPerfectClosure.equiv_comp_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectCl
osure`。
形式化陈述：equiv_comp_equiv_apply (x : L) : equiv j k p (equiv i j p x) = equiv i k p
 x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectRing.lift_comp_lift_apply`：lift_comp_lift_apply (x : L) : lift j 
k p (lift i j p x) = lift i k p x
-/
theorem equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  PerfectRing.lift_comp_lift_apply i j k p x

@[simp]
/-
**IsPerfectClosure.equiv_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectClosure`
。
形式化陈述：equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `IsPerfectClosure.equiv_comp_equiv_apply`：equiv_comp_equiv_apply (x : L) 
: equiv j k p (equiv i j p x) = equiv i k p x
-/
theorem equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p :=
  RingEquiv.ext (equiv_comp_equiv_apply i j k p)
/-
**IsPerfectClosure.equiv_comp_equiv_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `IsP
erfectClosure`。
形式化陈述：equiv_comp_equiv_apply_eq_self (x : L) : equiv j i p (equiv i j p x) = x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPerfectClosure.equiv_comp_equiv_apply`：equiv_comp_equiv_apply (x : L) 
: equiv j k p (equiv i j p x) = equiv i k p x
· 使用定理 `IsPerfectClosure.equiv_self_apply`：equiv_self_apply (x : L) : equiv i i 
p x = x
-/
theorem equiv_comp_equiv_apply_eq_self (x : L) :
    equiv j i p (equiv i j p x) = x := by
  rw [equiv_comp_equiv_apply, equiv_self_apply]
/-
**IsPerfectClosure.equiv_comp_equiv_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `IsPerfectCl
osure`。
形式化陈述：equiv_comp_equiv_eq_id : (equiv i j p).trans (equiv j i p) = RingEquiv.ref
l L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `IsPerfectClosure.equiv_comp_equiv_apply_eq_self`：equiv_comp_equiv_apply_
eq_self (x : L) : equiv j i p (equiv i j p x) = x
-/
theorem equiv_comp_equiv_eq_id :
    (equiv i j p).trans (equiv j i p) = RingEquiv.refl L :=
  RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

end comp

end IsPerfectClosure

end CommRing

namespace PerfectClosure

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (K)

/-- The absolute perfect closure `PerfectClosure` is a `p`-radical extension over the base ring.
In particular, it is a perfect closure of the base ring, that is,
`IsPerfectClosure (PerfectClosure.of K p) p`. -/
/-
**PerfectClosure.isPRadical** 是 Mathlib 中的一个实例，位于命名空间 `PerfectClosure`。
形式化陈述：isPRadical : IsPRadical (PerfectClosure.of K p) p where pow_mem' x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectClosure.induction_on`：induction_on (x : PerfectClosure K p) {q : 
PerfectClosure K p -> Prop} (h : forall x, q (mk K p x)) : q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iterate_frobenius`：iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n
· 使用定理 `PerfectClosure.iterate_frobenius_mk`：iterate_frobenius_mk (n : Nat) (x :
 K) : (frobenius (PerfectClosure K p) p)^[n] (mk K p ⟨n, x⟩) = of K p x
· 使用定理 `PerfectClosure.mk_eq_iff`：mk_eq_iff (x y : Nat × K) : mk K p x = mk K p 
y ↔ exists z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2
· 使用定理 `PerfectClosure.zero_def`：zero_def : (0 : PerfectClosure K p) = mk K p (0
, 0)
· 使用定理 `PerfectClosure.of_apply`：of_apply (x : K) : of K p x = mk _ _ (0, x)
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_pNilradical`：mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} 
{x : R} : x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
The absolute perfect closure `PerfectClosure` is a `p`-radical extension over th
e base ring.
In particular, it is a perfect closure of the base ring, that is,
`IsPerfectClosure (PerfectClosure.of K p) p`.
-/
instance isPRadical : IsPRadical (PerfectClosure.of K p) p where
  pow_mem' x := PerfectClosure.induction_on x fun x ↦ ⟨x.1, x.2, by
    rw [← iterate_frobenius, iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, of_apply, zero_def, mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

end PerfectClosure

section Field

variable [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar K p]
variable (K L)

/-- If `L / K` is a `p`-radical field extension, then it is purely inseparable. -/
/-
**IsPRadical.isPurelyInseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPRadical.isPurelyInseparable [IsPRadical (algebraMap K L) p] : IsPurelyI
nseparable K L
参数：algebraMap K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPRadical.pow_mem`：IsPRadical.pow_mem [IsPRadical i p] (x : L) : exists
 (n : Nat) (y : K), i y = x ^ p ^ n

--- 原说明 ---
If `L / K` is a `p`-radical field extension, then it is purely inseparable.
-/
theorem IsPRadical.isPurelyInseparable [IsPRadical (algebraMap K L) p] :
    IsPurelyInseparable K L :=
  (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

/-- If `L / K` is a purely inseparable field extension, then it is `p`-radical. In particular, if
`L` is perfect, then the (relative) perfect closure `perfectClosure K L` is a perfect closure
of `K`, that is, `IsPerfectClosure (algebraMap K (perfectClosure K L)) p`. -/
/-
**IsPurelyInseparable.isPRadical** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsPurelyInseparable.isPRadical [IsPurelyInseparable K L] : IsPRadical (alg
ebraMap K L) p where pow_mem'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `L / K` is a purely inseparable field extension, then it is `p`-radical. In p
articular, if
`L` is perfect, then the (relative) perfect closure `perfectClosure K L` is a pe
rfect closure
of `K`, that is, `IsPerfectClosure (algebraMap K (perfectClosure K L)) p`.
-/
instance IsPurelyInseparable.isPRadical [IsPurelyInseparable K L] :
    IsPRadical (algebraMap K L) p where
  pow_mem' := (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

end Field

end IsPerfectClosure

