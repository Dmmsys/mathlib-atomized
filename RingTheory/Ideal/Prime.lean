/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Lattice

/-!

# Prime ideals

This file contains the definition of `Ideal.IsPrime` for prime ideals.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
@[wikidata Q863912]
/-
**Ideal.IsPrime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{α : Type u} → [inst : Semiring α] → Ideal α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P`
-/
class IsPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I ≠ ⊤
  /-- If a product lies in the prime ideal, then at least one element lies in the prime ideal. -/
  mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
/-
**Ideal.isPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_iff {I : Ideal α} : IsPrime I ↔ I != ⊤ ∧ forall {x y : α}, x * y i
n I -> x in I ∨ y in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isPrime_iff {I : Ideal α} : IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
/-
**Ideal.IsPrime.ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → I ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
-/
theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I ≠ ⊤ :=
  hI.1
/-
**Ideal.notMem_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：notMem_of_isUnit (I : Ideal α) [I.IsPrime] {x : α} (hx : IsUnit x) : x ∉ I
参数：I : Ideal α；hx : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
-/
lemma notMem_of_isUnit (I : Ideal α) [I.IsPrime] {x : α} (hx : IsUnit x) : x ∉ I :=
  fun h ↦ ‹I.IsPrime›.ne_top (eq_top_of_isUnit_mem _ h hx)
/-
**Ideal.IsPrime.one_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → 1 ∉ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.notMem_of_isUnit`：notMem_of_isUnit (I : Ideal α) [I.IsPrime] {x : 
α} (hx : IsUnit x) : x ∉ I
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem IsPrime.one_notMem {I : Ideal α} (hI : I.IsPrime) : 1 ∉ I :=
  notMem_of_isUnit _ isUnit_one
/-
**Ideal.one_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
参数：I : Ideal α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.one_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → 1 ∉ I
-/
theorem one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I :=
  hI.one_notMem
/-
**Ideal.IsPrime.mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → ∀ {x y : α},
 x * y ∈ I → x ∈ I ∨ y ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem IsPrime.mem_or_mem {I : Ideal α} (hI : I.IsPrime) {x y : α} : x * y ∈ I → x ∈ I ∨ y ∈ I :=
  hI.2
/-
**Ideal.IsPrime.mul_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → ∀ {x y : α},
 x ∉ I → y ∉ I → x * y ∉ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem IsPrime.mul_notMem {I : Ideal α} (hI : I.IsPrime) {x y : α} :
    x ∉ I → y ∉ I → x * y ∉ I := fun hx hy h ↦
  hy ((hI.mem_or_mem h).resolve_left hx)
/-
**Ideal.IsPrime.mem_or_mem_of_mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPri
me`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → ∀ {x y : α},
 x * y = 0 → x ∈ I ∨ y ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsPrime.mem_or_mem_of_mul_eq_zero {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)
/-
**Ideal.IsPrime.mem_of_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → ∀ {r : α} (n
 : ℕ), r ^ n ∈ I → r ∈ I
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.one_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → 1 ∉ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem IsPrime.mem_of_pow_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (H : r ^ n ∈ I) :
    r ∈ I := by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id
/-
**Ideal.not_isPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：not_isPrime_iff {I : Ideal α} : ¬I.IsPrime ↔ I = ⊤ ∨ exists (x : α) (_hx :
 x ∉ I) (y : α) (_hy : y ∉ I), x * y in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_isPrime_iff {I : Ideal α} :
    ¬I.IsPrime ↔ I = ⊤ ∨ ∃ (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y ∈ I := by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩
/-
**Ideal.isPrime_bot** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：isPrime_bot [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
-/
instance isPrime_bot [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime :=
  ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

@[deprecated isPrime_bot (since := "2026-01-10")]
/-
**Ideal.bot_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：bot_prime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_prime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime := isPrime_bot
/-
**Ideal.IsPrime.mul_mem_iff_mem_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`
。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α} [I.IsTwoSided], I.IsPrime
 → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem IsPrime.mul_mem_iff_mem_or_mem {I : Ideal α} [I.IsTwoSided] (hI : I.IsPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩
/-
**Ideal.IsPrime.pow_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsPrime → ∀ {r : α} (n
 : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
参数：n : ℕ；r ^ n ∈ I ↔ r ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
-/
theorem IsPrime.pow_mem_iff_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (hn : 0 < n) :
    r ^ n ∈ I ↔ r ∈ I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩
/-
**Ideal.IsPrime.mul_mem_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α} [I.IsTwoSided] [I.IsPrime
] {x y : α}, x ∉ I → (x * y ∈ I ↔ y ∈ I)
参数：x * y ∈ I ↔ y ∈ I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsPrime.mul_mem_left_iff {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
    {x y : α} (hx : x ∉ I) : x * y ∈ I ↔ y ∈ I := by
  grind [Ideal.IsPrime.mul_mem_iff_mem_or_mem]
/-
**Ideal.IsPrime.mul_mem_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α} [I.IsTwoSided] [I.IsPrime
] {x y : α}, y ∉ I → (x * y ∈ I ↔ x ∈ I)
参数：x * y ∈ I ↔ x ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.mul_mem_iff_mem_or_mem`：∀ {α : Type u} [inst : Semiring α]
 {I : Ideal α} [I.IsTwoSided], I.IsPrime → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ 
I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsPrime.mul_mem_right_iff {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
    {x y : α} (hx : y ∉ I) : x * y ∈ I ↔ x ∈ I := by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

/-- The complement of a prime ideal `P ⊆ R` is a submonoid of `R`. -/
/-
**Ideal.primeCompl** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：primeCompl (P : Ideal α) [hp : P.IsPrime] : Submonoid α where carrier
参数：P : Ideal α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I

--- 原说明 ---
The complement of a prime ideal `P ⊆ R` is a submonoid of `R`.
-/
def primeCompl (P : Ideal α) [hp : P.IsPrime] : Submonoid α where
  carrier := (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

@[simp]
/-
**Ideal.mem_primeCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_primeCompl_iff {P : Ideal α} [P.IsPrime] {x : α} : x in P.primeCompl ↔
 x ∉ P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_primeCompl_iff {P : Ideal α} [P.IsPrime] {x : α} :
    x ∈ P.primeCompl ↔ x ∉ P := Iff.rfl
/-
**Ideal.primeCompl_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：primeCompl_bot [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).primeComp
l = nonZeroDivisors α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem primeCompl_bot [Nontrivial α] [NoZeroDivisors α] :
    (⊥ : Ideal α).primeCompl = nonZeroDivisors α := by
  ext
  simp

end Ideal

end Semiring

section Ring

/-
**IsDomain.of_bot_isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDomain.of_bot_isPrime (A : Type*) [Ring A] [hbp : (⊥ : Ideal A).IsPrime]
 : IsDomain A
参数：A : Type*；⊥ : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `Ideal.IsPrime.one_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → 1 ∉ I
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem IsDomain.of_bot_isPrime (A : Type*) [Ring A] [hbp : (⊥ : Ideal A).IsPrime] : IsDomain A :=
  @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.2 h⟩

end Ring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/-
**Ideal.eq_bot_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_bot_of_prime [h : I.IsPrime] : I = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Ideal.eq_bot_or_top`：eq_bot_or_top : I = ⊥ ∨ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
-/
theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1

end Ideal

end DivisionSemiring

