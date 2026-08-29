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
/--
Definition of `IsPrime` / `IsPrime` 的定义

English:
class IsPrime
  parameters: (I : Ideal α)
  axioms and operations (2):
    - ne_top' : I != ⊤
    - mem_or_mem' : forall {x y : α}, x * y in I -> x in I ∨ y in I

中文:
类 是素
  参数: (I : 理想 α)
  公理与运算 (2 个):
    - ne_top' : I != ⊤
    - mem_or_mem' : 对任意 {x y : α}, x * y in I -> x in I ∨ y in I
-/
class IsPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I != ⊤
  /-- If a product lies in the prime ideal, then at least one element lies in the prime ideal. -/
  mem_or_mem' : forall {x y : α}, x * y in I -> x in I ∨ y in I

/--
theorem `isPrime_iff` / 定理 `isPrime_iff`

English:
theorem isPrime_iff
  given: {I : Ideal α}
  statement: IsPrime I ↔ I != ⊤ ∧ forall {x y : α}, x * y in I -> x in I ∨ y in I
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isPrime_iff
  条件: {I : 理想 α}
  结论: 是素 I ↔ I != ⊤ ∧ 对任意 {x y : α}, x * y in I -> x in I ∨ y in I
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isPrime_iff {I : Ideal α} : IsPrime I ↔ I != ⊤ ∧ forall {x y : α}, x * y in I -> x in I ∨ y in I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/--
theorem `IsPrime.ne_top` / 定理 `IsPrime.ne_top`

English:
theorem IsPrime.ne_top
  given: {I : Ideal α} (hI : I.IsPrime)
  statement: I != ⊤
  proof: hI.1

中文:
定理 是素.ne_top
  条件: {I : 理想 α} (hI : I.是素)
  结论: I != ⊤
  证明: hI.1
-/
theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I != ⊤ :=
  hI.1

/--
lemma `notMem_of_isUnit` / 引理 `notMem_of_isUnit`

English:
lemma notMem_of_isUnit
  given: (I : Ideal α) [I.IsPrime] {x : α} (hx : IsUnit x)
  statement: x ∉ I
  proof: fun h => ‹I.IsPrime›.ne_top (eq_top_of_isUnit_mem _ h hx)

中文:
引理 notMem_of_isUnit
  条件: (I : 理想 α) [I.是素] {x : α} (hx : 是单位 x)
  结论: x ∉ I
  证明: fun h => ‹I.IsPrime›.ne_top (eq_top_of_isUnit_mem _ h hx)

Depends on / 依赖: I.IsPrime, IsPrime, eq_top_of_isUnit_mem, ne_top
-/
lemma notMem_of_isUnit (I : Ideal α) [I.IsPrime] {x : α} (hx : IsUnit x) : x ∉ I :=
  fun h => ‹I.IsPrime›.ne_top (eq_top_of_isUnit_mem _ h hx)

/--
theorem `IsPrime.one_notMem` / 定理 `IsPrime.one_notMem`

English:
theorem IsPrime.one_notMem
  given: {I : Ideal α} (hI : I.IsPrime)
  statement: 1 ∉ I
  proof: notMem_of_isUnit _ isUnit_one

中文:
定理 是素.one_notMem
  条件: {I : 理想 α} (hI : I.是素)
  结论: 1 ∉ I
  证明: notMem_of_isUnit _ isUnit_one

Depends on / 依赖: isUnit_one, notMem_of_isUnit
-/
theorem IsPrime.one_notMem {I : Ideal α} (hI : I.IsPrime) : 1 ∉ I :=
  notMem_of_isUnit _ isUnit_one

/--
theorem `one_notMem` / 定理 `one_notMem`

English:
theorem one_notMem
  given: (I : Ideal α) [hI : I.IsPrime]
  statement: 1 ∉ I
  proof: hI.one_notMem

中文:
定理 one_notMem
  条件: (I : 理想 α) [hI : I.是素]
  结论: 1 ∉ I
  证明: hI.one_notMem

Depends on / 依赖: hI.one_notMem, one_notMem
-/
theorem one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I :=
  hI.one_notMem

/--
theorem `IsPrime.mem_or_mem` / 定理 `IsPrime.mem_or_mem`

English:
theorem IsPrime.mem_or_mem
  given: {I : Ideal α} (hI : I.IsPrime) {x y : α}
  statement: x * y in I -> x in I ∨ y in I
  proof: hI.2

中文:
定理 是素.mem_or_mem
  条件: {I : 理想 α} (hI : I.是素) {x y : α}
  结论: x * y in I -> x in I ∨ y in I
  证明: hI.2
-/
theorem IsPrime.mem_or_mem {I : Ideal α} (hI : I.IsPrime) {x y : α} : x * y in I -> x in I ∨ y in I :=
  hI.2

/--
theorem `IsPrime.mul_notMem` / 定理 `IsPrime.mul_notMem`

English:
theorem IsPrime.mul_notMem
  given: {I : Ideal α} (hI : I.IsPrime) {x y : α}
  proof: fun hx hy h =>
  hy ((hI.mem_or_mem h).resolve_left hx)

中文:
定理 是素.mul_notMem
  条件: {I : 理想 α} (hI : I.是素) {x y : α}
  证明: fun hx hy h =>
  hy ((hI.mem_or_mem h).resolve_left hx)
-/
theorem IsPrime.mul_notMem {I : Ideal α} (hI : I.IsPrime) {x y : α} :
    x ∉ I -> y ∉ I -> x * y ∉ I := fun hx hy h =>
  hy ((hI.mem_or_mem h).resolve_left hx)

/--
theorem `IsPrime.mem_or_mem_of_mul_eq_zero` / 定理 `IsPrime.mem_or_mem_of_mul_eq_zero`

English:
theorem IsPrime.mem_or_mem_of_mul_eq_zero
  given: {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0)
  proof: hI.mem_or_mem (h.symm ▸ I.zero_mem)

中文:
定理 是素.mem_or_mem_of_mul_eq_zero
  条件: {I : 理想 α} (hI : I.是素) {x y : α} (h : x * y = 0)
  证明: hI.mem_or_mem (h.symm ▸ I.zero_mem)

Depends on / 依赖: I.zero_mem, h.symm, hI.mem_or_mem, mem_or_mem, zero_mem
-/
theorem IsPrime.mem_or_mem_of_mul_eq_zero {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x in I ∨ y in I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)

/--
theorem `IsPrime.mem_of_pow_mem` / 定理 `IsPrime.mem_of_pow_mem`

English:
theorem IsPrime.mem_of_pow_mem
  given: {I : Ideal α} (hI : I.IsPrime) {r : α} (n : Nat) (H : r ^ n in I)
  proof: by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

中文:
定理 是素.mem_of_pow_mem
  条件: {I : 理想 α} (hI : I.是素) {r : α} (n : 自然数) (H : r ^ n in I)
  证明: by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

Depends on / 依赖: Or.casesOn, casesOn, hI.mem_or_mem, hI.one_notMem.elim, mem_or_mem, one_notMem, pow_succ, pow_zero
-/
theorem IsPrime.mem_of_pow_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : Nat) (H : r ^ n in I) :
    r in I := by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact hI.one_notMem.elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

/--
theorem `not_isPrime_iff` / 定理 `not_isPrime_iff`

English:
theorem not_isPrime_iff
  given: {I : Ideal α}
  proof: by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

中文:
定理 not_isPrime_iff
  条件: {I : 理想 α}
  证明: by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

Depends on / 依赖: Classical, Classical.not_not, Ideal.isPrime_iff, Iff.rfl, isPrime_iff, not_and_or, not_forall, not_not, not_or, or_congr, simp_rw
-/
theorem not_isPrime_iff {I : Ideal α} :
    ¬I.IsPrime ↔ I = ⊤ ∨ exists (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y in I := by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

/--
Instance `isPrime_bot` / 实例 `isPrime_bot`

English:
instance isPrime_bot
  signature: [Nontrivial α] [NoZeroDivisors α]
  body: ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

@[deprecated isPrime_bot (since := "2026-01-10")]

中文:
实例 isPrime_bot
  签名: [非平凡 α] [无零因子 α]
  定义体: ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

@[deprecated isPrime_bot (since := "2026-01-10")]

Depends on / 依赖: Ideal.eq_top_iff_one, Submodule, Submodule.mem_bot, eq_top_iff_one, mem_bot, mul_eq_zero, mul_eq_zero.mp, one_ne_zero
-/
instance isPrime_bot [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime :=
  ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

@[deprecated isPrime_bot (since := "2026-01-10")]
/--
theorem `bot_prime` / 定理 `bot_prime`

English:
theorem bot_prime
  given: [Nontrivial α] [NoZeroDivisors α]
  statement: (⊥ : Ideal α).IsPrime
  proof: isPrime_bot

中文:
定理 bot_prime
  条件: [非平凡 α] [无零因子 α]
  结论: (⊥ : 理想 α).是素
  证明: isPrime_bot

Depends on / 依赖: isPrime_bot
-/
theorem bot_prime [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime := isPrime_bot

/--
theorem `IsPrime.mul_mem_iff_mem_or_mem` / 定理 `IsPrime.mul_mem_iff_mem_or_mem`

English:
theorem IsPrime.mul_mem_iff_mem_or_mem
  given: {I : Ideal α} [I.IsTwoSided] (hI : I.IsPrime)
  proof: @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

中文:
定理 是素.mul_mem_iff_mem_or_mem
  条件: {I : 理想 α} [I.是TwoSided] (hI : I.是素)
  证明: @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩
-/
theorem IsPrime.mul_mem_iff_mem_or_mem {I : Ideal α} [I.IsTwoSided] (hI : I.IsPrime) :
    forall {x y : α}, x * y in I ↔ x in I ∨ y in I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

/--
theorem `IsPrime.pow_mem_iff_mem` / 定理 `IsPrime.pow_mem_iff_mem`

English:
theorem IsPrime.pow_mem_iff_mem
  given: {I : Ideal α} (hI : I.IsPrime) {r : α} (n : Nat) (hn : 0 < n)
  proof: ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

中文:
定理 是素.pow_mem_iff_mem
  条件: {I : 理想 α} (hI : I.是素) {r : α} (n : 自然数) (hn : 0 < n)
  证明: ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

Depends on / 依赖: I.pow_mem_of_mem, hI.mem_of_pow_mem, mem_of_pow_mem, pow_mem_of_mem
-/
theorem IsPrime.pow_mem_iff_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : Nat) (hn : 0 < n) :
    r ^ n in I ↔ r in I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

/--
lemma `IsPrime.mul_mem_left_iff` / 引理 `IsPrime.mul_mem_left_iff`

English:
lemma IsPrime.mul_mem_left_iff
  statement: {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
  proof: by
  grind [Ideal.IsPrime.mul_mem_iff_mem_or_mem]

中文:
引理 是素.mul_mem_left_iff
  结论: {I : 理想 α} [I.是TwoSided] [I.是素]
  证明: by
  grind [Ideal.IsPrime.mul_mem_iff_mem_or_mem]

Depends on / 依赖: Ideal.IsPrime.mul_mem_iff_mem_or_mem, IsPrime, mul_mem_iff_mem_or_mem
-/
lemma IsPrime.mul_mem_left_iff {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
    {x y : α} (hx : x ∉ I) : x * y in I ↔ y in I := by
  grind [Ideal.IsPrime.mul_mem_iff_mem_or_mem]

/--
lemma `IsPrime.mul_mem_right_iff` / 引理 `IsPrime.mul_mem_right_iff`

English:
lemma IsPrime.mul_mem_right_iff
  statement: {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
  proof: by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

中文:
引理 是素.mul_mem_right_iff
  结论: {I : 理想 α} [I.是TwoSided] [I.是素]
  证明: by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

Depends on / 依赖: Ideal.IsPrime.mul_mem_iff_mem_or_mem, IsPrime, mul_mem_iff_mem_or_mem
-/
lemma IsPrime.mul_mem_right_iff {I : Ideal α} [I.IsTwoSided] [I.IsPrime]
    {x y : α} (hx : y ∉ I) : x * y in I ↔ x in I := by
  rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem] <;> aesop

/--
Definition of `primeCompl` / `primeCompl` 的定义

English:
definition primeCompl
  signature: (P : Ideal α) [hp : P.IsPrime]
  body: (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

@[simp]

中文:
定义 primeCompl
  签名: (P : 理想 α) [hp : P.是素]
  定义体: (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

@[simp]
-/
def primeCompl (P : Ideal α) [hp : P.IsPrime] : Submonoid α where
  carrier := (Pᶜ : Set α)
  one_mem' := P.one_notMem
  mul_mem' {_ _} hnx hny hxy := Or.casesOn (hp.mem_or_mem hxy) hnx hny

@[simp]
/--
theorem `mem_primeCompl_iff` / 定理 `mem_primeCompl_iff`

English:
theorem mem_primeCompl_iff
  given: {P : Ideal α} [P.IsPrime] {x : α}
  proof: Iff.rfl

中文:
定理 mem_primeCompl_iff
  条件: {P : 理想 α} [P.是素] {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_primeCompl_iff {P : Ideal α} [P.IsPrime] {x : α} :
    x in P.primeCompl ↔ x ∉ P := Iff.rfl

/--
theorem `primeCompl_bot` / 定理 `primeCompl_bot`

English:
theorem primeCompl_bot
  given: [Nontrivial α] [NoZeroDivisors α]
  proof: by
  ext
  simp

中文:
定理 primeCompl_bot
  条件: [非平凡 α] [无零因子 α]
  证明: by
  ext
  simp
-/
theorem primeCompl_bot [Nontrivial α] [NoZeroDivisors α] :
    (⊥ : Ideal α).primeCompl = nonZeroDivisors α := by
  ext
  simp

end Ideal

end Semiring

section Ring

/--
theorem `IsDomain.of_bot_isPrime` / 定理 `IsDomain.of_bot_isPrime`

English:
theorem IsDomain.of_bot_isPrime
  given: (A : Type*) [Ring A] [hbp : (⊥ : Ideal A).IsPrime]
  statement: IsDomain A
  proof: @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.2 h⟩

中文:
定理 是整环.of_bot_isPrime
  条件: (A : 类型) [环 A] [hbp : (⊥ : 理想 A).是素]
  结论: 是整环 A
  证明: @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.2 h⟩

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, hbp.one_notMem, one_notMem, to_isDomain
-/
theorem IsDomain.of_bot_isPrime (A : Type*) [Ring A] [hbp : (⊥ : Ideal A).IsPrime] : IsDomain A :=
  @NoZeroDivisors.to_isDomain A _ ⟨1, 0, fun h => hbp.one_notMem h⟩ ⟨fun h => hbp.2 h⟩

end Ring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/--
theorem `eq_bot_of_prime` / 定理 `eq_bot_of_prime`

English:
theorem eq_bot_of_prime
  given: [h : I.IsPrime]
  statement: I = ⊥
  proof: or_iff_not_imp_right.mp I.eq_bot_or_top h.1

中文:
定理 eq_bot_of_prime
  条件: [h : I.是素]
  结论: I = ⊥
  证明: or_iff_not_imp_right.mp I.eq_bot_or_top h.1

Depends on / 依赖: I.eq_bot_or_top, eq_bot_or_top, or_iff_not_imp_right, or_iff_not_imp_right.mp
-/
theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1

end Ideal

end DivisionSemiring
