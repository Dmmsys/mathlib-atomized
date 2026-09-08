/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Order.Lattice

/-!
# Characteristic of semirings

## Main definitions
* `CharP R p` expresses that the ring (additive monoid with one) `R` has characteristic `p`
* `ringChar`: the characteristic of a ring
* `ExpChar R p` expresses that the ring (additive monoid with one) `R` has
  exponential characteristic `p` (which is `1` if `R` has characteristic 0, and `p` if it has
  prime characteristic `p`)
-/

@[expose] public section

assert_not_exists Field Finset OrderHom

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
/-
**CharP._root_.CharP** 是 Mathlib 中的一个类，位于命名空间 `CharP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorb
ing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
class _root_.CharP (R : Type*) [AddMonoidWithOne R] (p : outParam ℕ) : Prop where
  cast_eq_zero_iff (R p) : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x

variable [CharP R p] {a b : ℕ}
/-
**CharP._root_.CharP.ofNat_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CharP.ofNat_eq_zero' (p : ℕ) [CharP R p]
    (a : ℕ) [a.AtLeastTwo] (h : p ∣ a) :
    (ofNat(a) : R) = 0 := by
  rwa [← CharP.cast_eq_zero_iff R p] at h

variable {R} in
/-
**CharP.congr** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：congr {q : Nat} (h : p = q) : CharP R q
参数：h : p = q。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr {q : ℕ} (h : p = q) : CharP R q := h ▸ ‹CharP R p›
/-
**CharP.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ) [CharP R p], ↑p = 0
参数：R : Type u_1；p : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
@[simp] lemma cast_eq_zero : (p : R) = 0 := (cast_eq_zero_iff R p p).2 dvd_rfl
/-
**CharP.cast_eq_mod** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：cast_eq_mod (k : Nat) : (k : R) = (k % p : Nat)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cast_eq_mod (k : ℕ) : (k : R) = (k % p : ℕ) :=
  have (a : ℕ) : ((p * a : ℕ) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R p]
    exact Nat.dvd_mul_right p a
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [this]
/-
**CharP.cast_eq_iff_mod_eq** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：cast_eq_iff_mod_eq [IsLeftCancelAdd R] : (a : R) = (b : R) ↔ a % p = b % p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.sub_mod_eq_zero_of_mod_eq`：∀ {m k n : ℕ}, m % k = n % k → (m - n) % 
k = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma cast_eq_iff_mod_eq [IsLeftCancelAdd R] : (a : R) = (b : R) ↔ a % p = b % p := by
  wlog! hle : a ≤ b
  · simpa only [eq_comm] using (this _ _ hle.le)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.cast_add, left_eq_add, CharP.cast_eq_zero_iff R p]
  constructor
  · simp +contextual [Nat.add_mod, Nat.dvd_iff_mod_eq_zero]
  intro h
  have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  simpa [Nat.dvd_iff_mod_eq_zero] using this

-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]
/-
**CharP.ofNat_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
-/
lemma ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0 := cast_eq_zero R p
/-
**CharP.eq** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
参数：hp : CharP R p；hq : CharP R q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
-/
lemma eq {p q : ℕ} (hp : CharP R p) (hq : CharP R q) : p = q :=
  Nat.dvd_antisymm ((cast_eq_zero_iff (self := hp) R p q).1 (@cast_eq_zero _ _ _ hq))
    ((cast_eq_zero_iff (self := hq) R q p).1 (@cast_eq_zero _ _ _ hp))
/-
**CharP.ofCharZero** 是 Mathlib 中的一个实例，位于命名空间 `CharP`。
形式化陈述：ofCharZero [CharZero R] : CharP R 0 where cast_eq_zero_iff x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance ofCharZero [CharZero R] : CharP R 0 where
  cast_eq_zero_iff x := by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

/-
**CharP.intCast_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔ (p : Int) ∣ a
参数：a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.dvd_neg`：∀ {a b : ℤ}, a ∣ -b ↔ a ∣ b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.neg_nonneg`：∀ {a : ℤ}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to ℕ using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
  · simp
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
/-
**CharP.charP_to_charZero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：charP_to_charZero [CharP R 0] : CharZero R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_inj_zero`：charZero_of_inj_zero [AddGroupWithOne R] (H : fora
ll n : Nat, (n : R) = 0 -> n = 0) : CharZero R
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
lemma charP_to_charZero [CharP R 0] : CharZero R :=
  charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)
/-
**CharP.charP_zero_iff_charZero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：charP_zero_iff_charZero : CharP R 0 ↔ CharZero R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
-/
lemma charP_zero_iff_charZero : CharP R 0 ↔ CharZero R :=
  ⟨fun _ ↦ charP_to_charZero R, fun _ ↦ ofCharZero R⟩

end AddGroupWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

/-
**CharP.** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» : ∃ p, CharP R p :=
  letI := Classical.decEq R
  by_cases
    (fun H : ∀ p : ℕ, (p : R) = 0 → p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_contradiction fun H2 =>
              Nat.find_min (not_forall.1 H)
                (Nat.mod_lt x <|
                  Nat.pos_of_ne_zero <| not_of_not_imp <| Nat.find_spec (not_forall.1 H))
                (not_imp_of_and_not
                  ⟨by
                    rwa [← Nat.mod_add_div x (Nat.find (not_forall.1 H)), Nat.cast_add,
                      Nat.cast_mul,
                      of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
                      zero_mul, add_zero] at H1,
                    H2⟩)),
          fun H1 => by
          rw [← Nat.mul_div_cancel' H1, Nat.cast_mul,
            of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
            zero_mul]⟩⟩⟩
/-
**CharP.existsUnique** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：existsUnique : exists! p, CharP R p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
-/
lemma existsUnique : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

end NonAssocSemiring
end CharP

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
/-
**ringChar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ringChar [NonAssocSemiring R] : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.existsUnique`：existsUnique : exists! p, CharP R p

--- 原说明 ---
Noncomputable function that outputs the unique characteristic of a semiring.
-/
noncomputable def ringChar [NonAssocSemiring R] : ℕ := Classical.choose (CharP.existsUnique R)

namespace ringChar
variable [NonAssocSemiring R]

/-
**ringChar.spec** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CharP.existsUnique`：existsUnique : exists! p, CharP R p
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
lemma spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  let : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)
/-
**ringChar.eq** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：eq (p : Nat) [C : CharP R p] : ringChar R = p
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CharP.existsUnique`：existsUnique : exists! p, CharP R p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm
/-
**ringChar.** 是 Mathlib 中的一个实例，位于命名空间 `ringChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) charP : CharP R (ringChar R) :=
  ⟨spec R⟩

variable {R}
/-
**ringChar.of_eq** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：of_eq {p : Nat} (h : ringChar R = p) : CharP R p
参数：h : ringChar R = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.congr`：congr {q : Nat} (h : p = q) : CharP R q
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
-/
lemma of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h
/-
**ringChar.eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：eq_iff {p : Nat} : ringChar R = p ↔ CharP R p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringChar.of_eq`：of_eq {p : Nat} (h : ringChar R = p) : CharP R p
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
-/
lemma eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ p⟩
/-
**ringChar.dvd** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：dvd {x : Nat} (hx : (x : R) = 0) : ringChar R ∣ x
参数：hx : (x : R) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
-/
lemma dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (spec R x).1 hx

@[simp]
/-
**ringChar.eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：eq_zero [CharZero R] : ringChar R = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
-/
lemma eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0
/-
**ringChar.Nat.cast_ringChar** 是 Mathlib 中的一个定理，位于命名空间 `ringChar.Nat`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocSemiring R], ↑(ringChar R) = 0
参数：ringChar R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
lemma Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [ringChar.spec]

@[simp]
/-
**ringChar.ringChar_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `subsingleton_iff_zero_eq_one`：subsingleton_iff_zero_eq_one : (0 : M₀) = 
1 ↔ Subsingleton M₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  rw [← Nat.dvd_one, ← spec, eq_comm, Nat.cast_one, subsingleton_iff_zero_eq_one]

@[nontriviality]
/-
**ringChar.ringChar_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `ringChar`。
形式化陈述：ringChar_subsingleton [Subsingleton R] : ringChar R = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringChar_subsingleton [Subsingleton R] : ringChar R = 1 := by simpa

end ringChar

/-
**CharP.neg_one_ne_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CharP.neg_one_ne_one [AddGroupWithOne R] (p : Nat) [CharP R p] [Fact (2 < 
p)] : (-1 : R) != (1 : R)
参数：p : Nat；2 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.zero_lt_two`：0 < 2
-/
lemma CharP.neg_one_ne_one [AddGroupWithOne R] (p : ℕ) [CharP R p] [Fact (2 < p)] :
    (-1 : R) ≠ (1 : R) := by
  rw [ne_comm, ← sub_ne_zero, sub_neg_eq_add, one_add_one_eq_two, ← Nat.cast_two, Ne,
    CharP.cast_eq_zero_iff R p 2]
  exact fun h ↦ (Fact.out : 2 < p).not_ge <| Nat.le_of_dvd Nat.zero_lt_two h

namespace CharP

section

variable [NonAssocRing R]

/-
**CharP.ringChar_zero_iff_CharZero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringChar.eq_iff`：eq_iff {p : Nat} : ringChar R = p ↔ CharP R p
· 使用引理 `CharP.charP_zero_iff_charZero`：charP_zero_iff_charZero : CharP R 0 ↔ Cha
rZero R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff, charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

/-
**CharP.char_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p] : p != 1
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

/-
**CharP.char_is_prime_of_two_le** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：char_is_prime_of_two_le (p : Nat) [CharP R p] (hp : 2 <= p) : Nat.Prime p
参数：p : Nat；hp : 2 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Dvd.dvd.antisymm'`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCan
celMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → b = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dvd.dvd.antisymm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCanc
elMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → a = b
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.prime_def`：prime_def {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, m ∣ p 
-> m = 1 ∨ m = p
-/
lemma char_is_prime_of_two_le (p : ℕ) [CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
  suffices ∀ (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : ℕ) (hdvd : ∃ e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (this.antisymm' ⟨e, hmul⟩))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := ‹e ∣ p›.antisymm ‹p ∣ e›
    have h₀ : 0 < p := by grind
    have : d * p = 1 * p := by grind
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)

section Nontrivial

variable [Nontrivial R]

/-
**CharP.char_is_prime_or_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：char_is_prime_or_zero (p : Nat) [hc : CharP R p] : Nat.Prime p ∨ p = 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.char_ne_one`：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p]
 : p != 1
· 使用引理 `CharP.char_is_prime_of_two_le`：char_is_prime_of_two_le (p : Nat) [CharP 
R p] (hp : 2 <= p) : Nat.Prime p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
lemma char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

/-- The characteristic is prime if it is non-zero. -/
/-
**CharP.char_prime_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：char_prime_of_ne_zero {p : Nat} [CharP R p] (hp : p != 0) : p.Prime
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0

--- 原说明 ---
The characteristic is prime if it is non-zero.
-/
lemma char_prime_of_ne_zero {p : ℕ} [CharP R p] (hp : p ≠ 0) : p.Prime :=
  (CharP.char_is_prime_or_zero R p).resolve_right hp
/-
**CharP.exists'** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] : C
harZero R ∨ exists p : Nat, Fact p.Prime ∧ CharP R p
参数：R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]
/-
**CharP.char_is_prime_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：char_is_prime_of_pos (p : Nat) [NeZero p] [CharP R p] : Fact p.Prime
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime :=
  ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩

end Nontrivial

end NoZeroDivisors

end Semiring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- This lemma is not an instance, to make sure that trying to prove `α` is a subsingleton does
-- not try to find a ring structure on `α`, which can be expensive.
/-
**CharP.CharOne.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `CharP.CharOne`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocSemiring R] [CharP R 1], Subsingleton R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma CharOne.subsingleton [CharP R 1] : Subsingleton R :=
  Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : ℕ) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]
/-
**CharP.false_of_nontrivial_of_char_one** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.CharOne.subsingleton`：∀ {R : Type u_1} [inst : NonAssocSemiring R]
 [CharP R 1], Subsingleton R
· 使用定理 `false_of_nontrivial_of_subsingleton`：false_of_nontrivial_of_subsingleton
 (α : Type*) [Nontrivial α] [Subsingleton α] : False
-/
lemma false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R
/-
**CharP.ringChar_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：ringChar_ne_one [Nontrivial R] : ringChar R != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
-/
lemma ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  simpa using not_subsingleton R
/-
**CharP.nontrivial_of_char_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：nontrivial_of_char_ne_one {v : Nat} (hv : v != 1) [hr : CharP R v] : Nontr
ivial R
参数：hv : v != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

end NonAssocSemiring
end CharP

namespace NeZero

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

/-
**NeZero.of_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R)
参数：h : ¬p ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
lemma of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩
/-
**NeZero.not_char_dvd** 是 Mathlib 中的一个引理，位于命名空间 `NeZero`。
形式化陈述：not_char_dvd (p : Nat) [CharP R p] (k : Nat) [h : NeZero (k : R)] : ¬p ∣ k
参数：p : Nat；k : Nat；k : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0
-/
lemma not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

end NeZero

/-!
### Exponential characteristic

This section defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).
-/

section AddMonoidWithOne
variable [AddMonoidWithOne R]

/-- The definition of the exponential characteristic of a semiring. -/
/-
**inductive** 是 Mathlib 中的一个类，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of the exponential characteristic of a semiring.
-/
class inductive ExpChar : ℕ → Prop
  | zero [CharZero R] : ExpChar 1
  | prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar q
/-
**expChar_prime** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：expChar_prime (p) [CharP R p] [Fact p.Prime] : ExpChar R p
参数：p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
instance expChar_prime (p) [CharP R p] [Fact p.Prime] : ExpChar R p := ExpChar.prime Fact.out
/-
**expChar_one** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：expChar_one [CharZero R] : ExpChar R 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance expChar_one [CharZero R] : ExpChar R 1 := ExpChar.zero
/-
**expChar_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
-/
lemma expChar_ne_zero (p : ℕ) [hR : ExpChar R p] : p ≠ 0 := by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

variable {R} in
/-- The exponential characteristic is unique. -/
/-
**ExpChar.eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ExpChar.eq {p q : Nat} (hp : ExpChar R p) (hq : ExpChar R q) : p = q
参数：hp : ExpChar R p；hq : ExpChar R q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q

--- 原说明 ---
The exponential characteristic is unique.
-/
lemma ExpChar.eq {p q : ℕ} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]
/-
**ExpChar.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ExpChar.congr {p : Nat} (q : Nat) [hq : ExpChar R q] (h : q = p) : ExpChar
 R p
参数：q : Nat；h : q = p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ExpChar.congr {p : ℕ} (q : ℕ) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

/-- The exponential characteristic is one if the characteristic is zero. -/
/-
**expChar_one_of_char_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_one_of_char_zero (q : Nat) [hp : CharP R 0] [hq : ExpChar R q] : q
 = 1
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q

--- 原说明 ---
The exponential characteristic is one if the characteristic is zero.
-/
lemma expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  rcases hq with q | hq_prime
  · rfl
  · exact False.elim <| hq_prime.ne_zero <| ‹CharP R q›.eq R hp

/-- The characteristic equals the exponential characteristic iff the former is prime. -/
/-
**char_eq_expChar_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：char_eq_expChar_iff (p q : Nat) [hp : CharP R p] [hq : ExpChar R q] : p = 
q ↔ p.Prime
参数：p q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The characteristic equals the exponential characteristic iff the former is prime
.
-/
lemma char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  rcases hq with q | hq_prime
  · rw [(CharP.eq R hp (.ofCharZero R) : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp ‹CharP R q›⟩

/-- The exponential characteristic is a prime number or one.
See also `CharP.char_is_prime_or_zero`. -/
/-
**expChar_is_prime_or_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_is_prime_or_one (q : Nat) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The exponential characteristic is a prime number or one.
See also `CharP.char_is_prime_or_zero`.
-/
lemma expChar_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by
  cases hq with
  | zero => exact .inr rfl
  | prime hp => exact .inl hp

/-- The exponential characteristic is positive. -/
/-
**expChar_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_pos (q : Nat) [ExpChar R q] : 0 < q
参数：q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_is_prime_or_one`：expChar_is_prime_or_one (q : Nat) [hq : ExpChar
 R q] : Nat.Prime q ∨ q = 1
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The exponential characteristic is positive.
-/
lemma expChar_pos (q : ℕ) [ExpChar R q] : 0 < q := by
  rcases expChar_is_prime_or_one R q with h | rfl
  exacts [Nat.Prime.pos h, Nat.one_pos]

/-- Any power of the exponential characteristic is positive. -/
/-
**expChar_pow_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 < q ^ n
参数：q : Nat；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用引理 `expChar_pos`：expChar_pos (q : Nat) [ExpChar R q] : 0 < q

--- 原说明 ---
Any power of the exponential characteristic is positive.
-/
lemma expChar_pow_pos (q : ℕ) [ExpChar R q] (n : ℕ) : 0 < q ^ n :=
  Nat.pow_pos (expChar_pos R q)

end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

/-- Noncomputable function that outputs the unique exponential characteristic of a semiring. -/
/-
**ringExpChar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ringExpChar : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputable function that outputs the unique exponential characteristic of a s
emiring.
-/
noncomputable def ringExpChar : ℕ := max (ringChar R) 1
/-
**ringExpChar.eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar R = q
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringExpChar.eq_1`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ringExpC
har R = max (ringChar R) 1
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.max_eq_left`：∀ {a b : ℕ}, b ≤ a → max a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
lemma ringExpChar.eq (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  rcases h with _ | h
  · have := CharP.ofCharZero R
    rw [ringExpChar, ringChar.eq R 0]; rfl
  rw [ringExpChar, ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le
/-
**ringExpChar.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ringExpChar`。
形式化陈述：∀ (R : Type u_1) [inst : NonAssocSemiring R] [CharZero R], ringExpChar R =
 1
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringExpChar.eq_1`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ringExpC
har R = max (ringChar R) 1
· 使用引理 `ringChar.eq_zero`：eq_zero [CharZero R] : ringChar R = 0
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
@[simp] lemma ringExpChar.eq_one [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar, ringChar.eq_zero, max_eq_right (Nat.zero_le _)]

section Nontrivial
variable [Nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
/-
**char_zero_of_expChar_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：char_zero_of_expChar_one (p : Nat) [hp : CharP R p] [hq : ExpChar R 1] : p
 = 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
· 使用引理 `CharP.char_ne_one`：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p]
 : p != 1

--- 原说明 ---
The exponential characteristic is one if the characteristic is zero.
-/
lemma char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (CharP.char_ne_one R 1 rfl)

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/-- The characteristic is zero if the exponential characteristic is one. -/
/-
**charZero_of_expChar_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.char_ne_one`：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p]
 : p != 1

--- 原说明 ---
The characteristic is zero if the exponential characteristic is one.
-/
lemma charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)

/-- The exponential characteristic is one iff the characteristic is zero. -/
/-
**expChar_one_iff_char_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_one_iff_char_zero (p q : Nat) [CharP R p] [ExpChar R q] : q = 1 ↔ 
p = 0
参数：p q : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `char_zero_of_expChar_one`：char_zero_of_expChar_one (p : Nat) [hp : CharP
 R p] [hq : ExpChar R 1] : p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `expChar_one_of_char_zero`：expChar_one_of_char_zero (q : Nat) [hp : CharP
 R 0] [hq : ExpChar R q] : q = 1

--- 原说明 ---
The exponential characteristic is one iff the characteristic is zero.
-/
lemma expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

end Nontrivial
end NonAssocSemiring

/-
**ExpChar.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar R q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.exists'`：exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [
Nontrivial R] : CharZero R ∨ exists p : Nat, Fact p.Prime ∧ CharP R p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma ExpChar.exists [Ring R] [IsDomain R] : ∃ q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]
/-
**ExpChar.exists_unique** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ExpChar.exists_unique [Ring R] [IsDomain R] : exists! q, ExpChar R q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用引理 `ExpChar.eq`：ExpChar.eq {p q : Nat} (hp : ExpChar R p) (hq : ExpChar R q)
 : p = q
-/
lemma ExpChar.exists_unique [Ring R] [IsDomain R] : ∃! q, ExpChar R q :=
  let ⟨q, H⟩ := ExpChar.exists R
  ⟨q, H, fun _ H2 ↦ ExpChar.eq H2 H⟩
/-
**ringExpChar.expChar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
-/
instance ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R) := by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

variable {R} in
/-
**ringExpChar.of_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringExpChar.of_eq [Ring R] [IsDomain R] {q : Nat} (h : ringExpChar R = q) 
: ExpChar R q
参数：h : ringExpChar R = q。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringExpChar.of_eq [Ring R] [IsDomain R] {q : ℕ} (h : ringExpChar R = q) : ExpChar R q :=
  h ▸ ringExpChar.expChar R

variable {R} in
/-
**ringExpChar.eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringExpChar.eq_iff [Ring R] [IsDomain R] {q : Nat} : ringExpChar R = q ↔ E
xpChar R q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringExpChar.of_eq`：ringExpChar.of_eq [Ring R] [IsDomain R] {q : Nat} (h 
: ringExpChar R = q) : ExpChar R q
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
-/
lemma ringExpChar.eq_iff [Ring R] [IsDomain R] {q : ℕ} : ringExpChar R = q ↔ ExpChar R q :=
  ⟨ringExpChar.of_eq, fun _ ↦ ringExpChar.eq R q⟩
