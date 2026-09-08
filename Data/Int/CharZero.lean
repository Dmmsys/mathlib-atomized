/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Int.Cast.Field
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Cast.Pi

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/

public section

open Nat Set

variable {α β : Type*}

namespace Int

@[simp, norm_cast]
/-
**Int.cast_div_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_div_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : Int} (n
_dvd : n ∣ m) : ((m / n : Int) : k) = m / n
参数：n_dvd : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_div`：cast_div [DivisionRing α] {m n : Int} (n_dvd : n ∣ m) (hn 
: (n : α) != 0) : ((m / n : Int) : α) = m / n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
-/
theorem cast_div_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) :
    ((m / n : ℤ) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)

-- Necessary for confluence with `ofNat_ediv` and `cast_div_charZero`.
@[simp, norm_cast]
/-
**Int.cast_div_ofNat_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_div_ofNat_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : N
at} (n_dvd : n ∣ m) : (((m : Int) / (n : Int) : Int) : k) = m / n
参数：n_dvd : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_div_charZero`：cast_div_charZero {k : Type*} [DivisionRing k] [C
harZero k] {m n : Int} (n_dvd : n ∣ m) : ((m / n : Int) : k) = m / n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem cast_div_ofNat_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℕ}
    (n_dvd : n ∣ m) : (((m : ℤ) / (n : ℤ) : ℤ) : k) = m / n := by
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd), cast_natCast, cast_natCast]

end Int

/-
**RingHom.injective_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.injective_int {α : Type*} [NonAssocRing α] (f : Int ->+* α) [CharZ
ero α] : Function.Injective f
参数：f : Int ->+* α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `RingHom.Int.subsingleton_ringHom`：∀ {R : Type u_5} [inst : NonAssocSemir
ing R], Subsingleton (ℤ →+* R)
-/
theorem RingHom.injective_int {α : Type*} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective

namespace Function
variable [AddGroupWithOne β] [CharZero β] {n : ℤ}

/-
**Function.support_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_intCast (hn : n != 0) : support (n : α -> β) = univ
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
-/
lemma support_intCast (hn : n ≠ 0) : support (n : α → β) = univ :=
  support_const <| Int.cast_ne_zero.2 hn
/-
**Function.mulSupport_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_intCast (hn : n != 1) : mulSupport (n : α -> β) = univ
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_const`：mulSupport_const {c : M} (hc : c != 1) : (mul
Support fun _ : ι => c) = Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_one`：cast_ne_one : (n : α) != 1 ↔ n != 1
-/
lemma mulSupport_intCast (hn : n ≠ 1) : mulSupport (n : α → β) = univ :=
  mulSupport_const <| Int.cast_ne_one.2 hn

end Function

