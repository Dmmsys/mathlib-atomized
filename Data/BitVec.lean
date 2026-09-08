/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

@[expose] public section

namespace BitVec

variable {w : Nat}

-- TODO: move to the Lean4 repository.
open Fin.CommRing in
/-
**BitVec.ofFin_intCast** 是 Mathlib 中的一个定理，位于命名空间 `BitVec`。
形式化陈述：ofFin_intCast (z : Int) : ofFin (z : Fin (2 ^ w)) = ↑z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BitVec.eq_nil`：∀ (x : BitVec 0), x = BitVec.nil
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BitVec.eq_of_toInt_eq`：∀ {n : ℕ} {x y : BitVec n}, x.toInt = y.toInt → x
 = y
· 使用定理 `BitVec.toInt_ofFin`：∀ {w : ℕ} (x : Fin (2 ^ w)), { toFin := x }.toInt = 
(↑↑x).bmod (2 ^ w)
· 使用定理 `Fin.val_intCast`：∀ {n : ℕ} [inst : NeZero n] (x : ℤ), ↑↑x = (x % ↑n).toN
at
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `BitVec.toInt_intCast`：∀ {w : ℕ} (x : ℤ), (↑x).toInt = x.bmod (2 ^ w)
· 使用定理 `Int.max_eq_left`：∀ {a b : ℤ}, b ≤ a → max a b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.emod_bmod`：∀ (x : ℤ) (n : ℕ), (x % ↑n).bmod n = x.bmod n
-/
theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2 ^ w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin, Fin.val_intCast, Int.natCast_pow, Nat.cast_ofNat, Int.ofNat_toNat,
      toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h, Int.emod_bmod]
    · omega

open Fin.CommRing in
/-
**BitVec.toFin_intCast** 是 Mathlib 中的一个定理，位于命名空间 `BitVec`。
形式化陈述：∀ {w : ℕ} (z : ℤ), (↑z).toFin = ↑z
参数：z : ℤ；↑z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BitVec.ofFin_intCast`：ofFin_intCast (z : Int) : ofFin (z : Fin (2 ^ w)) 
= ↑z
-/
@[simp] theorem toFin_intCast (z : ℤ) : (z : BitVec w).toFin = ↑z := by
  rw [← ofFin_intCast]

/-!
## Injectivity
-/

/-
**BitVec.toNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `BitVec`。
形式化陈述：∀ {n : ℕ}, Function.Injective BitVec.toNat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Injectivity
-/
theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**BitVec.toFin_injective** 是 Mathlib 中的一个定理，位于命名空间 `BitVec`。
形式化陈述：∀ {n : ℕ}, Function.Injective BitVec.toFin
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-!
## Scalar Multiplication and Powers
-/

open Fin.NatCast

/-
**BitVec.toFin_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `BitVec`。
形式化陈述：toFin_nsmul (n : Nat) (x : BitVec w) : toFin (n • x) = n • x.toFin
参数：n : Nat；x : BitVec w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BitVec.toFin_mul`：∀ {n : ℕ} (x y : BitVec n), (x * y).toFin = x.toFin * 
y.toFin
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toFin_nsmul (n : ℕ) (x : BitVec w) : toFin (n • x) = n • x.toFin :=
  toFin_mul _ _ |>.trans <| by
    open scoped Fin.CommRing in
    simp only [natCast_eq_ofNat, toFin_ofNat, Fin.ofNat_eq_cast, nsmul_eq_mul]
/-
**BitVec.toFin_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `BitVec`。
形式化陈述：toFin_zsmul (z : Int) (x : BitVec w) : toFin (z • x) = z • x.toFin
参数：z : Int；x : BitVec w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BitVec.toFin_mul`：∀ {n : ℕ} (x y : BitVec n), (x * y).toFin = x.toFin * 
y.toFin
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BitVec.toFin_intCast`：∀ {w : ℕ} (z : ℤ), (↑z).toFin = ↑z
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toFin_zsmul (z : ℤ) (x : BitVec w) : toFin (z • x) = z • x.toFin :=
  toFin_mul _ _ |>.trans <| by
    open scoped Fin.CommRing in
    simp only [zsmul_eq_mul, toFin_intCast]

set_option backward.isDefEq.respectTransparency false in
/-
**BitVec.toFin_pow** 是 Mathlib 中的一个引理，位于命名空间 `BitVec`。
形式化陈述：toFin_pow (x : BitVec w) (n : Nat) : toFin (x ^ n) = x.toFin ^ n
参数：x : BitVec w；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma toFin_pow (x : BitVec w) (n : ℕ) : toFin (x ^ n) = x.toFin ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ]

/-!
## Ring
-/

-- Verify that the `HPow` instance from Lean agrees definitionally with the instance via `Monoid`.
/-
**BitVec.** 是 Mathlib 中的一个示例，位于命名空间 `BitVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : @instHPow (Fin (2 ^ w)) ℕ NPow.toPow = Lean.Grind.Fin.instHPowFinNatOfNeZero := rfl
/-
**BitVec.** 是 Mathlib 中的一个实例，位于命名空间 `BitVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commSemiring _
    toFin_zero
    toFin_one
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    toFin_natCast
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`
/-
**BitVec.** 是 Mathlib 中的一个实例，位于命名空间 `BitVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

/-- The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`. -/
@[simps]
/-
**BitVec.equivFin** 是 Mathlib 中的一个定义，位于命名空间 `BitVec`。
形式化陈述：equivFin {m : Nat} : BitVec m ≃+* Fin (2 ^ m) where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BitVec.toFin_mul`：∀ {n : ℕ} (x y : BitVec n), (x * y).toFin = x.toFin * 
y.toFin
· 使用定理 `BitVec.toFin_add`：∀ {w : ℕ} (x y : BitVec w), (x + y).toFin = x.toFin + 
y.toFin

--- 原说明 ---
The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`.
-/
def equivFin {m : ℕ} : BitVec m ≃+* Fin (2 ^ m) where
  toFun a := a.toFin
  invFun a := ofFin a
  map_mul' := toFin_mul
  map_add' := toFin_add

end BitVec

