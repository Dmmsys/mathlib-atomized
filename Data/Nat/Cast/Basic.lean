/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Commute.zero_right Commute.add_right abs_eq_max_neg
  NeZero.natCast_ne
-- TODO: `MulOpposite.op_natCast` was not intended to be imported
-- assert_not_exists MulOpposite.op_natCast

open Additive Multiplicative

variable {α β : Type*}

namespace Nat

/-- `Nat.cast : ℕ → α` as an `AddMonoidHom`. -/
/-
**Nat.castAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：castAddMonoidHom (α : Type*) [AddMonoidWithOne α] : Nat ->+ α where toFun
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n

--- 原说明 ---
`Nat.cast : ℕ → α` as an `AddMonoidHom`.
-/
def castAddMonoidHom (α : Type*) [AddMonoidWithOne α] :
    ℕ →+ α where
  toFun := Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]
/-
**Nat.coe_castAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : Nat -> α
) = Nat.cast
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = Nat.cast :=
  rfl
/-
**Nat._root_.Even.natCast** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Even.natCast [AddMonoidWithOne α] {n : ℕ} (hn : Even n) : Even (n : α) :=
  hn.map <| Nat.castAddMonoidHom α

section NonAssocSemiring
variable [NonAssocSemiring α]

/-
**Nat.cast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(m * n) = ↑m * ↑n
参数：m n : ℕ；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
@[simp, norm_cast] lemma cast_mul (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_add, *]

variable (α) in
/-- `Nat.cast : ℕ → α` as a `RingHom` -/
@[instance_reducible]
/-
**Nat.castRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：castRingHom : Nat ->+* α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n

--- 原说明 ---
`Nat.cast : ℕ → α` as a `RingHom`
-/
def castRingHom : ℕ →+* α :=
  { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }
/-
**Nat.coe_castRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [inst : NonAssocSemiring α], ⇑(Nat.castRingHom α) = Nat.c
ast
参数：Nat.castRingHom α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_castRingHom : (castRingHom α : ℕ → α) = Nat.cast := rfl
/-
**Nat._root_.nsmul_eq_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.nsmul_eq_mul' (a : α) (n : ℕ) : n • a = a * n := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, mul_add, mul_one]
/-
**Nat.ofNat_nsmul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ofNat_nsmul_eq_mul (n : Nat) [n.AtLeastTwo] (a : α) : ofNat(n) • a = ofNat
(n) * a
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofNat_nsmul_eq_mul (n : ℕ) [n.AtLeastTwo] (a : α) : ofNat(n) • a = ofNat(n) * a := by
  simp [nsmul_eq_mul]

end NonAssocSemiring

section Semiring
variable [Semiring α] {m n : ℕ}

@[simp, norm_cast]
/-
**Nat.cast_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) = ↑m ^ n
参数：m n : ℕ；m ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_pow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n) = (m ^ n : α)
  | 0 => by simp
  | n + 1 => by rw [_root_.pow_succ', _root_.pow_succ', cast_mul, cast_pow m n]

@[gcongr]
/-
**Nat.cast_dvd_cast** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α)
参数：h : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
lemma cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α) := map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

end Semiring
end Nat

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B] [FunLike F ℕ A] [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
/-
**eq_natCast'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {A : Type u_3} {F : Type u_5} [inst : FunLike F ℕ A] [inst_1 : AddMonoid
WithOne A] [AddMonoidHomClass F ℕ A] (f : F),   f 1 = 1 → ∀ (n : ℕ), f n = ↑n
参数：f : F；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.cast_add_one]
/-
**map_natCast'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F
 A B] (f : F) (h : f 1 = 1) : forall n : Nat, f n = n
参数：f : F；h : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_natCast'`：∀ {A : Type u_3} {F : Type u_5} [inst : FunLike F ℕ A] [ins
t_1 : AddMonoidWithOne A] [AddMonoidHomClass F ℕ A] (f : F),   f 1 = 1 → ∀ (n : 
ℕ…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n :=
  eq_natCast' ((f : A →+ B).comp <| Nat.castAddMonoidHom _) (by simpa)
/-
**map_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ofNat' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A
 B] (f : F) (h : f 1 = 1) (n : Nat) [n.AtLeastTwo] : f (OfNat.ofNat n) = OfNat.o
fNat n
参数：f : F；h : f 1 = 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast'`：map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [Add
MonoidHomClass F A B] (f : F) (h : f 1 = 1) : forall n : Nat, f n = n
-/
theorem map_ofNat' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) (n : ℕ) [n.AtLeastTwo] : f (OfNat.ofNat n) = OfNat.ofNat n :=
  map_natCast' f h n

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type*} [MulZeroOneClass A] [FunLike F ℕ A]

/-- If two `MonoidWithZeroHom`s agree on the positive naturals they are equal. -/
/-
**ext_nat''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_nat'' [ZeroHomClass F Nat A] (f g : F) (h_pos : forall {n : Nat}, 0 < 
n -> f n = g n) : f = g
参数：f g : F；h_pos : forall {n : Nat}, 0 < n -> f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
If two `MonoidWithZeroHom`s agree on the positive naturals they are equal.
-/
theorem ext_nat'' [ZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  · exact h_pos n.succ_pos

@[ext]
/-
**MonoidWithZeroHom.ext_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidWithZeroHom.ext_nat {f g : Nat ->*₀ A} : (forall {n : Nat}, 0 < n ->
 f n = g n) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ext_nat''`：ext_nat'' [ZeroHomClass F Nat A] (f g : F) (h_pos : forall {n
 : Nat}, 0 < n -> f n = g n) : f = g
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem MonoidWithZeroHom.ext_nat {f g : ℕ →*₀ A} : (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat'' f g

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
/-
**eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) : forall n, f 
n = n
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_natCast'`：∀ {A : Type u_3} {F : Type u_5} [inst : FunLike F ℕ A] [ins
t_1 : AddMonoidWithOne A] [AddMonoidHomClass F ℕ A] (f : F),   f 1 = 1 → ∀ (n : 
ℕ…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem eq_natCast [FunLike F ℕ R] [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f

@[simp]
/-
**map_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : forall n : Nat,
 f (n : R) = n
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast'`：map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [Add
MonoidHomClass F A B] (f : F) (h : f 1 = 1) : forall n : Nat, f n = n
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f

/-- This lemma is not marked `@[simp]` lemma because its `#discr_tree_key` (for the LHS) would just
be `DFunLike.coe _ _`, due to the `ofNat` that https://github.com/leanprover/lean4/issues/2867
forces us to include, and therefore it would negatively impact performance.

If that issue is resolved, this can be marked `@[simp]`. -/
/-
**map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : Nat) [Nat.AtLe
astTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n

--- 原说明 ---
This lemma is not marked `@[simp]` lemma because its `#discr_tree_key` (for the 
LHS) would just
be `DFunLike.coe _ _`, due to the `ofNat` that https://github.com/leanprover/lea
n4/issues/2867
forces us to include, and therefore it would negatively impact performance.

If that issue is resolved, this can be marked `@[simp]`.
-/
theorem map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) [Nat.AtLeastTwo n] :
    (f ofNat(n) : S) = OfNat.ofNat n :=
  map_natCast f n
/-
**ext_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_nat [FunLike F Nat R] [RingHomClass F Nat R] (f g : F) : f = g
参数：f g : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ext_nat'`：ext_nat' [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F
) (h : f 1 = g 1) : f = g
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ext_nat [FunLike F ℕ R] [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp
/-
**NeZero.nat_of_neZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NeZero.nat_of_neZero {R S} [NonAssocSemiring R] [NonAssocSemiring S] {F} [
FunLike F R S] [RingHomClass F R S] (f : F) {n : Nat} [hn : NeZero (n : S)] : Ne
Zero (n : R)
参数：f : F；n : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NeZero.of_map`：of_map (f : F) [neZero : NeZero (f a)] : NeZero a
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem NeZero.nat_of_neZero {R S} [NonAssocSemiring R] [NonAssocSemiring S]
    {F} [FunLike F R S] [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) :=
  .of_map (f := f) (neZero := by simp only [map_natCast, hn])

end RingHomClass

namespace RingHom

/-- This is primed to match `eq_intCast'`. -/
/-
**RingHom.eq_natCast'** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_natCast' {R} [NonAssocSemiring R] (f : Nat ->+* R) : f = Nat.castRingHo
m R
参数：f : Nat ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n

--- 原说明 ---
This is primed to match `eq_intCast'`.
-/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f

end RingHom

@[simp, norm_cast]
/-
**Nat.cast_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.cast_id (n : Nat) : n.cast = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nat.cast_id (n : ℕ) : n.cast = n :=
  rfl

@[simp]
/-
**Nat.castRingHom_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.castRingHom_nat : Nat.castRingHom Nat = RingHom.id Nat
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl

/-- We don't use `RingHomClass` here, since that might cause type-class slowdown for
`Subsingleton`. -/
/-
**Nat.uniqueRingHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (Nat ->+* R) w
here default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.eq_natCast'`：eq_natCast' {R} [NonAssocSemiring R] (f : Nat ->+* 
R) : f = Nat.castRingHom R

--- 原说明 ---
We don't use `RingHomClass` here, since that might cause type-class slowdown for
`Subsingleton`.
-/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (ℕ →+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

namespace Pi

variable {π : α → Type*}

section NatCast
variable [∀ a, NatCast (π a)]

/-
**Pi.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instNatCast : NatCast (forall a, π a) where natCast n _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast (∀ a, π a) where natCast n _ := n

@[simp]
/-
**Pi.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：natCast_apply (n : Nat) (a : α) : (n : forall a, π a) a = n
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl

@[push ←]
/-
**Pi.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：natCast_def (n : Nat) : (n : forall a, π a) = fun _ => ↑n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_def (n : ℕ) : (n : ∀ a, π a) = fun _ ↦ ↑n :=
  rfl

end NatCast

section OfNat

-- This instance is low priority, as `to_additive` only works with the one that comes from `One`
-- and `Zero`.
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) instOfNat (n : ℕ) [∀ i, OfNat (π i) n] : OfNat ((i : α) → π i) n where
  ofNat _ := OfNat.ofNat n

@[simp]
/-
**Pi.ofNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：ofNat_apply (n : Nat) [forall i, OfNat (π i) n] (a : α) : (ofNat(n) : fora
ll a, π a) a = ofNat(n)
参数：n : Nat；π i；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_apply (n : ℕ) [∀ i, OfNat (π i) n] (a : α) : (ofNat(n) : ∀ a, π a) a = ofNat(n) := rfl

@[push ←]
/-
**Pi.ofNat_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：ofNat_def (n : Nat) [forall i, OfNat (π i) n] : (OfNat.ofNat n : forall a,
 π a) = fun _ => ofNat(n)
参数：n : Nat；π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofNat_def (n : ℕ) [∀ i, OfNat (π i) n] : (OfNat.ofNat n : ∀ a, π a) = fun _ ↦ ofNat(n) := rfl

end OfNat

end Pi

/-
**Sum.elim_natCast_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : Nat) : Sum.elim 
(n : α -> γ) (n : β -> γ) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.elim_lam_const_lam_const`：∀ {γ : Sort u_1} {α : Type u_2} {β : Type 
u_3} (c : γ), (Sum.elim (fun x => c) fun x => c) = fun x => c
-/
theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
