/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.Basic

/-!
# The power operator on `ℤˣ` by `ZMod 2`, `ℕ`, and `ℤ`

See also the related `negOnePow`.

## TODO

* Generalize this to `Pow G (Zmod n)` where `orderOf g = n`.

## Implementation notes

In future, we could consider a `LawfulPower M R` typeclass; but we can save ourselves a lot of work
by using `Module R (Additive M)` in its place, especially since this already has instances for
`R = ℕ` and `R = ℤ`.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (ZMod 2) (Additive ℤˣ) where
  smul z au := .ofMul <| au.toMul ^ z.val
/-
**ZMod.smul_units_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZMod.smul_units_def (z : ZMod 2) (au : Additive Intˣ) : z • au = z.val • a
u
参数：z : ZMod 2；au : Additive Intˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ZMod.smul_units_def (z : ZMod 2) (au : Additive ℤˣ) :
    z • au = z.val • au := rfl
/-
**ZMod.natCast_smul_units** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZMod.natCast_smul_units (n : Nat) (au : Additive Intˣ) : (n : ZMod 2) • au
 = n • au
参数：n : Nat；au : Additive Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.units_pow_eq_pow_mod_two`：units_pow_eq_pow_mod_two (u : Intˣ) (n : N
at) : u ^ n = u ^ (n % 2)
-/
lemma ZMod.natCast_smul_units (n : ℕ) (au : Additive ℤˣ) : (n : ZMod 2) • au = n • au :=
  (Int.units_pow_eq_pow_mod_two au n).symm

/-- This is an indirect way of saying that `ℤˣ` has a power operation by `ZMod 2`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an indirect way of saying that `ℤˣ` has a power operation by `ZMod 2`.
-/
instance : Module (ZMod 2) (Additive ℤˣ) where
  smul z au := .ofMul <| au.toMul ^ z.val
  one_smul _ := Additive.toMul.injective <| pow_one _
  mul_smul z₁ z₂ au := Additive.toMul.injective <| by
    dsimp only [ZMod.smul_units_def, toMul_nsmul]
    rw [← pow_mul, ZMod.val_mul, ← Int.units_pow_eq_pow_mod_two, mul_comm]
  smul_zero _ := Additive.toMul.injective <| one_pow _
  smul_add _ _ _ := Additive.toMul.injective <| mul_pow _ _ _
  add_smul z₁ z₂ au := Additive.toMul.injective <| by
    dsimp only [ZMod.smul_units_def, toMul_nsmul, toMul_add]
    rw [← pow_add, ZMod.val_add, ← Int.units_pow_eq_pow_mod_two]
  zero_smul au := Additive.toMul.injective <| pow_zero au.toMul

section CommSemiring
variable {R : Type*} [CommSemiring R] [Module R (Additive ℤˣ)]

/-- There is a canonical power operation on `ℤˣ` by `R` if `Additive ℤˣ` is an `R`-module.

In lemma names, this operation is called `uzpow` to match `zpow`.

Notably this is satisfied by `R ∈ {ℕ, ℤ, ZMod 2}`. -/
/-
**Int.instUnitsPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instUnitsPow : Pow Intˣ R where pow u r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical power operation on `ℤˣ` by `R` if `Additive ℤˣ` is an `R`-m
odule.

In lemma names, this operation is called `uzpow` to match `zpow`.

Notably this is satisfied by `R ∈ {ℕ, ℤ, ZMod 2}`.
-/
instance Int.instUnitsPow : Pow ℤˣ R where
  pow u r := (r • Additive.ofMul u).toMul

-- The above instances form no typeclass diamonds with the standard power operators
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Int.instUnitsPow = NPow.toPow := by with_implicit rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Int.instUnitsPow = ZPow.toPow := by with_implicit rfl
/-
**ofMul_uzpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (u : ℤˣ) (r : R),   Additive.ofMul (u ^ r) = r • Additive.ofMul u
参数：Additive ℤˣ；u : ℤˣ；r : R；u ^ r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofMul_uzpow (u : ℤˣ) (r : R) : Additive.ofMul (u ^ r) = r • Additive.ofMul u := rfl
/-
**toMul_uzpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (u : Additive ℤˣ) (r : R),   Additive.toMul (r • u) = Additive.toMul u ^
 r
参数：Additive ℤˣ；u : Additive ℤˣ；r : R；r • u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMul_uzpow (u : Additive ℤˣ) (r : R) : (r • u).toMul = u.toMul ^ r := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**uzpow_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (u : ℤˣ) (n : ℕ), u ^ ↑n = u ^ n
参数：Additive ℤˣ；u : ℤˣ；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toMul_nsmul`：toMul_nsmul [Monoid α] (n : Nat) (a : Additive α) : (n • a)
.toMul = a.toMul ^ n
· 使用定理 `toMul_ofMul`：toMul_ofMul (x : α) : (ofMul x).toMul = x
-/
@[norm_cast] lemma uzpow_natCast (u : ℤˣ) (n : ℕ) : u ^ (n : R) = u ^ n := by
  change ((n : R) • Additive.ofMul u).toMul = _
  rw [Nat.cast_smul_eq_nsmul, toMul_nsmul, toMul_ofMul]
/-
**uzpow_coe_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uzpow_coe_nat (s : Intˣ) (n : Nat) [n.AtLeastTwo] : s ^ (ofNat(n) : R) = s
 ^ (ofNat(n) : Nat)
参数：s : Intˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uzpow_natCast`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_
.Module R (Additive ℤˣ)] (u : ℤˣ) (n : ℕ), u ^ ↑n = u ^ n
-/
lemma uzpow_coe_nat (s : ℤˣ) (n : ℕ) [n.AtLeastTwo] :
    s ^ (ofNat(n) : R) = s ^ (ofNat(n) : ℕ) :=
  uzpow_natCast _ _
/-
**one_uzpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (x : R), 1 ^ x = 1
参数：Additive ℤˣ；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
@[simp] lemma one_uzpow (x : R) : (1 : ℤˣ) ^ x = 1 :=
  Additive.ofMul.injective <| smul_zero _
/-
**mul_uzpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_uzpow (s₁ s₂ : Intˣ) (x : R) : (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x
参数：s₁ s₂ : Intˣ；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
lemma mul_uzpow (s₁ s₂ : ℤˣ) (x : R) : (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x :=
  Additive.ofMul.injective <| smul_add x (Additive.ofMul s₁) (Additive.ofMul s₂)
/-
**uzpow_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (s : ℤˣ), s ^ 0 = 1
参数：Additive ℤˣ；s : ℤˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
@[simp] lemma uzpow_zero (s : ℤˣ) : (s ^ (0 : R) : ℤˣ) = (1 : ℤˣ) :=
  Additive.ofMul.injective <| zero_smul R (Additive.ofMul s)
/-
**uzpow_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Module R (Additi
ve ℤˣ)] (s : ℤˣ), s ^ 1 = s
参数：Additive ℤˣ；s : ℤˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
@[simp] lemma uzpow_one (s : ℤˣ) : (s ^ (1 : R) : ℤˣ) = s :=
  Additive.ofMul.injective <| one_smul R (Additive.ofMul s)
/-
**uzpow_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uzpow_mul (s : Intˣ) (x y : R) : s ^ (x * y) = (s ^ x) ^ y
参数：s : Intˣ；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma uzpow_mul (s : ℤˣ) (x y : R) : s ^ (x * y) = (s ^ x) ^ y :=
  Additive.ofMul.injective <| mul_comm x y ▸ mul_smul y x (Additive.ofMul s)
/-
**uzpow_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uzpow_add (s : Intˣ) (x y : R) : s ^ (x + y) = s ^ x * s ^ y
参数：s : Intˣ；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
lemma uzpow_add (s : ℤˣ) (x y : R) : s ^ (x + y) = s ^ x * s ^ y :=
  Additive.ofMul.injective <| add_smul x y (Additive.ofMul s)

end CommSemiring

section CommRing
variable {R : Type*} [CommRing R] [Module R (Additive ℤˣ)]

/-
**uzpow_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uzpow_sub (s : Intˣ) (x y : R) : s ^ (x - y) = s ^ x / s ^ y
参数：s : Intˣ；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
lemma uzpow_sub (s : ℤˣ) (x y : R) : s ^ (x - y) = s ^ x / s ^ y :=
  Additive.ofMul.injective <| sub_smul x y (Additive.ofMul s)
/-
**uzpow_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uzpow_neg (s : Intˣ) (x : R) : s ^ (-x) = (s ^ x)⁻¹
参数：s : Intˣ；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
lemma uzpow_neg (s : ℤˣ) (x : R) : s ^ (-x) = (s ^ x)⁻¹ :=
  Additive.ofMul.injective <| neg_smul x (Additive.ofMul s)

set_option backward.isDefEq.respectTransparency false in
/-
**uzpow_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : _root_.Module R (Additive ℤ
ˣ)] (u : ℤˣ) (z : ℤ), u ^ ↑z = u ^ z
参数：Additive ℤˣ；u : ℤˣ；z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `toMul_zsmul`：toMul_zsmul [DivInvMonoid α] (z : Int) (a : Additive α) : (
z • a).toMul = a.toMul ^ z
· 使用定理 `toMul_ofMul`：toMul_ofMul (x : α) : (ofMul x).toMul = x
-/
@[norm_cast] lemma uzpow_intCast (u : ℤˣ) (z : ℤ) : u ^ (z : R) = u ^ z := by
  change ((z : R) • Additive.ofMul u).toMul = _
  rw [Int.cast_smul_eq_zsmul, toMul_zsmul, toMul_ofMul]

end CommRing

