/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/

public section


open AffineMap AffineEquiv

set_option backward.isDefEq.respectTransparency false in
/-
**lineMap_inv_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_inv_two {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [A
ddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = 
midpoint R a b
参数：a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem lineMap_inv_two {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = midpoint R a b :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**lineMap_one_half** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lineMap_one_half {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [
AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R)
 = midpoint R a b
参数：a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `lineMap_inv_two`：lineMap_inv_two {R : Type*} {V P : Type*} [DivisionRing
 R] [CharZero R] [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) : lineM
ap a …
-/
theorem lineMap_one_half {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div, lineMap_inv_two]
/-
**homothety_invOf_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：homothety_invOf_two {R : Type*} {V P : Type*} [CommRing R] [Invertible (2 
: R)] [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) : homothety a (⅟2 
: R) b = midpoint R a b
参数：2 : R；a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem homothety_invOf_two {R : Type*} {V P : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) :
    homothety a (⅟2 : R) b = midpoint R a b :=
  rfl
/-
**homothety_inv_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：homothety_inv_two {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCom
mGroup V] [Module k V] [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = mid
point k a b
参数：a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem homothety_inv_two {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = midpoint k a b :=
  rfl
/-
**homothety_one_half** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：homothety_one_half {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCo
mmGroup V] [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = 
midpoint k a b
参数：a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `homothety_inv_two`：homothety_inv_two {k : Type*} {V P : Type*} [Field k]
 [CharZero k] [AddCommGroup V] [Module k V] [AddTorsor V P] (a b : P) : homothet
y a (2⁻…
-/
theorem homothety_one_half {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div, homothety_inv_two]

@[simp]
/-
**pi_midpoint_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_midpoint_apply {k ι : Type*} {V : ι -> Type*} {P : ι -> Type*} [Ring k]
 [Invertible (2 : k)] [forall i, AddCommGroup (V i)] [forall i, Module k (V i)] 
[forall i, AddTorsor (V i) (P i)] (f g : forall i, P i) (i : ι) : midpoint k f g
 i = midpoint k (f i) (g i)
参数：2 : k；V i；V i；V i；P i；f g : forall i, P i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem pi_midpoint_apply {k ι : Type*} {V : ι → Type*} {P : ι → Type*} [Ring k]
    [Invertible (2 : k)] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddTorsor (V i) (P i)] (f g : ∀ i, P i) (i : ι) :
    midpoint k f g i = midpoint k (f i) (g i) :=
  rfl
