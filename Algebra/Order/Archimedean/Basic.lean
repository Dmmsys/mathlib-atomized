/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Directed
public import Mathlib.Data.Rat.Floor

import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Monoid.Units
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Int.LeastGreatest

/-!
# Archimedean groups and fields

This file proves several results connected to the notion of Archimedean groups. Being Archimedean
means that for all elements `x` and `y > 0` there exists a natural number `n` such that `x ≤ n • y`.

## Main definitions

* `Archimedean.floorRing` defines a floor function on an archimedean linearly ordered ring making it
  into a `floorRing`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/

@[expose] public section

assert_not_exists Finset

open Int Set

variable {G M R K : Type*}

@[to_additive]
/-
**MulArchimedean.comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulArchimedean.comap [CommMonoid G] [LinearOrder G] [CommMonoid M] [Partia
lOrder M] [MulArchimedean M] (f : G ->* M) (hf : StrictMono f) : MulArchimedean 
G where arch x _ h
参数：f : G ->* M；hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma MulArchimedean.comap [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
    [MulArchimedean M] (f : G →* M) (hf : StrictMono f) :
    MulArchimedean G where
  arch x _ h := by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

@[to_additive]
/-
**OrderDual.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instMulArchimedean [CommGroup G] [PartialOrder G] [IsOrderedMono
id G] [MulArchimedean G] : MulArchimedean Gᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, 1 < a⁻¹ ↔ a < 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
-/
instance OrderDual.instMulArchimedean [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    [MulArchimedean G] :
    MulArchimedean Gᵒᵈ :=
  ⟨fun x y hy =>
    have hy : (ofDual y) < 1 := hy
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (one_lt_inv'.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩
/-
**Additive.instArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.instArchimedean [CommGroup G] [PartialOrder G] [MulArchimedean G]
 : Archimedean (Additive G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
-/
instance Additive.instArchimedean [CommGroup G] [PartialOrder G] [MulArchimedean G] :
    Archimedean (Additive G) :=
  ⟨fun x _ hy ↦ MulArchimedean.arch x.toMul hy⟩
/-
**Multiplicative.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.instMulArchimedean [AddCommGroup G] [PartialOrder G] [Archi
medean G] : MulArchimedean (Multiplicative G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
-/
instance Multiplicative.instMulArchimedean [AddCommGroup G] [PartialOrder G] [Archimedean G] :
    MulArchimedean (Multiplicative G) :=
  ⟨fun x _ hy ↦ Archimedean.arch x.toAdd hy⟩

section IsOrderedMonoid

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

/-- An archimedean decidable linearly ordered `CommGroup` has a version of the floor: for
`a > 1`, any `g` in the group lies between some two consecutive powers of `a`. -/
@[to_additive /-- An archimedean decidable linearly ordered `AddCommGroup` has a version of the
floor: for `a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/]
/-
**existsUnique_zpow_near_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_zpow_near_of_one_lt {a : G} (ha : 1 < a) (g : G) : exists! k 
: Int, a ^ k <= g ∧ g < a ^ (k + 1)
参数：ha : 1 < a；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_le_inv'`：inv_le_inv' : a <= b -> b⁻¹ <= a⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `zpow_le_zpow_iff_right`：zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m <= a
 ^ n ↔ m <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.exists_greatest_of_bdd`：exists_greatest_of_bdd {P : Int -> Prop} (Hb
dd : exists b : Int, forall z : Int, P z -> z <= b) (Hinh : exists z : Int, P z)
 : exists ub : I…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Int.le_of_lt_add_one`：∀ {a b : ℤ}, a < b + 1 → a ≤ b
· 使用引理 `zpow_lt_zpow_iff_right`：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a 
^ n ↔ m < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem existsUnique_zpow_near_of_one_lt {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, a ^ k ≤ g ∧ g < a ^ (k + 1) := by
  let s : Set ℤ := { n : ℤ | a ^ n ≤ g }
  obtain ⟨k, hk : g⁻¹ ≤ a ^ k⟩ := MulArchimedean.arch g⁻¹ ha
  have h_ne : s.Nonempty := ⟨-k, by simpa [s] using inv_le_inv' hk⟩
  obtain ⟨k, hk⟩ := MulArchimedean.arch g ha
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ) := by
    intro n hn
    apply (zpow_le_zpow_iff_right ha).mp
    rw [← zpow_natCast] at hk
    exact le_trans hn hk
  obtain ⟨m, hm, hm'⟩ := Int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne
  have hm'' : g < a ^ (m + 1) := by
    contrapose! hm'
    exact ⟨m + 1, hm', lt_add_one _⟩
  refine ⟨m, ⟨hm, hm''⟩, fun n hn => (hm' n hn.1).antisymm <| Int.le_of_lt_add_one ?_⟩
  rw [← zpow_lt_zpow_iff_right ha]
  exact lt_of_le_of_lt hm hn.2

@[to_additive]
/-
**existsUnique_zpow_near_of_one_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_zpow_near_of_one_lt' {a : G} (ha : 1 < a) (g : G) : exists! k
 : Int, 1 <= g / a ^ k ∧ g / a ^ k < a
参数：ha : 1 < a；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `existsUnique_zpow_near_of_one_lt`：existsUnique_zpow_near_of_one_lt {a : 
G} (ha : 1 < a) (g : G) : exists! k : Int, a ^ k <= g ∧ g < a ^ (k + 1)
-/
theorem existsUnique_zpow_near_of_one_lt' {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, 1 ≤ g / a ^ k ∧ g / a ^ k < a := by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]
/-
**existsUnique_div_zpow_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_div_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) : exists! m :
 Int, b / a ^ m in Set.Ico c (c * a)
参数：ha : 1 < a；b c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `existsUnique_zpow_near_of_one_lt'`：existsUnique_zpow_near_of_one_lt' {a 
: G} (ha : 1 < a) (g : G) : exists! k : Int, 1 <= g / a ^ k ∧ g / a ^ k < a
-/
theorem existsUnique_div_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ico c (c * a) := by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
/-
**existsUnique_mul_zpow_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_mul_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) : exists! m :
 Int, b * a ^ m in Set.Ico c (c * a)
参数：ha : 1 < a；b c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Bijective.existsUnique_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.Bijective f → ∀ {p : β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `existsUnique_zpow_near_of_one_lt'`：existsUnique_zpow_near_of_one_lt' {a 
: G} (ha : 1 < a) (g : G) : exists! k : Int, 1 <= g / a ^ k ∧ g / a ^ k < a
-/
theorem existsUnique_mul_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ico c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
/-
**existsUnique_add_zpow_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_add_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) : exists! m :
 Int, b * a ^ m in Set.Ioc c (c * a)
参数：ha : 1 < a；b c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Bijective.existsUnique_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.Bijective f → ∀ {p : β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `existsUnique_zpow_near_of_one_lt`：existsUnique_zpow_near_of_one_lt {a : 
G} (ha : 1 < a) (g : G) : exists! k : Int, a ^ k <= g ∧ g < a ^ (k + 1)
-/
theorem existsUnique_add_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.addRight (1 : ℤ)).bijective.existsUnique_iff.2 <| by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]
/-
**existsUnique_sub_zpow_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：existsUnique_sub_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) : exists! m :
 Int, b / a ^ m in Set.Ioc c (c * a)
参数：ha : 1 < a；b c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Bijective.existsUnique_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.Bijective f → ∀ {p : β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `existsUnique_add_zpow_mem_Ioc`：existsUnique_add_zpow_mem_Ioc {a : G} (ha
 : 1 < a) (b c : G) : exists! m : Int, b * a ^ m in Set.Ioc c (c * a)
-/
theorem existsUnique_sub_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

end IsOrderedMonoid

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsDirectedOrder R :=
  ⟨fun x y ↦
    let ⟨m, hm⟩ := exists_nat_ge x; let ⟨n, hn⟩ := exists_nat_ge y
    let ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    ⟨k, hm.trans <| Nat.mono_cast hmk, hn.trans <| Nat.mono_cast hnk⟩⟩

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

/-
**add_one_pow_unbounded_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : exists n : Nat, x < (y
 + 1) ^ n
参数：x : R；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `lt_one_add`：lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `one_add_mul_le_pow_of_sq_nonneg`：one_add_mul_le_pow_of_sq_nonneg (Hsq : 
0 <= a ^ 2) (Hsq' : 0 <= (1 + a) ^ 2) (H : 0 <= 2 + a) (n : Nat) : 1 + n * a <= 
(1 + a) ^ n
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
-/
theorem add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n :=
  have : 0 ≤ 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h ↦
    calc
      x ≤ n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ ≤ (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]
/-
**pow_unbounded_of_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : exists n
 : Nat, x < y ^ n
参数：x : R；hy1 : 1 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pos_add_of_lt'`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLT α],   a < b → ∃ c, 0 <
 c ∧ a + c …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_one_pow_unbounded_of_pos`：add_one_pow_unbounded_of_pos (x : R) (hy :
 0 < y) : exists n : Nat, x < (y + 1) ^ n
-/
lemma pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n := by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

end StrictOrderedSemiring

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsCodirectedOrder R where
  directed a b :=
    let ⟨m, hm⟩ := exists_int_le a; let ⟨n, hn⟩ := exists_int_le b
    ⟨(min m n : ℤ), le_trans (Int.cast_mono <| min_le_left _ _) hm,
      le_trans (Int.cast_mono <| min_le_right _ _) hn⟩

end OrderedRing

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

/-- See `exists_floor'` for a more general version which only assumes the element is bounded by
two integers. -/
/-
**exists_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_floor (x : R) : exists fl : Int, forall z : Int, z <= fl ↔ (z : R) 
<= x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_floor'`：exists_floor' {α} [Ring α] [PartialOrder α] [IsOrderedRin
g α] [Nontrivial α] (x : α) (below : exists n : Int, n <= x) (above : exists n :
 In…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_int_lt`：exists_int_lt (x : R) : exists n : Int, (n : R) < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_int_gt`：exists_int_gt (x : R) : exists n : Int, x < n

--- 原说明 ---
See `exists_floor'` for a more general version which only assumes the element is
 bounded by
two integers.
-/
theorem exists_floor (x : R) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : R) ≤ x := by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

end StrictOrderedRing

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] [ExistsAddOfLE R]
  {x y : R}

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
/-
**exists_nat_pow_near** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nat_pow_near (hx : 1 <= x) (hy : 1 < y) : exists n : Nat, y ^ n <= 
x ∧ x < y ^ (n + 1)
参数：hx : 1 <= x；hy : 1 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m

--- 原说明 ---
Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one.
-/
theorem exists_nat_pow_near (hx : 1 ≤ x) (hy : 1 < y) : ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_gt (Nat.find_min h hltn), by rwa [hnsp]⟩

end LinearOrderedSemiring

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

/-
**exists_nat_one_div_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_nat_one_div_lt (hε : 0 < ε) : exists n : Nat, 1 / (n + 1 : K) < ε
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma exists_nat_one_div_lt (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : K) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀, ← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

variable [ExistsAddOfLE K]

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
but with ≤ and < the other way around. -/
/-
**exists_mem_Ico_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : exists n : Int, x in Ico (
y ^ n) (y ^ (n + 1))
参数：hx : 0 < x；hy : 1 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `inv_lt_comm₀`：inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `zpow_le_zpow_right₀`：zpow_le_zpow_right₀ (ha : 1 <= a) (hmn : m <= n) : 
a ^ m <= a ^ n
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Int.exists_greatest_of_bdd`：exists_greatest_of_bdd {P : Int -> Prop} (Hb
dd : exists b : Int, forall z : Int, P z -> z <= b) (Hinh : exists z : Int, P z)
 : exists ub : I…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Int.lt_succ`：∀ (a : ℤ), a < a + 1

--- 原说明 ---
Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
but with ≤ and < the other way around.
-/
theorem exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  have he : ∃ m : ℤ, y ^ m ≤ x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N, zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b := by
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
    refine ⟨M, fun m hm ↦ ?_⟩
    contrapose! hM
    rw [← zpow_natCast]
    exact le_trans (zpow_le_zpow_right₀ hy.le hM.le) hm
  obtain ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
  exact ⟨n, hn₁, lt_of_not_ge fun hge => (Int.lt_succ _).not_ge (hn₂ _ hge)⟩

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around. -/
/-
**exists_mem_Ioc_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : exists n : Int, x in Ioc (
y ^ n) (y ^ (n + 1))
参数：hx : 0 < x；hy : 1 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_mem_Ico_zpow`：exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : exi
sts n : Int, x in Ico (y ^ n) (y ^ (n + 1))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `inv_lt_comm₀`：inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用引理 `le_inv_comm₀`：le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a <= b⁻¹ ↔ b <= a
⁻¹

--- 原说明 ---
Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around.
-/
theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
  let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
/-
**exists_pow_lt_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : exists n : Nat, y ^ n 
< x
参数：hx : 0 < x；hy : y < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹

--- 原说明 ---
For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`.
-/
theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x := by
  by_cases! y_pos : y ≤ 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
/-
**exists_nat_pow_near_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x <= 1) (ypos : 0 < y) 
(hy : y < 1) : exists n : Nat, y ^ (n + 1) < x ∧ x <= y ^ n
参数：xpos : 0 < x；hx : x <= 1；ypos : 0 < y；hy : y < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_pow_near`：exists_nat_pow_near (hx : 1 <= x) (hy : 1 < y) : ex
ists n : Nat, y ^ n <= x ∧ x < y ^ (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_le_inv_iff₀`：one_le_inv_iff₀ : 1 <= a⁻¹ ↔ 0 < a ∧ a <= 1 where mp h
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `one_lt_inv_iff₀`：one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where mp h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a

--- 原说明 ---
Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `
y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1`
-/
theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

/-- If `a < b * c`, `0 < b ≤ 1` and `0 < c < 1`, then there is a power `c ^ n` with `n : ℕ`
strictly between `a` and `b`. -/
/-
**exists_pow_btwn_of_lt_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_pow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ :
 b <= 1) (hc₀ : 0 < c) (hc₁ : c < 1) : exists n : Nat, a < c ^ n ∧ c ^ n < b
参数：h : a < b * c；hb₀ : 0 < b；hb₁ : b <= 1；hc₀ : 0 < c；hc₁ : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_lt_of_lt_one_right`：mul_lt_of_lt_one_right [PosMulStrictMono α] (ha 
: 0 < a) (h : b < 1) : a * b < a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.sub_one_lt`：∀ {n : ℕ}, n ≠ 0 → n - 1 < n
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → n.pred.succ = n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)

--- 原说明 ---
If `a < b * c`, `0 < b ≤ 1` and `0 < c < 1`, then there is a power `c ^ n` with 
`n : ℕ`
strictly between `a` and `b`.
-/
lemma exists_pow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b ≤ 1)
    (hc₀ : 0 < c) (hc₁ : c < 1) :
    ∃ n : ℕ, a < c ^ n ∧ c ^ n < b := by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this ≠ 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_eq_of_ne_zero hn).symm, pow_succ, mul_lt_mul_iff_left₀ hc₀] at H
  exact Nat.find_min this (Nat.sub_one_lt hn) H

/-- If `a < b * c`, `b` is positive and `0 < c < 1`, then there is a power `c ^ n` with `n : ℤ`
strictly between `a` and `b`. -/
/-
**exists_zpow_btwn_of_lt_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_zpow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ 
: 0 < c) (hc₁ : c < 1) : exists n : Int, a < c ^ n ∧ c ^ n < b
参数：h : a < b * c；hb₀ : 0 < b；hc₀ : 0 < c；hc₁ : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `exists_pow_btwn_of_lt_mul`：exists_pow_btwn_of_lt_mul {a b c : K} (h : a 
< b * c) (hb₀ : 0 < b) (hb₁ : b <= 1) (hc₀ : 0 < c) (hc₁ : c < 1) : exists n : N
at, a < c ^ n ∧…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `lt_inv_mul_iff₀'`：lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < 
b
· 使用引理 `inv_mul_lt_iff₀`：inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `lt_inv_comm₀`：lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用引理 `inv_lt_comm₀`：inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a

--- 原说明 ---
If `a < b * c`, `b` is positive and `0 < c < 1`, then there is a power `c ^ n` w
ith `n : ℤ`
strictly between `a` and `b`.
-/
lemma exists_zpow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
    (hc₁ : c < 1) :
    ∃ n : ℤ, a < c ^ n ∧ c ^ n < b := by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_gt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt_or_ge a 1 with ha₁ | ha₁
      · refine ⟨0, ?_⟩
        rw [zpow_zero]
        exact ⟨ha₁, hb₁⟩
      · have : b⁻¹ < a⁻¹ * c := by rwa [lt_inv_mul_iff₀' ha, inv_mul_lt_iff₀ hb₀]
        obtain ⟨n, hn₁, hn₂⟩ :=
          exists_pow_btwn_of_lt_mul this (inv_pos_of_pos ha) (inv_le_one_of_one_le₀ ha₁) hc₀ hc₁
        refine ⟨-n, ?_, ?_⟩
        · rwa [lt_inv_comm₀ (pow_pos hc₀ n) ha, ← zpow_natCast, ← zpow_neg] at hn₂
        · rwa [inv_lt_comm₀ hb₀ (pow_pos hc₀ n), ← zpow_natCast, ← zpow_neg] at hn₁

end LinearOrderedSemifield

section LinearOrderedField
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-
**archimedean_iff_nat_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_nat_lt : Archimedean K ↔ forall x : K, exists n : Nat, x <
 n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem archimedean_iff_nat_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩
/-
**archimedean_iff_nat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_nat_le : Archimedean K ↔ forall x : K, exists n : Nat, x <
= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `archimedean_iff_nat_lt`：archimedean_iff_nat_lt : Archimedean K ↔ forall 
x : K, exists n : Nat, x < n
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem archimedean_iff_nat_le : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩
/-
**archimedean_iff_int_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_int_lt : Archimedean K ↔ forall x : K, exists n : Int, x <
 n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_int_gt`：exists_int_gt (x : R) : exists n : Int, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `archimedean_iff_nat_lt`：archimedean_iff_nat_lt : Archimedean K ↔ forall 
x : K, exists n : Nat, x < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Int.self_le_toNat`：∀ (a : ℤ), a ≤ ↑a.toNat
-/
theorem archimedean_iff_int_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩
/-
**archimedean_iff_int_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_int_le : Archimedean K ↔ forall x : K, exists n : Int, x <
= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `archimedean_iff_int_lt`：archimedean_iff_int_lt : Archimedean K ↔ forall 
x : K, exists n : Int, x < n
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem archimedean_iff_int_le : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩
/-
**archimedean_iff_rat_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_rat_lt : Archimedean K ↔ forall x : K, exists q : Rat, x <
 q where mp _ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `archimedean_iff_nat_lt`：archimedean_iff_nat_lt : Archimedean K ↔ forall 
x : K, exists n : Nat, x < n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
-/
theorem archimedean_iff_rat_lt : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x < q where
  mp _ x :=
    let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x ↦
    let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h <| mod_cast Nat.le_ceil _⟩
/-
**archimedean_iff_rat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：archimedean_iff_rat_le : Archimedean K ↔ forall x : K, exists q : Rat, x <
= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `archimedean_iff_rat_lt`：archimedean_iff_rat_lt : Archimedean K ↔ forall 
x : K, exists q : Rat, x < q where mp _ x
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
-/
theorem archimedean_iff_rat_le : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

variable [Archimedean K] {x y ε : K}
/-
**exists_rat_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_gt (x : K) : exists q : Rat, x < q
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `archimedean_iff_rat_lt`：archimedean_iff_rat_lt : Archimedean K ↔ forall 
x : K, exists q : Rat, x < q where mp _ x
-/
theorem exists_rat_gt (x : K) : ∃ q : ℚ, x < q := archimedean_iff_rat_lt.mp ‹_› _
/-
**exists_rat_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_int_lt`：exists_int_lt (x : R) : exists n : Int, (n : R) < x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem exists_rat_lt (x : K) : ∃ q : ℚ, (q : K) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩
/-
**exists_div_btwn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_div_btwn {x y : K} {n : Nat} (h : x < y) (nh : (y - x)⁻¹ < n) : exi
sts z : Int, x < (z : K) / n ∧ (z : K) / n < y
参数：h : x < y；nh : (y - x)⁻¹ < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_floor`：exists_floor (x : R) : exists fl : Int, forall z : Int, z 
<= fl ↔ (z : R) <= x
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 42 条，此处仅展示前 30 条）
-/
theorem exists_div_btwn {x y : K} {n : ℕ} (h : x < y) (nh : (y - x)⁻¹ < n) :
    ∃ z : ℤ, x < (z : K) / n ∧ (z : K) / n < y := by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
  refine ⟨(lt_div_iff₀ n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add, Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]
/-
**exists_rat_btwn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat, x < q ∧ q < y
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `exists_div_btwn`：exists_div_btwn {x y : K} {n : Nat} (h : x < y) (nh : (
y - x)⁻¹ < n) : exists z : Int, x < (z : K) / n ∧ (z : K) / n < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y := by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : ℚ) / n, ?_, ?_⟩ <;> simpa
/-
**exists_rat_mem_uIoo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_mem_uIoo {x y : K} (h : x != y) : exists q : Rat, ↑q in Set.uIo
o x y
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_lt_max`：min_lt_max : min a b < max a b ↔ a != b
-/
theorem exists_rat_mem_uIoo {x y : K} (h : x ≠ y) : ∃ q : ℚ, ↑q ∈ Set.uIoo x y :=
  exists_rat_btwn (min_lt_max.mpr h)
/-
**exists_pow_btwn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pow_btwn {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 < y)
 : exists q : K, 0 < q ∧ x < q ^ n ∧ q ^ n < y
参数：hn : n != 0；h : x < y；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniform_continuous_npow_on_bounded`：uniform_continuous_npow_on_bounded (
B : α) {ε : α} (hε : 0 < ε) (n : Nat) : exists δ > 0, forall q r : α, |r| <= B -
> |q - r| <= δ -> |q ^ n…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 74 条，此处仅展示前 30 条）
-/
theorem exists_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : K} (h : x < y) (hy : 0 < y) :
    ∃ q : K, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  have ⟨δ, δ_pos, cont⟩ := uniform_continuous_npow_on_bounded (max 1 y)
    (sub_pos.mpr <| max_lt_iff.mpr ⟨h, hy⟩) n
  have ex : ∃ m : ℕ, y ≤ (m * δ) ^ n := by
    have ⟨m, hm⟩ := exists_nat_ge (y / δ + 1 / δ)
    refine ⟨m, le_trans ?_ (le_self_pow₀ ?_ hn)⟩ <;> rw [← div_le_iff₀ δ_pos]
    · exact (lt_add_of_pos_right _ <| by positivity).le.trans hm
    · exact (le_add_of_nonneg_left <| by positivity).trans hm
  let m := Nat.find ex
  have m_pos : 0 < m := (Nat.find_pos _).mpr <| by simpa [zero_pow hn] using hy
  let q := m.pred * δ
  have qny : q ^ n < y := lt_of_not_ge (Nat.find_min ex <| Nat.pred_lt m_pos.ne')
  have q1y : |q| < max 1 y := (abs_eq_self.mpr <| by positivity).trans_lt <| lt_max_iff.mpr
    (or_iff_not_imp_left.mpr fun q1 ↦ (le_self_pow₀ (le_of_not_gt q1) hn).trans_lt qny)
  have xqn : max x 0 < q ^ n :=
    calc _ = y - (y - max x 0) := by rw [sub_sub_cancel]
      _ ≤ (m * δ) ^ n - (y - max x 0) := sub_le_sub_right (Nat.find_spec ex) _
      _ < (m * δ) ^ n - ((m * δ) ^ n - q ^ n) := by
        refine sub_lt_sub_left ((le_abs_self _).trans_lt <| cont _ _ q1y.le ?_) _
        rw [← Nat.succ_pred_eq_of_pos m_pos, Nat.cast_succ, ← sub_mul,
          add_sub_cancel_left, one_mul, abs_eq_self.mpr (by positivity)]
      _ = q ^ n := sub_sub_cancel ..
  exact ⟨q, lt_of_le_of_ne (by positivity) fun q0 ↦
    (le_sup_right.trans_lt xqn).ne <| q0 ▸ (zero_pow hn).symm, le_sup_left.trans_lt xqn, qny⟩

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
/-
**exists_rat_pow_btwn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_pow_btwn {n : Nat} (hn : n != 0) {x y : K} (h : x < y) (hy : 0 
< y) : exists q : Rat, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) ^ n < y
参数：hn : n != 0；h : x < y；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `exists_pow_btwn`：exists_pow_btwn {n : Nat} (hn : n != 0) {x y : K} (h : 
x < y) (hy : 0 < y) : exists q : K, 0 < q ∧ x < q ^ n ∧ q ^ n < y
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a

--- 原说明 ---
There is a rational power between any two positive elements of an archimedean or
dered field.
-/
theorem exists_rat_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : K} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
  refine ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans ?_, hy₂.trans' ?_⟩ <;> assumption_mod_cast
/-
**le_of_forall_rat_lt_imp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_rat_lt_imp_le (h : forall q : Rat, (q : K) < x -> (q : K) <= 
y) : x <= y
参数：h : forall q : Rat, (q : K) < x -> (q : K) <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : K) < x → (q : K) ≤ y) : x ≤ y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_ge <| h _ hx
/-
**le_of_forall_lt_rat_imp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_lt_rat_imp_le (h : forall q : Rat, y < q -> x <= q) : x <= y
参数：h : forall q : Rat, y < q -> x <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_ge <| h _ hy
/-
**le_iff_forall_rat_lt_imp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_rat_lt_imp_le : x <= y ↔ forall q : Rat, (q : K) < x -> (q :
 K) <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_forall_rat_lt_imp_le`：le_of_forall_rat_lt_imp_le (h : forall q : R
at, (q : K) < x -> (q : K) <= y) : x <= y
-/
theorem le_iff_forall_rat_lt_imp_le : x ≤ y ↔ ∀ q : ℚ, (q : K) < x → (q : K) ≤ y :=
  ⟨fun hxy _ hqx ↦ hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩
/-
**le_iff_forall_lt_rat_imp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_lt_rat_imp_le : x <= y ↔ forall q : Rat, y < q -> x <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_forall_lt_rat_imp_le`：le_of_forall_lt_rat_imp_le (h : forall q : R
at, y < q -> x <= q) : x <= y
-/
theorem le_iff_forall_lt_rat_imp_le : x ≤ y ↔ ∀ q : ℚ, y < q → x ≤ q :=
  ⟨fun hxy _ hqx ↦ hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩
/-
**eq_of_forall_rat_lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_rat_lt_iff_lt (h : forall q : Rat, (q : K) < x ↔ (q : K) < y)
 : x = y
参数：h : forall q : Rat, (q : K) < x ↔ (q : K) < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_forall_rat_lt_imp_le`：le_of_forall_rat_lt_imp_le (h : forall q : R
at, (q : K) < x -> (q : K) <= y) : x <= y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : K) < x ↔ (q : K) < y) : x = y :=
  (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le
/-
**eq_of_forall_lt_rat_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_lt_rat_iff_lt (h : forall q : Rat, x < q ↔ y < q) : x = y
参数：h : forall q : Rat, x < q ↔ y < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_forall_lt_rat_imp_le`：le_of_forall_lt_rat_imp_le (h : forall q : R
at, y < q -> x <= q) : x <= y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
  (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le
/-
**exists_pos_rat_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_rat_lt {x : K} (x0 : 0 < x) : exists q : Rat, 0 < q ∧ (q : K) <
 x
参数：x0 : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
-/
theorem exists_pos_rat_lt {x : K} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : K) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0
/-
**exists_rat_near** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_rat_near (x : K) (ε0 : 0 < ε) : exists q : Rat, |x - q| < ε
参数：x : K；ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] (a : α) {b : α}, a - b < a ↔ 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `lt_add_iff_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddRightStrictMono α] [AddRightReflectLT α] (a : α) {b : α},   a < b + a 
↔ 0 < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `abs_sub_lt_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| < c ↔ a - b < c ∧ b - a 
< c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_lt_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] {a b c : α}, a - b < c ↔ a - c < b
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
-/
theorem exists_rat_near (x : K) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
    exists_rat_btwn <| ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end LinearOrderedField

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Archimedean ℕ :=
  ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n, nsmul_eq_mul, Nat.cast_id, mul_one]
    exact Nat.le_mul_of_pos_right n m0⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Archimedean ℤ :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
      le_trans (Int.self_le_toNat _) <| by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.natCast_nonneg n.toNat)⟩⟩
/-
**Nonneg.instArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nonneg.instArchimedean [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMon
oid M] [Archimedean M] : Archimedean { x : M // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
-/
instance Nonneg.instArchimedean [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Archimedean M] :
    Archimedean { x : M // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : M) (hy : (0 : M) < y)
    ⟨n, mod_cast hr⟩⟩
/-
**Nonneg.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nonneg.instMulArchimedean [CommSemiring R] [PartialOrder R] [IsStrictOrder
edRing R] [Archimedean R] [ExistsAddOfLE R] : MulArchimedean { x : R // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
-/
instance Nonneg.instMulArchimedean [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] [ExistsAddOfLE R] :
    MulArchimedean { x : R // 0 ≤ x } :=
  ⟨fun x _ hy ↦ (pow_unbounded_of_one_lt x hy).imp fun _ h ↦ h.le⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Archimedean NNRat := Nonneg.instArchimedean
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulArchimedean NNRat := Nonneg.instMulArchimedean

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
@[instance_reducible]
/-
**Archimedean.floorRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Archimedean.floorRing (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
 [Archimedean R] : FloorRing R
参数：R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear ordered archimedean ring is a floor ring. This is not an `instance` bec
ause in some
cases we have a computable `floor` function.
-/
noncomputable def Archimedean.floorRing (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] : FloorRing R :=
  .ofBounded _ exists_nat_ge

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear ordered field that is a floor ring is archimedean.
-/
instance (priority := 100) FloorRing.archimedean (K) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] :
    Archimedean K := by
  rw [archimedean_iff_int_le]
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩

@[to_additive]
/-
**Units.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimede
an M] : MulArchimedean Mˣ
参数：M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
-/
instance Units.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean Mˣ :=
  ⟨fun x {_} h ↦ MulArchimedean.arch x.val h⟩
/-
**WithBot.instArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithBot.instArchimedean (M) [AddCommMonoid M] [PartialOrder M] [Archimedea
n M] : Archimedean (WithBot M)
参数：M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
-/
instance WithBot.instArchimedean (M) [AddCommMonoid M] [PartialOrder M] [Archimedean M] :
    Archimedean (WithBot M) := by
  constructor
  intro x y hxy
  cases y with
  | bot => exact absurd hxy bot_le.not_gt
  | coe y =>
    cases x with
    | bot => refine ⟨0, bot_le⟩
    | coe x => simpa [← WithBot.coe_nsmul] using (Archimedean.arch x (by simpa using hxy))
/-
**WithZero.instMulArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithZero.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchim
edean M] : MulArchimedean (WithZero M)
参数：M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
-/
instance WithZero.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean (WithZero M) := by
  constructor
  intro x y hxy
  cases y with
  | zero => cases hxy.pos.false
  | coe y =>
    cases x with
    | zero => refine ⟨0, zero_le⟩
    | coe x => simpa [← WithZero.coe_pow] using (MulArchimedean.arch x (by simpa using hxy))
