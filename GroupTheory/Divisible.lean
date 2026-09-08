/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Algebra.Field.Defs

/-!
# Divisible Group and rootable group

In this file, we define a divisible additive monoid and a rootable monoid with some basic
properties.

## Main definition

* `DivisibleBy A α`: An additive monoid `A` is said to be divisible by `α` iff for all `n ≠ 0 ∈ α`
  and `y ∈ A`, there is an `x ∈ A` such that `n • x = y`. In this file, we adopt a constructive
  approach, i.e. we ask for an explicit `div : A → α → A` function such that `div a 0 = 0` and
  `n • div a n = a` for all `n ≠ 0 ∈ α`.
* `RootableBy A α`: A monoid `A` is said to be rootable by `α` iff for all `n ≠ 0 ∈ α` and `y ∈ A`,
  there is an `x ∈ A` such that `x^n = y`. In this file, we adopt a constructive approach, i.e. we
  ask for an explicit `root : A → α → A` function such that `root a 0 = 1` and `(root a n)ⁿ = a` for
  all `n ≠ 0 ∈ α`.

## Main results

For additive monoids and groups:

* `divisibleByOfSMulRightSurj` : the constructive definition of divisibility is implied by
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `smul_right_surj_of_divisibleBy` : the constructive definition of divisibility implies
  the condition that `n • x = a` has solutions for all `n ≠ 0` and `a ∈ A`.
* `Prod.divisibleBy` : `A × B` is divisible for any two divisible additive monoids.
* `Pi.divisibleBy` : any product of divisible additive monoids is divisible.
* `AddGroup.divisibleByIntOfDivisibleByNat` : for additive groups, int divisibility is implied
  by nat divisibility.
* `AddGroup.divisibleByNatOfDivisibleByInt` : for additive groups, nat divisibility is implied
  by int divisibility.
* `AddCommGroup.divisibleByIntOfSMulTopEqTop`: the constructive definition of divisibility
  is implied by the condition that `n • A = A` for all `n ≠ 0`.
* `AddCommGroup.smul_top_eq_top_of_divisibleBy_int`: the constructive definition of divisibility
  implies the condition that `n • A = A` for all `n ≠ 0`.
* `divisibleByIntOfCharZero` : any field of characteristic zero is divisible.
* `QuotientAddGroup.divisibleBy` : quotient group of divisible group is divisible.
* `Function.Surjective.divisibleBy` : if `A` is divisible and `A →+ B` is surjective, then `B`
  is divisible.

and their multiplicative counterparts:

* `rootableByOfPowLeftSurj` : the constructive definition of rootability is implied by the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `pow_left_surj_of_rootableBy` : the constructive definition of rootability implies the
  condition that `xⁿ = y` has solutions for all `n ≠ 0` and `a ∈ A`.
* `Prod.rootableBy` : any product of two rootable monoids is rootable.
* `Pi.rootableBy` : any product of rootable monoids is rootable.
* `Group.rootableByIntOfRootableByNat` : in groups, int rootability is implied by nat
  rootability.
* `Group.rootableByNatOfRootableByInt` : in groups, nat rootability is implied by int
  rootability.
* `QuotientGroup.rootableBy` : quotient group of rootable group is rootable.
* `Function.Surjective.rootableBy` : if `A` is rootable and `A →* B` is surjective, then `B` is
  rootable.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.
-/

@[expose] public section


open scoped Pointwise

section AddMonoid

variable (A α : Type*) [AddMonoid A] [SMul α A] [Zero α]

/--
An `AddMonoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
/-
**DivisibleBy** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → (α : Type u_2) → [AddMonoid A] → [SMul α A] → [Zero α] → 
Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddMonoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 
∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A`
 function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class DivisibleBy where
  /-- The division function -/
  div : A → α → A
  div_zero : ∀ a, div a 0 = 0
  div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • div a n = a

end AddMonoid

section Monoid

variable (A α : Type*) [Monoid A] [Pow A α] [Zero α]

/-- A `Monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive]
/-
**RootableBy** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → (α : Type u_2) → [Monoid A] → [Pow A α] → [Zero α] → Type
 (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and
 `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A
` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class RootableBy where
  /-- The root function -/
  root : A → α → A
  root_zero : ∀ a, root a 0 = 1
  root_cancel : ∀ {n : α} (a : A), n ≠ 0 → root a n ^ n = a

@[to_additive DivisibleBy.surjective_smul]
/-
**RootableBy.surjective_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RootableBy.surjective_pow [RootableBy A α] {n : α} (hn : n != 0) : Functio
n.Surjective fun a : A => a ^ n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootableBy.root_cancel`：∀ {A : Type u_1} {α : Type u_2} {inst : Monoid A
} {inst_1 : Pow A α} {inst_2 : Zero α} [self : RootableBy A α] {n : α}   (a : A)
, n ≠ 0 → Ro…
-/
theorem RootableBy.surjective_pow [RootableBy A α] {n : α} (hn : n ≠ 0) :
    Function.Surjective fun a : A => a ^ n := fun x =>
  ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

@[deprecated (since := "2026-04-19")] alias pow_left_surj_of_rootableBy :=
  RootableBy.surjective_pow

@[deprecated (since := "2026-04-19")] alias smul_right_surj_of_divisibleBy :=
  DivisibleBy.surjective_smul

/--
A `Monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructive version
implies the textbook approach.
-/
@[to_additive (attr := instance_reducible) divisibleByOfSMulRightSurj
  /-- An `AddMonoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the
  constructive version implies the textbook approach. -/]
/-
**rootableByOfPowLeftSurj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootableByOfPowLeftSurj (H : forall {n : α}, n != 0 -> Function.Surjective
 (fun a => a ^ n : A -> A)) : RootableBy A α where root a n
参数：H : forall {n : α}, n != 0 -> Function.Surjective (fun a => a ^ n : A -> A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def rootableByOfPowLeftSurj
    (H : ∀ {n : α}, n ≠ 0 → Function.Surjective (fun a => a ^ n : A → A)) : RootableBy A α where
  root a n := @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by exact dif_pos rfl
  root_cancel a hn := by
    dsimp only
    rw [dif_neg hn]
    exact (H hn a).choose_spec

section Pi

variable {ι β : Type*} (B : ι → Type*) [∀ i : ι, Pow (B i) β]
variable [Zero β] [∀ i : ι, Monoid (B i)] [∀ i, RootableBy (B i) β]

@[to_additive]
/-
**Pi.rootableBy** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.rootableBy : RootableBy (forall i, B i) β where root x n i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.rootableBy : RootableBy (∀ i, B i) β where
  root x n i := RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

end Pi

section Prod

variable {β B B' : Type*} [Pow B β] [Pow B' β]
variable [Zero β] [Monoid B] [Monoid B'] [RootableBy B β] [RootableBy B' β]

@[to_additive]
/-
**Prod.rootableBy** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.rootableBy : RootableBy (B × B') β where root p n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.rootableBy : RootableBy (B × B') β where
  root p n := (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

end Prod

section ULift

@[to_additive]
/-
**ULift.instRootableBy** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instRootableBy [RootableBy A α] : RootableBy (ULift A) α where root 
x a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.instRootableBy [RootableBy A α] : RootableBy (ULift A) α where
  root x a := ULift.up <| RootableBy.root x.down a
  root_zero x := ULift.ext _ _ <| RootableBy.root_zero x.down
  root_cancel _ h := ULift.ext _ _ <| RootableBy.root_cancel _ h

end ULift

end Monoid

namespace AddCommGroup

variable (A : Type*) [AddCommGroup A]

/-
**AddCommGroup.smul_top_eq_top_of_divisibleBy_int** 是 Mathlib 中的一个定理，位于命名空间 `Add
CommGroup`。
形式化陈述：smul_top_eq_top_of_divisibleBy_int [DivisibleBy A Int] {n : Int} (hn : n !
= 0) : n • (⊤ : AddSubgroup A) = ⊤
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.map_top_of_surjective`：∀ {G : Type u_1} [inst : AddGroup G] 
{N : Type u_5} [inst_1 : AddGroup N] (f : G →+ N),   Function.Surjective ⇑f → Ad
dSubgroup.map f ⊤ = ⊤
· 使用定理 `DivisibleBy.div_cancel`：∀ {A : Type u_1} {α : Type u_2} {inst : AddMonoi
d A} {inst_1 : SMul α A} {inst_2 : Zero α} [self : DivisibleBy A α]   {n : α} (a
 : A), n ≠ 0…
-/
theorem smul_top_eq_top_of_divisibleBy_int [DivisibleBy A ℤ] {n : ℤ} (hn : n ≠ 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

/-- If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
@[instance_reducible]
/-
**AddCommGroup.divisibleByIntOfSMulTopEqTop** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGr
oup`。
形式化陈述：divisibleByIntOfSMulTopEqTop (H : forall {n : Int} (_hn : n != 0), n • (⊤ 
: AddSubgroup A) = ⊤) : DivisibleBy A Int where div a n
参数：H : forall {n : Int} (_hn : n != 0), n • (⊤ : AddSubgroup A) = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
noncomputable def divisibleByIntOfSMulTopEqTop
    (H : ∀ {n : ℤ} (_hn : n ≠ 0), n • (⊤ : AddSubgroup A) = ⊤) : DivisibleBy A ℤ where
  div a n :=
    if hn : n = 0 then 0 else (show a ∈ n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dif_pos rfl
  div_cancel a hn := by
    simp_rw [dif_neg hn]
    generalize_proofs h1
    exact h1.choose_spec.2

end AddCommGroup

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) divisibleByIntOfCharZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    DivisibleBy 𝕜 ℤ where
  div q n := q / n
  div_zero q := by simp
  div_cancel {n} q hn := by
    rw [zsmul_eq_mul, (Int.cast_commute n _).eq, div_mul_cancel₀ q (Int.cast_ne_zero.mpr hn)]

namespace Group

variable (A : Type*) [Group A]

open Int in
/-- A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive (attr := instance_reducible)
  /-- An additive group is `ℤ`-divisible if it is `ℕ`-divisible. -/]
/-
**Group.rootableByIntOfRootableByNat** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：rootableByIntOfRootableByNat [RootableBy A Nat] : RootableBy A Int where r
oot a z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rootableByIntOfRootableByNat [RootableBy A ℕ] : RootableBy A ℤ where
  root a z :=
    match z with
    | (n : ℕ) => RootableBy.root a n
    | -[n+1] => (RootableBy.root a (n + 1))⁻¹
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    cases n
    · rw [Int.ofNat_eq_natCast, Nat.cast_ne_zero] at hn
      simp [RootableBy.root_cancel _ hn]
    · simp [RootableBy.root_cancel _ (Nat.add_one_ne_zero _)]

/-- A group is `ℕ`-rootable if it is `ℤ`-rootable
-/
@[to_additive (attr := instance_reducible)
  /-- An additive group is `ℕ`-divisible if it `ℤ`-divisible. -/]
/-
**Group.rootableByNatOfRootableByInt** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：rootableByNatOfRootableByInt [RootableBy A Int] : RootableBy A Nat where r
oot a n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rootableByNatOfRootableByInt [RootableBy A ℤ] : RootableBy A ℕ where
  root a n := RootableBy.root a (n : ℤ)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    have := RootableBy.root_cancel a (show (n : ℤ) ≠ 0 from mod_cast hn)
    simpa

end Group

section Hom

variable {A B α : Type*}
variable [Zero α] [Monoid A] [Monoid B] [Pow A α] [Pow B α] [RootableBy A α]
variable (f : A → B)

/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive (attr := instance_reducible)
      /-- If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also
      `α`-divisible. -/]
/-
**Function.Surjective.rootableBy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Surjective.rootableBy (hf : Function.Surjective f) (hpow : forall
 (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α
参数：hf : Function.Surjective f；hpow : forall (a : A) (n : α), f (a ^ n) = f a ^ n
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Function.Surjective.rootableBy (hf : Function.Surjective f)
    (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α :=
  rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
    ⟨f <| RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

end Hom

section Quotient

variable (α : Type*) {A : Type*} [CommGroup A] (B : Subgroup A)

/-- Any quotient group of a rootable group is rootable. -/
@[to_additive /-- Any quotient group of a divisible group is divisible -/]
/-
**QuotientGroup.rootableBy** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.rootableBy [RootableBy A Nat] : RootableBy (A ⧸ B) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any quotient group of a rootable group is rootable.
-/
noncomputable instance QuotientGroup.rootableBy [RootableBy A ℕ] : RootableBy (A ⧸ B) ℕ :=
  QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

end Quotient

