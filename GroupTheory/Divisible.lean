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
Definition of `DivisibleBy` / `DivisibleBy` 的定义

English:
class DivisibleBy
  parameters: where
  axioms and operations (3):
    - div : A -> α -> A
    - div_zero : forall a, div a 0 = 0
    - div_cancel : forall {n : α} (a : A), n != 0 -> n • div a n = a

中文:
类 DivisibleBy
  参数: where
  公理与运算 (3 个):
    - div : A -> α -> A
    - div_zero : 对任意 a, div a 0 = 0
    - div_cancel : 对任意 {n : α} (a : A), n != 0 -> n • div a n = a
-/
class DivisibleBy where
  /-- The division function -/
  div : A -> α -> A
  div_zero : forall a, div a 0 = 0
  div_cancel : forall {n : α} (a : A), n != 0 -> n • div a n = a

end AddMonoid

section Monoid

variable (A α : Type*) [Monoid A] [Pow A α] [Zero α]

/-- A `Monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive]
/--
Definition of `RootableBy` / `RootableBy` 的定义

English:
class RootableBy
  parameters: where
  axioms and operations (3):
    - root : A -> α -> A
    - root_zero : forall a, root a 0 = 1
    - root_cancel : forall {n : α} (a : A), n != 0 -> root a n ^ n = a

中文:
类 RootableBy
  参数: where
  公理与运算 (3 个):
    - root : A -> α -> A
    - root_zero : 对任意 a, root a 0 = 1
    - root_cancel : 对任意 {n : α} (a : A), n != 0 -> root a n ^ n = a
-/
class RootableBy where
  /-- The root function -/
  root : A -> α -> A
  root_zero : forall a, root a 0 = 1
  root_cancel : forall {n : α} (a : A), n != 0 -> root a n ^ n = a

@[to_additive DivisibleBy.surjective_smul]
/--
theorem `RootableBy.surjective_pow` / 定理 `RootableBy.surjective_pow`

English:
theorem RootableBy.surjective_pow
  given: [RootableBy A α] {n : α} (hn : n != 0)
  proof: fun x =>
  ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

@[deprecated (since := "2026-04-19")] alias pow_left_surj_of_rootableBy :=
  RootableBy.surjective_pow

@[deprecated (since := "2026-04-19")] alias smul_right_surj_of_divisibleBy :=
  DivisibleBy.surjective_smul

中文:
定理 RootableBy.surjective_pow
  条件: [RootableBy A α] {n : α} (hn : n != 0)
  证明: fun x =>
  ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

@[deprecated (since := "2026-04-19")] alias pow_left_surj_of_rootableBy :=
  RootableBy.surjective_pow

@[deprecated (since := "2026-04-19")] alias smul_right_surj_of_divisibleBy :=
  DivisibleBy.surjective_smul
-/
theorem RootableBy.surjective_pow [RootableBy A α] {n : α} (hn : n != 0) :
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
/--
Definition of `rootableByOfPowLeftSurj` / `rootableByOfPowLeftSurj` 的定义

English:
definition rootableByOfPowLeftSurj
  body: @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by exact dif_pos rfl
  root_cancel a hn := by
    dsimp only
    rw [dif_neg hn]
    exact (H hn a).choose_spec

中文:
定义 rootableByOfPowLeftSurj
  定义体: @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by exact dif_pos rfl
  root_cancel a hn := by
    dsimp only
    rw [dif_neg hn]
    exact (H hn a).choose_spec

Depends on / 依赖: Classical, Classical.dec
-/
noncomputable def rootableByOfPowLeftSurj
    (H : forall {n : α}, n != 0 -> Function.Surjective (fun a => a ^ n : A -> A)) : RootableBy A α where
  root a n := @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by exact dif_pos rfl
  root_cancel a hn := by
    dsimp only
    rw [dif_neg hn]
    exact (H hn a).choose_spec

section Pi

variable {ι β : Type*} (B : ι -> Type*) [forall i : ι, Pow (B i) β]
variable [Zero β] [forall i : ι, Monoid (B i)] [forall i, RootableBy (B i) β]

@[to_additive]
/--
Instance `Pi.rootableBy` / 实例 `Pi.rootableBy`

English:
instance Pi.rootableBy
  signature: : RootableBy (forall i, B i) β where
  body: RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

中文:
实例 依赖函数类型.rootableBy
  签名: : RootableBy (对任意 i, B i) β where
  定义体: RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

Depends on / 依赖: RootableBy, RootableBy.root
-/
instance Pi.rootableBy : RootableBy (forall i, B i) β where
  root x n i := RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

end Pi

section Prod

variable {β B B' : Type*} [Pow B β] [Pow B' β]
variable [Zero β] [Monoid B] [Monoid B'] [RootableBy B β] [RootableBy B' β]

@[to_additive]
/--
Instance `Prod.rootableBy` / 实例 `Prod.rootableBy`

English:
instance Prod.rootableBy
  signature: : RootableBy (B × B') β where
  body: (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

中文:
实例 积类型.rootableBy
  签名: : RootableBy (B × B') β where
  定义体: (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

Depends on / 依赖: RootableBy, RootableBy.root
-/
instance Prod.rootableBy : RootableBy (B × B') β where
  root p n := (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

end Prod

section ULift

@[to_additive]
/--
Instance `ULift.instRootableBy` / 实例 `ULift.instRootableBy`

English:
instance ULift.instRootableBy
  signature: [RootableBy A α]
  body: ULift.up RootableBy.root x.down a
root_zero x := ULift.ext _ _ RootableBy.root_zero x.down
root_cancel _ h := ULift.ext _ _ RootableBy.root_cancel _ h

中文:
实例 类型层提升.instRootableBy
  签名: [RootableBy A α]
  定义体: ULift.up RootableBy.root x.down a
root_zero x := ULift.ext _ _ RootableBy.root_zero x.down
root_cancel _ h := ULift.ext _ _ RootableBy.root_cancel _ h

Depends on / 依赖: RootableBy, RootableBy.root, ULift.up, x.down
-/
instance ULift.instRootableBy [RootableBy A α] : RootableBy (ULift A) α where
root x a := ULift.up RootableBy.root x.down a
root_zero x := ULift.ext _ _ RootableBy.root_zero x.down
root_cancel _ h := ULift.ext _ _ RootableBy.root_cancel _ h

end ULift

end Monoid

namespace AddCommGroup

variable (A : Type*) [AddCommGroup A]

/--
theorem `smul_top_eq_top_of_divisibleBy_int` / 定理 `smul_top_eq_top_of_divisibleBy_int`

English:
theorem smul_top_eq_top_of_divisibleBy_int
  given: [DivisibleBy A Int] {n : Int} (hn : n != 0)
  proof: AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

中文:
定理 smul_top_eq_top_of_divisibleBy_int
  条件: [DivisibleBy A 整数] {n : 整数} (hn : n != 0)
  证明: AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.map_top_of_surjective, DivisibleBy, DivisibleBy.div, DivisibleBy.div_cancel, div_cancel, map_top_of_surjective
-/
theorem smul_top_eq_top_of_divisibleBy_int [DivisibleBy A Int] {n : Int} (hn : n != 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

/-- If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
@[instance_reducible]
/--
Definition of `divisibleByIntOfSMulTopEqTop` / `divisibleByIntOfSMulTopEqTop` 的定义

English:
definition divisibleByIntOfSMulTopEqTop
  body: if hn : n = 0 then 0 else (show a in n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dif_pos rfl
  div_cancel a hn := by
    simp_rw [dif_neg hn]
    generalize_proofs h1
    exact h1.choose_spec.2

中文:
定义 divisibleBy整数OfSMulTopEqTop
  定义体: if hn : n = 0 then 0 else (show a in n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dif_pos rfl
  div_cancel a hn := by
    simp_rw [dif_neg hn]
    generalize_proofs h1
    exact h1.choose_spec.2

Depends on / 依赖: AddSubgroup, choose_spec, dif_neg, dif_pos, div_cancel, div_zero, generalize_proofs, h1.choose_spec, simp_rw
-/
noncomputable def divisibleByIntOfSMulTopEqTop
    (H : forall {n : Int} (_hn : n != 0), n • (⊤ : AddSubgroup A) = ⊤) : DivisibleBy A Int where
  div a n :=
    if hn : n = 0 then 0 else (show a in n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dif_pos rfl
  div_cancel a hn := by
    simp_rw [dif_neg hn]
    generalize_proofs h1
    exact h1.choose_spec.2

end AddCommGroup

instance (priority := 100) divisibleByIntOfCharZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    DivisibleBy 𝕜 Int where
  div q n := q / n
  div_zero q := by simp
  div_cancel {n} q hn := by
    rw [zsmul_eq_mul]; rw [(Int.cast_commute n _).eq]; rw [div_mul_cancel₀ q (Int.cast_ne_zero.mpr hn)]

namespace Group

variable (A : Type*) [Group A]

open Int in
/-- A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive (attr := instance_reducible)
  /-- An additive group is `ℤ`-divisible if it is `ℕ`-divisible. -/]
/--
Definition of `rootableByIntOfRootableByNat` / `rootableByIntOfRootableByNat` 的定义

English:
definition rootableByIntOfRootableByNat
  signature: [RootableBy A Nat]
  body: match z with
    | (n : Nat) => RootableBy.root a n
    | -[n+1] => (RootableBy.root a (n + 1))⁻¹
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    cases n
    · rw [Int.ofNat_eq_natCast, Nat.cast_ne_zero] at hn
      simp [RootableBy.root_cancel _ hn]
    · simp [RootableBy.r

中文:
定义 rootableBy整数OfRootableBy自然数
  签名: [RootableBy A 自然数]
  定义体: match z with
    | (n : Nat) => RootableBy.root a n
    | -[n+1] => (RootableBy.root a (n + 1))⁻¹
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    cases n
    · rw [Int.ofNat_eq_natCast, Nat.cast_ne_zero] at hn
      simp [RootableBy.root_cancel _ hn]
    · simp [RootableBy.r

Depends on / 依赖: Int.ofNat_eq_natCast, Nat.add_one_ne_zero, Nat.cast_ne_zero, RootableBy, RootableBy.root, RootableBy.root_cancel, RootableBy.root_zero, add_one_ne_zero, cast_ne_zero, ofNat_eq_natCast, root_cancel, root_zero
-/
def rootableByIntOfRootableByNat [RootableBy A Nat] : RootableBy A Int where
  root a z :=
    match z with
    | (n : Nat) => RootableBy.root a n
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
/--
Definition of `rootableByNatOfRootableByInt` / `rootableByNatOfRootableByInt` 的定义

English:
definition rootableByNatOfRootableByInt
  signature: [RootableBy A Int]
  body: RootableBy.root a (n : Int)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    have := RootableBy.root_cancel a (show (n : Int) != 0 from mod_cast hn)
    simpa

中文:
定义 rootableBy自然数OfRootableBy整数
  签名: [RootableBy A 整数]
  定义体: RootableBy.root a (n : Int)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    have := RootableBy.root_cancel a (show (n : Int) != 0 from mod_cast hn)
    simpa

Depends on / 依赖: RootableBy, RootableBy.root
-/
def rootableByNatOfRootableByInt [RootableBy A Int] : RootableBy A Nat where
  root a n := RootableBy.root a (n : Int)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    have := RootableBy.root_cancel a (show (n : Int) != 0 from mod_cast hn)
    simpa

end Group

section Hom

variable {A B α : Type*}
variable [Zero α] [Monoid A] [Monoid B] [Pow A α] [Pow B α] [RootableBy A α]
variable (f : A -> B)

/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive (attr := instance_reducible)
      /-- If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also
      `α`-divisible. -/]
/--
Definition of `Function.Surjective.rootableBy` / `Function.Surjective.rootableBy` 的定义

English:
definition Function.Surjective.rootableBy
  signature: (hf : Function.Surjective f)
  body: rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
⟨f RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

中文:
定义 函数.满射.rootableBy
  签名: (hf : 函数.满射 f)
  定义体: rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
⟨f RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

Depends on / 依赖: RootableBy, RootableBy.root, RootableBy.root_cancel, root_cancel, rootableByOfPowLeftSurj
-/
noncomputable def Function.Surjective.rootableBy (hf : Function.Surjective f)
    (hpow : forall (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α :=
  rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
⟨f RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

end Hom

section Quotient

variable (α : Type*) {A : Type*} [CommGroup A] (B : Subgroup A)

/-- Any quotient group of a rootable group is rootable. -/
@[to_additive /-- Any quotient group of a divisible group is divisible -/]
/--
Instance `QuotientGroup.rootableBy` / 实例 `QuotientGroup.rootableBy`

English:
instance QuotientGroup.rootableBy
  signature: [RootableBy A Nat]
  body: QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

中文:
实例 商群.rootableBy
  签名: [RootableBy A 自然数]
  定义体: QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

Depends on / 依赖: QuotientGroup, QuotientGroup.mk_surjective.rootableBy, mk_surjective, rootableBy
-/
noncomputable instance QuotientGroup.rootableBy [RootableBy A Nat] : RootableBy (A ⧸ B) Nat :=
  QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

end Quotient
