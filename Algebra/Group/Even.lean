/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Set.Operations

/-!
# Squares and even elements

This file defines square and even elements in a monoid.

## Main declarations

* `IsSquare a` means that there is some `r` such that `a = r * r`
* `Even a` means that there is some `r` such that `a = r + r`

## Note

* Many lemmas about `Even` / `IsSquare`, including important `simp` lemmas,
  are in `Mathlib/Algebra/Ring/Parity.lean`.

## TODO

* Try to generalize `IsSquare/Even` lemmas further. For example, there are still a few lemmas in
  `Algebra.Ring.Parity` whose `Semiring` assumptions I (DT) am not convinced are necessary.
* The "old" definition of `Even a` asked for the existence of an element `c` such that `a = 2 * c`.
  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.

## See also

`Mathlib/Algebra/Ring/Parity.lean` for the definition of odd elements as well as facts about
`Even` / `IsSquare` in rings.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

open MulOpposite

variable {F α β : Type*}

section Mul
variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some root `r : α`. -/
@[to_additive /-- An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
for some `r : α`. -/]
/--
Definition of `IsSquare` / `IsSquare` 的定义

English:
definition IsSquare
  signature: (a : α)
  body: exists r, a = r * r

@[to_additive]

中文:
定义 IsSquare
  签名: (a : α)
  定义体: exists r, a = r * r

@[to_additive]
-/
def IsSquare (a : α) : Prop := exists r, a = r * r

@[to_additive]
/--
lemma `isSquare_iff_exists_mul_self` / 引理 `isSquare_iff_exists_mul_self`

English:
lemma isSquare_iff_exists_mul_self
  given: (a : α)
  statement: IsSquare a ↔ exists r, a = r * r
  proof: .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self

中文:
引理 isSquare_iff_exists_mul_self
  条件: (a : α)
  结论: IsSquare a ↔ 存在 r, a = r * r
  证明: .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
-/
lemma isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ exists r, a = r * r := .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive (attr := aesop unsafe 5% forward)] IsSquare.exists_mul_self

@[to_additive (attr := simp, aesop safe)]
/--
lemma `IsSquare.mul_self` / 引理 `IsSquare.mul_self`

English:
lemma IsSquare.mul_self
  given: (r : α)
  statement: IsSquare (r * r)
  proof: ⟨r, rfl⟩

@[to_additive]

中文:
引理 IsSquare.mul_self
  条件: (r : α)
  结论: IsSquare (r * r)
  证明: ⟨r, rfl⟩

@[to_additive]
-/
lemma IsSquare.mul_self (r : α) : IsSquare (r * r) := ⟨r, rfl⟩

@[to_additive]
/--
lemma `isSquare_op_iff` / 引理 `isSquare_op_iff`

English:
lemma isSquare_op_iff
  given: {a : α}
  statement: IsSquare (op a) ↔ IsSquare a
  proof: ⟨fun ⟨r, hr⟩ => ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ => ⟨op r, congr_arg op hr⟩⟩

@[to_additive]

中文:
引理 isSquare_op_iff
  条件: {a : α}
  结论: IsSquare (op a) ↔ IsSquare a
  证明: ⟨fun ⟨r, hr⟩ => ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ => ⟨op r, congr_arg op hr⟩⟩

@[to_additive]

Depends on / 依赖: congr_arg, e.symm
-/
lemma isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨r, hr⟩ => ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ => ⟨op r, congr_arg op hr⟩⟩

@[to_additive]
/--
lemma `isSquare_unop_iff` / 引理 `isSquare_unop_iff`

English:
lemma isSquare_unop_iff
  given: {a : αᵐᵒᵖ}
  statement: IsSquare (unop a) ↔ IsSquare a
  proof: isSquare_op_iff.symm

@[to_additive]

中文:
引理 isSquare_unop_iff
  条件: {a : αᵐᵒᵖ}
  结论: IsSquare (unop a) ↔ IsSquare a
  证明: isSquare_op_iff.symm

@[to_additive]

Depends on / 依赖: isSquare_op_iff, isSquare_op_iff.symm
-/
lemma isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a := isSquare_op_iff.symm

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidablePred
  signature: (IsSquare : α -> Prop)] : DecidablePred (IsSquare
  body: fun _ => decidable_of_iff _ isSquare_unop_iff

@[simp]

中文:
实例 [DecidablePred
  签名: (IsSquare : α -> 命题)] : DecidablePred (IsSquare
  定义体: fun _ => decidable_of_iff _ isSquare_unop_iff

@[simp]

Depends on / 依赖: decidable_of_iff, isSquare_unop_iff
-/
instance [DecidablePred (IsSquare : α -> Prop)] : DecidablePred (IsSquare : αᵐᵒᵖ -> Prop) :=
  fun _ => decidable_of_iff _ isSquare_unop_iff

@[simp]
/--
lemma `even_ofMul_iff` / 引理 `even_ofMul_iff`

English:
lemma even_ofMul_iff
  given: {a : α}
  statement: Even (Additive.ofMul a) ↔ IsSquare a
  proof: Iff.rfl

@[simp]

中文:
引理 even_ofMul_iff
  条件: {a : α}
  结论: Even (Additive.ofMul a) ↔ IsSquare a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a := Iff.rfl

@[simp]
/--
lemma `isSquare_toMul_iff` / 引理 `isSquare_toMul_iff`

English:
lemma isSquare_toMul_iff
  given: {a : Additive α}
  statement: IsSquare (a.toMul) ↔ Even a
  proof: Iff.rfl

中文:
引理 isSquare_toMul_iff
  条件: {a : Additive α}
  结论: IsSquare (a.toMul) ↔ Even a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isSquare_toMul_iff {a : Additive α} : IsSquare (a.toMul) ↔ Even a := Iff.rfl

/--
Instance `Additive.instDecidablePredEven` / 实例 `Additive.instDecidablePredEven`

English:
instance Additive.instDecidablePredEven
  signature: [DecidablePred (IsSquare : α -> Prop)]
  body: fun _ => decidable_of_iff _ isSquare_toMul_iff

中文:
实例 Additive.instDecidablePredEven
  签名: [DecidablePred (IsSquare : α -> 命题)]
  定义体: fun _ => decidable_of_iff _ isSquare_toMul_iff

Depends on / 依赖: decidable_of_iff, isSquare_toMul_iff
-/
instance Additive.instDecidablePredEven [DecidablePred (IsSquare : α -> Prop)] :
    DecidablePred (Even : Additive α -> Prop) :=
  fun _ => decidable_of_iff _ isSquare_toMul_iff

end Mul

section Add
variable [Add α]

/--
lemma `isSquare_ofAdd_iff` / 引理 `isSquare_ofAdd_iff`

English:
lemma isSquare_ofAdd_iff
  given: {a : α}
  statement: IsSquare (Multiplicative.ofAdd a) ↔ Even a
  proof: Iff.rfl

@[simp]

中文:
引理 isSquare_ofAdd_iff
  条件: {a : α}
  结论: IsSquare (Multiplicative.ofAdd a) ↔ Even a
  证明: Iff.rfl

@[simp]
-/
@[simp] lemma isSquare_ofAdd_iff {a : α} : IsSquare (Multiplicative.ofAdd a) ↔ Even a := Iff.rfl

@[simp]
/--
lemma `even_toAdd_iff` / 引理 `even_toAdd_iff`

English:
lemma even_toAdd_iff
  given: {a : Multiplicative α}
  statement: Even a.toAdd ↔ IsSquare a
  proof: Iff.rfl

中文:
引理 even_toAdd_iff
  条件: {a : Multiplicative α}
  结论: Even a.toAdd ↔ IsSquare a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ IsSquare a := Iff.rfl

/--
Instance `Multiplicative.instDecidablePredIsSquare` / 实例 `Multiplicative.instDecidablePredIsSquare`

English:
instance Multiplicative.instDecidablePredIsSquare
  signature: [DecidablePred (Even : α -> Prop)]
  body: fun _ => decidable_of_iff _ even_toAdd_iff

中文:
实例 Multiplicative.instDecidablePredIsSquare
  签名: [DecidablePred (Even : α -> 命题)]
  定义体: fun _ => decidable_of_iff _ even_toAdd_iff

Depends on / 依赖: decidable_of_iff, even_toAdd_iff
-/
instance Multiplicative.instDecidablePredIsSquare [DecidablePred (Even : α -> Prop)] :
    DecidablePred (IsSquare : Multiplicative α -> Prop) :=
  fun _ => decidable_of_iff _ even_toAdd_iff

end Add

@[to_additive (attr := simp)]
/--
lemma `IsSquare.one` / 引理 `IsSquare.one`

English:
lemma IsSquare.one
  given: [MulOneClass α]
  statement: IsSquare (1 : α)
  proof: ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

中文:
引理 IsSquare.one
  条件: [MulOneClass α]
  结论: IsSquare (1 : α)
  证明: ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

Depends on / 依赖: mul_one
-/
lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

section MonoidHom
variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive (attr := aesop unsafe 90%)]
/--
lemma `IsSquare.map` / 引理 `IsSquare.map`

English:
lemma IsSquare.map
  given: {a : α} (f : F)
  statement: IsSquare a -> IsSquare (f a)
  proof: fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

@[to_additive]

中文:
引理 IsSquare.map
  条件: {a : α} (f : F)
  结论: IsSquare a -> IsSquare (f a)
  证明: fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

@[to_additive]
-/
lemma IsSquare.map {a : α} (f : F) : IsSquare a -> IsSquare (f a) :=
  fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

@[to_additive]
/--
lemma `isSquare_subset_image_isSquare` / 引理 `isSquare_subset_image_isSquare`

English:
lemma isSquare_subset_image_isSquare
  given: {f : F} (hf : Function.Surjective f)
  proof: fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

中文:
引理 isSquare_subset_image_isSquare
  条件: {f : F} (hf : Function.Surjective f)
  证明: fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩
-/
lemma isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) :
    {b | IsSquare b} subseteq f '' {a | IsSquare a} := fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

end MonoidHom

section Monoid
variable [Monoid α] {n : Nat} {a : α}

@[to_additive even_iff_exists_two_nsmul]
/--
lemma `isSquare_iff_exists_sq` / 引理 `isSquare_iff_exists_sq`

English:
lemma isSquare_iff_exists_sq
  given: (a : α)
  statement: IsSquare a ↔ exists r, a = r ^ 2
  proof: by simp [IsSquare, pow_two]

@[to_additive Even.exists_two_nsmul
  /-- Alias of the forwards direction of `even_iff_exists_two_nsmul`. -/]
alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq

中文:
引理 isSquare_iff_exists_sq
  条件: (a : α)
  结论: IsSquare a ↔ 存在 r, a = r ^ 2
  证明: by simp [IsSquare, pow_two]

@[to_additive Even.exists_two_nsmul
  /-- Alias of the forwards direction of `even_iff_exists_two_nsmul`. -/]
alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq

Depends on / 依赖: IsSquare, pow_two
-/
lemma isSquare_iff_exists_sq (a : α) : IsSquare a ↔ exists r, a = r ^ 2 := by simp [IsSquare, pow_two]

@[to_additive Even.exists_two_nsmul
  /-- Alias of the forwards direction of `even_iff_exists_two_nsmul`. -/]
alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq

-- provable by simp in `Algebra.Ring.Parity`
@[to_additive (attr := aesop safe) Even.two_nsmul]
/--
lemma `IsSquare.sq` / 引理 `IsSquare.sq`

English:
lemma IsSquare.sq
  given: (r : α)
  statement: IsSquare (r ^ 2)
  proof: ⟨r, pow_two _⟩

@[to_additive (attr := aesop unsafe 80%) Even.nsmul_right]

中文:
引理 IsSquare.sq
  条件: (r : α)
  结论: IsSquare (r ^ 2)
  证明: ⟨r, pow_two _⟩

@[to_additive (attr := aesop unsafe 80%) Even.nsmul_right]

Depends on / 依赖: pow_two
-/
lemma IsSquare.sq (r : α) : IsSquare (r ^ 2) := ⟨r, pow_two _⟩

@[to_additive (attr := aesop unsafe 80%) Even.nsmul_right]
/--
lemma `IsSquare.pow` / 引理 `IsSquare.pow`

English:
lemma IsSquare.pow
  given: (n : Nat) (ha : IsSquare a)
  statement: IsSquare (a ^ n)
  proof: by
  aesop (add simp Commute.mul_pow)

@[to_additive (attr := aesop unsafe 90%) Even.nsmul_left]

中文:
引理 IsSquare.pow
  条件: (n : 自然数) (ha : IsSquare a)
  结论: IsSquare (a ^ n)
  证明: by
  aesop (add simp Commute.mul_pow)

@[to_additive (attr := aesop unsafe 90%) Even.nsmul_left]

Depends on / 依赖: Commute, Commute.mul_pow, mul_pow
-/
lemma IsSquare.pow (n : Nat) (ha : IsSquare a) : IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_pow)

@[to_additive (attr := aesop unsafe 90%) Even.nsmul_left]
/--
lemma `Even.isSquare_pow` / 引理 `Even.isSquare_pow`

English:
lemma Even.isSquare_pow
  given: (hn : Even n)
  statement: forall a : α, IsSquare (a ^ n)
  proof: by aesop (add simp pow_add)

中文:
引理 Even.isSquare_pow
  条件: (hn : Even n)
  结论: 对任意 a : α, IsSquare (a ^ n)
  证明: by aesop (add simp pow_add)

Depends on / 依赖: pow_add
-/
lemma Even.isSquare_pow (hn : Even n) : forall a : α, IsSquare (a ^ n) := by aesop (add simp pow_add)

end Monoid

@[to_additive (attr := aesop unsafe 90%)]
/--
lemma `IsSquare.mul` / 引理 `IsSquare.mul`

English:
lemma IsSquare.mul
  given: [CommSemigroup α] {a b : α}
  statement: IsSquare a -> IsSquare b -> IsSquare (a * b)
  proof: fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

中文:
引理 IsSquare.mul
  条件: [CommSemigroup α] {a b : α}
  结论: IsSquare a -> IsSquare b -> IsSquare (a * b)
  证明: fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

Depends on / 依赖: mul_mul_mul_comm
-/
lemma IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a -> IsSquare b -> IsSquare (a * b) :=
  fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

section DivisionMonoid
variable [DivisionMonoid α] {a : α}

/--
lemma `isSquare_inv` / 引理 `isSquare_inv`

English:
lemma isSquare_inv
  statement: IsSquare a⁻¹ ↔ IsSquare a
  proof: by
  constructor <;> intro h <;> simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

@[to_additive] alias ⟨_, IsSquare.inv⟩ := isSquare_inv

@[to_additive (attr := aesop unsafe 80%) Even.zsmul_right]

中文:
引理 isSquare_inv
  结论: IsSquare a⁻¹ ↔ IsSquare a
  证明: by
  constructor <;> intro h <;> simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

@[to_additive] alias ⟨_, IsSquare.inv⟩ := isSquare_inv

@[to_additive (attr := aesop unsafe 80%) Even.zsmul_right]
-/
@[to_additive (attr := simp)] lemma isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  constructor <;> intro h <;> simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

@[to_additive] alias ⟨_, IsSquare.inv⟩ := isSquare_inv

@[to_additive (attr := aesop unsafe 80%) Even.zsmul_right]
/--
lemma `IsSquare.zpow` / 引理 `IsSquare.zpow`

English:
lemma IsSquare.zpow
  given: (n : Int)
  statement: IsSquare a -> IsSquare (a ^ n)
  proof: by
  aesop (add simp Commute.mul_zpow)

中文:
引理 IsSquare.zpow
  条件: (n : 整数)
  结论: IsSquare a -> IsSquare (a ^ n)
  证明: by
  aesop (add simp Commute.mul_zpow)

Depends on / 依赖: Commute, Commute.mul_zpow, mul_zpow
-/
lemma IsSquare.zpow (n : Int) : IsSquare a -> IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_zpow)

end DivisionMonoid

@[to_additive (attr := aesop unsafe 90%)]
/--
lemma `IsSquare.div` / 引理 `IsSquare.div`

English:
lemma IsSquare.div
  given: [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b)
  proof: by aesop (add simp div_eq_mul_inv)

@[to_additive (attr := simp, aesop unsafe 90%) Even.zsmul_left]

中文:
引理 IsSquare.div
  条件: [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b)
  证明: by aesop (add simp div_eq_mul_inv)

@[to_additive (attr := simp, aesop unsafe 90%) Even.zsmul_left]

Depends on / 依赖: div_eq_mul_inv
-/
lemma IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by aesop (add simp div_eq_mul_inv)

@[to_additive (attr := simp, aesop unsafe 90%) Even.zsmul_left]
/--
lemma `Even.isSquare_zpow` / 引理 `Even.isSquare_zpow`

English:
lemma Even.isSquare_zpow
  given: [Group α] {n : Int}
  statement: Even n -> forall a : α, IsSquare (a ^ n)
  proof: by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : Nat} {k : Int} (hk : Even k) :
IsSquare a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : Nat} {k : Int} (hk : E

中文:
引理 Even.isSquare_zpow
  条件: [Group α] {n : 整数}
  结论: Even n -> 对任意 a : α, IsSquare (a ^ n)
  证明: by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : Nat} {k : Int} (hk : Even k) :
IsSquare a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : Nat} {k : Int} (hk : E

Depends on / 依赖: zpow_add
-/
lemma Even.isSquare_zpow [Group α] {n : Int} : Even n -> forall a : α, IsSquare (a ^ n) := by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : Nat} {k : Int} (hk : Even k) :
IsSquare a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : Nat} {k : Int} (hk : Even k) :
Even a + (b + b) - 2 • c + k • d + (n + n) • e := by aesop
