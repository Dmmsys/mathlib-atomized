/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Conjugacy of group elements

See also `MulAut.conj` and `Quandle.conj`.
-/

@[expose] public section

assert_not_exists MonoidWithZero Multiset MulAction

universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
@[to_additive /-- We say that `a` is additively conjugate to `b` if for some additive unit `c` we
have `c + a + -c = b`. -/]
/--
Definition of `IsConj` / `IsConj` 的定义

English:
definition IsConj
  signature: (a b : α)
  body: exists c : αˣ, SemiconjBy (↑c) a b

@[to_additive (attr := refl)]

中文:
定义 IsConj
  签名: (a b : α)
  定义体: exists c : αˣ, SemiconjBy (↑c) a b

@[to_additive (attr := refl)]

Depends on / 依赖: SemiconjBy
-/
def IsConj (a b : α) :=
  exists c : αˣ, SemiconjBy (↑c) a b

@[to_additive (attr := refl)]
/--
theorem `IsConj.refl` / 定理 `IsConj.refl`

English:
theorem IsConj.refl
  given: (a : α)
  statement: IsConj a a
  proof: ⟨1, SemiconjBy.one_left a⟩

@[to_additive (attr := symm)]

中文:
定理 IsConj.refl
  条件: (a : α)
  结论: IsConj a a
  证明: ⟨1, SemiconjBy.one_left a⟩

@[to_additive (attr := symm)]

Depends on / 依赖: SemiconjBy, SemiconjBy.one_left, one_left
-/
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩

@[to_additive (attr := symm)]
/--
theorem `IsConj.symm` / 定理 `IsConj.symm`

English:
theorem IsConj.symm
  given: {a b : α}
  statement: IsConj a b -> IsConj b a

中文:
定理 IsConj.symm
  条件: {a b : α}
  结论: IsConj a b -> IsConj b a
-/
theorem IsConj.symm {a b : α} : IsConj a b -> IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩

@[to_additive]
/--
theorem `isConj_comm` / 定理 `isConj_comm`

English:
theorem isConj_comm
  given: {g h : α}
  statement: IsConj g h ↔ IsConj h g
  proof: ⟨IsConj.symm, IsConj.symm⟩

@[to_additive (attr := trans)]

中文:
定理 isConj_comm
  条件: {g h : α}
  结论: IsConj g h ↔ IsConj h g
  证明: ⟨IsConj.symm, IsConj.symm⟩

@[to_additive (attr := trans)]

Depends on / 依赖: IsConj, IsConj.symm
-/
theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩

@[to_additive (attr := trans)]
/--
theorem `IsConj.trans` / 定理 `IsConj.trans`

English:
theorem IsConj.trans
  given: {a b c : α}
  statement: IsConj a b -> IsConj b c -> IsConj a c

中文:
定理 IsConj.trans
  条件: {a b c : α}
  结论: IsConj a b -> IsConj b c -> IsConj a c
-/
theorem IsConj.trans {a b c : α} : IsConj a b -> IsConj b c -> IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[to_additive]
/--
theorem `IsConj.pow` / 定理 `IsConj.pow`

English:
theorem IsConj.pow
  given: {a b : α} (n : Nat)
  statement: IsConj a b -> IsConj (a ^ n) (b ^ n)

中文:
定理 IsConj.pow
  条件: {a b : α} (n : 自然数)
  结论: IsConj a b -> IsConj (a ^ n) (b ^ n)
-/
theorem IsConj.pow {a b : α} (n : Nat) : IsConj a b -> IsConj (a ^ n) (b ^ n)
  | ⟨c, hc⟩ => ⟨c, hc.pow_right n⟩

@[to_additive (attr := simp)]
/--
theorem `isConj_iff_eq` / 定理 `isConj_iff_eq`

English:
theorem isConj_iff_eq
  given: {α : Type*} [CommMonoid α] {a b : α}
  statement: IsConj a b ↔ a = b
  proof: ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy]; rw [mul_comm]; rw [← Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [c.mul_inv]; rw [mul_one] at hc
    exact hc, fun h => by rw [h]⟩

@[to_additive]

中文:
定理 isConj_iff_eq
  条件: {α : 类型} [交换幺半群 α] {a b : α}
  结论: IsConj a b ↔ a = b
  证明: ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy]; rw [mul_comm]; rw [← Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [c.mul_inv]; rw [mul_one] at hc
    exact hc, fun h => by rw [h]⟩

@[to_additive]

Depends on / 依赖: SemiconjBy, Units.mul_inv_eq_iff_eq_mul, c.mul_inv, mul_assoc, mul_comm, mul_inv, mul_inv_eq_iff_eq_mul, mul_one
-/
theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy]; rw [mul_comm]; rw [← Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [c.mul_inv]; rw [mul_one] at hc
    exact hc, fun h => by rw [h]⟩

@[to_additive]
/--
theorem `MonoidHom.map_isConj` / 定理 `MonoidHom.map_isConj`

English:
theorem MonoidHom.map_isConj
  given: (f : α ->* β) {a b : α}
  statement: IsConj a b -> IsConj (f a) (f b)

中文:
定理 幺半群态射.map_isConj
  条件: (f : α ->* β) {a b : α}
  结论: IsConj a b -> IsConj (f a) (f b)
-/
protected theorem MonoidHom.map_isConj (f : α ->* β) {a b : α} : IsConj a b -> IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩

@[to_additive (attr := simp)]
/--
theorem `isConj_one_right` / 定理 `isConj_one_right`

English:
theorem isConj_one_right
  given: {a : α}
  statement: IsConj 1 a ↔ a = 1
  proof: by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy]; rw [mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

@[to_additive (attr := simp)]

中文:
定理 isConj_one_right
  条件: {a : α}
  结论: IsConj 1 a ↔ a = 1
  证明: by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy]; rw [mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, c.isUnit.mul_eq_right.mp, h.symm, isUnit, mul_eq_right, mul_one
-/
theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 := by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy]; rw [mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

@[to_additive (attr := simp)]
/--
theorem `isConj_one_left` / 定理 `isConj_one_left`

English:
theorem isConj_one_left
  given: {a : α}
  statement: IsConj a 1 ↔ a = 1
  proof: calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

中文:
定理 isConj_one_left
  条件: {a : α}
  结论: IsConj a 1 ↔ a = 1
  证明: calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

Depends on / 依赖: IsConj, IsConj.symm, isConj_one_right
-/
theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

end Monoid

section Group

variable [Group α]

@[to_additive (attr := simp)]
/--
theorem `isConj_iff` / 定理 `isConj_iff`

English:
theorem isConj_iff
  given: {a b : α}
  statement: IsConj a b ↔ exists c : α, c * a * c⁻¹ = b
  proof: ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[to_additive]

中文:
定理 isConj_iff
  条件: {a b : α}
  结论: IsConj a b ↔ 存在 c : α, c * a * c⁻¹ = b
  证明: ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel, mul_inv_eq_iff_eq_mul
-/
theorem isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[to_additive]
/--
theorem `conj_inv` / 定理 `conj_inv`

English:
theorem conj_inv
  given: {a b : α}
  statement: (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹
  proof: by
  simp [mul_assoc]

@[to_additive (attr := simp)]

中文:
定理 conj_inv
  条件: {a b : α}
  结论: (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹
  证明: by
  simp [mul_assoc]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc
-/
theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ := by
  simp [mul_assoc]

@[to_additive (attr := simp)]
/--
theorem `conj_mul` / 定理 `conj_mul`

English:
theorem conj_mul
  given: {a b c : α}
  statement: b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹
  proof: by
  simp [mul_assoc]

@[to_additive (attr := simp)]

中文:
定理 conj_mul
  条件: {a b c : α}
  结论: b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹
  证明: by
  simp [mul_assoc]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc
-/
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by
  simp [mul_assoc]

@[to_additive (attr := simp)]
/--
theorem `conj_pow` / 定理 `conj_pow`

English:
theorem conj_pow
  given: {i : Nat} {a b : α}
  statement: (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
  proof: by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

@[to_additive (attr := simp)]

中文:
定理 conj_pow
  条件: {i : 自然数} {a b : α}
  结论: (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
  证明: by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

@[to_additive (attr := simp)]

Depends on / 依赖: pow_succ
-/
theorem conj_pow {i : Nat} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

@[to_additive (attr := simp)]
/--
theorem `conj_zpow` / 定理 `conj_zpow`

English:
theorem conj_zpow
  given: {i : Int} {a b : α}
  statement: (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
  proof: by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

@[to_additive]

中文:
定理 conj_zpow
  条件: {i : 整数} {a b : α}
  结论: (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
  证明: by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

@[to_additive]

Depends on / 依赖: conj_pow, inv_inv, mul_assoc, mul_inv_rev, zpow_negSucc
-/
theorem conj_zpow {i : Int} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

@[to_additive]
/--
theorem `conj_injective` / 定理 `conj_injective`

English:
theorem conj_injective
  given: {x : α}
  statement: Function.Injective fun g : α => x * g * x⁻¹
  proof: fun a b => by simp

中文:
定理 conj_injective
  条件: {x : α}
  结论: 函数.单射 fun g : α => x * g * x⁻¹
  证明: fun a b => by simp
-/
theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  fun a b => by simp

end Group

namespace IsConj

/- This small quotient API is largely copied from the API of `Associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `IsConj` iff there is a unit `u` such that `u * x = y * u` -/
@[to_additive (attr := instance_reducible) /-- The setoid of the relation `IsAddConj` iff there
is an additive unit `u` such that `u + x = y + u` -/]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: (α : Type*) [Monoid α]
  body: IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

中文:
定义 setoid
  签名: (α : 类型) [幺半群 α]
  定义体: IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩
-/
protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

end IsConj

attribute [local instance] IsConj.setoid
attribute [local instance] IsAddConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
@[to_additive /-- The quotient type of additive conjugacy classes of an additive group. -/]
/--
Definition of `ConjClasses` / `ConjClasses` 的定义

English:
definition ConjClasses
  signature: (α : Type*) [Monoid α]
  body: Quotient (IsConj.setoid α)

中文:
定义 ConjClasses
  签名: (α : 类型) [幺半群 α]
  定义体: Quotient (IsConj.setoid α)

Depends on / 依赖: IsConj, IsConj.setoid, Quotient, setoid
-/
def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)

namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

/-- The canonical quotient map from a monoid `α` into the `ConjClasses` of `α` -/
@[to_additive /-- The canonical quotient map from an additive monoid `α` into the
`AddConjClasses` of `α` -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {α : Type*} [Monoid α] (a : α)
  body: ⟦a⟧

@[to_additive]

中文:
定义 mk
  签名: {α : 类型} [幺半群 α] (a : α)
  定义体: ⟦a⟧

@[to_additive]
-/
protected def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ConjClasses α)
  body: ⟨⟦1⟧⟩

@[to_additive]

中文:
实例 :
  签名: 可居 (ConjClasses α)
  定义体: ⟨⟦1⟧⟩

@[to_additive]
-/
instance : Inhabited (ConjClasses α) := ⟨⟦1⟧⟩

@[to_additive]
/--
theorem `mk_eq_mk_iff_isConj` / 定理 `mk_eq_mk_iff_isConj`

English:
theorem mk_eq_mk_iff_isConj
  given: {a b : α}
  statement: ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b
  proof: Iff.intro Quotient.exact Quot.sound

@[to_additive]

中文:
定理 mk_eq_mk_iff_isConj
  条件: {a b : α}
  结论: ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b
  证明: Iff.intro Quotient.exact Quot.sound

@[to_additive]

Depends on / 依赖: Iff.intro, Quot.sound, Quotient, Quotient.exact
-/
theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotient.exact Quot.sound

@[to_additive]
/--
theorem `quotient_mk_eq_mk` / 定理 `quotient_mk_eq_mk`

English:
theorem quotient_mk_eq_mk
  given: (a : α)
  statement: ⟦a⟧ = ConjClasses.mk a
  proof: rfl

@[to_additive]

中文:
定理 quotient_mk_eq_mk
  条件: (a : α)
  结论: ⟦a⟧ = ConjClasses.mk a
  证明: rfl

@[to_additive]
-/
theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl

@[to_additive]
/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  given: (a : α)
  statement: Quot.mk Setoid.r a = ConjClasses.mk a
  proof: rfl

@[to_additive]

中文:
定理 quot_mk_eq_mk
  条件: (a : α)
  结论: 商.mk 集合等价关系.r a = ConjClasses.mk a
  证明: rfl

@[to_additive]
-/
theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a :=
  rfl

@[to_additive]
/--
theorem `forall_isConj` / 定理 `forall_isConj`

English:
theorem forall_isConj
  given: {p : ConjClasses α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (ConjClasses.mk a)
  proof: Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

@[to_additive]

中文:
定理 对任意_isConj
  条件: {p : ConjClasses α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (ConjClasses.mk a)
  证明: Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

@[to_additive]

Depends on / 依赖: Iff.intro, Quotient, Quotient.inductionOn, inductionOn
-/
theorem forall_isConj {p : ConjClasses α -> Prop} : (forall a, p a) ↔ forall a, p (ConjClasses.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

@[to_additive]
/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (@ConjClasses.mk α _)
  proof: forall_isConj.2 fun a => ⟨a, rfl⟩

@[to_additive]

中文:
定理 mk_surjective
  结论: 函数.满射 (@ConjClasses.mk α _)
  证明: forall_isConj.2 fun a => ⟨a, rfl⟩

@[to_additive]

Depends on / 依赖: forall_isConj
-/
theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_isConj.2 fun a => ⟨a, rfl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (ConjClasses α)
  body: ⟨⟦1⟧⟩

@[to_additive]

中文:
实例 :
  签名: 幺 (ConjClasses α)
  定义体: ⟨⟦1⟧⟩

@[to_additive]
-/
instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

@[to_additive]
/--
theorem `one_eq_mk_one` / 定理 `one_eq_mk_one`

English:
theorem one_eq_mk_one
  statement: (1 : ConjClasses α) = ConjClasses.mk 1
  proof: rfl

@[to_additive]

中文:
定理 one_eq_mk_one
  结论: (1 : ConjClasses α) = ConjClasses.mk 1
  证明: rfl

@[to_additive]
-/
theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl

@[to_additive]
/--
theorem `exists_rep` / 定理 `exists_rep`

English:
theorem exists_rep
  given: (a : ConjClasses α)
  statement: exists a0 : α, ConjClasses.mk a0 = a
  proof: Quot.exists_rep a

中文:
定理 存在_rep
  条件: (a : ConjClasses α)
  结论: 存在 a0 : α, ConjClasses.mk a0 = a
  证明: Quot.exists_rep a

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem exists_rep (a : ConjClasses α) : exists a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a

/-- A `MonoidHom` maps conjugacy classes of one group to conjugacy classes of another. -/
@[to_additive /-- An `AddMonoidHom` maps additive conjugacy classes of one additive group to
additive conjugacy classes of another. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ->* β)
  body: Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)

@[to_additive]

中文:
定义 map
  签名: (f : α ->* β)
  定义体: Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)

@[to_additive]

Depends on / 依赖: ConjClasses, ConjClasses.mk, Quotient, Quotient.lift, f.map_isConj, map_isConj, mk_eq_mk_iff_isConj
-/
def map (f : α ->* β) : ConjClasses α -> ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)

@[to_additive]
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: {f : α ->* β} (hf : Function.Surjective f)
  proof: by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note «slow-failing instance priority» /--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a 

中文:
定理 map_surjective
  条件: {f : α ->* β} (hf : 函数.满射 f)
  证明: by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note «slow-failing instance priority» /--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a 

Depends on / 依赖: ConjClasses, ConjClasses.mk, ConjClasses.mk_surjective, mk_surjective
-/
theorem map_surjective {f : α ->* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note «slow-failing instance priority» /--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
* a class `C` has instances `instT : C T` and `instT' : C T'`;
* types `T` and `T'` are both reducible specializations of another type `S`;
* the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
  instead they have to be found by instance search.

If those conditions hold, the instance `instT` should be assigned lower priority.

Note that there is no issue unless `T` and `T'` are reducibly equal to `S`, Otherwise the instance
discrimination tree can distinguish them, and the note does not apply.

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableRel
  signature: (IsConj : α -> α -> Prop)] : DecidableEq (ConjClasses α)
  body: inferInstanceAs DecidableEq Quotient (IsConj.setoid α)

中文:
实例 [DecidableRel
  签名: (IsConj : α -> α -> 命题)] : DecidableEq (ConjClasses α)
  定义体: inferInstanceAs DecidableEq Quotient (IsConj.setoid α)

Depends on / 依赖: DecidableEq, IsConj, IsConj.setoid, Quotient, setoid
-/
instance [DecidableRel (IsConj : α -> α -> Prop)] : DecidableEq (ConjClasses α) :=
inferInstanceAs DecidableEq Quotient (IsConj.setoid α)

end Monoid

section CommMonoid

variable [CommMonoid α]

@[to_additive]
/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  statement: Function.Injective (@ConjClasses.mk α _)
  proof: fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

@[to_additive]

中文:
定理 mk_injective
  结论: 函数.单射 (@ConjClasses.mk α _)
  证明: fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

@[to_additive]
-/
theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

@[to_additive]
/--
theorem `mk_bijective` / 定理 `mk_bijective`

English:
theorem mk_bijective
  statement: Function.Bijective (@ConjClasses.mk α _)
  proof: ⟨mk_injective, mk_surjective⟩

中文:
定理 mk_bijective
  结论: 函数.双射 (@ConjClasses.mk α _)
  证明: ⟨mk_injective, mk_surjective⟩

Depends on / 依赖: mk_injective, mk_surjective
-/
theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
@[to_additive /-- The bijection between an `AddCommGroup` and its `AddConjClasses`. -/]
/--
Definition of `mkEquiv` / `mkEquiv` 的定义

English:
definition mkEquiv
  signature: : α ≃ ConjClasses α
  body: ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse]; rw [Function.LeftInverse]; rw [forall_isConj]
    solve_by_elim⟩

中文:
定义 mkEquiv
  签名: : α ≃ ConjClasses α
  定义体: ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse]; rw [Function.LeftInverse]; rw [forall_isConj]
    solve_by_elim⟩

Depends on / 依赖: ConjClasses, ConjClasses.mk, Function, Function.LeftInverse, Function.RightInverse, LeftInverse, Quotient, Quotient.lift, Quotient.lift_mk, RightInverse, forall_isConj, isConj_iff_eq, lift_mk, solve_by_elim
-/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse]; rw [Function.LeftInverse]; rw [forall_isConj]
    solve_by_elim⟩

end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
@[to_additive /-- Given an element `a`, `addConjugatesOf a` is the set of additive conjugates. -/]
/--
Definition of `conjugatesOf` / `conjugatesOf` 的定义

English:
definition conjugatesOf
  signature: (a : α)
  body: { b | IsConj a b }

@[to_additive]

中文:
定义 conjugatesOf
  签名: (a : α)
  定义体: { b | IsConj a b }

@[to_additive]

Depends on / 依赖: IsConj
-/
def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }

@[to_additive]
/--
theorem `mem_conjugatesOf_self` / 定理 `mem_conjugatesOf_self`

English:
theorem mem_conjugatesOf_self
  given: {a : α}
  statement: a in conjugatesOf a
  proof: IsConj.refl _

@[to_additive]

中文:
定理 mem_conjugatesOf_self
  条件: {a : α}
  结论: a in conjugatesOf a
  证明: IsConj.refl _

@[to_additive]

Depends on / 依赖: IsConj, IsConj.refl
-/
theorem mem_conjugatesOf_self {a : α} : a in conjugatesOf a :=
  IsConj.refl _

@[to_additive]
/--
theorem `IsConj.conjugatesOf_eq` / 定理 `IsConj.conjugatesOf_eq`

English:
theorem IsConj.conjugatesOf_eq
  given: {a b : α} (ab : IsConj a b)
  statement: conjugatesOf a = conjugatesOf b
  proof: Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

@[to_additive]

中文:
定理 IsConj.conjugatesOf_eq
  条件: {a b : α} (ab : IsConj a b)
  结论: conjugatesOf a = conjugatesOf b
  证明: Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

@[to_additive]

Depends on / 依赖: Set.ext, ab.symm.trans, ab.trans
-/
theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

@[to_additive]
/--
theorem `isConj_iff_conjugatesOf_eq` / 定理 `isConj_iff_conjugatesOf_eq`

English:
theorem isConj_iff_conjugatesOf_eq
  given: {a b : α}
  statement: IsConj a b ↔ conjugatesOf a = conjugatesOf b
  proof: ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

中文:
定理 isConj_iff_conjugatesOf_eq
  条件: {a b : α}
  结论: IsConj a b ↔ conjugatesOf a = conjugatesOf b
  证明: ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

Depends on / 依赖: IsConj, IsConj.conjugatesOf_eq, conjugatesOf_eq, mem_conjugatesOf_self
-/
theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
@[to_additive /-- Given an additive conjugacy class `a`, `carrier a` is the set it represents. -/]
/--
Definition of `carrier` / `carrier` 的定义

English:
definition carrier
  signature: : ConjClasses α -> Set α
  body: Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab

@[to_additive]

中文:
定义 carrier
  签名: : ConjClasses α -> 集合 α
  定义体: Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab

@[to_additive]

Depends on / 依赖: IsConj, IsConj.conjugatesOf_eq, Quotient, Quotient.lift, conjugatesOf, conjugatesOf_eq
-/
def carrier : ConjClasses α -> Set α :=
  Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab

@[to_additive]
/--
theorem `mem_carrier_mk` / 定理 `mem_carrier_mk`

English:
theorem mem_carrier_mk
  given: {a : α}
  statement: a in carrier (ConjClasses.mk a)
  proof: IsConj.refl _

@[to_additive]

中文:
定理 mem_carrier_mk
  条件: {a : α}
  结论: a in carrier (ConjClasses.mk a)
  证明: IsConj.refl _

@[to_additive]

Depends on / 依赖: IsConj, IsConj.refl
-/
theorem mem_carrier_mk {a : α} : a in carrier (ConjClasses.mk a) :=
  IsConj.refl _

@[to_additive]
/--
theorem `mem_carrier_iff_mk_eq` / 定理 `mem_carrier_iff_mk_eq`

English:
theorem mem_carrier_iff_mk_eq
  given: {a : α} {b : ConjClasses α}
  proof: by
  revert b
  rw [forall_isConj]
  intro b
  rw [carrier]; rw [eq_comm]; rw [mk_eq_mk_iff_isConj]; rw [← quotient_mk_eq_mk]; rw [Quotient.lift_mk]
  rfl

@[to_additive]

中文:
定理 mem_carrier_iff_mk_eq
  条件: {a : α} {b : ConjClasses α}
  证明: by
  revert b
  rw [forall_isConj]
  intro b
  rw [carrier]; rw [eq_comm]; rw [mk_eq_mk_iff_isConj]; rw [← quotient_mk_eq_mk]; rw [Quotient.lift_mk]
  rfl

@[to_additive]

Depends on / 依赖: Quotient, Quotient.lift_mk, carrier, eq_comm, forall_isConj, lift_mk, mk_eq_mk_iff_isConj, quotient_mk_eq_mk, revert
-/
theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a in carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [forall_isConj]
  intro b
  rw [carrier]; rw [eq_comm]; rw [mk_eq_mk_iff_isConj]; rw [← quotient_mk_eq_mk]; rw [Quotient.lift_mk]
  rfl

@[to_additive]
/--
theorem `carrier_eq_preimage_mk` / 定理 `carrier_eq_preimage_mk`

English:
theorem carrier_eq_preimage_mk
  given: {a : ConjClasses α}
  statement: a.carrier = ConjClasses.mk ⁻¹' {a}
  proof: Set.ext fun _ => mem_carrier_iff_mk_eq

中文:
定理 carrier_eq_preimage_mk
  条件: {a : ConjClasses α}
  结论: a.carrier = ConjClasses.mk ⁻¹' {a}
  证明: Set.ext fun _ => mem_carrier_iff_mk_eq

Depends on / 依赖: Set.ext, mem_carrier_iff_mk_eq
-/
theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun _ => mem_carrier_iff_mk_eq

end ConjClasses
