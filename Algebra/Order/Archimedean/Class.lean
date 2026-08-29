/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# Archimedean classes of a linearly ordered group

This file defines archimedean classes of a given linearly ordered group. Archimedean classes
measure to what extent the group fails to be Archimedean. For additive group, elements `a` and `b`
in the same class are "equivalent" in the sense that there exist two natural numbers
`m` and `n` such that `|a| ≤ m • |b|` and `|b| ≤ n • |a|`. An element `a` in a higher class than `b`
is "infinitesimal" to `b` in the sense that `n • |a| < |b|` for all natural numbers `n`.

If `a` and `b` are in the same equivalence class, they're sometimes referred to as "commensurate"
elements.

## Main definitions

* `ArchimedeanClass` is the archimedean class for additive linearly ordered group.
* `MulArchimedeanClass` is the archimedean class for multiplicative linearly ordered group.
* `ArchimedeanClass.orderHom` and `MulArchimedeanClass.orderHom` are `OrderHom` over
  archimedean classes lifted from ordered group homomorphisms.
* `ArchimedeanClass.ballAddSubgroup` and `MulArchimedeanClass.ballSubgroup` are subgroups
  formed by an open interval of archimedean classes
* `ArchimedeanClass.closedBallAddSubgroup` and `MulArchimedeanClass.closedBallSubgroup` are
  subgroups formed by a closed interval of archimedean classes.

## Main statements

The following theorems state that an ordered commutative group is (mul-)archimedean if and only if
all non-identity elements belong to the same (`Mul`-)`ArchimedeanClass`:
* `ArchimedeanClass.archimedean_of_mk_eq_mk` / `MulArchimedeanClass.mulArchimedean_of_mk_eq_mk`
* `ArchimedeanClass.mk_eq_mk_of_archimedean` / `MulArchimedeanClass.mk_eq_mk_of_mulArchimedean`

## Implementation notes

Archimedean classes are equipped with a linear order, where elements with smaller absolute value
are placed in a *higher* classes by convention. Ordering backwards this way simplifies
formalization of theorems such as the Hahn embedding theorem.

To naturally derive this order, we first define it on the underlying group via the type
synonym (`Mul`-)`ArchimedeanOrder`, and define (`Mul`-)`ArchimedeanClass` as `Antisymmetrization` of
the order.

-/

@[expose] public section

section ArchimedeanOrder
variable {M : Type*}

variable (M) in
/-- Type synonym to equip an ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, |b|ₘ ^ n < |a|ₘ`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order. -/
@[to_additive ArchimedeanOrder
/-- Type synonym to equip an ordered group with a new `Preorder` defined by the infinitesimal order
of elements. `a` is said less than `b` if `b` is infinitesimal comparing to `a`, or more precisely,
`∀ n, n • |b| < |a|`. If `a` and `b` are neither infinitesimal to each other, they are equivalent
in this order. -/]
/--
Definition of `MulArchimedeanOrder` / `MulArchimedeanOrder` 的定义

English:
definition MulArchimedeanOrder
  body: M

中文:
定义 MulArchimedeanOrder
  定义体: M
-/
def MulArchimedeanOrder := M

namespace MulArchimedeanOrder

/-- Create a `MulArchimedeanOrder` element from the underlying type. -/
@[to_additive /-- Create a `ArchimedeanOrder` element from the underlying type. -/]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : M ≃ MulArchimedeanOrder M
  body: Equiv.refl _

中文:
定义 of
  签名: : M ≃ MulArchimedeanOrder M
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def of : M ≃ MulArchimedeanOrder M := Equiv.refl _

/-- Retrieve the underlying value from a `MulArchimedeanOrder` element. -/
@[to_additive /-- Retrieve the underlying value from a `ArchimedeanOrder` element. -/]
/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : MulArchimedeanOrder M ≃ M
  body: Equiv.refl _

@[to_additive (attr := simp)]

中文:
定义 val
  签名: : MulArchimedeanOrder M ≃ M
  定义体: Equiv.refl _

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.refl
-/
def val : MulArchimedeanOrder M ≃ M := Equiv.refl _

@[to_additive (attr := simp)]
/--
theorem `of_symm_eq` / 定理 `of_symm_eq`

English:
theorem of_symm_eq
  statement: (of (M := M)).symm = val
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 of_symm_eq
  结论: (of (M := M)).symm = val
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem of_symm_eq : (of (M := M)).symm = val := rfl

@[to_additive (attr := simp)]
/--
theorem `val_symm_eq` / 定理 `val_symm_eq`

English:
theorem val_symm_eq
  statement: (val (M := M)).symm = of
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 val_symm_eq
  结论: (val (M := M)).symm = of
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem val_symm_eq : (val (M := M)).symm = of := rfl

@[to_additive (attr := simp)]
/--
theorem `of_val` / 定理 `of_val`

English:
theorem of_val
  given: (a : MulArchimedeanOrder M)
  statement: of (val a) = a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 of_val
  条件: (a : MulArchimedeanOrder M)
  结论: of (val a) = a
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem of_val (a : MulArchimedeanOrder M) : of (val a) = a := rfl

@[to_additive (attr := simp)]
/--
theorem `val_of` / 定理 `val_of`

English:
theorem val_of
  given: (a : M)
  statement: val (of a) = a
  proof: rfl

@[to_additive]

中文:
定理 val_of
  条件: (a : M)
  结论: val (of a) = a
  证明: rfl

@[to_additive]
-/
theorem val_of (a : M) : val (of a) = a := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: M] : Nonempty (MulArchimedeanOrder M)
  body: inferInstanceAs (Nonempty M)

@[to_additive]

中文:
实例 [非空
  签名: M] : 非空 (MulArchimedeanOrder M)
  定义体: inferInstanceAs (Nonempty M)

@[to_additive]

Depends on / 依赖: Nonempty
-/
instance [Nonempty M] : Nonempty (MulArchimedeanOrder M) :=
  inferInstanceAs (Nonempty M)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: M] : Inhabited (MulArchimedeanOrder M)
  body: ⟨of default⟩

@[to_additive]

中文:
实例 [可居
  签名: M] : 可居 (MulArchimedeanOrder M)
  定义体: ⟨of default⟩

@[to_additive]
-/
instance [Inhabited M] : Inhabited (MulArchimedeanOrder M) :=
  ⟨of default⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Subsingleton (MulArchimedeanOrder M)
  body: inferInstanceAs (Subsingleton M)

中文:
实例 [子单例
  签名: M] : 子单例 (MulArchimedeanOrder M)
  定义体: inferInstanceAs (Subsingleton M)

Depends on / 依赖: Subsingleton
-/
instance [Subsingleton M] : Subsingleton (MulArchimedeanOrder M) :=
  inferInstanceAs (Subsingleton M)

variable [Group M] [Lattice M]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (MulArchimedeanOrder M)
  body: exists n, |b.val|ₘ <= |a.val|ₘ ^ n

@[to_additive]

中文:
实例 :
  签名: LE (MulArchimedeanOrder M)
  定义体: exists n, |b.val|ₘ <= |a.val|ₘ ^ n

@[to_additive]

Depends on / 依赖: a.val, b.val
-/
instance : LE (MulArchimedeanOrder M) where
  le a b := exists n, |b.val|ₘ <= |a.val|ₘ ^ n

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (MulArchimedeanOrder M)
  body: forall n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]

中文:
实例 :
  签名: LT (MulArchimedeanOrder M)
  定义体: forall n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]

Depends on / 依赖: a.val, b.val
-/
instance : LT (MulArchimedeanOrder M) where
  lt a b := forall n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {a b : MulArchimedeanOrder M}
  statement: a <= b ↔ exists n, |b.val|ₘ <= |a.val|ₘ ^ n
  proof: .rfl

@[to_additive]

中文:
定理 le_def
  条件: {a b : MulArchimedeanOrder M}
  结论: a <= b ↔ 存在 n, |b.val|ₘ <= |a.val|ₘ ^ n
  证明: .rfl

@[to_additive]
-/
theorem le_def {a b : MulArchimedeanOrder M} : a <= b ↔ exists n, |b.val|ₘ <= |a.val|ₘ ^ n := .rfl

@[to_additive]
/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {a b : MulArchimedeanOrder M}
  statement: a < b ↔ forall n, |b.val|ₘ ^ n < |a.val|ₘ
  proof: .rfl

中文:
定理 lt_def
  条件: {a b : MulArchimedeanOrder M}
  结论: a < b ↔ 对任意 n, |b.val|ₘ ^ n < |a.val|ₘ
  证明: .rfl
-/
theorem lt_def {a b : MulArchimedeanOrder M} : a < b ↔ forall n, |b.val|ₘ ^ n < |a.val|ₘ := .rfl

variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (MulArchimedeanOrder M)
  body: ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_ge a b := by
    rw [lt_def]; rw [le_def]; rw [le_def]
    suffices (forall (n : Nat), |b.val|ₘ ^ n < |a.val|ₘ) -> exists n, |b.val|ₘ <= |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

@[to_additive]

中文:
实例 :
  签名: 预序 (MulArchimedeanOrder M)
  定义体: ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_ge a b := by
    rw [lt_def]; rw [le_def]; rw [le_def]
    suffices (forall (n : Nat), |b.val|ₘ ^ n < |a.val|ₘ) -> exists n, |b.val|ₘ <= |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

@[to_additive]
-/
instance : Preorder (MulArchimedeanOrder M) where
  le_refl a := ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_ge a b := by
    rw [lt_def]; rw [le_def]; rw [le_def]
    suffices (forall (n : Nat), |b.val|ₘ ^ n < |a.val|ₘ) -> exists n, |b.val|ₘ <= |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Total (MulArchimedeanOrder M) (· <= ·)
  body: by
    obtain hab | hab := le_total |a.val|ₘ |b.val|ₘ
    · exact .inr ⟨1, by simpa using hab⟩
    · exact .inl ⟨1, by simpa using hab⟩

中文:
实例 :
  签名: @Std.全 (MulArchimedeanOrder M) (· <= ·)
  定义体: by
    obtain hab | hab := le_total |a.val|ₘ |b.val|ₘ
    · exact .inr ⟨1, by simpa using hab⟩
    · exact .inl ⟨1, by simpa using hab⟩

Depends on / 依赖: a.val, b.val, le_total
-/
instance : @Std.Total (MulArchimedeanOrder M) (· <= ·) where
  total a b := by
    obtain hab | hab := le_total |a.val|ₘ |b.val|ₘ
    · exact .inr ⟨1, by simpa using hab⟩
    · exact .inl ⟨1, by simpa using hab⟩

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be made to an `OrderHom` between their `MulArchimedeanOrder`. -/
@[to_additive /-- An `OrderAddMonoidHom` can be made to an `OrderHom` between their
`ArchimedeanOrder`. -/]
/--
Definition of `orderHom` / `orderHom` 的定义

English:
definition orderHom
  signature: (f : M ->*o N)
  body: of (f a.val)
  monotone' := by
    rintro a b ⟨n, hn⟩
    simp_rw [le_def, val_of, ← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

中文:
定义 orderHom
  签名: (f : M ->*o N)
  定义体: of (f a.val)
  monotone' := by
    rintro a b ⟨n, hn⟩
    simp_rw [le_def, val_of, ← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

Depends on / 依赖: a.val
-/
def orderHom (f : M ->*o N) : MulArchimedeanOrder M ->o MulArchimedeanOrder N where
  toFun a := of (f a.val)
  monotone' := by
    rintro a b ⟨n, hn⟩
    simp_rw [le_def, val_of, ← map_mabs, ← map_pow]
    exact ⟨n, OrderHomClass.monotone f hn⟩

end MulArchimedeanOrder

end ArchimedeanOrder

variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable (M) in
/-- `MulArchimedeanClass M` is the quotient of the group `M` by multiplicative archimedean
equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n : ℕ, |a|ₘ ≤ |b|ₘ ^ n)`. -/
@[to_additive ArchimedeanClass
/-- `ArchimedeanClass M` is the quotient of the additive group `M` by additive archimedean
equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b| ≤ m • |a|) ∧ (∃ n : ℕ, |a| ≤ n • |b|)`. -/]
/--
Definition of `MulArchimedeanClass` / `MulArchimedeanClass` 的定义

English:
definition MulArchimedeanClass
  body: Antisymmetrization (MulArchimedeanOrder M) (· <= ·)

中文:
定义 MulArchimedeanClass
  定义体: Antisymmetrization (MulArchimedeanOrder M) (· <= ·)

Depends on / 依赖: Antisymmetrization, MulArchimedeanOrder
-/
def MulArchimedeanClass := Antisymmetrization (MulArchimedeanOrder M) (· <= ·)

namespace MulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive /-- The archimedean class of a given element. -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (a : M)
  body: toAntisymmetrization _ (MulArchimedeanOrder.of a)

中文:
定义 mk
  签名: (a : M)
  定义体: toAntisymmetrization _ (MulArchimedeanOrder.of a)

Depends on / 依赖: MulArchimedeanOrder, MulArchimedeanOrder.of, toAntisymmetrization
-/
def mk (a : M) : MulArchimedeanClass M := toAntisymmetrization _ (MulArchimedeanOrder.of a)

/-- An induction principle for `MulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
/-- An induction principle for `ArchimedeanClass` -/]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {motive : MulArchimedeanClass M -> Prop} (mk : forall a, motive (.mk a))
  statement: forall x, motive x
  proof: Antisymmetrization.ind _ mk

@[to_additive]

中文:
定理 ind
  条件: {motive : MulArchimedeanClass M -> 命题} (mk : 对任意 a, motive (.mk a))
  结论: 对任意 x, motive x
  证明: Antisymmetrization.ind _ mk

@[to_additive]

Depends on / 依赖: Antisymmetrization, Antisymmetrization.ind
-/
theorem ind {motive : MulArchimedeanClass M -> Prop} (mk : forall a, motive (.mk a)) : forall x, motive x :=
  Antisymmetrization.ind _ mk

@[to_additive]
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : MulArchimedeanClass M -> Prop}
  statement: (forall A, p A) ↔ forall a, p (mk a)
  proof: Quotient.forall

中文:
定理 «对任意»
  条件: {p : MulArchimedeanClass M -> 命题}
  结论: (对任意 A, p A) ↔ 对任意 a, p (mk a)
  证明: Quotient.forall
-/
theorem «forall» {p : MulArchimedeanClass M -> Prop} : (forall A, p A) ↔ forall a, p (mk a) := Quotient.forall

variable (M) in
@[to_additive]
/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective mk (M := M)
  proof: Quotient.mk_surjective

中文:
定理 mk_surjective
  结论: 函数.满射 mk (M := M)
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
theorem mk_surjective : Function.Surjective mk (M := M) := Quotient.mk_surjective

variable (M) in
@[to_additive (attr := simp)]
/--
theorem `range_mk` / 定理 `range_mk`

English:
theorem range_mk
  statement: Set.range (mk (M := M)) = Set.univ
  proof: Set.range_eq_univ.mpr (mk_surjective M)

中文:
定理 range_mk
  结论: 集合.range (mk (M := M)) = 集合.univ
  证明: Set.range_eq_univ.mpr (mk_surjective M)

Depends on / 依赖: Set.range_eq_univ.mpr, Set.univ, mk_surjective, range_eq_univ
-/
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {a b : M}
  statement: mk a = mk b ↔ (exists m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
  proof: by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

中文:
定理 mk_eq_mk
  条件: {a b : M}
  结论: mk a = mk b ↔ (存在 m, |b|ₘ <= |a|ₘ ^ m) ∧ (存在 n, |a|ₘ <= |b|ₘ ^ n)
  证明: by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

Depends on / 依赖: Quotient, Quotient.eq, toAntisymmetrization
-/
theorem mk_eq_mk {a b : M} : mk a = mk b ↔ (exists m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n) := by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

/-- Lift a `M → α` function to `MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → α` function to `ArchimedeanClass M → α`. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b)
  body: Quotient.lift f fun _ _ h' => h _ _ mk_eq_mk.mpr h'

@[to_additive (attr := simp)]

中文:
定义 lift
  签名: {α : 类型} (f : M -> α) (h : 对任意 a b, mk a = mk b -> f a = f b)
  定义体: Quotient.lift f fun _ _ h' => h _ _ mk_eq_mk.mpr h'

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.lift, mk_eq_mk, mk_eq_mk.mpr
-/
def lift {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b) :
    MulArchimedeanClass M -> α :=
Quotient.lift f fun _ _ h' => h _ _ mk_eq_mk.mpr h'

@[to_additive (attr := simp)]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b)
  proof: by
  unfold lift
  exact Quotient.lift_mk f (fun _ _ h' => h _ _ <| mk_eq_mk.mpr h') a

中文:
定理 lift_mk
  结论: {α : 类型} (f : M -> α) (h : 对任意 a b, mk a = mk b -> f a = f b)
  证明: by
  unfold lift
  exact Quotient.lift_mk f (fun _ _ h' => h _ _ <| mk_eq_mk.mpr h') a

Depends on / 依赖: Quotient, Quotient.lift_mk, lift_mk, mk_eq_mk, mk_eq_mk.mpr
-/
theorem lift_mk {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b)
    (a : M) : lift f h (mk a) = f a := by
  unfold lift
  exact Quotient.lift_mk f (fun _ _ h' => h _ _ <| mk_eq_mk.mpr h') a

/-- Lift a `M → M → α` function to `MulArchimedeanClass M → MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → M → α` function to `ArchimedeanClass M → ArchimedeanClass M → α`. -/]
/--
Definition of `lift₂` / `lift₂` 的定义

English:
definition lift₂
  signature: {α : Type*} (f : M -> M -> α)
  body: Quotient.lift₂ f fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)

@[to_additive (attr := simp)]

中文:
定义 lift₂
  签名: {α : 类型} (f : M -> M -> α)
  定义体: Quotient.lift₂ f fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.lift, mk_eq_mk, mk_eq_mk.mpr
-/
def lift₂ {α : Type*} (f : M -> M -> α)
    (h : forall a₁ b₁ a₂ b₂, mk a₁ = mk b₁ -> mk a₂ = mk b₂ -> f a₁ a₂ = f b₁ b₂) :
    MulArchimedeanClass M -> MulArchimedeanClass M -> α :=
  Quotient.lift₂ f fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)

@[to_additive (attr := simp)]
/--
theorem `lift₂_mk` / 定理 `lift₂_mk`

English:
theorem lift₂_mk
  statement: {α : Type*} (f : M -> M -> α)
  proof: by
  unfold lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)) a b

中文:
定理 lift₂_mk
  结论: {α : 类型} (f : M -> M -> α)
  证明: by
  unfold lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)) a b

Depends on / 依赖: Quotient, Quotient.lift, mk_eq_mk, mk_eq_mk.mpr
-/
theorem lift₂_mk {α : Type*} (f : M -> M -> α)
    (h : forall a₁ b₁ a₂ b₂, mk a₁ = mk b₁ -> mk a₂ = mk b₂ -> f a₁ a₂ = f b₁ b₂)
    (a b : M) : lift₂ f h (mk a) (mk b) = f a b := by
  unfold lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ => h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)) a b

/-- Choose a representative element from a given archimedean class. -/
@[to_additive /-- Choose a representative element from a given archimedean class. -/]
noncomputable
/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: (A : MulArchimedeanClass M)
  body: (Quotient.out A).val

@[to_additive (attr := simp)]

中文:
定义 out
  签名: (A : MulArchimedeanClass M)
  定义体: (Quotient.out A).val

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.out
-/
def out (A : MulArchimedeanClass M) : M := (Quotient.out A).val

@[to_additive (attr := simp)]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: (A : MulArchimedeanClass M)
  statement: mk A.out = A
  proof: Quotient.out_eq' A

@[to_additive (attr := simp)]

中文:
定理 mk_out
  条件: (A : MulArchimedeanClass M)
  结论: mk A.out = A
  证明: Quotient.out_eq' A

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem mk_out (A : MulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive (attr := simp)]
/--
theorem `mk_inv` / 定理 `mk_inv`

English:
theorem mk_inv
  given: (a : M)
  statement: mk a⁻¹ = mk a
  proof: mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]

中文:
定理 mk_inv
  条件: (a : M)
  结论: mk a⁻¹ = mk a
  证明: mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]

Depends on / 依赖: mk_eq_mk, mk_eq_mk.mpr
-/
theorem mk_inv (a : M) : mk a⁻¹ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
/--
theorem `mk_div_comm` / 定理 `mk_div_comm`

English:
theorem mk_div_comm
  given: (a b : M)
  statement: mk (a / b) = mk (b / a)
  proof: by
  rw [← mk_inv]; rw [inv_div]

@[to_additive (attr := simp)]

中文:
定理 mk_div_comm
  条件: (a b : M)
  结论: mk (a / b) = mk (b / a)
  证明: by
  rw [← mk_inv]; rw [inv_div]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_div, mk_inv
-/
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv]; rw [inv_div]

@[to_additive (attr := simp)]
/--
theorem `mk_mabs` / 定理 `mk_mabs`

English:
theorem mk_mabs
  given: (a : M)
  statement: mk |a|ₘ = mk a
  proof: mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]

中文:
定理 mk_mabs
  条件: (a : M)
  结论: mk |a|ₘ = mk a
  证明: mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]

Depends on / 依赖: mk_eq_mk, mk_eq_mk.mpr
-/
theorem mk_mabs (a : M) : mk |a|ₘ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Subsingleton (MulArchimedeanClass M)
  body: inferInstanceAs (Subsingleton (Antisymmetrization ..))

@[to_additive]
noncomputable

中文:
实例 [子单例
  签名: M] : 子单例 (MulArchimedeanClass M)
  定义体: inferInstanceAs (Subsingleton (Antisymmetrization ..))

@[to_additive]
noncomputable

Depends on / 依赖: Antisymmetrization, Subsingleton
-/
instance [Subsingleton M] : Subsingleton (MulArchimedeanClass M) :=
  inferInstanceAs (Subsingleton (Antisymmetrization ..))

@[to_additive]
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (MulArchimedeanClass M)
  body: open scoped Classical in
  -- TODO: why does `inferInstanceAs` not work here?
  fast_instance% (inferInstance : LinearOrder (Antisymmetrization (MulArchimedeanOrder M) (· <= ·)))

@[to_additive]

中文:
实例 :
  签名: 线性序 (MulArchimedeanClass M)
  定义体: open scoped Classical in
  -- TODO: why does `inferInstanceAs` not work here?
  fast_instance% (inferInstance : LinearOrder (Antisymmetrization (MulArchimedeanOrder M) (· <= ·)))

@[to_additive]

Depends on / 依赖: Classical, scoped
-/
instance : LinearOrder (MulArchimedeanClass M) :=
  open scoped Classical in
  -- TODO: why does `inferInstanceAs` not work here?
  fast_instance% (inferInstance : LinearOrder (Antisymmetrization (MulArchimedeanOrder M) (· <= ·)))

@[to_additive]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  statement: mk a <= mk b ↔ exists n, |b|ₘ <= |a|ₘ ^ n
  proof: .rfl

@[to_additive]

中文:
定理 mk_le_mk
  结论: mk a <= mk b ↔ 存在 n, |b|ₘ <= |a|ₘ ^ n
  证明: .rfl

@[to_additive]
-/
theorem mk_le_mk : mk a <= mk b ↔ exists n, |b|ₘ <= |a|ₘ ^ n := .rfl

@[to_additive]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  statement: mk a < mk b ↔ forall n, |b|ₘ ^ n < |a|ₘ
  proof: .rfl

@[to_additive]

中文:
定理 mk_lt_mk
  结论: mk a < mk b ↔ 对任意 n, |b|ₘ ^ n < |a|ₘ
  证明: .rfl

@[to_additive]
-/
theorem mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ n < |a|ₘ := .rfl

@[to_additive]
/--
theorem `mk_le_mk_iff_lt` / 定理 `mk_le_mk_iff_lt`

English:
theorem mk_le_mk_iff_lt
  given: (ha : a != 1)
  statement: mk a <= mk b ↔ exists n, |b|ₘ < |a|ₘ ^ n
  proof: by
  refine ⟨fun ⟨n, hn⟩ => ⟨n + 1, hn.trans_lt ?_⟩, fun ⟨n, hn⟩ => ?_⟩
  · rw [pow_succ]
    exact lt_mul_of_one_lt_right' _ (one_lt_mabs.mpr ha)
  · exact ⟨n, hn.le⟩

中文:
定理 mk_le_mk_iff_lt
  条件: (ha : a != 1)
  结论: mk a <= mk b ↔ 存在 n, |b|ₘ < |a|ₘ ^ n
  证明: by
  refine ⟨fun ⟨n, hn⟩ => ⟨n + 1, hn.trans_lt ?_⟩, fun ⟨n, hn⟩ => ?_⟩
  · rw [pow_succ]
    exact lt_mul_of_one_lt_right' _ (one_lt_mabs.mpr ha)
  · exact ⟨n, hn.le⟩

Depends on / 依赖: hn.le, hn.trans_lt, lt_mul_of_one_lt_right, one_lt_mabs, one_lt_mabs.mpr, pow_succ, trans_lt
-/
theorem mk_le_mk_iff_lt (ha : a != 1) : mk a <= mk b ↔ exists n, |b|ₘ < |a|ₘ ^ n := by
  refine ⟨fun ⟨n, hn⟩ => ⟨n + 1, hn.trans_lt ?_⟩, fun ⟨n, hn⟩ => ?_⟩
  · rw [pow_succ]
    exact lt_mul_of_one_lt_right' _ (one_lt_mabs.mpr ha)
  · exact ⟨n, hn.le⟩

/-- 1 is in its own class (see `MulArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/
@[to_additive /-- 0 is in its own class (see `ArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (MulArchimedeanClass M)
  body: mk 1
  le_top A := by
    induction A using ind with | mk a
    rw [mk_le_mk]
    exact ⟨1, by simp⟩

@[to_additive]

中文:
实例 :
  签名: 有顶序 (MulArchimedeanClass M)
  定义体: mk 1
  le_top A := by
    induction A using ind with | mk a
    rw [mk_le_mk]
    exact ⟨1, by simp⟩

@[to_additive]
-/
noncomputable instance : OrderTop (MulArchimedeanClass M) where
  top := mk 1
  le_top A := by
    induction A using ind with | mk a
    rw [mk_le_mk]
    exact ⟨1, by simp⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MulArchimedeanClass M)
  body: ⟨⊤⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 可居 (MulArchimedeanClass M)
  定义体: ⟨⊤⟩

@[to_additive (attr := simp)]
-/
noncomputable instance : Inhabited (MulArchimedeanClass M) := ⟨⊤⟩

@[to_additive (attr := simp)]
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  statement: mk 1 = (⊤ : MulArchimedeanClass M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_one
  结论: mk 1 = (⊤ : MulArchimedeanClass M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_one : mk 1 = (⊤ : MulArchimedeanClass M) := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_eq_top_iff` / 定理 `mk_eq_top_iff`

English:
theorem mk_eq_top_iff
  statement: mk a = ⊤ ↔ a = 1 where
  proof: by simp [← mk_one, mk_eq_mk]
  mpr := by simp_all

@[to_additive (attr := simp)]

中文:
定理 mk_eq_top_iff
  结论: mk a = ⊤ ↔ a = 1 where
  证明: by simp [← mk_one, mk_eq_mk]
  mpr := by simp_all

@[to_additive (attr := simp)]

Depends on / 依赖: mk_eq_mk, mk_one
-/
theorem mk_eq_top_iff : mk a = ⊤ ↔ a = 1 where
  mp := by simp [← mk_one, mk_eq_mk]
  mpr := by simp_all

@[to_additive (attr := simp)]
/--
theorem `top_eq_mk_iff` / 定理 `top_eq_mk_iff`

English:
theorem top_eq_mk_iff
  statement: ⊤ = mk a ↔ a = 1
  proof: by
  rw [eq_comm]; rw [mk_eq_top_iff]

@[to_additive (attr := simp)]

中文:
定理 top_eq_mk_iff
  结论: ⊤ = mk a ↔ a = 1
  证明: by
  rw [eq_comm]; rw [mk_eq_top_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: eq_comm, mk_eq_top_iff
-/
theorem top_eq_mk_iff : ⊤ = mk a ↔ a = 1 := by
  rw [eq_comm]; rw [mk_eq_top_iff]

@[to_additive (attr := simp)]
/--
theorem `out_top` / 定理 `out_top`

English:
theorem out_top
  statement: (⊤ : MulArchimedeanClass M).out = 1
  proof: by
  rw [← mk_eq_top_iff]; rw [mk_out]

@[to_additive]

中文:
定理 out_top
  结论: (⊤ : MulArchimedeanClass M).out = 1
  证明: by
  rw [← mk_eq_top_iff]; rw [mk_out]

@[to_additive]

Depends on / 依赖: mk_eq_top_iff, mk_out
-/
theorem out_top : (⊤ : MulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_top_iff]; rw [mk_out]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial (MulArchimedeanClass M) where
  body: by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, ⊤, mk_eq_top_iff.ne.mpr hx⟩

@[to_additive]

中文:
实例 [非平凡
  签名: M] : 非平凡 (MulArchimedeanClass M) where
  定义体: by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, ⊤, mk_eq_top_iff.ne.mpr hx⟩

@[to_additive]

Depends on / 依赖: exists_ne, mk_eq_top_iff, mk_eq_top_iff.ne.mpr
-/
instance [Nontrivial M] : Nontrivial (MulArchimedeanClass M) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, ⊤, mk_eq_top_iff.ne.mpr hx⟩

@[to_additive]
/--
theorem `mk_antitoneOn` / 定理 `mk_antitoneOn`

English:
theorem mk_antitoneOn
  statement: AntitoneOn mk (Set.Ici (1 : M))
  proof: by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha]; rw [mabs_eq_self.mpr hb] at h
  simpa using h

@[to_additive]

中文:
定理 mk_antitoneOn
  结论: AntitoneOn mk (集合.左闭右无界区间 (1 : M))
  证明: by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha]; rw [mabs_eq_self.mpr hb] at h
  simpa using h

@[to_additive]

Depends on / 依赖: contrapose, mabs_eq_self, mabs_eq_self.mpr, mk_lt_mk
-/
theorem mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha]; rw [mabs_eq_self.mpr hb] at h
  simpa using h

@[to_additive]
/--
theorem `mk_monotoneOn` / 定理 `mk_monotoneOn`

English:
theorem mk_monotoneOn
  statement: MonotoneOn mk (Set.Iic (1 : M))
  proof: by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha]; rw [mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]

中文:
定理 mk_monotoneOn
  结论: MonotoneOn mk (集合.左无界右闭区间 (1 : M))
  证明: by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha]; rw [mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]

Depends on / 依赖: contrapose, mabs_eq_inv_self, mabs_eq_inv_self.mpr, mk_lt_mk
-/
theorem mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha]; rw [mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]
/--
theorem `mk_le_mk_of_mabs` / 定理 `mk_le_mk_of_mabs`

English:
theorem mk_le_mk_of_mabs
  given: {a b : M} (h : |a|ₘ <= |b|ₘ)
  statement: mk b <= mk a
  proof: by
  rw [← mk_mabs a]; rw [← mk_mabs]
  have ha := one_le_mabs a
  exact mk_antitoneOn ha (ha.trans h) h

@[to_additive]

中文:
定理 mk_le_mk_of_mabs
  条件: {a b : M} (h : |a|ₘ <= |b|ₘ)
  结论: mk b <= mk a
  证明: by
  rw [← mk_mabs a]; rw [← mk_mabs]
  have ha := one_le_mabs a
  exact mk_antitoneOn ha (ha.trans h) h

@[to_additive]

Depends on / 依赖: ha.trans, mk_antitoneOn, mk_mabs, one_le_mabs
-/
theorem mk_le_mk_of_mabs {a b : M} (h : |a|ₘ <= |b|ₘ) : mk b <= mk a := by
  rw [← mk_mabs a]; rw [← mk_mabs]
  have ha := one_le_mabs a
  exact mk_antitoneOn ha (ha.trans h) h

@[to_additive]
/--
theorem `min_le_mk_of_le_of_le` / 定理 `min_le_mk_of_le_of_le`

English:
theorem min_le_mk_of_le_of_le
  given: {x y z : M} (hy : y <= x) (hz : x <= z)
  statement: min (mk y) (mk z) <= mk x
  proof: by
  have H := mabs_le_max_mabs_mabs hy hz
  rw [← mabs_of_one_le (le_max_of_le_left (one_le_mabs y))] at H
  apply (mk_le_mk_of_mabs H).trans'
  obtain h | h := le_total |y|ₘ |z|ₘ
  · rw [max_eq_right h, min_eq_right, mk_mabs]
    exact mk_le_mk_of_mabs h
  · rw [max_eq_left h, min_eq_left, mk_mabs]
    exact mk_le_mk_of_mabs h

@[to_additive]

中文:
定理 min_le_mk_of_le_of_le
  条件: {x y z : M} (hy : y <= x) (hz : x <= z)
  结论: 最小值 (mk y) (mk z) <= mk x
  证明: by
  have H := mabs_le_max_mabs_mabs hy hz
  rw [← mabs_of_one_le (le_max_of_le_left (one_le_mabs y))] at H
  apply (mk_le_mk_of_mabs H).trans'
  obtain h | h := le_total |y|ₘ |z|ₘ
  · rw [max_eq_right h, min_eq_right, mk_mabs]
    exact mk_le_mk_of_mabs h
  · rw [max_eq_left h, min_eq_left, mk_mabs]
    exact mk_le_mk_of_mabs h

@[to_additive]

Depends on / 依赖: le_max_of_le_left, le_total, mabs_le_max_mabs_mabs, mabs_of_one_le, max_eq_left, max_eq_right, min_eq_left, min_eq_right, mk_le_mk_of_mabs, mk_mabs, one_le_mabs
-/
theorem min_le_mk_of_le_of_le {x y z : M} (hy : y <= x) (hz : x <= z) : min (mk y) (mk z) <= mk x := by
  have H := mabs_le_max_mabs_mabs hy hz
  rw [← mabs_of_one_le (le_max_of_le_left (one_le_mabs y))] at H
  apply (mk_le_mk_of_mabs H).trans'
  obtain h | h := le_total |y|ₘ |z|ₘ
  · rw [max_eq_right h, min_eq_right, mk_mabs]
    exact mk_le_mk_of_mabs h
  · rw [max_eq_left h, min_eq_left, mk_mabs]
    exact mk_le_mk_of_mabs h

@[to_additive]
/--
theorem `min_le_mk_mul` / 定理 `min_le_mk_mul`

English:
theorem min_le_mk_mul
  given: (a b : M)
  statement: min (mk a) (mk b) <= mk (a * b)
  proof: by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (mk_lt_mk.mp h.1 2).trans_le (mabs_mul_le _ _)
  have h2 := (mk_lt_mk.mp h.2 2).trans_le (mabs_mul_le _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_gt h2

@[to_additive]

中文:
定理 min_le_mk_mul
  条件: (a b : M)
  结论: 最小值 (mk a) (mk b) <= mk (a * b)
  证明: by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (mk_lt_mk.mp h.1 2).trans_le (mabs_mul_le _ _)
  have h2 := (mk_lt_mk.mp h.2 2).trans_le (mabs_mul_le _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_gt h2

@[to_additive]

Depends on / 依赖: h1.not_gt, lt_min_iff, mabs_mul_le, mk_lt_mk, mk_lt_mk.mp, mul_lt_mul_iff_left, mul_lt_mul_iff_right, not_gt, pow_two, trans_le
-/
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) <= mk (a * b) := by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (mk_lt_mk.mp h.1 2).trans_le (mabs_mul_le _ _)
  have h2 := (mk_lt_mk.mp h.2 2).trans_le (mabs_mul_le _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_gt h2

@[to_additive]
/--
theorem `min_le_mk_div` / 定理 `min_le_mk_div`

English:
theorem min_le_mk_div
  given: (a b : M)
  statement: min (mk a) (mk b) <= mk (a / b)
  proof: by
  simpa [div_eq_mul_inv] using min_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]

中文:
定理 min_le_mk_div
  条件: (a b : M)
  结论: 最小值 (mk a) (mk b) <= mk (a / b)
  证明: by
  simpa [div_eq_mul_inv] using min_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, min_le_mk_mul
-/
theorem min_le_mk_div (a b : M) : min (mk a) (mk b) <= mk (a / b) := by
  simpa [div_eq_mul_inv] using min_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]
/--
theorem `mk_left_le_mk_mul` / 定理 `mk_left_le_mk_mul`

English:
theorem mk_left_le_mk_mul
  given: (hab : mk a <= mk b)
  statement: mk a <= mk (a * b)
  proof: by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]

中文:
定理 mk_left_le_mk_mul
  条件: (hab : mk a <= mk b)
  结论: mk a <= mk (a * b)
  证明: by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]

Depends on / 依赖: min_le_mk_mul
-/
theorem mk_left_le_mk_mul (hab : mk a <= mk b) : mk a <= mk (a * b) := by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
/--
theorem `mk_right_le_mk_mul` / 定理 `mk_right_le_mk_mul`

English:
theorem mk_right_le_mk_mul
  given: (hba : mk b <= mk a)
  statement: mk b <= mk (a * b)
  proof: by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]

中文:
定理 mk_right_le_mk_mul
  条件: (hba : mk b <= mk a)
  结论: mk b <= mk (a * b)
  证明: by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]

Depends on / 依赖: min_le_mk_mul
-/
theorem mk_right_le_mk_mul (hba : mk b <= mk a) : mk b <= mk (a * b) := by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
/--
theorem `mk_left_le_mk_div` / 定理 `mk_left_le_mk_div`

English:
theorem mk_left_le_mk_div
  given: (hab : mk a <= mk b)
  statement: mk a <= mk (a / b)
  proof: by
  simpa [div_eq_mul_inv, hab] using mk_left_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]

中文:
定理 mk_left_le_mk_div
  条件: (hab : mk a <= mk b)
  结论: mk a <= mk (a / b)
  证明: by
  simpa [div_eq_mul_inv, hab] using mk_left_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mk_left_le_mk_mul
-/
theorem mk_left_le_mk_div (hab : mk a <= mk b) : mk a <= mk (a / b) := by
  simpa [div_eq_mul_inv, hab] using mk_left_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]
/--
theorem `mk_right_le_mk_div` / 定理 `mk_right_le_mk_div`

English:
theorem mk_right_le_mk_div
  given: (hba : mk b <= mk a)
  statement: mk b <= mk (a / b)
  proof: by
  simpa [div_eq_mul_inv, hba] using mk_right_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive (attr := simp)]

中文:
定理 mk_right_le_mk_div
  条件: (hba : mk b <= mk a)
  结论: mk b <= mk (a / b)
  证明: by
  simpa [div_eq_mul_inv, hba] using mk_right_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mk_right_le_mk_mul
-/
theorem mk_right_le_mk_div (hba : mk b <= mk a) : mk b <= mk (a / b) := by
  simpa [div_eq_mul_inv, hba] using mk_right_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive (attr := simp)]
/--
theorem `mk_left_le_mk_mul_iff` / 定理 `mk_left_le_mk_mul_iff`

English:
theorem mk_left_le_mk_mul_iff
  statement: mk a <= mk (a * b) ↔ mk a <= mk b where
  proof: by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_mul

@[to_additive (attr := simp)]

中文:
定理 mk_left_le_mk_mul_iff
  结论: mk a <= mk (a * b) ↔ mk a <= mk b where
  证明: by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_mul

@[to_additive (attr := simp)]

Depends on / 依赖: mk_left_le_mk_div, mk_left_le_mk_mul
-/
theorem mk_left_le_mk_mul_iff : mk a <= mk (a * b) ↔ mk a <= mk b where
  mp h := by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_mul

@[to_additive (attr := simp)]
/--
theorem `mk_right_le_mk_mul_iff` / 定理 `mk_right_le_mk_mul_iff`

English:
theorem mk_right_le_mk_mul_iff
  statement: mk b <= mk (a * b) ↔ mk b <= mk a
  proof: by
  rw [mul_comm]; rw [mk_left_le_mk_mul_iff]

@[to_additive (attr := simp)]

中文:
定理 mk_right_le_mk_mul_iff
  结论: mk b <= mk (a * b) ↔ mk b <= mk a
  证明: by
  rw [mul_comm]; rw [mk_left_le_mk_mul_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: mk_left_le_mk_mul_iff, mul_comm
-/
theorem mk_right_le_mk_mul_iff : mk b <= mk (a * b) ↔ mk b <= mk a := by
  rw [mul_comm]; rw [mk_left_le_mk_mul_iff]

@[to_additive (attr := simp)]
/--
theorem `mk_left_le_mk_div_iff` / 定理 `mk_left_le_mk_div_iff`

English:
theorem mk_left_le_mk_div_iff
  statement: mk a <= mk (a / b) ↔ mk a <= mk b where
  proof: by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_div

@[to_additive (attr := simp)]

中文:
定理 mk_left_le_mk_div_iff
  结论: mk a <= mk (a / b) ↔ mk a <= mk b where
  证明: by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_div

@[to_additive (attr := simp)]

Depends on / 依赖: mk_left_le_mk_div
-/
theorem mk_left_le_mk_div_iff : mk a <= mk (a / b) ↔ mk a <= mk b where
  mp h := by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_div

@[to_additive (attr := simp)]
/--
theorem `mk_right_le_mk_div_iff` / 定理 `mk_right_le_mk_div_iff`

English:
theorem mk_right_le_mk_div_iff
  statement: mk b <= mk (a / b) ↔ mk b <= mk a
  proof: by
  rw [mk_div_comm]; rw [mk_left_le_mk_div_iff]

@[to_additive (attr := simp)]

中文:
定理 mk_right_le_mk_div_iff
  结论: mk b <= mk (a / b) ↔ mk b <= mk a
  证明: by
  rw [mk_div_comm]; rw [mk_left_le_mk_div_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: mk_div_comm, mk_left_le_mk_div_iff
-/
theorem mk_right_le_mk_div_iff : mk b <= mk (a / b) ↔ mk b <= mk a := by
  rw [mk_div_comm]; rw [mk_left_le_mk_div_iff]

@[to_additive (attr := simp)]
/--
theorem `mk_mul_lt_mk_left_iff` / 定理 `mk_mul_lt_mk_left_iff`

English:
theorem mk_mul_lt_mk_left_iff
  statement: mk (a * b) < mk a ↔ mk b < mk a
  proof: le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_mul_iff

@[to_additive (attr := simp)]

中文:
定理 mk_mul_lt_mk_left_iff
  结论: mk (a * b) < mk a ↔ mk b < mk a
  证明: le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_mul_iff

@[to_additive (attr := simp)]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, mk_left_le_mk_mul_iff
-/
theorem mk_mul_lt_mk_left_iff : mk (a * b) < mk a ↔ mk b < mk a :=
  le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_mul_iff

@[to_additive (attr := simp)]
/--
theorem `mk_mul_lt_mk_right_iff` / 定理 `mk_mul_lt_mk_right_iff`

English:
theorem mk_mul_lt_mk_right_iff
  statement: mk (a * b) < mk b ↔ mk a < mk b
  proof: le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_mul_iff

@[to_additive (attr := simp)]

中文:
定理 mk_mul_lt_mk_right_iff
  结论: mk (a * b) < mk b ↔ mk a < mk b
  证明: le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_mul_iff

@[to_additive (attr := simp)]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, mk_right_le_mk_mul_iff
-/
theorem mk_mul_lt_mk_right_iff : mk (a * b) < mk b ↔ mk a < mk b :=
  le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_mul_iff

@[to_additive (attr := simp)]
/--
theorem `mk_div_lt_mk_left_iff` / 定理 `mk_div_lt_mk_left_iff`

English:
theorem mk_div_lt_mk_left_iff
  statement: mk (a / b) < mk a ↔ mk b < mk a
  proof: le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_div_iff

@[to_additive (attr := simp)]

中文:
定理 mk_div_lt_mk_left_iff
  结论: mk (a / b) < mk a ↔ mk b < mk a
  证明: le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_div_iff

@[to_additive (attr := simp)]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, mk_left_le_mk_div_iff
-/
theorem mk_div_lt_mk_left_iff : mk (a / b) < mk a ↔ mk b < mk a :=
  le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_div_iff

@[to_additive (attr := simp)]
/--
theorem `mk_div_lt_mk_right_iff` / 定理 `mk_div_lt_mk_right_iff`

English:
theorem mk_div_lt_mk_right_iff
  statement: mk (a / b) < mk b ↔ mk a < mk b
  proof: le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_div_iff

@[to_additive]

中文:
定理 mk_div_lt_mk_right_iff
  结论: mk (a / b) < mk b ↔ mk a < mk b
  证明: le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_div_iff

@[to_additive]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, mk_right_le_mk_div_iff
-/
theorem mk_div_lt_mk_right_iff : mk (a / b) < mk b ↔ mk a < mk b :=
  le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_div_iff

@[to_additive]
/--
theorem `mk_mul_eq_mk_left` / 定理 `mk_mul_eq_mk_left`

English:
theorem mk_mul_eq_mk_left
  given: (h : mk a < mk b)
  statement: mk (a * b) = mk a
  proof: by
  refine le_antisymm (mk_le_mk.mpr ⟨2, ?_⟩) (mk_left_le_mk_mul h.le)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a]; rw [pow_two]; rw [mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]

中文:
定理 mk_mul_eq_mk_left
  条件: (h : mk a < mk b)
  结论: mk (a * b) = mk a
  证明: by
  refine le_antisymm (mk_le_mk.mpr ⟨2, ?_⟩) (mk_left_le_mk_mul h.le)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a]; rw [pow_two]; rw [mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]

Depends on / 依赖: h.le, le_antisymm, le_of_mul_le_mul_left, mabs_mul, mk_le_mk, mk_le_mk.mpr, mk_left_le_mk_mul, mk_lt_mk, mul_comm, mul_le_mul_iff_right, pow_two
-/
theorem mk_mul_eq_mk_left (h : mk a < mk b) : mk (a * b) = mk a := by
  refine le_antisymm (mk_le_mk.mpr ⟨2, ?_⟩) (mk_left_le_mk_mul h.le)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a]; rw [pow_two]; rw [mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]
/--
theorem `mk_mul_eq_mk_right` / 定理 `mk_mul_eq_mk_right`

English:
theorem mk_mul_eq_mk_right
  given: (h : mk b < mk a)
  statement: mk (a * b) = mk b
  proof: mul_comm a b ▸ mk_mul_eq_mk_left h

@[to_additive]

中文:
定理 mk_mul_eq_mk_right
  条件: (h : mk b < mk a)
  结论: mk (a * b) = mk b
  证明: mul_comm a b ▸ mk_mul_eq_mk_left h

@[to_additive]

Depends on / 依赖: mk_mul_eq_mk_left, mul_comm
-/
theorem mk_mul_eq_mk_right (h : mk b < mk a) : mk (a * b) = mk b :=
  mul_comm a b ▸ mk_mul_eq_mk_left h

@[to_additive]
/--
theorem `mk_div_eq_mk_left` / 定理 `mk_div_eq_mk_left`

English:
theorem mk_div_eq_mk_left
  given: (h : mk a < mk b)
  statement: mk (a / b) = mk a
  proof: by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_left (a := a) (b := b⁻¹)

@[to_additive]

中文:
定理 mk_div_eq_mk_left
  条件: (h : mk a < mk b)
  结论: mk (a / b) = mk a
  证明: by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_left (a := a) (b := b⁻¹)

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mk_mul_eq_mk_left
-/
theorem mk_div_eq_mk_left (h : mk a < mk b) : mk (a / b) = mk a := by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_left (a := a) (b := b⁻¹)

@[to_additive]
/--
theorem `mk_div_eq_mk_right` / 定理 `mk_div_eq_mk_right`

English:
theorem mk_div_eq_mk_right
  given: (h : mk b < mk a)
  statement: mk (a / b) = mk b
  proof: by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_right (a := a) (b := b⁻¹)

中文:
定理 mk_div_eq_mk_right
  条件: (h : mk b < mk a)
  结论: mk (a / b) = mk b
  证明: by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_right (a := a) (b := b⁻¹)

Depends on / 依赖: div_eq_mul_inv, mk_mul_eq_mk_right
-/
theorem mk_div_eq_mk_right (h : mk b < mk a) : mk (a / b) = mk b := by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_right (a := a) (b := b⁻¹)

/-- The product over a set of an elements in distinct classes is in the lowest class. -/
@[to_additive /-- The sum over a set of an elements in distinct classes is in the lowest class. -/]
/--
theorem `mk_prod` / 定理 `mk_prod`

English:
theorem mk_prod
  statement: {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
  proof: by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs in (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : mk (a i) != mk (a (s.min' hs)) := by
      by_contra h
      obtain eq := hmono.injOn (by simp) hminmem h
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt | hlt := lt_or_gt_of_ne hne
    · rw [mk_mul_eq_mk_left hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, mk_mul_eq_mk_left hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

@[to_additive]

中文:
定理 mk_prod
  结论: {ι : 类型} [线性序 ι] {s : 有限集 ι} (hnonempty : s.非空)
  证明: by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs in (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : mk (a i) != mk (a (s.min' hs)) := by
      by_contra h
      obtain eq := hmono.injOn (by simp) hminmem h
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt | hlt := lt_or_gt_of_ne hne
    · rw [mk_mul_eq_mk_left hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, mk_mul_eq_mk_left hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

@[to_additive]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.cons, Finset.mem_cons_of_mem, Finset.min, Finset.prod_cons, Nonempty, _mem, cons_induction, hminmem, hmono.injOn, hmono.mono, hnonempty, lt_or_gt_of_ne, mem_cons_of_mem, mk_mul_, prod_cons, s.min, singleton
-/
theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι -> M} :
    StrictMonoOn (mk ∘ a) s -> mk (∏ i in s, (a i)) = mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs in (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : mk (a i) != mk (a (s.min' hs)) := by
      by_contra h
      obtain eq := hmono.injOn (by simp) hminmem h
      rw [eq] at hi
      exact hi (Finset.min'_mem _ hs)
    rw [← ih] at hne
    obtain hlt | hlt := lt_or_gt_of_ne hne
    · rw [mk_mul_eq_mk_left hlt]
      congr
      apply le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ (by simp))
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · rfl
      · refine (lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)).le
        apply (hmono.lt_iff_lt (by simp) hminmem).mp
        rw [ih] at hlt
        exact hlt
    · rw [mul_comm, mk_mul_eq_mk_left hlt, ih]
      congr 2
      refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ hminmem)
      intro y hy
      obtain rfl | hmem := Finset.mem_cons.mp hy
      · apply ((hmono.lt_iff_lt hminmem (by simp)).mp ?_).le
        rw [ih] at hlt
        exact hlt
      · exact Finset.min'_le _ _ hmem

@[to_additive]
/--
theorem `lt_of_mk_lt_mk_of_one_le` / 定理 `lt_of_mk_lt_mk_of_one_le`

English:
theorem lt_of_mk_lt_mk_of_one_le
  given: (h : mk a < mk b) (hpos : 1 <= a)
  statement: b < a
  proof: by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]

中文:
定理 lt_of_mk_lt_mk_of_one_le
  条件: (h : mk a < mk b) (hpos : 1 <= a)
  结论: b < a
  证明: by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]

Depends on / 依赖: mabs_eq_self, mabs_eq_self.mpr, mabs_lt, mk_lt_mk, mk_lt_mk.mp, pow_one
-/
theorem lt_of_mk_lt_mk_of_one_le (h : mk a < mk b) (hpos : 1 <= a) : b < a := by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]
/--
theorem `lt_of_mk_lt_mk_of_le_one` / 定理 `lt_of_mk_lt_mk_of_le_one`

English:
theorem lt_of_mk_lt_mk_of_le_one
  given: (h : mk a < mk b) (hneg : a <= 1)
  statement: a < b
  proof: by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_inv_self.mpr hneg]; rw [inv_inv] at h
  exact h.1

@[to_additive]

中文:
定理 lt_of_mk_lt_mk_of_le_one
  条件: (h : mk a < mk b) (hneg : a <= 1)
  结论: a < b
  证明: by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_inv_self.mpr hneg]; rw [inv_inv] at h
  exact h.1

@[to_additive]

Depends on / 依赖: inv_inv, mabs_eq_inv_self, mabs_eq_inv_self.mpr, mabs_lt, mk_lt_mk, mk_lt_mk.mp, pow_one
-/
theorem lt_of_mk_lt_mk_of_le_one (h : mk a < mk b) (hneg : a <= 1) : a < b := by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one]; rw [mabs_lt]; rw [mabs_eq_inv_self.mpr hneg]; rw [inv_inv] at h
  exact h.1

@[to_additive]
/--
theorem `one_lt_of_one_lt_of_mk_lt` / 定理 `one_lt_of_one_lt_of_mk_lt`

English:
theorem one_lt_of_one_lt_of_mk_lt
  given: (ha : 1 < a) (hab : mk a < mk (b / a))
  proof: by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

@[to_additive archimedean_of_mk_eq_mk]

中文:
定理 one_lt_of_one_lt_of_mk_lt
  条件: (ha : 1 < a) (hab : mk a < mk (b / a))
  证明: by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

@[to_additive archimedean_of_mk_eq_mk]

Depends on / 依赖: ha.le, lt_of_mk_lt_mk_of_le_one
-/
theorem one_lt_of_one_lt_of_mk_lt (ha : 1 < a) (hab : mk a < mk (b / a)) :
    1 < b := by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

@[to_additive archimedean_of_mk_eq_mk]
/--
theorem `mulArchimedean_of_mk_eq_mk` / 定理 `mulArchimedean_of_mk_eq_mk`

English:
theorem mulArchimedean_of_mk_eq_mk
  given: (h : forall a != (1 : M), forall b != 1, mk a = mk b)
  proof: by
    by_cases! hx : x <= 1
    · use 0
      simpa using hx
    · have hxy : mk x = mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := mk_eq_mk.mp hxy
      rw [mabs_eq_self.mpr hx.le]; rw [mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]

中文:
定理 mulArchimedean_of_mk_eq_mk
  条件: (h : 对任意 a != (1 : M), 对任意 b != 1, mk a = mk b)
  证明: by
    by_cases! hx : x <= 1
    · use 0
      simpa using hx
    · have hxy : mk x = mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := mk_eq_mk.mp hxy
      rw [mabs_eq_self.mpr hx.le]; rw [mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]

Depends on / 依赖: hx.le, hx.ne.symm, hy.le, hy.ne.symm, mabs_eq_self, mabs_eq_self.mpr, mk_eq_mk, mk_eq_mk.mp
-/
theorem mulArchimedean_of_mk_eq_mk (h : forall a != (1 : M), forall b != 1, mk a = mk b) :
    MulArchimedean M where
  arch x y hy := by
    by_cases! hx : x <= 1
    · use 0
      simpa using hx
    · have hxy : mk x = mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := mk_eq_mk.mp hxy
      rw [mabs_eq_self.mpr hx.le]; rw [mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]
/--
theorem `mk_eq_mk_of_mulArchimedean` / 定理 `mk_eq_mk_of_mulArchimedean`

English:
theorem mk_eq_mk_of_mulArchimedean
  given: [MulArchimedean M] (ha : a != 1) (hb : b != 1)
  proof: by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact mk_eq_mk.mpr ⟨hm, hn⟩

中文:
定理 mk_eq_mk_of_mulArchimedean
  条件: [MulArchimedean M] (ha : a != 1) (hb : b != 1)
  证明: by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact mk_eq_mk.mpr ⟨hm, hn⟩

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, mk_eq_mk, mk_eq_mk.mpr
-/
theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a != 1) (hb : b != 1) :
    mk a = mk b := by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact mk_eq_mk.mpr ⟨hm, hn⟩

section Hom
variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/
@[to_additive
/-- An `OrderAddMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/]
/--
Definition of `orderHom` / `orderHom` 的定义

English:
definition orderHom
  signature: (f : M ->*o N)
  body: (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]

中文:
定义 orderHom
  签名: (f : M ->*o N)
  定义体: (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]

Depends on / 依赖: MulArchimedeanOrder, MulArchimedeanOrder.orderHom, antisymmetrization, orderHom
-/
def orderHom (f : M ->*o N) : MulArchimedeanClass M ->o MulArchimedeanClass N :=
  (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]
/--
theorem `orderHom_mk` / 定理 `orderHom_mk`

English:
theorem orderHom_mk
  given: (f : M ->*o N) (a : M)
  statement: orderHom f (mk a) = mk (f a)
  proof: rfl

@[to_additive]

中文:
定理 orderHom_mk
  条件: (f : M ->*o N) (a : M)
  结论: orderHom f (mk a) = mk (f a)
  证明: rfl

@[to_additive]
-/
theorem orderHom_mk (f : M ->*o N) (a : M) : orderHom f (mk a) = mk (f a) := rfl

@[to_additive]
/--
theorem `map_mk_eq` / 定理 `map_mk_eq`

English:
theorem map_mk_eq
  given: (f : M ->*o N) (h : mk a = mk b)
  statement: mk (f a) = mk (f b)
  proof: by
  rw [← orderHom_mk]; rw [← orderHom_mk]; rw [h]

@[to_additive]

中文:
定理 map_mk_eq
  条件: (f : M ->*o N) (h : mk a = mk b)
  结论: mk (f a) = mk (f b)
  证明: by
  rw [← orderHom_mk]; rw [← orderHom_mk]; rw [h]

@[to_additive]

Depends on / 依赖: orderHom_mk
-/
theorem map_mk_eq (f : M ->*o N) (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [← orderHom_mk]; rw [← orderHom_mk]; rw [h]

@[to_additive]
/--
theorem `map_mk_le` / 定理 `map_mk_le`

English:
theorem map_mk_le
  given: (f : M ->*o N) (h : mk a <= mk b)
  statement: mk (f a) <= mk (f b)
  proof: by
  rw [← orderHom_mk]; rw [← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]

中文:
定理 map_mk_le
  条件: (f : M ->*o N) (h : mk a <= mk b)
  结论: mk (f a) <= mk (f b)
  证明: by
  rw [← orderHom_mk]; rw [← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]

Depends on / 依赖: OrderHomClass, OrderHomClass.monotone, monotone, orderHom_mk
-/
theorem map_mk_le (f : M ->*o N) (h : mk a <= mk b) : mk (f a) <= mk (f b) := by
  rw [← orderHom_mk]; rw [← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]
/--
theorem `orderHom_injective` / 定理 `orderHom_injective`

English:
theorem orderHom_injective
  given: {f : M ->*o N} (h : Function.Injective f)
  proof: by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]

中文:
定理 orderHom_injective
  条件: {f : M ->*o N} (h : 函数.单射 f)
  证明: by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: OrderHomClass, OrderHomClass.monotone, hmono.le_iff_le.mp, le_iff_le, map_mabs, map_pow, mk_eq_mk, monotone, orderHom_mk, simp_rw, strictMono_of_injective
-/
theorem orderHom_injective {f : M ->*o N} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]
/--
theorem `orderHom_top` / 定理 `orderHom_top`

English:
theorem orderHom_top
  given: (f : M ->*o N)
  statement: orderHom f ⊤ = ⊤
  proof: by
  rw [← mk_one]; rw [← mk_one]; rw [orderHom_mk]; rw [map_one]

中文:
定理 orderHom_top
  条件: (f : M ->*o N)
  结论: orderHom f ⊤ = ⊤
  证明: by
  rw [← mk_one]; rw [← mk_one]; rw [orderHom_mk]; rw [map_one]

Depends on / 依赖: map_one, mk_one, orderHom_mk
-/
theorem orderHom_top (f : M ->*o N) : orderHom f ⊤ = ⊤ := by
  rw [← mk_one]; rw [← mk_one]; rw [orderHom_mk]; rw [map_one]

end Hom

section LiftHom

variable {α : Type*} [PartialOrder α]

/-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `MulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `ArchimedeanClass M →o α`. -/]
/--
Definition of `liftOrderHom` / `liftOrderHom` 的定义

English:
definition liftOrderHom
  signature: (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b)
  body: lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hle := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa using h a b (mk_le_mk.mp hle)

@[to_additive (attr := simp)]

中文:
定义 liftOrderHom
  签名: (f : M -> α) (h : 对任意 a b, mk a <= mk b -> f a <= f b)
  定义体: lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hle := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa using h a b (mk_le_mk.mp hle)

@[to_additive (attr := simp)]

Depends on / 依赖: heq.ge, heq.le, le_antisymm
-/
def liftOrderHom (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b) :
    MulArchimedeanClass M ->o α where
  toFun := lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hle := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa using h a b (mk_le_mk.mp hle)

@[to_additive (attr := simp)]
/--
theorem `liftOrderHom_mk` / 定理 `liftOrderHom_mk`

English:
theorem liftOrderHom_mk
  given: (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b) (a : M)
  proof: lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) a

中文:
定理 liftOrderHom_mk
  条件: (f : M -> α) (h : 对任意 a b, mk a <= mk b -> f a <= f b) (a : M)
  证明: lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) a

Depends on / 依赖: heq.ge, heq.le, le_antisymm, lift_mk
-/
theorem liftOrderHom_mk (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b) (a : M) :
    liftOrderHom f h (mk a) = f a :=
  lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) a

end LiftHom

/-- Given a `UpperSet` of `MulArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/
@[to_additive /-- Given a `UpperSet` of `ArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/]
/--
Definition of `subsemigroup` / `subsemigroup` 的定义

English:
definition subsemigroup
  signature: (s : UpperSet (MulArchimedeanClass M))
  body: mk ⁻¹' s
  mul_mem' {a b} ha hb := by
    rw [Set.mem_preimage] at ha hb ⊢
    obtain h | h := min_le_iff.mp (min_le_mk_mul a b)
    · exact s.upper h ha
    · exact s.upper h hb

@[to_additive]

中文:
定义 subsemigroup
  签名: (s : 上集 (MulArchimedeanClass M))
  定义体: mk ⁻¹' s
  mul_mem' {a b} ha hb := by
    rw [Set.mem_preimage] at ha hb ⊢
    obtain h | h := min_le_iff.mp (min_le_mk_mul a b)
    · exact s.upper h ha
    · exact s.upper h hb

@[to_additive]
-/
def subsemigroup (s : UpperSet (MulArchimedeanClass M)) : Subsemigroup M where
  carrier := mk ⁻¹' s
  mul_mem' {a b} ha hb := by
    rw [Set.mem_preimage] at ha hb ⊢
    obtain h | h := min_le_iff.mp (min_le_mk_mul a b)
    · exact s.upper h ha
    · exact s.upper h hb

@[to_additive]
/--
theorem `subsemigroup_strictAnti` / 定理 `subsemigroup_strictAnti`

English:
theorem subsemigroup_strictAnti
  statement: StrictAnti (subsemigroup (M := M))
  proof: by
  intro s t hst
  rw [← SetLike.coe_ssubset_coe]
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => hst.le h, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

中文:
定理 subsemigroup_strictAnti
  结论: 严格递减 (subsemigroup (M := M))
  证明: by
  intro s t hst
  rw [← SetLike.coe_ssubset_coe]
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => hst.le h, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup, Set.ssubset_iff_subset_ne.mpr, SetLike, SetLike.coe_ssubset_coe, coe_ssubset_coe, contrapose, hst.le, le_of_eq, mk_surjective, ssubset_iff_subset_ne, subsemigroup
-/
theorem subsemigroup_strictAnti : StrictAnti (subsemigroup (M := M)) := by
  intro s t hst
  rw [← SetLike.coe_ssubset_coe]
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => hst.le h, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

/-- Make `MulArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/
@[to_additive /-- Make `ArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/]
noncomputable
/--
Definition of `subgroup` / `subgroup` 的定义

English:
definition subgroup
  signature: (s : UpperSet (MulArchimedeanClass M))
  body: if hs : s = ⊤ then
    ⊥
  else {
    subsemigroup s with
    one_mem' := by
      rw [subsemigroup]; rw [Set.mem_preimage]
      obtain ⟨u, hu⟩ := UpperSet.coe_nonempty.mpr hs
      simpa using s.upper (by simp) hu
    inv_mem' := by simp [subsemigroup]
  }

中文:
定义 subgroup
  签名: (s : 上集 (MulArchimedeanClass M))
  定义体: if hs : s = ⊤ then
    ⊥
  else {
    subsemigroup s with
    one_mem' := by
      rw [subsemigroup]; rw [Set.mem_preimage]
      obtain ⟨u, hu⟩ := UpperSet.coe_nonempty.mpr hs
      simpa using s.upper (by simp) hu
    inv_mem' := by simp [subsemigroup]
  }

Depends on / 依赖: Set.mem_preimage, UpperSet, UpperSet.coe_nonempty.mpr, coe_nonempty, inv_mem, mem_preimage, one_mem, s.upper, subsemigroup
-/
def subgroup (s : UpperSet (MulArchimedeanClass M)) : Subgroup M :=
  if hs : s = ⊤ then
    ⊥
  else {
    subsemigroup s with
    one_mem' := by
      rw [subsemigroup]; rw [Set.mem_preimage]
      obtain ⟨u, hu⟩ := UpperSet.coe_nonempty.mpr hs
      simpa using s.upper (by simp) hu
    inv_mem' := by simp [subsemigroup]
  }

variable {s : UpperSet (MulArchimedeanClass M)}

@[to_additive]
/--
theorem `subsemigroup_eq_subgroup_of_ne_top` / 定理 `subsemigroup_eq_subgroup_of_ne_top`

English:
theorem subsemigroup_eq_subgroup_of_ne_top
  given: (hs : s != ⊤)
  proof: by
  simp [subgroup, hs]

中文:
定理 subsemigroup_eq_subgroup_of_ne_top
  条件: (hs : s != ⊤)
  证明: by
  simp [subgroup, hs]

Depends on / 依赖: subgroup
-/
theorem subsemigroup_eq_subgroup_of_ne_top (hs : s != ⊤) :
    subsemigroup s = (subgroup s : Set M) := by
  simp [subgroup, hs]

variable (M) in
@[to_additive (attr := simp)]
/--
theorem `subgroup_eq_bot` / 定理 `subgroup_eq_bot`

English:
theorem subgroup_eq_bot
  statement: subgroup (M := M) ⊤ = ⊥
  proof: by
  simp [subgroup]

@[to_additive (attr := simp)]

中文:
定理 subgroup_eq_bot
  结论: subgroup (M := M) ⊤ = ⊥
  证明: by
  simp [subgroup]

@[to_additive (attr := simp)]

Depends on / 依赖: subgroup
-/
theorem subgroup_eq_bot : subgroup (M := M) ⊤ = ⊥ := by
  simp [subgroup]

@[to_additive (attr := simp)]
/--
theorem `mem_subgroup_iff` / 定理 `mem_subgroup_iff`

English:
theorem mem_subgroup_iff
  given: (hs : s != ⊤)
  statement: a in subgroup s ↔ mk a in s
  proof: by
  simp [subgroup, subsemigroup, hs]

@[to_additive]

中文:
定理 mem_subgroup_iff
  条件: (hs : s != ⊤)
  结论: a in subgroup s ↔ mk a in s
  证明: by
  simp [subgroup, subsemigroup, hs]

@[to_additive]

Depends on / 依赖: subgroup, subsemigroup
-/
theorem mem_subgroup_iff (hs : s != ⊤) : a in subgroup s ↔ mk a in s := by
  simp [subgroup, subsemigroup, hs]

@[to_additive]
/--
theorem `subgroup_strictAntiOn` / 定理 `subgroup_strictAntiOn`

English:
theorem subgroup_strictAntiOn
  statement: StrictAntiOn (subgroup (M := M)) (Set.Iio ⊤)
  proof: by
  intro s hs t ht hst
  rw [← SetLike.coe_ssubset_coe]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp hs).ne_top]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp ht).ne_top]
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simpa [subsemigroup] using hst.le, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [mk_surjective, subsemigroup] using heq

@[to_additive]

中文:
定理 subgroup_strictAntiOn
  结论: StrictAntiOn (subgroup (M := M)) (集合.左无界右开区间 ⊤)
  证明: by
  intro s hs t ht hst
  rw [← SetLike.coe_ssubset_coe]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp hs).ne_top]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp ht).ne_top]
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simpa [subsemigroup] using hst.le, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [mk_surjective, subsemigroup] using heq

@[to_additive]

Depends on / 依赖: Set.Iio, Set.mem_Iio.mp, Set.ssubset_iff_subset_ne.mpr, SetLike, SetLike.coe_ssubset_coe, coe_ssubset_coe, contrapose, hst.le, le_of_eq, mem_Iio, mk_surjective, ne_top, ssubset_iff_subset_ne, subsemigroup, subsemigroup_eq_subgroup_of_ne_top
-/
theorem subgroup_strictAntiOn : StrictAntiOn (subgroup (M := M)) (Set.Iio ⊤) := by
  intro s hs t ht hst
  rw [← SetLike.coe_ssubset_coe]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp hs).ne_top]
  rw [← subsemigroup_eq_subgroup_of_ne_top (Set.mem_Iio.mp ht).ne_top]
  refine Set.ssubset_iff_subset_ne.mpr ⟨by simpa [subsemigroup] using hst.le, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [mk_surjective, subsemigroup] using heq

@[to_additive]
/--
theorem `subgroup_antitone` / 定理 `subgroup_antitone`

English:
theorem subgroup_antitone
  statement: Antitone (subgroup (M := M))
  proof: by
  intro s t hst
  obtain rfl | hs := eq_or_ne s ⊤
  · rw [eq_top_iff.mpr hst]
  obtain rfl | ht := eq_or_ne t ⊤
  · simp
  rwa [subgroup_strictAntiOn.le_iff_ge ht.lt_top hs.lt_top]

中文:
定理 subgroup_antitone
  结论: 递减 (subgroup (M := M))
  证明: by
  intro s t hst
  obtain rfl | hs := eq_or_ne s ⊤
  · rw [eq_top_iff.mpr hst]
  obtain rfl | ht := eq_or_ne t ⊤
  · simp
  rwa [subgroup_strictAntiOn.le_iff_ge ht.lt_top hs.lt_top]

Depends on / 依赖: eq_or_ne, eq_top_iff, eq_top_iff.mpr, hs.lt_top, ht.lt_top, le_iff_ge, lt_top, subgroup_strictAntiOn, subgroup_strictAntiOn.le_iff_ge
-/
theorem subgroup_antitone : Antitone (subgroup (M := M)) := by
  intro s t hst
  obtain rfl | hs := eq_or_ne s ⊤
  · rw [eq_top_iff.mpr hst]
  obtain rfl | ht := eq_or_ne t ⊤
  · simp
  rwa [subgroup_strictAntiOn.le_iff_ge ht.lt_top hs.lt_top]

/-- An open ball defined by `MulArchimedeanClass.subgroup` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`. -/
@[to_additive /--An open ball defined by `ArchimedeanClass.addSubgroup` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`. -/]
noncomputable
/--
Definition of `ballSubgroup` / `ballSubgroup` 的定义

English:
abbreviation ballSubgroup
  signature: (c : MulArchimedeanClass M)
  body: subgroup (UpperSet.Ioi c)

中文:
缩写 ballSubgroup
  签名: (c : MulArchimedeanClass M)
  定义体: subgroup (UpperSet.Ioi c)

Depends on / 依赖: UpperSet, UpperSet.Ioi, subgroup
-/
abbrev ballSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ioi c)

/-- A closed ball defined by `MulArchimedeanClass.subgroup` of `UpperSet.Ici c`. -/
@[to_additive /-- A closed ball defined by `ArchimedeanClass.addSubgroup` of `UpperSet.Ici c`. -/]
noncomputable
/--
Definition of `closedBallSubgroup` / `closedBallSubgroup` 的定义

English:
abbreviation closedBallSubgroup
  signature: (c : MulArchimedeanClass M)
  body: subgroup (UpperSet.Ici c)

@[to_additive]

中文:
缩写 closedBallSubgroup
  签名: (c : MulArchimedeanClass M)
  定义体: subgroup (UpperSet.Ici c)

@[to_additive]

Depends on / 依赖: UpperSet, UpperSet.Ici, subgroup
-/
abbrev closedBallSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ici c)

@[to_additive]
/--
theorem `mem_ballSubgroup_iff` / 定理 `mem_ballSubgroup_iff`

English:
theorem mem_ballSubgroup_iff
  given: {a : M} {c : MulArchimedeanClass M} (hA : c != ⊤)
  proof: by
  simp [hA]

@[to_additive]

中文:
定理 mem_ballSubgroup_iff
  条件: {a : M} {c : MulArchimedeanClass M} (hA : c != ⊤)
  证明: by
  simp [hA]

@[to_additive]
-/
theorem mem_ballSubgroup_iff {a : M} {c : MulArchimedeanClass M} (hA : c != ⊤) :
    a in ballSubgroup c ↔ c < mk a := by
  simp [hA]

@[to_additive]
/--
theorem `mem_closedBallSubgroup_iff` / 定理 `mem_closedBallSubgroup_iff`

English:
theorem mem_closedBallSubgroup_iff
  given: {a : M} {c : MulArchimedeanClass M}
  proof: by
  simp

中文:
定理 mem_closedBallSubgroup_iff
  条件: {a : M} {c : MulArchimedeanClass M}
  证明: by
  simp
-/
theorem mem_closedBallSubgroup_iff {a : M} {c : MulArchimedeanClass M} :
    a in closedBallSubgroup c ↔ c <= mk a := by
  simp

variable (M) in
@[to_additive (attr := simp)]
/--
theorem `ballSubgroup_top` / 定理 `ballSubgroup_top`

English:
theorem ballSubgroup_top
  statement: ballSubgroup (M := M) ⊤ = ⊥
  proof: by
  convert! subgroup_eq_bot M
  simp

中文:
定理 ballSubgroup_top
  结论: ballSubgroup (M := M) ⊤ = ⊥
  证明: by
  convert! subgroup_eq_bot M
  simp

Depends on / 依赖: convert, subgroup_eq_bot
-/
theorem ballSubgroup_top : ballSubgroup (M := M) ⊤ = ⊥ := by
  convert! subgroup_eq_bot M
  simp

variable (M) in
@[to_additive (attr := simp)]
/--
theorem `closedBallSubgroup_top` / 定理 `closedBallSubgroup_top`

English:
theorem closedBallSubgroup_top
  statement: closedBallSubgroup (M := M) ⊤ = ⊥
  proof: by
  ext
  simp

@[to_additive]

中文:
定理 closedBallSubgroup_top
  结论: closedBallSubgroup (M := M) ⊤ = ⊥
  证明: by
  ext
  simp

@[to_additive]
-/
theorem closedBallSubgroup_top : closedBallSubgroup (M := M) ⊤ = ⊥ := by
  ext
  simp

@[to_additive]
/--
theorem `ballSubgroup_antitone` / 定理 `ballSubgroup_antitone`

English:
theorem ballSubgroup_antitone
  statement: Antitone (ballSubgroup (M := M))
  proof: by
  intro _ _ h
exact subgroup_antitone (UpperSet.Ioi_strictMono _).monotone h

中文:
定理 ballSubgroup_antitone
  结论: 递减 (ballSubgroup (M := M))
  证明: by
  intro _ _ h
exact subgroup_antitone (UpperSet.Ioi_strictMono _).monotone h

Depends on / 依赖: Ioi_strictMono, UpperSet, UpperSet.Ioi_strictMono, monotone, subgroup_antitone
-/
theorem ballSubgroup_antitone : Antitone (ballSubgroup (M := M)) := by
  intro _ _ h
exact subgroup_antitone (UpperSet.Ioi_strictMono _).monotone h

end MulArchimedeanClass

variable (M) in
/-- `FiniteMulArchimedeanClass M` is the quotient of the non-one elements of the group `M` by
multiplicative archimedean equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n : ℕ, |a|ₘ ≤ |b|ₘ ^ n)`.

It is defined as the subtype of non-top elements of `MulArchimedeanClass M`
(`⊤ : MulArchimedeanClass M` is the archimedean class of `1`).

This is useful since the family of non-top archimedean classes is linearly independent. -/
@[to_additive FiniteArchimedeanClass
/-- `FiniteArchimedeanClass M` is the quotient of the non-zero elements of the additive group `M` by
additive archimedean equivalence, where two elements `a` and `b` are in the same class iff
`(∃ m : ℕ, |b| ≤ m • |a|) ∧ (∃ n : ℕ, |a| ≤ n • |b|)`.

It is defined as the subtype of non-top elements of `ArchimedeanClass M`
(`⊤ : ArchimedeanClass M` is the archimedean class of `0`).

This is useful since the family of non-top archimedean classes is linearly independent. -/]
/--
Definition of `FiniteMulArchimedeanClass` / `FiniteMulArchimedeanClass` 的定义

English:
abbreviation FiniteMulArchimedeanClass
  body: {A : MulArchimedeanClass M // A != ⊤}

中文:
缩写 FiniteMulArchimedeanClass
  定义体: {A : MulArchimedeanClass M // A != ⊤}

Depends on / 依赖: MulArchimedeanClass
-/
abbrev FiniteMulArchimedeanClass := {A : MulArchimedeanClass M // A != ⊤}

namespace FiniteMulArchimedeanClass

/-- Create a `FiniteMulArchimedeanClass` from a non-one element. -/
@[to_additive /-- Create a `FiniteArchimedeanClass` from a non-zero element. -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (a : M) (h : a != 1)
  body: ⟨MulArchimedeanClass.mk a, MulArchimedeanClass.mk_eq_top_iff.not.mpr h⟩

@[to_additive (attr := simp)]

中文:
定义 mk
  签名: (a : M) (h : a != 1)
  定义体: ⟨MulArchimedeanClass.mk a, MulArchimedeanClass.mk_eq_top_iff.not.mpr h⟩

@[to_additive (attr := simp)]

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.mk, MulArchimedeanClass.mk_eq_top_iff.not.mpr, mk_eq_top_iff
-/
def mk (a : M) (h : a != 1) : FiniteMulArchimedeanClass M :=
  ⟨MulArchimedeanClass.mk a, MulArchimedeanClass.mk_eq_top_iff.not.mpr h⟩

@[to_additive (attr := simp)]
/--
theorem `val_mk` / 定理 `val_mk`

English:
theorem val_mk
  given: {a : M} (h : a != 1)
  statement: (mk a h).val = MulArchimedeanClass.mk a
  proof: rfl

@[to_additive]

中文:
定理 val_mk
  条件: {a : M} (h : a != 1)
  结论: (mk a h).val = MulArchimedeanClass.mk a
  证明: rfl

@[to_additive]
-/
theorem val_mk {a : M} (h : a != 1) : (mk a h).val = MulArchimedeanClass.mk a := rfl

@[to_additive]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {a : M} (ha : a != 1) {b : M} (hb : b != 1)
  proof: .rfl

@[to_additive]

中文:
定理 mk_le_mk
  条件: {a : M} (ha : a != 1) {b : M} (hb : b != 1)
  证明: .rfl

@[to_additive]
-/
theorem mk_le_mk {a : M} (ha : a != 1) {b : M} (hb : b != 1) :
    mk a ha <= mk b hb ↔ MulArchimedeanClass.mk a <= MulArchimedeanClass.mk b := .rfl

@[to_additive]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: {a : M} (ha : a != 1) {b : M} (hb : b != 1)
  proof: .rfl

中文:
定理 mk_lt_mk
  条件: {a : M} (ha : a != 1) {b : M} (hb : b != 1)
  证明: .rfl
-/
theorem mk_lt_mk {a : M} (ha : a != 1) {b : M} (hb : b != 1) :
    mk a ha < mk b hb ↔ MulArchimedeanClass.mk a < MulArchimedeanClass.mk b := .rfl

/--
theorem `min_le_mk_mul` / 定理 `min_le_mk_mul`

English:
theorem min_le_mk_mul
  statement: {a b : M} (ha : a != 1) (hb : b != 1)
  proof: MulArchimedeanClass.min_le_mk_mul a b

中文:
定理 min_le_mk_mul
  结论: {a b : M} (ha : a != 1) (hb : b != 1)
  证明: MulArchimedeanClass.min_le_mk_mul a b
-/
@[to_additive] theorem min_le_mk_mul {a b : M} (ha : a != 1) (hb : b != 1)
    (hab : a * b != 1) : min (mk a ha) (mk b hb) <= mk (a * b) hab :=
  MulArchimedeanClass.min_le_mk_mul a b

/--
theorem `mk_inv` / 定理 `mk_inv`

English:
theorem mk_inv
  given: {a : M} (ha : a != 1)
  statement: mk a⁻¹ (by simp [ha]) = mk a ha
  proof: Subtype.ext (MulArchimedeanClass.mk_inv a)

中文:
定理 mk_inv
  条件: {a : M} (ha : a != 1)
  结论: mk a⁻¹ (by simp [ha]) = mk a ha
  证明: Subtype.ext (MulArchimedeanClass.mk_inv a)
-/
@[to_additive] theorem mk_inv {a : M} (ha : a != 1) : mk a⁻¹ (by simp [ha]) = mk a ha :=
  Subtype.ext (MulArchimedeanClass.mk_inv a)

/-- An induction principle for `FiniteMulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for `FiniteArchimedeanClass`. -/]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {motive : FiniteMulArchimedeanClass M -> Prop}
  proof: by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

@[to_additive]

中文:
定理 ind
  结论: {motive : FiniteMulArchimedeanClass M -> 命题}
  证明: by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

@[to_additive]

Depends on / 依赖: FiniteMulArchimedeanClass, MulArchimedeanClass, MulArchimedeanClass.forall
-/
theorem ind {motive : FiniteMulArchimedeanClass M -> Prop}
    (mk : forall a, (ha : a != 1) -> motive (.mk a ha)) : forall x, motive x := by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulArchimedean
  signature: M] : Subsingleton (FiniteMulArchimedeanClass M) where
  body: by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa [mk] using MulArchimedeanClass.mk_eq_mk_of_mulArchimedean ha hb

@[to_additive]

中文:
实例 [MulArchimedean
  签名: M] : 子单例 (FiniteMulArchimedeanClass M) where
  定义体: by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa [mk] using MulArchimedeanClass.mk_eq_mk_of_mulArchimedean ha hb

@[to_additive]

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.mk_eq_mk_of_mulArchimedean, mk_eq_mk_of_mulArchimedean
-/
instance [MulArchimedean M] : Subsingleton (FiniteMulArchimedeanClass M) where
  allEq A B := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa [mk] using MulArchimedeanClass.mk_eq_mk_of_mulArchimedean ha hb

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nonempty (FiniteMulArchimedeanClass M)
  body: by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  exact ⟨mk x hx, by simpa using hx⟩

中文:
实例 [非平凡
  签名: M] : 非空 (FiniteMulArchimedeanClass M)
  定义体: by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  exact ⟨mk x hx, by simpa using hx⟩

Depends on / 依赖: exists_ne
-/
instance [Nontrivial M] : Nonempty (FiniteMulArchimedeanClass M) := by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  exact ⟨mk x hx, by simpa using hx⟩

/-- Lift a `f : {a : M // a ≠ 1} → α` function to `FiniteMulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `f : {a : M // a ≠ 0} → α` function to `FiniteArchimedeanClass M → α`. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {α : Type*} (f : {a : M // a != 1} -> α)
  body: fun ⟨A, hA⟩ => by
  refine (MulArchimedeanClass.lift
    (fun b => if h : b = 1 then ⊤ else WithTop.some (f ⟨b, h⟩)) (fun a b h' => ?_) A).untop ?_
  · split_ifs with ha hb hb
    · rfl
    · exact (hb (MulArchimedeanClass.mk_eq_top_iff.mp (ha ▸ h').symm)).elim
    · exact (ha (MulArchimedeanClass.mk_eq_top_iff.mp (by apply hb ▸ h'))).elim
    · rw [h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [mk] using h')]
  · induction A using MulArchimedeanClass.ind with | mk a
    simpa using MulArchimedeanClass.mk_eq_top_iff.not.mp hA

@[to_additive (attr := simp)]

中文:
定义 lift
  签名: {α : 类型} (f : {a : M // a != 1} -> α)
  定义体: fun ⟨A, hA⟩ => by
  refine (MulArchimedeanClass.lift
    (fun b => if h : b = 1 then ⊤ else WithTop.some (f ⟨b, h⟩)) (fun a b h' => ?_) A).untop ?_
  · split_ifs with ha hb hb
    · rfl
    · exact (hb (MulArchimedeanClass.mk_eq_top_iff.mp (ha ▸ h').symm)).elim
    · exact (ha (MulArchimedeanClass.mk_eq_top_iff.mp (by apply hb ▸ h'))).elim
    · rw [h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [mk] using h')]
  · induction A using MulArchimedeanClass.ind with | mk a
    simpa using MulArchimedeanClass.mk_eq_top_iff.not.mp hA

@[to_additive (attr := simp)]

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.ind, MulArchimedeanClass.lift, MulArchimedeanClass.mk_eq_top_iff.mp, MulArchimedeanClass.mk_eq_top_iff.not.mp, WithTop, WithTop.some, mk_eq_top_iff, split_ifs
-/
def lift {α : Type*} (f : {a : M // a != 1} -> α)
    (h : forall (a b : {a : M // a != 1}), mk a.val a.prop = mk b.val b.prop -> f a = f b) :
    FiniteMulArchimedeanClass M -> α := fun ⟨A, hA⟩ => by
  refine (MulArchimedeanClass.lift
    (fun b => if h : b = 1 then ⊤ else WithTop.some (f ⟨b, h⟩)) (fun a b h' => ?_) A).untop ?_
  · split_ifs with ha hb hb
    · rfl
    · exact (hb (MulArchimedeanClass.mk_eq_top_iff.mp (ha ▸ h').symm)).elim
    · exact (ha (MulArchimedeanClass.mk_eq_top_iff.mp (by apply hb ▸ h'))).elim
    · rw [h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [mk] using h')]
  · induction A using MulArchimedeanClass.ind with | mk a
    simpa using MulArchimedeanClass.mk_eq_top_iff.not.mp hA

@[to_additive (attr := simp)]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: {α : Type*} (f : {a : M // a != 1} -> α)
  proof: by simp [lift, mk, ha]

中文:
定理 lift_mk
  结论: {α : 类型} (f : {a : M // a != 1} -> α)
  证明: by simp [lift, mk, ha]
-/
theorem lift_mk {α : Type*} (f : {a : M // a != 1} -> α)
    (h : forall (a b : {a : M // a != 1}), mk a.val a.prop = mk b.val b.prop -> f a = f b)
    {a : M} (ha : a != 1) :
    lift f h (mk a ha) = f ⟨a, ha⟩ := by simp [lift, mk, ha]

/-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean classes to a
monotone function `FiniteMulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean
classes to a monotone function `FiniteArchimedeanClass M₁ →o α`. -/]
/--
Definition of `liftOrderHom` / `liftOrderHom` 的定义

English:
definition liftOrderHom
  signature: {α : Type*} [PartialOrder α]
  body: lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hAB := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa using h ⟨a, ha⟩ ⟨b, hb⟩ hAB

@[to_additive (attr := simp)]

中文:
定义 liftOrderHom
  签名: {α : 类型} [偏序 α]
  定义体: lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hAB := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa using h ⟨a, ha⟩ ⟨b, hb⟩ hAB

@[to_additive (attr := simp)]

Depends on / 依赖: heq.ge, heq.le, le_antisymm
-/
def liftOrderHom {α : Type*} [PartialOrder α]
    (f : {a : M // a != 1} -> α)
    (h : forall (a b : {a : M // a != 1}), mk a.val a.prop <= mk b.val b.prop -> f a <= f b) :
    FiniteMulArchimedeanClass M ->o α where
  toFun := lift f fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hAB := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa using h ⟨a, ha⟩ ⟨b, hb⟩ hAB

@[to_additive (attr := simp)]
/--
theorem `liftOrderHom_mk` / 定理 `liftOrderHom_mk`

English:
theorem liftOrderHom_mk
  statement: {α : Type*} [PartialOrder α]
  proof: lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) ha

中文:
定理 liftOrderHom_mk
  结论: {α : 类型} [偏序 α]
  证明: lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) ha

Depends on / 依赖: heq.ge, heq.le, le_antisymm, lift_mk
-/
theorem liftOrderHom_mk {α : Type*} [PartialOrder α]
    (f : {a : M // a != 1} -> α)
    (h : forall (a b : {a : M // a != 1}), mk a.val a.prop <= mk b.val b.prop -> f a <= f b)
    {a : M} (ha : a != 1) : liftOrderHom f h (mk a ha) = f ⟨a, ha⟩ :=
  lift_mk f (fun a b heq => le_antisymm (h a b heq.le) (h b a heq.ge)) ha

variable (M) in
/-- Adding top to the type of finite classes yields the type of all classes. -/
@[to_additive /-- Adding top to the type of finite classes yields the type of all classes. -/]
noncomputable
/--
Definition of `withTopOrderIso` / `withTopOrderIso` 的定义

English:
definition withTopOrderIso
  signature: : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanClass M
  body: WithTop.subtypeOrderIso

@[to_additive (attr := simp)]

中文:
定义 withTopOrderIso
  签名: : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanClass M
  定义体: WithTop.subtypeOrderIso

@[to_additive (attr := simp)]

Depends on / 依赖: WithTop, WithTop.subtypeOrderIso, subtypeOrderIso
-/
def withTopOrderIso : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanClass M :=
  WithTop.subtypeOrderIso

@[to_additive (attr := simp)]
/--
theorem `withTopOrderIso_apply_coe` / 定理 `withTopOrderIso_apply_coe`

English:
theorem withTopOrderIso_apply_coe
  given: (A : FiniteMulArchimedeanClass M)
  proof: WithTop.subtypeOrderIso_apply_coe A

@[to_additive]

中文:
定理 withTopOrderIso_apply_coe
  条件: (A : FiniteMulArchimedeanClass M)
  证明: WithTop.subtypeOrderIso_apply_coe A

@[to_additive]

Depends on / 依赖: WithTop, WithTop.subtypeOrderIso_apply_coe, subtypeOrderIso_apply_coe
-/
theorem withTopOrderIso_apply_coe (A : FiniteMulArchimedeanClass M) :
    withTopOrderIso M (A : WithTop (FiniteMulArchimedeanClass M)) = A.val :=
  WithTop.subtypeOrderIso_apply_coe A

@[to_additive]
/--
theorem `withTopOrderIso_symm_apply` / 定理 `withTopOrderIso_symm_apply`

English:
theorem withTopOrderIso_symm_apply
  given: {a : M} (h : a != 1)
  proof: WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

中文:
定理 withTopOrderIso_symm_apply
  条件: {a : M} (h : a != 1)
  证明: WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.mk_eq_top_iff.ne.mpr, WithTop, WithTop.subtypeOrderIso_symm_apply, mk_eq_top_iff, subtypeOrderIso_symm_apply
-/
theorem withTopOrderIso_symm_apply {a : M} (h : a != 1) :
    (withTopOrderIso M).symm (MulArchimedeanClass.mk a) = mk a h :=
  WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderIso` on `MulArchimedeanClass` induces an `OrderIso` on `FiniteMulArchimedeanClass`. -/
@[to_additive
/-- An `OrderIso` on `ArchimedeanClass` induces an `OrderIso` on `FiniteArchimedeanClass`. -/]
noncomputable
/--
Definition of `congrOrderIso` / `congrOrderIso` 的定义

English:
definition congrOrderIso
  signature: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  body: Equiv.subtypeEquiv e (by simp)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]

中文:
定义 congrOrderIso
  签名: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  定义体: Equiv.subtypeEquiv e (by simp)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.subtypeEquiv, subtypeEquiv
-/
def congrOrderIso (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) :
    FiniteMulArchimedeanClass M ≃o FiniteMulArchimedeanClass N where
  __ := Equiv.subtypeEquiv e (by simp)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]
/--
theorem `coe_congrOrderIso_apply` / 定理 `coe_congrOrderIso_apply`

English:
theorem coe_congrOrderIso_apply
  statement: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_congrOrderIso_apply
  结论: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_congrOrderIso_apply (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
    (a : FiniteMulArchimedeanClass M) :
    (congrOrderIso e a : MulArchimedeanClass N) = e a := rfl

@[to_additive (attr := simp)]
/--
theorem `congrOrderIso_symm` / 定理 `congrOrderIso_symm`

English:
theorem congrOrderIso_symm
  given: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  proof: rfl

中文:
定理 congrOrderIso_symm
  条件: (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
  证明: rfl
-/
theorem congrOrderIso_symm (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) :
    (congrOrderIso e).symm = congrOrderIso e.symm := rfl

/-- The upper set in `MulArchimedeanClass M` consisting of an upper set in
`FiniteMulArchimedeanClass M` plus `⊤`. -/
@[to_additive /-- The upper set in `ArchimedeanClass M` consisting of an upper set in
`FiniteArchimedeanClass M` plus `⊤`. -/]
/--
Definition of `toUpperSetMulArchimedeanClass` / `toUpperSetMulArchimedeanClass` 的定义

English:
definition toUpperSetMulArchimedeanClass
  signature: :
  body: .ofStrictMono (fun s =>
    { carrier := {a | forall h : a != ⊤, ⟨a, h⟩ in s}
      upper' _ _ le mem ne := s.upper le (mem <| ne_top_of_le_ne_top ne le) })
  fun s t lt => by
    simp_rw [lt_iff_le_not_ge] at lt ⊢
    exact ⟨fun _ mem ne => lt.1 (mem _), fun hst => lt.2 fun x mem => hst (fun _ => mem) x.2⟩

中文:
定义 toUpperSetMulArchimedeanClass
  签名: :
  定义体: .ofStrictMono (fun s =>
    { carrier := {a | forall h : a != ⊤, ⟨a, h⟩ in s}
      upper' _ _ le mem ne := s.upper le (mem <| ne_top_of_le_ne_top ne le) })
  fun s t lt => by
    simp_rw [lt_iff_le_not_ge] at lt ⊢
    exact ⟨fun _ mem ne => lt.1 (mem _), fun hst => lt.2 fun x mem => hst (fun _ => mem) x.2⟩

Depends on / 依赖: carrier, lt_iff_le_not_ge, ne_top_of_le_ne_top, ofStrictMono, s.upper, simp_rw
-/
noncomputable def toUpperSetMulArchimedeanClass :
    UpperSet (FiniteMulArchimedeanClass M) ↪o UpperSet (MulArchimedeanClass M) :=
  .ofStrictMono (fun s =>
    { carrier := {a | forall h : a != ⊤, ⟨a, h⟩ in s}
      upper' _ _ le mem ne := s.upper le (mem <| ne_top_of_le_ne_top ne le) })
  fun s t lt => by
    simp_rw [lt_iff_le_not_ge] at lt ⊢
    exact ⟨fun _ mem ne => lt.1 (mem _), fun hst => lt.2 fun x mem => hst (fun _ => mem) x.2⟩

/-- The `MulArchimedeanClass.subsemigroup` associated to an upper set in
`FiniteMulArchimedeanClass M` is a subgroup. -/
@[to_additive /-- The `ArchimedeanClass.subsemigroup` associated to an upper set in
`FiniteArchimedeanClass M` is a subgroup. -/]
/--
Definition of `subgroup` / `subgroup` 的定义

English:
definition subgroup
  signature: (s : UpperSet (FiniteMulArchimedeanClass M))
  body: MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s)
  one_mem' h := (h rfl).elim
  inv_mem' := by simp [MulArchimedeanClass.subsemigroup]

中文:
定义 subgroup
  签名: (s : 上集 (FiniteMulArchimedeanClass M))
  定义体: MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s)
  one_mem' h := (h rfl).elim
  inv_mem' := by simp [MulArchimedeanClass.subsemigroup]

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.subsemigroup, subsemigroup, toUpperSetMulArchimedeanClass
-/
noncomputable def subgroup (s : UpperSet (FiniteMulArchimedeanClass M)) : Subgroup M where
  __ := MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s)
  one_mem' h := (h rfl).elim
  inv_mem' := by simp [MulArchimedeanClass.subsemigroup]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

@[to_additive]
/--
theorem `subsemigroup_eq_subgroup` / 定理 `subsemigroup_eq_subgroup`

English:
theorem subsemigroup_eq_subgroup
  proof: rfl

中文:
定理 subsemigroup_eq_subgroup
  证明: rfl
-/
theorem subsemigroup_eq_subgroup :
    MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s) = (subgroup s : Set M) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (M) in
@[to_additive (attr := simp)]
/--
theorem `subgroup_eq_bot` / 定理 `subgroup_eq_bot`

English:
theorem subgroup_eq_bot
  statement: subgroup (M := M) ⊤ = ⊥
  proof: by
  ext; simp [subgroup, MulArchimedeanClass.subsemigroup, toUpperSetMulArchimedeanClass]

@[to_additive (attr := simp)]

中文:
定理 subgroup_eq_bot
  结论: subgroup (M := M) ⊤ = ⊥
  证明: by
  ext; simp [subgroup, MulArchimedeanClass.subsemigroup, toUpperSetMulArchimedeanClass]

@[to_additive (attr := simp)]

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.subsemigroup, subgroup, subsemigroup, toUpperSetMulArchimedeanClass
-/
theorem subgroup_eq_bot : subgroup (M := M) ⊤ = ⊥ := by
  ext; simp [subgroup, MulArchimedeanClass.subsemigroup, toUpperSetMulArchimedeanClass]

@[to_additive (attr := simp)]
/--
theorem `mem_subgroup_iff` / 定理 `mem_subgroup_iff`

English:
theorem mem_subgroup_iff
  statement: a in subgroup s ↔ forall h : a != 1, mk a h in s
  proof: by
  simp_rw [mk, Ne, ← MulArchimedeanClass.mk_eq_top_iff]; rfl

中文:
定理 mem_subgroup_iff
  结论: a in subgroup s ↔ 对任意 h : a != 1, mk a h in s
  证明: by
  simp_rw [mk, Ne, ← MulArchimedeanClass.mk_eq_top_iff]; rfl

Depends on / 依赖: MulArchimedeanClass, MulArchimedeanClass.mk_eq_top_iff, mk_eq_top_iff, simp_rw
-/
theorem mem_subgroup_iff : a in subgroup s ↔ forall h : a != 1, mk a h in s := by
  simp_rw [mk, Ne, ← MulArchimedeanClass.mk_eq_top_iff]; rfl

/--
theorem `subgroup_strictAnti` / 定理 `subgroup_strictAnti`

English:
theorem subgroup_strictAnti
  statement: StrictAnti (subgroup (M := M))
  proof: fun _ _ h =>
  MulArchimedeanClass.subsemigroup_strictAnti (toUpperSetMulArchimedeanClass.strictMono h)

中文:
定理 subgroup_strictAnti
  结论: 严格递减 (subgroup (M := M))
  证明: fun _ _ h =>
  MulArchimedeanClass.subsemigroup_strictAnti (toUpperSetMulArchimedeanClass.strictMono h)
-/
@[to_additive] theorem subgroup_strictAnti : StrictAnti (subgroup (M := M)) := fun _ _ h =>
  MulArchimedeanClass.subsemigroup_strictAnti (toUpperSetMulArchimedeanClass.strictMono h)

/-- An open ball defined by `FiniteMulArchimedeanClass.subgroup` of `UpperSet.Ioi c`. -/
@[to_additive
/--An open ball defined by `FiniteArchimedeanClass.addSubgroup` of `UpperSet.Ioi c`. -/]
/--
Definition of `ballSubgroup` / `ballSubgroup` 的定义

English:
abbreviation ballSubgroup
  signature: (c : FiniteMulArchimedeanClass M)
  body: subgroup (UpperSet.Ioi c)

中文:
缩写 ballSubgroup
  签名: (c : FiniteMulArchimedeanClass M)
  定义体: subgroup (UpperSet.Ioi c)

Depends on / 依赖: UpperSet, UpperSet.Ioi, subgroup
-/
noncomputable abbrev ballSubgroup (c : FiniteMulArchimedeanClass M) := subgroup (UpperSet.Ioi c)

/-- A closed ball defined by `FiniteMulArchimedeanClass.subgroup` of `UpperSet.Ici c`. -/
@[to_additive
/-- A closed ball defined by `FiniteArchimedeanClass.addSubgroup` of `UpperSet.Ici c`. -/]
/--
Definition of `closedBallSubgroup` / `closedBallSubgroup` 的定义

English:
abbreviation closedBallSubgroup
  signature: (c : FiniteMulArchimedeanClass M)
  body: subgroup (UpperSet.Ici c)

@[to_additive]

中文:
缩写 closedBallSubgroup
  签名: (c : FiniteMulArchimedeanClass M)
  定义体: subgroup (UpperSet.Ici c)

@[to_additive]

Depends on / 依赖: UpperSet, UpperSet.Ici, subgroup
-/
noncomputable abbrev closedBallSubgroup (c : FiniteMulArchimedeanClass M) :=
  subgroup (UpperSet.Ici c)

@[to_additive]
/--
theorem `mem_ballSubgroup_iff` / 定理 `mem_ballSubgroup_iff`

English:
theorem mem_ballSubgroup_iff
  given: {a : M} {c : FiniteMulArchimedeanClass M}
  proof: by
  simp

@[to_additive]

中文:
定理 mem_ballSubgroup_iff
  条件: {a : M} {c : FiniteMulArchimedeanClass M}
  证明: by
  simp

@[to_additive]
-/
theorem mem_ballSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a in ballSubgroup c ↔ forall h : a != 1, c < mk a h := by
  simp

@[to_additive]
/--
theorem `mem_closedBallSubgroup_iff` / 定理 `mem_closedBallSubgroup_iff`

English:
theorem mem_closedBallSubgroup_iff
  given: {a : M} {c : FiniteMulArchimedeanClass M}
  proof: by
  simp

@[to_additive]

中文:
定理 mem_closedBallSubgroup_iff
  条件: {a : M} {c : FiniteMulArchimedeanClass M}
  证明: by
  simp

@[to_additive]
-/
theorem mem_closedBallSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a in closedBallSubgroup c ↔ forall h : a != 1, c <= mk a h := by
  simp

@[to_additive]
/--
theorem `ballSubgroup_strictAnti` / 定理 `ballSubgroup_strictAnti`

English:
theorem ballSubgroup_strictAnti
  statement: StrictAnti (ballSubgroup (M := M))
  proof: fun _ _ h => subgroup_strictAnti UpperSet.Ioi_strictMono _ h

中文:
定理 ballSubgroup_strictAnti
  结论: 严格递减 (ballSubgroup (M := M))
  证明: fun _ _ h => subgroup_strictAnti UpperSet.Ioi_strictMono _ h
-/
theorem ballSubgroup_strictAnti : StrictAnti (ballSubgroup (M := M)) :=
fun _ _ h => subgroup_strictAnti UpperSet.Ioi_strictMono _ h

end FiniteMulArchimedeanClass
