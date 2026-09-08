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
/-
**MulArchimedeanOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulArchimedeanOrder
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulArchimedeanOrder := M

namespace MulArchimedeanOrder

/-- Create a `MulArchimedeanOrder` element from the underlying type. -/
@[to_additive /-- Create a `ArchimedeanOrder` element from the underlying type. -/]
/-
**MulArchimedeanOrder.of** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：of : M ≃ MulArchimedeanOrder M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Create a `MulArchimedeanOrder` element from the underlying type.
-/
def of : M ≃ MulArchimedeanOrder M := Equiv.refl _

/-- Retrieve the underlying value from a `MulArchimedeanOrder` element. -/
@[to_additive /-- Retrieve the underlying value from a `ArchimedeanOrder` element. -/]
/-
**MulArchimedeanOrder.val** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：val : MulArchimedeanOrder M ≃ M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Retrieve the underlying value from a `MulArchimedeanOrder` element.
-/
def val : MulArchimedeanOrder M ≃ M := Equiv.refl _

@[to_additive (attr := simp)]
/-
**MulArchimedeanOrder.of_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder`
。
形式化陈述：of_symm_eq : (of (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem of_symm_eq : (of (M := M)).symm = val := rfl

@[to_additive (attr := simp)]
/-
**MulArchimedeanOrder.val_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder
`。
形式化陈述：val_symm_eq : (val (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem val_symm_eq : (val (M := M)).symm = of := rfl

@[to_additive (attr := simp)]
/-
**MulArchimedeanOrder.of_val** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：of_val (a : MulArchimedeanOrder M) : of (val a) = a
参数：a : MulArchimedeanOrder M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_val (a : MulArchimedeanOrder M) : of (val a) = a := rfl

@[to_additive (attr := simp)]
/-
**MulArchimedeanOrder.val_of** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：val_of (a : M) : val (of a) = a
参数：a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_of (a : M) : val (of a) = a := rfl

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty M] : Nonempty (MulArchimedeanOrder M) :=
  inferInstanceAs (Nonempty M)

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited M] : Inhabited (MulArchimedeanOrder M) :=
  ⟨of default⟩

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Subsingleton (MulArchimedeanOrder M) :=
  inferInstanceAs (Subsingleton M)

variable [Group M] [Lattice M]

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (MulArchimedeanOrder M) where
  le a b := ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT (MulArchimedeanOrder M) where
  lt a b := ∀ n, |b.val|ₘ ^ n < |a.val|ₘ

@[to_additive]
/-
**MulArchimedeanOrder.le_def** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：le_def {a b : MulArchimedeanOrder M} : a <= b ↔ exists n, |b.val|ₘ <= |a.v
al|ₘ ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {a b : MulArchimedeanOrder M} : a ≤ b ↔ ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n := .rfl

@[to_additive]
/-
**MulArchimedeanOrder.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：lt_def {a b : MulArchimedeanOrder M} : a < b ↔ forall n, |b.val|ₘ ^ n < |a
.val|ₘ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def {a b : MulArchimedeanOrder M} : a < b ↔ ∀ n, |b.val|ₘ ^ n < |a.val|ₘ := .rfl

variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (MulArchimedeanOrder M) where
  le_refl a := ⟨1, by simp⟩
  le_trans a b c := by
    intro ⟨m, hm⟩ ⟨n, hn⟩
    use m * n
    rw [pow_mul]
    exact hn.trans (pow_le_pow_left' hm n)
  lt_iff_le_not_ge a b := by
    rw [lt_def, le_def, le_def]
    suffices (∀ (n : ℕ), |b.val|ₘ ^ n < |a.val|ₘ) → ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n by
      simpa using this
    intro h
    obtain h := (h 1).le
    exact ⟨1, by simpa using h⟩

@[to_additive]
/-
**MulArchimedeanOrder.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Total (MulArchimedeanOrder M) (· ≤ ·) where
  total a b := by
    obtain hab | hab := le_total |a.val|ₘ |b.val|ₘ
    · exact .inr ⟨1, by simpa using hab⟩
    · exact .inl ⟨1, by simpa using hab⟩

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be made to an `OrderHom` between their `MulArchimedeanOrder`. -/
@[to_additive /-- An `OrderAddMonoidHom` can be made to an `OrderHom` between their
`ArchimedeanOrder`. -/]
/-
**MulArchimedeanOrder.orderHom** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanOrder`。
形式化陈述：orderHom (f : M ->*o N) : MulArchimedeanOrder M ->o MulArchimedeanOrder N 
where toFun a
参数：f : M ->*o N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def orderHom (f : M →*o N) : MulArchimedeanOrder M →o MulArchimedeanOrder N where
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
/-
**MulArchimedeanClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulArchimedeanClass
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulArchimedeanClass := Antisymmetrization (MulArchimedeanOrder M) (· ≤ ·)

namespace MulArchimedeanClass

/-- The archimedean class of a given element. -/
@[to_additive /-- The archimedean class of a given element. -/]
/-
**MulArchimedeanClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk (a : M) : MulArchimedeanClass M
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The archimedean class of a given element.
-/
def mk (a : M) : MulArchimedeanClass M := toAntisymmetrization _ (MulArchimedeanOrder.of a)

/-- An induction principle for `MulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
/-- An induction principle for `ArchimedeanClass` -/]
/-
**MulArchimedeanClass.ind** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：ind {motive : MulArchimedeanClass M -> Prop} (mk : forall a, motive (.mk a
)) : forall x, motive x
参数：mk : forall a, motive (.mk a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antisymmetrization.ind`：∀ {α : Type u_1} (r : α → α → Prop) [inst : IsPr
eorder α r] {p : Antisymmetrization α r → Prop},   (∀ (a : α), p (toAntisymmetri
zation r a))…
-/
theorem ind {motive : MulArchimedeanClass M → Prop} (mk : ∀ a, motive (.mk a)) : ∀ x, motive x :=
  Antisymmetrization.ind _ mk

@[to_additive]
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : MulArchimedeanClass M → Prop} : (∀ A, p A) ↔ ∀ a, p (mk a) := Quotient.forall

variable (M) in
@[to_additive]
/-
**MulArchimedeanClass.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：mk_surjective : Function.Surjective mk (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk_surjective

variable (M) in
@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.range_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：range_mk : Set.range (mk (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `MulArchimedeanClass.mk_surjective`：mk_surjective : Function.Surjective m
k (M
-/
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (mk_surjective M)

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MulArchimedeanClass.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists 
n, |a|ₘ <= |b|ₘ ^ n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk {a b : M} : mk a = mk b ↔ (∃ m, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, |a|ₘ ≤ |b|ₘ ^ n) := by
  unfold mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

/-- Lift a `M → α` function to `MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → α` function to `ArchimedeanClass M → α`. -/]
/-
**MulArchimedeanClass.lift** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：lift {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b) :
 MulArchimedeanClass M -> α
参数：f : M -> α；h : forall a b, mk a = mk b -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `M → α` function to `MulArchimedeanClass M → α`.
-/
def lift {α : Type*} (f : M → α) (h : ∀ a b, mk a = mk b → f a = f b) :
    MulArchimedeanClass M → α :=
  Quotient.lift f fun _ _ h' ↦ h _ _ <| mk_eq_mk.mpr h'

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：lift_mk {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b
) (a : M) : lift f h (mk a) = f a
参数：f : M -> α；h : forall a b, mk a = mk b -> f a = f b；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulArchimedeanClass.mk_eq_mk`：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists
 m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
-/
theorem lift_mk {α : Type*} (f : M → α) (h : ∀ a b, mk a = mk b → f a = f b)
    (a : M) : lift f h (mk a) = f a := by
  unfold lift
  exact Quotient.lift_mk f (fun _ _ h' ↦ h _ _ <| mk_eq_mk.mpr h') a

/-- Lift a `M → M → α` function to `MulArchimedeanClass M → MulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `M → M → α` function to `ArchimedeanClass M → ArchimedeanClass M → α`. -/]
/-
**MulArchimedeanClass.lift** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：lift {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b) :
 MulArchimedeanClass M -> α
参数：f : M -> α；h : forall a b, mk a = mk b -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `M → M → α` function to `MulArchimedeanClass M → MulArchimedeanClass M → 
α`.
-/
def lift₂ {α : Type*} (f : M → M → α)
    (h : ∀ a₁ b₁ a₂ b₂, mk a₁ = mk b₁ → mk a₂ = mk b₂ → f a₁ a₂ = f b₁ b₂) :
    MulArchimedeanClass M → MulArchimedeanClass M → α :=
  Quotient.lift₂ f fun _ _ _ _ h₁ h₂ ↦ h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.lift** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：lift {α : Type*} (f : M -> α) (h : forall a b, mk a = mk b -> f a = f b) :
 MulArchimedeanClass M -> α
参数：f : M -> α；h : forall a b, mk a = mk b -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift₂_mk {α : Type*} (f : M → M → α)
    (h : ∀ a₁ b₁ a₂ b₂, mk a₁ = mk b₁ → mk a₂ = mk b₂ → f a₁ a₂ = f b₁ b₂)
    (a b : M) : lift₂ f h (mk a) (mk b) = f a b := by
  unfold lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ ↦ h _ _ _ _ (mk_eq_mk.mpr h₁) (mk_eq_mk.mpr h₂)) a b

/-- Choose a representative element from a given archimedean class. -/
@[to_additive /-- Choose a representative element from a given archimedean class. -/]
noncomputable
/-
**MulArchimedeanClass.out** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：out (A : MulArchimedeanClass M) : M
参数：A : MulArchimedeanClass M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def out (A : MulArchimedeanClass M) : M := (Quotient.out A).val

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_out (A : MulArchimedeanClass M) : mk A.out = A
参数：A : MulArchimedeanClass M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem mk_out (A : MulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_inv (a : M) : mk a⁻¹ = mk a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulArchimedeanClass.mk_eq_mk`：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists
 m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem mk_inv (a : M) : mk a⁻¹ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
/-
**MulArchimedeanClass.mk_div_comm** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass
`。
形式化陈述：mk_div_comm (a b : M) : mk (a / b) = mk (b / a)
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv, inv_div]

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_mabs** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_mabs (a : M) : mk |a|ₘ = mk a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulArchimedeanClass.mk_eq_mk`：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists
 m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLe
ftMono α] [MulRightMono α] (a : α), |(|a|ₘ)|ₘ = |a|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem mk_mabs (a : M) : mk |a|ₘ = mk a :=
  mk_eq_mk.mpr ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩

@[to_additive]
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Subsingleton (MulArchimedeanClass M) :=
  inferInstanceAs (Subsingleton (Antisymmetrization ..))

@[to_additive]
noncomputable
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (MulArchimedeanClass M) :=
  open scoped Classical in
  -- TODO: why does `inferInstanceAs` not work here?
  fast_instance% (inferInstance : LinearOrder (Antisymmetrization (MulArchimedeanOrder M) (· ≤ ·)))

@[to_additive]
/-
**MulArchimedeanClass.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_le_mk : mk a <= mk b ↔ exists n, |b|ₘ <= |a|ₘ ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk : mk a ≤ mk b ↔ ∃ n, |b|ₘ ≤ |a|ₘ ^ n := .rfl

@[to_additive]
/-
**MulArchimedeanClass.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ n < |a|ₘ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := .rfl

@[to_additive]
/-
**MulArchimedeanClass.mk_le_mk_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanC
lass`。
形式化陈述：mk_le_mk_iff_lt (ha : a != 1) : mk a <= mk b ↔ exists n, |b|ₘ < |a|ₘ ^ n
参数：ha : a != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_mabs`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
[MulLeftMono α] {a : α}, 1 < |a|ₘ ↔ a ≠ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mk_le_mk_iff_lt (ha : a ≠ 1) : mk a ≤ mk b ↔ ∃ n, |b|ₘ < |a|ₘ ^ n := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n + 1, hn.trans_lt ?_⟩, fun ⟨n, hn⟩ ↦ ?_⟩
  · rw [pow_succ]
    exact lt_mul_of_one_lt_right' _ (one_lt_mabs.mpr ha)
  · exact ⟨n, hn.le⟩

/-- 1 is in its own class (see `MulArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/
@[to_additive /-- 0 is in its own class (see `ArchimedeanClass.mk_eq_top_iff`),
which is also the largest class. -/]
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : OrderTop (MulArchimedeanClass M) where
  top := mk 1
  le_top A := by
    induction A using ind with | mk a
    rw [mk_le_mk]
    exact ⟨1, by simp⟩

@[to_additive]
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited (MulArchimedeanClass M) := ⟨⊤⟩

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_one : mk 1 = (⊤ : MulArchimedeanClass M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one : mk 1 = (⊤ : MulArchimedeanClass M) := rfl

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：mk_eq_top_iff : mk a = ⊤ ↔ a = 1 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mabs_one`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLef
tMono α], |1|ₘ = 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_top_iff : mk a = ⊤ ↔ a = 1 where
  mp := by simp [← mk_one, mk_eq_mk]
  mpr := by simp_all

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.top_eq_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：top_eq_mk_iff : ⊤ = mk a ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MulArchimedeanClass.mk_eq_top_iff`：mk_eq_top_iff : mk a = ⊤ ↔ a = 1 wher
e mp
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem top_eq_mk_iff : ⊤ = mk a ↔ a = 1 := by
  rw [eq_comm, mk_eq_top_iff]

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.out_top** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：out_top : (⊤ : MulArchimedeanClass M).out = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.mk_eq_top_iff`：mk_eq_top_iff : mk a = ⊤ ↔ a = 1 wher
e mp
· 使用定理 `MulArchimedeanClass.mk_out`：mk_out (A : MulArchimedeanClass M) : mk A.ou
t = A
-/
theorem out_top : (⊤ : MulArchimedeanClass M).out = 1 := by
  rw [← mk_eq_top_iff, mk_out]

@[to_additive]
/-
**MulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nontrivial (MulArchimedeanClass M) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    exact ⟨mk x, ⊤, mk_eq_top_iff.ne.mpr hx⟩

@[to_additive]
/-
**MulArchimedeanClass.mk_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_eq_self`：mabs_eq_self : |a|ₘ = a ↔ 1 <= a
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
-/
theorem mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr hb] at h
  simpa using h

@[to_additive]
/-
**MulArchimedeanClass.mk_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_eq_inv_self`：mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a <= 1
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
-/
theorem mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]
/-
**MulArchimedeanClass.mk_le_mk_of_mabs** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedean
Class`。
形式化陈述：mk_le_mk_of_mabs {a b : M} (h : |a|ₘ <= |b|ₘ) : mk b <= mk a
参数：h : |a|ₘ <= |b|ₘ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.mk_mabs`：mk_mabs (a : M) : mk |a|ₘ = mk a
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `MulArchimedeanClass.mk_antitoneOn`：mk_antitoneOn : AntitoneOn mk (Set.Ic
i (1 : M))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mk_le_mk_of_mabs {a b : M} (h : |a|ₘ ≤ |b|ₘ) : mk b ≤ mk a := by
  rw [← mk_mabs a, ← mk_mabs]
  have ha := one_le_mabs a
  exact mk_antitoneOn ha (ha.trans h) h

@[to_additive]
/-
**MulArchimedeanClass.min_le_mk_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：min_le_mk_of_le_of_le {x y z : M} (hy : y <= x) (hz : x <= z) : min (mk y)
 (mk z) <= mk x
参数：hy : y <= x；hz : x <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_le_max_mabs_mabs`：mabs_le_max_mabs_mabs (hab : a <= b) (hbc : b <= 
c) : |b|ₘ <= max |a|ₘ |c|ₘ
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `MulArchimedeanClass.mk_le_mk_of_mabs`：mk_le_mk_of_mabs {a b : M} (h : |a
|ₘ <= |b|ₘ) : mk b <= mk a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mabs_of_one_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] {
a : α} [MulLeftMono α], 1 ≤ a → |a|ₘ = a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `one_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [Mul
LeftMono α] [MulRightMono α] (a : α), 1 ≤ |a|ₘ
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `MulArchimedeanClass.mk_mabs`：mk_mabs (a : M) : mk |a|ₘ = mk a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
-/
theorem min_le_mk_of_le_of_le {x y z : M} (hy : y ≤ x) (hz : x ≤ z) : min (mk y) (mk z) ≤ mk x := by
  have H := mabs_le_max_mabs_mabs hy hz
  rw [← mabs_of_one_le (le_max_of_le_left (one_le_mabs y))] at H
  apply (mk_le_mk_of_mabs H).trans'
  obtain h | h := le_total |y|ₘ |z|ₘ
  · rw [max_eq_right h, min_eq_right, mk_mabs]
    exact mk_le_mk_of_mabs h
  · rw [max_eq_left h, min_eq_left, mk_mabs]
    exact mk_le_mk_of_mabs h

@[to_additive]
/-
**MulArchimedeanClass.min_le_mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：min_le_mk_mul (a b : M) : min (mk a) (mk b) <= mk (a * b)
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用引理 `mabs_mul_le`：mabs_mul_le (a b : α) : |a * b|ₘ <= |a|ₘ * |b|ₘ
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (mk_lt_mk.mp h.1 2).trans_le (mabs_mul_le _ _)
  have h2 := (mk_lt_mk.mp h.2 2).trans_le (mabs_mul_le _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_gt h2

@[to_additive]
/-
**MulArchimedeanClass.min_le_mk_div** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanCla
ss`。
形式化陈述：min_le_mk_div (a b : M) : min (mk a) (mk b) <= mk (a / b)
参数：a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `MulArchimedeanClass.min_le_mk_mul`：min_le_mk_mul (a b : M) : min (mk a) 
(mk b) <= mk (a * b)
-/
theorem min_le_mk_div (a b : M) : min (mk a) (mk b) ≤ mk (a / b) := by
  simpa [div_eq_mul_inv] using min_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]
/-
**MulArchimedeanClass.mk_left_le_mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedea
nClass`。
形式化陈述：mk_left_le_mk_mul (hab : mk a <= mk b) : mk a <= mk (a * b)
参数：hab : mk a <= mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `MulArchimedeanClass.min_le_mk_mul`：min_le_mk_mul (a b : M) : min (mk a) 
(mk b) <= mk (a * b)
-/
theorem mk_left_le_mk_mul (hab : mk a ≤ mk b) : mk a ≤ mk (a * b) := by
  simpa [hab] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
/-
**MulArchimedeanClass.mk_right_le_mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimede
anClass`。
形式化陈述：mk_right_le_mk_mul (hba : mk b <= mk a) : mk b <= mk (a * b)
参数：hba : mk b <= mk a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `MulArchimedeanClass.min_le_mk_mul`：min_le_mk_mul (a b : M) : min (mk a) 
(mk b) <= mk (a * b)
-/
theorem mk_right_le_mk_mul (hba : mk b ≤ mk a) : mk b ≤ mk (a * b) := by
  simpa [hba] using min_le_mk_mul (a := a) (b := b)

@[to_additive]
/-
**MulArchimedeanClass.mk_left_le_mk_div** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedea
nClass`。
形式化陈述：mk_left_le_mk_div (hab : mk a <= mk b) : mk a <= mk (a / b)
参数：hab : mk a <= mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_mul`：mk_left_le_mk_mul (hab : mk a <= 
mk b) : mk a <= mk (a * b)
-/
theorem mk_left_le_mk_div (hab : mk a ≤ mk b) : mk a ≤ mk (a / b) := by
  simpa [div_eq_mul_inv, hab] using mk_left_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive]
/-
**MulArchimedeanClass.mk_right_le_mk_div** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimede
anClass`。
形式化陈述：mk_right_le_mk_div (hba : mk b <= mk a) : mk b <= mk (a / b)
参数：hba : mk b <= mk a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulArchimedeanClass.mk_right_le_mk_mul`：mk_right_le_mk_mul (hba : mk b <
= mk a) : mk b <= mk (a * b)
-/
theorem mk_right_le_mk_div (hba : mk b ≤ mk a) : mk b ≤ mk (a / b) := by
  simpa [div_eq_mul_inv, hba] using mk_right_le_mk_mul (a := a) (b := b⁻¹)

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_left_le_mk_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：mk_left_le_mk_mul_iff : mk a <= mk (a * b) ↔ mk a <= mk b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_mul_cancel_left`：div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_div`：mk_left_le_mk_div (hab : mk a <= 
mk b) : mk a <= mk (a / b)
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_mul`：mk_left_le_mk_mul (hab : mk a <= 
mk b) : mk a <= mk (a * b)
-/
theorem mk_left_le_mk_mul_iff : mk a ≤ mk (a * b) ↔ mk a ≤ mk b where
  mp h := by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_mul

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_right_le_mk_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchi
medeanClass`。
形式化陈述：mk_right_le_mk_mul_iff : mk b <= mk (a * b) ↔ mk b <= mk a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_mul_iff`：mk_left_le_mk_mul_iff : mk a 
<= mk (a * b) ↔ mk a <= mk b where mp h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_right_le_mk_mul_iff : mk b ≤ mk (a * b) ↔ mk b ≤ mk a := by
  rw [mul_comm, mk_left_le_mk_mul_iff]

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_left_le_mk_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：mk_left_le_mk_div_iff : mk a <= mk (a / b) ↔ mk a <= mk b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_cancel`：div_div_cancel (a b : G) : a / (a / b) = b
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_div`：mk_left_le_mk_div (hab : mk a <= 
mk b) : mk a <= mk (a / b)
-/
theorem mk_left_le_mk_div_iff : mk a ≤ mk (a / b) ↔ mk a ≤ mk b where
  mp h := by simpa using mk_left_le_mk_div h
  mpr := mk_left_le_mk_div

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_right_le_mk_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchi
medeanClass`。
形式化陈述：mk_right_le_mk_div_iff : mk b <= mk (a / b) ↔ mk b <= mk a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulArchimedeanClass.mk_div_comm`：mk_div_comm (a b : M) : mk (a / b) = mk
 (b / a)
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_div_iff`：mk_left_le_mk_div_iff : mk a 
<= mk (a / b) ↔ mk a <= mk b where mp h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_right_le_mk_div_iff : mk b ≤ mk (a / b) ↔ mk b ≤ mk a := by
  rw [mk_div_comm, mk_left_le_mk_div_iff]

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_mul_lt_mk_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：mk_mul_lt_mk_left_iff : mk (a * b) < mk a ↔ mk b < mk a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_mul_iff`：mk_left_le_mk_mul_iff : mk a 
<= mk (a * b) ↔ mk a <= mk b where mp h
-/
theorem mk_mul_lt_mk_left_iff : mk (a * b) < mk a ↔ mk b < mk a :=
  le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_mul_iff

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_mul_lt_mk_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchi
medeanClass`。
形式化陈述：mk_mul_lt_mk_right_iff : mk (a * b) < mk b ↔ mk a < mk b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `MulArchimedeanClass.mk_right_le_mk_mul_iff`：mk_right_le_mk_mul_iff : mk 
b <= mk (a * b) ↔ mk b <= mk a
-/
theorem mk_mul_lt_mk_right_iff : mk (a * b) < mk b ↔ mk a < mk b :=
  le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_mul_iff

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_div_lt_mk_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：mk_div_lt_mk_left_iff : mk (a / b) < mk a ↔ mk b < mk a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_div_iff`：mk_left_le_mk_div_iff : mk a 
<= mk (a / b) ↔ mk a <= mk b where mp h
-/
theorem mk_div_lt_mk_left_iff : mk (a / b) < mk a ↔ mk b < mk a :=
  le_iff_le_iff_lt_iff_lt.1 mk_left_le_mk_div_iff

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mk_div_lt_mk_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchi
medeanClass`。
形式化陈述：mk_div_lt_mk_right_iff : mk (a / b) < mk b ↔ mk a < mk b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `MulArchimedeanClass.mk_right_le_mk_div_iff`：mk_right_le_mk_div_iff : mk 
b <= mk (a / b) ↔ mk b <= mk a
-/
theorem mk_div_lt_mk_right_iff : mk (a / b) < mk b ↔ mk a < mk b :=
  le_iff_le_iff_lt_iff_lt.1 mk_right_le_mk_div_iff

@[to_additive]
/-
**MulArchimedeanClass.mk_mul_eq_mk_left** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedea
nClass`。
形式化陈述：mk_mul_eq_mk_left (h : mk a < mk b) : mk (a * b) = mk a
参数：h : mk a < mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulArchimedeanClass.mk_le_mk`：mk_le_mk : mk a <= mk b ↔ exists n, |b|ₘ <
= |a|ₘ ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mabs_mul'`：mabs_mul' (a b : G) : |a|ₘ <= |b|ₘ * |b * a|ₘ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
· 使用定理 `MulArchimedeanClass.mk_left_le_mk_mul`：mk_left_le_mk_mul (hab : mk a <= 
mk b) : mk a <= mk (a * b)
-/
theorem mk_mul_eq_mk_left (h : mk a < mk b) : mk (a * b) = mk a := by
  refine le_antisymm (mk_le_mk.mpr ⟨2, ?_⟩) (mk_left_le_mk_mul h.le)
  rw [mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a, pow_two, mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

@[to_additive]
/-
**MulArchimedeanClass.mk_mul_eq_mk_right** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimede
anClass`。
形式化陈述：mk_mul_eq_mk_right (h : mk b < mk a) : mk (a * b) = mk b
参数：h : mk b < mk a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.mk_mul_eq_mk_left`：mk_mul_eq_mk_left (h : mk a < mk 
b) : mk (a * b) = mk a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mk_mul_eq_mk_right (h : mk b < mk a) : mk (a * b) = mk b :=
  mul_comm a b ▸ mk_mul_eq_mk_left h

@[to_additive]
/-
**MulArchimedeanClass.mk_div_eq_mk_left** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedea
nClass`。
形式化陈述：mk_div_eq_mk_left (h : mk a < mk b) : mk (a / b) = mk a
参数：h : mk a < mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulArchimedeanClass.mk_mul_eq_mk_left`：mk_mul_eq_mk_left (h : mk a < mk 
b) : mk (a * b) = mk a
-/
theorem mk_div_eq_mk_left (h : mk a < mk b) : mk (a / b) = mk a := by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_left (a := a) (b := b⁻¹)

@[to_additive]
/-
**MulArchimedeanClass.mk_div_eq_mk_right** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimede
anClass`。
形式化陈述：mk_div_eq_mk_right (h : mk b < mk a) : mk (a / b) = mk b
参数：h : mk b < mk a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulArchimedeanClass.mk_mul_eq_mk_right`：mk_mul_eq_mk_right (h : mk b < m
k a) : mk (a * b) = mk b
-/
theorem mk_div_eq_mk_right (h : mk b < mk a) : mk (a / b) = mk b := by
  simpa [h, div_eq_mul_inv] using mk_mul_eq_mk_right (a := a) (b := b⁻¹)

/-- The product over a set of an elements in distinct classes is in the lowest class. -/
@[to_additive /-- The sum over a set of an elements in distinct classes is in the lowest class. -/]
/-
**MulArchimedeanClass.mk_prod** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty
) {a : ι -> M} : StrictMonoOn (mk ∘ a) s -> mk (∏ i in s, (a i)) = mk (a (s.min'
 hnonempty))
参数：hnonempty : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.min'_singleton`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), 
{a}.min' ⋯ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `MulArchimedeanClass.mk_mul_eq_mk_left`：mk_mul_eq_mk_left (h : mk a < mk 
b) : mk (a * b) = mk a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.le_min'`：le_min' (x) (H2 : forall y in s, x <= y) : x <= s.min' H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The product over a set of an elements in distinct classes is in the lowest class
.
-/
theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι → M} :
    StrictMonoOn (mk ∘ a) s → mk (∏ i ∈ s, (a i)) = mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs ∈ (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (Finset.min'_mem _ _)
    have hne : mk (a i) ≠ mk (a (s.min' hs)) := by
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
/-
**MulArchimedeanClass.lt_of_mk_lt_mk_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `MulArc
himedeanClass`。
形式化陈述：lt_of_mk_lt_mk_of_one_le (h : mk a < mk b) (hpos : 1 <= a) : b < a
参数：h : mk a < mk b；hpos : 1 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_eq_self`：mabs_eq_self : |a|ₘ = a ↔ 1 <= a
· 使用定理 `mabs_lt`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [Mul
LeftMono α] {a b : α} [MulRightMono α],   |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
-/
theorem lt_of_mk_lt_mk_of_one_le (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]
/-
**MulArchimedeanClass.lt_of_mk_lt_mk_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MulArc
himedeanClass`。
形式化陈述：lt_of_mk_lt_mk_of_le_one (h : mk a < mk b) (hneg : a <= 1) : a < b
参数：h : mk a < mk b；hneg : a <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_eq_inv_self`：mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a <= 1
· 使用定理 `mabs_lt`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] [Mul
LeftMono α] {a b : α} [MulRightMono α],   |a|ₘ < b ↔ b⁻¹ < a ∧ a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulArchimedeanClass.mk_lt_mk`：mk_lt_mk : mk a < mk b ↔ forall n, |b|ₘ ^ 
n < |a|ₘ
-/
theorem lt_of_mk_lt_mk_of_le_one (h : mk a < mk b) (hneg : a ≤ 1) : a < b := by
  obtain h := mk_lt_mk.mp h 1
  rw [pow_one, mabs_lt, mabs_eq_inv_self.mpr hneg, inv_inv] at h
  exact h.1

@[to_additive]
/-
**MulArchimedeanClass.one_lt_of_one_lt_of_mk_lt** 是 Mathlib 中的一个定理，位于命名空间 `MulAr
chimedeanClass`。
形式化陈述：one_lt_of_one_lt_of_mk_lt (ha : 1 < a) (hab : mk a < mk (b / a)) : 1 < b
参数：ha : 1 < a；hab : mk a < mk (b / a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.lt_of_mk_lt_mk_of_le_one`：lt_of_mk_lt_mk_of_le_one (
h : mk a < mk b) (hneg : a <= 1) : a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem one_lt_of_one_lt_of_mk_lt (ha : 1 < a) (hab : mk a < mk (b / a)) :
    1 < b := by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

@[to_additive archimedean_of_mk_eq_mk]
/-
**MulArchimedeanClass.mulArchimedean_of_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulA
rchimedeanClass`。
形式化陈述：mulArchimedean_of_mk_eq_mk (h : forall a != (1 : M), forall b != 1, mk a =
 mk b) : MulArchimedean M where arch x y hy
参数：h : forall a != (1 : M), forall b != 1, mk a = mk b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulArchimedeanClass.mk_eq_mk`：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists
 m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mabs_eq_self`：mabs_eq_self : |a|ₘ = a ↔ 1 <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mulArchimedean_of_mk_eq_mk (h : ∀ a ≠ (1 : M), ∀ b ≠ 1, mk a = mk b) :
    MulArchimedean M where
  arch x y hy := by
    by_cases! hx : x ≤ 1
    · use 0
      simpa using hx
    · have hxy : mk x = mk y := h x hx.ne.symm y hy.ne.symm
      obtain ⟨_, ⟨m, hm⟩⟩ := mk_eq_mk.mp hxy
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact ⟨m, hm⟩

@[to_additive mk_eq_mk_of_archimedean]
/-
**MulArchimedeanClass.mk_eq_mk_of_mulArchimedean** 是 Mathlib 中的一个定理，位于命名空间 `MulA
rchimedeanClass`。
形式化陈述：mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a != 1) (hb : b != 1) 
: mk a = mk b
参数：ha : a != 1；hb : b != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulArchimedeanClass.mk_eq_mk`：mk_eq_mk {a b : M} : mk a = mk b ↔ (exists
 m, |b|ₘ <= |a|ₘ ^ m) ∧ (exists n, |a|ₘ <= |b|ₘ ^ n)
· 使用定理 `MulArchimedean.arch`：∀ {R : Type u_2} {inst : CommMonoid R} {inst_1 : Pa
rtialOrder R} [self : MulArchimedean R] (x : R) {y : R},   1 < y → ∃ n, x ≤ y ^ 
n
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem mk_eq_mk_of_mulArchimedean [MulArchimedean M] (ha : a ≠ 1) (hb : b ≠ 1) :
    mk a = mk b := by
  obtain hm := MulArchimedean.arch |b|ₘ (show 1 < |a|ₘ by simpa using ha)
  obtain hn := MulArchimedean.arch |a|ₘ (show 1 < |b|ₘ by simpa using hb)
  exact mk_eq_mk.mpr ⟨hm, hn⟩

section Hom
variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/
@[to_additive
/-- An `OrderAddMonoidHom` can be lifted to an `OrderHom` over archimedean classes. -/]
/-
**MulArchimedeanClass.orderHom** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：orderHom (f : M ->*o N) : MulArchimedeanClass M ->o MulArchimedeanClass N
参数：f : M ->*o N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def orderHom (f : M →*o N) : MulArchimedeanClass M →o MulArchimedeanClass N :=
  (MulArchimedeanOrder.orderHom f).antisymmetrization

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.orderHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass
`。
形式化陈述：orderHom_mk (f : M ->*o N) (a : M) : orderHom f (mk a) = mk (f a)
参数：f : M ->*o N；a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderHom_mk (f : M →*o N) (a : M) : orderHom f (mk a) = mk (f a) := rfl

@[to_additive]
/-
**MulArchimedeanClass.map_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：map_mk_eq (f : M ->*o N) (h : mk a = mk b) : mk (f a) = mk (f b)
参数：f : M ->*o N；h : mk a = mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.orderHom_mk`：orderHom_mk (f : M ->*o N) (a : M) : or
derHom f (mk a) = mk (f a)
-/
theorem map_mk_eq (f : M →*o N) (h : mk a = mk b) : mk (f a) = mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk, h]

@[to_additive]
/-
**MulArchimedeanClass.map_mk_le** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClass`。
形式化陈述：map_mk_le (f : M ->*o N) (h : mk a <= mk b) : mk (f a) <= mk (f b)
参数：f : M ->*o N；h : mk a <= mk b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.orderHom_mk`：orderHom_mk (f : M ->*o N) (a : M) : or
derHom f (mk a) = mk (f a)
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
-/
theorem map_mk_le (f : M →*o N) (h : mk a ≤ mk b) : mk (f a) ≤ mk (f b) := by
  rw [← orderHom_mk, ← orderHom_mk]
  exact OrderHomClass.monotone _ h

@[to_additive]
/-
**MulArchimedeanClass.orderHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimede
anClass`。
形式化陈述：orderHom_injective {f : M ->*o N} (h : Function.Injective f) : Function.In
jective (orderHom f)
参数：h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.ind`：ind {motive : MulArchimedeanClass M -> Prop} (m
k : forall a, motive (.mk a)) : forall x, motive x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderMonoidHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneC
lass β], OrderHomClass…
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…
-/
theorem orderHom_injective {f : M →*o N} (h : Function.Injective f) :
    Function.Injective (orderHom f) := by
  intro a b
  induction a using ind with | mk a
  induction b using ind with | mk b
  simp_rw [orderHom_mk, mk_eq_mk, ← map_mabs, ← map_pow]
  obtain hmono := (OrderHomClass.monotone f).strictMono_of_injective h
  intro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  exact ⟨⟨m, hmono.le_iff_le.mp hm⟩, ⟨n, hmono.le_iff_le.mp hn⟩⟩

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.orderHom_top** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanClas
s`。
形式化陈述：orderHom_top (f : M ->*o N) : orderHom f ⊤ = ⊤
参数：f : M ->*o N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulArchimedeanClass.mk_one`：mk_one : mk 1 = (⊤ : MulArchimedeanClass M)
· 使用定理 `MulArchimedeanClass.orderHom_mk`：orderHom_mk (f : M ->*o N) (a : M) : or
derHom f (mk a) = mk (f a)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
-/
theorem orderHom_top (f : M →*o N) : orderHom f ⊤ = ⊤ := by
  rw [← mk_one, ← mk_one, orderHom_mk, map_one]

end Hom

section LiftHom

variable {α : Type*} [PartialOrder α]

/-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `MulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `M → α` that's monotone along archimedean classes to a
monotone function `ArchimedeanClass M →o α`. -/]
/-
**MulArchimedeanClass.liftOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClas
s`。
形式化陈述：liftOrderHom (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b) : M
ulArchimedeanClass M ->o α where toFun
参数：f : M -> α；h : forall a b, mk a <= mk b -> f a <= f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOrderHom (f : M → α) (h : ∀ a b, mk a ≤ mk b → f a ≤ f b) :
    MulArchimedeanClass M →o α where
  toFun := lift f fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hle := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa using h a b (mk_le_mk.mp hle)

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.liftOrderHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanC
lass`。
形式化陈述：liftOrderHom_mk (f : M -> α) (h : forall a b, mk a <= mk b -> f a <= f b) 
(a : M) : liftOrderHom f h (mk a) = f a
参数：f : M -> α；h : forall a b, mk a <= mk b -> f a <= f b；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.lift_mk`：lift_mk {α : Type*} (f : M -> α) (h : foral
l a b, mk a = mk b -> f a = f b) (a : M) : lift f h (mk a) = f a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem liftOrderHom_mk (f : M → α) (h : ∀ a b, mk a ≤ mk b → f a ≤ f b) (a : M) :
    liftOrderHom f h (mk a) = f a :=
  lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) a

end LiftHom

/-- Given a `UpperSet` of `MulArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/
@[to_additive /-- Given a `UpperSet` of `ArchimedeanClass`,
all group elements belonging to these classes form a subsemigroup.
This is not yet a subgroup because it doesn't contain the identity if `s = ⊤`. -/]
/-
**MulArchimedeanClass.subsemigroup** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClas
s`。
形式化陈述：subsemigroup (s : UpperSet (MulArchimedeanClass M)) : Subsemigroup M where
 carrier
参数：s : UpperSet (MulArchimedeanClass M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subsemigroup (s : UpperSet (MulArchimedeanClass M)) : Subsemigroup M where
  carrier := mk ⁻¹' s
  mul_mem' {a b} ha hb := by
    rw [Set.mem_preimage] at ha hb ⊢
    obtain h | h := min_le_iff.mp (min_le_mk_mul a b)
    · exact s.upper h ha
    · exact s.upper h hb

@[to_additive]
/-
**MulArchimedeanClass.subsemigroup_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `MulArch
imedeanClass`。
形式化陈述：subsemigroup_strictAnti : StrictAnti (subsemigroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_ssubset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike
 A B] [inst_1 : PartialOrder A] [IsConcreteLE A B] {S T : A},   ↑S ⊂ ↑T ↔ S < T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_subset_ne`：∀ {α : Type u} {s t : Set α}, s ⊂ t ↔ s ⊆ t ∧
 s ≠ t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem subsemigroup_strictAnti : StrictAnti (subsemigroup (M := M)) := by
  intro s t hst
  rw [← SetLike.coe_ssubset_coe]
  refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h ↦ hst.le h, ?_⟩
  contrapose! hst with heq
  apply le_of_eq
  simpa [MulArchimedeanClass.mk_surjective, MulArchimedeanClass.subsemigroup] using heq

/-- Make `MulArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/
@[to_additive /-- Make `ArchimedeanClass.subsemigroup` a subgroup by assigning
s = ⊤ with a junk value ⊥. -/]
noncomputable
/-
**MulArchimedeanClass.subgroup** 是 Mathlib 中的一个定义，位于命名空间 `MulArchimedeanClass`。
形式化陈述：subgroup (s : UpperSet (MulArchimedeanClass M)) : Subgroup M
参数：s : UpperSet (MulArchimedeanClass M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subgroup (s : UpperSet (MulArchimedeanClass M)) : Subgroup M :=
  if hs : s = ⊤ then
    ⊥
  else {
    subsemigroup s with
    one_mem' := by
      rw [subsemigroup, Set.mem_preimage]
      obtain ⟨u, hu⟩ := UpperSet.coe_nonempty.mpr hs
      simpa using s.upper (by simp) hu
    inv_mem' := by simp [subsemigroup]
  }

variable {s : UpperSet (MulArchimedeanClass M)}

@[to_additive]
/-
**MulArchimedeanClass.subsemigroup_eq_subgroup_of_ne_top** 是 Mathlib 中的一个定理，位于命名
空间 `MulArchimedeanClass`。
形式化陈述：subsemigroup_eq_subgroup_of_ne_top (hs : s != ⊤) : subsemigroup s = (subgr
oup s : Set M)
参数：hs : s != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsemigroup_eq_subgroup_of_ne_top (hs : s ≠ ⊤) :
    subsemigroup s = (subgroup s : Set M) := by
  simp [subgroup, hs]

variable (M) in
@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.subgroup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedeanC
lass`。
形式化陈述：subgroup_eq_bot : subgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subgroup_eq_bot : subgroup (M := M) ⊤ = ⊥ := by
  simp [subgroup]

@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.mem_subgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedean
Class`。
形式化陈述：mem_subgroup_iff (hs : s != ⊤) : a in subgroup s ↔ mk a in s
参数：hs : s != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subgroup_iff (hs : s ≠ ⊤) : a ∈ subgroup s ↔ mk a ∈ s := by
  simp [subgroup, subsemigroup, hs]

@[to_additive]
/-
**MulArchimedeanClass.subgroup_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：subgroup_strictAntiOn : StrictAntiOn (subgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_ssubset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike
 A B] [inst_1 : PartialOrder A] [IsConcreteLE A B] {S T : A},   ↑S ⊂ ↑T ↔ S < T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `MulArchimedeanClass.subsemigroup_eq_subgroup_of_ne_top`：subsemigroup_eq_
subgroup_of_ne_top (hs : s != ⊤) : subsemigroup s = (subgroup s : Set M)
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_subset_ne`：∀ {α : Type u} {s t : Set α}, s ⊂ t ↔ s ⊆ t ∧
 s ≠ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulArchimedeanClass.range_mk`：range_mk : Set.range (mk (M
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
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
/-
**MulArchimedeanClass.subgroup_antitone** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedea
nClass`。
形式化陈述：subgroup_antitone : Antitone (subgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulArchimedeanClass.subgroup_eq_bot`：subgroup_eq_bot : subgroup (M
· 使用定理 `StrictAntiOn.le_iff_ge`：StrictAntiOn.le_iff_ge (hf : StrictAntiOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ b <= a
· 使用定理 `MulArchimedeanClass.subgroup_strictAntiOn`：subgroup_strictAntiOn : Stric
tAntiOn (subgroup (M
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
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
/-
**MulArchimedeanClass.ballSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `MulArchimedeanCl
ass`。
形式化陈述：ballSubgroup (c : MulArchimedeanClass M)
参数：c : MulArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ballSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ioi c)

/-- A closed ball defined by `MulArchimedeanClass.subgroup` of `UpperSet.Ici c`. -/
@[to_additive /-- A closed ball defined by `ArchimedeanClass.addSubgroup` of `UpperSet.Ici c`. -/]
noncomputable
/-
**MulArchimedeanClass.closedBallSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `MulArchime
deanClass`。
形式化陈述：closedBallSubgroup (c : MulArchimedeanClass M)
参数：c : MulArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev closedBallSubgroup (c : MulArchimedeanClass M) := subgroup (UpperSet.Ici c)

@[to_additive]
/-
**MulArchimedeanClass.mem_ballSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulArchime
deanClass`。
形式化陈述：mem_ballSubgroup_iff {a : M} {c : MulArchimedeanClass M} (hA : c != ⊤) : a
 in ballSubgroup c ↔ c < mk a
参数：hA : c != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ballSubgroup_iff {a : M} {c : MulArchimedeanClass M} (hA : c ≠ ⊤) :
    a ∈ ballSubgroup c ↔ c < mk a := by
  simp [hA]

@[to_additive]
/-
**MulArchimedeanClass.mem_closedBallSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulA
rchimedeanClass`。
形式化陈述：mem_closedBallSubgroup_iff {a : M} {c : MulArchimedeanClass M} : a in clos
edBallSubgroup c ↔ c <= mk a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closedBallSubgroup_iff {a : M} {c : MulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ c ≤ mk a := by
  simp

variable (M) in
@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.ballSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `MulArchimedean
Class`。
形式化陈述：ballSubgroup_top : ballSubgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.Ioi_top`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTo
p α], UpperSet.Ioi ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulArchimedeanClass.subgroup_eq_bot`：subgroup_eq_bot : subgroup (M
-/
theorem ballSubgroup_top : ballSubgroup (M := M) ⊤ = ⊥ := by
  convert! subgroup_eq_bot M
  simp

variable (M) in
@[to_additive (attr := simp)]
/-
**MulArchimedeanClass.closedBallSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `MulArchi
medeanClass`。
形式化陈述：closedBallSubgroup_top : closedBallSubgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedBallSubgroup_top : closedBallSubgroup (M := M) ⊤ = ⊥ := by
  ext
  simp

@[to_additive]
/-
**MulArchimedeanClass.ballSubgroup_antitone** 是 Mathlib 中的一个定理，位于命名空间 `MulArchim
edeanClass`。
形式化陈述：ballSubgroup_antitone : Antitone (ballSubgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.subgroup_antitone`：subgroup_antitone : Antitone (sub
group (M
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `UpperSet.Ioi_strictMono`：Ioi_strictMono : StrictMono (Ioi (α
-/
theorem ballSubgroup_antitone : Antitone (ballSubgroup (M := M)) := by
  intro _ _ h
  exact subgroup_antitone <| (UpperSet.Ioi_strictMono _).monotone h

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
/-
**FiniteMulArchimedeanClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FiniteMulArchimedeanClass
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FiniteMulArchimedeanClass := {A : MulArchimedeanClass M // A ≠ ⊤}

namespace FiniteMulArchimedeanClass

/-- Create a `FiniteMulArchimedeanClass` from a non-one element. -/
@[to_additive /-- Create a `FiniteArchimedeanClass` from a non-zero element. -/]
/-
**FiniteMulArchimedeanClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMulArchimedeanCl
ass`。
形式化陈述：mk (a : M) (h : a != 1) : FiniteMulArchimedeanClass M
参数：a : M；h : a != 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `FiniteMulArchimedeanClass` from a non-one element.
-/
def mk (a : M) (h : a ≠ 1) : FiniteMulArchimedeanClass M :=
  ⟨MulArchimedeanClass.mk a, MulArchimedeanClass.mk_eq_top_iff.not.mpr h⟩

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchimede
anClass`。
形式化陈述：val_mk {a : M} (h : a != 1) : (mk a h).val = MulArchimedeanClass.mk a
参数：h : a != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mk {a : M} (h : a ≠ 1) : (mk a h).val = MulArchimedeanClass.mk a := rfl

@[to_additive]
/-
**FiniteMulArchimedeanClass.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchime
deanClass`。
形式化陈述：mk_le_mk {a : M} (ha : a != 1) {b : M} (hb : b != 1) : mk a ha <= mk b hb 
↔ MulArchimedeanClass.mk a <= MulArchimedeanClass.mk b
参数：ha : a != 1；hb : b != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {a : M} (ha : a ≠ 1) {b : M} (hb : b ≠ 1) :
    mk a ha ≤ mk b hb ↔ MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b := .rfl

@[to_additive]
/-
**FiniteMulArchimedeanClass.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchime
deanClass`。
形式化陈述：mk_lt_mk {a : M} (ha : a != 1) {b : M} (hb : b != 1) : mk a ha < mk b hb ↔
 MulArchimedeanClass.mk a < MulArchimedeanClass.mk b
参数：ha : a != 1；hb : b != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk {a : M} (ha : a ≠ 1) {b : M} (hb : b ≠ 1) :
    mk a ha < mk b hb ↔ MulArchimedeanClass.mk a < MulArchimedeanClass.mk b := .rfl
/-
**FiniteMulArchimedeanClass.min_le_mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulAr
chimedeanClass`。
形式化陈述：∀ {M : Type u_1} [inst : CommGroup M] [inst_1 : LinearOrder M] [inst_2 : I
sOrderedMonoid M] {a b : M} (ha : a ≠ 1)   (hb : b ≠ 1) (hab : a * b ≠ 1),   min
 (FiniteMulArchimedeanClass.mk a ha) (FiniteMulArchimedeanClass.mk b hb) ≤ Finit
eMulArchimedeanClass.mk (a * b) hab
参数：ha : a ≠ 1；hb : b ≠ 1；hab : a * b ≠ 1；FiniteMulArchimedeanClass.mk a ha；Finit
eMulArchimedeanClass.mk b hb；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.min_le_mk_mul`：min_le_mk_mul (a b : M) : min (mk a) 
(mk b) <= mk (a * b)
-/
@[to_additive] theorem min_le_mk_mul {a b : M} (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a * b ≠ 1) : min (mk a ha) (mk b hb) ≤ mk (a * b) hab :=
  MulArchimedeanClass.min_le_mk_mul a b
/-
**FiniteMulArchimedeanClass.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchimede
anClass`。
形式化陈述：∀ {M : Type u_1} [inst : CommGroup M] [inst_1 : LinearOrder M] [inst_2 : I
sOrderedMonoid M] {a : M} (ha : a ≠ 1),   FiniteMulArchimedeanClass.mk a⁻¹ ⋯ = F
initeMulArchimedeanClass.mk a ha
参数：ha : a ≠ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MulArchimedeanClass.mk_inv`：mk_inv (a : M) : mk a⁻¹ = mk a
-/
@[to_additive] theorem mk_inv {a : M} (ha : a ≠ 1) : mk a⁻¹ (by simp [ha]) = mk a ha :=
  Subtype.ext (MulArchimedeanClass.mk_inv a)

/-- An induction principle for `FiniteMulArchimedeanClass`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for `FiniteArchimedeanClass`. -/]
/-
**FiniteMulArchimedeanClass.ind** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchimedeanC
lass`。
形式化陈述：ind {motive : FiniteMulArchimedeanClass M -> Prop} (mk : forall a, (ha : a
 != 1) -> motive (.mk a ha)) : forall x, motive x
参数：mk : forall a, (ha : a != 1) -> motive (.mk a ha)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a

--- 原说明 ---
An induction principle for `FiniteMulArchimedeanClass`.
-/
theorem ind {motive : FiniteMulArchimedeanClass M → Prop}
    (mk : ∀ a, (ha : a ≠ 1) → motive (.mk a ha)) : ∀ x, motive x := by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

@[to_additive]
/-
**FiniteMulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteMulArchimedeanClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulArchimedean M] : Subsingleton (FiniteMulArchimedeanClass M) where
  allEq A B := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa [mk] using MulArchimedeanClass.mk_eq_mk_of_mulArchimedean ha hb

@[to_additive]
/-
**FiniteMulArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteMulArchimedeanClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nonempty (FiniteMulArchimedeanClass M) := by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  exact ⟨mk x hx, by simpa using hx⟩

/-- Lift a `f : {a : M // a ≠ 1} → α` function to `FiniteMulArchimedeanClass M → α`. -/
@[to_additive /-- Lift a `f : {a : M // a ≠ 0} → α` function to `FiniteArchimedeanClass M → α`. -/]
/-
**FiniteMulArchimedeanClass.lift** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMulArchimedean
Class`。
形式化陈述：lift {α : Type*} (f : {a : M // a != 1} -> α) (h : forall (a b : {a : M //
 a != 1}), mk a.val a.prop = mk b.val b.prop -> f a = f b) : FiniteMulArchimedea
nClass M -> α
参数：f : {a : M // a != 1} -> α；h : forall (a b : {a : M // a != 1}), mk a.val a.p
rop = mk b.val b.prop -> f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `f : {a : M // a ≠ 1} → α` function to `FiniteMulArchimedeanClass M → α`.
-/
def lift {α : Type*} (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop = mk b.val b.prop → f a = f b) :
    FiniteMulArchimedeanClass M → α := fun ⟨A, hA⟩ ↦ by
  refine (MulArchimedeanClass.lift
    (fun b ↦ if h : b = 1 then ⊤ else WithTop.some (f ⟨b, h⟩)) (fun a b h' ↦ ?_) A).untop ?_
  · split_ifs with ha hb hb
    · rfl
    · exact (hb (MulArchimedeanClass.mk_eq_top_iff.mp (ha ▸ h').symm)).elim
    · exact (ha (MulArchimedeanClass.mk_eq_top_iff.mp (by apply hb ▸ h'))).elim
    · rw [h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [mk] using h')]
  · induction A using MulArchimedeanClass.ind with | mk a
    simpa using MulArchimedeanClass.mk_eq_top_iff.not.mp hA

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMulArchimed
eanClass`。
形式化陈述：lift_mk {α : Type*} (f : {a : M // a != 1} -> α) (h : forall (a b : {a : M
 // a != 1}), mk a.val a.prop = mk b.val b.prop -> f a = f b) {a : M} (ha : a !=
 1) : lift f h (mk a ha) = f ⟨a, ha⟩
参数：f : {a : M // a != 1} -> α；h : forall (a b : {a : M // a != 1}), mk a.val a.p
rop = mk b.val b.prop -> f a = f b；ha : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `MulArchimedeanClass.lift.congr_simp`：∀ {M : Type u_1} [inst : CommGroup 
M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedMonoid M] {α : Type u_2}   (f f_1
 : M → α) (e_f : f = f_1)…
· 使用定理 `MulArchimedeanClass.lift_mk`：lift_mk {α : Type*} (f : M -> α) (h : foral
l a b, mk a = mk b -> f a = f b) (a : M) : lift f h (mk a) = f a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_mk {α : Type*} (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop = mk b.val b.prop → f a = f b)
    {a : M} (ha : a ≠ 1) :
    lift f h (mk a ha) = f ⟨a, ha⟩ := by simp [lift, mk, ha]

/-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean classes to a
monotone function `FiniteMulArchimedeanClass M →o α`. -/
@[to_additive /-- Lift a function `{a : M // a ≠ 1} → α` that's monotone along archimedean
classes to a monotone function `FiniteArchimedeanClass M₁ →o α`. -/]
/-
**FiniteMulArchimedeanClass.liftOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMulArc
himedeanClass`。
形式化陈述：liftOrderHom {α : Type*} [PartialOrder α] (f : {a : M // a != 1} -> α) (h 
: forall (a b : {a : M // a != 1}), mk a.val a.prop <= mk b.val b.prop -> f a <=
 f b) : FiniteMulArchimedeanClass M ->o α where toFun
参数：f : {a : M // a != 1} -> α；h : forall (a b : {a : M // a != 1}), mk a.val a.p
rop <= mk b.val b.prop -> f a <= f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOrderHom {α : Type*} [PartialOrder α]
    (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop ≤ mk b.val b.prop → f a ≤ f b) :
    FiniteMulArchimedeanClass M →o α where
  toFun := lift f fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)
  monotone' A B hAB := by
    induction A using ind with | mk a ha
    induction B using ind with | mk b hb
    simpa using h ⟨a, ha⟩ ⟨b, hb⟩ hAB

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.liftOrderHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMul
ArchimedeanClass`。
形式化陈述：liftOrderHom_mk {α : Type*} [PartialOrder α] (f : {a : M // a != 1} -> α) 
(h : forall (a b : {a : M // a != 1}), mk a.val a.prop <= mk b.val b.prop -> f a
 <= f b) {a : M} (ha : a != 1) : liftOrderHom f h (mk a ha) = f ⟨a, ha⟩
参数：f : {a : M // a != 1} -> α；h : forall (a b : {a : M // a != 1}), mk a.val a.p
rop <= mk b.val b.prop -> f a <= f b；ha : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `FiniteMulArchimedeanClass.lift_mk`：lift_mk {α : Type*} (f : {a : M // a 
!= 1} -> α) (h : forall (a b : {a : M // a != 1}), mk a.val a.prop = mk b.val b.
prop -> f a = f b) {a :…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem liftOrderHom_mk {α : Type*} [PartialOrder α]
    (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), mk a.val a.prop ≤ mk b.val b.prop → f a ≤ f b)
    {a : M} (ha : a ≠ 1) : liftOrderHom f h (mk a ha) = f ⟨a, ha⟩ :=
  lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) ha

variable (M) in
/-- Adding top to the type of finite classes yields the type of all classes. -/
@[to_additive /-- Adding top to the type of finite classes yields the type of all classes. -/]
noncomputable
/-
**FiniteMulArchimedeanClass.withTopOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMul
ArchimedeanClass`。
形式化陈述：withTopOrderIso : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanC
lass M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def withTopOrderIso : WithTop (FiniteMulArchimedeanClass M) ≃o MulArchimedeanClass M :=
  WithTop.subtypeOrderIso

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.withTopOrderIso_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 
`FiniteMulArchimedeanClass`。
形式化陈述：withTopOrderIso_apply_coe (A : FiniteMulArchimedeanClass M) : withTopOrder
Iso M (A : WithTop (FiniteMulArchimedeanClass M)) = A.val
参数：A : FiniteMulArchimedeanClass M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.subtypeOrderIso_apply_coe`：subtypeOrderIso_apply_coe [PartialOrd
er α] [OrderTop α] [DecidablePred (· = (⊤ : α))] (a : {a : α // a != ⊤}) : subty
peOrderIso (a : WithTop…
-/
theorem withTopOrderIso_apply_coe (A : FiniteMulArchimedeanClass M) :
    withTopOrderIso M (A : WithTop (FiniteMulArchimedeanClass M)) = A.val :=
  WithTop.subtypeOrderIso_apply_coe A

@[to_additive]
/-
**FiniteMulArchimedeanClass.withTopOrderIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 `FiniteMulArchimedeanClass`。
形式化陈述：withTopOrderIso_symm_apply {a : M} (h : a != 1) : (withTopOrderIso M).symm
 (MulArchimedeanClass.mk a) = mk a h
参数：h : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.subtypeOrderIso_symm_apply`：subtypeOrderIso_symm_apply [PartialO
rder α] [OrderTop α] [DecidablePred (· = (⊤ : α))] {a : α} (h : a != ⊤) : subtyp
eOrderIso.symm a = (⟨a, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `MulArchimedeanClass.mk_eq_top_iff`：mk_eq_top_iff : mk a = ⊤ ↔ a = 1 wher
e mp
-/
theorem withTopOrderIso_symm_apply {a : M} (h : a ≠ 1) :
    (withTopOrderIso M).symm (MulArchimedeanClass.mk a) = mk a h :=
  WithTop.subtypeOrderIso_symm_apply (MulArchimedeanClass.mk_eq_top_iff.ne.mpr h)

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

/-- An `OrderIso` on `MulArchimedeanClass` induces an `OrderIso` on `FiniteMulArchimedeanClass`. -/
@[to_additive
/-- An `OrderIso` on `ArchimedeanClass` induces an `OrderIso` on `FiniteArchimedeanClass`. -/]
noncomputable
/-
**FiniteMulArchimedeanClass.congrOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMulAr
chimedeanClass`。
形式化陈述：congrOrderIso (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) : Finit
eMulArchimedeanClass M ≃o FiniteMulArchimedeanClass N where __
参数：e : MulArchimedeanClass M ≃o MulArchimedeanClass N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def congrOrderIso (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) :
    FiniteMulArchimedeanClass M ≃o FiniteMulArchimedeanClass N where
  __ := Equiv.subtypeEquiv e (by simp)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.coe_congrOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `F
initeMulArchimedeanClass`。
形式化陈述：coe_congrOrderIso_apply (e : MulArchimedeanClass M ≃o MulArchimedeanClass 
N) (a : FiniteMulArchimedeanClass M) : (congrOrderIso e a : MulArchimedeanClass 
N) = e a
参数：e : MulArchimedeanClass M ≃o MulArchimedeanClass N；a : FiniteMulArchimedeanCl
ass M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_congrOrderIso_apply (e : MulArchimedeanClass M ≃o MulArchimedeanClass N)
    (a : FiniteMulArchimedeanClass M) :
    (congrOrderIso e a : MulArchimedeanClass N) = e a := rfl

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.congrOrderIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finite
MulArchimedeanClass`。
形式化陈述：congrOrderIso_symm (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) : 
(congrOrderIso e).symm = congrOrderIso e.symm
参数：e : MulArchimedeanClass M ≃o MulArchimedeanClass N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrOrderIso_symm (e : MulArchimedeanClass M ≃o MulArchimedeanClass N) :
    (congrOrderIso e).symm = congrOrderIso e.symm := rfl

/-- The upper set in `MulArchimedeanClass M` consisting of an upper set in
`FiniteMulArchimedeanClass M` plus `⊤`. -/
@[to_additive /-- The upper set in `ArchimedeanClass M` consisting of an upper set in
`FiniteArchimedeanClass M` plus `⊤`. -/]
/-
**FiniteMulArchimedeanClass.toUpperSetMulArchimedeanClass** 是 Mathlib 中的一个定义，位于命
名空间 `FiniteMulArchimedeanClass`。
形式化陈述：toUpperSetMulArchimedeanClass : UpperSet (FiniteMulArchimedeanClass M) ↪o 
UpperSet (MulArchimedeanClass M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def toUpperSetMulArchimedeanClass :
    UpperSet (FiniteMulArchimedeanClass M) ↪o UpperSet (MulArchimedeanClass M) :=
  .ofStrictMono (fun s ↦
    { carrier := {a | ∀ h : a ≠ ⊤, ⟨a, h⟩ ∈ s}
      upper' _ _ le mem ne := s.upper le (mem <| ne_top_of_le_ne_top ne le) })
  fun s t lt ↦ by
    simp_rw [lt_iff_le_not_ge] at lt ⊢
    exact ⟨fun _ mem ne ↦ lt.1 (mem _), fun hst ↦ lt.2 fun x mem ↦ hst (fun _ ↦ mem) x.2⟩

/-- The `MulArchimedeanClass.subsemigroup` associated to an upper set in
`FiniteMulArchimedeanClass M` is a subgroup. -/
@[to_additive /-- The `ArchimedeanClass.subsemigroup` associated to an upper set in
`FiniteArchimedeanClass M` is a subgroup. -/]
/-
**FiniteMulArchimedeanClass.subgroup** 是 Mathlib 中的一个定义，位于命名空间 `FiniteMulArchime
deanClass`。
形式化陈述：subgroup (s : UpperSet (FiniteMulArchimedeanClass M)) : Subgroup M where _
_
参数：s : UpperSet (FiniteMulArchimedeanClass M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def subgroup (s : UpperSet (FiniteMulArchimedeanClass M)) : Subgroup M where
  __ := MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s)
  one_mem' h := (h rfl).elim
  inv_mem' := by simp [MulArchimedeanClass.subsemigroup]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

@[to_additive]
/-
**FiniteMulArchimedeanClass.subsemigroup_eq_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `
FiniteMulArchimedeanClass`。
形式化陈述：subsemigroup_eq_subgroup : MulArchimedeanClass.subsemigroup (toUpperSetMul
ArchimedeanClass s) = (subgroup s : Set M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subsemigroup_eq_subgroup :
    MulArchimedeanClass.subsemigroup (toUpperSetMulArchimedeanClass s) = (subgroup s : Set M) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (M) in
@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.subgroup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMul
ArchimedeanClass`。
形式化陈述：subgroup_eq_bot : subgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `UpperSet.mk.congr_simp`：∀ {α : Type u_1} [inst : LE α] (carrier carrier_
1 : Set α) (e_carrier : carrier = carrier_1)   (upper' : IsUpperSet carrier), { 
carrier := c…
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.mk.congr_simp`：∀ {G : Type u_3} [inst : Group G] (toSubmonoid t
oSubmonoid_1 : Submonoid G)   (e_toSubmonoid : toSubmonoid = toSubmonoid_1)   (i
nv_mem' : ∀ …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subgroup_eq_bot : subgroup (M := M) ⊤ = ⊥ := by
  ext; simp [subgroup, MulArchimedeanClass.subsemigroup, toUpperSetMulArchimedeanClass]

@[to_additive (attr := simp)]
/-
**FiniteMulArchimedeanClass.mem_subgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMu
lArchimedeanClass`。
形式化陈述：mem_subgroup_iff : a in subgroup s ↔ forall h : a != 1, mk a h in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subgroup_iff : a ∈ subgroup s ↔ ∀ h : a ≠ 1, mk a h ∈ s := by
  simp_rw [mk, Ne, ← MulArchimedeanClass.mk_eq_top_iff]; rfl
/-
**FiniteMulArchimedeanClass.subgroup_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Finit
eMulArchimedeanClass`。
形式化陈述：∀ {M : Type u_1} [inst : CommGroup M] [inst_1 : LinearOrder M] [inst_2 : I
sOrderedMonoid M],   StrictAnti FiniteMulArchimedeanClass.subgroup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulArchimedeanClass.subsemigroup_strictAnti`：subsemigroup_strictAnti : S
trictAnti (subsemigroup (M
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
@[to_additive] theorem subgroup_strictAnti : StrictAnti (subgroup (M := M)) := fun _ _ h ↦
  MulArchimedeanClass.subsemigroup_strictAnti (toUpperSetMulArchimedeanClass.strictMono h)

/-- An open ball defined by `FiniteMulArchimedeanClass.subgroup` of `UpperSet.Ioi c`. -/
@[to_additive
/--An open ball defined by `FiniteArchimedeanClass.addSubgroup` of `UpperSet.Ioi c`. -/]
/-
**FiniteMulArchimedeanClass.ballSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiniteMulA
rchimedeanClass`。
形式化陈述：ballSubgroup (c : FiniteMulArchimedeanClass M)
参数：c : FiniteMulArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev ballSubgroup (c : FiniteMulArchimedeanClass M) := subgroup (UpperSet.Ioi c)

/-- A closed ball defined by `FiniteMulArchimedeanClass.subgroup` of `UpperSet.Ici c`. -/
@[to_additive
/-- A closed ball defined by `FiniteArchimedeanClass.addSubgroup` of `UpperSet.Ici c`. -/]
/-
**FiniteMulArchimedeanClass.closedBallSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fini
teMulArchimedeanClass`。
形式化陈述：closedBallSubgroup (c : FiniteMulArchimedeanClass M)
参数：c : FiniteMulArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev closedBallSubgroup (c : FiniteMulArchimedeanClass M) :=
  subgroup (UpperSet.Ici c)

@[to_additive]
/-
**FiniteMulArchimedeanClass.mem_ballSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fini
teMulArchimedeanClass`。
形式化陈述：mem_ballSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} : a in ball
Subgroup c ↔ forall h : a != 1, c < mk a h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ballSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a ∈ ballSubgroup c ↔ ∀ h : a ≠ 1, c < mk a h := by
  simp

@[to_additive]
/-
**FiniteMulArchimedeanClass.mem_closedBallSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间
 `FiniteMulArchimedeanClass`。
形式化陈述：mem_closedBallSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} : a i
n closedBallSubgroup c ↔ forall h : a != 1, c <= mk a h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closedBallSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ ∀ h : a ≠ 1, c ≤ mk a h := by
  simp

@[to_additive]
/-
**FiniteMulArchimedeanClass.ballSubgroup_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `F
initeMulArchimedeanClass`。
形式化陈述：ballSubgroup_strictAnti : StrictAnti (ballSubgroup (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMulArchimedeanClass.subgroup_strictAnti`：∀ {M : Type u_1} [inst : 
CommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedMonoid M],   StrictAnti
 FiniteMulArchimedeanClass.subgroup
· 使用定理 `UpperSet.Ioi_strictMono`：Ioi_strictMono : StrictMono (Ioi (α
-/
theorem ballSubgroup_strictAnti : StrictAnti (ballSubgroup (M := M)) :=
  fun _ _ h ↦ subgroup_strictAnti <| UpperSet.Ioi_strictMono _ h

end FiniteMulArchimedeanClass

