/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `List ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : Holor α ds₁` and `x₂ : Holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/

@[expose] public section


universe u

open List

/--
Definition of `HolorIndex` / `HolorIndex` 的定义

English:
definition HolorIndex
  signature: (ds : List Nat)
  body: { is : List Nat // Forall₂ (· < ·) is ds }

中文:
定义 HolorIndex
  签名: (ds : List 自然数)
  定义体: { is : List Nat // Forall₂ (· < ·) is ds }
-/
def HolorIndex (ds : List Nat) : Type :=
  { is : List Nat // Forall₂ (· < ·) is ds }

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List Nat}

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: : forall {ds₁ : List Nat}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₁

中文:
定义 take
  签名: : 对任意 {ds₁ : List 自然数}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₁
-/
def take : forall {ds₁ : List Nat}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₁
  | ds, is => ⟨List.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: : forall {ds₁ : List Nat}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₂

中文:
定义 drop
  签名: : 对任意 {ds₁ : List 自然数}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₂
-/
def drop : forall {ds₁ : List Nat}, HolorIndex (ds₁ ++ ds₂) -> HolorIndex ds₂
  | ds, is => ⟨List.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩

/--
theorem `cast_type` / 定理 `cast_type`

English:
theorem cast_type
  given: (is : List Nat) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁)
  proof: by subst eq; rfl

中文:
定理 cast_type
  条件: (is : List 自然数) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁)
  证明: by subst eq; rfl

Depends on / 依赖: Set.ext
-/
theorem cast_type (is : List Nat) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is := by subst eq; rfl

/--
Definition of `assocRight` / `assocRight` 的定义

English:
definition assocRight
  signature: : HolorIndex (ds₁ ++ ds₂ ++ ds₃) -> HolorIndex (ds₁ ++ (ds₂ ++ ds₃))
  body: cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

中文:
定义 assocRight
  签名: : HolorIndex (ds₁ ++ ds₂ ++ ds₃) -> HolorIndex (ds₁ ++ (ds₂ ++ ds₃))
  定义体: cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

Depends on / 依赖: HolorIndex, Subset, Subset.antisymm, antisymm, append_assoc, congr_arg, e.subset, e.symm.subset, subset
-/
def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) -> HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

/--
Definition of `assocLeft` / `assocLeft` 的定义

English:
definition assocLeft
  signature: : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) -> HolorIndex (ds₁ ++ ds₂ ++ ds₃)
  body: cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)

中文:
定义 assocLeft
  签名: : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) -> HolorIndex (ds₁ ++ ds₂ ++ ds₃)
  定义体: cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)

Depends on / 依赖: HolorIndex, append_assoc, congr_arg
-/
def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) -> HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)

/--
theorem `take_take` / 定理 `take_take`

English:
theorem take_take
  statement: forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take

中文:
定理 take_take
  结论: 对任意 t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
-/
theorem take_take : forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
Subtype.ext by
      simp [assocRight, take, cast_type, List.take_take, Nat.le_add_right]

/--
theorem `drop_take` / 定理 `drop_take`

English:
theorem drop_take
  statement: forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop

中文:
定理 drop_take
  结论: 对任意 t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
-/
theorem drop_take : forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, take, drop, cast_type, List.drop_take])

/--
theorem `drop_drop` / 定理 `drop_drop`

English:
theorem drop_drop
  statement: forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop

中文:
定理 drop_drop
  结论: 对任意 t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
-/
theorem drop_drop : forall t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, drop, cast_type, List.drop_drop])

end HolorIndex

/--
Definition of `Holor` / `Holor` 的定义

English:
definition Holor
  signature: (α : Type u) (ds : List Nat)
  body: HolorIndex ds -> α

中文:
定义 Holor
  签名: (α : 类型u) (ds : List 自然数)
  定义体: HolorIndex ds -> α

Depends on / 依赖: HolorIndex
-/
def Holor (α : Type u) (ds : List Nat) :=
  HolorIndex ds -> α

namespace Holor

variable {α : Type} {d : Nat} {ds : List Nat} {ds₁ : List Nat} {ds₂ : List Nat} {ds₃ : List Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Holor α ds)
  body: ⟨fun _ => default⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (Holor α ds)
  定义体: ⟨fun _ => default⟩
-/
instance [Inhabited α] : Inhabited (Holor α ds) :=
  ⟨fun _ => default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] : Zero (Holor α ds)
  body: ⟨fun _ => 0⟩

中文:
实例 [Zero
  签名: α] : Zero (Holor α ds)
  定义体: ⟨fun _ => 0⟩
-/
instance [Zero α] : Zero (Holor α ds) :=
  ⟨fun _ => 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] : Add (Holor α ds)
  body: ⟨fun x y t => x t + y t⟩

中文:
实例 [Add
  签名: α] : Add (Holor α ds)
  定义体: ⟨fun x y t => x t + y t⟩
-/
instance [Add α] : Add (Holor α ds) :=
  ⟨fun x y t => x t + y t⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: α] : Neg (Holor α ds)
  body: ⟨fun a t => -a t⟩

中文:
实例 [Neg
  签名: α] : Neg (Holor α ds)
  定义体: ⟨fun a t => -a t⟩
-/
instance [Neg α] : Neg (Holor α ds) :=
  ⟨fun a t => -a t⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddSemigroup
  signature: α] : AddSemigroup (Holor α ds)
  body: inferInstanceAs AddSemigroup (HolorIndex ds -> α)

中文:
实例 [AddSemigroup
  签名: α] : AddSemigroup (Holor α ds)
  定义体: inferInstanceAs AddSemigroup (HolorIndex ds -> α)

Depends on / 依赖: AddSemigroup, HolorIndex
-/
instance [AddSemigroup α] : AddSemigroup (Holor α ds) :=
inferInstanceAs AddSemigroup (HolorIndex ds -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommSemigroup
  signature: α] : AddCommSemigroup (Holor α ds)
  body: inferInstanceAs AddCommSemigroup (HolorIndex ds -> α)

中文:
实例 [AddCommSemigroup
  签名: α] : AddCommSemigroup (Holor α ds)
  定义体: inferInstanceAs AddCommSemigroup (HolorIndex ds -> α)

Depends on / 依赖: AddCommSemigroup, HolorIndex
-/
instance [AddCommSemigroup α] : AddCommSemigroup (Holor α ds) :=
inferInstanceAs AddCommSemigroup (HolorIndex ds -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] : AddMonoid (Holor α ds)
  body: inferInstanceAs AddMonoid (HolorIndex ds -> α)

中文:
实例 [AddMonoid
  签名: α] : AddMonoid (Holor α ds)
  定义体: inferInstanceAs AddMonoid (HolorIndex ds -> α)

Depends on / 依赖: AddMonoid, HolorIndex
-/
instance [AddMonoid α] : AddMonoid (Holor α ds) :=
inferInstanceAs AddMonoid (HolorIndex ds -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: α] : AddCommMonoid (Holor α ds)
  body: inferInstanceAs AddCommMonoid (HolorIndex ds -> α)

中文:
实例 [AddCommMonoid
  签名: α] : AddCommMonoid (Holor α ds)
  定义体: inferInstanceAs AddCommMonoid (HolorIndex ds -> α)

Depends on / 依赖: AddCommMonoid, HolorIndex
-/
instance [AddCommMonoid α] : AddCommMonoid (Holor α ds) :=
inferInstanceAs AddCommMonoid (HolorIndex ds -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: α] : AddGroup (Holor α ds)
  body: inferInstanceAs AddGroup (HolorIndex ds -> α)

中文:
实例 [AddGroup
  签名: α] : AddGroup (Holor α ds)
  定义体: inferInstanceAs AddGroup (HolorIndex ds -> α)

Depends on / 依赖: AddGroup, HolorIndex
-/
instance [AddGroup α] : AddGroup (Holor α ds) :=
inferInstanceAs AddGroup (HolorIndex ds -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: α] : AddCommGroup (Holor α ds)
  body: inferInstanceAs AddCommGroup (HolorIndex ds -> α)

中文:
实例 [AddCommGroup
  签名: α] : AddCommGroup (Holor α ds)
  定义体: inferInstanceAs AddCommGroup (HolorIndex ds -> α)

Depends on / 依赖: AddCommGroup, HolorIndex
-/
instance [AddCommGroup α] : AddCommGroup (Holor α ds) :=
inferInstanceAs AddCommGroup (HolorIndex ds -> α)

-- scalar product
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : SMul α (Holor α ds)
  body: ⟨fun a x => fun t => a * x t⟩

中文:
实例 [Mul
  签名: α] : SMul α (Holor α ds)
  定义体: ⟨fun a x => fun t => a * x t⟩
-/
instance [Mul α] : SMul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : Module α (Holor α ds)
  body: inferInstanceAs Module α (HolorIndex ds -> α)

中文:
实例 [Semiring
  签名: α] : Module α (Holor α ds)
  定义体: inferInstanceAs Module α (HolorIndex ds -> α)

Depends on / 依赖: HolorIndex, Module
-/
instance [Semiring α] : Module α (Holor α ds) :=
inferInstanceAs Module α (HolorIndex ds -> α)

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: [Mul α] (x : Holor α ds₁) (y : Holor α ds₂)
  body: fun t =>
  x t.take * y t.drop

local infixl:70 " otimes " => mul

中文:
定义 mul
  签名: [Mul α] (x : Holor α ds₁) (y : Holor α ds₂)
  定义体: fun t =>
  x t.take * y t.drop

local infixl:70 " otimes " => mul
-/
def mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
  x t.take * y t.drop

local infixl:70 " otimes " => mul

/--
theorem `cast_type` / 定理 `cast_type`

English:
theorem cast_type
  given: (eq : ds₁ = ds₂) (a : Holor α ds₁)
  proof: by
  subst eq; rfl

中文:
定理 cast_type
  条件: (eq : ds₁ = ds₂) (a : Holor α ds₁)
  证明: by
  subst eq; rfl
-/
theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) eq) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t) := by
  subst eq; rfl

/--
Definition of `assocRight` / `assocRight` 的定义

English:
definition assocRight
  signature: : Holor α (ds₁ ++ ds₂ ++ ds₃) -> Holor α (ds₁ ++ (ds₂ ++ ds₃))
  body: cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

中文:
定义 assocRight
  签名: : Holor α (ds₁ ++ ds₂ ++ ds₃) -> Holor α (ds₁ ++ (ds₂ ++ ds₃))
  定义体: cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

Depends on / 依赖: append_assoc, congr_arg
-/
def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) -> Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

/--
Definition of `assocLeft` / `assocLeft` 的定义

English:
definition assocLeft
  signature: : Holor α (ds₁ ++ (ds₂ ++ ds₃)) -> Holor α (ds₁ ++ ds₂ ++ ds₃)
  body: cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

中文:
定义 assocLeft
  签名: : Holor α (ds₁ ++ (ds₂ ++ ds₃)) -> Holor α (ds₁ ++ ds₂ ++ ds₃)
  定义体: cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

Depends on / 依赖: Or.inl, append_assoc, congr_arg, hs.imp
-/
def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) -> Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_assoc0` / 定理 `mul_assoc0`

English:
theorem mul_assoc0
  given: [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃)
  proof: funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc]; rw [← HolorIndex.take_take]; rw [← HolorIndex.drop_take]; rw [← HolorIndex.drop_drop]; rw [cast_type]
    · rfl
    rw [append_assoc]

中文:
定理 mul_assoc0
  条件: [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃)
  证明: funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc]; rw [← HolorIndex.take_take]; rw [← HolorIndex.drop_take]; rw [← HolorIndex.drop_drop]; rw [cast_type]
    · rfl
    rw [append_assoc]

Depends on / 依赖: HolorIndex, HolorIndex.drop_drop, HolorIndex.drop_take, HolorIndex.take_take, Or.inr, append_assoc, assocLeft, cast_type, drop_drop, drop_take, ht.imp, mul_assoc, take_take
-/
theorem mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    x otimes y otimes z = (x otimes (y otimes z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc]; rw [← HolorIndex.take_take]; rw [← HolorIndex.drop_take]; rw [← HolorIndex.drop_drop]; rw [cast_type]
    · rfl
    rw [append_assoc]

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃)
  proof: by simp [cast_heq, mul_assoc0, assocLeft]

中文:
定理 mul_assoc
  条件: [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃)
  证明: by simp [cast_heq, mul_assoc0, assocLeft]

Depends on / 依赖: assocLeft, cast_heq, mul_assoc0
-/
theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    mul (mul x y) z ≍ mul x (mul y z) := by simp [cast_heq, mul_assoc0, assocLeft]

/--
theorem `mul_left_distrib` / 定理 `mul_left_distrib`

English:
theorem mul_left_distrib
  given: [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂)
  proof: funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)

中文:
定理 mul_left_distrib
  条件: [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂)
  证明: funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)

Depends on / 依赖: left_distrib, t.drop, t.take
-/
theorem mul_left_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂) :
    x otimes (y + z) = x otimes y + x otimes z := funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)

/--
theorem `mul_right_distrib` / 定理 `mul_right_distrib`

English:
theorem mul_right_distrib
  given: [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂)
  proof: funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor α ds₂) : (0 : Holor α ds₁) otimes x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor α ds₁

中文:
定理 mul_right_distrib
  条件: [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂)
  证明: funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor α ds₂) : (0 : Holor α ds₁) otimes x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor α ds₁

Depends on / 依赖: add_mul, t.drop, t.take
-/
theorem mul_right_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂) :
    (x + y) otimes z = x otimes z + y otimes z := funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor α ds₂) : (0 : Holor α ds₁) otimes x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor α ds₁) : x otimes (0 : Holor α ds₂) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_scalar_mul` / 定理 `mul_scalar_mul`

English:
theorem mul_scalar_mul
  given: [Mul α] (x : Holor α []) (y : Holor α ds)
  proof: by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

中文:
定理 mul_scalar_mul
  条件: [Mul α] (x : Holor α []) (y : Holor α ds)
  证明: by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

Depends on / 依赖: HSMul.hSMul, HolorIndex, HolorIndex.drop, HolorIndex.take, SMul.smul, unfoldPartialApp
-/
theorem mul_scalar_mul [Mul α] (x : Holor α []) (y : Holor α ds) :
    x otimes y = x ⟨[], Forall₂.nil⟩ • y := by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

-- holor slices
/--
Definition of `slice` / `slice` 的定义

English:
definition slice
  signature: (x : Holor α (d :: ds)) (i : Nat) (h : i < d)
  body: fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

中文:
定义 slice
  签名: (x : Holor α (d :: ds)) (i : 自然数) (h : i < d)
  定义体: fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

Depends on / 依赖: HolorIndex
-/
def slice (x : Holor α (d :: ds)) (i : Nat) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

/--
Definition of `unitVec` / `unitVec` 的定义

English:
definition unitVec
  signature: [Monoid α] [AddMonoid α] (d : Nat) (j : Nat)
  body: fun ti =>
  if ti.1 = [j] then 1 else 0

中文:
定义 unitVec
  签名: [Monoid α] [AddMonoid α] (d : 自然数) (j : 自然数)
  定义体: fun ti =>
  if ti.1 = [j] then 1 else 0
-/
def unitVec [Monoid α] [AddMonoid α] (d : Nat) (j : Nat) : Holor α [d] := fun ti =>
  if ti.1 = [j] then 1 else 0

/--
theorem `holor_index_cons_decomp` / 定理 `holor_index_cons_decomp`

English:
theorem holor_index_cons_decomp
  given: (p : HolorIndex (d :: ds) -> Prop)

中文:
定理 holor_index_cons_decomp
  条件: (p : HolorIndex (d :: ds) -> 命题)
-/
theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) -> Prop) :
    forall t : HolorIndex (d :: ds),
      (forall i is, forall h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) -> p t
  | ⟨[], hforall₂⟩, _ => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, _⟩, hp => hp i is rfl

/--
theorem `slice_eq` / 定理 `slice_eq`

English:
theorem slice_eq
  given: (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y)
  statement: x = y
  proof: funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_c

中文:
定理 slice_eq
  条件: (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y)
  结论: x = y
  证明: funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_c

Depends on / 依赖: HolorIndex, Subtype, Subtype.ext, congr_arg, hiisdds, holor_index_cons_decomp, nonempty_subtype
-/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg x (Subtype.ext rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
        _ = y ⟨i :: is, _⟩ := congr_arg y (Subtype.ext rfl)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `slice_unitVec_mul` / 定理 `slice_unitVec_mul`

English:
theorem slice_unitVec_mul
  given: [Semiring α] {i : Nat} {j : Nat} (hid : i < d) (x : Holor α ds)
  proof: funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl

中文:
定理 slice_unitVec_mul
  条件: [Semiring α] {i : 自然数} {j : 自然数} (hid : i < d) (x : Holor α ds)
  证明: funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl

Depends on / 依赖: HolorIndex, HolorIndex.drop, HolorIndex.take, unitVec
-/
theorem slice_unitVec_mul [Semiring α] {i : Nat} {j : Nat} (hid : i < d) (x : Holor α ds) :
    slice (unitVec d j otimes x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl

/--
theorem `slice_add` / 定理 `slice_add`

English:
theorem slice_add
  given: [Add α] (i : Nat) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds))
  proof: funext fun t => by simp [slice, (· + ·), Add.add]

中文:
定理 slice_add
  条件: [Add α] (i : 自然数) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds))
  证明: funext fun t => by simp [slice, (· + ·), Add.add]

Depends on / 依赖: Add.add
-/
theorem slice_add [Add α] (i : Nat) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·), Add.add]

/--
theorem `slice_zero` / 定理 `slice_zero`

English:
theorem slice_zero
  given: [Zero α] (i : Nat) (hid : i < d)
  statement: slice (0 : Holor α (d :: ds)) i hid = 0
  proof: rfl

中文:
定理 slice_zero
  条件: [Zero α] (i : 自然数) (hid : i < d)
  结论: slice (0 : Holor α (d :: ds)) i hid = 0
  证明: rfl
-/
theorem slice_zero [Zero α] (i : Nat) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl

/--
theorem `slice_sum` / 定理 `slice_sum`

English:
theorem slice_sum
  statement: [AddCommMonoid α] {β : Type} (i : Nat) (hid : i < d) (s : Finset β)
  proof: by
  let := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in]; rw [ih]; rw [slice_add]; rw [Finset.sum_insert h_not_in]

中文:
定理 slice_sum
  结论: [AddCommMonoid α] {β : Type} (i : 自然数) (hid : i < d) (s : Finset β)
  证明: by
  let := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in]; rw [ih]; rw [slice_add]; rw [Finset.sum_insert h_not_in]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, Finset.sum_insert, h_not_in, induction_on, slice_add, slice_zero, sum_insert
-/
theorem slice_sum [AddCommMonoid α] {β : Type} (i : Nat) (hid : i < d) (s : Finset β)
    (f : β -> Holor α (d :: ds)) : (∑ x in s, slice (f x) i hid) = slice (∑ x in s, f x) i hid := by
  let := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in]; rw [ih]; rw [slice_add]; rw [Finset.sum_insert h_not_in]

set_option backward.isDefEq.respectTransparency false in
/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
/--
theorem `sum_unitVec_mul_slice` / 定理 `sum_unitVec_mul_slice`

English:
theorem sum_unitVec_mul_slice
  given: [Semiring α] (x : Holor α (d :: ds))
  proof: by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [slice_unitVec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
  · intro (b : { x // x in Finset.range d }) (_ : b in (Finset.range d).attach) (hbi : b != ⟨i, _⟩)
    have hbi' : i != b := by 

中文:
定理 sum_unitVec_mul_slice
  条件: [Semiring α] (x : Holor α (d :: ds))
  证明: by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [slice_unitVec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
  · intro (b : { x // x in Finset.range d }) (_ : b in (Finset.range d).attach) (hbi : b != ⟨i, _⟩)
    have hbi' : i != b := by 

Depends on / 依赖: Finset, Finset.attach, Finset.mem_attach, Finset.mem_range, Finset.range, Finset.sum_eq_single, Subtype, Subtype.coe_mk, Subtype.ext_iff, Subtype.mk, absurd, attach, coe_mk, ext_iff, hbi.symm, mem_attach, mem_range, slice_eq, slice_sum, slice_unitVec_mul
-/
theorem sum_unitVec_mul_slice [Semiring α] (x : Holor α (d :: ds)) :
    (∑ i in (Finset.range d).attach,
        unitVec d i otimes slice x i (Nat.succ_le_of_lt (Finset.mem_range.1 i.prop))) =
      x := by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [slice_unitVec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
  · intro (b : { x // x in Finset.range d }) (_ : b in (Finset.range d).attach) (hbi : b != ⟨i, _⟩)
    have hbi' : i != b := by simpa only [Ne, Subtype.ext_iff, Subtype.coe_mk] using hbi.symm
    simp [hbi']
  · intro (hid' : Subtype.mk i _ ∉ Finset.attach (Finset.range d))
    exfalso
    exact absurd (Finset.mem_attach _ _) hid'

-- CP rank
/--
Inductive type `CPRankMax1` / 归纳类型 `CPRankMax1`

English:
inductive CPRankMax1
  parameters: [Mul α]
  constructors (2):
    - nil: (x : Holor α []) : CPRankMax1 x
    - cons: {d : Nat} {ds : List Nat} (x : Holor α [d]) (y : Holor α ds) : CPRankMax1 y -> CPRankMax1 (x otimes y)

中文:
归纳类型 CPRankMax1
  参数: [Mul α]
  构造子 (2 个):
    - nil: (x : Holor α []) : CPRankMax1 x
    - cons: {d : 自然数} {ds : List 自然数} (x : Holor α [d]) (y : Holor α ds) : CPRankMax1 y -> CPRankMax1 (x otimes y)
-/
inductive CPRankMax1 [Mul α] : forall {ds}, Holor α ds -> Prop
  | nil (x : Holor α []) : CPRankMax1 x
  | cons {d : Nat} {ds : List Nat} (x : Holor α [d]) (y : Holor α ds) :
    CPRankMax1 y -> CPRankMax1 (x otimes y)

/--
Inductive type `CPRankMax` / 归纳类型 `CPRankMax`

English:
inductive CPRankMax
  parameters: [Mul α] [AddMonoid α]
  constructors (2):
    - zero: {ds : List Nat} : CPRankMax 0 (0 : Holor α ds)
    - succ: (n : Nat) {ds : List Nat} (x : Holor α ds) (y : Holor α ds) : CPRankMax1 x -> CPRankMax n y -> CPRankMax (n + 1) (x + y)

中文:
归纳类型 CPRankMax
  参数: [Mul α] [AddMonoid α]
  构造子 (2 个):
    - zero: {ds : List 自然数} : CPRankMax 0 (0 : Holor α ds)
    - succ: (n : 自然数) {ds : List 自然数} (x : Holor α ds) (y : Holor α ds) : CPRankMax1 x -> CPRankMax n y -> CPRankMax (n + 1) (x + y)
-/
inductive CPRankMax [Mul α] [AddMonoid α] : Nat -> forall {ds}, Holor α ds -> Prop
  | zero {ds : List Nat} : CPRankMax 0 (0 : Holor α ds)
  | succ (n : Nat) {ds : List Nat} (x : Holor α ds) (y : Holor α ds) :
    CPRankMax1 x -> CPRankMax n y -> CPRankMax (n + 1) (x + y)

/--
theorem `cprankMax_nil` / 定理 `cprankMax_nil`

English:
theorem cprankMax_nil
  given: [Mul α] [AddMonoid α] (x : Holor α nil)
  statement: CPRankMax 1 x
  proof: by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h

中文:
定理 cprankMax_nil
  条件: [Mul α] [AddMonoid α] (x : Holor α nil)
  结论: CPRankMax 1 x
  证明: by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h

Depends on / 依赖: CPRankMax, CPRankMax.succ, CPRankMax.zero, CPRankMax1, CPRankMax1.nil, add_zero, zero_add
-/
theorem cprankMax_nil [Mul α] [AddMonoid α] (x : Holor α nil) : CPRankMax 1 x := by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h

/--
theorem `cprankMax_1` / 定理 `cprankMax_1`

English:
theorem cprankMax_1
  given: [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x)
  proof: by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'

中文:
定理 cprankMax_1
  条件: [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x)
  证明: by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'

Depends on / 依赖: CPRankMax, CPRankMax.succ, CPRankMax.zero, add_zero, zero_add
-/
theorem cprankMax_1 [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x) :
    CPRankMax 1 x := by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'

/--
theorem `cprankMax_add` / 定理 `cprankMax_add`

English:
theorem cprankMax_add
  given: [Mul α] [AddMonoid α]

中文:
定理 cprankMax_add
  条件: [Mul α] [AddMonoid α]
-/
theorem cprankMax_add [Mul α] [AddMonoid α] :
    forall {m : Nat} {n : Nat} {x : Holor α ds} {y : Holor α ds},
      CPRankMax m x -> CPRankMax n y -> CPRankMax (m + n) (x + y)
  | 0, n, x, y, hx, hy => by
    match hx with
    | CPRankMax.zero => simp only [zero_add, hy]
  | m + 1, n, _, y, CPRankMax.succ _ x₁ x₂ hx₁ hx₂, hy => by
    suffices CPRankMax (m + n + 1) (x₁ + (x₂ + y)) by
      simpa only [add_comm, add_assoc, add_left_comm] using this
    apply CPRankMax.succ
    · assumption
    · exact cprankMax_add hx₂ hy

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cprankMax_mul` / 定理 `cprankMax_mul`

English:
theorem cprankMax_mul
  given: [NonUnitalNonAssocSemiring α]

中文:
定理 cprankMax_mul
  条件: [NonUnitalNonAssocSemiring α]
-/
theorem cprankMax_mul [NonUnitalNonAssocSemiring α] :
    forall (n : Nat) (x : Holor α [d]) (y : Holor α ds), CPRankMax n y -> CPRankMax n (x otimes y)
  | 0, x, _, CPRankMax.zero => by simp [mul_zero x, CPRankMax.zero]
  | n + 1, x, _, CPRankMax.succ _ y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    rw [Nat.add_comm]
    apply cprankMax_add
    · exact cprankMax_1 (CPRankMax1.cons _ _ hy₁)
    · exact cprankMax_mul _ x y₂ hy₂

/--
theorem `cprankMax_sum` / 定理 `cprankMax_sum`

English:
theorem cprankMax_sum
  statement: [NonUnitalNonAssocSemiring α] {β} {n : Nat} (s : Finset β)
  proof: letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
  

中文:
定理 cprankMax_sum
  结论: [NonUnitalNonAssocSemiring α] {β} {n : 自然数} (s : Finset β)
  证明: letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
  

Depends on / 依赖: CPRankMax, CPRankMax.zero, Classical, Classical.decEq, Finset, Finset.card, Finset.card_insert_of_notMem, Finset.induction_on, Finset.mem_insert_self, Finset.sum_insert, Nat.add_comm, Nat.one_mul, Nat.right_distrib, add_comm, card_insert_of_notMem, cprankMax_add, h_cprank, h_x_notin_s, induction_on, mem_insert_self
-/
theorem cprankMax_sum [NonUnitalNonAssocSemiring α] {β} {n : Nat} (s : Finset β)
    (f : β -> Holor α ds) : (forall x in s, CPRankMax n (f x)) -> CPRankMax (s.card * n) (∑ x in s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
      have ih' : CPRankMax (Finset.card s * n) (∑ x in s, f x) := by grind
      exact cprankMax_add (h_cprank x (Finset.mem_insert_self x s)) ih')

/--
theorem `cprankMax_upper_bound` / 定理 `cprankMax_upper_bound`

English:
theorem cprankMax_upper_bound
  given: [Semiring α]
  statement: forall {ds}, forall x : Holor α ds, CPRankMax ds.prod x
  proof: fun i => cprankMax_mul _ _ _ (cprankMax_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).prod = Finset.card (Finset.range d) * prod ds := by
      simp [Finset.card_range]
    have :
      CPRankMax (Finset.card (Finset.attach (Finset.range d)) * prod ds)
        (

中文:
定理 cprankMax_upper_bound
  条件: [Semiring α]
  结论: 对任意 {ds}, 对任意 x : Holor α ds, CPRankMax ds.prod x
  证明: fun i => cprankMax_mul _ _ _ (cprankMax_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).prod = Finset.card (Finset.range d) * prod ds := by
      simp [Finset.card_range]
    have :
      CPRankMax (Finset.card (Finset.attach (Finset.range d)) * prod ds)
        (

Depends on / 依赖: CPRankMax, Finset, Finset.attach, Finset.card, Finset.card_range, Finset.range, List.cons, attach, card_range, cprankMax_mul, cprankMax_sum, cprankMax_upper_bound, h_cprankMax_sum, h_dds_prod, h_summands, i.val, mem_range, otimes, unitVec
-/
theorem cprankMax_upper_bound [Semiring α] : forall {ds}, forall x : Holor α ds, CPRankMax ds.prod x
  | [], x => cprankMax_nil x
  | d :: ds, x => by
    have h_summands :
      forall i : { x // x in Finset.range d },
        CPRankMax ds.prod (unitVec d i.1 otimes slice x i.1 (mem_range.1 i.2)) :=
      fun i => cprankMax_mul _ _ _ (cprankMax_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).prod = Finset.card (Finset.range d) * prod ds := by
      simp [Finset.card_range]
    have :
      CPRankMax (Finset.card (Finset.attach (Finset.range d)) * prod ds)
        (∑ i in Finset.attach (Finset.range d),
          unitVec d i.val otimes slice x i.val (mem_range.1 i.2)) :=
      cprankMax_sum (Finset.range d).attach _ fun i _ => h_summands i
    have h_cprankMax_sum :
      CPRankMax (Finset.card (Finset.range d) * prod ds)
        (∑ i in Finset.attach (Finset.range d),
          unitVec d i.val otimes slice x i.val (mem_range.1 i.2)) := by rwa [Finset.card_attach] at this
    rw [← sum_unitVec_mul_slice x]
    rw [h_dds_prod]
    exact h_cprankMax_sum

/--
Definition of `cprank` / `cprank` 的定义

English:
definition cprank
  signature: [Ring α] (x : Holor α ds)
  body: @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩

中文:
定义 cprank
  签名: [Ring α] (x : Holor α ds)
  定义体: @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩

Depends on / 依赖: CPRankMax, Classical, Classical.decPred, Nat.find, cprankMax_upper_bound, decPred, ds.prod
-/
noncomputable def cprank [Ring α] (x : Holor α ds) : Nat :=
  @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩

/--
theorem `cprank_upper_bound` / 定理 `cprank_upper_bound`

English:
theorem cprank_upper_bound
  given: [Ring α]
  statement: forall {ds}, forall x : Holor α ds, cprank x <= ds.prod
  proof: fun {ds} x =>
  letI := Classical.decPred fun n : Nat => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

中文:
定理 cprank_upper_bound
  条件: [Ring α]
  结论: 对任意 {ds}, 对任意 x : Holor α ds, cprank x <= ds.prod
  证明: fun {ds} x =>
  letI := Classical.decPred fun n : Nat => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

Depends on / 依赖: CPRankMax, Classical, Classical.decPred, Nat.find_min, cprankMax_upper_bound, decPred, ds.prod, find_min
-/
theorem cprank_upper_bound [Ring α] : forall {ds}, forall x : Holor α ds, cprank x <= ds.prod :=
  fun {ds} x =>
  letI := Classical.decPred fun n : Nat => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

end Holor
