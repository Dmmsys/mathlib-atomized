/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Parity -- Algebra.Group.Even can't prove `IsSquare 0` by simp
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Sums of squares

We introduce a predicate for sums of squares in a ring.

## Main declarations

- `IsSumSq : R → Prop`: for a type `R` with addition, multiplication and a zero,
  an inductive predicate defining the property of being a sum of squares in `R`.
  `0 : R` is a sum of squares and if `S` is a sum of squares, then, for all `a : R`,
  `a * a + s` is a sum of squares.
- `AddMonoid.sumSq R` and `Subsemiring.sumSq R`: respectively
  the submonoid or subsemiring of sums of squares in an additive monoid or semiring `R`
  with multiplication.
-/

@[expose] public section

variable {R : Type*}

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
@[mk_iff]
/--
Inductive type `IsSumSq` / 归纳类型 `IsSumSq`

English:
inductive IsSumSq
  parameters: [Mul R] [Add R] [Zero R]
  constructors (2):
    - zero: IsSumSq 0
    - sq_add: (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

中文:
归纳类型 IsSumSq
  参数: [Mul R] [Add R] [Zero R]
  构造子 (2 个):
    - zero: IsSumSq 0
    - sq_add: (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)
-/
inductive IsSumSq [Mul R] [Add R] [Zero R] : R -> Prop
  | zero : IsSumSq 0
  | sq_add (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `IsSumSq.rec'` / 定理 `IsSumSq.rec'`

English:
theorem IsSumSq.rec'
  statement: [Mul R] [Add R] [Zero R]
  proof: match h with
  | .zero => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

中文:
定理 IsSumSq.rec'
  结论: [Mul R] [Add R] [Zero R]
  证明: match h with
  | .zero => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

Depends on / 依赖: mul_self, sq_add
-/
theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (s : R) -> (h : IsSumSq s) -> Prop}
    (zero : motive 0 zero)
    (sq_add : forall {x s}, (hx : IsSquare x) -> (hs : IsSumSq s) -> motive s hs ->
      motive (x + s) (by rcases hx with ⟨_, rfl⟩; exact sq_add _ hs))
    {s : R} (h : IsSumSq s) : motive s h :=
  match h with
  | .zero => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

/--
In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
/--
theorem `IsSumSq.add` / 定理 `IsSumSq.add`

English:
theorem IsSumSq.add
  statement: [AddMonoid R] [Mul R] {s₁ s₂ : R}
  proof: by
  induction h₁ <;> simp_all [add_assoc, sq_add]

中文:
定理 IsSumSq.add
  结论: [AddMonoid R] [Mul R] {s₁ s₂ : R}
  证明: by
  induction h₁ <;> simp_all [add_assoc, sq_add]

Depends on / 依赖: add_assoc, sq_add
-/
theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [add_assoc, sq_add]

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {s : T}

set_option linter.style.whitespace false in -- manual alignment is not recognised
variable (T) in
/--
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R` is the submonoid of sums of
squares in `R`.
-/
@[simps]
/--
Definition of `sumSq` / `sumSq` 的定义

English:
definition sumSq
  signature: : AddSubmonoid T where
  body: {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem' := .add

中文:
定义 sumSq
  签名: : AddSubmonoid T where
  定义体: {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem' := .add

Depends on / 依赖: IsSumSq
-/
def sumSq : AddSubmonoid T where
  carrier := {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem' := .add

attribute [norm_cast] coe_sumSq

/--
theorem `mem_sumSq` / 定理 `mem_sumSq`

English:
theorem mem_sumSq
  statement: s in sumSq T ↔ IsSumSq s
  proof: Iff.rfl

中文:
定理 mem_sumSq
  结论: s in sumSq T ↔ IsSumSq s
  证明: Iff.rfl
-/
@[simp] theorem mem_sumSq : s in sumSq T ↔ IsSumSq s := Iff.rfl

end AddSubmonoid

/--
theorem `IsSumSq.mul_self` / 定理 `IsSumSq.mul_self`

English:
theorem IsSumSq.mul_self
  given: [AddZeroClass R] [Mul R] (a : R)
  statement: IsSumSq (a * a)
  proof: by
  simpa using sq_add a zero

中文:
定理 IsSumSq.mul_self
  条件: [AddZeroClass R] [Mul R] (a : R)
  结论: IsSumSq (a * a)
  证明: by
  simpa using sq_add a zero
-/
@[simp] theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  simpa using sq_add a zero

/--
In an additive unital magma with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even).
-/
@[aesop unsafe 80% apply]
/--
theorem `IsSquare.isSumSq` / 定理 `IsSquare.isSumSq`

English:
theorem IsSquare.isSumSq
  given: [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x)
  statement: IsSumSq x
  proof: by aesop

中文:
定理 IsSquare.isSumSq
  条件: [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x)
  结论: IsSumSq x
  证明: by aesop
-/
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by aesop

attribute [simp, aesop safe] IsSumSq.zero

@[simp, aesop safe]
/--
theorem `IsSumSq.one` / 定理 `IsSumSq.one`

English:
theorem IsSumSq.one
  given: [AddZeroClass R] [MulOneClass R]
  statement: IsSumSq (1 : R)
  proof: by aesop

中文:
定理 IsSumSq.one
  条件: [AddZeroClass R] [MulOneClass R]
  结论: IsSumSq (1 : R)
  证明: by aesop
-/
theorem IsSumSq.one [AddZeroClass R] [MulOneClass R] : IsSumSq (1 : R) := by aesop

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
/--
theorem `AddSubmonoid.closure_isSquare` / 定理 `AddSubmonoid.closure_isSquare`

English:
theorem AddSubmonoid.closure_isSquare
  given: [AddMonoid R] [Mul R]
  proof: by
  refine closure_eq_of_le (fun x hx => IsSquare.isSumSq hx) (fun x hx => ?_)
  induction hx <;> aesop

中文:
定理 AddSubmonoid.closure_isSquare
  条件: [AddMonoid R] [Mul R]
  证明: by
  refine closure_eq_of_le (fun x hx => IsSquare.isSumSq hx) (fun x hx => ?_)
  induction hx <;> aesop

Depends on / 依赖: IsSquare, IsSquare.isSumSq, closure_eq_of_le, isSumSq
-/
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSq R := by
  refine closure_eq_of_le (fun x hx => IsSquare.isSumSq hx) (fun x hx => ?_)
  induction hx <;> aesop

/--
In an additive commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares.
-/
@[aesop unsafe 90% apply]
/--
theorem `IsSumSq.sum` / 定理 `IsSumSq.sum`

English:
theorem IsSumSq.sum
  statement: [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι -> R}
  proof: by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

中文:
定理 IsSumSq.sum
  结论: [AddCommMonoid R] [Mul R] {ι : 类型} {I : Finset ι} {s : ι -> R}
  证明: by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

Depends on / 依赖: AddSubmonoid, AddSubmonoid.sumSq, sum_mem
-/
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι -> R}
    (hs : forall i in I, IsSumSq <| s i) : IsSumSq (∑ i in I, s i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

/--
theorem `IsSumSq.sum_isSquare` / 定理 `IsSumSq.sum_isSquare`

English:
theorem IsSumSq.sum_isSquare
  statement: [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι -> R}
  proof: by aesop

中文:
定理 IsSumSq.sum_isSquare
  结论: [AddCommMonoid R] [Mul R] {ι : 类型} (I : Finset ι) {x : ι -> R}
  证明: by aesop
-/
theorem IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι -> R}
    (hx : forall i in I, IsSquare <| x i) : IsSumSq (∑ i in I, x i) := by aesop

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, a i * a i` is a sum of squares.
-/
@[simp↓]
/--
theorem `IsSumSq.sum_mul_self` / 定理 `IsSumSq.sum_mul_self`

English:
theorem IsSumSq.sum_mul_self
  given: [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι -> R)
  proof: by aesop

@[simp↓]

中文:
定理 IsSumSq.sum_mul_self
  条件: [AddCommMonoid R] [Mul R] {ι : 类型} (I : Finset ι) (a : ι -> R)
  证明: by aesop

@[simp↓]
-/
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι -> R) :
    IsSumSq (∑ i in I, a i * a i) := by aesop

@[simp↓]
/--
theorem `IsSumSq.sum_sq` / 定理 `IsSumSq.sum_sq`

English:
theorem IsSumSq.sum_sq
  given: [CommSemiring R] {ι : Type*} (I : Finset ι) (a : ι -> R)
  proof: by aesop

中文:
定理 IsSumSq.sum_sq
  条件: [CommSemiring R] {ι : 类型} (I : Finset ι) (a : ι -> R)
  证明: by aesop
-/
theorem IsSumSq.sum_sq [CommSemiring R] {ι : Type*} (I : Finset ι) (a : ι -> R) :
    IsSumSq (∑ i in I, a i ^ 2) := by aesop

namespace NonUnitalSubsemiring
variable {T : Type*} [NonUnitalCommSemiring T]

variable (T) in
/--
Definition of `sumSq` / `sumSq` 的定义

English:
definition sumSq
  signature: : NonUnitalSubsemiring T
  body: (Subsemigroup.square T).nonUnitalSubsemiringClosure

中文:
定义 sumSq
  签名: : NonUnitalSubsemiring T
  定义体: (Subsemigroup.square T).nonUnitalSubsemiringClosure

Depends on / 依赖: Subsemigroup, Subsemigroup.square, nonUnitalSubsemiringClosure, square
-/
def sumSq : NonUnitalSubsemiring T := (Subsemigroup.square T).nonUnitalSubsemiringClosure

/--
theorem `sumSq_toAddSubmonoid` / 定理 `sumSq_toAddSubmonoid`

English:
theorem sumSq_toAddSubmonoid
  statement: (sumSq T).toAddSubmonoid = .sumSq T
  proof: by
  simp [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]

@[simp]

中文:
定理 sumSq_toAddSubmonoid
  结论: (sumSq T).toAddSubmonoid = .sumSq T
  证明: by
  simp [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]

@[simp]

Depends on / 依赖: asOver, f.asOver, pullback
-/
@[simp] theorem sumSq_toAddSubmonoid : (sumSq T).toAddSubmonoid = .sumSq T := by
  simp [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]

@[simp]
/--
theorem `mem_sumSq` / 定理 `mem_sumSq`

English:
theorem mem_sumSq
  given: {s : T}
  statement: s in sumSq T ↔ IsSumSq s
  proof: by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]

中文:
定理 mem_sumSq
  条件: {s : T}
  结论: s in sumSq T ↔ IsSumSq s
  证明: by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.mem_toAddSubmonoid, mem_toAddSubmonoid
-/
theorem mem_sumSq {s : T} : s in sumSq T ↔ IsSumSq s := by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]

/--
theorem `coe_sumSq` / 定理 `coe_sumSq`

English:
theorem coe_sumSq
  statement: sumSq T = {s : T | IsSumSq s}
  proof: by ext; simp

中文:
定理 coe_sumSq
  结论: sumSq T = {s : T | IsSumSq s}
  证明: by ext; simp
-/
@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

/--
theorem `closure_isSquare` / 定理 `closure_isSquare`

English:
theorem closure_isSquare
  statement: closure {x : T | IsSquare x} = sumSq T
  proof: by
  simp [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

中文:
定理 closure_isSquare
  结论: closure {x : T | IsSquare x} = sumSq T
  证明: by
  simp [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

Depends on / 依赖: asOver, f.asOver, pullback
-/
@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  simp [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

end NonUnitalSubsemiring

@[simp, aesop safe]
/--
theorem `IsSumSq.natCast` / 定理 `IsSumSq.natCast`

English:
theorem IsSumSq.natCast
  given: {R : Type*} [NonAssocSemiring R] (n : Nat)
  statement: IsSumSq (n : R)
  proof: by
  induction n <;> aesop

@[simp]

中文:
定理 IsSumSq.natCast
  条件: {R : 类型} [NonAssocSemiring R] (n : 自然数)
  结论: IsSumSq (n : R)
  证明: by
  induction n <;> aesop

@[simp]
-/
theorem IsSumSq.natCast {R : Type*} [NonAssocSemiring R] (n : Nat) : IsSumSq (n : R) := by
  induction n <;> aesop

@[simp]
/--
theorem `Nat.isSumSq` / 定理 `Nat.isSumSq`

English:
theorem Nat.isSumSq
  given: (n : Nat)
  statement: IsSumSq n
  proof: IsSumSq.natCast n

中文:
定理 Nat.isSumSq
  条件: (n : 自然数)
  结论: IsSumSq n
  证明: IsSumSq.natCast n

Depends on / 依赖: IsSumSq, IsSumSq.natCast, natCast
-/
theorem Nat.isSumSq (n : Nat) : IsSumSq n := IsSumSq.natCast n

/--
In a commutative (possibly non-unital) semiring,
if `s₁` and `s₂` are sums of squares, then `s₁ * s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
/--
theorem `IsSumSq.mul` / 定理 `IsSumSq.mul`

English:
theorem IsSumSq.mul
  statement: [NonUnitalCommSemiring R] {s₁ s₂ : R}
  proof: by
  simpa using mul_mem (by simpa : _ in NonUnitalSubsemiring.sumSq R) (by simpa)

中文:
定理 IsSumSq.mul
  结论: [NonUnitalCommSemiring R] {s₁ s₂ : R}
  证明: by
  simpa using mul_mem (by simpa : _ in NonUnitalSubsemiring.sumSq R) (by simpa)

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.sumSq, asOverProp, f.asOverProp, mul_mem, pullback
-/
theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ in NonUnitalSubsemiring.sumSq R) (by simpa)

/--
theorem `Submonoid.square_subsemiringClosure` / 定理 `Submonoid.square_subsemiringClosure`

English:
theorem Submonoid.square_subsemiringClosure
  given: {T : Type*} [CommSemiring T]
  proof: by
  simp [Submonoid.subsemiringClosure_eq_closure]

中文:
定理 Submonoid.square_subsemiringClosure
  条件: {T : 类型} [CommSemiring T]
  证明: by
  simp [Submonoid.subsemiringClosure_eq_closure]
-/
private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]

namespace Subsemiring
variable {T : Type*} [CommSemiring T]

variable (T) in
/--
Definition of `sumSq` / `sumSq` 的定义

English:
definition sumSq
  signature: : Subsemiring T where
  body: NonUnitalSubsemiring.sumSq T
  one_mem' := by simp

中文:
定义 sumSq
  签名: : Subsemiring T where
  定义体: NonUnitalSubsemiring.sumSq T
  one_mem' := by simp

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.sumSq
-/
def sumSq : Subsemiring T where
  __ := NonUnitalSubsemiring.sumSq T
  one_mem' := by simp

/--
theorem `sumSq_toNonUnitalSubsemiring` / 定理 `sumSq_toNonUnitalSubsemiring`

English:
theorem sumSq_toNonUnitalSubsemiring
  proof: rfl

@[simp]

中文:
定理 sumSq_toNonUnitalSubsemiring
  证明: rfl

@[simp]

Depends on / 依赖: asOverProp, pullback
-/
@[simp] theorem sumSq_toNonUnitalSubsemiring :
    (sumSq T).toNonUnitalSubsemiring = .sumSq T := rfl

@[simp]
/--
theorem `mem_sumSq` / 定理 `mem_sumSq`

English:
theorem mem_sumSq
  given: {s : T}
  statement: s in sumSq T ↔ IsSumSq s
  proof: by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]

中文:
定理 mem_sumSq
  条件: {s : T}
  结论: s in sumSq T ↔ IsSumSq s
  证明: by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]

Depends on / 依赖: Subsemiring, Subsemiring.mem_toNonUnitalSubsemiring, mem_toNonUnitalSubsemiring
-/
theorem mem_sumSq {s : T} : s in sumSq T ↔ IsSumSq s := by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]

/--
theorem `coe_sumSq` / 定理 `coe_sumSq`

English:
theorem coe_sumSq
  statement: sumSq T = {s : T | IsSumSq s}
  proof: by ext; simp

中文:
定理 coe_sumSq
  结论: sumSq T = {s : T | IsSumSq s}
  证明: by ext; simp
-/
@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp

/--
theorem `closure_isSquare` / 定理 `closure_isSquare`

English:
theorem closure_isSquare
  statement: closure {x : T | IsSquare x} = sumSq T
  proof: by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]

中文:
定理 closure_isSquare
  结论: closure {x : T | IsSquare x} = sumSq T
  证明: by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]
-/
@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares is a sum of squares. -/
@[aesop unsafe 50% apply]
/--
theorem `IsSumSq.prod` / 定理 `IsSumSq.prod`

English:
theorem IsSumSq.prod
  statement: [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι -> R}
  proof: by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

中文:
定理 IsSumSq.prod
  结论: [CommSemiring R] {ι : 类型} {I : Finset ι} {x : ι -> R}
  证明: by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

Depends on / 依赖: Subsemiring, Subsemiring.sumSq, prod_mem
-/
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι -> R}
    (hx : forall i in I, IsSumSq <| x i) : IsSumSq (∏ i in I, x i) := by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `IsSumSq.nonneg` / 定理 `IsSumSq.nonneg`

English:
theorem IsSumSq.nonneg
  statement: {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  induction hs using IsSumSq.rec' with
  | zero => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h

中文:
定理 IsSumSq.nonneg
  结论: {R : 类型} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  证明: by
  induction hs using IsSumSq.rec' with
  | zero => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h

Depends on / 依赖: IsSquare, IsSquare.nonneg, IsSumSq, IsSumSq.rec, add_nonneg, nonneg, sq_add
-/
theorem IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 <= s := by
  induction hs using IsSumSq.rec' with
  | zero => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h
