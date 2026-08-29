/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Formally real rings

A ring `R` is *formally real* if, whenever `∑ i, x i ^ 2 = 0`, in fact `x i = 0` for all `i`.

We define formally real rings in an index-free manner using the inductive predicate
`IsSumNonzeroSq`, which asserts that an element is a finite sum of squares of nonzero elements.
A ring is then formally real if `¬ IsSumNonzeroSq 0`.

## Main declaration

- `IsFormallyReal`: typeclass stating that a ring is formally real.

-/

@[expose] public section

variable {R : Type*}

section IsSumNonzeroSq

/--
The property of being a sum of squares of nonzero elements (S) is defined inductively by:
`a * a : R` is (S) for all nonzero `a`, and
if `s : R` is (S), and `a ≠ 0`, then `a * a + s` is (S).
-/
@[mk_iff]
/--
Inductive type `IsSumNonzeroSq` / 归纳类型 `IsSumNonzeroSq`

English:
inductive IsSumNonzeroSq
  parameters: [Mul R] [Add R] [Zero R]
  constructors (2):
    - sq: {a : R} (ha : a != 0) : IsSumNonzeroSq (a * a)
    - sq_add: {a s : R} (ha : a != 0) (hs : IsSumNonzeroSq s) : IsSumNonzeroSq (a * a + s)

中文:
归纳类型 是SumNonzeroSq
  参数: [乘法 R] [加法 R] [零 R]
  构造子 (2 个):
    - sq: {a : R} (ha : a != 0) : 是SumNonzeroSq (a * a)
    - sq_add: {a s : R} (ha : a != 0) (hs : 是SumNonzeroSq s) : 是SumNonzeroSq (a * a + s)
-/
inductive IsSumNonzeroSq [Mul R] [Add R] [Zero R] : R -> Prop
  | sq {a : R} (ha : a != 0) : IsSumNonzeroSq (a * a)
  | sq_add {a s : R} (ha : a != 0) (hs : IsSumNonzeroSq s) : IsSumNonzeroSq (a * a + s)

attribute [aesop 90%] IsSumNonzeroSq.sq

@[aesop 90%]
/--
theorem `IsSumNonzeroSq.add` / 定理 `IsSumNonzeroSq.add`

English:
theorem IsSumNonzeroSq.add
  statement: [AddMonoid R] [Mul R] {s₁ s₂ : R}
  proof: by
  induction h₁ <;> simp_all [sq_add, add_assoc]

中文:
定理 是SumNonzeroSq.add
  结论: [加法幺半群 R] [乘法 R] {s₁ s₂ : R}
  证明: by
  induction h₁ <;> simp_all [sq_add, add_assoc]

Depends on / 依赖: add_assoc, sq_add
-/
theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [sq_add, add_assoc]

/--
theorem `IsSumNonzeroSq.isSumSq` / 定理 `IsSumNonzeroSq.isSumSq`

English:
theorem IsSumNonzeroSq.isSumSq
  statement: [AddMonoid R] [Mul R] {s : R}
  proof: by
  induction h <;> aesop

中文:
定理 是SumNonzeroSq.isSumSq
  结论: [加法幺半群 R] [乘法 R] {s : R}
  证明: by
  induction h <;> aesop
-/
theorem IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s : R}
    (h : IsSumNonzeroSq s) : IsSumSq s := by
  induction h <;> aesop

/--
theorem `isSumNonzeroSq_iff_isSumSq` / 定理 `isSumNonzeroSq_iff_isSumSq`

English:
theorem isSumNonzeroSq_iff_isSumSq
  given: [NonUnitalNonAssocSemiring R] {s : R} (hs : s != 0)
  proof: IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)


中文:
定理 isSumNonzeroSq_iff_isSumSq
  条件: [非幺非结合半环 R] {s : R} (hs : s != 0)
  证明: IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)


Depends on / 依赖: IsSumNonzeroSq, IsSumNonzeroSq.isSumSq, isSumSq
-/
theorem isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s != 0) :
    IsSumNonzeroSq s ↔ IsSumSq s where
  mp := IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)

alias ⟨_, IsSumSq.isSumNonzeroSq_of_ne_zero⟩ := isSumNonzeroSq_iff_isSumSq

namespace AddSubsemigroup

variable [AddMonoid R] [Mul R] {s : R}

variable (R) in
/-- The subsemigroup of sums of squares of nonzero elements. -/
@[simps]
/--
Definition of `sumNonzeroSq` / `sumNonzeroSq` 的定义

English:
definition sumNonzeroSq
  signature: : AddSubsemigroup R where
  body: {s : R | IsSumNonzeroSq s}
  add_mem' := .add

中文:
定义 sumNonzeroSq
  签名: : 加法子半群 R where
  定义体: {s : R | IsSumNonzeroSq s}
  add_mem' := .add

Depends on / 依赖: IsSumNonzeroSq
-/
def sumNonzeroSq : AddSubsemigroup R where
  carrier := {s : R | IsSumNonzeroSq s}
  add_mem' := .add

attribute [norm_cast] coe_sumNonzeroSq

/--
theorem `mem_sumNonzeroSq` / 定理 `mem_sumNonzeroSq`

English:
theorem mem_sumNonzeroSq
  statement: s in sumNonzeroSq R ↔ IsSumNonzeroSq s
  proof: .rfl

@[simp]

中文:
定理 mem_sumNonzeroSq
  结论: s in sumNonzeroSq R ↔ 是SumNonzeroSq s
  证明: .rfl

@[simp]
-/
@[simp] theorem mem_sumNonzeroSq : s in sumNonzeroSq R ↔ IsSumNonzeroSq s := .rfl

@[simp]
/--
theorem `closure_mul_self` / 定理 `closure_mul_self`

English:
theorem closure_mul_self
  statement: closure {x * x | x != (0 : R)} = sumNonzeroSq R
  proof: by
  refine closure_eq_of_le (fun x hx => by aesop) (fun x hx => ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aeso

中文:
定理 closure_mul_self
  结论: closure {x * x | x != (0 : R)} = sumNonzeroSq R
  证明: by
  refine closure_eq_of_le (fun x hx => by aesop) (fun x hx => ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aeso

Depends on / 依赖: closure_eq_of_le
-/
theorem closure_mul_self : closure {x * x | x != (0 : R)} = sumNonzeroSq R := by
  refine closure_eq_of_le (fun x hx => by aesop) (fun x hx => ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aesop
    aesop

end AddSubsemigroup

end IsSumNonzeroSq

variable (R) in
/--
Definition of `IsFormallyReal` / `IsFormallyReal` 的定义

English:
class IsFormallyReal
  parameters: [AddCommMonoid R] [Mul R]
  axioms and operations (1):
    - not_isSumNonzeroSq_zero : ¬ IsSumNonzeroSq (0 : R)

中文:
类 是Formally实数
  参数: [加法交换幺半群 R] [乘法 R]
  公理与运算 (1 个):
    - not_isSumNonzeroSq_zero : ¬ 是SumNonzeroSq (0 : R)

Depends on / 依赖: Scheme, Scheme.Hom.opensFunctor, infer_instance, opensFunctor
-/
class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  not_isSumNonzeroSq_zero : ¬ IsSumNonzeroSq (0 : R)

namespace IsFormallyReal

/--
theorem `of_eq_zero_of_mul_self_of_eq_zero_of_add` / 定理 `of_eq_zero_of_mul_self_of_eq_zero_of_add`

English:
theorem of_eq_zero_of_mul_self_of_eq_zero_of_add
  statement: [AddCommMonoid R] [Mul R]
  proof: by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]

中文:
定理 of_eq_zero_of_mul_self_of_eq_zero_of_add
  结论: [加法交换幺半群 R] [乘法 R]
  证明: by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]

Depends on / 依赖: Functor, Functor.PreservesOneHypercovers.of_coverPreserving, IsSumNonzeroSq, IsSumSq, IsSumSq.mul_self, PreservesOneHypercovers, Scheme, Scheme.Hom.coverPreserving_opensFunctor, coverPreserving_opensFunctor, hs.isSumSq, isSumSq, mul_self, of_coverPreserving, sq_add
-/
theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : forall {a : R}, a * a = 0 -> a = 0)
    (ha : forall {s₁ s₂ : R}, IsSumSq s₁ -> IsSumSq s₂ -> s₁ + s₂ = 0 -> s₁ = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]

/--
theorem `of_eq_zero_of_eq_zero_of_mul_self_add` / 定理 `of_eq_zero_of_eq_zero_of_mul_self_add`

English:
theorem of_eq_zero_of_eq_zero_of_mul_self_add
  statement: [NonUnitalNonAssocSemiring R]
  proof: by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc => ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]

中文:
定理 of_eq_zero_of_eq_zero_of_mul_self_add
  结论: [非幺非结合半环 R]
  证明: by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc => ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]

Depends on / 依赖: IsSumNonzeroSq, IsSumSq, IsSumSq.zero, hs.isSumSq, isSumSq, sq_add
-/
theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : forall {s a : R}, IsSumSq s -> a * a + s = 0 -> a = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices forall (x : R), IsSumNonzeroSq x -> x != 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc => ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R
  body: of_eq_zero_of_mul_self_of_eq_zero_of_add mul_self_eq_zero.mp
    fun hs₁ hs₂ h => ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

中文:
实例 [环
  签名: R] [线性序 R] [是StrictOrdered环 R] : 是Formally实数 R
  定义体: of_eq_zero_of_mul_self_of_eq_zero_of_add mul_self_eq_zero.mp
    fun hs₁ hs₂ h => ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

Depends on / 依赖: IsSumSq, IsSumSq.nonneg, add_eq_zero_iff_of_nonneg, mul_self_eq_zero, mul_self_eq_zero.mp, nonneg, of_eq_zero_of_mul_self_of_eq_zero_of_add
-/
instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
of_eq_zero_of_mul_self_of_eq_zero_of_add mul_self_eq_zero.mp
    fun hs₁ hs₂ h => ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [IsFormallyReal R] : IsReduced R
  body: by
  rw [isReduced_iff_pow_one_lt 2 (by lia)]
  intro x hx
  by_contra! hc
exact not_isSumNonzeroSq_zero by simpa [← pow_two, hx] using IsSumNonzeroSq.sq hc

中文:
实例 [环
  签名: R] [是Formally实数 R] : 是既约 R
  定义体: by
  rw [isReduced_iff_pow_one_lt 2 (by lia)]
  intro x hx
  by_contra! hc
exact not_isSumNonzeroSq_zero by simpa [← pow_two, hx] using IsSumNonzeroSq.sq hc

Depends on / 依赖: IsSumNonzeroSq, IsSumNonzeroSq.sq, isReduced_iff_pow_one_lt, not_isSumNonzeroSq_zero, pow_two
-/
instance [Ring R] [IsFormallyReal R] : IsReduced R := by
  rw [isReduced_iff_pow_one_lt 2 (by lia)]
  intro x hx
  by_contra! hc
exact not_isSumNonzeroSq_zero by simpa [← pow_two, hx] using IsSumNonzeroSq.sq hc

/--
theorem `eq_zero_of_add_right` / 定理 `eq_zero_of_add_right`

English:
theorem eq_zero_of_add_right
  statement: [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
  proof: by
  by_contra! h₁
  have h₂ : s₂ != 0 := fun hc => by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

中文:
定理 eq_zero_of_add_right
  结论: [非幺非结合半环 R] [是Formally实数 R]
  证明: by
  by_contra! h₁
  have h₂ : s₂ != 0 := fun hc => by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

Depends on / 依赖: IsSumNonzeroSq, IsSumNonzeroSq.add, isSumNonzeroSq_iff_isSumSq, not_isSumNonzeroSq_zero
-/
theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  by_contra! h₁
  have h₂ : s₂ != 0 := fun hc => by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

/--
theorem `eq_zero_of_add_left` / 定理 `eq_zero_of_add_left`

English:
theorem eq_zero_of_add_left
  statement: [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
  proof: by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

中文:
定理 eq_zero_of_add_left
  结论: [非幺非结合半环 R] [是Formally实数 R]
  证明: by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

Depends on / 依赖: eq_zero_of_add_right
-/
theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

/--
theorem `eq_zero_of_isSumSq_of_neg_isSumSq` / 定理 `eq_zero_of_isSumSq_of_neg_isSumSq`

English:
theorem eq_zero_of_isSumSq_of_neg_isSumSq
  statement: [NonUnitalNonAssocRing R] [IsFormallyReal R]
  proof: eq_zero_of_add_right h₁ h₂ (by simp)

中文:
定理 eq_zero_of_isSumSq_of_neg_isSumSq
  结论: [非幺非结合环 R] [是Formally实数 R]
  证明: eq_zero_of_add_right h₁ h₂ (by simp)

Depends on / 依赖: eq_zero_of_add_right
-/
theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  eq_zero_of_add_right h₁ h₂ (by simp)

end IsFormallyReal
