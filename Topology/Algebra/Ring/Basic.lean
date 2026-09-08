/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.GroupTopology

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `Sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Filter TopologicalSpace Function Topology Filter

section IsTopologicalSemiring

variable (R : Type*)

/-- A topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `IsTopologicalSemiring` class should *only* be instantiated in the presence of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAssocRing`,
then `IsTopologicalRing` should be used. Note: in the presence of `NonAssocRing`, these classes are
mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` or
`IsTopologicalSemiring.toIsTopologicalRing`). -/
/-
**IsTopologicalSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [TopologicalSpace R] → [NonUnitalNonAssocSemiring R] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological semiring is a semiring `R` where addition and multiplication are c
ontinuous.
We allow for non-unital and non-associative semirings as well.

The `IsTopologicalSemiring` class should *only* be instantiated in the presence 
of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAs
socRing`,
then `IsTopologicalRing` should be used. Note: in the presence of `NonAssocRing`
, these classes are
mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` or
`IsTopologicalSemiring.toIsTopologicalRing`).
-/
class IsTopologicalSemiring [TopologicalSpace R] [NonUnitalNonAssocSemiring R] : Prop
    extends ContinuousAdd R, ContinuousMul R

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See `IsTopologicalSemiring.continuousNeg_of_mul`
and `IsTopologicalSemiring.toIsTopologicalRing`) -/
/-
**IsTopologicalRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [TopologicalSpace R] → [NonUnitalNonAssocRing R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological ring is a ring `R` where addition, multiplication and negation are
 continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from conti
nuity of
multiplication as it is multiplication with `-1`. (See `IsTopologicalSemiring.co
ntinuousNeg_of_mul`
and `IsTopologicalSemiring.toIsTopologicalRing`)
-/
class IsTopologicalRing [TopologicalSpace R] [NonUnitalNonAssocRing R] : Prop
    extends IsTopologicalSemiring R, ContinuousNeg R

/-- A semitopological semiring is a semiring `R` where addition is jointly continuous and
multiplication is continuous in each variable separately.
We allow for non-unital and non-associative semirings as well.

The `IsSemitopologicalSemiring` class should *only* be instantiated in the presence of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAssocRing`,
then `IsSemitopologicalRing` should be used. Note: in the presence of `NonAssocRing`, these classes
are mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` or
`IsSemitopologicalSemiring.toIsTopologicalRing`). -/
/-
**IsSemitopologicalSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [TopologicalSpace R] → [NonUnitalNonAssocSemiring R] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semitopological semiring is a semiring `R` where addition is jointly continuou
s and
multiplication is continuous in each variable separately.
We allow for non-unital and non-associative semirings as well.

The `IsSemitopologicalSemiring` class should *only* be instantiated in the prese
nce of a
`NonUnitalNonAssocSemiring` instance; if there is an instance of `NonUnitalNonAs
socRing`,
then `IsSemitopologicalRing` should be used. Note: in the presence of `NonAssocR
ing`, these classes
are mathematically equivalent (see `IsTopologicalSemiring.continuousNeg_of_mul` 
or
`IsSemitopologicalSemiring.toIsTopologicalRing`).
-/
class IsSemitopologicalSemiring (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  extends ContinuousAdd R, SeparatelyContinuousMul R

/-- A semitopological ring is a ring `R` where addition is jointly continuous and
multiplication is continuous in each variable separately, and negation is continuous as well.
We allow for non-unital and non-associative rings as well.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See `IsTopologicalSemiring.continuousNeg_of_mul`
and `IsSemitopologicalSemiring.toIsSemitopologicalRing`) -/
/-
**IsSemitopologicalRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [TopologicalSpace R] → [NonUnitalNonAssocRing R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semitopological ring is a ring `R` where addition is jointly continuous and
multiplication is continuous in each variable separately, and negation is contin
uous as well.
We allow for non-unital and non-associative rings as well.

If `R` is a (unital) ring, then continuity of negation can be derived from conti
nuity of
multiplication as it is multiplication with `-1`. (See `IsTopologicalSemiring.co
ntinuousNeg_of_mul`
and `IsSemitopologicalSemiring.toIsSemitopologicalRing`)
-/
class IsSemitopologicalRing (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocRing R]
  extends IsSemitopologicalSemiring R, ContinuousNeg R

variable {R}

/-- If `R` is a ring with a separately continuous multiplication, then negation is continuous as
well since it is just multiplication with `-1`. -/
/-
**IsSemitopologicalSemiring.continuousNeg_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemitopologicalSemiring.continuousNeg_of_mul [TopologicalSpace R] [NonAs
socRing R] [SeparatelyContinuousMul R] : ContinuousNeg R where continuous_neg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If `R` is a ring with a separately continuous multiplication, then negation is c
ontinuous as
well since it is just multiplication with `-1`.
-/
theorem IsSemitopologicalSemiring.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R]
    [SeparatelyContinuousMul R] : ContinuousNeg R where
  continuous_neg := by simpa using continuous_id.const_mul (-1 : R)

@[deprecated (since := "2026-03-13")] alias IsTopologicalSemiring.continuousNeg_of_mul :=
  IsSemitopologicalSemiring.continuousNeg_of_mul

/-- If `R` is a ring which is a semitopological semiring, then it is automatically a
semitopological ring. This exists so that one can place a topological ring structure on `R` without
explicitly proving `continuous_neg`. -/
/-
**IsSemitopologicalSemiring.toIsSemitopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsSemitopologicalSemiring.toIsSemitopologicalRing [TopologicalSpace R] [No
nAssocRing R] (_ : IsSemitopologicalSemiring R) : IsSemitopologicalRing R where 
toContinuousNeg
参数：_ : IsSemitopologicalSemiring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.continuousNeg_of_mul`：IsSemitopologicalSemirin
g.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R] [SeparatelyContinuo
usMul R] : ContinuousNeg R where con…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…

--- 原说明 ---
If `R` is a ring which is a semitopological semiring, then it is automatically a
semitopological ring. This exists so that one can place a topological ring struc
ture on `R` without
explicitly proving `continuous_neg`.
-/
theorem IsSemitopologicalSemiring.toIsSemitopologicalRing [TopologicalSpace R] [NonAssocRing R]
    (_ : IsSemitopologicalSemiring R) : IsSemitopologicalRing R where
  toContinuousNeg := IsSemitopologicalSemiring.continuousNeg_of_mul

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
/-
**IsTopologicalSemiring.toIsTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalSemiring.toIsTopologicalRing [TopologicalSpace R] [NonAssocRi
ng R] (_ : IsTopologicalSemiring R) : IsTopologicalRing R where toContinuousNeg
参数：_ : IsTopologicalSemiring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.continuousNeg_of_mul`：IsSemitopologicalSemirin
g.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R] [SeparatelyContinuo
usMul R] : ContinuousNeg R where con…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R

--- 原说明 ---
If `R` is a ring which is a topological semiring, then it is automatically a top
ological
ring. This exists so that one can place a topological ring structure on `R` with
out explicitly
proving `continuous_neg`.
-/
theorem IsTopologicalSemiring.toIsTopologicalRing [TopologicalSpace R] [NonAssocRing R]
    (_ : IsTopologicalSemiring R) : IsTopologicalRing R where
  toContinuousNeg := IsSemitopologicalSemiring.continuousNeg_of_mul
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsTopologicalRing.toIsSemitopologicalRing (R : Type*)
    [TopologicalSpace R] [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsSemitopologicalRing R where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsTopologicalSemiring.toIsSemitopologicalSemiring (R : Type*)
    [TopologicalSpace R] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsSemitopologicalSemiring R where

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsSemitopologicalRing.toIsTopologicalAddGroup [NonUnitalNonAssocRing R]
    [TopologicalSpace R] [IsSemitopologicalRing R] : IsTopologicalAddGroup R := ⟨⟩

-- kept just to avoid breaking manual usage of the previous instance
/-
**IsTopologicalRing.to_topologicalAddGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing R] [Topolo
gicalSpace R] [IsTopologicalRing R] : IsTopologicalAddGroup R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
-/
theorem IsTopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : IsTopologicalAddGroup R := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [DiscreteTopology R] : IsTopologicalSemiring R := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace R]
    [NonUnitalNonAssocRing R] [DiscreteTopology R] : IsTopologicalRing R := ⟨⟩

section

namespace NonUnitalSubsemiring

variable [TopologicalSpace R] [NonUnitalSemiring R]

/-
**NonUnitalSubsemiring.instIsSemitopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `
NonUnitalSubsemiring`。
形式化陈述：instIsSemitopologicalSemiring [IsSemitopologicalSemiring R] (S : NonUnital
Subsemiring R) : IsSemitopologicalSemiring S
参数：S : NonUnitalSubsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AddSubmonoid.continuousAdd`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : AddMonoid M] [ContinuousAdd M] (S : AddSubmonoid M),   ContinuousAdd 
↥S
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
instance instIsSemitopologicalSemiring [IsSemitopologicalSemiring R] (S : NonUnitalSubsemiring R) :
    IsSemitopologicalSemiring S :=
  { S.toSubsemigroup.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }
/-
**NonUnitalSubsemiring.instIsTopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonU
nitalSubsemiring`。
形式化陈述：instIsTopologicalSemiring [IsTopologicalSemiring R] (S : NonUnitalSubsemir
ing R) : IsTopologicalSemiring S
参数：S : NonUnitalSubsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `AddSubmonoid.continuousAdd`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : AddMonoid M] [ContinuousAdd M] (S : AddSubmonoid M),   ContinuousAdd 
↥S
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
instance instIsTopologicalSemiring [IsTopologicalSemiring R] (S : NonUnitalSubsemiring R) :
    IsTopologicalSemiring S :=
  { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

variable [IsSemitopologicalSemiring R]

/-- The (topological) closure of a non-unital subsemiring of a non-unital topological semiring is
itself a non-unital subsemiring. -/
/-
**NonUnitalSubsemiring.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：topologicalClosure (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring R
参数：s : NonUnitalSubsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological) closure of a non-unital subsemiring of a non-unital topologica
l semiring is
itself a non-unital subsemiring.
-/
def topologicalClosure (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
/-
**NonUnitalSubsemiring.topologicalClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubsemiring`。
形式化陈述：topologicalClosure_coe (s : NonUnitalSubsemiring R) : (s.topologicalClosur
e : Set R) = _root_.closure (s : Set R)
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem topologicalClosure_coe (s : NonUnitalSubsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl
/-
**NonUnitalSubsemiring.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubsemiring`。
形式化陈述：le_topologicalClosure (s : NonUnitalSubsemiring R) : s <= s.topologicalClo
sure
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem le_topologicalClosure (s : NonUnitalSubsemiring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
/-
**NonUnitalSubsemiring.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `No
nUnitalSubsemiring`。
形式化陈述：isClosed_topologicalClosure (s : NonUnitalSubsemiring R) : IsClosed (s.top
ologicalClosure : Set R)
参数：s : NonUnitalSubsemiring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_topologicalClosure (s : NonUnitalSubsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure
/-
**NonUnitalSubsemiring.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalSubsemiring`。
形式化陈述：topologicalClosure_minimal (s : NonUnitalSubsemiring R) {t : NonUnitalSubs
emiring R} (h : s <= t) (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t
参数：s : NonUnitalSubsemiring R；h : s <= t；ht : IsClosed (t : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem topologicalClosure_minimal (s : NonUnitalSubsemiring R) {t : NonUnitalSubsemiring R}
    (h : s ≤ t) (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**NonUnitalSubsemiring.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talSubsemiring`。
形式化陈述：topologicalClosure_mono {s t : NonUnitalSubsemiring R} (h : s <= t) : s.to
pologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem topologicalClosure_mono {s t : NonUnitalSubsemiring R} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a non-unital subsemiring of a non-unital topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
/-
**NonUnitalSubsemiring.nonUnitalCommSemiringTopologicalClosure** 是 Mathlib 中的一个缩
写定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：nonUnitalCommSemiringTopologicalClosure [T2Space R] (s : NonUnitalSubsemir
ing R) (hs : forall x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologica
lClosure
参数：s : NonUnitalSubsemiring R；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital subsemiring of a non-unital topological semiring is commutative,
 then so is its
topological closure.

See note [reducible non-instances]
-/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space R] (s : NonUnitalSubsemiring R)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubsemiring

variable [TopologicalSpace R] [Semiring R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalSemiring R] : IsTopologicalSemiring (ULift R) where

namespace Subsemiring

/-
**Subsemiring.semitopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：semitopologicalSemiring [IsSemitopologicalSemiring R] (S : Subsemiring R) 
: IsSemitopologicalSemiring S
参数：S : Subsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AddSubmonoid.continuousAdd`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : AddMonoid M] [ContinuousAdd M] (S : AddSubmonoid M),   ContinuousAdd 
↥S
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
-/
instance semitopologicalSemiring [IsSemitopologicalSemiring R] (S : Subsemiring R) :
    IsSemitopologicalSemiring S :=
  { S.toSubmonoid.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }
/-
**Subsemiring.topologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：topologicalSemiring [IsTopologicalSemiring R] (S : Subsemiring R) : IsTopo
logicalSemiring S
参数：S : Subsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `AddSubmonoid.continuousAdd`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : AddMonoid M] [ContinuousAdd M] (S : AddSubmonoid M),   ContinuousAdd 
↥S
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
instance topologicalSemiring [IsTopologicalSemiring R] (S : Subsemiring R) :
    IsTopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }
/-
**Subsemiring.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：continuousSMul (s : Subsemiring R) (X) [TopologicalSpace X] [MulAction R X
] [ContinuousSMul R X] : ContinuousSMul s X
参数：s : Subsemiring R；X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance continuousSMul (s : Subsemiring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Submonoid.continuousSMul

end Subsemiring

variable [IsSemitopologicalSemiring R]

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
/-
**Subsemiring.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemiring.topologicalClosure (s : Subsemiring R) : Subsemiring R
参数：s : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring.
-/
def Subsemiring.topologicalClosure (s : Subsemiring R) : Subsemiring R :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
/-
**Subsemiring.topologicalClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.topologicalClosure_coe (s : Subsemiring R) : (s.topologicalClo
sure : Set R) = _root_.closure (s : Set R)
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl
/-
**Subsemiring.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.le_topologicalClosure (s : Subsemiring R) : s <= s.topological
Closure
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subsemiring.le_topologicalClosure (s : Subsemiring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
/-
**Subsemiring.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.isClosed_topologicalClosure (s : Subsemiring R) : IsClosed (s.
topologicalClosure : Set R)
参数：s : Subsemiring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure
/-
**Subsemiring.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.topologicalClosure_minimal (s : Subsemiring R) {t : Subsemirin
g R} (h : s <= t) (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t
参数：s : Subsemiring R；h : s <= t；ht : IsClosed (t : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring R) {t : Subsemiring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**Subsemiring.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemiring.topologicalClosure_mono {s t : Subsemiring R} (h : s <= t) : s
.topologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Subsemiring.topologicalClosure_mono {s t : Subsemiring R} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
/-
**Subsemiring.commSemiringTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subsemiring.commSemiringTopologicalClosure [T2Space R] (s : Subsemiring R)
 (hs : forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure
参数：s : Subsemiring R；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a subsemiring of a topological semiring is commutative, then so is its
topological closure.

See note [reducible non-instances].
-/
abbrev Subsemiring.commSemiringTopologicalClosure [T2Space R] (s : Subsemiring R)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end

section

variable {S : Type*} [TopologicalSpace R] [TopologicalSpace S]

/-- The product topology on the Cartesian product of two topological semirings
  makes the product into a topological semiring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product topology on the Cartesian product of two topological semirings
  makes the product into a topological semiring.
-/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [IsTopologicalSemiring R]
    [IsTopologicalSemiring S] : IsTopologicalSemiring (R × S) where

/-- The product topology on the Cartesian product of two topological rings
  makes the product into a topological ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product topology on the Cartesian product of two topological rings
  makes the product into a topological ring.
-/
instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [IsTopologicalRing R]
    [IsTopologicalRing S] : IsTopologicalRing (R × S) where

/-- The product topology on the Cartesian product of two semitopological semirings
  makes the product into a semitopological semiring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product topology on the Cartesian product of two semitopological semirings
  makes the product into a semitopological semiring.
-/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [IsSemitopologicalSemiring R]
    [IsSemitopologicalSemiring S] : IsSemitopologicalSemiring (R × S) where

/-- The product topology on the Cartesian product of two semitopological rings
  makes the product into a semitopological ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product topology on the Cartesian product of two semitopological rings
  makes the product into a semitopological ring.
-/
instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [IsSemitopologicalRing R]
    [IsSemitopologicalRing S] : IsSemitopologicalRing (R × S) where

end

/-
**Pi.instIsTopologicalSemiring** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {R : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (R 
i)]   [inst_1 : (i : ι) → NonUnitalNonAssocSemiring (R i)] [∀ (i : ι), IsTopolog
icalSemiring (R i)],   IsTopologicalSemiring ((i : ι) → R i)
参数：i : ι；R i；i : ι；R i；i : ι；R i；(i : ι) → R i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
-/
instance Pi.instIsTopologicalSemiring {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, IsTopologicalSemiring (R i)] :
    IsTopologicalSemiring (∀ i, R i) where
/-
**Pi.instIsTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsTopologicalRing {ι : Type*} {R : ι -> Type*} [forall i, Topologic
alSpace (R i)] [forall i, NonUnitalNonAssocRing (R i)] [forall i, IsTopologicalR
ing (R i)] : IsTopologicalRing (forall i, R i)
参数：R i；R i；R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsTopologicalSemiring`：∀ {ι : Type u_2} {R : ι → Type u_3} [inst 
: (i : ι) → TopologicalSpace (R i)]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (R i)] [∀ (i :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Pi.continuousNeg`：∀ {ι : Type u_1} {C : ι → Type u_2} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Neg (C i)]   [∀ (i : ι), ContinuousN
eg (C …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
instance Pi.instIsTopologicalRing {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocRing (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (∀ i, R i) := ⟨⟩
/-
**Pi.instIsSemitopologicalSemiring** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_2} {R : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (R 
i)]   [inst_1 : (i : ι) → NonUnitalNonAssocSemiring (R i)] [∀ (i : ι), IsSemitop
ologicalSemiring (R i)],   IsSemitopologicalSemiring ((i : ι) → R i)
参数：i : ι；R i；i : ι；R i；i : ι；R i；(i : ι) → R i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
instance Pi.instIsSemitopologicalSemiring {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, IsSemitopologicalSemiring (R i)] :
    IsSemitopologicalSemiring (∀ i, R i) where
/-
**Pi.instIsSemitopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsSemitopologicalRing {ι : Type*} {R : ι -> Type*} [forall i, Topol
ogicalSpace (R i)] [forall i, NonUnitalNonAssocRing (R i)] [forall i, IsSemitopo
logicalRing (R i)] : IsSemitopologicalRing (forall i, R i)
参数：R i；R i；R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsSemitopologicalSemiring`：∀ {ι : Type u_2} {R : ι → Type u_3} [i
nst : (i : ι) → TopologicalSpace (R i)]   [inst_1 : (i : ι) → NonUnitalNonAssocS
emiring (R i)] [∀ (i :…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `Pi.continuousNeg`：∀ {ι : Type u_1} {C : ι → Type u_2} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Neg (C i)]   [∀ (i : ι), ContinuousN
eg (C …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
-/
instance Pi.instIsSemitopologicalRing {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, NonUnitalNonAssocRing (R i)] [∀ i, IsSemitopologicalRing (R i)] :
    IsSemitopologicalRing (∀ i, R i) := ⟨⟩

section MulOpposite

open MulOpposite

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousAdd R] :
    ContinuousAdd Rᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
    IsSemitopologicalSemiring Rᵐᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵐᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [ContinuousNeg R] : ContinuousNeg Rᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵐᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsSemitopologicalRing R] :
    IsSemitopologicalRing Rᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [SeparatelyContinuousMul R] :
    SeparatelyContinuousMul Rᵃᵒᵖ :=
  separatelyContinuousMul_induced opMulEquiv.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
    IsSemitopologicalSemiring Rᵃᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsSemitopologicalRing R] :
    IsSemitopologicalRing Rᵃᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousMul R] :
    ContinuousMul Rᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵃᵒᵖ := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵃᵒᵖ := ⟨⟩

end AddOpposite

section

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]

/-
**IsTopologicalRing.of_addGroup_of_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalRing.of_addGroup_of_nhds_zero [IsTopologicalAddGroup R] (hmul
 : Tendsto (uncurry ((· * ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0) (hmul_left : f
orall x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0) (hmul_right : forall x
₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : IsTopologicalRing R where c
ontinuous_mul
参数：hmul : Tendsto (uncurry ((· * ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0；hmul_lef
t : forall x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0；hmul_right : foral
l x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `continuous_of_continuousAt_zero₂`：∀ {G : Type w} [inst : TopologicalSpac
e G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {H : Type u_1} {M : Type u_
2}   [inst_3 : AddComm…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
theorem IsTopologicalRing.of_addGroup_of_nhds_zero [IsTopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : IsTopologicalRing R where
  continuous_mul := by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]
/-
**IsTopologicalRing.of_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalRing.of_nhds_zero (hadd : Tendsto (uncurry ((· + ·) : R -> R 
-> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0) (hneg : Tendsto (fun x => -x : R -> R) (𝓝 0) (𝓝 0)) 
(hmul : Tendsto (uncurry ((· * ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0) (hmul_lef
t : forall x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0) (hmul_right : for
all x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) (hleft : forall x₀ : R, 
𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : IsTopologicalRing R
参数：hadd : Tendsto (uncurry ((· + ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0；hneg : T
endsto (fun x => -x : R -> R) (𝓝 0) (𝓝 0)；hmul : Tendsto (uncurry ((· * ·) : R -
> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0；hmul_left : forall x₀ : R, Tendsto (fun x : R => 
x₀ * x) (𝓝 0) <| 𝓝 0；hmul_right : forall x₀ : R, Tendsto (fun x : R => x * x₀) (
𝓝 0) <| 𝓝 0；hleft : forall x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.of_comm_of_nhds_zero`：∀ {G : Type u} [inst : AddCo
mmGroup G] [inst_1 : TopologicalSpace G],   Filter.Tendsto (Function.uncurry fun
 x1 x2 => x1 + x2) (nhds 0 ×ˢ nh…
· 使用定理 `IsTopologicalRing.of_addGroup_of_nhds_zero`：IsTopologicalRing.of_addGrou
p_of_nhds_zero [IsTopologicalAddGroup R] (hmul : Tendsto (uncurry ((· * ·) : R -
> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0) …
-/
theorem IsTopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : IsTopologicalRing R :=
  have := IsTopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  IsTopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

end

variable [TopologicalSpace R]

section

variable [NonUnitalNonAssocRing R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalRing R] : IsTopologicalRing (ULift R) where

variable [IsSemitopologicalRing R]

/-- In a topological semiring, the left-multiplication `AddMonoidHom` is continuous. -/
/-
**mulLeft_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeft_continuous (x : R) : Continuous (AddMonoidHom.mulLeft x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
In a topological semiring, the left-multiplication `AddMonoidHom` is continuous.
-/
theorem mulLeft_continuous (x : R) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_id.const_mul _

/-- In a topological semiring, the right-multiplication `AddMonoidHom` is continuous. -/
/-
**mulRight_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRight_continuous (x : R) : Continuous (AddMonoidHom.mulRight x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
In a topological semiring, the right-multiplication `AddMonoidHom` is continuous
.
-/
theorem mulRight_continuous (x : R) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul_const _

end

namespace ContinuousAddEquiv

variable [Semiring R] [IsTopologicalSemiring R]

/-- The additive homeomorphism from a topological ring to itself,
induced by left multiplication by a unit. -/
@[simps! apply]
/-
**ContinuousAddEquiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAddEquiv`。
形式化陈述：mulLeft (r : Rˣ) : R ≃ₜ+ R where __
参数：r : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive homeomorphism from a topological ring to itself,
induced by left multiplication by a unit.
-/
def mulLeft (r : Rˣ) : R ≃ₜ+ R where
  __ := r.mulLeft
  map_add' x₁ x₂ := left_distrib ↑r x₁ x₂
  continuous_toFun := continuous_const_mul _
  continuous_invFun := continuous_const_mul _

/-- The additive homeomorphism from a topological ring to itself,
induced by right multiplication by a unit. -/
@[simps! apply]
/-
**ContinuousAddEquiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAddEquiv`。
形式化陈述：mulRight (r : Rˣ) : R ≃ₜ+ R where __
参数：r : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive homeomorphism from a topological ring to itself,
induced by right multiplication by a unit.
-/
def mulRight (r : Rˣ) : R ≃ₜ+ R where
  __ := r.mulRight
  map_add' x₁ x₂ := right_distrib x₁ x₂ r
  continuous_toFun := continuous_mul_const _
  continuous_invFun := continuous_mul_const _

end ContinuousAddEquiv

namespace NonUnitalSubring

variable [NonUnitalRing R]

/-
**NonUnitalSubring.instIsTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSub
ring`。
形式化陈述：instIsTopologicalRing [IsTopologicalRing R] (S : NonUnitalSubring R) : IsT
opologicalRing S
参数：S : NonUnitalSubring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `AddSubgroup.instIsTopologicalAddGroupSubtypeMem`：∀ {G : Type w} [inst : 
TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (S : AddSubg
roup G),   IsTopologicalAddGroup ↥S
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance instIsTopologicalRing [IsTopologicalRing R] (S : NonUnitalSubring R) :
    IsTopologicalRing S :=
  { S.toSubsemigroup.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }
/-
**NonUnitalSubring.instIsSemitopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnita
lSubring`。
形式化陈述：instIsSemitopologicalRing [IsSemitopologicalRing R] (S : NonUnitalSubring 
R) : IsSemitopologicalRing S
参数：S : NonUnitalSubring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `AddSubgroup.instIsTopologicalAddGroupSubtypeMem`：∀ {G : Type w} [inst : 
TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (S : AddSubg
roup G),   IsTopologicalAddGroup ↥S
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance instIsSemitopologicalRing [IsSemitopologicalRing R] (S : NonUnitalSubring R) :
    IsSemitopologicalRing S :=
  { S.toSubsemigroup.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

variable [IsSemitopologicalRing R]

/-- The (topological) closure of a non-unital subring of a non-unital topological ring is
itself a non-unital subring. -/
/-
**NonUnitalSubring.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：topologicalClosure (S : NonUnitalSubring R) : NonUnitalSubring R
参数：S : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological) closure of a non-unital subring of a non-unital topological ri
ng is
itself a non-unital subring.
-/
def topologicalClosure (S : NonUnitalSubring R) : NonUnitalSubring R :=
  { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }
/-
**NonUnitalSubring.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
ring`。
形式化陈述：le_topologicalClosure (s : NonUnitalSubring R) : s <= s.topologicalClosure
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem le_topologicalClosure (s : NonUnitalSubring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
/-
**NonUnitalSubring.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talSubring`。
形式化陈述：isClosed_topologicalClosure (s : NonUnitalSubring R) : IsClosed (s.topolog
icalClosure : Set R)
参数：s : NonUnitalSubring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_topologicalClosure (s : NonUnitalSubring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure
/-
**NonUnitalSubring.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubring`。
形式化陈述：topologicalClosure_minimal (s : NonUnitalSubring R) {t : NonUnitalSubring 
R} (h : s <= t) (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t
参数：s : NonUnitalSubring R；h : s <= t；ht : IsClosed (t : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem topologicalClosure_minimal (s : NonUnitalSubring R) {t : NonUnitalSubring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**NonUnitalSubring.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubring`。
形式化陈述：topologicalClosure_mono {s t : NonUnitalSubring R} (h : s <= t) : s.topolo
gicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem topologicalClosure_mono {s t : NonUnitalSubring R} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a non-unital subring of a non-unital topological ring is commutative, then so is its
topological closure.

See note [reducible non-instances] -/
/-
**NonUnitalSubring.nonUnitalCommRingTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名
空间 `NonUnitalSubring`。
形式化陈述：nonUnitalCommRingTopologicalClosure [T2Space R] (s : NonUnitalSubring R) (
hs : forall x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure
参数：s : NonUnitalSubring R；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital subring of a non-unital topological ring is commutative, then so
 is its
topological closure.

See note [reducible non-instances]
-/
abbrev nonUnitalCommRingTopologicalClosure [T2Space R] (s : NonUnitalSubring R)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubring

variable [Ring R]

/-
**Subring.instIsTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subring.instIsTopologicalRing [IsTopologicalRing R] (S : Subring R) : IsTo
pologicalRing S
参数：S : Subring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `AddSubgroup.instIsTopologicalAddGroupSubtypeMem`：∀ {G : Type w} [inst : 
TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (S : AddSubg
roup G),   IsTopologicalAddGroup ↥S
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance Subring.instIsTopologicalRing [IsTopologicalRing R] (S : Subring R) :
    IsTopologicalRing S :=
  { S.toSubmonoid.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }
/-
**Subring.instIsSemitopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subring.instIsSemitopologicalRing [IsSemitopologicalRing R] (S : Subring R
) : IsSemitopologicalRing S
参数：S : Subring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `AddSubgroup.instIsTopologicalAddGroupSubtypeMem`：∀ {G : Type w} [inst : 
TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (S : AddSubg
roup G),   IsTopologicalAddGroup ↥S
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance Subring.instIsSemitopologicalRing [IsSemitopologicalRing R] (S : Subring R) :
    IsSemitopologicalRing S :=
  { S.toSubmonoid.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

variable [IsSemitopologicalRing R]
/-
**Subring.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subring.continuousSMul (s : Subring R) (X) [TopologicalSpace X] [MulAction
 R X] [ContinuousSMul R X] : ContinuousSMul s X
参数：s : Subring R；X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subring.continuousSMul (s : Subring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Subsemiring.continuousSMul s.toSubsemiring X

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
/-
**Subring.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subring.topologicalClosure (S : Subring R) : Subring R
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological-space) closure of a subring of a topological ring is
itself a subring.
-/
def Subring.topologicalClosure (S : Subring R) : Subring R :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }
/-
**Subring.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subring.le_topologicalClosure (s : Subring R) : s <= s.topologicalClosure
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subring.le_topologicalClosure (s : Subring R) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
/-
**Subring.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subring.isClosed_topologicalClosure (s : Subring R) : IsClosed (s.topologi
calClosure : Set R)
参数：s : Subring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subring.isClosed_topologicalClosure (s : Subring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure
/-
**Subring.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subring.topologicalClosure_minimal (s : Subring R) {t : Subring R} (h : s 
<= t) (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t
参数：s : Subring R；h : s <= t；ht : IsClosed (t : Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subring.topologicalClosure_minimal (s : Subring R) {t : Subring R} (h : s ≤ t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**Subring.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subring.topologicalClosure_mono {s t : Subring R} (h : s <= t) : s.topolog
icalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Subring.topologicalClosure_mono {s t : Subring R} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a subring of a topological ring is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
/-
**Subring.commRingTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subring.commRingTopologicalClosure [T2Space R] (s : Subring R) (hs : foral
l x y : s, x * y = y * x) : CommRing s.topologicalClosure
参数：s : Subring R；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a subring of a topological ring is commutative, then so is its topological cl
osure.

See note [reducible non-instances].
-/
abbrev Subring.commRingTopologicalClosure [T2Space R] (s : Subring R)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end IsTopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `RingTopology R` which endows a ring `R` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `R` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : R → S` induces `coinduced f : TopologicalSpace R → RingTopology S`. -/


universe u v

/-- A ring topology on a ring `R` is a topology for which addition, negation and multiplication
are continuous. -/
/-
**RingTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Ring R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring topology on a ring `R` is a topology for which addition, negation and mul
tiplication
are continuous.
-/
structure RingTopology (R : Type u) [Ring R] : Type u
  extends TopologicalSpace R, IsTopologicalRing R

namespace RingTopology

variable {R : Type*} [Ring R]

/-
**RingTopology.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `RingTopology`。
形式化陈述：inhabited {R : Type u} [Ring R] : Inhabited (RingTopology R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited {R : Type u} [Ring R] : Inhabited (RingTopology R) :=
  ⟨let _ : TopologicalSpace R := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩
/-
**RingTopology.toTopologicalSpace_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingTopol
ogy`。
形式化陈述：toTopologicalSpace_injective : Injective (toTopologicalSpace : RingTopolog
y R -> TopologicalSpace R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology R → TopologicalSpace R) := by
  intro f g _; cases f; cases g; congr

@[ext]
/-
**RingTopology.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingTopology`。
形式化陈述：ext {f g : RingTopology R} (h : f.IsOpen = g.IsOpen) : f = g
参数：h : f.IsOpen = g.IsOpen。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingTopology.toTopologicalSpace_injective`：toTopologicalSpace_injective 
: Injective (toTopologicalSpace : RingTopology R -> TopologicalSpace R)
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
-/
theorem ext {f g : RingTopology R} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

/-- The ordering on ring topologies on the ring `R`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
/-
**RingTopology.** 是 Mathlib 中的一个实例，位于命名空间 `RingTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordering on ring topologies on the ring `R`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`).
-/
instance : PartialOrder (RingTopology R) :=
  PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

set_option backward.privateInPublic true in
/-
**RingTopology.def_sInf** 是 Mathlib 中的一个定义，位于命名空间 `RingTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def def_sInf (S : Set (RingTopology R)) : RingTopology R :=
  let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
    toContinuousMul := continuousMul_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
    toContinuousNeg := continuousNeg_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousNeg }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Ring topologies on `R` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
/-
**RingTopology.** 是 Mathlib 中的一个实例，位于命名空间 `RingTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring topologies on `R` form a complete lattice, with `⊥` the discrete topology a
nd `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all 
their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of 
all ring topologies
contained in the intersection of `s` and `t`.
-/
instance : CompleteSemilatticeInf (RingTopology R) where
  sInf := def_sInf
  isGLB_sInf _ := .of_image (f := toTopologicalSpace) .rfl (isGLB_sInf _)
/-
**RingTopology.** 是 Mathlib 中的一个实例，位于命名空间 `RingTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (RingTopology R) :=
  completeLatticeOfCompleteSemilatticeInf _

/-- Given `f : R → S` and a topology on `R`, the coinduced ring topology on `S` is the finest
topology such that `f` is continuous and `S` is a topological ring. -/
/-
**RingTopology.coinduced** 是 Mathlib 中的一个定义，位于命名空间 `RingTopology`。
形式化陈述：coinduced {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R -> S) : R
ingTopology S
参数：f : R -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : R → S` and a topology on `R`, the coinduced ring topology on `S` is t
he finest
topology such that `f` is continuous and `S` is a topological ring.
-/
def coinduced {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R → S) : RingTopology S :=
  sInf { b : RingTopology S | t.coinduced f ≤ b.toTopologicalSpace }
/-
**RingTopology.coinduced_continuous** 是 Mathlib 中的一个定理，位于命名空间 `RingTopology`。
形式化陈述：coinduced_continuous {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : 
R -> S) : Continuous[t, (coinduced f).toTopologicalSpace] f
参数：f : R -> S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sInf_rng`：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : 
Set (TopologicalSpace β)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous
[t₁, t] f
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
-/
theorem coinduced_continuous {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R → S) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
  continuous_sInf_rng.2 <| forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
/-
**RingTopology.toAddGroupTopology** 是 Mathlib 中的一个定义，位于命名空间 `RingTopology`。
形式化陈述：toAddGroupTopology (t : RingTopology R) : AddGroupTopology R where toTopol
ogicalSpace
参数：t : RingTopology R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from ring topologies on `a` to additive group topologies o
n `a`.
-/
def toAddGroupTopology (t : RingTopology R) : AddGroupTopology R where
  toTopologicalSpace := t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
/-
**RingTopology.toAddGroupTopology.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Ring
Topology.toAddGroupTopology`。
形式化陈述：{R : Type u_1} → [inst : Ring R] → RingTopology R ↪o AddGroupTopology R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order embedding from ring topologies on `a` to additive group topologies on 
`a`.
-/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology R) (AddGroupTopology R) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

end RingTopology

section AbsoluteValue

/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
/-
**AbsoluteValue.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] 
[PartialOrder S] (v : AbsoluteValue R S) {f : T ->+* R} (hf : Function.Injective
 f) : AbsoluteValue T S where toMulHom
参数：v : AbsoluteValue R S；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an absolute value on a semiring `T` from an absolute value on a semiri
ng `R`
and an injective ring homomorphism `f : T →+* R`
-/
def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S where
  toMulHom := v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)

end AbsoluteValue

