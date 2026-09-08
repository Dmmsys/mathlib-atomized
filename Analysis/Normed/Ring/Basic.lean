/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Submodule

import Mathlib.Data.Fintype.Order

/-!
# Normed rings

In this file we define (semi)normed rings. We also prove some theorems about these definitions.

A normed ring instance can be constructed from a given real absolute value on a ring via
`AbsoluteValue.toNormedRing`.
-/

@[expose] public section

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NonUnitalSeminormedRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  protected norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalSeminormedRing.toNonUnitalRing

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**SeminormedRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminormed ring is a ring endowed with a seminorm which satisfies the inequali
ty
`‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] SeminormedRing.toRing

-- see Note [lower instance priority]
/-- A seminormed ring is a non-unital seminormed ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminormed ring is a non-unital seminormed ring.
-/
instance (priority := 100) SeminormedRing.toNonUnitalSeminormedRing [β : SeminormedRing α] :
    NonUnitalSeminormedRing α :=
  { β with }

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NonUnitalNormedRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalNormedRing.toNonUnitalRing

-- see Note [lower instance priority]
/-- A non-unital normed ring is a non-unital seminormed ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital normed ring is a non-unital seminormed ring.
-/
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSeminormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSeminormedRing α :=
  { β with }

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NormedRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y
‖ ≤ ‖x‖ ‖y‖`.
-/
class NormedRing (α : Type*) extends Norm α, Ring α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedRing.toRing

-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed ring is a seminormed ring.
-/
instance (priority := 100) NormedRing.toSeminormedRing [β : NormedRing α] : SeminormedRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed ring is a non-unital normed ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed ring is a non-unital normed ring.
-/
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }

/-- A non-unital seminormed commutative ring is a non-unital commutative ring endowed with a
seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NonUnitalSeminormedCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital seminormed commutative ring is a non-unital commutative ring endowe
d with a
seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class NonUnitalSeminormedCommRing (α : Type*)
    extends NonUnitalSeminormedRing α, NonUnitalCommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalSeminormedCommRing.toNonUnitalCommRing

/-- A non-unital normed commutative ring is a non-unital commutative ring endowed with a
norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NonUnitalNormedCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital normed commutative ring is a non-unital commutative ring endowed wi
th a
norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class NonUnitalNormedCommRing (α : Type*) extends NonUnitalNormedRing α, NonUnitalCommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalNormedCommRing.toNonUnitalCommRing

-- see Note [lower instance priority]
/-- A non-unital normed commutative ring is a non-unital seminormed commutative ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital normed commutative ring is a non-unital seminormed commutative ring
.
-/
instance (priority := 100) NonUnitalNormedCommRing.toNonUnitalSeminormedCommRing
    [β : NonUnitalNormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**SeminormedCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminormed commutative ring is a commutative ring endowed with a seminorm whic
h satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class SeminormedCommRing (α : Type*) extends SeminormedRing α, CommRing α where

-- see Note [lower instance priority]
attribute [instance 10] SeminormedCommRing.toCommRing

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
/-
**NormedCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed commutative ring is a commutative ring endowed with a norm which satisf
ies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`.
-/
class NormedCommRing (α : Type*) extends NormedRing α, CommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NormedCommRing.toCommRing

-- see Note [lower instance priority]
/-- A seminormed commutative ring is a non-unital seminormed commutative ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminormed commutative ring is a non-unital seminormed commutative ring.
-/
instance (priority := 100) SeminormedCommRing.toNonUnitalSeminormedCommRing
    [β : SeminormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a non-unital normed commutative ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed commutative ring is a non-unital normed commutative ring.
-/
instance (priority := 100) NormedCommRing.toNonUnitalNormedCommRing
    [β : NormedCommRing α] : NonUnitalNormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a seminormed commutative ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed commutative ring is a seminormed commutative ring.
-/
instance (priority := 100) NormedCommRing.toSeminormedCommRing [β : NormedCommRing α] :
    SeminormedCommRing α :=
  { β with }
/-
**PUnit.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.normedCommRing : NormedCommRing PUnit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
· 使用定理 `CommRing.mul_comm`：∀ {α : Type u} [self : CommRing α] (a b : α), a * b =
 b * a
-/
instance PUnit.normedCommRing : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul_le _ _ := by simp }

section NormOneClass

/-- A mixin class with the axiom `‖1‖ = 1`. Many `NormedRing`s and all `NormedField`s satisfy this
axiom. -/
/-
**NormOneClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → [Norm α] → [One α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin class with the axiom `‖1‖ = 1`. Many `NormedRing`s and all `NormedField`
s satisfy this
axiom.
-/
class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup G] [One G] [NormOneClass G]

/-
**nnnorm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : One G] [NormO
neClass G], ‖1‖₊ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
-/
@[simp] lemma nnnorm_one : ‖(1 : G)‖₊ = 1 := NNReal.eq norm_one
/-
**enorm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : One G] [NormO
neClass G], ‖1‖ₑ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_one : ‖(1 : G)‖ₑ = 1 := by simp [enorm]
/-
**NormOneClass.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormOneClass.nontrivial : Nontrivial G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem NormOneClass.nontrivial : Nontrivial G :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp

end SeminormedAddCommGroup

end NormOneClass

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalSeminormedRing.toSeminormedAddCommGroup
    [NonUnitalSeminormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSeminormedRing α› with }
/-
**ULift.normOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] : N
ormOneClass (ULift α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩
/-
**Prod.normOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] [Sem
inormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩
/-
**Pi.normOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normOneClass {ι : Type*} {α : ι -> Type*} [Nonempty ι] [Fintype ι] [for
all i, SeminormedAddCommGroup (α i)] [forall i, One (α i)] [forall i, NormOneCla
ss (α i)] : NormOneClass (forall i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
instance Pi.normOneClass {ι : Type*} {α : ι → Type*} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩
/-
**MulOpposite.normOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass 
α] : NormOneClass αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
-/
instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α] {a a₁ a₂ b c : α}

/-- The norm is submultiplicative. -/
/-
**norm_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.norm_mul_le`：∀ {α : Type u_5} [self : NonUnitalS
eminormedRing α] (a b : α), ‖a * b‖ ≤ ‖a‖ * ‖b‖

--- 原说明 ---
The norm is submultiplicative.
-/
theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  NonUnitalSeminormedRing.norm_mul_le a b
/-
**nnnorm_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_mul_le (a b : α) : ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := norm_mul_le a b
/-
**norm_mul_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_mul_le_of_le {r₁ r₂ : Real} (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂) : ‖a₁
 * a₂‖ <= r₁ * r₂
参数：h₁ : ‖a₁‖ <= r₁；h₂ : ‖a₂‖ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
  (norm_mul_le ..).trans <| mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
/-
**nnnorm_mul_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_mul_le_of_le {r₁ r₂ : Real>=0} (h₁ : ‖a₁‖₊ <= r₁) (h₂ : ‖a₂‖₊ <= r₂
) : ‖a₁ * a₂‖₊ <= r₁ * r₂
参数：h₁ : ‖a₁‖₊ <= r₁；h₂ : ‖a₂‖₊ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nnnorm_mul_le`：nnnorm_mul_le (a b : α) : ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
lemma nnnorm_mul_le_of_le {r₁ r₂ : ℝ≥0} (h₁ : ‖a₁‖₊ ≤ r₁) (h₂ : ‖a₂‖₊ ≤ r₂) :
    ‖a₁ * a₂‖₊ ≤ r₁ * r₂ := (nnnorm_mul_le ..).trans <| mul_le_mul' h₁ h₂
/-
**norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : 
α), ‖a * b‖ = ‖a‖ * ‖b‖
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormMulClass.norm_mul`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : Mul α}
 [self : NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl
/-
**nnnorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : Mul α] [NormM
ulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
lemma nnnorm_mul₃_le : ‖a * b * c‖₊ ≤ ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
  nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl
/-
**one_le_norm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 <= ‖(1 : β)‖
参数：β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_mul_iff_one_le_left`：le_mul_iff_one_le_left [MulPosMono α] [MulPosRef
lectLE α] (a0 : 0 < a) : a <= b * a ↔ 1 <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)
/-
**one_le_nnnorm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 <= ‖(1 : β)‖₊
参数：β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_le_norm_one`：one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 <
= ‖(1 : β)‖
-/
theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β

/-- In a seminormed ring, the left-multiplication `AddMonoidHom` is bounded. -/
/-
**mulLeft_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeft_bound (x : α) : forall y : α, ‖AddMonoidHom.mulLeft x y‖ <= ‖x‖ * 
‖y‖
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖

--- 原说明 ---
In a seminormed ring, the left-multiplication `AddMonoidHom` is bounded.
-/
theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x

/-- In a seminormed ring, the right-multiplication `AddMonoidHom` is bounded. -/
/-
**mulRight_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRight_bound (x : α) : forall y : α, ‖AddMonoidHom.mulRight x y‖ <= ‖x‖ 
* ‖y‖
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖

--- 原说明 ---
In a seminormed ring, the right-multiplication `AddMonoidHom` is bounded.
-/
theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
/-
**NonUnitalSubalgebra.nonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : 
Type*} [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : 
NonUnitalSeminormedRing s
参数：s : NonUnitalSubalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra of a non-unital seminormed ring is also a non-unital sem
inormed ring,
with the restriction of the norm.
-/
instance NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalSeminormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalSeminormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalSeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, NonUnitalSubringClass.toNonUnitalRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring, with the
restriction of the norm. -/
/-
**NonUnitalSubalgebra.nonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type
*} [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnita
lNormedRing s
参数：s : NonUnitalSubalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra of a non-unital normed ring is also a non-unital normed 
ring, with the
restriction of the norm.
-/
instance NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnitalNormedRing s :=
  { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring,
with the restriction of the norm. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra of a non-unital normed ring is also a non-unital normed 
ring,
with the restriction of the norm.
-/
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalNormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalNormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalNormedRing s :=
  { nonUnitalSeminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**ULift.nonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul_le x y := norm_mul_le x.down y.down }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
/-
**Prod.nonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] : NonUnitalSemino
rmedRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital seminormed ring structure on the product of two non-unital seminormed
 rings,
  using the sup norm.
-/
instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul_le x y := calc
      ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
      _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
      _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
        (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
      _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
      _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
      _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
      _ = ‖x‖ * ‖y‖ := rfl }
/-
**MulOpposite.instNonUnitalSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ whe
re __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul_le := MulOpposite.rec' fun x ↦ MulOpposite.rec' fun y ↦
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α] {a b c : α}

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
/-
**Subalgebra.seminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [Seminormed
Ring E] [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s
参数：s : Subalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of a seminormed ring is also a seminormed ring, with the restrictio
n of the
norm.
-/
instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) SubalgebraClass.seminormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : SeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, SubringClass.toRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm. -/
/-
**Subalgebra.normedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E] 
[Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s
参数：s : Subalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of a normed ring is also a normed ring, with the restriction of the
 norm.
-/
instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the
norm. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of a normed ring is also a normed ring, with the restriction of the
norm.
-/
instance (priority := 75) SubalgebraClass.normedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [NormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**Nat.norm_cast_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] (n : ℕ), ‖↑n‖ ≤ ↑n * ‖1‖
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl
/-
**List.norm_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.norm_prod_le' : forall {l : List α}, l != [] -> ‖l.prod‖ <= (l.map no
rm).prod | [], h => (h rfl).elim | [a], _ => by simp | a::b::l, _ => by rw [List
.map_cons]; rw [List.prod_cons]; rw [List.prod_cons (a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.prod‖ ≤ (l.map norm).prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, List.prod_cons (a := ‖a‖)]
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)
/-
**List.nnnorm_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.nnnorm_prod_le' {l : List α} (hl : l != []) : ‖l.prod‖₊ <= (l.map nnn
orm).prod
参数：hl : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `List.norm_prod_le'`：List.norm_prod_le' : forall {l : List α}, l != [] ->
 ‖l.prod‖ <= (l.map norm).prod | [], h => (h rfl).elim | [a], _ => by simp | a::
b::l, _ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_list_prod`：coe_list_prod (l : List Real>=0) : ((l.prod : Real
>=0) : Real) = (l.map (↑)).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
/-
**List.norm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] (l : List α), 
‖l.prod‖ ≤ (List.map norm l).prod
参数：l : List α；List.map norm l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.norm_prod_le'`：List.norm_prod_le' : forall {l : List α}, l != [] ->
 ‖l.prod‖ <= (l.map norm).prod | [], h => (h rfl).elim | [a], _ => by simp | a::
b::l, _ …
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.prod‖ ≤ (l.map norm).prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)
/-
**List.nnnorm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ <= (l.map nn
norm).prod
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `List.norm_prod_le`：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneCl
ass α] (l : List α), ‖l.prod‖ ≤ (List.map norm l).prod
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_list_prod`：coe_list_prod (l : List Real>=0) : ((l.prod : Real
>=0) : Real) = (l.map (↑)).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
/-
**Finset.norm_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s
.Nonempty) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i‖
参数：s : Finset ι；hs : s.Nonempty；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.norm_prod_le'`：List.norm_prod_le' : forall {l : List α}, l != [] ->
 ‖l.prod‖ <= (l.map norm).prod | [], h => (h rfl).elim | [a], _ => by simp | a::
b::l, _ …
-/
theorem Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using! hs
  simpa using! List.norm_prod_le' this
/-
**Finset.nnnorm_prod_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs :
 s.Nonempty) (f : ι -> α) : ‖∏ i in s, f i‖₊ <= ∏ i in s, ‖f i‖₊
参数：s : Finset ι；hs : s.Nonempty；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.norm_prod_le'`：Finset.norm_prod_le' {α : Type*} [NormedCommRing α
] (s : Finset ι) (hs : s.Nonempty) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖
f i‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]
/-
**Finset.norm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : F
inset ι) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i‖
参数：s : Finset ι；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.norm_prod_le`：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneCl
ass α] (l : List α), ‖l.prod‖ ≤ (List.map norm l).prod
-/
theorem Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using! (l.map f).norm_prod_le
/-
**Finset.nnnorm_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s :
 Finset ι) (f : ι -> α) : ‖∏ i in s, f i‖₊ <= ∏ i in s, ‖f i‖₊
参数：s : Finset ι；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.norm_prod_le`：Finset.norm_prod_le {α : Type*} [NormedCommRing α] 
[NormOneClass α] (s : Finset ι) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i
‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]
/-
**norm_natAbs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_natAbs (z : Int) : ‖(z.natAbs : α)‖ = ‖(z : α)‖
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
lemma norm_natAbs (z : ℤ) :
    ‖(z.natAbs : α)‖ = ‖(z : α)‖ := by
  rcases z.natAbs_eq with hz | hz
  · rw [← Int.cast_natCast, ← hz]
  · rw [← Int.cast_natCast, ← norm_neg, ← Int.cast_neg, ← hz]
/-
**nnnorm_natAbs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_natAbs (z : Int) : ‖(z.natAbs : α)‖₊ = ‖(z : α)‖₊
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_natAbs`：norm_natAbs (z : Int) : ‖(z.natAbs : α)‖ = ‖(z : α)‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_natAbs (z : ℤ) :
    ‖(z.natAbs : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← NNReal.coe_inj, -Nat.cast_natAbs, norm_natAbs]
/-
**norm_intCast_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] (z : ℤ), ‖↑|z|‖ = ‖↑z‖
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma norm_intCast_abs (z : ℤ) :
    ‖((|z| : ℤ) : α)‖ = ‖(z : α)‖ := by
  simp [← norm_natAbs]
/-
**nnnorm_intCast_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] (z : ℤ), ‖↑|z|‖₊ = ‖↑z‖₊
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_intCast_abs (z : ℤ) :
    ‖((|z| : ℤ) : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← nnnorm_natAbs]

/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
/-
**nnnorm_pow_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] (a : α) {n : ℕ}, 0 < n → ‖a ^ n
‖₊ ≤ ‖a‖₊ ^ n
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`.
-/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_right (nnnorm_pow_le' a n.succ_pos) _)

/-- If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`. -/
/-
**nnnorm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖₊ <= ‖a‖₊ ^ n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `nnnorm_pow_le'`：∀ {α : Type u_2} [inst : SeminormedRing α] (a : α) {n : 
ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`.
-/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp)
    fun k _hk => nnnorm_pow_le' a k.succ_pos

/-- If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `norm_pow_le`. -/
/-
**norm_pow_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a‖ ^ n
参数：a : α；h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `nnnorm_pow_le'`：∀ {α : Type u_2} [inst : SeminormedRing α] (a : α) {n : 
ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n

--- 原说明 ---
If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `nor
m_pow_le`.
-/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

/-- If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`.
See also `norm_pow_le'`. -/
/-
**norm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖ <= ‖a‖ ^ n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `norm_pow_le'`：norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a
‖ ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`.
See also `norm_pow_le'`.
-/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp)
    fun n _hn => norm_pow_le' a n.succ_pos
/-
**eventually_norm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_norm_pow_le (a : α) : forallᶠ n : Nat in atTop, ‖a ^ n‖ <= ‖a‖ 
^ n
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `norm_pow_le'`：norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a
‖ ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
-/
theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩
/-
**ULift.seminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.seminormedRing : SeminormedRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.ring with }

/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
/-
**Prod.seminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed ring structure on the product of two seminormed rings,
  using the sup norm.
-/
instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { nonUnitalSeminormedRing, instRing with }
/-
**MulOpposite.instSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instNonUnitalSeminormedRing

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
/-
**norm_sub_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_mul_le (ha : ‖a‖ <= 1) : ‖c - a * b‖ <= ‖c - a‖ + ‖1 - b‖
参数：ha : ‖a‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one_sub`：mul_one_sub (a b : α) : a * (1 - b) = a - a * b
· 使用定理 `norm_sub_le_norm_sub_add_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAd
dGroup E] (a b c : E), ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it th
en shows that
chord length is a metric on the unit complex numbers.
-/
lemma norm_sub_mul_le (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ :=
  calc
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
/-
**norm_sub_mul_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sub_mul_le' (hb : ‖b‖ <= 1) : ‖c - a * b‖ <= ‖1 - a‖ + ‖c - b‖
参数：hb : ‖b‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `norm_sub_mul_le`：norm_sub_mul_le (ha : ‖a‖ <= 1) : ‖c - a * b‖ <= ‖c - a
‖ + ‖1 - b‖

--- 原说明 ---
This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it th
en shows that
chord length is a metric on the unit complex numbers.
-/
lemma norm_sub_mul_le' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ := by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
/-
**nnnorm_sub_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_sub_mul_le (ha : ‖a‖₊ <= 1) : ‖c - a * b‖₊ <= ‖c - a‖₊ + ‖1 - b‖₊
参数：ha : ‖a‖₊ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_sub_mul_le`：norm_sub_mul_le (ha : ‖a‖ <= 1) : ‖c - a * b‖ <= ‖c - a
‖ + ‖1 - b‖

--- 原说明 ---
This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it th
en shows that
chord length is a metric on the unit complex numbers.
-/
lemma nnnorm_sub_mul_le (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ := norm_sub_mul_le ha

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
/-
**nnnorm_sub_mul_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_sub_mul_le' (hb : ‖b‖₊ <= 1) : ‖c - a * b‖₊ <= ‖1 - a‖₊ + ‖c - b‖₊
参数：hb : ‖b‖₊ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_sub_mul_le'`：norm_sub_mul_le' (hb : ‖b‖ <= 1) : ‖c - a * b‖ <= ‖1 -
 a‖ + ‖c - b‖

--- 原说明 ---
This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it th
en shows that
chord length is a metric on the unit complex numbers.
-/
lemma nnnorm_sub_mul_le' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ := norm_sub_mul_le' hb
/-
**norm_commutator_units_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_commutator_units_sub_one_le (a b : αˣ) : ‖(a * b * a⁻¹ * b⁻¹).val - 1
‖ <= 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖
参数：a b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `norm_mul₃_le`：norm_mul₃_le : ‖a * b * c‖ <= ‖a‖ * ‖b‖ * ‖c‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_one_mul`：sub_one_mul (a b : α) : (a - 1) * b = a * b - b
· 使用定理 `mul_sub_one`：mul_sub_one (a b : α) : a * (b - 1) = a * b - a
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Abel.termg_eq`：termg_eq {α : Type*} [AddCommGroup α] (n :
 Int) (x a : α) : termg n x a = n • x + a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 63 条，此处仅展示前 30 条）
-/
lemma norm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ ≤ 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ :=
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ ≤ ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ ≤ (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ ≤ (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring
/-
**nnnorm_commutator_units_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_commutator_units_sub_one_le (a b : αˣ) : ‖(a * b * a⁻¹ * b⁻¹).val -
 1‖₊ <= 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.val - 1‖₊ * ‖b.val - 1‖₊
参数：a b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `norm_commutator_units_sub_one_le`：norm_commutator_units_sub_one_le (a b 
: αˣ) : ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ <= 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖
 * ‖b.val - 1‖
-/
lemma nnnorm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖₊ ≤ 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.val - 1‖₊ * ‖b.val - 1‖₊ := by
  simpa using! norm_commutator_units_sub_one_le a b

/-- A homomorphism `f` between semi_normed_rings is bounded if there exists a positive
  constant `C` such that for all `x` in `α`, `norm (f x) ≤ C * norm x`. -/
/-
**RingHom.IsBounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.IsBounded {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRi
ng β] (f : α ->+* β) : Prop
参数：f : α ->+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism `f` between semi_normed_rings is bounded if there exists a positi
ve
  constant `C` such that for all `x` in `α`, `norm (f x) ≤ C * norm x`.
-/
def RingHom.IsBounded {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRing β]
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/-
**ULift.nonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
/-
**Prod.nonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α 
× β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm.
-/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }
/-
**MulOpposite.instNonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/-
**Units.norm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖
参数：x : αˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
-/
theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)
/-
**Units.nnnorm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊
参数：x : αˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.norm_pos`：Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖
-/
theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos
/-
**ULift.normedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.normedRing : NormedRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddCommGroup with }

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
/-
**Prod.normedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.normedRing [NormedRing β] : NormedRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed ring structure on the product of two normed rings, using the sup norm.
-/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { nonUnitalNormedRing, instRing with }
/-
**MulOpposite.instNormedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/-
**ULift.nonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

/-- Non-unital seminormed commutative ring structure on the product of two non-unital seminormed
commutative rings, using the sup norm. -/
/-
**Prod.nonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] : NonUnit
alSeminormedCommRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital seminormed commutative ring structure on the product of two non-unita
l seminormed
commutative rings, using the sup norm.
-/
instance Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing (α × β) :=
  { nonUnitalSeminormedRing, instNonUnitalCommRing with }
/-
**MulOpposite.instNonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing 
αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- A non-unital subalgebra of a non-unital seminormed commutative ring is also a non-unital
seminormed commutative ring, with the restriction of the norm. -/
/-
**NonUnitalSubalgebra.nonUnitalSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {
E : Type*} [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra
 𝕜 E) : NonUnitalSeminormedCommRing s
参数：s : NonUnitalSubalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra of a non-unital seminormed commutative ring is also a no
n-unital
seminormed commutative ring, with the restriction of the norm.
-/
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

/-- A non-unital subalgebra of a non-unital normed commutative ring is also a non-unital normed
commutative ring, with the restriction of the norm. -/
/-
**NonUnitalSubalgebra.nonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : 
Type*} [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : 
NonUnitalNormedCommRing s
参数：s : NonUnitalSubalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra of a non-unital normed commutative ring is also a non-un
ital normed
commutative ring, with the restriction of the norm.
-/
instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }
/-
**ULift.nonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

/-- Non-unital normed commutative ring structure on the product of two non-unital normed
commutative rings, using the sup norm. -/
/-
**Prod.nonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] : NonUnitalNormed
CommRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital normed commutative ring structure on the product of two non-unital no
rmed
commutative rings, using the sup norm.
-/
instance Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }
/-
**MulOpposite.instNonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ whe
re __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/-
**ULift.seminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.seminormedCommRing : SeminormedCommRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

/-- Seminormed commutative ring structure on the product of two seminormed commutative rings,
  using the sup norm. -/
/-
**Prod.seminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed commutative ring structure on the product of two seminormed commutati
ve rings,
  using the sup norm.
-/
instance Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, instCommRing with }
/-
**MulOpposite.instSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

end SeminormedCommRing

section NormedCommRing

/-- A subalgebra of a seminormed commutative ring is also a seminormed commutative ring, with the
restriction of the norm. -/
/-
**Subalgebra.seminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [Semino
rmedCommRing E] [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s
参数：s : Subalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of a seminormed commutative ring is also a seminormed commutative r
ing, with the
restriction of the norm.
-/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

/-- A subalgebra of a normed commutative ring is also a normed commutative ring, with the
restriction of the norm. -/
/-
**Subalgebra.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedComm
Ring E] [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s
参数：s : Subalgebra 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of a normed commutative ring is also a normed commutative ring, wit
h the
restriction of the norm.
-/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]
/-
**ULift.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.normedCommRing : NormedCommRing (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

/-- Normed commutative ring structure on the product of two normed commutative rings, using the sup
norm. -/
/-
**Prod.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed commutative ring structure on the product of two normed commutative rings
, using the sup
norm.
-/
instance Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β) :=
  { nonUnitalNormedRing, instCommRing with }
/-
**MulOpposite.instNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where
  __ := instNormedRing
  __ := instSeminormedCommRing

/-- The restriction of a power-multiplicative function to a subalgebra is power-multiplicative. -/
/-
**IsPowMul.restriction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPowMul.restriction {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (A 
: Subalgebra R S) {f : S -> Real} (hf_pm : IsPowMul f) : IsPowMul fun x : A => f
 x.val
参数：A : Subalgebra R S；hf_pm : IsPowMul f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A

--- 原说明 ---
The restriction of a power-multiplicative function to a subalgebra is power-mult
iplicative.
-/
theorem IsPowMul.restriction {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (A : Subalgebra R S) {f : S → ℝ} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa using hf_pm (↑x) hn

end NormedCommRing

/-
**Real.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.normedCommRing : NormedCommRing Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
· 使用定理 `CommRing.mul_comm`：∀ {α : Type u} [self : CommRing α] (a b : α), a * b =
 b * a
-/
instance Real.normedCommRing : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul_le x y := (abs_mul x y).le }

namespace NNReal

open NNReal

/-
**NNReal.norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：norm_eq (x : Real>=0) : ‖(x : Real)‖ = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
-/
theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]
/-
**NNReal.nnnorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), ‖↑x‖₊ = x
参数：x : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x := by ext; simp [nnnorm]
/-
**NNReal.enorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
参数：x : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.nnnorm_eq`：∀ (x : NNReal), ‖↑x‖₊ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ₑ = x := by simp [enorm]

end NNReal

/-- A restatement of `MetricSpace.tendsto_atTop` in terms of the norm. -/
/-
**NormedAddCommGroup.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirectedOrde
r α] {β : Type*} [SeminormedAddCommGroup β] {f : α -> β} {b : β} : Tendsto f atT
op (𝓝 b) ↔ forall ε, 0 < ε -> exists N, forall n, N <= n -> ‖f n - b‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A restatement of `MetricSpace.tendsto_atTop` in terms of the norm.
-/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/-- A variant of `NormedAddCommGroup.tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
/-
**NormedAddCommGroup.tendsto_atTop'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirectedOrd
er α] [NoMaxOrder α] {β : Type*} [SeminormedAddCommGroup β] {f : α -> β} {b : β}
 : Tendsto f atTop (𝓝 b) ↔ forall ε, 0 < ε -> exists N, forall n, N < n -> ‖f n 
- b‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant of `NormedAddCommGroup.tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    [NoMaxOrder α] {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

section RingHomIsometric

variable {R₁ R₂ : Type*}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
/-
**RingHomIsometric** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R₁ : Type u_5} →   {R₂ : Type u_6} → [inst : Semiring R₁] → [inst_1 : Sem
iring R₂] → [Norm R₁] → [Norm R₂] → (R₁ →+* R₂) → Prop
参数：R₁ →+* R₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This class states that a ring homomorphism is isometric. This is a sufficient as
sumption
for a continuous semilinear map to be bounded and this is the main use for this 
typeclass.
-/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  norm_map : ∀ {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.norm_map

@[simp]
/-
**RingHomIsometric.nnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHomIsometric.nnnorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R
₁ ->+* R₂) [RingHomIsometric σ] (x : R₁) : ‖σ x‖₊ = ‖x‖₊
参数：σ : R₁ ->+* R₂；x : R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
-/
theorem RingHomIsometric.nnnorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ →+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖₊ = ‖x‖₊ :=
  NNReal.eq norm_map

@[simp]
/-
**RingHomIsometric.enorm_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHomIsometric.enorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁
 ->+* R₂) [RingHomIsometric σ] (x : R₁) : ‖σ x‖ₑ = ‖x‖ₑ
参数：σ : R₁ ->+* R₂；x : R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomIsometric.nnnorm_map`：RingHomIsometric.nnnorm_map [SeminormedRing
 R₁] [SeminormedRing R₂] (σ : R₁ ->+* R₂) [RingHomIsometric σ] (x : R₁) : ‖σ x‖₊
 = ‖x‖₊
-/
theorem RingHomIsometric.enorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ →+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖ₑ = ‖x‖ₑ :=
  congrArg ENNReal.ofNNReal <| nnnorm_map σ x

variable [SeminormedRing R₁]
/-
**RingHomIsometric.ids** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨rfl⟩

end RingHomIsometric

section NormMulClass

/-- A mixin class for strict multiplicativity of the norm, `‖a * b‖ = ‖a‖ * ‖b‖` (rather than
`≤` as in the definition of `NormedRing`). Many `NormedRing`s satisfy this stronger property,
including all `NormedDivisionRing`s and `NormedField`s. -/
/-
**NormMulClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → [Norm α] → [Mul α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin class for strict multiplicativity of the norm, `‖a * b‖ = ‖a‖ * ‖b‖` (ra
ther than
`≤` as in the definition of `NormedRing`). Many `NormedRing`s satisfy this stron
ger property,
including all `NormedDivisionRing`s and `NormedField`s.
-/
class NormMulClass (α : Type*) [Norm α] [Mul α] : Prop where
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
/-
**norm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClass α] (a b : 
α), ‖a * b‖ = ‖a‖ * ‖b‖
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormMulClass.norm_mul`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : Mul α}
 [self : NormMulClass α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
    ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormMulClass.norm_mul a b

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [Mul α] [NormMulClass α] (a b : α)

/-
**nnnorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : Mul α] [NormM
ulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq <| norm_mul a b
/-
**enorm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : Mul α] [NormM
ulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_mul : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by simp [enorm]

end SeminormedAddCommGroup

section SeminormedRing

variable [SeminormedRing α] [NormOneClass α] [NormMulClass α]

/-- `norm` as a `MonoidWithZeroHom`. -/
@[simps]
/-
**normHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normHom : α ->*₀ Real where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm` as a `MonoidWithZeroHom`.
-/
def normHom : α →*₀ ℝ where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

/-- `nnnorm` as a `MonoidWithZeroHom`. -/
@[simps]
/-
**nnnormHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nnnormHom : α ->*₀ Real>=0 where toFun
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nnnorm` as a `MonoidWithZeroHom`.
-/
def nnnormHom : α →*₀ ℝ≥0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
/-
**norm_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
/-
**nnnorm_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n
/-
**enorm_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass 
α] (a : α) (n : ℕ), ‖a ^ n‖ₑ = ‖a‖ₑ ^ n
参数：a : α；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma enorm_pow (a : α) (n : ℕ) : ‖a ^ n‖ₑ = ‖a‖ₑ ^ n := by simp [enorm]
/-
**List.norm_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass 
α] (l : List α),   ‖l.prod‖ = (List.map norm l).prod
参数：l : List α；List.map norm l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
protected theorem List.norm_prod (l : List α) : ‖l.prod‖ = (l.map norm).prod :=
  map_list_prod (normHom.toMonoidHom : α →* ℝ) _
/-
**List.nnnorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] [NormMulClass 
α] (l : List α),   ‖l.prod‖₊ = (List.map nnnorm l).prod
参数：l : List α；List.map nnnorm l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
protected theorem List.nnnorm_prod (l : List α) : ‖l.prod‖₊ = (l.map nnnorm).prod :=
  map_list_prod (nnnormHom.toMonoidHom : α →* ℝ≥0) _

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing α] [NormMulClass α] [NormOneClass α]

@[simp]
/-
**norm_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖ = ∏ b ∈ s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
/-
**nnnorm_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f 
b‖₊
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖₊ = ∏ b ∈ s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end SeminormedCommRing

section NormedAddCommGroup
variable [NormedAddCommGroup α] [MulOneClass α] [NormMulClass α] [Nontrivial α]

/-- Deduce `NormOneClass` from `NormMulClass` under a suitable nontriviality hypothesis. Not
an instance, in order to avoid loops with `NormOneClass.nontrivial`. -/
/-
**NormMulClass.toNormOneClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NormMulClass.toNormOneClass : NormOneClass α where norm_one
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_eq_left₀`：mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a != 0) : a * 
b = a ↔ b = 1
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

--- 原说明 ---
Deduce `NormOneClass` from `NormMulClass` under a suitable nontriviality hypothe
sis. Not
an instance, in order to avoid loops with `NormOneClass.nontrivial`.
-/
lemma NormMulClass.toNormOneClass : NormOneClass α where
  norm_one := by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

end NormedAddCommGroup

section NormedRing
variable [NormedRing α] [NormMulClass α]

/-
**NormMulClass.isAbsoluteValue_norm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormMulClass.isAbsoluteValue_norm : IsAbsoluteValue (norm : α -> Real) whe
re abv_nonneg'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
instance NormMulClass.isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul
/-
**NormMulClass.toNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormMulClass.toNoZeroDivisors : NoZeroDivisors α where eq_zero_or_eq_zero_
of_mul_eq_zero h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
instance NormMulClass.toNoZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    simpa only [← norm_eq_zero (E := α), norm_mul, mul_eq_zero] using h

end NormedRing

end NormMulClass

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

/-- A non-unital ring homomorphism from a `NonUnitalRing` to a `NonUnitalSeminormedRing`
induces a `NonUnitalSeminormedRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NonUnitalSeminormedRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing
 S] [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism from a `NonUnitalRing` to a `NonUnitalSeminormedR
ing`
induces a `NonUnitalSeminormedRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R := fast_instance%
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul_le x y := show ‖f _‖ ≤ _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `NonUnitalRing` to a
`NonUnitalNormedRing` induces a `NonUnitalNormedRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NonUnitalNormedRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S] [Non
UnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedR
ing R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `NonUnitalRing` to a
`NonUnitalNormedRing` induces a `NonUnitalNormedRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) :
    NonUnitalNormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/-- A non-unital ring homomorphism from a `Ring` to a `SeminormedRing` induces a
`SeminormedRing` structure on the domain.

See note [reducible non-instances] -/
/-
**SeminormedRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass 
F R S] (f : F) : SeminormedRing R
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism from a `Ring` to a `SeminormedRing` induces a
`SeminormedRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

/-- An injective non-unital ring homomorphism from a `Ring` to a `NormedRing` induces a
`NormedRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NormedRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (
f : F) (hf : Function.Injective f) : NormedRing R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `Ring` to a `NormedRing` induce
s a
`NormedRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

/-- A non-unital ring homomorphism from a `NonUnitalCommRing` to a `NonUnitalSeminormedCommRing`
induces a `NonUnitalSeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NonUnitalSeminormedCommRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSemino
rmedCommRing S] [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommR
ing R
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism from a `NonUnitalCommRing` to a `NonUnitalSeminor
medCommRing`
induces a `NonUnitalSeminormedCommRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

/-- An injective non-unital ring homomorphism from a `NonUnitalCommRing` to a
`NonUnitalNormedCommRing` induces a `NonUnitalNormedCommRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NonUnitalNormedCommRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedComm
Ring S] [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonU
nitalNormedCommRing R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `NonUnitalCommRing` to a
`NonUnitalNormedCommRing` induces a `NonUnitalNormedCommRing` structure on the d
omain.

See note [reducible non-instances]
-/
abbrev NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) :
    NonUnitalNormedCommRing R := fast_instance%
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }
/-- A non-unital ring homomorphism from a `CommRing` to a `SeminormedRing` induces a
`SeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
/-
**SeminormedCommRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingH
omClass F R S] (f : F) : SeminormedCommRing R
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism from a `CommRing` to a `SeminormedRing` induces a
`SeminormedCommRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

/-- An injective non-unital ring homomorphism from a `CommRing` to a `NormedRing` induces a
`NormedCommRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NormedCommRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass 
F R S] (f : F) (hf : Function.Injective f) : NormedCommRing R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `CommRing` to a `NormedRing` in
duces a
`NormedCommRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R := fast_instance%
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
/-
**NormOneClass.induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
 [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) : @NormOneClass R
 (SeminormedRing.induced R S f).toNorm _
参数：R S : Type*；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1

--- 原说明 ---
A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the no
rm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ =
 1`.
-/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
/-
**NormMulClass.induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormMulClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
 [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (f : F) : @NormMulClass R
 (SeminormedRing.induced R S f).toNorm _
参数：R S : Type*；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

--- 原说明 ---
A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the no
rm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ =
 1`.
-/
theorem NormMulClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormMulClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

/-
**SubringClass.toSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : Seminorme
dRing s
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : SeminormedRing s :=
  fast_instance% SeminormedRing.induced s R (SubringClass.subtype s)
/-
**SubringClass.toNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  fast_instance% NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective
/-
**SubringClass.toSeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toSeminormedCommRing [SeminormedCommRing R] [_h : SubringClass S R] (s : S
) : SeminormedCommRing s
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toSeminormedCommRing [SeminormedCommRing R] [_h : SubringClass S R] (s : S) :
    SeminormedCommRing s :=
  fast_instance% SeminormedCommRing.induced s R (SubringClass.subtype s)
/-
**SubringClass.toNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCom
mRing s
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  fast_instance% NormedCommRing.induced s R (SubringClass.subtype s) Subtype.val_injective
/-
**SubringClass.toNormOneClass** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toNormOneClass [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s :
 S) : NormOneClass s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormOneClass.induced`：NormOneClass.induced {F : Type*} (R S : Type*) [Ri
ng R] [SeminormedRing S] [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (
f : F) : @…
-/
instance toNormOneClass [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s : S) :
    NormOneClass s :=
  .induced s R <| SubringClass.subtype _
/-
**SubringClass.toNormMulClass** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
形式化陈述：toNormMulClass [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s :
 S) : NormMulClass s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormMulClass.induced`：NormMulClass.induced {F : Type*} (R S : Type*) [Ri
ng R] [SeminormedRing S] [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (
f : F) : @…
-/
instance toNormMulClass [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s : S) :
    NormMulClass s :=
  .induced s R <| SubringClass.subtype _

end SubringClass

namespace AbsoluteValue

/-- A real absolute value on a ring determines a `NormedRing` structure. -/
@[instance_reducible]
/-
**AbsoluteValue.toNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R Real) : NormedRing 
R where norm
参数：v : AbsoluteValue R Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real absolute value on a ring determines a `NormedRing` structure.
-/
noncomputable def toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing R where
  norm := v
  dist x y := v (-x + y)
  dist_eq _ _ := rfl
  dist_self x := by simp
  dist_comm x y := by rw [add_comm (-x), add_comm (-y), ← sub_eq_add_neg, v.map_sub, sub_eq_add_neg]
  dist_triangle x y z := by simpa [neg_add_eq_sub, add_comm (v (y - x))] using v.sub_le z y x
  edist_dist x y := rfl
  norm_mul_le x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [add_comm, ← sub_eq_add_neg, AbsoluteValue.map_sub_eq_zero_iff] at hxy
    exact hxy.symm

end AbsoluteValue

namespace Real

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section mul

variable {R ι ι' : Type*} [Semiring R] [Finite ι] [Finite ι']

/-
**Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg {F : Type*} [FunLike F R Real] [No
nnegHomClass F R Real] [MulHomClass F R Real] (v : F) (x : ι -> R) (y : ι' -> R)
 : ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j)
参数：v : F；x : ι -> R；y : ι' -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iSup_mul_of_nonneg`：Real.iSup_mul_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (⨆ i, f i) * r = ⨆ i, f i * r
· 使用引理 `Real.iSup_nonneg`：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.mul_iSup_of_nonneg`：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨆ i, r * f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finite.ciSup_prod`：ciSup_prod (f : ι × ι' -> α) : ⨆ a, f a = ⨆ i, ⨆ i', 
f (i, i')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg {F : Type*} [FunLike F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] (v : F) (x : ι → R) (y : ι' → R) :
    ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j) := by
  simp_rw [Real.iSup_mul_of_nonneg (iSup_nonneg fun i ↦ apply_nonneg v (y i)),
    Real.mul_iSup_of_nonneg (apply_nonneg v _), map_mul, Finite.ciSup_prod]

end mul

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section prod

universe u v

variable {α R : Type*} [Fintype α] {ι : α → Type u} [∀ a, Finite (ι a)]

/-
**Real.iSup_prod_eq_prod_iSup_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：iSup_prod_eq_prod_iSup_of_nonneg {f : (a : α) -> ι a -> Real} (hf₀ : foral
l a i, 0 <= f a i) : ⨆ (i : (a : α) -> ι a), ∏ a, f a (i a) = ∏ a, ⨆ i, f a i
参数：a : α；hf₀ : forall a i, 0 <= f a i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Finset.prod_eq_zero_iff`：prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a
 in s, f a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isEmpty_pi`：isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exis
ts a, IsEmpty (π a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
· 使用定理 `Classical.nonempty_pi`：Classical.nonempty_pi {ι} {α : ι -> Sort*} : None
mpty (forall i, α i) ↔ forall i, Nonempty (α i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
（共 31 条，此处仅展示前 30 条）
-/
lemma iSup_prod_eq_prod_iSup_of_nonneg {f : (a : α) → ι a → ℝ} (hf₀ : ∀ a i, 0 ≤ f a i) :
    ⨆ (i : (a : α) → ι a), ∏ a, f a (i a) = ∏ a, ⨆ i, f a i := by
  rcases isEmpty_or_nonempty ((a : α) → ι a) with h | h
  · rw [iSup_of_isEmpty, eq_comm, Finset.prod_eq_zero_iff]
    obtain ⟨a, ha⟩ := isEmpty_pi.mp h
    exact ⟨a, by simp⟩
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i ↦ Finset.prod_le_prod (by simp [hf₀])
      fun a ha ↦ Finite.le_ciSup_of_le _ le_rfl
  · rw [Classical.nonempty_pi] at h
    have H a : ∃ i : ι a, f a i = ⨆ i, f a i := exists_eq_ciSup_of_finite
    choose i hi using H
    simp only [← hi]
    exact Finite.le_ciSup_of_le i le_rfl
/-
**Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass** 是 Mathlib 中的一个引理，位于命名空间 `Real`
。
形式化陈述：iSup_prod_eq_prod_iSup_of_nonnegHomClass {F : Type*} [FunLike F R Real] [N
onnegHomClass F R Real] (v : F) {x : (a : α) -> ι a -> R} : ⨆ (i : (a : α) -> ι 
a), ∏ a, v (x a (i a)) = ∏ a, ⨆ i, v (x a i)
参数：v : F；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.iSup_prod_eq_prod_iSup_of_nonneg`：iSup_prod_eq_prod_iSup_of_nonneg 
{f : (a : α) -> ι a -> Real} (hf₀ : forall a i, 0 <= f a i) : ⨆ (i : (a : α) -> 
ι a), ∏ a, f a (i a) = ∏ a,…
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
-/
lemma iSup_prod_eq_prod_iSup_of_nonnegHomClass {F : Type*} [FunLike F R ℝ]
    [NonnegHomClass F R ℝ] (v : F) {x : (a : α) → ι a → R} :
    ⨆ (i : (a : α) → ι a), ∏ a, v (x a (i a)) = ∏ a, ⨆ i, v (x a i) :=
  Real.iSup_prod_eq_prod_iSup_of_nonneg (f := fun a i ↦ v (x a i)) (fun _ _ ↦ apply_nonneg v _)

end prod

end Real

