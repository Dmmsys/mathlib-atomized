/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.NNReal.Star

/-! # `ℝ` and `ℝ≥0` are \*-ordered rings. -/

public section

open scoped NNReal

/-- Although the instance `RCLike.toStarOrderedRing` exists, it is locked behind the
`ComplexOrder` scope because currently the order on `ℂ` is not enabled globally. But we
want `StarOrderedRing ℝ` to be available globally, so we include this instance separately.
In addition, providing this instance here makes it available earlier in the import
hierarchy; otherwise in order to access it we would need to import
`Mathlib/Analysis/RCLike/Basic.lean`. -/
/-
**Real.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instStarOrderedRing : StarOrderedRing Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `StarOrderedRing.of_nonneg_iff'`：of_nonneg_iff' [NonUnitalRing R] [Partia
lOrder R] [StarRing R] (h_add : forall {x y : R}, x <= y -> forall z, z + x <= z
 + y) (h_nonneg_iff …
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Although the instance `RCLike.toStarOrderedRing` exists, it is locked behind the
`ComplexOrder` scope because currently the order on `ℂ` is not enabled globally.
 But we
want `StarOrderedRing ℝ` to be available globally, so we include this instance s
eparately.
In addition, providing this instance here makes it available earlier in the impo
rt
hierarchy; otherwise in order to access it we would need to import
`Mathlib/Analysis/RCLike/Basic.lean`.
-/
instance Real.instStarOrderedRing : StarOrderedRing ℝ :=
  StarOrderedRing.of_nonneg_iff' add_le_add_right fun r => by
    refine ⟨fun hr => ⟨√r, (mul_self_sqrt hr).symm⟩, ?_⟩
    rintro ⟨s, rfl⟩
    exact mul_self_nonneg s
/-
**NNReal.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNReal.instStarOrderedRing : StarOrderedRing Real>=0
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `StarOrderedRing.of_le_iff`：of_le_iff (h_le_iff : forall x y : R, x <= y 
↔ exists s, y = x + star s * s) : StarOrderedRing R where le_iff x y
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarNNReal`：TrivialStar NNReal
· 使用定理 `NNReal.mul_self_sqrt`：∀ (x : NNReal), NNReal.sqrt x * NNReal.sqrt x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
instance NNReal.instStarOrderedRing : StarOrderedRing ℝ≥0 := by
  refine .of_le_iff fun x y ↦ ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    refine ⟨sqrt d, ?_⟩
    simp only [star_trivial, mul_self_sqrt]
  · rintro ⟨p, -, rfl⟩
    exact le_self_add

-- for lack of a better place with the necessary imports, we place this here
-- this exists only to satisfy the trivial instances of this class
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [AddGroup R] [Lattice R] [AddLeftMono R] [Star R] :
    SelfAdjointDecompose R where
  exists_nonneg_sub_nonneg {a} _ :=
    ⟨a⁺, a⁻, posPart_nonneg a, negPart_nonneg a, by simp⟩
