/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Rays in modules

This file defines rays in modules.

## Main definitions

* `SameRay`: two vectors belong to the same ray if they are proportional with a nonnegative
  coefficient.

* `Module.Ray` is a type for the equivalence class of nonzero vectors in a module with some
  common positive multiple.
-/

@[expose] public noncomputable section

open Module

section StrictOrderedCommSemiring

-- TODO: remove `[IsStrictOrderedRing R]` and `@[nolint unusedArguments]`.
/-- Two vectors are in the same ray if either one of them is zero or some positive multiples of them
are equal (in the typical case over a field, this means one of them is a nonnegative multiple of
the other). -/
@[nolint unusedArguments]
/-
**SameRay** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SameRay (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing
 R] {M : Type*} [AddCommMonoid M] [Module R M] (v₁ v₂ : M) : Prop
参数：R : Type*；v₁ v₂ : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vectors are in the same ray if either one of them is zero or some positive m
ultiples of them
are equal (in the typical case over a field, this means one of them is a nonnega
tive multiple of
the other).
-/
def SameRay (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {M : Type*} [AddCommMonoid M] [Module R M] (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

set_option linter.unusedVariables false in
/-- Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that
`RayVector.Setoid` can be an instance. -/
@[nolint unusedArguments]
/-
**RayVector** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RayVector (R M : Type*) [Zero M]
参数：R M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonzero vectors, as used to define rays. This type depends on an unused argument
 `R` so that
`RayVector.Setoid` can be an instance.
-/
def RayVector (R M : Type*) [Zero M] :=
  { v : M // v ≠ 0 }

/-- Equivalence between `RayVector` and non-zero vectors. -/
/-
**RayVector.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RayVector.equiv (R M : Type*) [Zero M] : RayVector R M ≃ { v : M // v != 0
 }
参数：R M : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Equivalence between `RayVector` and non-zero vectors.
-/
def RayVector.equiv (R M : Type*) [Zero M] : RayVector R M ≃ { v : M // v ≠ 0 } :=
  Equiv.refl _
/-
**RayVector.coe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RayVector.coe {R M : Type*} [Zero M] : CoeOut (RayVector R M) M where coe 
x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance RayVector.coe {R M : Type*} [Zero M] : CoeOut (RayVector R M) M where
  coe x := (equiv R M x).val

@[simp]
/-
**RayVector.coe_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RayVector.coe_equiv_symm {R M : Type*} [Zero M] {v : M} (h : v != 0) : (Ra
yVector.equiv R M).symm ⟨v, h⟩ = v
参数：h : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem RayVector.coe_equiv_symm {R M : Type*} [Zero M] {v : M} (h : v ≠ 0) :
    (RayVector.equiv R M).symm ⟨v, h⟩ = v := rfl

@[ext]
/-
**RayVector.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RayVector.ext {R M : Type*} [Zero M] {x y : RayVector R M} (h : (x : M) = 
(y : M)) : x = y
参数：h : (x : M) = (y : M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem RayVector.ext {R M : Type*} [Zero M] {x y : RayVector R M} (h : (x : M) = (y : M)) :
    x = y := Subtype.ext h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Zero M] [Nontrivial M] : Nonempty (RayVector R M) :=
  ⟨Classical.indefiniteDescription _ <| exists_ne (0 : M)⟩

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι : Type*) [DecidableEq ι]

namespace SameRay

variable {x y z : M}

@[simp]
/-
**SameRay.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：zero_left (y : M) : SameRay R 0 y
参数：y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_left (y : M) : SameRay R 0 y :=
  Or.inl rfl

@[simp]
/-
**SameRay.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：zero_right (x : M) : SameRay R x 0
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_right (x : M) : SameRay R x 0 :=
  Or.inr <| Or.inl rfl

@[nontriviality]
/-
**SameRay.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y
参数：x y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
-/
theorem of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y := by
  rw [Subsingleton.elim x 0]
  exact zero_left _

@[nontriviality]
/-
**SameRay.of_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y
参数：x y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.of_subsingleton`：of_subsingleton [Subsingleton M] (x y : M) : Sa
meRay R x y
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
-/
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y :=
  haveI := Module.subsingleton R M
  of_subsingleton x y

/-- `SameRay` is reflexive. -/
@[refl]
/-
**SameRay.refl** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：refl (x : M) : SameRay R x x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
`SameRay` is reflexive.
-/
theorem refl (x : M) : SameRay R x x :=
  Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)
/-
**SameRay.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : 
_root_.Module R M] {x : M}, SameRay R x x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.refl`：refl (x : M) : SameRay R x x
-/
protected theorem rfl : SameRay R x x :=
  refl _

/-- `SameRay` is symmetric. -/
@[symm]
/-
**SameRay.symm** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：symm (h : SameRay R x y) : SameRay R y x
参数：h : SameRay R x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_left_comm`：∀ {a b c : Prop}, a ∨ b ∨ c ↔ b ∨ a ∨ c

--- 原说明 ---
`SameRay` is symmetric.
-/
theorem symm (h : SameRay R x y) : SameRay R y x :=
  (or_left_comm.1 h).imp_right <| Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩

/-- If `x` and `y` are nonzero vectors on the same ray, then there exist positive numbers `r₁ r₂`
such that `r₁ • x = r₂ • y`. -/
/-
**SameRay.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_pos (h : SameRay R x y) (hx : x != 0) (hy : y != 0) : exists r₁ r₂ 
: R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y
参数：h : SameRay R x y；hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b

--- 原说明 ---
If `x` and `y` are nonzero vectors on the same ray, then there exist positive nu
mbers `r₁ r₂`
such that `r₁ • x = r₂ • y`.
-/
theorem exists_pos (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
  (h.resolve_left hx).resolve_left hy
/-
**SameRay.sameRay_comm** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：sameRay_comm : SameRay R x y ↔ SameRay R y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
-/
theorem sameRay_comm : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩

/-- `SameRay` is transitive unless the vector in the middle is zero and both other vectors are
nonzero. -/
/-
**SameRay.trans** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 -> x = 0 ∨ z
 = 0) : SameRay R x z
参数：hxy : SameRay R x y；hyz : SameRay R y z；hy : y = 0 -> x = 0 ∨ z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `SameRay.exists_pos`：exists_pos (h : SameRay R x y) (hx : x != 0) (hy : y
 != 0) : exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…

--- 原说明 ---
`SameRay` is transitive unless the vector in the middle is zero and both other v
ectors are
nonzero.
-/
theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 → x = 0 ∨ z = 0) :
    SameRay R x z := by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, ?_⟩)
  rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]

variable {S : Type*} [CommSemiring S] [PartialOrder S]
  [Algebra S R] [Module S M] [SMulPosMono S R]
  [IsScalarTower S R M] {a : S}

/-- A vector is in the same ray as a nonnegative multiple of itself. -/
/-
**SameRay.sameRay_nonneg_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：sameRay_nonneg_smul_right (v : M) (h : 0 <= a) : SameRay R v (a • v)
参数：v : M；h : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用引理 `algebraMap_nonneg`：algebraMap_nonneg {a : α} (ha : 0 <= a) : 0 <= algebr
aMap α β a
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
A vector is in the same ray as a nonnegative multiple of itself.
-/
lemma sameRay_nonneg_smul_right (v : M) (h : 0 ≤ a) : SameRay R v (a • v) := by
  obtain h | h := (algebraMap_nonneg R h).eq_or_lt'
  · rw [← algebraMap_smul R a v, h, zero_smul]
    exact zero_right _
  · refine Or.inr <| Or.inr ⟨algebraMap S R a, 1, h, by nontriviality R; exact zero_lt_one, ?_⟩
    module

/-- A nonnegative multiple of a vector is in the same ray as that vector. -/
/-
**SameRay.sameRay_nonneg_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：sameRay_nonneg_smul_left (v : M) (ha : 0 <= a) : SameRay R (a • v) v
参数：v : M；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)

--- 原说明 ---
A nonnegative multiple of a vector is in the same ray as that vector.
-/
lemma sameRay_nonneg_smul_left (v : M) (ha : 0 ≤ a) : SameRay R (a • v) v :=
  (sameRay_nonneg_smul_right v ha).symm

/-- A vector is in the same ray as a positive multiple of itself. -/
/-
**SameRay.sameRay_pos_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：sameRay_pos_smul_right (v : M) (ha : 0 < a) : SameRay R v (a • v)
参数：v : M；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A vector is in the same ray as a positive multiple of itself.
-/
lemma sameRay_pos_smul_right (v : M) (ha : 0 < a) : SameRay R v (a • v) :=
  sameRay_nonneg_smul_right v ha.le

/-- A positive multiple of a vector is in the same ray as that vector. -/
/-
**SameRay.sameRay_pos_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：sameRay_pos_smul_left (v : M) (ha : 0 < a) : SameRay R (a • v) v
参数：v : M；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.sameRay_nonneg_smul_left`：sameRay_nonneg_smul_left (v : M) (ha :
 0 <= a) : SameRay R (a • v) v
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A positive multiple of a vector is in the same ray as that vector.
-/
lemma sameRay_pos_smul_left (v : M) (ha : 0 < a) : SameRay R (a • v) v :=
  sameRay_nonneg_smul_left v ha.le

/-- A vector is in the same ray as a nonnegative multiple of one it is in the same ray as. -/
/-
**SameRay.nonneg_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：nonneg_smul_right (h : SameRay R x y) (ha : 0 <= a) : SameRay R x (a • y)
参数：h : SameRay R x y；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.trans`：trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y
 = 0 -> x = 0 ∨ z = 0) : SameRay R x z
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
A vector is in the same ray as a nonnegative multiple of one it is in the same r
ay as.
-/
lemma nonneg_smul_right (h : SameRay R x y) (ha : 0 ≤ a) : SameRay R x (a • y) :=
  h.trans (sameRay_nonneg_smul_right y ha) fun hy => Or.inr <| by rw [hy, smul_zero]

/-- A nonnegative multiple of a vector is in the same ray as one it is in the same ray as. -/
/-
**SameRay.nonneg_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `SameRay`。
形式化陈述：nonneg_smul_left (h : SameRay R x y) (ha : 0 <= a) : SameRay R (a • x) y
参数：h : SameRay R x y；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
· 使用引理 `SameRay.nonneg_smul_right`：nonneg_smul_right (h : SameRay R x y) (ha : 0
 <= a) : SameRay R x (a • y)

--- 原说明 ---
A nonnegative multiple of a vector is in the same ray as one it is in the same r
ay as.
-/
lemma nonneg_smul_left (h : SameRay R x y) (ha : 0 ≤ a) : SameRay R (a • x) y :=
  (h.symm.nonneg_smul_right ha).symm

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
/-
**SameRay.pos_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：pos_smul_right (h : SameRay R x y) (ha : 0 < a) : SameRay R x (a • y)
参数：h : SameRay R x y；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.nonneg_smul_right`：nonneg_smul_right (h : SameRay R x y) (ha : 0
 <= a) : SameRay R x (a • y)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A vector is in the same ray as a positive multiple of one it is in the same ray 
as.
-/
theorem pos_smul_right (h : SameRay R x y) (ha : 0 < a) : SameRay R x (a • y) :=
  h.nonneg_smul_right ha.le

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
/-
**SameRay.pos_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：pos_smul_left (h : SameRay R x y) (hr : 0 < a) : SameRay R (a • x) y
参数：h : SameRay R x y；hr : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.nonneg_smul_left`：nonneg_smul_left (h : SameRay R x y) (ha : 0 <
= a) : SameRay R (a • x) y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A positive multiple of a vector is in the same ray as one it is in the same ray 
as.
-/
theorem pos_smul_left (h : SameRay R x y) (hr : 0 < a) : SameRay R (a • x) y :=
  h.nonneg_smul_left hr.le

/-- If two vectors are on the same ray then they remain so after applying a linear map. -/
/-
**SameRay.map** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：map (f : M ->ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y)
参数：f : M ->ₗ[R] N；h : SameRay R x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…

--- 原说明 ---
If two vectors are on the same ray then they remain so after applying a linear m
ap.
-/
theorem map (f : M →ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y) :=
  (h.imp fun hx => by rw [hx, map_zero]) <|
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The images of two vectors under an injective linear map are on the same ray if and only if the
original vectors are on the same ray. -/
/-
**SameRay._root_.Function.Injective.sameRay_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `S
ameRay`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The images of two vectors under an injective linear map are on the same ray if a
nd only if the
original vectors are on the same ray.
-/
theorem _root_.Function.Injective.sameRay_map_iff
    {F : Type*} [FunLike F M N] [LinearMapClass F R M N]
    {f : F} (hf : Function.Injective f) :
    SameRay R (f x) (f y) ↔ SameRay R x y := by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]

/-- The images of two vectors under a linear equivalence are on the same ray if and only if the
original vectors are on the same ray. -/
@[simp]
/-
**SameRay.sameRay_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：sameRay_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y
参数：e : M ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.sameRay_map_iff`：∀ {R : Type u_1} [inst : CommSemirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}  
 [inst_3 : AddCommMonoid…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e

--- 原说明 ---
The images of two vectors under a linear equivalence are on the same ray if and 
only if the
original vectors are on the same ray.
-/
theorem sameRay_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y :=
  Function.Injective.sameRay_map_iff (EquivLike.injective e)

/-- If two vectors are on the same ray then both scaled by the same action are also on the same
ray. -/
/-
**SameRay.smul** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] (
h : SameRay R x y) (s : S) : SameRay R (s • x) (s • y)
参数：h : SameRay R x y；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.map`：map (f : M ->ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) 
(f y)

--- 原说明 ---
If two vectors are on the same ray then both scaled by the same action are also 
on the same
ray.
-/
theorem smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
    (h : SameRay R x y) (s : S) : SameRay R (s • x) (s • y) :=
  h.map (s • (LinearMap.id : M →ₗ[R] M))

/-- If `x` and `y` are on the same ray as `z`, then so is `x + y`. -/
/-
**SameRay.add_left** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z
参数：hx : SameRay R x z；hy : SameRay R y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用定理 `SameRay.exists_pos`：exists_pos (h : SameRay R x y) (hx : x != 0) (hy : y
 != 0) : exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` and `y` are on the same ray as `z`, then so is `x + y`.
-/
theorem add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z := by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, ?_, ?_⟩)
  · positivity
  · convert! congr(ry • $Hx + rx • $Hy) using 1 <;> module

/-- If `y` and `z` are on the same ray as `x`, then so is `y + z`. -/
/-
**SameRay.add_right** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z)
参数：hy : SameRay R x y；hz : SameRay R x z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
· 使用定理 `SameRay.add_left`：add_left (hx : SameRay R x z) (hy : SameRay R y z) : S
ameRay R (x + y) z

--- 原说明 ---
If `y` and `z` are on the same ray as `x`, then so is `y + z`.
-/
theorem add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z) :=
  (hy.symm.add_left hz.symm).symm

end SameRay

variable (R M)

/-- The setoid of the `SameRay` relation for the subtype of nonzero vectors. -/
/-
**RayVector.Setoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RayVector.Setoid : Setoid (RayVector R M) where r x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid of the `SameRay` relation for the subtype of nonzero vectors.
-/
instance RayVector.Setoid : Setoid (RayVector R M) where
  r x y := SameRay R (x : M) y
  iseqv :=
    ⟨fun _ => SameRay.refl _, fun h => h.symm, by
      intro x y z hxy hyz
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
/-
**Module.Ray** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Ray
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ray (equivalence class of nonzero vectors with common positive multiples) in a
 module.
-/
def Module.Ray :=
  Quotient (RayVector.Setoid R M)

variable {R M}

/-- Equivalence of nonzero vectors, in terms of `SameRay`. -/
/-
**equiv_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equiv_iff_sameRay {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Equivalence of nonzero vectors, in terms of `SameRay`.
-/
theorem equiv_iff_sameRay {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl

variable (R)

/-- The ray given by a nonzero vector. -/
/-
**rayOfNeZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rayOfNeZero (v : M) (h : v != 0) : Module.Ray R M
参数：v : M；h : v != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The ray given by a nonzero vector.
-/
def rayOfNeZero (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦(RayVector.equiv R M).symm ⟨v, h⟩⟧

/-- An induction principle for `Module.Ray`, used as `induction x using Module.Ray.ind`. -/
/-
**Module.Ray.ind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall (v) (hv : v != 0),
 C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
参数：h : forall (v) (hv : v != 0), C (rayOfNeZero R v hv)；x : Module.Ray R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q

--- 原说明 ---
An induction principle for `Module.Ray`, used as `induction x using Module.Ray.i
nd`.
-/
theorem Module.Ray.ind {C : Module.Ray R M → Prop} (h : ∀ (v) (hv : v ≠ 0), C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotient.ind (Subtype.rec <| h) x

variable {R}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nonempty (Module.Ray R M) :=
  Nonempty.map Quotient.mk' inferInstance

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `SameRay`. -/
/-
**ray_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : rayOfNeZero R _ h
v₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
参数：hv₁ : v₁ != 0；hv₂ : v₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `SameRay`.
-/
theorem ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotient.eq'

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp]
/-
**ray_pos_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ray_pos_smul {v : M} (h : v != 0) {r : R} (hr : 0 < r) (hrv : r • v != 0) 
: rayOfNeZero R (r • v) hrv = rayOfNeZero R v h
参数：h : v != 0；hr : 0 < r；hrv : r • v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用引理 `SameRay.sameRay_pos_smul_left`：sameRay_pos_smul_left (v : M) (ha : 0 < a
) : SameRay R (a • v) v
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
The ray given by a positive multiple of a nonzero vector.
-/
theorem ray_pos_smul {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r) (hrv : r • v ≠ 0) :
    rayOfNeZero R (r • v) hrv = rayOfNeZero R v h :=
  (ray_eq_iff _ _).2 <| SameRay.sameRay_pos_smul_left v hr

/-- An equivalence between modules implies an equivalence between ray vectors. -/
/-
**RayVector.mapLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N
参数：e : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between modules implies an equivalence between ray vectors.
-/
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm

/-- An equivalence between modules implies an equivalence between rays. -/
/-
**Module.Ray.map** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N
参数：e : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between modules implies an equivalence between rays.
-/
def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  Quotient.congr (RayVector.mapLinearEquiv e) fun _ _ => (SameRay.sameRay_map_iff _).symm

@[simp]
/-
**Module.Ray.map_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v != 0) : Module.Ray.ma
p e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv)
参数：e : M ≃ₗ[R] N；v : M；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl

@[simp]
/-
**Module.Ray.map_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.ref
l _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
-/
theorem Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.refl _ :=
  Equiv.ext <| Module.Ray.ind R fun _ _ => rfl

@[simp]
/-
**Module.Ray.map_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray
.map e.symm
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl

section Action

variable {G : Type*} [Group G] [DistribMulAction G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any invertible action preserves the non-zeroness of ray vectors. This is primari
ly of interest
when `G = Rˣ`
-/
instance {R : Type*} : MulAction G (RayVector R M) where
  smul r := Subtype.map (r • ·) fun _ => (smul_ne_zero_iff_ne _).2
  mul_smul a b _ := Subtype.ext <| mul_smul a b _
  one_smul _ := Subtype.ext <| one_smul _ _

variable [SMulCommClass R G M]

/-- Any invertible action preserves the non-zeroness of rays. This is primarily of interest when
`G = Rˣ` -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any invertible action preserves the non-zeroness of rays. This is primarily of i
nterest when
`G = Rˣ`
-/
instance : MulAction G (Module.Ray R M) where
  smul r := Quotient.map (r • ·) fun _ _ h => h.smul _
  mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' <| mul_smul a b _
  one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' <| one_smul _ _

/-- The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.map`. -/
@[simp]
/-
**Module.Ray.linearEquiv_smul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Ray.linearEquiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) : 
e • v = Module.Ray.map e v
参数：e : M ≃ₗ[R] M；v : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.m
ap`.
-/
theorem Module.Ray.linearEquiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) :
    e • v = Module.Ray.map e v :=
  rfl

@[simp]
/-
**smul_rayOfNeZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_rayOfNeZero (g : G) (v : M) (hv) : g • rayOfNeZero R v hv = rayOfNeZe
ro R (g • v) ((smul_ne_zero_iff_ne _).2 hv)
参数：g : G；v : M；hv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_rayOfNeZero (g : G) (v : M) (hv) :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl

end Action

namespace Module.Ray

/-- Scaling by a positive unit is a no-op. -/
/-
**Module.Ray.units_smul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：units_smul_of_pos (u : Rˣ) (hu : 0 < (u : R)) (v : Module.Ray R M) : u • v
 = v
参数：u : Rˣ；hu : 0 < (u : R)；v : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_rayOfNeZero`：smul_rayOfNeZero (g : G) (v : M) (hv) : g • rayOfNeZer
o R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv)
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用引理 `SameRay.sameRay_pos_smul_left`：sameRay_pos_smul_left (v : M) (ha : 0 < a
) : SameRay R (a • v) v
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
Scaling by a positive unit is a no-op.
-/
theorem units_smul_of_pos (u : Rˣ) (hu : 0 < (u : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  rw [smul_rayOfNeZero, ray_eq_iff]
  exact SameRay.sameRay_pos_smul_left _ hu

/-- An arbitrary `RayVector` giving a ray. -/
/-
**Module.Ray.someRayVector** 是 Mathlib 中的一个定义，位于命名空间 `Module.Ray`。
形式化陈述：someRayVector (x : Module.Ray R M) : RayVector R M
参数：x : Module.Ray R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary `RayVector` giving a ray.
-/
def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotient.out x

/-- The ray of `someRayVector`. -/
@[simp]
/-
**Module.Ray.someRayVector_ray** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：someRayVector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R
 M) = x
参数：x : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q

--- 原说明 ---
The ray of `someRayVector`.
-/
theorem someRayVector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R M) = x :=
  Quotient.out_eq _

/-- An arbitrary nonzero vector giving a ray. -/
/-
**Module.Ray.someVector** 是 Mathlib 中的一个定义，位于命名空间 `Module.Ray`。
形式化陈述：someVector (x : Module.Ray R M) : M
参数：x : Module.Ray R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary nonzero vector giving a ray.
-/
def someVector (x : Module.Ray R M) : M :=
  x.someRayVector

/-- `someVector` is nonzero. -/
@[simp]
/-
**Module.Ray.someVector_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：someVector_ne_zero (x : Module.Ray R M) : x.someVector != 0
参数：x : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`someVector` is nonzero.
-/
theorem someVector_ne_zero (x : Module.Ray R M) : x.someVector ≠ 0 :=
  x.someRayVector.property

/-- The ray of `someVector`. -/
@[simp]
/-
**Module.Ray.someVector_ray** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：someVector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.someVector_ne_zero
 = x
参数：x : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Ray.someVector_ne_zero`：someVector_ne_zero (x : Module.Ray R M) :
 x.someVector != 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q

--- 原说明 ---
The ray of `someVector`.
-/
theorem someVector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.someVector_ne_zero = x :=
  (congr_arg _ (Subtype.coe_eta _ _) :).trans x.out_eq

end Module.Ray

end StrictOrderedCommSemiring

section StrictOrderedCommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] {x y : M}

/-- `SameRay.neg` as an `iff`. -/
@[simp]
/-
**sameRay_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`SameRay.neg` as an `iff`.
-/
theorem sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y := by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]

alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff
/-
**sameRay_neg_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameRay_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y) := by rw [← sameRay_neg_iff, neg_neg]
/-
**eq_zero_of_sameRay_neg_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_zero_of_sameRay_neg_smul_right [IsDomain R] [IsTorsionFree R M] {r : R}
 (hr : r < 0) (h : SameRay R x (r • x)) : x = 0
参数：hr : r < 0；h : SameRay R x (r • x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma eq_zero_of_sameRay_neg_smul_right [IsDomain R] [IsTorsionFree R M] {r : R} (hr : r < 0)
    (h : SameRay R x (r • x)) : x = 0 := by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
  · simpa [hr.ne] using h₀
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine h.resolve_left (ne_of_gt <| sub_pos.2 ?_)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁

/-- If a vector is in the same ray as its negation, that vector is zero. -/
/-
**eq_zero_of_sameRay_self_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_sameRay_self_neg [IsDomain R] [IsTorsionFree R M] (h : SameRay 
R x (-x)) : x = 0
参数：h : SameRay R x (-x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_zero_of_sameRay_neg_smul_right`：eq_zero_of_sameRay_neg_smul_right [Is
Domain R] [IsTorsionFree R M] {r : R} (hr : r < 0) (h : SameRay R x (r • x)) : x
 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x

--- 原说明 ---
If a vector is in the same ray as its negation, that vector is zero.
-/
theorem eq_zero_of_sameRay_self_neg [IsDomain R] [IsTorsionFree R M] (h : SameRay R x (-x)) :
    x = 0 := by
  refine eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) ?_
  rwa [neg_one_smul]

namespace RayVector

/-- Negating a nonzero vector. -/
/-
**RayVector.** 是 Mathlib 中的一个实例，位于命名空间 `RayVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negating a nonzero vector.
-/
instance {R : Type*} : Neg (RayVector R M) :=
  ⟨fun v => (equiv R M).symm ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast]
/-
**RayVector.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `RayVector`。
形式化陈述：coe_neg {R : Type*} (v : RayVector R M) : ↑(-v) = -(v : M)
参数：v : RayVector R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negating a nonzero vector commutes with coercion to the underlying module.
-/
theorem coe_neg {R : Type*} (v : RayVector R M) : ↑(-v) = -(v : M) :=
  rfl

/-- Negating a nonzero vector twice produces the original vector. -/
/-
**RayVector.** 是 Mathlib 中的一个实例，位于命名空间 `RayVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negating a nonzero vector twice produces the original vector.
-/
instance {R : Type*} : InvolutiveNeg (RayVector R M) where
  neg_neg v := by rw [RayVector.ext_iff, coe_neg, coe_neg, neg_neg]

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp]
/-
**RayVector.equiv_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `RayVector`。
形式化陈述：equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y

--- 原说明 ---
If two nonzero vectors are equivalent, so are their negations.
-/
theorem equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
  sameRay_neg_iff

end RayVector

variable (R)

/-- Negating a ray. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negating a ray.
-/
instance : Neg (Module.Ray R M) :=
  ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩

/-- The ray given by the negation of a nonzero vector. -/
@[simp]
/-
**neg_rayOfNeZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_rayOfNeZero (v : M) (h : v != 0) : -rayOfNeZero R _ h = rayOfNeZero R 
(-v) (neg_ne_zero.2 h)
参数：v : M；h : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ray given by the negation of a nonzero vector.
-/
theorem neg_rayOfNeZero (v : M) (h : v ≠ 0) :
    -rayOfNeZero R _ h = rayOfNeZero R (-v) (neg_ne_zero.2 h) :=
  rfl

namespace Module.Ray

variable {R}

/-- Negating a ray twice produces the original ray. -/
/-
**Module.Ray.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Ray`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negating a ray twice produces the original ray.
-/
instance : InvolutiveNeg (Module.Ray R M) where
  neg_neg x := by apply ind R (by simp) x
  -- Quotient.ind (fun a => congr_arg Quotient.mk' <| neg_neg _) x

/-- A ray does not equal its own negation. -/
/-
**Module.Ray.ne_neg_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：ne_neg_self [IsDomain R] [IsTorsionFree R M] (x : Module.Ray R M) : x != -
x
参数：x : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_rayOfNeZero`：neg_rayOfNeZero (v : M) (h : v != 0) : -rayOfNeZero R _
 h = rayOfNeZero R (-v) (neg_ne_zero.2 h)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_zero_of_sameRay_self_neg`：eq_zero_of_sameRay_self_neg [IsDomain R] [I
sTorsionFree R M] (h : SameRay R x (-x)) : x = 0

--- 原说明 ---
A ray does not equal its own negation.
-/
theorem ne_neg_self [IsDomain R] [IsTorsionFree R M] (x : Module.Ray R M) : x ≠ -x := by
  induction x using Module.Ray.ind with | h x hx =>
  rw [neg_rayOfNeZero, Ne, ray_eq_iff]
  exact mt eq_zero_of_sameRay_self_neg hx
/-
**Module.Ray.neg_units_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v)
参数：u : Rˣ；v : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rayOfNeZero.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : A
ddCommMonoid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v) := by
  induction v using Module.Ray.ind
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]

/-- Scaling by a negative unit is negation. -/
/-
**Module.Ray.units_smul_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：units_smul_of_neg (u : Rˣ) (hu : (u : R) < 0) (v : Module.Ray R M) : u • v
 = -v
参数：u : Rˣ；hu : (u : R) < 0；v : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Module.Ray.neg_units_smul`：neg_units_smul (u : Rˣ) (v : Module.Ray R M) 
: -u • v = -(u • v)
· 使用定理 `Module.Ray.units_smul_of_pos`：units_smul_of_pos (u : Rˣ) (hu : 0 < (u : 
R)) (v : Module.Ray R M) : u • v = v
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `Right.neg_pos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
Scaling by a negative unit is negation.
-/
theorem units_smul_of_neg (u : Rˣ) (hu : (u : R) < 0) (v : Module.Ray R M) : u • v = -v := by
  rw [← neg_inj, neg_neg, ← neg_units_smul, units_smul_of_pos]
  rwa [Units.val_neg, Right.neg_pos_iff]

@[simp]
/-
**Module.Ray.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Ray`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : I
sStrictOrderedRing R] {M : Type u_2}   {N : Type u_3} [inst_3 : AddCommGroup M] 
[inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Module
 R N] (f : M ≃ₗ[R] N) (v : Module.Ray R M), (Module.Ray.map f) (-v) = -(Module.R
ay.map f) v
参数：f : M ≃ₗ[R] N；v : Module.Ray R M；Module.Ray.map f；-v；Module.Ray.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `LinearEquiv.map_ne_zero_iff`：map_ne_zero_iff {x : M} : e x != 0 ↔ x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rayOfNeZero.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : A
ddCommMonoid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_neg (f : M ≃ₗ[R] N) (v : Module.Ray R M) : map f (-v) = -map f v := by
  induction v using Module.Ray.ind with | h g hg => simp

end Module.Ray

end StrictOrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- `SameRay` follows from membership of `MulAction.orbit` for the `Units.posSubgroup`. -/
/-
**sameRay_of_mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_of_mem_orbit {v₁ v₂ : M} (h : v₁ in MulAction.orbit (Units.posSubg
roup R) v₂) : SameRay R v₁ v₂
参数：h : v₁ in MulAction.orbit (Units.posSubgroup R) v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.sameRay_pos_smul_left`：sameRay_pos_smul_left (v : M) (ha : 0 < a
) : SameRay R (a • v) v
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
`SameRay` follows from membership of `MulAction.orbit` for the `Units.posSubgrou
p`.
-/
theorem sameRay_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ MulAction.orbit (Units.posSubgroup R) v₂) :
    SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  exact SameRay.sameRay_pos_smul_left _ hr

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp]
/-
**units_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v
参数：u : Rˣ；v : Module.Ray R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Ray.units_smul_of_pos`：units_smul_of_pos (u : Rˣ) (hu : 0 < (u : 
R)) (v : Module.Ray R M) : u • v = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a

--- 原说明 ---
Scaling by an inverse unit is the same as scaling by itself.
-/
theorem units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v :=
  have := mul_self_pos.2 u.ne_zero
  calc
    u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm <| (u⁻¹ • v).units_smul_of_pos _ (by exact this)
    _ = u • v := by rw [mul_smul, smul_inv_smul]

/-- Two scalar multiples of a common vector whose coefficients have nonnegative product
lie on a common ray. -/
/-
**sameRay_smul_smul_of_mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_smul_smul_of_mul_nonneg {v : M} {c₁ c₂ : R} (h : 0 <= c₁ * c₂) : S
ameRay R (c₁ • v) (c₂ • v)
参数：h : 0 <= c₁ * c₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_pos_iff`：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosS
trictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 
<…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Two scalar multiples of a common vector whose coefficients have nonnegative prod
uct
lie on a common ray.
-/
theorem sameRay_smul_smul_of_mul_nonneg {v : M} {c₁ c₂ : R} (h : 0 ≤ c₁ * c₂) :
    SameRay R (c₁ • v) (c₂ • v) := by
  rcases eq_or_ne c₁ 0 with hc₁ | hc₁
  · rw [hc₁, zero_smul]; exact SameRay.zero_left _
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_smul]; exact SameRay.zero_right _
  have hpos : 0 < c₁ * c₂ := h.lt_of_ne (mul_ne_zero hc₁ hc₂).symm
  rcases mul_pos_iff.mp hpos with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr ⟨c₂, c₁, h₂, h₁, by module⟩)
  · exact Or.inr (Or.inr ⟨-c₂, -c₁, neg_pos.2 h₂, neg_pos.2 h₁, by module⟩)

section

variable [IsTorsionFree R M]

@[simp]
/-
**sameRay_smul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 <= r ∨ v 
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `eq_zero_of_sameRay_neg_smul_right`：eq_zero_of_sameRay_neg_smul_right [Is
Domain R] [IsTorsionFree R M] {r : R} (hr : r < 0) (h : SameRay R x (r • x)) : x
 = 0
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sameRay_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 ≤ r ∨ v = 0 :=
  ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
/-
**sameRay_smul_right_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_smul_right_iff_of_ne {v : M} (hv : v != 0) {r : R} (hr : r != 0) :
 SameRay R v (r • v) ↔ 0 < r
参数：hv : v != 0；hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ne.le_iff_lt`：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A nonzero vector is in the same ray as a multiple of itself if and only if that 
multiple
is positive.
-/
theorem sameRay_smul_right_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R v (r • v) ↔ 0 < r := by
  simp only [sameRay_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]

@[simp]
/-
**sameRay_smul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 <= r ∨ v =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `sameRay_smul_right_iff`：sameRay_smul_right_iff {v : M} {r : R} : SameRay
 R v (r • v) ↔ 0 <= r ∨ v = 0
-/
theorem sameRay_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 ≤ r ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_smul_right_iff

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
/-
**sameRay_smul_left_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_smul_left_iff_of_ne {v : M} (hv : v != 0) {r : R} (hr : r != 0) : 
SameRay R (r • v) v ↔ 0 < r
参数：hv : v != 0；hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `sameRay_smul_right_iff_of_ne`：sameRay_smul_right_iff_of_ne {v : M} (hv :
 v != 0) {r : R} (hr : r != 0) : SameRay R v (r • v) ↔ 0 < r

--- 原说明 ---
A multiple of a nonzero vector is in the same ray as that vector if and only if 
that multiple
is positive.
-/
theorem sameRay_smul_left_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R (r • v) v ↔ 0 < r :=
  SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)

@[simp]
/-
**sameRay_neg_smul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r <=
 0 ∨ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sameRay_smul_right_iff`：sameRay_smul_right_iff {v : M} {r : R} : SameRay
 R v (r • v) ↔ 0 <= r ∨ v = 0
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameRay_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r ≤ 0 ∨ v = 0 := by
  rw [← sameRay_neg_iff, neg_neg, ← neg_smul, sameRay_smul_right_iff, neg_nonneg]
/-
**sameRay_neg_smul_right_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v != 0) (hr : r != 
0) : SameRay R (-v) (r • v) ↔ r < 0
参数：hv : v != 0；hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ne.le_iff_lt`：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameRay_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (-v) (r • v) ↔ r < 0 := by
  simp only [sameRay_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]

@[simp]
/-
**sameRay_neg_smul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r <= 
0 ∨ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `sameRay_neg_smul_right_iff`：sameRay_neg_smul_right_iff {v : M} {r : R} :
 SameRay R (-v) (r • v) ↔ r <= 0 ∨ v = 0
-/
theorem sameRay_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r ≤ 0 ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff
/-
**sameRay_neg_smul_left_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v != 0) (hr : r != 0
) : SameRay R (r • v) (-v) ↔ r < 0
参数：hv : v != 0；hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `sameRay_neg_smul_right_iff_of_ne`：sameRay_neg_smul_right_iff_of_ne {v : 
M} {r : R} (hv : v != 0) (hr : r != 0) : SameRay R (-v) (r • v) ↔ r < 0
-/
theorem sameRay_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (r • v) (-v) ↔ r < 0 :=
  SameRay.sameRay_comm.trans <| sameRay_neg_smul_right_iff_of_ne hv hr

@[simp]
/-
**units_smul_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ 0 < (u 
: R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `sameRay_smul_left_iff_of_ne`：sameRay_smul_left_iff_of_ne {v : M} (hv : v
 != 0) {r : R} (hr : r != 0) : SameRay R (r • v) v ↔ 0 < r
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ 0 < (u : R) := by
  induction v using Module.Ray.ind with | h v hv =>
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]

@[simp]
/-
**units_smul_eq_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ u.1 < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Module.Ray.neg_units_smul`：neg_units_smul (u : Rˣ) (v : Module.Ray R M) 
: -u • v = -(u • v)
· 使用定理 `units_smul_eq_self_iff`：units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray 
R M} : u • v = v ↔ 0 < (u : R)
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ u.1 < 0 := by
  rw [← neg_inj, neg_neg, ← Module.Ray.neg_units_smul, units_smul_eq_self_iff, Units.val_neg,
    neg_pos]

/-- Two vectors are in the same ray, or the first is in the same ray as the negation of the
second, if and only if they are not linearly independent. -/
/-
**sameRay_or_sameRay_neg_iff_not_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sameRay_or_sameRay_neg_iff_not_linearIndependent {x y : M} : SameRay R x y
 ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Fin.exists_fin_two`：∀ {p : Fin 2 → Prop}, (∃ i, p i) ↔ p 0 ∨ p 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
Two vectors are in the same ray, or the first is in the same ray as the negation
 of the
second, if and only if they are not linearly independent.
-/
theorem sameRay_or_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  simp_rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
    · exact False.elim (hy hy0)
    · refine ⟨![r₁, -r₂], ?_⟩
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
    · exact False.elim (hx hx0)
    · exact False.elim (hy (neg_eq_zero.1 hy0))
    · refine ⟨![r₁, r₂], ?_⟩
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
  · rcases h with ⟨m, hm, hmne⟩
    rw [Fin.sum_univ_two, add_eq_zero_iff_eq_neg] at hm
    dsimp only [Matrix.cons_val] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm1, hx, hm0.ne] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm0, hy, hm1.ne] at hm
    · rw [Fin.exists_fin_two] at hmne
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
    · exfalso
      simp [hm0, hy, hm1.ne.symm] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      rwa [neg_smul]
    · exfalso
      simp [hm1, hx, hm0.ne.symm] at hm
    · refine Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, ?_⟩))
      rwa [smul_neg]

/-- Two vectors are in the same ray, or they are nonzero and the first is in the same ray as the
negation of the second, if and only if they are not linearly independent. -/
/-
**sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} : S
ameRay R x y ∨ x != 0 ∧ y != 0 ∧ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_or_sameRay_neg_iff_not_linearIndependent`：sameRay_or_sameRay_neg
_iff_not_linearIndependent {x y : M} : SameRay R x y ∨ SameRay R x (-y) ↔ ¬Linea
rIndependent R ![x, y]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
Two vectors are in the same ray, or they are nonzero and the first is in the sam
e ray as the
negation of the second, if and only if they are not linearly independent.
-/
theorem sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0 <;> simp [hx, hy]

end

end LinearOrderedCommRing

namespace SameRay

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y v₁ v₂ : M}

/-
**SameRay.exists_pos_left** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_pos_left (h : SameRay R x y) (hx : x != 0) (hy : y != 0) : exists r
 : R, 0 < r ∧ r • x = y
参数：h : SameRay R x y；hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_pos`：exists_pos (h : SameRay R x y) (hx : x != 0) (hy : y
 != 0) : exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem exists_pos_left (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ r • x = y :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩
/-
**SameRay.exists_pos_right** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_pos_right (h : SameRay R x y) (hx : x != 0) (hy : y != 0) : exists 
r : R, 0 < r ∧ x = r • y
参数：h : SameRay R x y；hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SameRay.exists_pos_left`：exists_pos_left (h : SameRay R x y) (hx : x != 
0) (hy : y != 0) : exists r : R, 0 < r ∧ r • x = y
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
-/
theorem exists_pos_right (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ x = r • y :=
  (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm

/-- If a vector `v₂` is on the same ray as a nonzero vector `v₁`, then it is equal to `c • v₁` for
some nonnegative `c`. -/
/-
**SameRay.exists_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_nonneg_left (h : SameRay R x y) (hx : x != 0) : exists r : R, 0 <= 
r ∧ r • x = y
参数：h : SameRay R x y；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SameRay.exists_pos_left`：exists_pos_left (h : SameRay R x y) (hx : x != 
0) (hy : y != 0) : exists r : R, 0 < r ∧ r • x = y

--- 原说明 ---
If a vector `v₂` is on the same ray as a nonzero vector `v₁`, then it is equal t
o `c • v₁` for
some nonnegative `c`.
-/
theorem exists_nonneg_left (h : SameRay R x y) (hx : x ≠ 0) : ∃ r : R, 0 ≤ r ∧ r • x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt

/-- If a vector `v₁` is on the same ray as a nonzero vector `v₂`, then it is equal to `c • v₂` for
some nonnegative `c`. -/
/-
**SameRay.exists_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_nonneg_right (h : SameRay R x y) (hy : y != 0) : exists r : R, 0 <=
 r ∧ x = r • y
参数：h : SameRay R x y；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SameRay.exists_nonneg_left`：exists_nonneg_left (h : SameRay R x y) (hx :
 x != 0) : exists r : R, 0 <= r ∧ r • x = y
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x

--- 原说明 ---
If a vector `v₁` is on the same ray as a nonzero vector `v₂`, then it is equal t
o `c • v₂` for
some nonnegative `c`.
-/
theorem exists_nonneg_right (h : SameRay R x y) (hy : y ≠ 0) : ∃ r : R, 0 ≤ r ∧ x = r • y :=
  (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm

/-- If vectors `v₁` and `v₂` are on the same ray, then for some nonnegative `a b`, `a + b = 1`, we
have `v₁ = a • (v₁ + v₂)` and `v₂ = b • (v₁ + v₂)`. -/
/-
**SameRay.exists_eq_smul_add** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_eq_smul_add (h : SameRay R v₁ v₂) : exists a b : R, 0 <= a ∧ 0 <= b
 ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂)
参数：h : SameRay R v₁ v₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If vectors `v₁` and `v₂` are on the same ray, then for some nonnegative `a b`, `
a + b = 1`, we
have `v₁ = a • (v₁ + v₂)` and `v₂ = b • (v₁ + v₂)`.
-/
theorem exists_eq_smul_add (h : SameRay R v₁ v₂) :
    ∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) := by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
  · use 1, 0
    simp
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, ?_, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']

/-- If vectors `v₁` and `v₂` are on the same ray, then they are nonnegative multiples of the same
vector. Actually, this vector can be assumed to be `v₁ + v₂`, see `SameRay.exists_eq_smul_add`. -/
/-
**SameRay.exists_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `SameRay`。
形式化陈述：exists_eq_smul (h : SameRay R v₁ v₂) : exists (u : M) (a b : R), 0 <= a ∧ 
0 <= b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u
参数：h : SameRay R v₁ v₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_eq_smul_add`：exists_eq_smul_add (h : SameRay R v₁ v₂) : e
xists a b : R, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ +
 v₂)

--- 原说明 ---
If vectors `v₁` and `v₂` are on the same ray, then they are nonnegative multiple
s of the same
vector. Actually, this vector can be assumed to be `v₁ + v₂`, see `SameRay.exist
s_eq_smul_add`.
-/
theorem exists_eq_smul (h : SameRay R v₁ v₂) :
    ∃ (u : M) (a b : R), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
  ⟨v₁ + v₂, h.exists_eq_smul_add⟩

end SameRay

section LinearOrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y : M}

/-
**exists_pos_left_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_left_iff_sameRay (hx : x != 0) (hy : y != 0) : (exists r : R, 0
 < r ∧ r • x = y) ↔ SameRay R x y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.sameRay_pos_smul_right`：sameRay_pos_smul_right (v : M) (ha : 0 <
 a) : SameRay R v (a • v)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `SameRay.exists_pos_left`：exists_pos_left (h : SameRay R x y) (hx : x != 
0) (hy : y != 0) : exists r : R, 0 < r ∧ r • x = y
-/
theorem exists_pos_left_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_pos_left hx hy⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_pos_smul_right x hr
/-
**exists_pos_left_iff_sameRay_and_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_left_iff_sameRay_and_ne_zero (hx : x != 0) : (exists r : R, 0 <
 r ∧ r • x = y) ↔ SameRay R x y ∧ y != 0
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_pos_left_iff_sameRay`：exists_pos_left_iff_sameRay (hx : x != 0) (
hy : y != 0) : (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y
-/
theorem exists_pos_left_iff_sameRay_and_ne_zero (hx : x ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y ≠ 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hx, hr.le, hr.ne']
  · rintro ⟨hxy, hy⟩
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy
/-
**exists_nonneg_left_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nonneg_left_iff_sameRay (hx : x != 0) : (exists r : R, 0 <= r ∧ r •
 x = y) ↔ SameRay R x y
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SameRay.sameRay_nonneg_smul_right`：sameRay_nonneg_smul_right (v : M) (h 
: 0 <= a) : SameRay R v (a • v)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `SameRay.exists_nonneg_left`：exists_nonneg_left (h : SameRay R x y) (hx :
 x != 0) : exists r : R, 0 <= r ∧ r • x = y
-/
theorem exists_nonneg_left_iff_sameRay (hx : x ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_nonneg_left hx⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_nonneg_smul_right x hr
/-
**exists_pos_right_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_right_iff_sameRay (hx : x != 0) (hy : y != 0) : (exists r : R, 
0 < r ∧ x = r • y) ↔ SameRay R x y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `exists_pos_left_iff_sameRay`：exists_pos_left_iff_sameRay (hx : x != 0) (
hy : y != 0) : (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y
-/
theorem exists_pos_right_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay hy hx
/-
**exists_pos_right_iff_sameRay_and_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_right_iff_sameRay_and_ne_zero (hy : y != 0) : (exists r : R, 0 
< r ∧ x = r • y) ↔ SameRay R x y ∧ x != 0
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `exists_pos_left_iff_sameRay_and_ne_zero`：exists_pos_left_iff_sameRay_and
_ne_zero (hx : x != 0) : (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y !
= 0
-/
theorem exists_pos_right_iff_sameRay_and_ne_zero (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y ∧ x ≠ 0 := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay_and_ne_zero hy
/-
**exists_nonneg_right_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nonneg_right_iff_sameRay (hy : y != 0) : (exists r : R, 0 <= r ∧ x 
= r • y) ↔ SameRay R x y
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `exists_nonneg_left_iff_sameRay`：exists_nonneg_left_iff_sameRay (hx : x !
= 0) : (exists r : R, 0 <= r ∧ r • x = y) ↔ SameRay R x y
-/
theorem exists_nonneg_right_iff_sameRay (hy : y ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_nonneg_left_iff_sameRay (R := R) hy

end LinearOrderedField

