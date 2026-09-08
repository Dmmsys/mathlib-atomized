/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Data.ENNReal.Operations

/-!
# Scalar multiplication on `ℝ≥0∞`.

This file defines basic scalar actions on extended nonnegative reals, showing that
`MulAction`s, `DistribMulAction`s, `Module`s and `Algebra`s restrict from `ℝ≥0∞` to `ℝ≥0`.
-/

@[expose] public section

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

-- TODO: generalize some of these to `WithTop α`
section Actions

/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {M : Type*} [MulAction ℝ≥0∞ M] : SMul ℝ≥0 M :=
  ⟨fun c m ↦ (c : ℝ≥0∞) • m⟩

/-- A `MulAction` over `ℝ≥0∞` restricts to a `MulAction` over `ℝ≥0`. -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MulAction` over `ℝ≥0∞` restricts to a `MulAction` over `ℝ≥0`.
-/
noncomputable instance {M : Type*} [MulAction ℝ≥0∞ M] : MulAction ℝ≥0 M :=
  fast_instance% MulAction.compHom M ofNNRealHom.toMonoidHom
/-
**ENNReal.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>=0) (x : M) : c • x 
= (c : Real>=0∞) • x
参数：c : Real>=0；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def {M : Type*} [MulAction ℝ≥0∞ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ≥0∞) • x :=
  rfl

@[simp]
/-
**ENNReal.smul_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：smul_one (c : Real>=0) : c • (1 : Real>=0∞) = (c : Real>=0∞)
参数：c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_one (c : ℝ≥0) : c • (1 : ℝ≥0∞) = (c : ℝ≥0∞) := by simp [smul_def]
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Type*} [MulAction ℝ≥0∞ M] [MulAction ℝ≥0∞ N] [SMul M N] [IsScalarTower ℝ≥0∞ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := smul_assoc (r : ℝ≥0∞)
/-
**ENNReal.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
形式化陈述：smulCommClass_left {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulCo
mmClass Real>=0∞ M N] : SMulCommClass Real>=0 M N where smul_comm r
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_left {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass ℝ≥0∞ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := smul_comm (r : ℝ≥0∞)
/-
**ENNReal.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
形式化陈述：smulCommClass_right {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulC
ommClass M Real>=0∞ N] : SMulCommClass M Real>=0 N where smul_comm m r
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_right {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass M ℝ≥0∞ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := smul_comm m (r : ℝ≥0∞)

/-- A `DistribMulAction` over `ℝ≥0∞` restricts to a `DistribMulAction` over `ℝ≥0`. -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DistribMulAction` over `ℝ≥0∞` restricts to a `DistribMulAction` over `ℝ≥0`.
-/
noncomputable instance {M : Type*} [AddMonoid M] [DistribMulAction ℝ≥0∞ M] :
    DistribMulAction ℝ≥0 M :=
  fast_instance% DistribMulAction.compHom M ofNNRealHom.toMonoidHom

/-- A `Module` over `ℝ≥0∞` restricts to a `Module` over `ℝ≥0`. -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Module` over `ℝ≥0∞` restricts to a `Module` over `ℝ≥0`.
-/
noncomputable instance {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M] : Module ℝ≥0 M :=
  fast_instance% Module.compHom M ofNNRealHom

set_option backward.isDefEq.respectTransparency false in
/-- An `Algebra` over `ℝ≥0∞` restricts to an `Algebra` over `ℝ≥0`. -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Algebra` over `ℝ≥0∞` restricts to an `Algebra` over `ℝ≥0`.
-/
noncomputable instance {A : Type*} [Semiring A] [Algebra ℝ≥0∞ A] : Algebra ℝ≥0 A where
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ≥0∞) x, smul_def]
  algebraMap := (algebraMap ℝ≥0∞ A).comp (ofNNRealHom : ℝ≥0 →+* ℝ≥0∞)

-- verify that the above produces instances we might care about
/-
**ENNReal.** 是 Mathlib 中的一个示例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Algebra ℝ≥0 ℝ≥0∞ := inferInstance
/-
**ENNReal.** 是 Mathlib 中的一个示例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : DistribMulAction ℝ≥0ˣ ℝ≥0∞ := inferInstance
/-
**ENNReal.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_smul {R} (r : R) (s : Real>=0) [SMul R Real>=0] [SMul R Real>=0∞] [IsS
calarTower R Real>=0 Real>=0] [IsScalarTower R Real>=0 Real>=0∞] : (↑(r • s) : R
eal>=0∞) = (r : R) • (s : Real>=0∞)
参数：r : R；s : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem coe_smul {R} (r : R) (s : ℝ≥0) [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = (r : R) • (s : ℝ≥0∞) := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← ENNReal.coe_mul, smul_mul_assoc,
    one_mul]
/-
**ENNReal.smul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：smul_top {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScal
arTower R Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0∞] [DecidableEq R] (
c : R) : c • ∞ = if c = 0 then 0 else ∞
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `ENNReal.mul_top'`：mul_top' : a * ∞ = if a = 0 then 0 else ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_top {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul, mul_top']
  simp_rw [smul_eq_zero, or_iff_left one_ne_zero]
/-
**ENNReal.nnreal_smul_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：nnreal_smul_lt_top {x : Real>=0} {y : Real>=0∞} (hy : y < ⊤) : x • y < ⊤
参数：hy : y < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ := mul_lt_top (by simp) hy
/-
**ENNReal.nnreal_smul_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：nnreal_smul_ne_top {x : Real>=0} {y : Real>=0∞} (hy : y != ⊤) : x • y != ⊤
参数：hy : y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ := mul_ne_top (by simp) hy
/-
**ENNReal.nnreal_smul_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：nnreal_smul_ne_top_iff {x : Real>=0} {y : Real>=0∞} (hx : x != 0) : x • y 
!= ⊤ ↔ y != ⊤
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_top`：smul_top {R : Type*} [Semiring R] [IsDomain R] [Module
 R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0
∞] [De…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.nnreal_smul_ne_top`：nnreal_smul_ne_top {x : Real>=0} {y : Real>=
0∞} (hy : y != ⊤) : x • y != ⊤
-/
lemma nnreal_smul_ne_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y ≠ ⊤ ↔ y ≠ ⊤ :=
  ⟨by rintro h rfl; simp [smul_top (R := ℝ≥0), hx] at h, nnreal_smul_ne_top⟩
/-
**ENNReal.nnreal_smul_lt_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：nnreal_smul_lt_top_iff {x : Real>=0} {y : Real>=0∞} (hx : x != 0) : x • y 
< ⊤ ↔ y < ⊤
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `ENNReal.nnreal_smul_ne_top_iff`：nnreal_smul_ne_top_iff {x : Real>=0} {y 
: Real>=0∞} (hx : x != 0) : x • y != ⊤ ↔ y != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nnreal_smul_lt_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y < ⊤ ↔ y < ⊤ := by
  rw [lt_top_iff_ne_top, lt_top_iff_ne_top, nnreal_smul_ne_top_iff hx]

@[simp]
/-
**ENNReal.smul_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：smul_toNNReal (a : Real>=0) (b : Real>=0∞) : (a • b).toNNReal = a * b.toNN
Real
参数：a : Real>=0；b : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_toNNReal (a : ℝ≥0) (b : ℝ≥0∞) : (a • b).toNNReal = a * b.toNNReal := by
  change ((a : ℝ≥0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
/-
**ENNReal.toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_smul (r : Real>=0) (s : Real>=0∞) : (r • s).toReal = r • s.toReal
参数：r : Real>=0；s : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r
-/
theorem toReal_smul (r : ℝ≥0) (s : ℝ≥0∞) : (r • s).toReal = r • s.toReal := by
  rw [ENNReal.smul_def, smul_eq_mul, toReal_mul, coe_toReal]
  rfl
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosSMulStrictMono ℝ≥0 ℝ≥0∞ where
  smul_lt_smul_of_pos_left _r hr _a _b hab :=
    ENNReal.mul_lt_mul_right (coe_pos.2 hr).ne' coe_ne_top hab
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulPosMono ℝ≥0 ℝ≥0∞ where
  smul_le_smul_of_nonneg_right _r _ _a _b hab := _root_.mul_le_mul_left (coe_le_coe.2 hab) _
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedModule ℝ≥0 ℝ≥0∞ where
/-
**ENNReal.** 是 Mathlib 中的一个示例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CovariantClass ℝ≥0∞ ℝ≥0∞ (· • ·) (· ≤ ·) := inferInstance
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedSMul ℝ≥0 ℝ≥0∞ where
  smul_le_smul_left a b hab c := by gcongr
  smul_le_smul_right a b hab c := by gcongr
/-
**ENNReal.** 是 Mathlib 中的一个示例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : CovariantClass ℝ≥0 ℝ≥0∞ (· • ·) (· ≤ ·) := inferInstance

end Actions

end ENNReal

