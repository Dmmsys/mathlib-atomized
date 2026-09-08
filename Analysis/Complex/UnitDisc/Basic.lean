/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Algebra.Group.NatPowAssoc
public import Mathlib.Algebra.Group.PNatPowAssoc

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

@[expose] public section

open Set Function Metric Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Complex

/-- The complex unit disc, denoted as `𝔻` within the Complex namespace -/
/-
**Complex.UnitDisc** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：UnitDisc : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex unit disc, denoted as `𝔻` within the Complex namespace
-/
def UnitDisc : Type :=
  Subsemigroup.unitBall ℂ deriving TopologicalSpace

/-- The complex closed unit disc, denoted as `𝕔𝔻` within the Complex namespace -/
/-
**Complex.UnitClosedDisc** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：UnitClosedDisc : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex closed unit disc, denoted as `𝕔𝔻` within the Complex namespace
-/
def UnitClosedDisc : Type :=
  Submonoid.unitClosedBall ℂ deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
@[inherit_doc] scoped[Complex.UnitDisc] notation "𝕔𝔻" => Complex.UnitClosedDisc

open UnitDisc

namespace UnitDisc

/-- Coercion to `ℂ`. -/
/-
**Complex.UnitDisc.coe** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
形式化陈述：Complex.UnitDisc → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to `ℂ`.
-/
@[coe] protected def coe : 𝔻 → ℂ := Subtype.val
/-
**Complex.UnitDisc.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc
`。
形式化陈述：instCommSemigroup : CommSemigroup UnitDisc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to `ℂ`.
-/
instance instCommSemigroup : CommSemigroup UnitDisc := inferInstanceAs <| CommSemigroup (ball _ _)
/-
**Complex.UnitDisc.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Complex.Unit
Disc`。
形式化陈述：instSemigroupWithZero : SemigroupWithZero UnitDisc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero : SemigroupWithZero UnitDisc :=
  inferInstanceAs <| SemigroupWithZero (ball _ _)
/-
**Complex.UnitDisc.instIsCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDi
sc`。
形式化陈述：instIsCancelMulZero : IsCancelMulZero UnitDisc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsCancelMulZero : IsCancelMulZero UnitDisc :=
  inferInstanceAs <| IsCancelMulZero (ball _ _)
/-
**Complex.UnitDisc.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc
`。
形式化陈述：instHasDistribNeg : HasDistribNeg UnitDisc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasDistribNeg : HasDistribNeg UnitDisc :=
  inferInstanceAs <| HasDistribNeg (ball _ _)
/-
**Complex.UnitDisc.instCoe** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
形式化陈述：instCoe : Coe UnitDisc Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoe : Coe UnitDisc ℂ := ⟨UnitDisc.coe⟩

@[ext]
/-
**Complex.UnitDisc.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_injective : Injective ((↑) : 𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Injective ((↑) : 𝔻 → ℂ) :=
  Subtype.coe_injective

@[simp, norm_cast]
/-
**Complex.UnitDisc.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_inj {z w : 𝔻} : (z : Complex) = w ↔ z = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
-/
theorem coe_inj {z w : 𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

@[fun_prop]
/-
**Complex.UnitDisc.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝔻 → ℂ) := .subtypeVal

@[fun_prop]
/-
**Complex.UnitDisc.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：continuous_coe : Continuous ((↑) : 𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Complex.UnitDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmbedding
 ((↑) : 𝔻 -> Complex)
-/
theorem continuous_coe : Continuous ((↑) : 𝔻 → ℂ) := isEmbedding_coe.continuous
/-
**Complex.UnitDisc.norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1
参数：z : 𝔻。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ < 1 :=
  mem_ball_zero_iff.1 z.2
/-
**Complex.UnitDisc.norm_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：norm_ne_one (z : 𝔻) : ‖(z : Complex)‖ != 1
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Complex.UnitDisc.norm_lt_one`：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1
-/
theorem norm_ne_one (z : 𝔻) : ‖(z : ℂ)‖ ≠ 1 :=
  z.norm_lt_one.ne
/-
**Complex.UnitDisc.sq_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：sq_norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ ^ 2 < 1
参数：z : 𝔻。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq_lt_one_iff_abs_lt_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : Lin
earOrder α] [IsStrictOrderedRing α] (a : α), a ^ 2 < 1 ↔ |a| < 1
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `Complex.UnitDisc.norm_lt_one`：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1
-/
theorem sq_norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_norm]
  exact z.norm_lt_one
/-
**Complex.UnitDisc.normSq_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：normSq_lt_one (z : 𝔻) : normSq z < 1
参数：z : 𝔻。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_self_eq_normSq`：norm_mul_self_eq_normSq (z : Complex) :
 ‖z‖ * ‖z‖ = normSq z
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.UnitDisc.sq_norm_lt_one`：sq_norm_lt_one (z : 𝔻) : ‖(z : Complex)
‖ ^ 2 < 1
-/
theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  rw [← Complex.norm_mul_self_eq_normSq, ← sq]
  exact z.sq_norm_lt_one
/-
**Complex.UnitDisc.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_ne_one (z : 𝔻) : (z : Complex) != 1
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Complex.UnitDisc.norm_ne_one`：norm_ne_one (z : 𝔻) : ‖(z : Complex)‖ != 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne (‖·‖) <| by simp [z.norm_ne_one]
/-
**Complex.UnitDisc.coe_ne_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_ne_neg_one (z : 𝔻) : (z : Complex) != -1
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.UnitDisc.norm_ne_one`：norm_ne_one (z : 𝔻) : ‖(z : Complex)‖ != 1
-/
theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne (‖·‖) <| by simpa [norm_neg] using z.norm_ne_one
/-
**Complex.UnitDisc.one_add_coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDi
sc`。
形式化陈述：one_add_coe_ne_zero (z : 𝔻) : (1 + z : Complex) != 0
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Complex.UnitDisc.coe_ne_neg_one`：coe_ne_neg_one (z : 𝔻) : (z : Complex) 
!= -1
-/
theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
/-
**Complex.UnitDisc.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : Complex)
参数：z w : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

@[simp, norm_cast]
/-
**Complex.UnitDisc.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_neg (z : 𝔻) : ↑(-z) = (-z : Complex)
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (z : 𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
/-
**Complex.UnitDisc.mk** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
形式化陈述：mk (z : Complex) (hz : ‖z‖ < 1) : 𝔻
参数：z : Complex；hz : ‖z‖ < 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an el
ement
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`.
-/
def mk (z : ℂ) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift ℂ 𝔻 (↑) (‖·‖ < 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
/-
**Complex.UnitDisc.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
形式化陈述：{motive : Complex.UnitDisc → Sort u_1} →   ((z : ℂ) → (hz : ‖z‖ < 1) → mot
ive (Complex.UnitDisc.mk z hz)) → (z : Complex.UnitDisc) → motive z
参数：(z : ℂ) → (hz : ‖z‖ < 1) → motive (Complex.UnitDisc.mk z hz)；z : Complex.Unit
Disc。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.UnitDisc.norm_lt_one`：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1

--- 原说明 ---
A cases eliminator that makes `cases z` use `UnitDisc.mk` instead of `Subtype.mk
`.
-/
protected def casesOn {motive : 𝔻 → Sort*} (mk : ∀ z hz, motive (.mk z hz)) (z : 𝔻) :
    motive z :=
  mk z z.norm_lt_one

@[simp]
/-
**Complex.UnitDisc.casesOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：casesOn_mk {motive : 𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {z
 : Complex} (hz : ‖z‖ < 1) : (mk z hz).casesOn mk' = mk' z hz
参数：mk' : forall z hz, motive (.mk z hz)；hz : ‖z‖ < 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem casesOn_mk {motive : 𝔻 → Sort*} (mk' : ∀ z hz, motive (.mk z hz)) {z : ℂ} (hz : ‖z‖ < 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

@[simp]
/-
**Complex.UnitDisc.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_mk (z : Complex) (hz : ‖z‖ < 1) : (mk z hz : Complex) = z
参数：z : Complex；hz : ‖z‖ < 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (z : ℂ) (hz : ‖z‖ < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
/-
**Complex.UnitDisc.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：mk_coe (z : 𝔻) (hz : ‖(z : Complex)‖ < 1
参数：z : 𝔻。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.eta`：∀ {α : Sort u} {p : α → Prop} (a : { x // p x }) (h : p ↑a)
, ⟨↑a, h⟩ = a
-/
theorem mk_coe (z : 𝔻) (hz : ‖(z : ℂ)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
/-
**Complex.UnitDisc.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：mk_inj {z w : Complex} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : mk z hz = mk w hw ↔
 z = w
参数：hz : ‖z‖ < 1；hw : ‖w‖ < 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem mk_inj {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : 𝔻 → Prop} : (∀ z, p z) ↔ ∀ z hz, p (mk z hz) :=
  ⟨fun h z hz ↦ h (mk z hz), fun h z ↦ h z z.norm_lt_one⟩
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : 𝔻 → Prop} : (∃ z, p z) ↔ ∃ z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ ↦ ⟨mk z hz, h⟩⟩

@[simp]
/-
**Complex.UnitDisc.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：mk_neg (z : Complex) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz
)
参数：z : Complex；hz : ‖-z‖ < 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_neg (z : ℂ) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
/-
**Complex.UnitDisc.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_zero : ((0 : 𝔻) : Complex) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

@[simp]
/-
**Complex.UnitDisc.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_eq_zero {z : 𝔻} : (z : Complex) = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Complex.UnitDisc.coe_injective`：coe_injective : Injective ((↑) : 𝔻 -> Co
mplex)
· 使用定理 `Complex.UnitDisc.coe_zero`：coe_zero : ((0 : 𝔻) : Complex) = 0
-/
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero
/-
**Complex.UnitDisc.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：Complex.UnitDisc.mk 0 Complex.UnitDisc.mk_zero._proof_1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl
/-
**Complex.UnitDisc.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ {z : ℂ} (hz : ‖z‖ < 1), Complex.UnitDisc.mk z hz = 0 ↔ z = 0
参数：hz : ‖z‖ < 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ < 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited 𝔻 :=
  ⟨0⟩
/-
**Complex.UnitDisc.instMulActionCircle** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDi
sc`。
形式化陈述：instMulActionCircle : MulAction Circle 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionCircle : MulAction Circle 𝔻 :=
  inferInstanceAs <| MulAction (sphere _ _) (ball _ _)
/-
**Complex.UnitDisc.instIsScalarTower_circle_circle** 是 Mathlib 中的一个实例，位于命名空间 `Co
mplex.UnitDisc`。
形式化陈述：instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (sphere _ _) (ball _ _)
/-
**Complex.UnitDisc.instIsScalarTower_circle** 是 Mathlib 中的一个实例，位于命名空间 `Complex.U
nitDisc`。
形式化陈述：instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (ball _ _) (ball _ _)
/-
**Complex.UnitDisc.instSMulCommClass_circle_left** 是 Mathlib 中的一个实例，位于命名空间 `Comp
lex.UnitDisc`。
形式化陈述：instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻 :=
  inferInstanceAs <| SMulCommClass (sphere _ _) (ball _ _) (ball _ _)
/-
**Complex.UnitDisc.instSMulCommClass_circle_right** 是 Mathlib 中的一个实例，位于命名空间 `Com
plex.UnitDisc`。
形式化陈述：instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
/-
**Complex.UnitDisc.coe_circle_smul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : Complex)
参数：z : Circle；w : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_circle := coe_circle_smul
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow UnitDisc ℕ+ where
  pow z n := ⟨z ^ (n : ℕ), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

@[simp, norm_cast]
/-
**Complex.UnitDisc.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：coe_pow (z : 𝔻) (n : Nat+) : ((z ^ n : 𝔻) : Complex) = z ^ (n : Nat)
参数：z : 𝔻；n : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (z : 𝔻) (n : ℕ+) : ((z ^ n : 𝔻) : ℂ) = z ^ (n : ℕ) := rfl

@[fun_prop]
/-
**Complex.UnitDisc.continuous_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：continuous_pow (n : Nat+) : Continuous (· ^ n : 𝔻 -> 𝔻)
参数：n : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `Complex.UnitDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmbedding
 ((↑) : 𝔻 -> Complex)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Complex.UnitDisc.continuous_coe`：continuous_coe : Continuous ((↑) : 𝔻 ->
 Complex)
-/
theorem continuous_pow (n : ℕ+) : Continuous (· ^ n : 𝔻 → 𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

@[simp]
/-
**Complex.UnitDisc.pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：pow_eq_zero {z : 𝔻} {n : Nat+} : z ^ n = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.UnitDisc.coe_inj`：coe_inj {z w : 𝔻} : (z : Complex) = w ↔ z = w
· 使用定理 `Complex.UnitDisc.coe_pow`：coe_pow (z : 𝔻) (n : Nat+) : ((z ^ n : 𝔻) : Co
mplex) = z ^ (n : Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pow_eq_zero {z : 𝔻} {n : ℕ+} : z ^ n = 0 ↔ z = 0 := by
  rw [← coe_inj, coe_pow]
  simp
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PNatPowAssoc 𝔻 where
  ppow_add m n z := mod_cast pow_add (z : ℂ) m n
  ppow_one z := by simp [← coe_inj]
/-
**Complex.UnitDisc.tendsto_pow_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x.UnitDisc`。
形式化陈述：tendsto_pow_atTop_nhds_zero (z : 𝔻) : Tendsto (fun n : Nat+ => z ^ n) atTo
p (𝓝 0)
参数：z : 𝔻。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `Complex.UnitDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmbedding
 ((↑) : 𝔻 -> Complex)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one`：tendsto_pow_atTop_nhds_zero
_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R] {x : R} : Tends
to (fun n : Nat => x ^ n) atTop (…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.UnitDisc.norm_lt_one`：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1
· 使用引理 `tendsto_PNat_val_atTop_atTop`：tendsto_PNat_val_atTop_atTop : Tendsto PNa
t.val atTop atTop
-/
theorem tendsto_pow_atTop_nhds_zero (z : 𝔻) :
    Tendsto (fun n : ℕ+ ↦ z ^ n) atTop (𝓝 0) := by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
    |>.comp tendsto_PNat_val_atTop_atTop

/-- Real part of a point of the unit disc. -/
/-
**Complex.UnitDisc.re** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
形式化陈述：re (z : 𝔻) : Real
参数：z : 𝔻。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real part of a point of the unit disc.
-/
def re (z : 𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
/-
**Complex.UnitDisc.im** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
形式化陈述：im (z : 𝔻) : Real
参数：z : 𝔻。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Imaginary part of a point of the unit disc.
-/
def im (z : 𝔻) : ℝ :=
  Complex.im z

@[simp, norm_cast]
/-
**Complex.UnitDisc.re_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：re_coe (z : 𝔻) : (z : Complex).re = z.re
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
/-
**Complex.UnitDisc.im_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：im_coe (z : 𝔻) : (z : Complex).im = z.im
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
/-
**Complex.UnitDisc.re_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：re_neg (z : 𝔻) : (-z).re = -z.re
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
/-
**Complex.UnitDisc.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：im_neg (z : 𝔻) : (-z).im = -z.im
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl
/-
**Complex.UnitDisc.re_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：Complex.UnitDisc.re 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/-
**Complex.UnitDisc.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：Complex.UnitDisc.im 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/-- Conjugate point of the unit disc. -/
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugate point of the unit disc.
-/
instance : Star 𝔻 where
  star z := mk (conj z) <| (norm_conj z).symm ▸ z.norm_lt_one

/-- Conjugate point of the unit disc. Deprecated, use `star` instead. -/
@[deprecated star (since := "2026-01-06")]
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugate point of the unit disc. Deprecated, use `star` instead.
-/
protected def «conj» (z : 𝔻) := star z
/-
**Complex.UnitDisc.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ (z : Complex.UnitDisc), ↑(star z) = (starRingEnd ℂ) ↑z
参数：z : Complex.UnitDisc；star z；starRingEnd ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_star (z : 𝔻) : (↑(star z) : ℂ) = conj ↑z := rfl

@[deprecated (since := "2026-01-06")]
alias coe_conj := coe_star

@[simp]
/-
**Complex.UnitDisc.star_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ {z : Complex.UnitDisc}, star z = 0 ↔ z = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem star_eq_zero {z : 𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

@[simp]
/-
**Complex.UnitDisc.star_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：star 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem star_zero : star (0 : 𝔻) = 0 := by simp
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar 𝔻 where
  star_involutive z := by ext; simp

@[deprecated star_star (since := "2026-01-06")]
/-
**Complex.UnitDisc.conj_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：conj_conj (z : 𝔻) : star (star z) = z
参数：z : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem conj_conj (z : 𝔻) : star (star z) = z := star_star z
/-
**Complex.UnitDisc.star_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ (z : Complex.UnitDisc), star (-z) = -star z
参数：z : Complex.UnitDisc；-z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem star_neg (z : 𝔻) : star (-z) = -(star z) := rfl

@[deprecated (since := "2026-01-06")]
alias conj_neg := UnitDisc.star_neg
/-
**Complex.UnitDisc.re_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ (z : Complex.UnitDisc), (star z).re = z.re
参数：z : Complex.UnitDisc；star z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem re_star (z : 𝔻) : (star z).re = z.re := rfl

@[deprecated (since := "2026-01-06")]
alias re_conj := UnitDisc.re_star
/-
**Complex.UnitDisc.im_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：∀ (z : Complex.UnitDisc), (star z).im = -z.im
参数：z : Complex.UnitDisc；star z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem im_star (z : 𝔻) : (star z).im = -z.im := rfl

@[deprecated (since := "2026-01-06")] alias im_conj := UnitDisc.im_star
/-
**Complex.UnitDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul 𝔻 where
  star_mul z w := coe_injective <| by simp [mul_comm]

@[deprecated star_mul' (since := "2026-01-06")]
/-
**Complex.UnitDisc.conj_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitDisc`。
形式化陈述：conj_mul (z w : 𝔻) : star (z * w) = star z * star w
参数：z w : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y
-/
theorem conj_mul (z w : 𝔻) : star (z * w) = star z * star w :=
  star_mul' z w

end UnitDisc

namespace UnitClosedDisc

/-- Coercion to `ℂ`. -/
/-
**Complex.UnitClosedDisc.coe** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：Complex.UnitClosedDisc → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to `ℂ`.
-/
@[coe] protected def coe : 𝕔𝔻 → ℂ := Subtype.val
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to `ℂ`.
-/
instance : MonoidWithZero 𝕔𝔻 := inferInstanceAs <| MonoidWithZero (closedBall _ _)
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCancelMulZero 𝕔𝔻 :=
  inferInstanceAs <| IsCancelMulZero (closedBall _ _)
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg 𝕔𝔻 :=
  inferInstanceAs <| HasDistribNeg (closedBall _ _)
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe 𝕔𝔻 ℂ := ⟨UnitClosedDisc.coe⟩

@[ext]
/-
**Complex.UnitClosedDisc.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitCl
osedDisc`。
形式化陈述：coe_injective : Injective ((↑) : 𝕔𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Injective ((↑) : 𝕔𝔻 → ℂ) :=
  Subtype.coe_injective

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：coe_inj {z w : 𝕔𝔻} : (z : Complex) = w ↔ z = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
-/
theorem coe_inj {z w : 𝕔𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

@[fun_prop]
/-
**Complex.UnitClosedDisc.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.Unit
ClosedDisc`。
形式化陈述：isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝕔𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝕔𝔻 → ℂ) := .subtypeVal

@[fun_prop]
/-
**Complex.UnitClosedDisc.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitC
losedDisc`。
形式化陈述：continuous_coe : Continuous ((↑) : 𝕔𝔻 -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Complex.UnitClosedDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmb
edding ((↑) : 𝕔𝔻 -> Complex)
-/
theorem continuous_coe : Continuous ((↑) : 𝕔𝔻 → ℂ) := isEmbedding_coe.continuous
/-
**Complex.UnitClosedDisc.norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClos
edDisc`。
形式化陈述：norm_le_one (z : 𝕔𝔻) : ‖(z : Complex)‖ <= 1
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem norm_le_one (z : 𝕔𝔻) : ‖(z : ℂ)‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 z.2
/-
**Complex.UnitClosedDisc.sq_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitC
losedDisc`。
形式化陈述：sq_norm_lt_one (z : 𝕔𝔻) : ‖(z : Complex)‖ ^ 2 <= 1
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq_le_one_iff_abs_le_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : Lin
earOrder α] [IsStrictOrderedRing α] (a : α), a ^ 2 ≤ 1 ↔ |a| ≤ 1
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `Complex.UnitClosedDisc.norm_le_one`：norm_le_one (z : 𝕔𝔻) : ‖(z : Complex
)‖ <= 1
-/
theorem sq_norm_lt_one (z : 𝕔𝔻) : ‖(z : ℂ)‖ ^ 2 ≤ 1 := by
  rw [sq_le_one_iff_abs_le_one, abs_norm]
  exact z.norm_le_one
/-
**Complex.UnitClosedDisc.normSq_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitCl
osedDisc`。
形式化陈述：normSq_lt_one (z : 𝕔𝔻) : normSq z <= 1
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_self_eq_normSq`：norm_mul_self_eq_normSq (z : Complex) :
 ‖z‖ * ‖z‖ = normSq z
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.UnitClosedDisc.sq_norm_lt_one`：sq_norm_lt_one (z : 𝕔𝔻) : ‖(z : C
omplex)‖ ^ 2 <= 1
-/
theorem normSq_lt_one (z : 𝕔𝔻) : normSq z ≤ 1 := by
  rw [← Complex.norm_mul_self_eq_normSq, ← sq]
  exact z.sq_norm_lt_one

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：coe_mul (z w : 𝕔𝔻) : ↑(z * w) = (z * w : Complex)
参数：z w : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (z w : 𝕔𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：coe_neg (z : 𝕔𝔻) : ↑(-z) = (-z : Complex)
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (z : 𝕔𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝕔𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
/-
**Complex.UnitClosedDisc.mk** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：mk (z : Complex) (hz : ‖z‖ <= 1) : 𝕔𝔻
参数：z : Complex；hz : ‖z‖ <= 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an el
ement
of `𝕔𝔻` instead of `↥Metric.ball (0 : ℂ) 1`.
-/
def mk (z : ℂ) (hz : ‖z‖ ≤ 1) : 𝕔𝔻 :=
  ⟨z, mem_closedBall_zero_iff.2 hz⟩
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift ℂ 𝕔𝔻 (↑) (‖·‖ ≤ 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitClosedDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
/-
**Complex.UnitClosedDisc.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：{motive : Complex.UnitClosedDisc → Sort u_1} →   ((z : ℂ) → (hz : ‖z‖ ≤ 1)
 → motive (Complex.UnitClosedDisc.mk z hz)) → (z : Complex.UnitClosedDisc) → mot
ive z
参数：(z : ℂ) → (hz : ‖z‖ ≤ 1) → motive (Complex.UnitClosedDisc.mk z hz)；z : Comple
x.UnitClosedDisc。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.UnitClosedDisc.norm_le_one`：norm_le_one (z : 𝕔𝔻) : ‖(z : Complex
)‖ <= 1

--- 原说明 ---
A cases eliminator that makes `cases z` use `UnitClosedDisc.mk` instead of `Subt
ype.mk`.
-/
protected def casesOn {motive : 𝕔𝔻 → Sort*} (mk : ∀ z hz, motive (.mk z hz)) (z : 𝕔𝔻) :
    motive z :=
  mk z z.norm_le_one

@[simp]
/-
**Complex.UnitClosedDisc.casesOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClose
dDisc`。
形式化陈述：casesOn_mk {motive : 𝕔𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {
z : Complex} (hz : ‖z‖ <= 1) : (mk z hz).casesOn mk' = mk' z hz
参数：mk' : forall z hz, motive (.mk z hz)；hz : ‖z‖ <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem casesOn_mk {motive : 𝕔𝔻 → Sort*} (mk' : ∀ z hz, motive (.mk z hz)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：coe_mk (z : Complex) (hz : ‖z‖ <= 1) : (mk z hz : Complex) = z
参数：z : Complex；hz : ‖z‖ <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (z : ℂ) (hz : ‖z‖ ≤ 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：mk_coe (z : 𝕔𝔻) (hz : ‖(z : Complex)‖ <= 1
参数：z : 𝕔𝔻。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.eta`：∀ {α : Sort u} {p : α → Prop} (a : { x // p x }) (h : p ↑a)
, ⟨↑a, h⟩ = a
-/
theorem mk_coe (z : 𝕔𝔻) (hz : ‖(z : ℂ)‖ ≤ 1 := z.norm_le_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
/-
**Complex.UnitClosedDisc.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：mk_inj {z w : Complex} (hz : ‖z‖ <= 1) (hw : ‖w‖ <= 1) : mk z hz = mk w hw
 ↔ z = w
参数：hz : ‖z‖ <= 1；hw : ‖w‖ <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem mk_inj {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : 𝕔𝔻 → Prop} : (∀ z, p z) ↔ ∀ z hz, p (mk z hz) :=
  ⟨fun h z hz ↦ h (mk z hz), fun h z ↦ h z z.norm_le_one⟩
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : 𝕔𝔻 → Prop} : (∃ z, p z) ↔ ∃ z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ ↦ ⟨z, z.norm_le_one, hz⟩, fun ⟨z, hz, h⟩ ↦ ⟨mk z hz, h⟩⟩

@[simp]
/-
**Complex.UnitClosedDisc.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：mk_neg (z : Complex) (hz : ‖-z‖ <= 1) : mk (-z) hz = -mk z (norm_neg z ▸ h
z)
参数：z : Complex；hz : ‖-z‖ <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_neg (z : ℂ) (hz : ‖-z‖ ≤ 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedD
isc`。
形式化陈述：coe_zero : ((0 : 𝕔𝔻) : Complex) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : 𝕔𝔻) : ℂ) = 0 :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClos
edDisc`。
形式化陈述：coe_eq_zero {z : 𝕔𝔻} : (z : Complex) = 0 ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Complex.UnitClosedDisc.coe_injective`：coe_injective : Injective ((↑) : 𝕔
𝔻 -> Complex)
· 使用定理 `Complex.UnitClosedDisc.coe_zero`：coe_zero : ((0 : 𝕔𝔻) : Complex) = 0
-/
theorem coe_eq_zero {z : 𝕔𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero
/-
**Complex.UnitClosedDisc.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：Complex.UnitClosedDisc.mk 0 Complex.UnitClosedDisc.mk_zero._proof_1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl
/-
**Complex.UnitClosedDisc.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClose
dDisc`。
形式化陈述：∀ {z : ℂ} (hz : ‖z‖ ≤ 1), Complex.UnitClosedDisc.mk z hz = 0 ↔ z = 0
参数：hz : ‖z‖ ≤ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ ≤ 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

@[simp]
/-
**Complex.UnitClosedDisc.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：coe_one : ((1 : 𝕔𝔻) : Complex) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : 𝕔𝔻) : ℂ) = 1 :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClose
dDisc`。
形式化陈述：coe_eq_one {z : 𝕔𝔻} : (z : Complex) = 1 ↔ z = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Complex.UnitClosedDisc.coe_injective`：coe_injective : Injective ((↑) : 𝕔
𝔻 -> Complex)
· 使用定理 `Complex.UnitClosedDisc.coe_one`：coe_one : ((1 : 𝕔𝔻) : Complex) = 1
-/
theorem coe_eq_one {z : 𝕔𝔻} : (z : ℂ) = 1 ↔ z = 1 :=
  coe_injective.eq_iff' coe_one
/-
**Complex.UnitClosedDisc.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：Complex.UnitClosedDisc.mk 1 Complex.UnitClosedDisc.mk_one._proof_1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_one : mk 1 (by simp) = 1 := rfl
/-
**Complex.UnitClosedDisc.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosed
Disc`。
形式化陈述：∀ {z : ℂ} (hz : ‖z‖ ≤ 1), Complex.UnitClosedDisc.mk z hz = 1 ↔ z = 1
参数：hz : ‖z‖ ≤ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mk_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) : mk z hz = 1 ↔ z = 1 := by simp [← coe_inj]
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited 𝕔𝔻 :=
  ⟨0⟩
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction Circle 𝕔𝔻 :=
  inferInstanceAs <| MulAction (sphere _ _) (closedBall _ _)
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower Circle Circle 𝕔𝔻 :=
  inferInstanceAs <| IsScalarTower (sphere _ _) (sphere _ _) (closedBall _ _)
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower Circle 𝕔𝔻 𝕔𝔻 :=
  isScalarTower_sphere_closedBall_closedBall
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass Circle 𝕔𝔻 𝕔𝔻 :=
  instSMulCommClass_sphere_closedBall_closedBall
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _
/-
**Complex.UnitClosedDisc.instMulActionClosedBall** 是 Mathlib 中的一个实例，位于命名空间 `Comp
lex.UnitClosedDisc`。
形式化陈述：instMulActionClosedBall : MulAction 𝕔𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionClosedBall : MulAction 𝕔𝔻 𝔻 :=
  inferInstanceAs <| MulAction (closedBall _ _) (ball _ _)
/-
**Complex.UnitClosedDisc.instIsScalarTower_closedBall_closedBall** 是 Mathlib 中的一
个实例，位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：instIsScalarTower_closedBall_closedBall : IsScalarTower 𝕔𝔻 𝕔𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_closedBall_closedBall :
    IsScalarTower 𝕔𝔻 𝕔𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (closedBall _ _) (closedBall _ _) (ball _ _)
/-
**Complex.UnitClosedDisc.instIsScalarTower_closedBall** 是 Mathlib 中的一个实例，位于命名空间 
`Complex.UnitClosedDisc`。
形式化陈述：instIsScalarTower_closedBall : IsScalarTower 𝕔𝔻 𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_closedBall : IsScalarTower 𝕔𝔻 𝔻 𝔻 :=
  inferInstanceAs <| IsScalarTower (closedBall _ _) (ball _ _) (ball _ _)
/-
**Complex.UnitClosedDisc.instSMulCommClass_closedBall_left** 是 Mathlib 中的一个实例，位于
命名空间 `Complex.UnitClosedDisc`。
形式化陈述：instSMulCommClass_closedBall_left : SMulCommClass 𝕔𝔻 𝔻 𝔻
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
instance instSMulCommClass_closedBall_left : SMulCommClass 𝕔𝔻 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩
/-
**Complex.UnitClosedDisc.instSMulCommClass_closedBall_right** 是 Mathlib 中的一个实例，位
于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：instSMulCommClass_closedBall_right : SMulCommClass 𝔻 𝕔𝔻 𝔻
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass_closedBall_right : SMulCommClass 𝔻 𝕔𝔻 𝔻 :=
  SMulCommClass.symm _ _ _
/-
**Complex.UnitClosedDisc.instSMulCommClass_circle_closedBall** 是 Mathlib 中的一个实例，
位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：instSMulCommClass_circle_closedBall : SMulCommClass Circle 𝕔𝔻 𝔻
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass_circle_closedBall : SMulCommClass Circle 𝕔𝔻 𝔻 :=
  inferInstanceAs <| SMulCommClass (sphere _ _) (closedBall _ _) (ball _ _)
/-
**Complex.UnitClosedDisc.instSMulCommClass_closedBall_circle** 是 Mathlib 中的一个实例，
位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：instSMulCommClass_closedBall_circle : SMulCommClass 𝕔𝔻 Circle 𝔻
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass_closedBall_circle : SMulCommClass 𝕔𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_closedBall_smul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.
UnitClosedDisc`。
形式化陈述：coe_closedBall_smul (z : 𝕔𝔻) (w : 𝔻) : ↑(z • w) = (z * w : Complex)
参数：z : 𝕔𝔻；w : 𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_closedBall_smul (z : 𝕔𝔻) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_closedBall := coe_closedBall_smul

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_circle_smul** 是 Mathlib 中的一个定理，位于命名空间 `Complex.Unit
ClosedDisc`。
形式化陈述：coe_circle_smul (z : Circle) (w : 𝕔𝔻) : ↑(z • w) = (z * w : Complex)
参数：z : Circle；w : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_circle_smul (z : Circle) (w : 𝕔𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow 𝕔𝔻 ℕ where
  pow z n := ⟨z ^ n, by simp [pow_le_one₀ (norm_nonneg _) z.norm_le_one]⟩

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：coe_pow (z : 𝕔𝔻) (n : Nat) : ((z ^ n : 𝕔𝔻) : Complex) = z ^ (n : Nat)
参数：z : 𝕔𝔻；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (z : 𝕔𝔻) (n : ℕ) : ((z ^ n : 𝕔𝔻) : ℂ) = z ^ (n : ℕ) := rfl

@[fun_prop]
/-
**Complex.UnitClosedDisc.continuous_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitC
losedDisc`。
形式化陈述：continuous_pow (n : Nat) : Continuous (· ^ n : 𝕔𝔻 -> 𝕔𝔻)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `Complex.UnitClosedDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmb
edding ((↑) : 𝕔𝔻 -> Complex)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Complex.UnitClosedDisc.continuous_coe`：continuous_coe : Continuous ((↑) 
: 𝕔𝔻 -> Complex)
-/
theorem continuous_pow (n : ℕ) : Continuous (· ^ n : 𝕔𝔻 → 𝕔𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatPowAssoc 𝕔𝔻 where
  npow_add m n z := mod_cast pow_add (z : ℂ) m n
  npow_one z := by simp [← coe_inj]
  npow_zero z := by simp [← coe_inj]

/-- Real part of a point of the unit disc. -/
/-
**Complex.UnitClosedDisc.re** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：re (z : 𝕔𝔻) : Real
参数：z : 𝕔𝔻。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real part of a point of the unit disc.
-/
def re (z : 𝕔𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
/-
**Complex.UnitClosedDisc.im** 是 Mathlib 中的一个定义，位于命名空间 `Complex.UnitClosedDisc`。
形式化陈述：im (z : 𝕔𝔻) : Real
参数：z : 𝕔𝔻。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Imaginary part of a point of the unit disc.
-/
def im (z : 𝕔𝔻) : ℝ :=
  Complex.im z

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.re_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：re_coe (z : 𝕔𝔻) : (z : Complex).re = z.re
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_coe (z : 𝕔𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
/-
**Complex.UnitClosedDisc.im_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：im_coe (z : 𝕔𝔻) : (z : Complex).im = z.im
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_coe (z : 𝕔𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.re_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：re_neg (z : 𝕔𝔻) : (-z).re = -z.re
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_neg (z : 𝕔𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
/-
**Complex.UnitClosedDisc.im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDis
c`。
形式化陈述：im_neg (z : 𝕔𝔻) : (-z).im = -z.im
参数：z : 𝕔𝔻。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem im_neg (z : 𝕔𝔻) : (-z).im = -z.im :=
  rfl
/-
**Complex.UnitClosedDisc.re_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：Complex.UnitClosedDisc.re 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/-
**Complex.UnitClosedDisc.im_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：Complex.UnitClosedDisc.im 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/-- Conjugate point of the unit disc. -/
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugate point of the unit disc.
-/
instance : Star 𝕔𝔻 where
  star z := mk (conj z) <| (norm_conj z).symm ▸ z.norm_le_one
/-
**Complex.UnitClosedDisc.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedD
isc`。
形式化陈述：∀ (z : Complex.UnitClosedDisc), ↑(star z) = (starRingEnd ℂ) ↑z
参数：z : Complex.UnitClosedDisc；star z；starRingEnd ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_star (z : 𝕔𝔻) : (↑(star z) : ℂ) = conj ↑z := rfl

@[simp]
/-
**Complex.UnitClosedDisc.star_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClo
sedDisc`。
形式化陈述：∀ {z : Complex.UnitClosedDisc}, star z = 0 ↔ z = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem star_eq_zero {z : 𝕔𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

@[simp]
/-
**Complex.UnitClosedDisc.star_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosed
Disc`。
形式化陈述：star 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem star_zero : star (0 : 𝕔𝔻) = 0 := by simp
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar 𝕔𝔻 where
  star_involutive z := by ext; simp
/-
**Complex.UnitClosedDisc.star_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedD
isc`。
形式化陈述：∀ (z : Complex.UnitClosedDisc), star (-z) = -star z
参数：z : Complex.UnitClosedDisc；-z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem star_neg (z : 𝕔𝔻) : star (-z) = -(star z) := rfl
/-
**Complex.UnitClosedDisc.re_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：∀ (z : Complex.UnitClosedDisc), (star z).re = z.re
参数：z : Complex.UnitClosedDisc；star z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem re_star (z : 𝕔𝔻) : (star z).re = z.re := rfl
/-
**Complex.UnitClosedDisc.im_star** 是 Mathlib 中的一个定理，位于命名空间 `Complex.UnitClosedDi
sc`。
形式化陈述：∀ (z : Complex.UnitClosedDisc), (star z).im = -z.im
参数：z : Complex.UnitClosedDisc；star z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem im_star (z : 𝕔𝔻) : (star z).im = -z.im := rfl
/-
**Complex.UnitClosedDisc.** 是 Mathlib 中的一个实例，位于命名空间 `Complex.UnitClosedDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul 𝕔𝔻 where
  star_mul z w := coe_injective <| by simp [mul_comm]

end UnitClosedDisc

end Complex

