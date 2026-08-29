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

/--
Definition of `UnitDisc` / `UnitDisc` 的定义

English:
definition UnitDisc
  signature: : Type
  body: Subsemigroup.unitBall Complex deriving TopologicalSpace

中文:
定义 UnitDisc
  签名: : 类型
  定义体: Subsemigroup.unitBall Complex deriving TopologicalSpace

Depends on / 依赖: Subsemigroup, Subsemigroup.unitBall, TopologicalSpace, deriving, unitBall
-/
def UnitDisc : Type :=
  Subsemigroup.unitBall Complex deriving TopologicalSpace

/--
Definition of `UnitClosedDisc` / `UnitClosedDisc` 的定义

English:
definition UnitClosedDisc
  signature: : Type
  body: Submonoid.unitClosedBall Complex deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
@[inherit_doc] scoped[Complex.UnitDisc] notation "𝕔𝔻" => Complex.UnitClosedDisc

中文:
定义 UnitClosedDisc
  签名: : 类型
  定义体: Submonoid.unitClosedBall Complex deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
@[inherit_doc] scoped[Complex.UnitDisc] notation "𝕔𝔻" => Complex.UnitClosedDisc

Depends on / 依赖: Submonoid, Submonoid.unitClosedBall, TopologicalSpace, deriving, unitClosedBall
-/
def UnitClosedDisc : Type :=
  Submonoid.unitClosedBall Complex deriving TopologicalSpace

@[inherit_doc] scoped[Complex.UnitDisc] notation "𝔻" => Complex.UnitDisc
@[inherit_doc] scoped[Complex.UnitDisc] notation "𝕔𝔻" => Complex.UnitClosedDisc

open UnitDisc

namespace UnitDisc

/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: : 𝔻 -> Complex
  body: Subtype.val

中文:
定义 coe
  签名: : 𝔻 -> 复形
  定义体: Subtype.val
-/
@[coe] protected def coe : 𝔻 -> Complex := Subtype.val

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: : CommSemigroup UnitDisc
  body: inferInstanceAs CommSemigroup (ball _ _)

中文:
实例 instCommSemigroup
  签名: : 交换半群 UnitDisc
  定义体: inferInstanceAs CommSemigroup (ball _ _)

Depends on / 依赖: CommSemigroup
-/
instance instCommSemigroup : CommSemigroup UnitDisc := inferInstanceAs CommSemigroup (ball _ _)

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: : SemigroupWithZero UnitDisc
  body: inferInstanceAs SemigroupWithZero (ball _ _)

中文:
实例 instSemigroupWithZero
  签名: : 带零半群 UnitDisc
  定义体: inferInstanceAs SemigroupWithZero (ball _ _)

Depends on / 依赖: SemigroupWithZero
-/
instance instSemigroupWithZero : SemigroupWithZero UnitDisc :=
inferInstanceAs SemigroupWithZero (ball _ _)

/--
Instance `instIsCancelMulZero` / 实例 `instIsCancelMulZero`

English:
instance instIsCancelMulZero
  signature: : IsCancelMulZero UnitDisc
  body: inferInstanceAs IsCancelMulZero (ball _ _)

中文:
实例 instIsCancelMulZero
  签名: : 是乘零消去 UnitDisc
  定义体: inferInstanceAs IsCancelMulZero (ball _ _)

Depends on / 依赖: IsCancelMulZero
-/
instance instIsCancelMulZero : IsCancelMulZero UnitDisc :=
inferInstanceAs IsCancelMulZero (ball _ _)

/--
Instance `instHasDistribNeg` / 实例 `instHasDistribNeg`

English:
instance instHasDistribNeg
  signature: : HasDistribNeg UnitDisc
  body: inferInstanceAs HasDistribNeg (ball _ _)

中文:
实例 instHasDistribNeg
  签名: : 有DistribNeg UnitDisc
  定义体: inferInstanceAs HasDistribNeg (ball _ _)

Depends on / 依赖: HasDistribNeg
-/
instance instHasDistribNeg : HasDistribNeg UnitDisc :=
inferInstanceAs HasDistribNeg (ball _ _)

/--
Instance `instCoe` / 实例 `instCoe`

English:
instance instCoe
  signature: : Coe UnitDisc Complex
  body: ⟨UnitDisc.coe⟩

@[ext]

中文:
实例 instCoe
  签名: : Coe UnitDisc 复形
  定义体: ⟨UnitDisc.coe⟩

@[ext]

Depends on / 依赖: UnitDisc, UnitDisc.coe
-/
instance instCoe : Coe UnitDisc Complex := ⟨UnitDisc.coe⟩

@[ext]
/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : 𝔻 -> Complex)
  proof: Subtype.coe_injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : 𝔻 -> 复形)
  证明: Subtype.coe_injective

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : 𝔻 -> Complex) :=
  Subtype.coe_injective

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {z w : 𝔻}
  statement: (z : Complex) = w ↔ z = w
  proof: Subtype.val_inj

@[fun_prop]

中文:
定理 coe_inj
  条件: {z w : 𝔻}
  结论: (z : 复形) = w ↔ z = w
  证明: Subtype.val_inj

@[fun_prop]

Depends on / 依赖: Subtype, Subtype.val_inj, val_inj
-/
theorem coe_inj {z w : 𝔻} : (z : Complex) = w ↔ z = w := Subtype.val_inj

@[fun_prop]
/--
theorem `isEmbedding_coe` / 定理 `isEmbedding_coe`

English:
theorem isEmbedding_coe
  statement: Topology.IsEmbedding ((↑) : 𝔻 -> Complex)
  proof: .subtypeVal

@[fun_prop]

中文:
定理 isEmbedding_coe
  结论: 拓扑.是嵌入 ((↑) : 𝔻 -> 复形)
  证明: .subtypeVal

@[fun_prop]

Depends on / 依赖: subtypeVal
-/
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝔻 -> Complex) := .subtypeVal

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : 𝔻 -> Complex)
  proof: isEmbedding_coe.continuous

中文:
定理 continuous_coe
  结论: 连续 ((↑) : 𝔻 -> 复形)
  证明: isEmbedding_coe.continuous

Depends on / 依赖: continuous, isEmbedding_coe, isEmbedding_coe.continuous
-/
theorem continuous_coe : Continuous ((↑) : 𝔻 -> Complex) := isEmbedding_coe.continuous

/--
theorem `norm_lt_one` / 定理 `norm_lt_one`

English:
theorem norm_lt_one
  given: (z : 𝔻)
  statement: ‖(z : Complex)‖ < 1
  proof: mem_ball_zero_iff.1 z.2

中文:
定理 norm_lt_one
  条件: (z : 𝔻)
  结论: ‖(z : 复形)‖ < 1
  证明: mem_ball_zero_iff.1 z.2

Depends on / 依赖: mem_ball_zero_iff
-/
theorem norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1 :=
  mem_ball_zero_iff.1 z.2

/--
theorem `norm_ne_one` / 定理 `norm_ne_one`

English:
theorem norm_ne_one
  given: (z : 𝔻)
  statement: ‖(z : Complex)‖ != 1
  proof: z.norm_lt_one.ne

中文:
定理 norm_ne_one
  条件: (z : 𝔻)
  结论: ‖(z : 复形)‖ != 1
  证明: z.norm_lt_one.ne

Depends on / 依赖: norm_lt_one, z.norm_lt_one.ne
-/
theorem norm_ne_one (z : 𝔻) : ‖(z : Complex)‖ != 1 :=
  z.norm_lt_one.ne

/--
theorem `sq_norm_lt_one` / 定理 `sq_norm_lt_one`

English:
theorem sq_norm_lt_one
  given: (z : 𝔻)
  statement: ‖(z : Complex)‖ ^ 2 < 1
  proof: by
  rw [sq_lt_one_iff_abs_lt_one]; rw [abs_norm]
  exact z.norm_lt_one

中文:
定理 sq_norm_lt_one
  条件: (z : 𝔻)
  结论: ‖(z : 复形)‖ ^ 2 < 1
  证明: by
  rw [sq_lt_one_iff_abs_lt_one]; rw [abs_norm]
  exact z.norm_lt_one

Depends on / 依赖: abs_norm, norm_lt_one, sq_lt_one_iff_abs_lt_one, z.norm_lt_one
-/
theorem sq_norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one]; rw [abs_norm]
  exact z.norm_lt_one

/--
theorem `normSq_lt_one` / 定理 `normSq_lt_one`

English:
theorem normSq_lt_one
  given: (z : 𝔻)
  statement: normSq z < 1
  proof: by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

中文:
定理 normSq_lt_one
  条件: (z : 𝔻)
  结论: normSq z < 1
  证明: by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

Depends on / 依赖: Complex.norm_mul_self_eq_normSq, norm_mul_self_eq_normSq, sq_norm_lt_one, z.sq_norm_lt_one
-/
theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: (z : 𝔻)
  statement: (z : Complex) != 1
  proof: ne_of_apply_ne (‖·‖) by simp [z.norm_ne_one]

中文:
定理 coe_ne_one
  条件: (z : 𝔻)
  结论: (z : 复形) != 1
  证明: ne_of_apply_ne (‖·‖) by simp [z.norm_ne_one]

Depends on / 依赖: ne_of_apply_ne, norm_ne_one, z.norm_ne_one
-/
theorem coe_ne_one (z : 𝔻) : (z : Complex) != 1 :=
ne_of_apply_ne (‖·‖) by simp [z.norm_ne_one]

/--
theorem `coe_ne_neg_one` / 定理 `coe_ne_neg_one`

English:
theorem coe_ne_neg_one
  given: (z : 𝔻)
  statement: (z : Complex) != -1
  proof: ne_of_apply_ne (‖·‖) by simpa [norm_neg] using z.norm_ne_one

中文:
定理 coe_ne_neg_one
  条件: (z : 𝔻)
  结论: (z : 复形) != -1
  证明: ne_of_apply_ne (‖·‖) by simpa [norm_neg] using z.norm_ne_one

Depends on / 依赖: ne_of_apply_ne, norm_ne_one, norm_neg, z.norm_ne_one
-/
theorem coe_ne_neg_one (z : 𝔻) : (z : Complex) != -1 :=
ne_of_apply_ne (‖·‖) by simpa [norm_neg] using z.norm_ne_one

/--
theorem `one_add_coe_ne_zero` / 定理 `one_add_coe_ne_zero`

English:
theorem one_add_coe_ne_zero
  given: (z : 𝔻)
  statement: (1 + z : Complex) != 0
  proof: mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]

中文:
定理 one_add_coe_ne_zero
  条件: (z : 𝔻)
  结论: (1 + z : 复形) != 0
  证明: mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]

Depends on / 依赖: coe_ne_neg_one, neg_eq_iff_add_eq_zero, z.coe_ne_neg_one.symm
-/
theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : Complex) != 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (z w : 𝔻)
  statement: ↑(z * w) = (z * w : Complex)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (z w : 𝔻)
  结论: ↑(z * w) = (z * w : 复形)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : Complex) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (z : 𝔻)
  statement: ↑(-z) = (-z : Complex)
  proof: rfl

中文:
定理 coe_neg
  条件: (z : 𝔻)
  结论: ↑(-z) = (-z : 复形)
  证明: rfl
-/
theorem coe_neg (z : 𝔻) : ↑(-z) = (-z : Complex) := rfl

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (z : Complex) (hz : ‖z‖ < 1)
  body: ⟨z, mem_ball_zero_iff.2 hz⟩

中文:
定义 mk
  签名: (z : 复形) (hz : ‖z‖ < 1)
  定义体: ⟨z, mem_ball_zero_iff.2 hz⟩

Depends on / 依赖: mem_ball_zero_iff
-/
def mk (z : Complex) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift Complex 𝔻 (↑) (‖·‖ < 1)
  body: ⟨mk z hz, rfl⟩

中文:
实例 :
  签名: CanLift 复形 𝔻 (↑) (‖·‖ < 1)
  定义体: ⟨mk z hz, rfl⟩
-/
instance : CanLift Complex 𝔻 (↑) (‖·‖ < 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
/--
Definition of `casesOn` / `casesOn` 的定义

English:
definition casesOn
  signature: {motive : 𝔻 -> Sort*} (mk : forall z hz, motive (.mk z hz)) (z : 𝔻)
  body: mk z z.norm_lt_one

@[simp]

中文:
定义 casesOn
  签名: {motive : 𝔻 -> 类型层*} (mk : 对任意 z hz, motive (.mk z hz)) (z : 𝔻)
  定义体: mk z z.norm_lt_one

@[simp]
-/
protected def casesOn {motive : 𝔻 -> Sort*} (mk : forall z hz, motive (.mk z hz)) (z : 𝔻) :
    motive z :=
  mk z z.norm_lt_one

@[simp]
/--
theorem `casesOn_mk` / 定理 `casesOn_mk`

English:
theorem casesOn_mk
  given: {motive : 𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {z : Complex} (hz : ‖z‖ < 1)
  proof: rfl

@[simp]

中文:
定理 casesOn_mk
  条件: {motive : 𝔻 -> 类型层*} (mk' : 对任意 z hz, motive (.mk z hz)) {z : 复形} (hz : ‖z‖ < 1)
  证明: rfl

@[simp]
-/
theorem casesOn_mk {motive : 𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {z : Complex} (hz : ‖z‖ < 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (z : Complex) (hz : ‖z‖ < 1)
  statement: (mk z hz : Complex) = z
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (z : 复形) (hz : ‖z‖ < 1)
  结论: (mk z hz : 复形) = z
  证明: rfl

@[simp]
-/
theorem coe_mk (z : Complex) (hz : ‖z‖ < 1) : (mk z hz : Complex) = z :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (z : 𝔻) (hz : ‖(z : Complex)‖ < 1 := z.norm_lt_one)
  statement: mk z hz = z
  proof: Subtype.eta _ _

@[simp]

中文:
定理 mk_coe
  条件: (z : 𝔻) (hz : ‖(z : 复形)‖ < 1 := z.norm_lt_one)
  结论: mk z hz = z
  证明: Subtype.eta _ _

@[simp]

Depends on / 依赖: norm_lt_one, z.norm_lt_one
-/
theorem mk_coe (z : 𝔻) (hz : ‖(z : Complex)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
/--
theorem `mk_inj` / 定理 `mk_inj`

English:
theorem mk_inj
  given: {z w : Complex} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
  statement: mk z hz = mk w hw ↔ z = w
  proof: Subtype.mk_eq_mk

中文:
定理 mk_inj
  条件: {z w : 复形} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
  结论: mk z hz = mk w hw ↔ z = w
  证明: Subtype.mk_eq_mk

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk
-/
theorem mk_inj {z w : Complex} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : 𝔻 -> Prop}
  statement: (forall z, p z) ↔ forall z hz, p (mk z hz)
  proof: ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_lt_one⟩

中文:
定理 «对任意»
  条件: {p : 𝔻 -> 命题}
  结论: (对任意 z, p z) ↔ 对任意 z hz, p (mk z hz)
  证明: ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_lt_one⟩
-/
protected theorem «forall» {p : 𝔻 -> Prop} : (forall z, p z) ↔ forall z hz, p (mk z hz) :=
  ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_lt_one⟩

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : 𝔻 -> Prop}
  statement: (exists z, p z) ↔ exists z hz, p (mk z hz)
  proof: ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]

中文:
定理 «存在»
  条件: {p : 𝔻 -> 命题}
  结论: (存在 z, p z) ↔ 存在 z hz, p (mk z hz)
  证明: ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]
-/
protected theorem «exists» {p : 𝔻 -> Prop} : (exists z, p z) ↔ exists z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_lt_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]
/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: (z : Complex) (hz : ‖-z‖ < 1)
  statement: mk (-z) hz = -mk z (norm_neg z ▸ hz)
  proof: rfl

@[simp]

中文:
定理 mk_neg
  条件: (z : 复形) (hz : ‖-z‖ < 1)
  结论: mk (-z) hz = -mk z (norm_neg z ▸ hz)
  证明: rfl

@[simp]
-/
theorem mk_neg (z : Complex) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : 𝔻) : Complex) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ((0 : 𝔻) : 复形) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ((0 : 𝔻) : Complex) = 0 :=
  rfl

@[simp]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {z : 𝔻}
  statement: (z : Complex) = 0 ↔ z = 0
  proof: coe_injective.eq_iff' coe_zero

中文:
定理 coe_eq_zero
  条件: {z : 𝔻}
  结论: (z : 复形) = 0 ↔ z = 0
  证明: coe_injective.eq_iff' coe_zero

Depends on / 依赖: coe_injective, coe_injective.eq_iff, coe_zero, eq_iff
-/
theorem coe_eq_zero {z : 𝔻} : (z : Complex) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk 0 (by simp) = 0
  proof: rfl

中文:
定理 mk_zero
  结论: mk 0 (by simp) = 0
  证明: rfl
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl

/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {z : Complex} (hz : ‖z‖ < 1)
  statement: mk z hz = 0 ↔ z = 0
  proof: by simp [← coe_inj]

中文:
定理 mk_eq_zero
  条件: {z : 复形} (hz : ‖z‖ < 1)
  结论: mk z hz = 0 ↔ z = 0
  证明: by simp [← coe_inj]
-/
@[simp] theorem mk_eq_zero {z : Complex} (hz : ‖z‖ < 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited 𝔻
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 𝔻
  定义体: ⟨0⟩
-/
instance : Inhabited 𝔻 :=
  ⟨0⟩

/--
Instance `instMulActionCircle` / 实例 `instMulActionCircle`

English:
instance instMulActionCircle
  signature: : MulAction Circle 𝔻
  body: inferInstanceAs MulAction (sphere _ _) (ball _ _)

中文:
实例 instMulActionCircle
  签名: : 乘法作用 Circle 𝔻
  定义体: inferInstanceAs MulAction (sphere _ _) (ball _ _)

Depends on / 依赖: MulAction, sphere
-/
instance instMulActionCircle : MulAction Circle 𝔻 :=
inferInstanceAs MulAction (sphere _ _) (ball _ _)

/--
Instance `instIsScalarTower_circle_circle` / 实例 `instIsScalarTower_circle_circle`

English:
instance instIsScalarTower_circle_circle
  signature: : IsScalarTower Circle Circle 𝔻
  body: inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (ball _ _)

中文:
实例 instIsScalarTower_circle_circle
  签名: : 标量塔 Circle Circle 𝔻
  定义体: inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (ball _ _)

Depends on / 依赖: IsScalarTower, sphere
-/
instance instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (ball _ _)

/--
Instance `instIsScalarTower_circle` / 实例 `instIsScalarTower_circle`

English:
instance instIsScalarTower_circle
  signature: : IsScalarTower Circle 𝔻 𝔻
  body: inferInstanceAs IsScalarTower (sphere _ _) (ball _ _) (ball _ _)

中文:
实例 instIsScalarTower_circle
  签名: : 标量塔 Circle 𝔻 𝔻
  定义体: inferInstanceAs IsScalarTower (sphere _ _) (ball _ _) (ball _ _)

Depends on / 依赖: IsScalarTower, sphere
-/
instance instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
inferInstanceAs IsScalarTower (sphere _ _) (ball _ _) (ball _ _)

/--
Instance `instSMulCommClass_circle_left` / 实例 `instSMulCommClass_circle_left`

English:
instance instSMulCommClass_circle_left
  signature: : SMulCommClass Circle 𝔻 𝔻
  body: inferInstanceAs SMulCommClass (sphere _ _) (ball _ _) (ball _ _)

中文:
实例 instSMulCommClass_circle_left
  签名: : 标量交换类 Circle 𝔻 𝔻
  定义体: inferInstanceAs SMulCommClass (sphere _ _) (ball _ _) (ball _ _)

Depends on / 依赖: SMulCommClass, sphere
-/
instance instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻 :=
inferInstanceAs SMulCommClass (sphere _ _) (ball _ _) (ball _ _)

/--
Instance `instSMulCommClass_circle_right` / 实例 `instSMulCommClass_circle_right`

English:
instance instSMulCommClass_circle_right
  signature: : SMulCommClass 𝔻 Circle 𝔻
  body: SMulCommClass.symm _ _ _

@[simp, norm_cast]

中文:
实例 instSMulCommClass_circle_right
  签名: : 标量交换类 𝔻 Circle 𝔻
  定义体: SMulCommClass.symm _ _ _

@[simp, norm_cast]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
/--
theorem `coe_circle_smul` / 定理 `coe_circle_smul`

English:
theorem coe_circle_smul
  given: (z : Circle) (w : 𝔻)
  statement: ↑(z • w) = (z * w : Complex)
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_circle := coe_circle_smul

中文:
定理 coe_circle_smul
  条件: (z : Circle) (w : 𝔻)
  结论: ↑(z • w) = (z * w : 复形)
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_circle := coe_circle_smul
-/
theorem coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : Complex) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_circle := coe_circle_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow UnitDisc Nat+
  body: ⟨z ^ (n : Nat), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 UnitDisc 自然数+
  定义体: ⟨z ^ (n : Nat), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

@[simp, norm_cast]

Depends on / 依赖: norm_lt_one, pow_lt_one_iff_of_nonneg, z.norm_lt_one
-/
instance : Pow UnitDisc Nat+ where
  pow z n := ⟨z ^ (n : Nat), by simp [pow_lt_one_iff_of_nonneg, z.norm_lt_one]⟩

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (z : 𝔻) (n : Nat+)
  statement: ((z ^ n : 𝔻) : Complex) = z ^ (n : Nat)
  proof: rfl

@[fun_prop]

中文:
定理 coe_pow
  条件: (z : 𝔻) (n : 自然数+)
  结论: ((z ^ n : 𝔻) : 复形) = z ^ (n : 自然数)
  证明: rfl

@[fun_prop]
-/
theorem coe_pow (z : 𝔻) (n : Nat+) : ((z ^ n : 𝔻) : Complex) = z ^ (n : Nat) := rfl

@[fun_prop]
/--
theorem `continuous_pow` / 定理 `continuous_pow`

English:
theorem continuous_pow
  given: (n : Nat+)
  statement: Continuous (· ^ n : 𝔻 -> 𝔻)
  proof: by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

@[simp]

中文:
定理 continuous_pow
  条件: (n : 自然数+)
  结论: 连续 (· ^ n : 𝔻 -> 𝔻)
  证明: by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

@[simp]

Depends on / 依赖: Function, Function.comp_def, coe_pow, comp_def, continuous_iff, fun_prop, isEmbedding_coe, isEmbedding_coe.continuous_iff
-/
theorem continuous_pow (n : Nat+) : Continuous (· ^ n : 𝔻 -> 𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

@[simp]
/--
theorem `pow_eq_zero` / 定理 `pow_eq_zero`

English:
theorem pow_eq_zero
  given: {z : 𝔻} {n : Nat+}
  statement: z ^ n = 0 ↔ z = 0
  proof: by
  rw [← coe_inj]; rw [coe_pow]
  simp

中文:
定理 pow_eq_zero
  条件: {z : 𝔻} {n : 自然数+}
  结论: z ^ n = 0 ↔ z = 0
  证明: by
  rw [← coe_inj]; rw [coe_pow]
  simp

Depends on / 依赖: coe_inj, coe_pow
-/
theorem pow_eq_zero {z : 𝔻} {n : Nat+} : z ^ n = 0 ↔ z = 0 := by
  rw [← coe_inj]; rw [coe_pow]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PNatPowAssoc 𝔻
  body: mod_cast pow_add (z : Complex) m n
  ppow_one z := by simp [← coe_inj]

中文:
实例 :
  签名: P自然数PowAssoc 𝔻
  定义体: mod_cast pow_add (z : Complex) m n
  ppow_one z := by simp [← coe_inj]

Depends on / 依赖: mod_cast, pow_add
-/
instance : PNatPowAssoc 𝔻 where
  ppow_add m n z := mod_cast pow_add (z : Complex) m n
  ppow_one z := by simp [← coe_inj]

/--
theorem `tendsto_pow_atTop_nhds_zero` / 定理 `tendsto_pow_atTop_nhds_zero`

English:
theorem tendsto_pow_atTop_nhds_zero
  given: (z : 𝔻)
  proof: by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
.comp tendsto_PNat_val_atTop_atTop

中文:
定理 tendsto_pow_atTop_nhds_zero
  条件: (z : 𝔻)
  证明: by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
.comp tendsto_PNat_val_atTop_atTop

Depends on / 依赖: coe_pow, comp_def, isEmbedding_coe, isEmbedding_coe.tendsto_nhds_iff, norm_lt_one, tendsto_PNat_val_atTop_atTop, tendsto_nhds_iff, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr, z.norm_lt_one
-/
theorem tendsto_pow_atTop_nhds_zero (z : 𝔻) :
    Tendsto (fun n : Nat+ => z ^ n) atTop (𝓝 0) := by
  simp only [isEmbedding_coe.tendsto_nhds_iff, comp_def, coe_pow]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr z.norm_lt_one
.comp tendsto_PNat_val_atTop_atTop

/--
Definition of `re` / `re` 的定义

English:
definition re
  signature: (z : 𝔻)
  body: Complex.re z

中文:
定义 re
  签名: (z : 𝔻)
  定义体: Complex.re z

Depends on / 依赖: Complex.re
-/
def re (z : 𝔻) : Real :=
  Complex.re z

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (z : 𝔻)
  body: Complex.im z

@[simp, norm_cast]

中文:
定义 im
  签名: (z : 𝔻)
  定义体: Complex.im z

@[simp, norm_cast]

Depends on / 依赖: Complex.im
-/
def im (z : 𝔻) : Real :=
  Complex.im z

@[simp, norm_cast]
/--
theorem `re_coe` / 定理 `re_coe`

English:
theorem re_coe
  given: (z : 𝔻)
  statement: (z : Complex).re = z.re
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_coe
  条件: (z : 𝔻)
  结论: (z : 复形).re = z.re
  证明: rfl

@[simp, norm_cast]
-/
theorem re_coe (z : 𝔻) : (z : Complex).re = z.re :=
  rfl

@[simp, norm_cast]
/--
theorem `im_coe` / 定理 `im_coe`

English:
theorem im_coe
  given: (z : 𝔻)
  statement: (z : Complex).im = z.im
  proof: rfl

@[simp]

中文:
定理 im_coe
  条件: (z : 𝔻)
  结论: (z : 复形).im = z.im
  证明: rfl

@[simp]
-/
theorem im_coe (z : 𝔻) : (z : Complex).im = z.im :=
  rfl

@[simp]
/--
theorem `re_neg` / 定理 `re_neg`

English:
theorem re_neg
  given: (z : 𝔻)
  statement: (-z).re = -z.re
  proof: rfl

@[simp]

中文:
定理 re_neg
  条件: (z : 𝔻)
  结论: (-z).re = -z.re
  证明: rfl

@[simp]
-/
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  given: (z : 𝔻)
  statement: (-z).im = -z.im
  proof: rfl

中文:
定理 im_neg
  条件: (z : 𝔻)
  结论: (-z).im = -z.im
  证明: rfl
-/
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

/--
theorem `re_zero` / 定理 `re_zero`

English:
theorem re_zero
  statement: re 0 = 0
  proof: rfl

中文:
定理 re_zero
  结论: re 0 = 0
  证明: rfl
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: im 0 = 0
  proof: rfl

中文:
定理 im_zero
  结论: im 0 = 0
  证明: rfl
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star 𝔻
  body: mk (conj z) (norm_conj z).symm ▸ z.norm_lt_one

中文:
实例 :
  签名: 对合 𝔻
  定义体: mk (conj z) (norm_conj z).symm ▸ z.norm_lt_one

Depends on / 依赖: norm_conj, norm_lt_one, z.norm_lt_one
-/
instance : Star 𝔻 where
star z := mk (conj z) (norm_conj z).symm ▸ z.norm_lt_one

/-- Conjugate point of the unit disc. Deprecated, use `star` instead. -/
@[deprecated star (since := "2026-01-06")]
/--
Definition of `«conj»` / `«conj»` 的定义

English:
definition «conj»
  signature: (z : 𝔻)
  body: star z

中文:
定义 «conj»
  签名: (z : 𝔻)
  定义体: star z
-/
protected def «conj» (z : 𝔻) := star z

/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (z : 𝔻)
  statement: (↑(star z) : Complex) = conj ↑z
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias coe_conj := coe_star

@[simp]

中文:
定理 coe_star
  条件: (z : 𝔻)
  结论: (↑(star z) : 复形) = conj ↑z
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias coe_conj := coe_star

@[simp]
-/
@[simp] theorem coe_star (z : 𝔻) : (↑(star z) : Complex) = conj ↑z := rfl

@[deprecated (since := "2026-01-06")]
alias coe_conj := coe_star

@[simp]
/--
theorem `star_eq_zero` / 定理 `star_eq_zero`

English:
theorem star_eq_zero
  given: {z : 𝔻}
  statement: star z = 0 ↔ z = 0
  proof: by
  simp [← coe_eq_zero]

@[simp]

中文:
定理 star_eq_zero
  条件: {z : 𝔻}
  结论: star z = 0 ↔ z = 0
  证明: by
  simp [← coe_eq_zero]

@[simp]
-/
protected theorem star_eq_zero {z : 𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

@[simp]
/--
theorem `star_zero` / 定理 `star_zero`

English:
theorem star_zero
  statement: star (0 : 𝔻) = 0
  proof: by simp

中文:
定理 star_zero
  结论: star (0 : 𝔻) = 0
  证明: by simp
-/
protected theorem star_zero : star (0 : 𝔻) = 0 := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar 𝔻
  body: by ext; simp

@[deprecated star_star (since := "2026-01-06")]

中文:
实例 :
  签名: InvolutiveStar 𝔻
  定义体: by ext; simp

@[deprecated star_star (since := "2026-01-06")]
-/
instance : InvolutiveStar 𝔻 where
  star_involutive z := by ext; simp

@[deprecated star_star (since := "2026-01-06")]
/--
theorem `conj_conj` / 定理 `conj_conj`

English:
theorem conj_conj
  given: (z : 𝔻)
  statement: star (star z) = z
  proof: star_star z

中文:
定理 conj_conj
  条件: (z : 𝔻)
  结论: star (star z) = z
  证明: star_star z

Depends on / 依赖: star_star
-/
theorem conj_conj (z : 𝔻) : star (star z) = z := star_star z

/--
theorem `star_neg` / 定理 `star_neg`

English:
theorem star_neg
  given: (z : 𝔻)
  statement: star (-z) = -(star z)
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias conj_neg := UnitDisc.star_neg

中文:
定理 star_neg
  条件: (z : 𝔻)
  结论: star (-z) = -(star z)
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias conj_neg := UnitDisc.star_neg
-/
@[simp] protected theorem star_neg (z : 𝔻) : star (-z) = -(star z) := rfl

@[deprecated (since := "2026-01-06")]
alias conj_neg := UnitDisc.star_neg

/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  given: (z : 𝔻)
  statement: (star z).re = z.re
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias re_conj := UnitDisc.re_star

中文:
定理 re_star
  条件: (z : 𝔻)
  结论: (star z).re = z.re
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias re_conj := UnitDisc.re_star
-/
@[simp] protected theorem re_star (z : 𝔻) : (star z).re = z.re := rfl

@[deprecated (since := "2026-01-06")]
alias re_conj := UnitDisc.re_star

/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  given: (z : 𝔻)
  statement: (star z).im = -z.im
  proof: rfl

@[deprecated (since := "2026-01-06")] alias im_conj := UnitDisc.im_star

中文:
定理 im_star
  条件: (z : 𝔻)
  结论: (star z).im = -z.im
  证明: rfl

@[deprecated (since := "2026-01-06")] alias im_conj := UnitDisc.im_star
-/
@[simp] protected theorem im_star (z : 𝔻) : (star z).im = -z.im := rfl

@[deprecated (since := "2026-01-06")] alias im_conj := UnitDisc.im_star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul 𝔻
  body: coe_injective by simp [mul_comm]

@[deprecated star_mul' (since := "2026-01-06")]

中文:
实例 :
  签名: StarMul 𝔻
  定义体: coe_injective by simp [mul_comm]

@[deprecated star_mul' (since := "2026-01-06")]

Depends on / 依赖: coe_injective, mul_comm
-/
instance : StarMul 𝔻 where
star_mul z w := coe_injective by simp [mul_comm]

@[deprecated star_mul' (since := "2026-01-06")]
/--
theorem `conj_mul` / 定理 `conj_mul`

English:
theorem conj_mul
  given: (z w : 𝔻)
  statement: star (z * w) = star z * star w
  proof: star_mul' z w

中文:
定理 conj_mul
  条件: (z w : 𝔻)
  结论: star (z * w) = star z * star w
  证明: star_mul' z w

Depends on / 依赖: star_mul
-/
theorem conj_mul (z w : 𝔻) : star (z * w) = star z * star w :=
  star_mul' z w

end UnitDisc

namespace UnitClosedDisc

/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: : 𝕔𝔻 -> Complex
  body: Subtype.val

中文:
定义 coe
  签名: : 𝕔𝔻 -> 复形
  定义体: Subtype.val
-/
@[coe] protected def coe : 𝕔𝔻 -> Complex := Subtype.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero 𝕔𝔻
  body: inferInstanceAs MonoidWithZero (closedBall _ _)

中文:
实例 :
  签名: 带零幺半群 𝕔𝔻
  定义体: inferInstanceAs MonoidWithZero (closedBall _ _)

Depends on / 依赖: MonoidWithZero, closedBall
-/
instance : MonoidWithZero 𝕔𝔻 := inferInstanceAs MonoidWithZero (closedBall _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCancelMulZero 𝕔𝔻
  body: inferInstanceAs IsCancelMulZero (closedBall _ _)

中文:
实例 :
  签名: 是乘零消去 𝕔𝔻
  定义体: inferInstanceAs IsCancelMulZero (closedBall _ _)

Depends on / 依赖: IsCancelMulZero, closedBall
-/
instance : IsCancelMulZero 𝕔𝔻 :=
inferInstanceAs IsCancelMulZero (closedBall _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg 𝕔𝔻
  body: inferInstanceAs HasDistribNeg (closedBall _ _)

中文:
实例 :
  签名: 有DistribNeg 𝕔𝔻
  定义体: inferInstanceAs HasDistribNeg (closedBall _ _)

Depends on / 依赖: HasDistribNeg, closedBall
-/
instance : HasDistribNeg 𝕔𝔻 :=
inferInstanceAs HasDistribNeg (closedBall _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe 𝕔𝔻 Complex
  body: ⟨UnitClosedDisc.coe⟩

@[ext]

中文:
实例 :
  签名: Coe 𝕔𝔻 复形
  定义体: ⟨UnitClosedDisc.coe⟩

@[ext]

Depends on / 依赖: UnitClosedDisc, UnitClosedDisc.coe
-/
instance : Coe 𝕔𝔻 Complex := ⟨UnitClosedDisc.coe⟩

@[ext]
/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : 𝕔𝔻 -> Complex)
  proof: Subtype.coe_injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : 𝕔𝔻 -> 复形)
  证明: Subtype.coe_injective

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : 𝕔𝔻 -> Complex) :=
  Subtype.coe_injective

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {z w : 𝕔𝔻}
  statement: (z : Complex) = w ↔ z = w
  proof: Subtype.val_inj

@[fun_prop]

中文:
定理 coe_inj
  条件: {z w : 𝕔𝔻}
  结论: (z : 复形) = w ↔ z = w
  证明: Subtype.val_inj

@[fun_prop]

Depends on / 依赖: Subtype, Subtype.val_inj, val_inj
-/
theorem coe_inj {z w : 𝕔𝔻} : (z : Complex) = w ↔ z = w := Subtype.val_inj

@[fun_prop]
/--
theorem `isEmbedding_coe` / 定理 `isEmbedding_coe`

English:
theorem isEmbedding_coe
  statement: Topology.IsEmbedding ((↑) : 𝕔𝔻 -> Complex)
  proof: .subtypeVal

@[fun_prop]

中文:
定理 isEmbedding_coe
  结论: 拓扑.是嵌入 ((↑) : 𝕔𝔻 -> 复形)
  证明: .subtypeVal

@[fun_prop]

Depends on / 依赖: subtypeVal
-/
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : 𝕔𝔻 -> Complex) := .subtypeVal

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : 𝕔𝔻 -> Complex)
  proof: isEmbedding_coe.continuous

中文:
定理 continuous_coe
  结论: 连续 ((↑) : 𝕔𝔻 -> 复形)
  证明: isEmbedding_coe.continuous

Depends on / 依赖: continuous, isEmbedding_coe, isEmbedding_coe.continuous
-/
theorem continuous_coe : Continuous ((↑) : 𝕔𝔻 -> Complex) := isEmbedding_coe.continuous

/--
theorem `norm_le_one` / 定理 `norm_le_one`

English:
theorem norm_le_one
  given: (z : 𝕔𝔻)
  statement: ‖(z : Complex)‖ <= 1
  proof: mem_closedBall_zero_iff.1 z.2

中文:
定理 norm_le_one
  条件: (z : 𝕔𝔻)
  结论: ‖(z : 复形)‖ <= 1
  证明: mem_closedBall_zero_iff.1 z.2

Depends on / 依赖: mem_closedBall_zero_iff
-/
theorem norm_le_one (z : 𝕔𝔻) : ‖(z : Complex)‖ <= 1 :=
  mem_closedBall_zero_iff.1 z.2

/--
theorem `sq_norm_lt_one` / 定理 `sq_norm_lt_one`

English:
theorem sq_norm_lt_one
  given: (z : 𝕔𝔻)
  statement: ‖(z : Complex)‖ ^ 2 <= 1
  proof: by
  rw [sq_le_one_iff_abs_le_one]; rw [abs_norm]
  exact z.norm_le_one

中文:
定理 sq_norm_lt_one
  条件: (z : 𝕔𝔻)
  结论: ‖(z : 复形)‖ ^ 2 <= 1
  证明: by
  rw [sq_le_one_iff_abs_le_one]; rw [abs_norm]
  exact z.norm_le_one

Depends on / 依赖: abs_norm, norm_le_one, sq_le_one_iff_abs_le_one, z.norm_le_one
-/
theorem sq_norm_lt_one (z : 𝕔𝔻) : ‖(z : Complex)‖ ^ 2 <= 1 := by
  rw [sq_le_one_iff_abs_le_one]; rw [abs_norm]
  exact z.norm_le_one

/--
theorem `normSq_lt_one` / 定理 `normSq_lt_one`

English:
theorem normSq_lt_one
  given: (z : 𝕔𝔻)
  statement: normSq z <= 1
  proof: by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

@[simp, norm_cast]

中文:
定理 normSq_lt_one
  条件: (z : 𝕔𝔻)
  结论: normSq z <= 1
  证明: by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

@[simp, norm_cast]

Depends on / 依赖: Complex.norm_mul_self_eq_normSq, norm_mul_self_eq_normSq, sq_norm_lt_one, z.sq_norm_lt_one
-/
theorem normSq_lt_one (z : 𝕔𝔻) : normSq z <= 1 := by
  rw [← Complex.norm_mul_self_eq_normSq]; rw [← sq]
  exact z.sq_norm_lt_one

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (z w : 𝕔𝔻)
  statement: ↑(z * w) = (z * w : Complex)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (z w : 𝕔𝔻)
  结论: ↑(z * w) = (z * w : 复形)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (z w : 𝕔𝔻) : ↑(z * w) = (z * w : Complex) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (z : 𝕔𝔻)
  statement: ↑(-z) = (-z : Complex)
  proof: rfl

中文:
定理 coe_neg
  条件: (z : 𝕔𝔻)
  结论: ↑(-z) = (-z : 复形)
  证明: rfl
-/
theorem coe_neg (z : 𝕔𝔻) : ↑(-z) = (-z : Complex) := rfl

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (z : Complex) (hz : ‖z‖ <= 1)
  body: ⟨z, mem_closedBall_zero_iff.2 hz⟩

中文:
定义 mk
  签名: (z : 复形) (hz : ‖z‖ <= 1)
  定义体: ⟨z, mem_closedBall_zero_iff.2 hz⟩

Depends on / 依赖: mem_closedBall_zero_iff
-/
def mk (z : Complex) (hz : ‖z‖ <= 1) : 𝕔𝔻 :=
  ⟨z, mem_closedBall_zero_iff.2 hz⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift Complex 𝕔𝔻 (↑) (‖·‖ <= 1)
  body: ⟨mk z hz, rfl⟩

中文:
实例 :
  签名: CanLift 复形 𝕔𝔻 (↑) (‖·‖ <= 1)
  定义体: ⟨mk z hz, rfl⟩
-/
instance : CanLift Complex 𝕔𝔻 (↑) (‖·‖ <= 1) where
  prf z hz := ⟨mk z hz, rfl⟩

/-- A cases eliminator that makes `cases z` use `UnitClosedDisc.mk` instead of `Subtype.mk`. -/
@[elab_as_elim, cases_eliminator]
/--
Definition of `casesOn` / `casesOn` 的定义

English:
definition casesOn
  signature: {motive : 𝕔𝔻 -> Sort*} (mk : forall z hz, motive (.mk z hz)) (z : 𝕔𝔻)
  body: mk z z.norm_le_one

@[simp]

中文:
定义 casesOn
  签名: {motive : 𝕔𝔻 -> 类型层*} (mk : 对任意 z hz, motive (.mk z hz)) (z : 𝕔𝔻)
  定义体: mk z z.norm_le_one

@[simp]
-/
protected def casesOn {motive : 𝕔𝔻 -> Sort*} (mk : forall z hz, motive (.mk z hz)) (z : 𝕔𝔻) :
    motive z :=
  mk z z.norm_le_one

@[simp]
/--
theorem `casesOn_mk` / 定理 `casesOn_mk`

English:
theorem casesOn_mk
  given: {motive : 𝕔𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {z : Complex} (hz : ‖z‖ <= 1)
  proof: rfl

@[simp]

中文:
定理 casesOn_mk
  条件: {motive : 𝕔𝔻 -> 类型层*} (mk' : 对任意 z hz, motive (.mk z hz)) {z : 复形} (hz : ‖z‖ <= 1)
  证明: rfl

@[simp]
-/
theorem casesOn_mk {motive : 𝕔𝔻 -> Sort*} (mk' : forall z hz, motive (.mk z hz)) {z : Complex} (hz : ‖z‖ <= 1) :
    (mk z hz).casesOn mk' = mk' z hz :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (z : Complex) (hz : ‖z‖ <= 1)
  statement: (mk z hz : Complex) = z
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (z : 复形) (hz : ‖z‖ <= 1)
  结论: (mk z hz : 复形) = z
  证明: rfl

@[simp]
-/
theorem coe_mk (z : Complex) (hz : ‖z‖ <= 1) : (mk z hz : Complex) = z :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (z : 𝕔𝔻) (hz : ‖(z : Complex)‖ <= 1 := z.norm_le_one)
  statement: mk z hz = z
  proof: Subtype.eta _ _

@[simp]

中文:
定理 mk_coe
  条件: (z : 𝕔𝔻) (hz : ‖(z : 复形)‖ <= 1 := z.norm_le_one)
  结论: mk z hz = z
  证明: Subtype.eta _ _

@[simp]

Depends on / 依赖: norm_le_one, z.norm_le_one
-/
theorem mk_coe (z : 𝕔𝔻) (hz : ‖(z : Complex)‖ <= 1 := z.norm_le_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
/--
theorem `mk_inj` / 定理 `mk_inj`

English:
theorem mk_inj
  given: {z w : Complex} (hz : ‖z‖ <= 1) (hw : ‖w‖ <= 1)
  statement: mk z hz = mk w hw ↔ z = w
  proof: Subtype.mk_eq_mk

中文:
定理 mk_inj
  条件: {z w : 复形} (hz : ‖z‖ <= 1) (hw : ‖w‖ <= 1)
  结论: mk z hz = mk w hw ↔ z = w
  证明: Subtype.mk_eq_mk

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk
-/
theorem mk_inj {z w : Complex} (hz : ‖z‖ <= 1) (hw : ‖w‖ <= 1) : mk z hz = mk w hw ↔ z = w :=
  Subtype.mk_eq_mk

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : 𝕔𝔻 -> Prop}
  statement: (forall z, p z) ↔ forall z hz, p (mk z hz)
  proof: ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_le_one⟩

中文:
定理 «对任意»
  条件: {p : 𝕔𝔻 -> 命题}
  结论: (对任意 z, p z) ↔ 对任意 z hz, p (mk z hz)
  证明: ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_le_one⟩
-/
protected theorem «forall» {p : 𝕔𝔻 -> Prop} : (forall z, p z) ↔ forall z hz, p (mk z hz) :=
  ⟨fun h z hz => h (mk z hz), fun h z => h z z.norm_le_one⟩

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : 𝕔𝔻 -> Prop}
  statement: (exists z, p z) ↔ exists z hz, p (mk z hz)
  proof: ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_le_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]

中文:
定理 «存在»
  条件: {p : 𝕔𝔻 -> 命题}
  结论: (存在 z, p z) ↔ 存在 z hz, p (mk z hz)
  证明: ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_le_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]
-/
protected theorem «exists» {p : 𝕔𝔻 -> Prop} : (exists z, p z) ↔ exists z hz, p (mk z hz) :=
  ⟨fun ⟨z, hz⟩ => ⟨z, z.norm_le_one, hz⟩, fun ⟨z, hz, h⟩ => ⟨mk z hz, h⟩⟩

@[simp]
/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: (z : Complex) (hz : ‖-z‖ <= 1)
  statement: mk (-z) hz = -mk z (norm_neg z ▸ hz)
  proof: rfl

@[simp]

中文:
定理 mk_neg
  条件: (z : 复形) (hz : ‖-z‖ <= 1)
  结论: mk (-z) hz = -mk z (norm_neg z ▸ hz)
  证明: rfl

@[simp]
-/
theorem mk_neg (z : Complex) (hz : ‖-z‖ <= 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : 𝕔𝔻) : Complex) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ((0 : 𝕔𝔻) : 复形) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ((0 : 𝕔𝔻) : Complex) = 0 :=
  rfl

@[simp]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {z : 𝕔𝔻}
  statement: (z : Complex) = 0 ↔ z = 0
  proof: coe_injective.eq_iff' coe_zero

中文:
定理 coe_eq_zero
  条件: {z : 𝕔𝔻}
  结论: (z : 复形) = 0 ↔ z = 0
  证明: coe_injective.eq_iff' coe_zero

Depends on / 依赖: coe_injective, coe_injective.eq_iff, coe_zero, eq_iff
-/
theorem coe_eq_zero {z : 𝕔𝔻} : (z : Complex) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk 0 (by simp) = 0
  proof: rfl

中文:
定理 mk_zero
  结论: mk 0 (by simp) = 0
  证明: rfl
-/
@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl

/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {z : Complex} (hz : ‖z‖ <= 1)
  statement: mk z hz = 0 ↔ z = 0
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 mk_eq_zero
  条件: {z : 复形} (hz : ‖z‖ <= 1)
  结论: mk z hz = 0 ↔ z = 0
  证明: by simp [← coe_inj]

@[simp]
-/
@[simp] theorem mk_eq_zero {z : Complex} (hz : ‖z‖ <= 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : 𝕔𝔻) : Complex) = 1
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ((1 : 𝕔𝔻) : 复形) = 1
  证明: rfl

@[simp]
-/
theorem coe_one : ((1 : 𝕔𝔻) : Complex) = 1 :=
  rfl

@[simp]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {z : 𝕔𝔻}
  statement: (z : Complex) = 1 ↔ z = 1
  proof: coe_injective.eq_iff' coe_one

中文:
定理 coe_eq_one
  条件: {z : 𝕔𝔻}
  结论: (z : 复形) = 1 ↔ z = 1
  证明: coe_injective.eq_iff' coe_one

Depends on / 依赖: coe_injective, coe_injective.eq_iff, coe_one, eq_iff
-/
theorem coe_eq_one {z : 𝕔𝔻} : (z : Complex) = 1 ↔ z = 1 :=
  coe_injective.eq_iff' coe_one

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  statement: mk 1 (by simp) = 1
  proof: rfl

中文:
定理 mk_one
  结论: mk 1 (by simp) = 1
  证明: rfl
-/
@[simp] theorem mk_one : mk 1 (by simp) = 1 := rfl

/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {z : Complex} (hz : ‖z‖ <= 1)
  statement: mk z hz = 1 ↔ z = 1
  proof: by simp [← coe_inj]

中文:
定理 mk_eq_one
  条件: {z : 复形} (hz : ‖z‖ <= 1)
  结论: mk z hz = 1 ↔ z = 1
  证明: by simp [← coe_inj]
-/
@[simp] theorem mk_eq_one {z : Complex} (hz : ‖z‖ <= 1) : mk z hz = 1 ↔ z = 1 := by simp [← coe_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited 𝕔𝔻
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 𝕔𝔻
  定义体: ⟨0⟩
-/
instance : Inhabited 𝕔𝔻 :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Circle 𝕔𝔻
  body: inferInstanceAs MulAction (sphere _ _) (closedBall _ _)

中文:
实例 :
  签名: 乘法作用 Circle 𝕔𝔻
  定义体: inferInstanceAs MulAction (sphere _ _) (closedBall _ _)

Depends on / 依赖: MulAction, closedBall, sphere
-/
instance : MulAction Circle 𝕔𝔻 :=
inferInstanceAs MulAction (sphere _ _) (closedBall _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Circle Circle 𝕔𝔻
  body: inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (closedBall _ _)

中文:
实例 :
  签名: 标量塔 Circle Circle 𝕔𝔻
  定义体: inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (closedBall _ _)

Depends on / 依赖: IsScalarTower, closedBall, sphere
-/
instance : IsScalarTower Circle Circle 𝕔𝔻 :=
inferInstanceAs IsScalarTower (sphere _ _) (sphere _ _) (closedBall _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Circle 𝕔𝔻 𝕔𝔻
  body: isScalarTower_sphere_closedBall_closedBall

中文:
实例 :
  签名: 标量塔 Circle 𝕔𝔻 𝕔𝔻
  定义体: isScalarTower_sphere_closedBall_closedBall

Depends on / 依赖: isScalarTower_sphere_closedBall_closedBall
-/
instance : IsScalarTower Circle 𝕔𝔻 𝕔𝔻 :=
  isScalarTower_sphere_closedBall_closedBall

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass Circle 𝕔𝔻 𝕔𝔻
  body: instSMulCommClass_sphere_closedBall_closedBall

中文:
实例 :
  签名: 标量交换类 Circle 𝕔𝔻 𝕔𝔻
  定义体: instSMulCommClass_sphere_closedBall_closedBall

Depends on / 依赖: instSMulCommClass_sphere_closedBall_closedBall
-/
instance : SMulCommClass Circle 𝕔𝔻 𝕔𝔻 :=
  instSMulCommClass_sphere_closedBall_closedBall

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass 𝕔𝔻 Circle 𝕔𝔻
  body: SMulCommClass.symm _ _ _

中文:
实例 :
  签名: 标量交换类 𝕔𝔻 Circle 𝕔𝔻
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _

/--
Instance `instMulActionClosedBall` / 实例 `instMulActionClosedBall`

English:
instance instMulActionClosedBall
  signature: : MulAction 𝕔𝔻 𝔻
  body: inferInstanceAs MulAction (closedBall _ _) (ball _ _)

中文:
实例 instMulActionClosedBall
  签名: : 乘法作用 𝕔𝔻 𝔻
  定义体: inferInstanceAs MulAction (closedBall _ _) (ball _ _)

Depends on / 依赖: MulAction, closedBall
-/
instance instMulActionClosedBall : MulAction 𝕔𝔻 𝔻 :=
inferInstanceAs MulAction (closedBall _ _) (ball _ _)

/--
Instance `instIsScalarTower_closedBall_closedBall` / 实例 `instIsScalarTower_closedBall_closedBall`

English:
instance instIsScalarTower_closedBall_closedBall
  signature: :
  body: inferInstanceAs IsScalarTower (closedBall _ _) (closedBall _ _) (ball _ _)

中文:
实例 instIsScalarTower_closedBall_closedBall
  签名: :
  定义体: inferInstanceAs IsScalarTower (closedBall _ _) (closedBall _ _) (ball _ _)

Depends on / 依赖: IsScalarTower, closedBall
-/
instance instIsScalarTower_closedBall_closedBall :
    IsScalarTower 𝕔𝔻 𝕔𝔻 𝔻 :=
inferInstanceAs IsScalarTower (closedBall _ _) (closedBall _ _) (ball _ _)

/--
Instance `instIsScalarTower_closedBall` / 实例 `instIsScalarTower_closedBall`

English:
instance instIsScalarTower_closedBall
  signature: : IsScalarTower 𝕔𝔻 𝔻 𝔻
  body: inferInstanceAs IsScalarTower (closedBall _ _) (ball _ _) (ball _ _)

中文:
实例 instIsScalarTower_closedBall
  签名: : 标量塔 𝕔𝔻 𝔻 𝔻
  定义体: inferInstanceAs IsScalarTower (closedBall _ _) (ball _ _) (ball _ _)

Depends on / 依赖: IsScalarTower, closedBall
-/
instance instIsScalarTower_closedBall : IsScalarTower 𝕔𝔻 𝔻 𝔻 :=
inferInstanceAs IsScalarTower (closedBall _ _) (ball _ _) (ball _ _)

/--
Instance `instSMulCommClass_closedBall_left` / 实例 `instSMulCommClass_closedBall_left`

English:
instance instSMulCommClass_closedBall_left
  signature: : SMulCommClass 𝕔𝔻 𝔻 𝔻
  body: ⟨fun _ _ _ => Subtype.ext mul_left_comm _ _ _⟩

中文:
实例 instSMulCommClass_closedBall_left
  签名: : 标量交换类 𝕔𝔻 𝔻 𝔻
  定义体: ⟨fun _ _ _ => Subtype.ext mul_left_comm _ _ _⟩

Depends on / 依赖: Subtype, Subtype.ext, mul_left_comm
-/
instance instSMulCommClass_closedBall_left : SMulCommClass 𝕔𝔻 𝔻 𝔻 :=
⟨fun _ _ _ => Subtype.ext mul_left_comm _ _ _⟩

/--
Instance `instSMulCommClass_closedBall_right` / 实例 `instSMulCommClass_closedBall_right`

English:
instance instSMulCommClass_closedBall_right
  signature: : SMulCommClass 𝔻 𝕔𝔻 𝔻
  body: SMulCommClass.symm _ _ _

中文:
实例 instSMulCommClass_closedBall_right
  签名: : 标量交换类 𝔻 𝕔𝔻 𝔻
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance instSMulCommClass_closedBall_right : SMulCommClass 𝔻 𝕔𝔻 𝔻 :=
  SMulCommClass.symm _ _ _

/--
Instance `instSMulCommClass_circle_closedBall` / 实例 `instSMulCommClass_circle_closedBall`

English:
instance instSMulCommClass_circle_closedBall
  signature: : SMulCommClass Circle 𝕔𝔻 𝔻
  body: inferInstanceAs SMulCommClass (sphere _ _) (closedBall _ _) (ball _ _)

中文:
实例 instSMulCommClass_circle_closedBall
  签名: : 标量交换类 Circle 𝕔𝔻 𝔻
  定义体: inferInstanceAs SMulCommClass (sphere _ _) (closedBall _ _) (ball _ _)

Depends on / 依赖: SMulCommClass, closedBall, sphere
-/
instance instSMulCommClass_circle_closedBall : SMulCommClass Circle 𝕔𝔻 𝔻 :=
inferInstanceAs SMulCommClass (sphere _ _) (closedBall _ _) (ball _ _)

/--
Instance `instSMulCommClass_closedBall_circle` / 实例 `instSMulCommClass_closedBall_circle`

English:
instance instSMulCommClass_closedBall_circle
  signature: : SMulCommClass 𝕔𝔻 Circle 𝔻
  body: SMulCommClass.symm _ _ _

@[simp, norm_cast]

中文:
实例 instSMulCommClass_closedBall_circle
  签名: : 标量交换类 𝕔𝔻 Circle 𝔻
  定义体: SMulCommClass.symm _ _ _

@[simp, norm_cast]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance instSMulCommClass_closedBall_circle : SMulCommClass 𝕔𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
/--
theorem `coe_closedBall_smul` / 定理 `coe_closedBall_smul`

English:
theorem coe_closedBall_smul
  given: (z : 𝕔𝔻) (w : 𝔻)
  statement: ↑(z • w) = (z * w : Complex)
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_closedBall := coe_closedBall_smul

@[simp, norm_cast]

中文:
定理 coe_closedBall_smul
  条件: (z : 𝕔𝔻) (w : 𝔻)
  结论: ↑(z • w) = (z * w : 复形)
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_closedBall := coe_closedBall_smul

@[simp, norm_cast]
-/
theorem coe_closedBall_smul (z : 𝕔𝔻) (w : 𝔻) : ↑(z • w) = (z * w : Complex) :=
  rfl

@[deprecated (since := "2026-01-06")]
alias coe_smul_closedBall := coe_closedBall_smul

@[simp, norm_cast]
/--
theorem `coe_circle_smul` / 定理 `coe_circle_smul`

English:
theorem coe_circle_smul
  given: (z : Circle) (w : 𝕔𝔻)
  statement: ↑(z • w) = (z * w : Complex)
  proof: rfl

中文:
定理 coe_circle_smul
  条件: (z : Circle) (w : 𝕔𝔻)
  结论: ↑(z • w) = (z * w : 复形)
  证明: rfl
-/
theorem coe_circle_smul (z : Circle) (w : 𝕔𝔻) : ↑(z • w) = (z * w : Complex) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass 𝕔𝔻 Circle 𝕔𝔻
  body: SMulCommClass.symm _ _ _

中文:
实例 :
  签名: 标量交换类 𝕔𝔻 Circle 𝕔𝔻
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance : SMulCommClass 𝕔𝔻 Circle 𝕔𝔻 :=
  SMulCommClass.symm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow 𝕔𝔻 Nat
  body: ⟨z ^ n, by simp [pow_le_one₀ (norm_nonneg _) z.norm_le_one]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 𝕔𝔻 自然数
  定义体: ⟨z ^ n, by simp [pow_le_one₀ (norm_nonneg _) z.norm_le_one]⟩

@[simp, norm_cast]

Depends on / 依赖: norm_le_one, norm_nonneg, z.norm_le_one
-/
instance : Pow 𝕔𝔻 Nat where
  pow z n := ⟨z ^ n, by simp [pow_le_one₀ (norm_nonneg _) z.norm_le_one]⟩

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (z : 𝕔𝔻) (n : Nat)
  statement: ((z ^ n : 𝕔𝔻) : Complex) = z ^ (n : Nat)
  proof: rfl

@[fun_prop]

中文:
定理 coe_pow
  条件: (z : 𝕔𝔻) (n : 自然数)
  结论: ((z ^ n : 𝕔𝔻) : 复形) = z ^ (n : 自然数)
  证明: rfl

@[fun_prop]
-/
theorem coe_pow (z : 𝕔𝔻) (n : Nat) : ((z ^ n : 𝕔𝔻) : Complex) = z ^ (n : Nat) := rfl

@[fun_prop]
/--
theorem `continuous_pow` / 定理 `continuous_pow`

English:
theorem continuous_pow
  given: (n : Nat)
  statement: Continuous (· ^ n : 𝕔𝔻 -> 𝕔𝔻)
  proof: by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

中文:
定理 continuous_pow
  条件: (n : 自然数)
  结论: 连续 (· ^ n : 𝕔𝔻 -> 𝕔𝔻)
  证明: by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

Depends on / 依赖: Function, Function.comp_def, coe_pow, comp_def, continuous_iff, fun_prop, isEmbedding_coe, isEmbedding_coe.continuous_iff
-/
theorem continuous_pow (n : Nat) : Continuous (· ^ n : 𝕔𝔻 -> 𝕔𝔻) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_pow]
  fun_prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatPowAssoc 𝕔𝔻
  body: mod_cast pow_add (z : Complex) m n
  npow_one z := by simp [← coe_inj]
  npow_zero z := by simp [← coe_inj]

中文:
实例 :
  签名: 自然数PowAssoc 𝕔𝔻
  定义体: mod_cast pow_add (z : Complex) m n
  npow_one z := by simp [← coe_inj]
  npow_zero z := by simp [← coe_inj]

Depends on / 依赖: mod_cast, pow_add
-/
instance : NatPowAssoc 𝕔𝔻 where
  npow_add m n z := mod_cast pow_add (z : Complex) m n
  npow_one z := by simp [← coe_inj]
  npow_zero z := by simp [← coe_inj]

/--
Definition of `re` / `re` 的定义

English:
definition re
  signature: (z : 𝕔𝔻)
  body: Complex.re z

中文:
定义 re
  签名: (z : 𝕔𝔻)
  定义体: Complex.re z

Depends on / 依赖: Complex.re
-/
def re (z : 𝕔𝔻) : Real :=
  Complex.re z

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (z : 𝕔𝔻)
  body: Complex.im z

@[simp, norm_cast]

中文:
定义 im
  签名: (z : 𝕔𝔻)
  定义体: Complex.im z

@[simp, norm_cast]

Depends on / 依赖: Complex.im
-/
def im (z : 𝕔𝔻) : Real :=
  Complex.im z

@[simp, norm_cast]
/--
theorem `re_coe` / 定理 `re_coe`

English:
theorem re_coe
  given: (z : 𝕔𝔻)
  statement: (z : Complex).re = z.re
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_coe
  条件: (z : 𝕔𝔻)
  结论: (z : 复形).re = z.re
  证明: rfl

@[simp, norm_cast]
-/
theorem re_coe (z : 𝕔𝔻) : (z : Complex).re = z.re :=
  rfl

@[simp, norm_cast]
/--
theorem `im_coe` / 定理 `im_coe`

English:
theorem im_coe
  given: (z : 𝕔𝔻)
  statement: (z : Complex).im = z.im
  proof: rfl

@[simp]

中文:
定理 im_coe
  条件: (z : 𝕔𝔻)
  结论: (z : 复形).im = z.im
  证明: rfl

@[simp]
-/
theorem im_coe (z : 𝕔𝔻) : (z : Complex).im = z.im :=
  rfl

@[simp]
/--
theorem `re_neg` / 定理 `re_neg`

English:
theorem re_neg
  given: (z : 𝕔𝔻)
  statement: (-z).re = -z.re
  proof: rfl

@[simp]

中文:
定理 re_neg
  条件: (z : 𝕔𝔻)
  结论: (-z).re = -z.re
  证明: rfl

@[simp]
-/
theorem re_neg (z : 𝕔𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
/--
theorem `im_neg` / 定理 `im_neg`

English:
theorem im_neg
  given: (z : 𝕔𝔻)
  statement: (-z).im = -z.im
  proof: rfl

中文:
定理 im_neg
  条件: (z : 𝕔𝔻)
  结论: (-z).im = -z.im
  证明: rfl
-/
theorem im_neg (z : 𝕔𝔻) : (-z).im = -z.im :=
  rfl

/--
theorem `re_zero` / 定理 `re_zero`

English:
theorem re_zero
  statement: re 0 = 0
  proof: rfl

中文:
定理 re_zero
  结论: re 0 = 0
  证明: rfl
-/
@[simp] theorem re_zero : re 0 = 0 := rfl
/--
theorem `im_zero` / 定理 `im_zero`

English:
theorem im_zero
  statement: im 0 = 0
  proof: rfl

中文:
定理 im_zero
  结论: im 0 = 0
  证明: rfl
-/
@[simp] theorem im_zero : im 0 = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star 𝕔𝔻
  body: mk (conj z) (norm_conj z).symm ▸ z.norm_le_one

中文:
实例 :
  签名: 对合 𝕔𝔻
  定义体: mk (conj z) (norm_conj z).symm ▸ z.norm_le_one

Depends on / 依赖: norm_conj, norm_le_one, z.norm_le_one
-/
instance : Star 𝕔𝔻 where
star z := mk (conj z) (norm_conj z).symm ▸ z.norm_le_one

/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (z : 𝕔𝔻)
  statement: (↑(star z) : Complex) = conj ↑z
  proof: rfl

@[simp]

中文:
定理 coe_star
  条件: (z : 𝕔𝔻)
  结论: (↑(star z) : 复形) = conj ↑z
  证明: rfl

@[simp]
-/
@[simp] theorem coe_star (z : 𝕔𝔻) : (↑(star z) : Complex) = conj ↑z := rfl

@[simp]
/--
theorem `star_eq_zero` / 定理 `star_eq_zero`

English:
theorem star_eq_zero
  given: {z : 𝕔𝔻}
  statement: star z = 0 ↔ z = 0
  proof: by
  simp [← coe_eq_zero]

@[simp]

中文:
定理 star_eq_zero
  条件: {z : 𝕔𝔻}
  结论: star z = 0 ↔ z = 0
  证明: by
  simp [← coe_eq_zero]

@[simp]
-/
protected theorem star_eq_zero {z : 𝕔𝔻} : star z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

@[simp]
/--
theorem `star_zero` / 定理 `star_zero`

English:
theorem star_zero
  statement: star (0 : 𝕔𝔻) = 0
  proof: by simp

中文:
定理 star_zero
  结论: star (0 : 𝕔𝔻) = 0
  证明: by simp
-/
protected theorem star_zero : star (0 : 𝕔𝔻) = 0 := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar 𝕔𝔻
  body: by ext; simp

中文:
实例 :
  签名: InvolutiveStar 𝕔𝔻
  定义体: by ext; simp
-/
instance : InvolutiveStar 𝕔𝔻 where
  star_involutive z := by ext; simp

/--
theorem `star_neg` / 定理 `star_neg`

English:
theorem star_neg
  given: (z : 𝕔𝔻)
  statement: star (-z) = -(star z)
  proof: rfl

中文:
定理 star_neg
  条件: (z : 𝕔𝔻)
  结论: star (-z) = -(star z)
  证明: rfl
-/
@[simp] protected theorem star_neg (z : 𝕔𝔻) : star (-z) = -(star z) := rfl

/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  given: (z : 𝕔𝔻)
  statement: (star z).re = z.re
  proof: rfl

中文:
定理 re_star
  条件: (z : 𝕔𝔻)
  结论: (star z).re = z.re
  证明: rfl
-/
@[simp] protected theorem re_star (z : 𝕔𝔻) : (star z).re = z.re := rfl

/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  given: (z : 𝕔𝔻)
  statement: (star z).im = -z.im
  proof: rfl

中文:
定理 im_star
  条件: (z : 𝕔𝔻)
  结论: (star z).im = -z.im
  证明: rfl
-/
@[simp] protected theorem im_star (z : 𝕔𝔻) : (star z).im = -z.im := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul 𝕔𝔻
  body: coe_injective by simp [mul_comm]

中文:
实例 :
  签名: StarMul 𝕔𝔻
  定义体: coe_injective by simp [mul_comm]

Depends on / 依赖: coe_injective, mul_comm
-/
instance : StarMul 𝕔𝔻 where
star_mul z w := coe_injective by simp [mul_comm]

end UnitClosedDisc

end Complex
