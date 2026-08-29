/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `PMF` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : PMF β` is the distribution given by sampling `a : α` from `pa : PMF α`,
and then sampling from `pb a : PMF β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/

@[expose] public section


noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal

open MeasureTheory

namespace PMF

section Pure

open scoped Classical in
/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

中文:
定义 pure
  签名: (a : α)
  定义体: ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

Depends on / 依赖: hasSum_ite_eq
-/
def pure (a : α) : PMF α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

variable (a a' : α)

open scoped Classical in
@[simp]
/--
theorem `pure_apply` / 定理 `pure_apply`

English:
theorem pure_apply
  statement: pure a a' = if a' = a then 1 else 0
  proof: rfl

@[simp]

中文:
定理 pure_apply
  结论: pure a a' = if a' = a then 1 else 0
  证明: rfl

@[simp]
-/
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

@[simp]
/--
theorem `support_pure` / 定理 `support_pure`

English:
theorem support_pure
  statement: (pure a).support = {a}
  proof: Set.ext fun a' => by simp [mem_support_iff]

中文:
定理 support_pure
  结论: (pure a).support = {a}
  证明: Set.ext fun a' => by simp [mem_support_iff]

Depends on / 依赖: Set.ext, mem_support_iff
-/
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]

/--
theorem `mem_support_pure_iff` / 定理 `mem_support_pure_iff`

English:
theorem mem_support_pure_iff
  statement: a' in (pure a).support ↔ a' = a
  proof: by simp

中文:
定理 mem_support_pure_iff
  结论: a' in (pure a).support ↔ a' = a
  证明: by simp
-/
theorem mem_support_pure_iff : a' in (pure a).support ↔ a' = a := by simp

/--
theorem `pure_apply_self` / 定理 `pure_apply_self`

English:
theorem pure_apply_self
  statement: pure a a = 1
  proof: if_pos rfl

中文:
定理 pure_apply_self
  结论: pure a a = 1
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl

/--
theorem `pure_apply_of_ne` / 定理 `pure_apply_of_ne`

English:
theorem pure_apply_of_ne
  given: (h : a' != a)
  statement: pure a a' = 0
  proof: if_neg h

中文:
定理 pure_apply_of_ne
  条件: (h : a' != a)
  结论: pure a a' = 0
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem pure_apply_of_ne (h : a' != a) : pure a a' = 0 :=
  if_neg h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (PMF α)
  body: ⟨pure default⟩

中文:
实例 [可居
  签名: α] : 可居 (PMF α)
  定义体: ⟨pure default⟩
-/
instance [Inhabited α] : Inhabited (PMF α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

open scoped Classical in
@[simp]
/--
theorem `toOuterMeasure_pure_apply` / 定理 `toOuterMeasure_pure_apply`

English:
theorem toOuterMeasure_pure_apply
  statement: (pure a).toOuterMeasure s = if a in s then 1 else 0
  proof: by
  refine (toOuterMeasure_apply (pure a) s).trans ?_
  split_ifs with ha
  · refine (tsum_congr fun b => ?_).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb =>
      symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine (tsum_congr fun b => ?_).trans tsum_zero
    exact

中文:
定理 toOuterMeasure_pure_apply
  结论: (pure a).toOuterMeasure s = if a in s then 1 else 0
  证明: by
  refine (toOuterMeasure_apply (pure a) s).trans ?_
  split_ifs with ha
  · refine (tsum_congr fun b => ?_).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb =>
      symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine (tsum_congr fun b => ?_).trans tsum_zero
    exact

Depends on / 依赖: h.symm, ite_eq_left_iff, ite_eq_right_iff, split_ifs, toOuterMeasure_apply, tsum_congr, tsum_ite_eq, tsum_zero
-/
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a in s then 1 else 0 := by
  refine (toOuterMeasure_apply (pure a) s).trans ?_
  split_ifs with ha
  · refine (tsum_congr fun b => ?_).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb =>
      symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine (tsum_congr fun b => ?_).trans tsum_zero
    exact ite_eq_right_iff.2 fun hb =>
      ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim

variable [MeasurableSpace α]

open scoped Classical in
/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise. -/
@[simp]
/--
theorem `toMeasure_pure_apply` / 定理 `toMeasure_pure_apply`

English:
theorem toMeasure_pure_apply
  given: (hs : MeasurableSet s)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply (pure a) hs).trans (toOuterMeasure_pure_apply a s)

中文:
定理 toMeasure_pure_apply
  条件: (hs : 可测集 s)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply (pure a) hs).trans (toOuterMeasure_pure_apply a s)

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_pure_apply
-/
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a in s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) hs).trans (toOuterMeasure_pure_apply a s)

/--
theorem `toMeasure_pure` / 定理 `toMeasure_pure`

English:
theorem toMeasure_pure
  statement: (pure a).toMeasure = Measure.dirac a
  proof: Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl

@[simp]

中文:
定理 toMeasure_pure
  结论: (pure a).toMeasure = 测度.dirac a
  证明: Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl

@[simp]

Depends on / 依赖: Measure, Measure.dirac_apply, Measure.ext, dirac_apply, toMeasure_pure_apply
-/
theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by rw [toMeasure_pure_apply a s hs, Measure.dirac_apply' a hs]; rfl

@[simp]
/--
theorem `toPMF_dirac` / 定理 `toPMF_dirac`

English:
theorem toPMF_dirac
  given: [Countable α] [h : MeasurableSingletonClass α]
  proof: by
  rw [toPMF_eq_iff_toMeasure_eq]; rw [toMeasure_pure]

中文:
定理 toPMF_dirac
  条件: [可数 α] [h : MeasurableSingleton类 α]
  证明: by
  rw [toPMF_eq_iff_toMeasure_eq]; rw [toMeasure_pure]

Depends on / 依赖: toMeasure_pure, toPMF_eq_iff_toMeasure_eq
-/
theorem toPMF_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toPMF = pure a := by
  rw [toPMF_eq_iff_toMeasure_eq]; rw [toMeasure_pure]

end Measure

end Pure

section Bind

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (p : PMF α) (f : α -> PMF β)
  body: ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩

中文:
定义 bind
  签名: (p : PMF α) (f : α -> PMF β)
  定义体: ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum_iff, ENNReal.tsum_comm.trans, ENNReal.tsum_mul_left, hasSum_iff, mul_one, summable, tsum_coe, tsum_comm, tsum_mul_left
-/
def bind (p : PMF α) (f : α -> PMF β) : PMF β :=
  ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩

variable (p : PMF α) (f : α -> PMF β) (g : β -> PMF γ)

@[simp]
/--
theorem `bind_apply` / 定理 `bind_apply`

English:
theorem bind_apply
  given: (b : β)
  statement: p.bind f b = ∑' a, p a * f a b
  proof: rfl

@[simp]

中文:
定理 bind_apply
  条件: (b : β)
  结论: p.bind f b = ∑' a, p a * f a b
  证明: rfl

@[simp]
-/
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b := rfl

@[simp]
/--
theorem `support_bind` / 定理 `support_bind`

English:
theorem support_bind
  statement: (p.bind f).support = ⋃ a in p.support, (f a).support
  proof: Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]

中文:
定理 support_bind
  结论: (p.bind f).support = ⋃ a in p.support, (f a).support
  证明: Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_zero, Set.ext, mem_support_iff, not_or, tsum_eq_zero
-/
theorem support_bind : (p.bind f).support = ⋃ a in p.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]

/--
theorem `mem_support_bind_iff` / 定理 `mem_support_bind_iff`

English:
theorem mem_support_bind_iff
  given: (b : β)
  proof: by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]

中文:
定理 mem_support_bind_iff
  条件: (b : β)
  证明: by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]

Depends on / 依赖: Set.mem_iUnion, exists_prop, mem_iUnion, support_bind
-/
theorem mem_support_bind_iff (b : β) :
    b in (p.bind f).support ↔ exists a in p.support, b in (f a).support := by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

@[simp]
/--
theorem `pure_bind` / 定理 `pure_bind`

English:
theorem pure_bind
  given: (a : α) (f : α -> PMF β)
  statement: (pure a).bind f = f a
  proof: by
  ext
  simp

@[simp]

中文:
定理 pure_bind
  条件: (a : α) (f : α -> PMF β)
  结论: (pure a).bind f = f a
  证明: by
  ext
  simp

@[simp]
-/
theorem pure_bind (a : α) (f : α -> PMF β) : (pure a).bind f = f a := by
  ext
  simp

@[simp]
/--
theorem `bind_pure` / 定理 `bind_pure`

English:
theorem bind_pure
  statement: p.bind pure = p
  proof: PMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
(tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero])
    by rw [pure_apply_self, mul_one])

@[simp]

中文:
定理 bind_pure
  结论: p.bind pure = p
  证明: PMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
(tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero])
    by rw [pure_apply_self, mul_one])

@[simp]

Depends on / 依赖: PMF.ext, _root_, _root_.trans, bind_apply, hy.symm, mul_one, mul_zero, pure_apply_of_ne, pure_apply_self, tsum_eq_single
-/
theorem bind_pure : p.bind pure = p :=
  PMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
(tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero])
    by rw [pure_apply_self, mul_one])

@[simp]
/--
theorem `bind_const` / 定理 `bind_const`

English:
theorem bind_const
  given: (p : PMF α) (q : PMF β)
  statement: (p.bind fun _ => q) = q
  proof: PMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]

@[simp]

中文:
定理 bind_const
  条件: (p : PMF α) (q : PMF β)
  结论: (p.bind fun _ => q) = q
  证明: PMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_mul_right, PMF.ext, bind_apply, one_mul, tsum_coe, tsum_mul_right
-/
theorem bind_const (p : PMF α) (q : PMF β) : (p.bind fun _ => q) = q :=
  PMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]

@[simp]
/--
theorem `bind_bind` / 定理 `bind_bind`

English:
theorem bind_bind
  statement: (p.bind f).bind g = p.bind fun a => (f a).bind g
  proof: PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

中文:
定理 bind_bind
  结论: (p.bind f).bind g = p.bind fun a => (f a).bind g
  证明: PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

Depends on / 依赖: ENNReal, ENNReal.coe_inj.symm, ENNReal.tsum_comm, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm, PMF.ext, bind_apply, coe_inj, mul_assoc, mul_comm, mul_left_comm, tsum_comm, tsum_mul_left, tsum_mul_right
-/
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

/--
theorem `bind_comm` / 定理 `bind_comm`

English:
theorem bind_comm
  given: (p : PMF α) (q : PMF β) (f : α -> β -> PMF γ)
  proof: PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

中文:
定理 bind_comm
  条件: (p : PMF α) (q : PMF β) (f : α -> β -> PMF γ)
  证明: PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

Depends on / 依赖: ENNReal, ENNReal.coe_inj.symm, ENNReal.tsum_comm, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm, PMF.ext, bind_apply, coe_inj, mul_assoc, mul_comm, mul_left_comm, tsum_comm, tsum_mul_left, tsum_mul_right
-/
theorem bind_comm (p : PMF α) (q : PMF β) (f : α -> β -> PMF γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  PMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

section Measure

variable (s : Set β)

@[simp]
/--
theorem `toOuterMeasure_bind_apply` / 定理 `toOuterMeasure_bind_apply`

English:
theorem toOuterMeasure_bind_apply
  proof: by
  classical
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b in s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b in s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b in s th

中文:
定理 toOuterMeasure_bind_apply
  证明: by
  classical
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b in s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b in s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b in s th

Depends on / 依赖: ENNReal, ENNReal.tsum_comm, ENNReal.tsum_mul_left, Set.indicator_apply, classical, congr_arg, indicator_apply, p.bind, split_ifs, toOuterMeasure, toOuterMeasure_apply, tsum_comm, tsum_congr, tsum_mul_left
-/
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s := by
  classical
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b in s then ∑' a, p a * f a b else 0 := by
      simp [toOuterMeasure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b in s then f a b else 0 := tsum_congr fun b => by split_ifs <;> simp
    _ = ∑' (a) (b), p a * if b in s then f a b else 0 := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, if b in s then f a b else 0 := tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' a, p a * ∑' b, if b in s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [toOuterMeasure_apply, Set.indicator_apply]

/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/
@[simp]
/--
theorem `toMeasure_bind_apply` / 定理 `toMeasure_bind_apply`

English:
theorem toMeasure_bind_apply
  given: [MeasurableSpace β] (hs : MeasurableSet s)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

中文:
定理 toMeasure_bind_apply
  条件: [可测空间 β] (hs : 可测集 s)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

Depends on / 依赖: congr_arg, p.bind, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_bind_apply, tsum_congr
-/
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) hs).symm))

end Measure

end Bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad PMF
  body: pure a
  bind pa pb := pa.bind pb

中文:
实例 :
  签名: 单子 PMF
  定义体: pure a
  bind pa pb := pa.bind pb
-/
instance : Monad PMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/--
Definition of `bindOnSupport` / `bindOnSupport` 的定义

English:
definition bindOnSupport
  signature: (p : PMF α) (f : forall a in p.support, PMF β)
  body: ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe)
    simp_rw [ENNReal.tsum_mul_left]
    split_ifs with h
    · simp only [h, zero_mul]
    · rw [(f a h).tsum_coe, mul_one

中文:
定义 bindOnSupport
  签名: (p : PMF α) (f : 对任意 a in p.support, PMF β)
  定义体: ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe)
    simp_rw [ENNReal.tsum_mul_left]
    split_ifs with h
    · simp only [h, zero_mul]
    · rw [(f a h).tsum_coe, mul_one

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum_iff, ENNReal.tsum_comm.trans, ENNReal.tsum_mul_left, _root_, _root_.trans, hasSum_iff, mul_one, p.tsum_coe, simp_rw, split_ifs, summable, tsum_coe, tsum_comm, tsum_congr, tsum_mul_left, zero_mul
-/
def bindOnSupport (p : PMF α) (f : forall a in p.support, PMF β) : PMF β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b, ENNReal.summable.hasSum_iff.2 (by
    refine ENNReal.tsum_comm.trans (_root_.trans (tsum_congr fun a => ?_) p.tsum_coe)
    simp_rw [ENNReal.tsum_mul_left]
    split_ifs with h
    · simp only [h, zero_mul]
    · rw [(f a h).tsum_coe, mul_one])⟩

variable {p : PMF α} (f : forall a in p.support, PMF β)

@[simp]
/--
theorem `bindOnSupport_apply` / 定理 `bindOnSupport_apply`

English:
theorem bindOnSupport_apply
  given: (b : β)
  proof: rfl

@[simp]

中文:
定理 bindOnSupport_apply
  条件: (b : β)
  证明: rfl

@[simp]
-/
theorem bindOnSupport_apply (b : β) :
    p.bindOnSupport f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b := rfl

@[simp]
/--
theorem `support_bindOnSupport` / 定理 `support_bindOnSupport`

English:
theorem support_bindOnSupport
  proof: by
  ext
  -- `simp` suffices; squeezed for performance
  simp only [mem_support_iff, bindOnSupport_apply, ne_eq, ENNReal.tsum_eq_zero,
    dite_eq_left_iff, mul_eq_zero, not_forall, not_or, and_exists_self,
    Set.mem_iUnion]

中文:
定理 support_bindOnSupport
  证明: by
  ext
  -- `simp` suffices; squeezed for performance
  simp only [mem_support_iff, bindOnSupport_apply, ne_eq, ENNReal.tsum_eq_zero,
    dite_eq_left_iff, mul_eq_zero, not_forall, not_or, and_exists_self,
    Set.mem_iUnion]
-/
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a in p.support), (f a h).support := by
  ext
  -- `simp` suffices; squeezed for performance
  simp only [mem_support_iff, bindOnSupport_apply, ne_eq, ENNReal.tsum_eq_zero,
    dite_eq_left_iff, mul_eq_zero, not_forall, not_or, and_exists_self,
    Set.mem_iUnion]

/--
theorem `mem_support_bindOnSupport_iff` / 定理 `mem_support_bindOnSupport_iff`

English:
theorem mem_support_bindOnSupport_iff
  given: (b : β)
  proof: by
  simp only [support_bindOnSupport, Set.mem_iUnion]

中文:
定理 mem_support_bindOnSupport_iff
  条件: (b : β)
  证明: by
  simp only [support_bindOnSupport, Set.mem_iUnion]

Depends on / 依赖: Set.mem_iUnion, mem_iUnion, support_bindOnSupport
-/
theorem mem_support_bindOnSupport_iff (b : β) :
    b in (p.bindOnSupport f).support ↔ exists (a : α) (h : a in p.support), b in (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_iUnion]

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
/--
theorem `bindOnSupport_eq_bind` / 定理 `bindOnSupport_eq_bind`

English:
theorem bindOnSupport_eq_bind
  given: (p : PMF α) (f : α -> PMF β)
  proof: by
  ext b
  have : forall a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]

中文:
定理 bindOnSupport_eq_bind
  条件: (p : PMF α) (f : α -> PMF β)
  证明: by
  ext b
  have : forall a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]

Depends on / 依赖: bindOnSupport_apply, bind_apply, dite_eq_ite, h.symm, ite_eq_right_iff, mul_ite, mul_zero, p.bind_apply, zero_mul
-/
theorem bindOnSupport_eq_bind (p : PMF α) (f : α -> PMF β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f := by
  ext b
  have : forall a, ite (p a = 0) 0 (p a * f a b) = p a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]

/--
theorem `bindOnSupport_eq_zero_iff` / 定理 `bindOnSupport_eq_zero_iff`

English:
theorem bindOnSupport_eq_zero_iff
  given: (b : β)
  proof: by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]

中文:
定理 bindOnSupport_eq_zero_iff
  条件: (b : β)
  证明: by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_zero, Trans.trans, bindOnSupport_apply, dif_neg, mul_eq_zero, or_iff_not_imp_left, tsum_eq_zero
-/
theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ forall (a) (ha : p a != 0), f a ha b = 0 := by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
/--
theorem `pure_bindOnSupport` / 定理 `pure_bindOnSupport`

English:
theorem pure_bindOnSupport
  given: (a : α) (f : forall (a' : α) (_ : a' in (pure a).support), PMF β)
  proof: by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  classical
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a (fun _ => _))
  by_cases h : a' = a <;> simp [h]

中文:
定理 pure_bindOnSupport
  条件: (a : α) (f : 对任意 (a' : α) (_ : a' in (pure a).support), PMF β)
  证明: by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  classical
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a (fun _ => _))
  by_cases h : a' = a <;> simp [h]

Depends on / 依赖: PMF.ext, _root_, _root_.trans, bindOnSupport_apply, classical, pure_apply, tsum_congr, tsum_ite_eq
-/
theorem pure_bindOnSupport (a : α) (f : forall (a' : α) (_ : a' in (pure a).support), PMF β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine PMF.ext fun b => ?_
  simp only [bindOnSupport_apply, pure_apply]
  classical
  refine _root_.trans (tsum_congr fun a' => ?_) (tsum_ite_eq a (fun _ => _))
  by_cases h : a' = a <;> simp [h]

/--
theorem `bindOnSupport_pure` / 定理 `bindOnSupport_pure`

English:
theorem bindOnSupport_pure
  given: (p : PMF α)
  statement: (p.bindOnSupport fun a _ => pure a) = p
  proof: by
  simp only [PMF.bind_pure, PMF.bindOnSupport_eq_bind]

中文:
定理 bindOnSupport_pure
  条件: (p : PMF α)
  结论: (p.bindOnSupport fun a _ => pure a) = p
  证明: by
  simp only [PMF.bind_pure, PMF.bindOnSupport_eq_bind]

Depends on / 依赖: PMF.bindOnSupport_eq_bind, PMF.bind_pure, bindOnSupport_eq_bind, bind_pure
-/
theorem bindOnSupport_pure (p : PMF α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [PMF.bind_pure, PMF.bindOnSupport_eq_bind]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `bindOnSupport_bindOnSupport` / 定理 `bindOnSupport_bindOnSupport`

English:
theorem bindOnSupport_bindOnSupport
  statement: (p : PMF α) (f : forall a in p.support, PMF β)
  proof: by
  refine PMF.ext fun a => ?_
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  classical
  simp only [ENNReal.tsum_eq_zero]
  refine ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => ?_)
  split_ifs with h

中文:
定理 bindOnSupport_bindOnSupport
  结论: (p : PMF α) (f : 对任意 a in p.support, PMF β)
  证明: by
  refine PMF.ext fun a => ?_
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  classical
  simp only [ENNReal.tsum_eq_zero]
  refine ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => ?_)
  split_ifs with h

Depends on / 依赖: ENNReal, ENNReal.tsum_comm.trans, ENNReal.tsum_eq_zero, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm, PMF.ext, absurd, any_goals, bindOnSupport_apply, classical, split_ifs, tsum_comm, tsum_congr, tsum_dite_right, tsum_eq_zero, tsum_mul_left, tsum_mul_right
-/
theorem bindOnSupport_bindOnSupport (p : PMF α) (f : forall a in p.support, PMF β)
    (g : forall b in (p.bindOnSupport f).support, PMF γ) :
    (p.bindOnSupport f).bindOnSupport g =
      p.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) := by
  refine PMF.ext fun a => ?_
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  classical
  simp only [ENNReal.tsum_eq_zero]
  refine ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => ?_)
  split_ifs with h _ h_1 H h_2
  any_goals ring1
  · absurd H
    simpa [h] using h_1 a'
  · simp [h_2]

/--
theorem `bindOnSupport_comm` / 定理 `bindOnSupport_comm`

English:
theorem bindOnSupport_comm
  given: (p : PMF α) (q : PMF β) (f : forall a in p.support, forall b in q.support, PMF γ)
  proof: by
  apply PMF.ext; rintro c
  simp only [bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm]
  refine _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => ?_)
  split_ifs with h1 h2 h2 <;> ring

中文:
定理 bindOnSupport_comm
  条件: (p : PMF α) (q : PMF β) (f : 对任意 a in p.support, 对任意 b in q.support, PMF γ)
  证明: by
  apply PMF.ext; rintro c
  simp only [bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm]
  refine _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => ?_)
  split_ifs with h1 h2 h2 <;> ring

Depends on / 依赖: ENNReal, ENNReal.tsum_comm, ENNReal.tsum_mul_left.symm, PMF.ext, _root_, _root_.trans, bindOnSupport_apply, split_ifs, tsum_comm, tsum_congr, tsum_dite_right, tsum_mul_left
-/
theorem bindOnSupport_comm (p : PMF α) (q : PMF β) (f : forall a in p.support, forall b in q.support, PMF γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb := by
  apply PMF.ext; rintro c
  simp only [bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm]
  refine _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => ?_)
  split_ifs with h1 h2 h2 <;> ring

section Measure

variable (s : Set β)

@[simp]
/--
theorem `toOuterMeasure_bindOnSupport_apply` / 定理 `toOuterMeasure_bindOnSupport_apply`

English:
theorem toOuterMeasure_bindOnSupport_apply
  proof: by
  simp only [toOuterMeasure_apply]
  classical
  calc
    (∑' b, ite (b in s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b in s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [t

中文:
定理 toOuterMeasure_bindOnSupport_apply
  证明: by
  simp only [toOuterMeasure_apply]
  classical
  calc
    (∑' b, ite (b in s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b in s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [t

Depends on / 依赖: ENNReal, ENNReal.tsum_comm, classical, split_ifs, toOuterMeasure_apply, tsum_comm, tsum_congr, tsum_zero
-/
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s := by
  simp only [toOuterMeasure_apply]
  classical
  calc
    (∑' b, ite (b in s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b in s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [tsum_zero]
    _ = ∑' (a) (b), ite (b in s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b in s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b in s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [ite_self, tsum_zero]

/-- The measure of a set under `p.bindOnSupport f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function. -/
@[simp]
/--
theorem `toMeasure_bindOnSupport_apply` / 定理 `toMeasure_bindOnSupport_apply`

English:
theorem toMeasure_bindOnSupport_apply
  given: [MeasurableSpace β] (hs : MeasurableSet s)
  proof: by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_bindOnSupport_apply]

中文:
定理 toMeasure_bindOnSupport_apply
  条件: [可测空间 β] (hs : 可测集 s)
  证明: by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_bindOnSupport_apply]

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_bindOnSupport_apply
-/
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s := by
  simp only [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_bindOnSupport_apply]

end Measure

end BindOnSupport

end PMF
