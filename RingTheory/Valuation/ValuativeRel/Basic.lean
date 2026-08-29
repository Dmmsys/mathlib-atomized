/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Adam Topaz
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Order.Filter.Bases.Basic

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `vle : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ≤ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of valuations.

## Main Definitions

- `ValuativeRel R` endows a semiring `R` with a relation "arising from a valuation". When `R` is a
  ring, this is equivalent to fixing an equivalence class of valuations on `R`.
  Use the notation `x ≤ᵥ y` for this relation.
- `ValuativeRel.valuation R` is the "canonical" valuation associated to `ValuativeRel R`,
  taking values in `ValuativeRel.ValueGroupWithZero R`.
- Given a valuation `v` on `R` and an instance `[ValuativeRel R]`, writing `[v.Compatible]`
  ensures that the relation `x ≤ᵥ y` is equivalent to `v x ≤ v y`. Note that
  it is possible to have `[v.Compatible]` and `[w.Compatible]` for two different valuations on `R`.
- Given `[ValuativeRel A]`, `[ValuativeRel B]` and `[Algebra A B]`, the class
  `[ValuativeExtension A B]` ensures that the algebra map `A → B` is compatible with the valuations
  on `A` and `B`. For example, this can be used to talk about extensions of valued fields.


## Remark

The last two axioms in `ValuativeRel`, namely `vle_mul_cancel` and `not_vle_one_zero`, are
used to ensure that we have a well-behaved valuation taking values in a *value group* (with zero).
In principle, it should be possible to drop these two axioms and obtain a value monoid,
however, such a value monoid would not necessarily embed into an ordered abelian group with zero.
Similarly, without these axioms, the support of the valuation need not be a prime ideal.
We have thus opted to include these two axioms and obtain a `ValueGroupWithZero` associated to
a `ValuativeRel` in order to best align with the literature about valuations on commutative rings.

Future work could refactor `ValuativeRel` by dropping the `vle_mul_cancel` and `not_vle_one_zero`
axioms, opting to make these mixins instead.

## Projects

The `ValuativeRel` class should eventually replace the existing `Valued` typeclass.
Once such a refactor happens, `ValuativeRel` could be renamed to `Valued`.

## TODO
Split this file. For instance, the universal properties of `ValueGroupWithZero` and definition of
`IsRankLeOne` could be separated out.
-/

@[expose] public section

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x y : R`
which is the natural relation arising from (the equivalence class of) a valuation on `R` when `R`
is a ring. More precisely, if `v` is a valuation on `R` then the associated relation is
`x ≤ᵥ y ↔ v x ≤ v y`. Use this class to talk about the case where `R` is equipped
with an equivalence class of valuations. -/
@[ext]
/--
Definition of `ValuativeRel` / `ValuativeRel` 的定义

English:
class ValuativeRel
  parameters: (R : Type*) [Semiring R]
  axioms and operations (8):
    - vle : R -> R -> Prop
    - vle_total((x y)) : vle x y ∨ vle y x
    - vle_trans({z y x}) : vle x y -> vle y z -> vle x z
    - vle_add({x y z}) : vle x z -> vle y z -> vle (x + y) z
    - mul_vle_mul_left({x y} (h : vle x y) (z)) : vle (x * z) (y * z)
    - vle_mul_cancel({x y z}) : ¬ vle z 0 -> vle (x * z) (y * z) -> vle x y
    - not_vle_one_zero : ¬ vle 1 0
    - vle_mul_comm({x y}) : vle (x * y) (y * x)

中文:
类 ValuativeRel
  参数: (R : 类型) [Semiring R]
  公理与运算 (8 个):
    - vle : R -> R -> 命题
    - vle_total((x y)) : vle x y ∨ vle y x
    - vle_trans({z y x}) : vle x y -> vle y z -> vle x z
    - vle_add({x y z}) : vle x z -> vle y z -> vle (x + y) z
    - mul_vle_mul_left({x y} (h : vle x y) (z)) : vle (x * z) (y * z)
    - vle_mul_cancel({x y z}) : ¬ vle z 0 -> vle (x * z) (y * z) -> vle x y
    - not_vle_one_zero : ¬ vle 1 0
    - vle_mul_comm({x y}) : vle (x * y) (y * x)
-/
class ValuativeRel (R : Type*) [Semiring R] where
  /-- The valuation less-equal operator arising from `ValuativeRel`. -/
  vle : R -> R -> Prop
  vle_total (x y) : vle x y ∨ vle y x
  vle_trans {z y x} : vle x y -> vle y z -> vle x z
  vle_add {x y z} : vle x z -> vle y z -> vle (x + y) z
  mul_vle_mul_left {x y} (h : vle x y) (z) : vle (x * z) (y * z)
  vle_mul_cancel {x y z} : ¬ vle z 0 -> vle (x * z) (y * z) -> vle x y
  not_vle_one_zero : ¬ vle 1 0
  vle_mul_comm {x y} : vle (x * y) (y * x)

@[inherit_doc] infix:50 " <=ᵥ " => ValuativeRel.vle

macro_rules | `($a <=ᵥ $b) => `(binrel% ValuativeRel.vle $a $b)

namespace Valuation

variable {R Γ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/--
Definition of `Compatible` / `Compatible` 的定义

English:
class Compatible
  parameters: [ValuativeRel R]
  axioms and operations (1):
    - vle_iff_le((x y : R)) : x <=ᵥ y ↔ v x <= v y

中文:
类 Compatible
  参数: [ValuativeRel R]
  公理与运算 (1 个):
    - vle_iff_le((x y : R)) : x <=ᵥ y ↔ v x <= v y
-/
class Compatible [ValuativeRel R] where
  vle_iff_le (x y : R) : x <=ᵥ y ↔ v x <= v y

end Valuation

/--
Definition of `ValuativePreorder` / `ValuativePreorder` 的定义

English:
class ValuativePreorder
  parameters: (R : Type*) [Semiring R] [ValuativeRel R] [Preorder R]
  axioms and operations (1):
    - vle_iff_le((x y : R)) : x <=ᵥ y ↔ x <= y

中文:
类 ValuativePreorder
  参数: (R : 类型) [Semiring R] [ValuativeRel R] [Preorder R]
  公理与运算 (1 个):
    - vle_iff_le((x y : R)) : x <=ᵥ y ↔ x <= y
-/
class ValuativePreorder (R : Type*) [Semiring R] [ValuativeRel R] [Preorder R] where
  vle_iff_le (x y : R) : x <=ᵥ y ↔ x <= y

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R] {x x' y y' z : R}

/--
Definition of `vlt` / `vlt` 的定义

English:
definition vlt
  signature: (x y : R)
  body: ¬ y <=ᵥ x

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)

中文:
定义 vlt
  签名: (x y : R)
  定义体: ¬ y <=ᵥ x

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)
-/
def vlt (x y : R) : Prop := ¬ y <=ᵥ x

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)

/--
Definition of `veq` / `veq` 的定义

English:
definition veq
  signature: : R -> R -> Prop
  body: AntisymmRel (· <=ᵥ ·)

@[inherit_doc] infix:50 " =ᵥ " => ValuativeRel.veq

中文:
定义 veq
  签名: : R -> R -> 命题
  定义体: AntisymmRel (· <=ᵥ ·)

@[inherit_doc] infix:50 " =ᵥ " => ValuativeRel.veq

Depends on / 依赖: AntisymmRel
-/
def veq : R -> R -> Prop := AntisymmRel (· <=ᵥ ·)

@[inherit_doc] infix:50 " =ᵥ " => ValuativeRel.veq

/--
lemma `veq_mul_comm` / 引理 `veq_mul_comm`

English:
lemma veq_mul_comm
  given: (x y : R)
  statement: x * y =ᵥ y * x
  proof: ⟨vle_mul_comm, vle_mul_comm⟩

macro_rules | `($a =ᵥ $b) => `(binrel% ValuativeRel.veq $a $b)

中文:
引理 veq_mul_comm
  条件: (x y : R)
  结论: x * y =ᵥ y * x
  证明: ⟨vle_mul_comm, vle_mul_comm⟩

macro_rules | `($a =ᵥ $b) => `(binrel% ValuativeRel.veq $a $b)

Depends on / 依赖: PseudoEMetricSpace, vle_mul_comm
-/
lemma veq_mul_comm (x y : R) : x * y =ᵥ y * x := ⟨vle_mul_comm, vle_mul_comm⟩

macro_rules | `($a =ᵥ $b) => `(binrel% ValuativeRel.veq $a $b)

/--
lemma `not_vle` / 引理 `not_vle`

English:
lemma not_vle
  statement: ¬ x <=ᵥ y ↔ y <ᵥ x
  proof: .rfl

中文:
引理 not_vle
  结论: ¬ x <=ᵥ y ↔ y <ᵥ x
  证明: .rfl
-/
@[simp, grind =] lemma not_vle : ¬ x <=ᵥ y ↔ y <ᵥ x := .rfl
/--
lemma `not_vlt` / 引理 `not_vlt`

English:
lemma not_vlt
  statement: ¬ x <ᵥ y ↔ y <=ᵥ x
  proof: not_vle.not_left

中文:
引理 not_vlt
  结论: ¬ x <ᵥ y ↔ y <=ᵥ x
  证明: not_vle.not_left
-/
@[simp, grind =] lemma not_vlt : ¬ x <ᵥ y ↔ y <=ᵥ x := not_vle.not_left
/--
lemma `veq_def` / 引理 `veq_def`

English:
lemma veq_def
  statement: x =ᵥ y ↔ x <=ᵥ y ∧ y <=ᵥ x
  proof: .rfl

protected alias ⟨_, vle.not_vlt⟩ := not_vlt
protected alias ⟨_, vlt.not_vle⟩ := not_vle

中文:
引理 veq_def
  结论: x =ᵥ y ↔ x <=ᵥ y ∧ y <=ᵥ x
  证明: .rfl

protected alias ⟨_, vle.not_vlt⟩ := not_vlt
protected alias ⟨_, vlt.not_vle⟩ := not_vle
-/
lemma veq_def : x =ᵥ y ↔ x <=ᵥ y ∧ y <=ᵥ x := .rfl

protected alias ⟨_, vle.not_vlt⟩ := not_vlt
protected alias ⟨_, vlt.not_vle⟩ := not_vle

/--
lemma `veq_comm` / 引理 `veq_comm`

English:
lemma veq_comm
  statement: x =ᵥ y ↔ y =ᵥ x
  proof: antisymmRel_comm
@[symm] protected alias ⟨veq.symm, _⟩ := veq_comm

中文:
引理 veq_comm
  结论: x =ᵥ y ↔ y =ᵥ x
  证明: antisymmRel_comm
@[symm] protected alias ⟨veq.symm, _⟩ := veq_comm

Depends on / 依赖: antisymmRel_comm
-/
lemma veq_comm : x =ᵥ y ↔ y =ᵥ x := antisymmRel_comm
@[symm] protected alias ⟨veq.symm, _⟩ := veq_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Symm R (· =ᵥ ·)
  body: veq.symm

中文:
实例 :
  签名: @Std.Symm R (· =ᵥ ·)
  定义体: veq.symm

Depends on / 依赖: veq.symm
-/
instance : @Std.Symm R (· =ᵥ ·) where
  symm _ _ := veq.symm

/--
lemma `vle_of_veq` / 引理 `vle_of_veq`

English:
lemma vle_of_veq
  given: (h : x =ᵥ y)
  statement: x <=ᵥ y
  proof: h.1

中文:
引理 vle_of_veq
  条件: (h : x =ᵥ y)
  结论: x <=ᵥ y
  证明: h.1
-/
lemma vle_of_veq (h : x =ᵥ y) : x <=ᵥ y := h.1
/--
lemma `vge_of_veq` / 引理 `vge_of_veq`

English:
lemma vge_of_veq
  given: (h : x =ᵥ y)
  statement: y <=ᵥ x
  proof: h.2

protected alias veq.vle := vle_of_veq
protected alias veq.vge := vge_of_veq

中文:
引理 vge_of_veq
  条件: (h : x =ᵥ y)
  结论: y <=ᵥ x
  证明: h.2

protected alias veq.vle := vle_of_veq
protected alias veq.vge := vge_of_veq
-/
lemma vge_of_veq (h : x =ᵥ y) : y <=ᵥ x := h.2

protected alias veq.vle := vle_of_veq
protected alias veq.vge := vge_of_veq

/--
lemma `not_vlt_of_veq` / 引理 `not_vlt_of_veq`

English:
lemma not_vlt_of_veq
  given: (h : x =ᵥ y)
  statement: ¬ x <ᵥ y
  proof: h.vge.not_vlt

中文:
引理 not_vlt_of_veq
  条件: (h : x =ᵥ y)
  结论: ¬ x <ᵥ y
  证明: h.vge.not_vlt

Depends on / 依赖: h.vge.not_vlt, not_vlt
-/
lemma not_vlt_of_veq (h : x =ᵥ y) : ¬ x <ᵥ y := h.vge.not_vlt
/--
lemma `not_vgt_of_veq` / 引理 `not_vgt_of_veq`

English:
lemma not_vgt_of_veq
  given: (h : x =ᵥ y)
  statement: ¬ y <ᵥ x
  proof: h.vle.not_vlt

protected alias veq.not_vlt := not_vlt_of_veq
protected alias veq.not_vgt := not_vgt_of_veq

中文:
引理 not_vgt_of_veq
  条件: (h : x =ᵥ y)
  结论: ¬ y <ᵥ x
  证明: h.vle.not_vlt

protected alias veq.not_vlt := not_vlt_of_veq
protected alias veq.not_vgt := not_vgt_of_veq

Depends on / 依赖: IsInducing, IsInducing.subtypeVal, WeakPseudoEMetricSpace, WeakPseudoEMetricSpace.IsInducing, h.vle.not_vlt, not_vlt, subtypeVal
-/
lemma not_vgt_of_veq (h : x =ᵥ y) : ¬ y <ᵥ x := h.vle.not_vlt

protected alias veq.not_vlt := not_vlt_of_veq
protected alias veq.not_vgt := not_vgt_of_veq

/--
lemma `vle_refl` / 引理 `vle_refl`

English:
lemma vle_refl
  given: (x : R)
  statement: x <=ᵥ x
  proof: or_self_iff.1 vle_total x x

中文:
引理 vle_refl
  条件: (x : R)
  结论: x <=ᵥ x
  证明: or_self_iff.1 vle_total x x
-/
@[simp, refl] lemma vle_refl (x : R) : x <=ᵥ x := or_self_iff.1 vle_total x x
/--
lemma `vle_rfl` / 引理 `vle_rfl`

English:
lemma vle_rfl
  statement: x <=ᵥ x
  proof: vle_refl x

protected alias vle.refl := vle_refl
protected alias vle.rfl := vle_rfl

中文:
引理 vle_rfl
  结论: x <=ᵥ x
  证明: vle_refl x

protected alias vle.refl := vle_refl
protected alias vle.rfl := vle_rfl

Depends on / 依赖: vle_refl
-/
lemma vle_rfl : x <=ᵥ x := vle_refl x

protected alias vle.refl := vle_refl
protected alias vle.rfl := vle_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl R (· <=ᵥ ·)
  body: vle_rfl

中文:
实例 :
  签名: @Std.Refl R (· <=ᵥ ·)
  定义体: vle_rfl

Depends on / 依赖: Subtype, Subtype.coe_injective, WeakEMetricSpace, WeakEMetricSpace.induced, coe_injective, induced, vle_rfl
-/
instance : @Std.Refl R (· <=ᵥ ·) where
  refl _ := vle_rfl

/--
lemma `veq_refl` / 引理 `veq_refl`

English:
lemma veq_refl
  given: (x : R)
  statement: x =ᵥ x
  proof: AntisymmRel.rfl

中文:
引理 veq_refl
  条件: (x : R)
  结论: x =ᵥ x
  证明: AntisymmRel.rfl
-/
@[simp, refl] lemma veq_refl (x : R) : x =ᵥ x := AntisymmRel.rfl
/--
lemma `veq_rfl` / 引理 `veq_rfl`

English:
lemma veq_rfl
  statement: x =ᵥ x
  proof: veq_refl x

protected alias veq.refl := veq_refl
protected alias veq.rfl := veq_rfl

中文:
引理 veq_rfl
  结论: x =ᵥ x
  证明: veq_refl x

protected alias veq.refl := veq_refl
protected alias veq.rfl := veq_rfl

Depends on / 依赖: veq_refl
-/
lemma veq_rfl : x =ᵥ x := veq_refl x

protected alias veq.refl := veq_refl
protected alias veq.rfl := veq_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl R (· =ᵥ ·)
  body: veq_rfl

@[simp]

中文:
实例 :
  签名: @Std.Refl R (· =ᵥ ·)
  定义体: veq_rfl

@[simp]

Depends on / 依赖: veq_rfl
-/
instance : @Std.Refl R (· =ᵥ ·) where
  refl _ := veq_rfl

@[simp]
/--
theorem `zero_vle` / 定理 `zero_vle`

English:
theorem zero_vle
  given: (x : R)
  statement: 0 <=ᵥ x
  proof: by
  simpa using mul_vle_mul_left ((vle_total 0 1).resolve_right not_vle_one_zero) x

@[simp]

中文:
定理 zero_vle
  条件: (x : R)
  结论: 0 <=ᵥ x
  证明: by
  simpa using mul_vle_mul_left ((vle_total 0 1).resolve_right not_vle_one_zero) x

@[simp]

Depends on / 依赖: EMetricSpace, mul_vle_mul_left, not_vle_one_zero, resolve_right, vle_total
-/
theorem zero_vle (x : R) : 0 <=ᵥ x := by
  simpa using mul_vle_mul_left ((vle_total 0 1).resolve_right not_vle_one_zero) x

@[simp]
/--
theorem `not_vlt_zero` / 定理 `not_vlt_zero`

English:
theorem not_vlt_zero
  given: (x : R)
  statement: ¬ x <ᵥ 0
  proof: by
  simp

中文:
定理 not_vlt_zero
  条件: (x : R)
  结论: ¬ x <ᵥ 0
  证明: by
  simp
-/
theorem not_vlt_zero (x : R) : ¬ x <ᵥ 0 := by
  simp

/--
theorem `vlt.ne_zero` / 定理 `vlt.ne_zero`

English:
theorem vlt.ne_zero
  given: (h : x <ᵥ y)
  statement: y != 0
  proof: by
  rintro rfl; exact not_vlt_zero _ h

@[simp]

中文:
定理 vlt.ne_zero
  条件: (h : x <ᵥ y)
  结论: y != 0
  证明: by
  rintro rfl; exact not_vlt_zero _ h

@[simp]

Depends on / 依赖: not_vlt_zero
-/
theorem vlt.ne_zero (h : x <ᵥ y) : y != 0 := by
  rintro rfl; exact not_vlt_zero _ h

@[simp]
/--
lemma `zero_vlt_one` / 引理 `zero_vlt_one`

English:
lemma zero_vlt_one
  statement: (0 : R) <ᵥ 1
  proof: not_vle_one_zero

@[deprecated mul_vle_mul_left (since := "2026-01-06")]

中文:
引理 zero_vlt_one
  结论: (0 : R) <ᵥ 1
  证明: not_vle_one_zero

@[deprecated mul_vle_mul_left (since := "2026-01-06")]

Depends on / 依赖: not_vle_one_zero
-/
lemma zero_vlt_one : (0 : R) <ᵥ 1 :=
  not_vle_one_zero

@[deprecated mul_vle_mul_left (since := "2026-01-06")]
/--
lemma `vle_mul_right` / 引理 `vle_mul_right`

English:
lemma vle_mul_right
  given: (z) (h : x <=ᵥ y)
  statement: x * z <=ᵥ y * z
  proof: mul_vle_mul_left h z

中文:
引理 vle_mul_right
  条件: (z) (h : x <=ᵥ y)
  结论: x * z <=ᵥ y * z
  证明: mul_vle_mul_left h z

Depends on / 依赖: mul_vle_mul_left
-/
lemma vle_mul_right (z) (h : x <=ᵥ y) : x * z <=ᵥ y * z :=
  mul_vle_mul_left h z

/--
lemma `mul_vle_mul_right` / 引理 `mul_vle_mul_right`

English:
lemma mul_vle_mul_right
  given: (h : x <=ᵥ y) (z)
  statement: z * x <=ᵥ z * y
  proof: vle_trans (veq_mul_comm _ _).1 (vle_trans (mul_vle_mul_left h z) ((veq_mul_comm _ _).1))

中文:
引理 mul_vle_mul_right
  条件: (h : x <=ᵥ y) (z)
  结论: z * x <=ᵥ z * y
  证明: vle_trans (veq_mul_comm _ _).1 (vle_trans (mul_vle_mul_left h z) ((veq_mul_comm _ _).1))

Depends on / 依赖: mul_vle_mul_left, veq_mul_comm, vle_trans
-/
lemma mul_vle_mul_right (h : x <=ᵥ y) (z) : z * x <=ᵥ z * y :=
  vle_trans (veq_mul_comm _ _).1 (vle_trans (mul_vle_mul_left h z) ((veq_mul_comm _ _).1))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vle vle vle
  body: vle_trans

protected alias vle.trans := vle_trans

中文:
实例 :
  签名: @Trans R R R vle vle vle
  定义体: vle_trans

protected alias vle.trans := vle_trans

Depends on / 依赖: vle_trans
-/
instance : @Trans R R R vle vle vle where
  trans := vle_trans

protected alias vle.trans := vle_trans

/--
lemma `vle_trans'` / 引理 `vle_trans'`

English:
lemma vle_trans'
  given: (h1 : y <=ᵥ z) (h2 : x <=ᵥ y)
  statement: x <=ᵥ z
  proof: h2.trans h1

protected alias vle.trans' := vle_trans'

中文:
引理 vle_trans'
  条件: (h1 : y <=ᵥ z) (h2 : x <=ᵥ y)
  结论: x <=ᵥ z
  证明: h2.trans h1

protected alias vle.trans' := vle_trans'

Depends on / 依赖: h2.trans
-/
lemma vle_trans' (h1 : y <=ᵥ z) (h2 : x <=ᵥ y) : x <=ᵥ z :=
  h2.trans h1

protected alias vle.trans' := vle_trans'

/--
lemma `veq_trans` / 引理 `veq_trans`

English:
lemma veq_trans
  given: (h1 : x =ᵥ y) (h2 : y =ᵥ z)
  statement: x =ᵥ z
  proof: AntisymmRel.trans h1 h2

中文:
引理 veq_trans
  条件: (h1 : x =ᵥ y) (h2 : y =ᵥ z)
  结论: x =ᵥ z
  证明: AntisymmRel.trans h1 h2

Depends on / 依赖: AntisymmRel, AntisymmRel.trans
-/
lemma veq_trans (h1 : x =ᵥ y) (h2 : y =ᵥ z) : x =ᵥ z :=
  AntisymmRel.trans h1 h2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R veq veq veq
  body: veq_trans

中文:
实例 :
  签名: @Trans R R R veq veq veq
  定义体: veq_trans

Depends on / 依赖: veq_trans
-/
instance : @Trans R R R veq veq veq where
  trans := veq_trans

/--
lemma `vle_of_veq_of_vle` / 引理 `vle_of_veq_of_vle`

English:
lemma vle_of_veq_of_vle
  given: (h1 : x =ᵥ y) (h2 : y <=ᵥ z)
  statement: x <=ᵥ z
  proof: h1.1.trans h2

中文:
引理 vle_of_veq_of_vle
  条件: (h1 : x =ᵥ y) (h2 : y <=ᵥ z)
  结论: x <=ᵥ z
  证明: h1.1.trans h2
-/
lemma vle_of_veq_of_vle (h1 : x =ᵥ y) (h2 : y <=ᵥ z) : x <=ᵥ z :=
  h1.1.trans h2

/--
lemma `vle_of_vle_of_veq` / 引理 `vle_of_vle_of_veq`

English:
lemma vle_of_vle_of_veq
  given: (h1 : x <=ᵥ y) (h2 : y =ᵥ z)
  statement: x <=ᵥ z
  proof: h1.trans h2.1

中文:
引理 vle_of_vle_of_veq
  条件: (h1 : x <=ᵥ y) (h2 : y =ᵥ z)
  结论: x <=ᵥ z
  证明: h1.trans h2.1

Depends on / 依赖: h1.trans
-/
lemma vle_of_vle_of_veq (h1 : x <=ᵥ y) (h2 : y =ᵥ z) : x <=ᵥ z :=
  h1.trans h2.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R veq vle vle
  body: vle_of_veq_of_vle

中文:
实例 :
  签名: @Trans R R R veq vle vle
  定义体: vle_of_veq_of_vle

Depends on / 依赖: vle_of_veq_of_vle
-/
instance : @Trans R R R veq vle vle where
  trans := vle_of_veq_of_vle

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vle veq vle
  body: vle_of_vle_of_veq

中文:
实例 :
  签名: @Trans R R R vle veq vle
  定义体: vle_of_vle_of_veq

Depends on / 依赖: vle_of_vle_of_veq
-/
instance : @Trans R R R vle veq vle where
  trans := vle_of_vle_of_veq

/--
lemma `vlt_of_vlt_of_vle` / 引理 `vlt_of_vlt_of_vle`

English:
lemma vlt_of_vlt_of_vle
  given: (h1 : x <ᵥ y) (h2 : y <=ᵥ z)
  statement: x <ᵥ z
  proof: fun h => (h1 (vle_trans h2 h)).elim

alias vlt.trans_vle := vlt_of_vlt_of_vle

中文:
引理 vlt_of_vlt_of_vle
  条件: (h1 : x <ᵥ y) (h2 : y <=ᵥ z)
  结论: x <ᵥ z
  证明: fun h => (h1 (vle_trans h2 h)).elim

alias vlt.trans_vle := vlt_of_vlt_of_vle

Depends on / 依赖: vle_trans
-/
lemma vlt_of_vlt_of_vle (h1 : x <ᵥ y) (h2 : y <=ᵥ z) : x <ᵥ z :=
  fun h => (h1 (vle_trans h2 h)).elim

alias vlt.trans_vle := vlt_of_vlt_of_vle

/--
lemma `vlt_of_vle_of_vlt` / 引理 `vlt_of_vle_of_vlt`

English:
lemma vlt_of_vle_of_vlt
  given: (h1 : x <=ᵥ y) (h2 : y <ᵥ z)
  statement: x <ᵥ z
  proof: fun h => (h2 (vle_trans h h1)).elim

alias vle.trans_vlt := vlt_of_vle_of_vlt

中文:
引理 vlt_of_vle_of_vlt
  条件: (h1 : x <=ᵥ y) (h2 : y <ᵥ z)
  结论: x <ᵥ z
  证明: fun h => (h2 (vle_trans h h1)).elim

alias vle.trans_vlt := vlt_of_vle_of_vlt

Depends on / 依赖: vle_trans
-/
lemma vlt_of_vle_of_vlt (h1 : x <=ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  fun h => (h2 (vle_trans h h1)).elim

alias vle.trans_vlt := vlt_of_vle_of_vlt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vlt vle vlt
  body: vlt_of_vlt_of_vle

中文:
实例 :
  签名: @Trans R R R vlt vle vlt
  定义体: vlt_of_vlt_of_vle

Depends on / 依赖: vlt_of_vlt_of_vle
-/
instance : @Trans R R R vlt vle vlt where
  trans := vlt_of_vlt_of_vle

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vle vlt vlt
  body: vlt_of_vle_of_vlt

中文:
实例 :
  签名: @Trans R R R vle vlt vlt
  定义体: vlt_of_vle_of_vlt

Depends on / 依赖: vlt_of_vle_of_vlt
-/
instance : @Trans R R R vle vlt vlt where
  trans := vlt_of_vle_of_vlt

/--
lemma `vlt.vle` / 引理 `vlt.vle`

English:
lemma vlt.vle
  given: (h : x <ᵥ y)
  statement: x <=ᵥ y
  proof: (vle_total _ _).resolve_right h

中文:
引理 vlt.vle
  条件: (h : x <ᵥ y)
  结论: x <=ᵥ y
  证明: (vle_total _ _).resolve_right h

Depends on / 依赖: resolve_right, vle_total
-/
lemma vlt.vle (h : x <ᵥ y) : x <=ᵥ y :=
  (vle_total _ _).resolve_right h

/--
lemma `vlt.trans` / 引理 `vlt.trans`

English:
lemma vlt.trans
  given: (h1 : x <ᵥ y) (h2 : y <ᵥ z)
  statement: x <ᵥ z
  proof: h1.trans_vle h2.vle

中文:
引理 vlt.trans
  条件: (h1 : x <ᵥ y) (h2 : y <ᵥ z)
  结论: x <ᵥ z
  证明: h1.trans_vle h2.vle

Depends on / 依赖: h1.trans_vle, h2.vle, trans_vle
-/
lemma vlt.trans (h1 : x <ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  h1.trans_vle h2.vle

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vlt vlt vlt
  body: vlt.trans

中文:
实例 :
  签名: @Trans R R R vlt vlt vlt
  定义体: vlt.trans

Depends on / 依赖: vlt.trans
-/
instance : @Trans R R R vlt vlt vlt where
  trans := vlt.trans

/--
lemma `vlt_of_veq_of_vlt` / 引理 `vlt_of_veq_of_vlt`

English:
lemma vlt_of_veq_of_vlt
  given: (h1 : x =ᵥ y) (h2 : y <ᵥ z)
  statement: x <ᵥ z
  proof: h1.vle.trans_vlt h2

中文:
引理 vlt_of_veq_of_vlt
  条件: (h1 : x =ᵥ y) (h2 : y <ᵥ z)
  结论: x <ᵥ z
  证明: h1.vle.trans_vlt h2

Depends on / 依赖: h1.vle.trans_vlt, trans_vlt
-/
lemma vlt_of_veq_of_vlt (h1 : x =ᵥ y) (h2 : y <ᵥ z) : x <ᵥ z :=
  h1.vle.trans_vlt h2

/--
lemma `vlt_of_vlt_of_veq` / 引理 `vlt_of_vlt_of_veq`

English:
lemma vlt_of_vlt_of_veq
  given: (h1 : x <ᵥ y) (h2 : y =ᵥ z)
  statement: x <ᵥ z
  proof: h1.trans_vle h2.vle

中文:
引理 vlt_of_vlt_of_veq
  条件: (h1 : x <ᵥ y) (h2 : y =ᵥ z)
  结论: x <ᵥ z
  证明: h1.trans_vle h2.vle

Depends on / 依赖: h1.trans_vle, h2.vle, trans_vle
-/
lemma vlt_of_vlt_of_veq (h1 : x <ᵥ y) (h2 : y =ᵥ z) : x <ᵥ z :=
  h1.trans_vle h2.vle

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R veq vlt vlt
  body: vlt_of_veq_of_vlt

中文:
实例 :
  签名: @Trans R R R veq vlt vlt
  定义体: vlt_of_veq_of_vlt

Depends on / 依赖: vlt_of_veq_of_vlt
-/
instance : @Trans R R R veq vlt vlt where
  trans := vlt_of_veq_of_vlt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans R R R vlt veq vlt
  body: vlt_of_vlt_of_veq

@[gcongr]

中文:
实例 :
  签名: @Trans R R R vlt veq vlt
  定义体: vlt_of_vlt_of_veq

@[gcongr]

Depends on / 依赖: vlt_of_vlt_of_veq
-/
instance : @Trans R R R vlt veq vlt where
  trans := vlt_of_vlt_of_veq

@[gcongr]
/--
theorem `vlt_imp_vlt_of_vle_of_vle` / 定理 `vlt_imp_vlt_of_vle_of_vle`

English:
theorem vlt_imp_vlt_of_vle_of_vle
  given: (h1 : x <=ᵥ x') (h2 : y' <=ᵥ y)
  statement: x' <ᵥ y' -> x <ᵥ y
  proof: (h1.trans_vlt <| ·.trans_vle h2)

@[gcongr]

中文:
定理 vlt_imp_vlt_of_vle_of_vle
  条件: (h1 : x <=ᵥ x') (h2 : y' <=ᵥ y)
  结论: x' <ᵥ y' -> x <ᵥ y
  证明: (h1.trans_vlt <| ·.trans_vle h2)

@[gcongr]

Depends on / 依赖: h1.trans_vlt, trans_vle, trans_vlt
-/
theorem vlt_imp_vlt_of_vle_of_vle (h1 : x <=ᵥ x') (h2 : y' <=ᵥ y) : x' <ᵥ y' -> x <ᵥ y :=
  (h1.trans_vlt <| ·.trans_vle h2)

@[gcongr]
/--
lemma `mul_vle_mul` / 引理 `mul_vle_mul`

English:
lemma mul_vle_mul
  given: {x x' y y' : R} (h1 : x <=ᵥ y) (h2 : x' <=ᵥ y')
  statement: x * x' <=ᵥ y * y'
  proof: (mul_vle_mul_left h1 _).trans (mul_vle_mul_right h2 _)

中文:
引理 mul_vle_mul
  条件: {x x' y y' : R} (h1 : x <=ᵥ y) (h2 : x' <=ᵥ y')
  结论: x * x' <=ᵥ y * y'
  证明: (mul_vle_mul_left h1 _).trans (mul_vle_mul_right h2 _)

Depends on / 依赖: mul_vle_mul_left, mul_vle_mul_right
-/
lemma mul_vle_mul {x x' y y' : R} (h1 : x <=ᵥ y) (h2 : x' <=ᵥ y') : x * x' <=ᵥ y * y' :=
  (mul_vle_mul_left h1 _).trans (mul_vle_mul_right h2 _)

/--
lemma `mul_vle_mul_iff_left` / 引理 `mul_vle_mul_iff_left`

English:
lemma mul_vle_mul_iff_left
  given: (hz : 0 <ᵥ z)
  statement: x * z <=ᵥ y * z ↔ x <=ᵥ y
  proof: ⟨vle_mul_cancel hz, (mul_vle_mul_left · _)⟩

中文:
引理 mul_vle_mul_iff_left
  条件: (hz : 0 <ᵥ z)
  结论: x * z <=ᵥ y * z ↔ x <=ᵥ y
  证明: ⟨vle_mul_cancel hz, (mul_vle_mul_left · _)⟩
-/
@[simp] lemma mul_vle_mul_iff_left (hz : 0 <ᵥ z) : x * z <=ᵥ y * z ↔ x <=ᵥ y :=
  ⟨vle_mul_cancel hz, (mul_vle_mul_left · _)⟩

/--
lemma `mul_vle_mul_iff_right` / 引理 `mul_vle_mul_iff_right`

English:
lemma mul_vle_mul_iff_right
  given: (hx : 0 <ᵥ x)
  statement: x * y <=ᵥ x * z ↔ y <=ᵥ z
  proof: by
  refine ⟨fun h => ?_ , fun h => ?_⟩
  · grw [veq_mul_comm, veq_mul_comm (x := x)] at h
    rwa [mul_vle_mul_iff_left hx] at h
  · grw [veq_mul_comm, veq_mul_comm (x := x)]
    rwa [mul_vle_mul_iff_left hx]

中文:
引理 mul_vle_mul_iff_right
  条件: (hx : 0 <ᵥ x)
  结论: x * y <=ᵥ x * z ↔ y <=ᵥ z
  证明: by
  refine ⟨fun h => ?_ , fun h => ?_⟩
  · grw [veq_mul_comm, veq_mul_comm (x := x)] at h
    rwa [mul_vle_mul_iff_left hx] at h
  · grw [veq_mul_comm, veq_mul_comm (x := x)]
    rwa [mul_vle_mul_iff_left hx]
-/
@[simp] lemma mul_vle_mul_iff_right (hx : 0 <ᵥ x) : x * y <=ᵥ x * z ↔ y <=ᵥ z := by
  refine ⟨fun h => ?_ , fun h => ?_⟩
  · grw [veq_mul_comm, veq_mul_comm (x := x)] at h
    rwa [mul_vle_mul_iff_left hx] at h
  · grw [veq_mul_comm, veq_mul_comm (x := x)]
    rwa [mul_vle_mul_iff_left hx]

/--
lemma `mul_vlt_mul_iff_left` / 引理 `mul_vlt_mul_iff_left`

English:
lemma mul_vlt_mul_iff_left
  given: (hz : 0 <ᵥ z)
  statement: x * z <ᵥ y * z ↔ x <ᵥ y
  proof: (mul_vle_mul_iff_left hz).not

@[gcongr] alias ⟨_, mul_vlt_mul_left⟩ := mul_vlt_mul_iff_left
@[deprecated (since := "2026-01-06")] alias vlt_mul_right := mul_vlt_mul_left

中文:
引理 mul_vlt_mul_iff_left
  条件: (hz : 0 <ᵥ z)
  结论: x * z <ᵥ y * z ↔ x <ᵥ y
  证明: (mul_vle_mul_iff_left hz).not

@[gcongr] alias ⟨_, mul_vlt_mul_left⟩ := mul_vlt_mul_iff_left
@[deprecated (since := "2026-01-06")] alias vlt_mul_right := mul_vlt_mul_left
-/
@[simp] lemma mul_vlt_mul_iff_left (hz : 0 <ᵥ z) : x * z <ᵥ y * z ↔ x <ᵥ y :=
  (mul_vle_mul_iff_left hz).not

@[gcongr] alias ⟨_, mul_vlt_mul_left⟩ := mul_vlt_mul_iff_left
@[deprecated (since := "2026-01-06")] alias vlt_mul_right := mul_vlt_mul_left

/--
lemma `mul_vlt_mul_iff_right` / 引理 `mul_vlt_mul_iff_right`

English:
lemma mul_vlt_mul_iff_right
  given: (hx : 0 <ᵥ x)
  statement: x * y <ᵥ x * z ↔ y <ᵥ z
  proof: (mul_vle_mul_iff_right hx).not

@[gcongr] alias ⟨_, mul_vlt_mul_right⟩ := mul_vlt_mul_iff_right
@[deprecated (since := "2026-01-06")] alias vlt_mul_left := mul_vlt_mul_right

@[gcongr]

中文:
引理 mul_vlt_mul_iff_right
  条件: (hx : 0 <ᵥ x)
  结论: x * y <ᵥ x * z ↔ y <ᵥ z
  证明: (mul_vle_mul_iff_right hx).not

@[gcongr] alias ⟨_, mul_vlt_mul_right⟩ := mul_vlt_mul_iff_right
@[deprecated (since := "2026-01-06")] alias vlt_mul_left := mul_vlt_mul_right

@[gcongr]
-/
@[simp] lemma mul_vlt_mul_iff_right (hx : 0 <ᵥ x) : x * y <ᵥ x * z ↔ y <ᵥ z :=
  (mul_vle_mul_iff_right hx).not

@[gcongr] alias ⟨_, mul_vlt_mul_right⟩ := mul_vlt_mul_iff_right
@[deprecated (since := "2026-01-06")] alias vlt_mul_left := mul_vlt_mul_right

@[gcongr]
/--
lemma `mul_veq_mul` / 引理 `mul_veq_mul`

English:
lemma mul_veq_mul
  given: (h1 : x =ᵥ y) (h2 : x' =ᵥ y')
  statement: x * x' =ᵥ y * y'
  proof: ⟨mul_vle_mul h1.vle h2.vle, mul_vle_mul h1.vge h2.vge⟩

中文:
引理 mul_veq_mul
  条件: (h1 : x =ᵥ y) (h2 : x' =ᵥ y')
  结论: x * x' =ᵥ y * y'
  证明: ⟨mul_vle_mul h1.vle h2.vle, mul_vle_mul h1.vge h2.vge⟩

Depends on / 依赖: h1.vge, h1.vle, h2.vge, h2.vle, mul_vle_mul
-/
lemma mul_veq_mul (h1 : x =ᵥ y) (h2 : x' =ᵥ y') : x * x' =ᵥ y * y' :=
  ⟨mul_vle_mul h1.vle h2.vle, mul_vle_mul h1.vge h2.vge⟩

/--
lemma `veq_mul_right_comm` / 引理 `veq_mul_right_comm`

English:
lemma veq_mul_right_comm
  given: (x y z : R)
  statement: x * y * z =ᵥ x * z * y
  proof: by
  grw [mul_assoc, veq_mul_comm y, mul_assoc]

中文:
引理 veq_mul_right_comm
  条件: (x y z : R)
  结论: x * y * z =ᵥ x * z * y
  证明: by
  grw [mul_assoc, veq_mul_comm y, mul_assoc]

Depends on / 依赖: mul_assoc, veq_mul_comm
-/
lemma veq_mul_right_comm (x y z : R) : x * y * z =ᵥ x * z * y := by
  grw [mul_assoc, veq_mul_comm y, mul_assoc]

/--
lemma `veq_mul_mul_mul_comm` / 引理 `veq_mul_mul_mul_comm`

English:
lemma veq_mul_mul_mul_comm
  given: (x y z w : R)
  statement: x * y * (z * w) =ᵥ x * z * (y * w)
  proof: by
  grw [← mul_assoc, veq_mul_right_comm x, mul_assoc]

中文:
引理 veq_mul_mul_mul_comm
  条件: (x y z w : R)
  结论: x * y * (z * w) =ᵥ x * z * (y * w)
  证明: by
  grw [← mul_assoc, veq_mul_right_comm x, mul_assoc]

Depends on / 依赖: mul_assoc, veq_mul_right_comm
-/
lemma veq_mul_mul_mul_comm (x y z w : R) : x * y * (z * w) =ᵥ x * z * (y * w) := by
  grw [← mul_assoc, veq_mul_right_comm x, mul_assoc]

/--
theorem `vle_add_cases` / 定理 `vle_add_cases`

English:
theorem vle_add_cases
  given: (x y : R)
  statement: x + y <=ᵥ x ∨ x + y <=ᵥ y
  proof: (vle_total y x).imp (fun h => vle_add .rfl h) (fun h => vle_add h .rfl)

中文:
定理 vle_add_cases
  条件: (x y : R)
  结论: x + y <=ᵥ x ∨ x + y <=ᵥ y
  证明: (vle_total y x).imp (fun h => vle_add .rfl h) (fun h => vle_add h .rfl)

Depends on / 依赖: vle_add, vle_total
-/
theorem vle_add_cases (x y : R) : x + y <=ᵥ x ∨ x + y <=ᵥ y :=
  (vle_total y x).imp (fun h => vle_add .rfl h) (fun h => vle_add h .rfl)

/--
lemma `zero_vlt_mul` / 引理 `zero_vlt_mul`

English:
lemma zero_vlt_mul
  given: (hx : 0 <ᵥ x) (hy : 0 <ᵥ y)
  statement: 0 <ᵥ x * y
  proof: by
  contrapose hy
  rw [not_vlt] at hy ⊢
  grw [show (0 : R) = x * 0 by simp, veq_mul_comm, veq_mul_comm x] at hy
  exact vle_mul_cancel hx hy

中文:
引理 zero_vlt_mul
  条件: (hx : 0 <ᵥ x) (hy : 0 <ᵥ y)
  结论: 0 <ᵥ x * y
  证明: by
  contrapose hy
  rw [not_vlt] at hy ⊢
  grw [show (0 : R) = x * 0 by simp, veq_mul_comm, veq_mul_comm x] at hy
  exact vle_mul_cancel hx hy
-/
@[simp] lemma zero_vlt_mul (hx : 0 <ᵥ x) (hy : 0 <ᵥ y) : 0 <ᵥ x * y := by
  contrapose hy
  rw [not_vlt] at hy ⊢
  grw [show (0 : R) = x * 0 by simp, veq_mul_comm, veq_mul_comm x] at hy
  exact vle_mul_cancel hx hy

variable (R) in
/--
Definition of `posSubmonoid` / `posSubmonoid` 的定义

English:
definition posSubmonoid
  signature: : Submonoid R where
  body: { x | 0 <ᵥ x }
  mul_mem' := zero_vlt_mul
  one_mem' := zero_vlt_one

中文:
定义 posSubmonoid
  签名: : Submonoid R where
  定义体: { x | 0 <ᵥ x }
  mul_mem' := zero_vlt_mul
  one_mem' := zero_vlt_one
-/
def posSubmonoid : Submonoid R where
  carrier := { x | 0 <ᵥ x }
  mul_mem' := zero_vlt_mul
  one_mem' := zero_vlt_one

/--
lemma `zero_vlt_coe_posSubmonoid` / 引理 `zero_vlt_coe_posSubmonoid`

English:
lemma zero_vlt_coe_posSubmonoid
  given: (x : posSubmonoid R)
  statement: 0 <ᵥ x.val
  proof: x.prop

@[simp]

中文:
引理 zero_vlt_coe_posSubmonoid
  条件: (x : posSubmonoid R)
  结论: 0 <ᵥ x.val
  证明: x.prop

@[simp]
-/
@[simp] lemma zero_vlt_coe_posSubmonoid (x : posSubmonoid R) : 0 <ᵥ x.val := x.prop

@[simp]
/--
lemma `posSubmonoid_def` / 引理 `posSubmonoid_def`

English:
lemma posSubmonoid_def
  given: (x : R)
  statement: x in posSubmonoid R ↔ 0 <ᵥ x
  proof: Iff.rfl

中文:
引理 posSubmonoid_def
  条件: (x : R)
  结论: x in posSubmonoid R ↔ 0 <ᵥ x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma posSubmonoid_def (x : R) : x in posSubmonoid R ↔ 0 <ᵥ x := Iff.rfl

/--
lemma `right_cancel_posSubmonoid` / 引理 `right_cancel_posSubmonoid`

English:
lemma right_cancel_posSubmonoid
  given: (x y : R) (u : posSubmonoid R)
  proof: by simp

中文:
引理 right_cancel_posSubmonoid
  条件: (x y : R) (u : posSubmonoid R)
  证明: by simp
-/
lemma right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    x * u <=ᵥ y * u ↔ x <=ᵥ y := by simp

/--
lemma `left_cancel_posSubmonoid` / 引理 `left_cancel_posSubmonoid`

English:
lemma left_cancel_posSubmonoid
  given: (x y : R) (u : posSubmonoid R)
  proof: by simp

@[simp]

中文:
引理 left_cancel_posSubmonoid
  条件: (x y : R) (u : posSubmonoid R)
  证明: by simp

@[simp]
-/
lemma left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    u * x <=ᵥ u * y ↔ x <=ᵥ y := by simp

@[simp]
/--
lemma `val_posSubmonoid_ne_zero` / 引理 `val_posSubmonoid_ne_zero`

English:
lemma val_posSubmonoid_ne_zero
  given: (x : posSubmonoid R)
  statement: (x : R) != 0
  proof: by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose this
  simp [this]

中文:
引理 val_posSubmonoid_ne_zero
  条件: (x : posSubmonoid R)
  结论: (x : R) != 0
  证明: by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose this
  simp [this]

Depends on / 依赖: contrapose, posSubmonoid_def, x.prop
-/
lemma val_posSubmonoid_ne_zero (x : posSubmonoid R) : (x : R) != 0 := by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose this
  simp [this]

variable (R) in
/-- The setoid used to construct `ValueGroupWithZero R`. -/
@[instance_reducible]
/--
Definition of `valueSetoid` / `valueSetoid` 的定义

English:
definition valueSetoid
  signature: : Setoid (R × posSubmonoid R) where
  body: fun (x, s) (y, t) => x * t <=ᵥ y * s ∧ y * s <=ᵥ x * t
  iseqv := {
    refl ru := ⟨vle_refl _, vle_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := mul_vle_mul h1 (vle_refl ↑w)
        grw [veq_mul_right_comm (x :

中文:
定义 valueSetoid
  签名: : Setoid (R × posSubmonoid R) where
  定义体: fun (x, s) (y, t) => x * t <=ᵥ y * s ∧ y * s <=ᵥ x * t
  iseqv := {
    refl ru := ⟨vle_refl _, vle_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := mul_vle_mul h1 (vle_refl ↑w)
        grw [veq_mul_right_comm (x :
-/
def valueSetoid : Setoid (R × posSubmonoid R) where
  r := fun (x, s) (y, t) => x * t <=ᵥ y * s ∧ y * s <=ᵥ x * t
  iseqv := {
    refl ru := ⟨vle_refl _, vle_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := mul_vle_mul h1 (vle_refl ↑w)
        grw [veq_mul_right_comm (x := s)] at this
        have := vle_trans this (mul_vle_mul h3 (vle_refl _))
        grw [veq_mul_right_comm r, veq_mul_right_comm t] at this
        simpa using this
      · have := mul_vle_mul h4 (vle_refl ↑u)
        grw [veq_mul_right_comm s] at this
        have := vle_trans this (mul_vle_mul h2 (vle_refl _))
        grw [veq_mul_right_comm t, veq_mul_right_comm r] at this
        simpa using this
  }

variable (R) in
/--
Definition of `ValueGroupWithZero` / `ValueGroupWithZero` 的定义

English:
definition ValueGroupWithZero
  body: Quotient (valueSetoid R)

中文:
定义 ValueGroupWithZero
  定义体: Quotient (valueSetoid R)

Depends on / 依赖: Quotient, valueSetoid
-/
def ValueGroupWithZero := Quotient (valueSetoid R)

/-- Construct an element of the value group-with-zero from an element `r : R` and
  `y : posSubmonoid R`. This should be thought of as `v r / v y`. -/
protected
/--
Definition of `ValueGroupWithZero.mk` / `ValueGroupWithZero.mk` 的定义

English:
definition ValueGroupWithZero.mk
  signature: (x : R) (y : posSubmonoid R)
  body: Quotient.mk _ (x, y)

protected

中文:
定义 ValueGroupWithZero.mk
  签名: (x : R) (y : posSubmonoid R)
  定义体: Quotient.mk _ (x, y)

protected

Depends on / 依赖: Quotient, Quotient.mk
-/
def ValueGroupWithZero.mk (x : R) (y : posSubmonoid R) : ValueGroupWithZero R :=
  Quotient.mk _ (x, y)

protected
/--
theorem `ValueGroupWithZero.sound` / 定理 `ValueGroupWithZero.sound`

English:
theorem ValueGroupWithZero.sound
  statement: {t s : posSubmonoid R}
  proof: Quotient.sound ⟨h₁, h₂⟩

protected

中文:
定理 ValueGroupWithZero.sound
  结论: {t s : posSubmonoid R}
  证明: Quotient.sound ⟨h₁, h₂⟩

protected

Depends on / 依赖: Quotient, Quotient.sound
-/
theorem ValueGroupWithZero.sound {t s : posSubmonoid R}
    (h₁ : x * s <=ᵥ y * t) (h₂ : y * t <=ᵥ x * s) :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s :=
  Quotient.sound ⟨h₁, h₂⟩

protected
/--
theorem `ValueGroupWithZero.exact` / 定理 `ValueGroupWithZero.exact`

English:
theorem ValueGroupWithZero.exact
  statement: {t s : posSubmonoid R}
  proof: Quotient.exact h

protected

中文:
定理 ValueGroupWithZero.exact
  结论: {t s : posSubmonoid R}
  证明: Quotient.exact h

protected

Depends on / 依赖: Quotient, Quotient.exact
-/
theorem ValueGroupWithZero.exact {t s : posSubmonoid R}
    (h : ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s) :
    x * s <=ᵥ y * t ∧ y * t <=ᵥ x * s :=
  Quotient.exact h

protected
/--
theorem `ValueGroupWithZero.ind` / 定理 `ValueGroupWithZero.ind`

English:
theorem ValueGroupWithZero.ind
  statement: {motive : ValueGroupWithZero R -> Prop} (mk : forall x y, motive (.mk x y))
  proof: Quotient.ind (fun (x, y) => mk x y) t

中文:
定理 ValueGroupWithZero.ind
  结论: {motive : ValueGroupWithZero R -> 命题} (mk : 对任意 x y, motive (.mk x y))
  证明: Quotient.ind (fun (x, y) => mk x y) t

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem ValueGroupWithZero.ind {motive : ValueGroupWithZero R -> Prop} (mk : forall x y, motive (.mk x y))
    (t : ValueGroupWithZero R) : motive t :=
  Quotient.ind (fun (x, y) => mk x y) t

/-- Lifts a function `R → posSubmonoid R → α` to the value group-with-zero of `R`. -/
protected
/--
Definition of `ValueGroupWithZero.lift` / `ValueGroupWithZero.lift` 的定义

English:
definition ValueGroupWithZero.lift
  signature: {α : Sort*} (f : R -> posSubmonoid R -> α)
  body: Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected

中文:
定义 ValueGroupWithZero.lift
  签名: {α : Sort*} (f : R -> posSubmonoid R -> α)
  定义体: Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected

Depends on / 依赖: Quotient, Quotient.lift
-/
def ValueGroupWithZero.lift {α : Sort*} (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t)
    (t : ValueGroupWithZero R) : α :=
  Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected
/--
theorem `ValueGroupWithZero.lift_mk` / 定理 `ValueGroupWithZero.lift_mk`

English:
theorem ValueGroupWithZero.lift_mk
  statement: {α : Sort*} (f : R -> posSubmonoid R -> α)
  proof: rfl

中文:
定理 ValueGroupWithZero.lift_mk
  结论: {α : Sort*} (f : R -> posSubmonoid R -> α)
  证明: rfl
-/
theorem ValueGroupWithZero.lift_mk {α : Sort*} (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t)
    (x : R) (y : posSubmonoid R) : ValueGroupWithZero.lift f hf (.mk x y) = f x y := rfl

/-- Lifts a function `R → posSubmonoid R → R → posSubmonoid R → α` to
  the value group-with-zero of `R`. -/
protected
/--
Definition of `ValueGroupWithZero.lift₂` / `ValueGroupWithZero.lift₂` 的定义

English:
definition ValueGroupWithZero.lift₂
  signature: {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
  body: Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected

中文:
定义 ValueGroupWithZero.lift₂
  签名: {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
  定义体: Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected

Depends on / 依赖: Quotient, Quotient.lift
-/
def ValueGroupWithZero.lift₂ {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
    (hf : forall (x y z w : R) (t s u v : posSubmonoid R),
      x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> z * u <=ᵥ w * v -> w * v <=ᵥ z * u ->
      f x s z v = f y t w u)
    (t₁ : ValueGroupWithZero R) (t₂ : ValueGroupWithZero R) : α :=
  Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected
/--
lemma `ValueGroupWithZero.lift₂_mk` / 引理 `ValueGroupWithZero.lift₂_mk`

English:
lemma ValueGroupWithZero.lift₂_mk
  statement: {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
  proof: rfl

中文:
引理 ValueGroupWithZero.lift₂_mk
  结论: {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
  证明: rfl
-/
lemma ValueGroupWithZero.lift₂_mk {α : Sort*} (f : R -> posSubmonoid R -> R -> posSubmonoid R -> α)
    (hf : forall (x y z w : R) (t s u v : posSubmonoid R),
      x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> z * u <=ᵥ w * v -> w * v <=ᵥ z * u ->
      f x s z v = f y t w u)
    (x y : R) (z w : posSubmonoid R) :
    ValueGroupWithZero.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl

/--
theorem `ValueGroupWithZero.mk_eq_mk` / 定理 `ValueGroupWithZero.mk_eq_mk`

English:
theorem ValueGroupWithZero.mk_eq_mk
  given: {t s : posSubmonoid R}
  proof: Quotient.eq

中文:
定理 ValueGroupWithZero.mk_eq_mk
  条件: {t s : posSubmonoid R}
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem ValueGroupWithZero.mk_eq_mk {t s : posSubmonoid R} :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s ↔ x * s <=ᵥ y * t ∧ y * t <=ᵥ x * s :=
  Quotient.eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ValueGroupWithZero R)
  body: .mk 0 1

@[simp]

中文:
实例 :
  签名: Zero (ValueGroupWithZero R)
  定义体: .mk 0 1

@[simp]
-/
instance : Zero (ValueGroupWithZero R) where
  zero := .mk 0 1

@[simp]
/--
theorem `ValueGroupWithZero.mk_eq_zero` / 定理 `ValueGroupWithZero.mk_eq_zero`

English:
theorem ValueGroupWithZero.mk_eq_zero
  given: (x : R) (y : posSubmonoid R)
  proof: ⟨fun h => by simpa using ValueGroupWithZero.mk_eq_mk.mp h,
    fun h => ValueGroupWithZero.sound (by simpa using h) (by simp)⟩

@[simp]

中文:
定理 ValueGroupWithZero.mk_eq_zero
  条件: (x : R) (y : posSubmonoid R)
  证明: ⟨fun h => by simpa using ValueGroupWithZero.mk_eq_mk.mp h,
    fun h => ValueGroupWithZero.sound (by simpa using h) (by simp)⟩

@[simp]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.mk_eq_mk.mp, ValueGroupWithZero.sound, mk_eq_mk
-/
theorem ValueGroupWithZero.mk_eq_zero (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 0 ↔ x <=ᵥ 0 :=
  ⟨fun h => by simpa using ValueGroupWithZero.mk_eq_mk.mp h,
    fun h => ValueGroupWithZero.sound (by simpa using h) (by simp)⟩

@[simp]
/--
theorem `ValueGroupWithZero.mk_zero` / 定理 `ValueGroupWithZero.mk_zero`

English:
theorem ValueGroupWithZero.mk_zero
  given: (x : posSubmonoid R)
  statement: ValueGroupWithZero.mk 0 x = 0
  proof: (ValueGroupWithZero.mk_eq_zero 0 x).mpr .rfl

中文:
定理 ValueGroupWithZero.mk_zero
  条件: (x : posSubmonoid R)
  结论: ValueGroupWithZero.mk 0 x = 0
  证明: (ValueGroupWithZero.mk_eq_zero 0 x).mpr .rfl

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.mk_eq_zero, mk_eq_zero
-/
theorem ValueGroupWithZero.mk_zero (x : posSubmonoid R) : ValueGroupWithZero.mk 0 x = 0 :=
  (ValueGroupWithZero.mk_eq_zero 0 x).mpr .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (ValueGroupWithZero R)
  body: .mk 1 1

@[simp]

中文:
实例 :
  签名: One (ValueGroupWithZero R)
  定义体: .mk 1 1

@[simp]
-/
instance : One (ValueGroupWithZero R) where
  one := .mk 1 1

@[simp]
/--
theorem `ValueGroupWithZero.mk_self` / 定理 `ValueGroupWithZero.mk_self`

English:
theorem ValueGroupWithZero.mk_self
  given: (x : posSubmonoid R)
  statement: ValueGroupWithZero.mk (x : R) x = 1
  proof: ValueGroupWithZero.sound (by simp) (by simp)

@[simp]

中文:
定理 ValueGroupWithZero.mk_self
  条件: (x : posSubmonoid R)
  结论: ValueGroupWithZero.mk (x : R) x = 1
  证明: ValueGroupWithZero.sound (by simp) (by simp)

@[simp]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.sound
-/
theorem ValueGroupWithZero.mk_self (x : posSubmonoid R) : ValueGroupWithZero.mk (x : R) x = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
/--
theorem `ValueGroupWithZero.mk_one_one` / 定理 `ValueGroupWithZero.mk_one_one`

English:
theorem ValueGroupWithZero.mk_one_one
  statement: ValueGroupWithZero.mk (1 : R) 1 = 1
  proof: ValueGroupWithZero.sound (by simp) (by simp)

@[simp]

中文:
定理 ValueGroupWithZero.mk_one_one
  结论: ValueGroupWithZero.mk (1 : R) 1 = 1
  证明: ValueGroupWithZero.sound (by simp) (by simp)

@[simp]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.sound
-/
theorem ValueGroupWithZero.mk_one_one : ValueGroupWithZero.mk (1 : R) 1 = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
/--
theorem `ValueGroupWithZero.mk_eq_one` / 定理 `ValueGroupWithZero.mk_eq_one`

English:
theorem ValueGroupWithZero.mk_eq_one
  given: (x : R) (y : posSubmonoid R)
  proof: by
  simp [← mk_one_one, mk_eq_mk]

中文:
定理 ValueGroupWithZero.mk_eq_one
  条件: (x : R) (y : posSubmonoid R)
  证明: by
  simp [← mk_one_one, mk_eq_mk]

Depends on / 依赖: mk_eq_mk, mk_one_one
-/
theorem ValueGroupWithZero.mk_eq_one (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 1 ↔ x <=ᵥ y ∧ y <=ᵥ x := by
  simp [← mk_one_one, mk_eq_mk]

/--
theorem `ValueGroupWithZero.lift_zero` / 定理 `ValueGroupWithZero.lift_zero`

English:
theorem ValueGroupWithZero.lift_zero
  statement: {α : Sort*} (f : R -> posSubmonoid R -> α)
  proof: rfl

@[simp]

中文:
定理 ValueGroupWithZero.lift_zero
  结论: {α : Sort*} (f : R -> posSubmonoid R -> α)
  证明: rfl

@[simp]
-/
theorem ValueGroupWithZero.lift_zero {α : Sort*} (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t) :
    ValueGroupWithZero.lift f hf 0 = f 0 1 :=
  rfl

@[simp]
/--
theorem `ValueGroupWithZero.lift_one` / 定理 `ValueGroupWithZero.lift_one`

English:
theorem ValueGroupWithZero.lift_one
  statement: {α : Sort*} (f : R -> posSubmonoid R -> α)
  proof: rfl

中文:
定理 ValueGroupWithZero.lift_one
  结论: {α : Sort*} (f : R -> posSubmonoid R -> α)
  证明: rfl

Depends on / 依赖: arbitrarily, chosen
-/
theorem ValueGroupWithZero.lift_one {α : Sort*} (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t) :
    ValueGroupWithZero.lift f hf 1 = f 1 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (ValueGroupWithZero R)
  body: ValueGroupWithZero.lift₂ (fun a b c d => .mk (a * c) (b * d)) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroupWithZero.sound
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₁ h₃
    · grw [Submonoid.coe_mu

中文:
实例 :
  签名: Mul (ValueGroupWithZero R)
  定义体: ValueGroupWithZero.lift₂ (fun a b c d => .mk (a * c) (b * d)) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroupWithZero.sound
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₁ h₃
    · grw [Submonoid.coe_mu

Depends on / 依赖: Submonoid, Submonoid.coe_mul, ValueGroupWithZero, ValueGroupWithZero.lift, ValueGroupWithZero.sound, coe_mul, mul_vle_mul, veq_mul_mul_mul_comm
-/
instance : Mul (ValueGroupWithZero R) where
mul := ValueGroupWithZero.lift₂ (fun a b c d => .mk (a * c) (b * d)) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroupWithZero.sound
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₁ h₃
    · grw [Submonoid.coe_mul, Submonoid.coe_mul,
        veq_mul_mul_mul_comm x, veq_mul_mul_mul_comm y]
      exact mul_vle_mul h₂ h₄

@[simp]
/--
theorem `ValueGroupWithZero.mk_mul_mk` / 定理 `ValueGroupWithZero.mk_mul_mk`

English:
theorem ValueGroupWithZero.mk_mul_mk
  given: (a b : R) (c d : posSubmonoid R)
  proof: rfl

中文:
定理 ValueGroupWithZero.mk_mul_mk
  条件: (a b : R) (c d : posSubmonoid R)
  证明: rfl
-/
theorem ValueGroupWithZero.mk_mul_mk (a b : R) (c d : posSubmonoid R) :
    ValueGroupWithZero.mk a c * ValueGroupWithZero.mk b d = ValueGroupWithZero.mk (a * b) (c * d) :=
  rfl

/--
theorem `ValueGroupWithZero.lift_mul` / 定理 `ValueGroupWithZero.lift_mul`

English:
theorem ValueGroupWithZero.lift_mul
  statement: {α : Type*} [Mul α] (f : R -> posSubmonoid R -> α)
  proof: by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _

中文:
定理 ValueGroupWithZero.lift_mul
  结论: {α : 类型} [Mul α] (f : R -> posSubmonoid R -> α)
  证明: by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind
-/
theorem ValueGroupWithZero.lift_mul {α : Type*} [Mul α] (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t)
    (hdist : forall (a b r s), f (a * b) (r * s) = f a r * f b s)
    (a b : ValueGroupWithZero R) :
    ValueGroupWithZero.lift f hf (a * b) =
      ValueGroupWithZero.lift f hf a * ValueGroupWithZero.lift f hf b := by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero (ValueGroupWithZero R)
  body: by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp [mul_assoc]
one_mul := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.mk_one_one]
mul_one := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.m

中文:
实例 :
  签名: CommMonoidWithZero (ValueGroupWithZero R)
  定义体: by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp [mul_assoc]
one_mul := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.mk_one_one]
mul_one := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.m

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind, ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_one_one, ValueGroupWithZero.mk_zer, ValueGroupWithZero.mk_zero, mk_mul_mk, mk_one_one, mk_zer, mk_zero, mul_assoc, mul_one, mul_zero, one_mul, zero_mul
-/
instance : CommMonoidWithZero (ValueGroupWithZero R) where
  mul_assoc a b c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp [mul_assoc]
one_mul := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.mk_one_one]
mul_one := ValueGroupWithZero.ind by simp [← ValueGroupWithZero.mk_one_one]
zero_mul := ValueGroupWithZero.ind fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_mul_mk]
    simp
mul_zero := ValueGroupWithZero.ind fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_mul_mk]
    simp
  mul_comm a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    apply ValuativeRel.ValueGroupWithZero.sound <;>
    · simp only [Submonoid.coe_mul]
      nth_grw 2 [veq_mul_comm]
      nth_grw 6 [veq_mul_comm]
npow n := ValueGroupWithZero.lift (fun a b => ValueGroupWithZero.mk (a ^ n) (b ^ n)) by
    intro x y t s h₁ h₂
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, ← ValueGroupWithZero.mk_mul_mk, ih]
      apply congrArg (_ * ·)
      exact ValueGroupWithZero.sound h₁ h₂
  npow_zero := ValueGroupWithZero.ind (by simp_rw [HPow.hPow, Pow.pow]; simp)
  npow_succ n := ValueGroupWithZero.ind (by simp_rw [HPow.hPow, Pow.pow]; simp [pow_succ])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (ValueGroupWithZero R)
  body: ValueGroupWithZero.lift₂ (fun a s b t => a * t <=ᵥ b * s) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w <=ᵥ 0 <;> by_cases hz : z <=ᵥ 0
    · refine propext ⟨fun h => vle_trans ?_ (zero_vle _), fun h => vle_trans ?_ (zero_vle _)⟩
      · apply vle_mul_cancel (s * v).prop
        grw [

中文:
实例 :
  签名: LE (ValueGroupWithZero R)
  定义体: ValueGroupWithZero.lift₂ (fun a s b t => a * t <=ᵥ b * s) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w <=ᵥ 0 <;> by_cases hz : z <=ᵥ 0
    · refine propext ⟨fun h => vle_trans ?_ (zero_vle _), fun h => vle_trans ?_ (zero_vle _)⟩
      · apply vle_mul_cancel (s * v).prop
        grw [

Depends on / 依赖: Submonoid, Submonoid.coe_mul, ValueGroupWithZero, ValueGroupWithZero.lift, coe_mul, mul_assoc, mul_vle_mul_left, propext, veq_mul_right_comm, vle_mul_cancel, vle_trans, zero_vle
-/
instance : LE (ValueGroupWithZero R) where
le := ValueGroupWithZero.lift₂ (fun a s b t => a * t <=ᵥ b * s) by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w <=ᵥ 0 <;> by_cases hz : z <=ᵥ 0
    · refine propext ⟨fun h => vle_trans ?_ (zero_vle _), fun h => vle_trans ?_ (zero_vle _)⟩
      · apply vle_mul_cancel (s * v).prop
        grw [veq_mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply (mul_vle_mul_left (mul_vle_mul_left h₂ v) u).trans
        grw [veq_mul_right_comm x]
        apply (mul_vle_mul_left (mul_vle_mul_left h t) u).trans
        apply vle_trans (mul_vle_mul_left (mul_vle_mul_left (mul_vle_mul_left hz s) t) u)
        simp
      · apply vle_mul_cancel (t * u).prop
        grw [veq_mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply (mul_vle_mul_left (mul_vle_mul_left h₁ u) v).trans
        grw [veq_mul_right_comm y]
        apply (mul_vle_mul_left (mul_vle_mul_left h s) v).trans
        apply vle_trans (mul_vle_mul_left (mul_vle_mul_left (mul_vle_mul_left hw t) s) v)
        simp
    · absurd hz
      apply vle_mul_cancel u.prop
      simpa using h₃.trans (mul_vle_mul_left hw v)
    · absurd hw
      apply vle_mul_cancel v.prop
      simpa using h₄.trans (mul_vle_mul_left hz u)
    · refine propext ⟨fun h => ?_, fun h => ?_⟩
      · apply vle_mul_cancel s.prop
        apply vle_mul_cancel hz
        calc y * u * s * z
          _ =ᵥ y * s * (z * u) := by grw [veq_mul_comm z, veq_mul_mul_mul_comm, mul_assoc]
          _ <=ᵥ x * t * (w * v) := by gcongr
          _ =ᵥ x * v * (t * w) := by grw [veq_mul_comm w, veq_mul_mul_mul_comm, mul_assoc]
          _ <=ᵥ z * s * (t * w) := by gcongr
          _ =ᵥ w * t * s * z := by grw [veq_mul_comm, veq_mul_comm _ w, veq_mul_comm z, ← mul_assoc]
      · apply vle_mul_cancel t.prop
        apply vle_mul_cancel hw
        calc x * v * t * w
          _ =ᵥ x * t * (w * v) := by grw [veq_mul_comm w, veq_mul_mul_mul_comm, mul_assoc]
          _ <=ᵥ y * s * (z * u) := by gcongr
          _ =ᵥ y * u * (s * z) := by grw [veq_mul_comm z, veq_mul_mul_mul_comm, mul_assoc]
          _ <=ᵥ w * t * (s * z) := by gcongr
          _ =ᵥ z * s * t * w := by grw [veq_mul_comm, veq_mul_comm _ z, veq_mul_comm w, ← mul_assoc]

@[simp]
/--
theorem `ValueGroupWithZero.mk_le_mk` / 定理 `ValueGroupWithZero.mk_le_mk`

English:
theorem ValueGroupWithZero.mk_le_mk
  given: (x y : R) (t s : posSubmonoid R)
  proof: Iff.rfl

中文:
定理 ValueGroupWithZero.mk_le_mk
  条件: (x y : R) (t s : posSubmonoid R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ValueGroupWithZero.mk_le_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t <= ValueGroupWithZero.mk y s ↔ x * s <=ᵥ y * t := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (ValueGroupWithZero R)
  body: ValueGroupWithZero.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroupWithZero.ind with | mk a₁ a₂
    induction b using ValueGroupWithZero.ind with | mk b₁ b₂
    induction c using ValueGroupWithZero.ind with | mk c₁ c₂
    rw [ValueGroupWithZero.mk_le_mk] at hab hbc

中文:
实例 :
  签名: LinearOrder (ValueGroupWithZero R)
  定义体: ValueGroupWithZero.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroupWithZero.ind with | mk a₁ a₂
    induction b using ValueGroupWithZero.ind with | mk b₁ b₂
    induction c using ValueGroupWithZero.ind with | mk c₁ c₂
    rw [ValueGroupWithZero.mk_le_mk] at hab hbc

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind
-/
instance : LinearOrder (ValueGroupWithZero R) where
  le_refl := ValueGroupWithZero.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroupWithZero.ind with | mk a₁ a₂
    induction b using ValueGroupWithZero.ind with | mk b₁ b₂
    induction c using ValueGroupWithZero.ind with | mk c₁ c₂
    rw [ValueGroupWithZero.mk_le_mk] at hab hbc ⊢
    apply vle_mul_cancel b₂.prop
    calc a₁ * c₂ * b₂
      _ =ᵥ a₁ * b₂ * c₂ := by grw [veq_mul_right_comm]
      _ <=ᵥ b₁ * a₂ * c₂ := mul_vle_mul_left hab _
      _ =ᵥ b₁ * c₂ * a₂ := by grw [veq_mul_right_comm]
      _ <=ᵥ c₁ * b₂ * a₂ := mul_vle_mul_left hbc _
      _ =ᵥ c₁ * a₂ * b₂ := by grw [veq_mul_right_comm]
  le_antisymm a b hab hba := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    exact ValueGroupWithZero.sound hab hba
  le_total a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    rw [ValueGroupWithZero.mk_le_mk]; rw [ValueGroupWithZero.mk_le_mk]
    apply vle_total
  toDecidableLE := Classical.decRel LE.le

@[simp]
/--
theorem `ValueGroupWithZero.mk_lt_mk` / 定理 `ValueGroupWithZero.mk_lt_mk`

English:
theorem ValueGroupWithZero.mk_lt_mk
  given: (x y : R) (t s : posSubmonoid R)
  proof: by
  rw [lt_iff_not_ge]; rw [← not_vle]; rw [mk_le_mk]

@[simp]

中文:
定理 ValueGroupWithZero.mk_lt_mk
  条件: (x y : R) (t s : posSubmonoid R)
  证明: by
  rw [lt_iff_not_ge]; rw [← not_vle]; rw [mk_le_mk]

@[simp]

Depends on / 依赖: lt_iff_not_ge, mk_le_mk, not_vle
-/
theorem ValueGroupWithZero.mk_lt_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t < ValueGroupWithZero.mk y s ↔ x * s <ᵥ y * t := by
  rw [lt_iff_not_ge]; rw [← not_vle]; rw [mk_le_mk]

@[simp]
/--
lemma `ValueGroupWithZero.mk_pos` / 引理 `ValueGroupWithZero.mk_pos`

English:
lemma ValueGroupWithZero.mk_pos
  given: {s : posSubmonoid R}
  proof: by rw [← mk_zero 1]; simp [-mk_zero]

中文:
引理 ValueGroupWithZero.mk_pos
  条件: {s : posSubmonoid R}
  证明: by rw [← mk_zero 1]; simp [-mk_zero]

Depends on / 依赖: mk_zero
-/
lemma ValueGroupWithZero.mk_pos {s : posSubmonoid R} :
    0 < ValueGroupWithZero.mk x s ↔ 0 <ᵥ x := by rw [← mk_zero 1]; simp [-mk_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (ValueGroupWithZero R)
  body: 0

中文:
实例 :
  签名: Bot (ValueGroupWithZero R)
  定义体: 0
-/
instance : Bot (ValueGroupWithZero R) where
  bot := 0

/--
theorem `ValueGroupWithZero.bot_eq_zero` / 定理 `ValueGroupWithZero.bot_eq_zero`

English:
theorem ValueGroupWithZero.bot_eq_zero
  statement: (⊥ : ValueGroupWithZero R) = 0
  proof: rfl

中文:
定理 ValueGroupWithZero.bot_eq_zero
  结论: (⊥ : ValueGroupWithZero R) = 0
  证明: rfl
-/
theorem ValueGroupWithZero.bot_eq_zero : (⊥ : ValueGroupWithZero R) = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (ValueGroupWithZero R)
  body: ValueGroupWithZero.ind fun x y => by
    rw [ValueGroupWithZero.bot_eq_zero]; rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_le_mk]
    simp

中文:
实例 :
  签名: OrderBot (ValueGroupWithZero R)
  定义体: ValueGroupWithZero.ind fun x y => by
    rw [ValueGroupWithZero.bot_eq_zero]; rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_le_mk]
    simp

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.bot_eq_zero, ValueGroupWithZero.ind, ValueGroupWithZero.mk_le_mk, ValueGroupWithZero.mk_zero, bot_eq_zero, mk_le_mk, mk_zero
-/
instance : OrderBot (ValueGroupWithZero R) where
  bot_le := ValueGroupWithZero.ind fun x y => by
    rw [ValueGroupWithZero.bot_eq_zero]; rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_le_mk]
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedMonoid (ValueGroupWithZero R)
  body: by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp only [ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_le_mk, Submonoid.coe_mul]
    nth_grw 1 [veq_mul_mul_mul_comm]
    nth_grw 2 [veq_mul_mul_mul_c

中文:
实例 :
  签名: IsOrderedMonoid (ValueGroupWithZero R)
  定义体: by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp only [ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_le_mk, Submonoid.coe_mul]
    nth_grw 1 [veq_mul_mul_mul_comm]
    nth_grw 2 [veq_mul_mul_mul_c

Depends on / 依赖: Submonoid, Submonoid.coe_mul, ValueGroupWithZero, ValueGroupWithZero.ind, ValueGroupWithZero.mk_le_mk, ValueGroupWithZero.mk_mul_mk, coe_mul, mk_le_mk, mk_mul_mk, mul_vle_mul_left, nth_grw, veq_mul_mul_mul_comm
-/
instance : IsOrderedMonoid (ValueGroupWithZero R) where
  mul_le_mul_left a b hab c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp only [ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_le_mk, Submonoid.coe_mul]
    nth_grw 1 [veq_mul_mul_mul_comm]
    nth_grw 2 [veq_mul_mul_mul_comm]
    exact mul_vle_mul_left hab _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (ValueGroupWithZero R)
  body: ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x <=ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x <=ᵥ 0 <;> by_cases hy : y <=ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply vle_mul_cancel s.prop
      simpa using vle_trans h₂ (mul_vle_mul_left

中文:
实例 :
  签名: Inv (ValueGroupWithZero R)
  定义体: ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x <=ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x <=ᵥ 0 <;> by_cases hy : y <=ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply vle_mul_cancel s.prop
      simpa using vle_trans h₂ (mul_vle_mul_left

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.lift, ValueGroupWithZero.sound, absurd, classical, dif_neg, mul_vle_mul_left, s.prop, t.prop, veq_mul, veq_mul_comm, vle_mul_cancel, vle_trans
-/
instance : Inv (ValueGroupWithZero R) where
  inv := ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x <=ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x <=ᵥ 0 <;> by_cases hy : y <=ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply vle_mul_cancel s.prop
      simpa using vle_trans h₂ (mul_vle_mul_left hx t)
    · absurd hx
      apply vle_mul_cancel t.prop
      simpa using vle_trans h₁ (mul_vle_mul_left hy s)
    · simp only [dif_neg hx, dif_neg hy]
      apply ValueGroupWithZero.sound
      · grw [veq_mul_comm, veq_mul_comm _ x]
        simpa using h₂
      · grw [veq_mul_comm, veq_mul_comm _ y]
        simpa [mul_comm] using h₁

@[simp]
/--
theorem `ValueGroupWithZero.inv_mk` / 定理 `ValueGroupWithZero.inv_mk`

English:
theorem ValueGroupWithZero.inv_mk
  given: (x : R) (y : posSubmonoid R) (hx : ¬x <=ᵥ 0)
  proof: dif_neg hx

中文:
定理 ValueGroupWithZero.inv_mk
  条件: (x : R) (y : posSubmonoid R) (hx : ¬x <=ᵥ 0)
  证明: dif_neg hx

Depends on / 依赖: dif_neg
-/
theorem ValueGroupWithZero.inv_mk (x : R) (y : posSubmonoid R) (hx : ¬x <=ᵥ 0) :
    (ValueGroupWithZero.mk x y)⁻¹ = ValueGroupWithZero.mk (y : R) ⟨x, hx⟩ := dif_neg hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedCommGroupWithZero (ValueGroupWithZero R)
  body: bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroupWithZero.mk_zero 1]; rw [← ValueGroupWithZero.mk_one_one]; rw [ValueGroupWithZero.mk_le_mk] at h
    simp [not_vle_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero

中文:
实例 :
  签名: LinearOrderedCommGroupWithZero (ValueGroupWithZero R)
  定义体: bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroupWithZero.mk_zero 1]; rw [← ValueGroupWithZero.mk_one_one]; rw [ValueGroupWithZero.mk_le_mk] at h
    simp [not_vle_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero

Depends on / 依赖: bot_le
-/
instance : LinearOrderedCommGroupWithZero (ValueGroupWithZero R) where
  isBot_zero _ := bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroupWithZero.mk_zero 1]; rw [← ValueGroupWithZero.mk_one_one]; rw [ValueGroupWithZero.mk_le_mk] at h
    simp [not_vle_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero.ind fun x y h => by
    rw [ne_eq]; rw [← ValueGroupWithZero.mk_zero 1]; rw [ValueGroupWithZero.mk_eq_mk] at h
    simp only [Submonoid.coe_one, mul_one, zero_mul, zero_vle, and_true] at h
    grw [ValueGroupWithZero.inv_mk x y h, ← ValueGroupWithZero.mk_one_one,
      ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_eq_mk, veq_mul_comm x]
    simp
  mul_lt_mul_of_pos_left := ValueGroupWithZero.ind fun a x ha => ValueGroupWithZero.ind fun b y =>
    ValueGroupWithZero.ind fun c z hbc => by
      simp only [ValueGroupWithZero.mk_lt_mk,
        ValueGroupWithZero.mk_mul_mk, Submonoid.coe_mul]
      grw [veq_mul_mul_mul_comm, veq_mul_mul_mul_comm _ c]
      simp_all

section Valuation

variable {R : Type*} [Ring R] [ValuativeRel R] {x : R}

variable (R) in
/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation R (ValueGroupWithZero R) where
  body: ValueGroupWithZero.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [vle_add_cases]

中文:
定义 valuation
  签名: : Valuation R (ValueGroupWithZero R) where
  定义体: ValueGroupWithZero.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [vle_add_cases]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.mk
-/
def valuation : Valuation R (ValueGroupWithZero R) where
  toFun r := ValueGroupWithZero.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [vle_add_cases]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (valuation R).Compatible
  body: by simp [valuation]

@[simp]

中文:
实例 :
  签名: (valuation R).Compatible
  定义体: by simp [valuation]

@[simp]

Depends on / 依赖: valuation
-/
instance : (valuation R).Compatible where
  vle_iff_le _ _ := by simp [valuation]

@[simp]
/--
lemma `ValueGroupWithZero.lift_valuation` / 引理 `ValueGroupWithZero.lift_valuation`

English:
lemma ValueGroupWithZero.lift_valuation
  statement: {α : Sort*} (f : R -> posSubmonoid R -> α)
  proof: rfl

中文:
引理 ValueGroupWithZero.lift_valuation
  结论: {α : Sort*} (f : R -> posSubmonoid R -> α)
  证明: rfl
-/
lemma ValueGroupWithZero.lift_valuation {α : Sort*} (f : R -> posSubmonoid R -> α)
    (hf : forall (x y : R) (t s : posSubmonoid R), x * t <=ᵥ y * s -> y * s <=ᵥ x * t -> f x s = f y t)
    (x : R) :
    ValueGroupWithZero.lift f hf (valuation R x) = f x 1 :=
  rfl

/--
lemma `valuation_eq_zero_iff` / 引理 `valuation_eq_zero_iff`

English:
lemma valuation_eq_zero_iff
  statement: valuation R x = 0 ↔ x <=ᵥ 0
  proof: ValueGroupWithZero.mk_eq_zero _ _

中文:
引理 valuation_eq_zero_iff
  结论: valuation R x = 0 ↔ x <=ᵥ 0
  证明: ValueGroupWithZero.mk_eq_zero _ _

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.mk_eq_zero, mk_eq_zero
-/
lemma valuation_eq_zero_iff : valuation R x = 0 ↔ x <=ᵥ 0 :=
  ValueGroupWithZero.mk_eq_zero _ _

/--
lemma `valuation_posSubmonoid_ne_zero` / 引理 `valuation_posSubmonoid_ne_zero`

English:
lemma valuation_posSubmonoid_ne_zero
  given: (x : posSubmonoid R)
  proof: by
  rw [ne_eq]; rw [valuation_eq_zero_iff]
  exact x.prop

中文:
引理 valuation_posSubmonoid_ne_zero
  条件: (x : posSubmonoid R)
  证明: by
  rw [ne_eq]; rw [valuation_eq_zero_iff]
  exact x.prop

Depends on / 依赖: ne_eq, valuation_eq_zero_iff, x.prop
-/
lemma valuation_posSubmonoid_ne_zero (x : posSubmonoid R) :
    valuation R (x : R) != 0 := by
  rw [ne_eq]; rw [valuation_eq_zero_iff]
  exact x.prop

/--
lemma `ValueGroupWithZero.mk_eq_div` / 引理 `ValueGroupWithZero.mk_eq_div`

English:
lemma ValueGroupWithZero.mk_eq_div
  given: (r : R) (s : posSubmonoid R)
  proof: by
  rw [eq_div_iff (valuation_posSubmonoid_ne_zero _)]
  simp [valuation, mk_eq_mk]

中文:
引理 ValueGroupWithZero.mk_eq_div
  条件: (r : R) (s : posSubmonoid R)
  证明: by
  rw [eq_div_iff (valuation_posSubmonoid_ne_zero _)]
  simp [valuation, mk_eq_mk]

Depends on / 依赖: eq_div_iff, mk_eq_mk, valuation, valuation_posSubmonoid_ne_zero
-/
lemma ValueGroupWithZero.mk_eq_div (r : R) (s : posSubmonoid R) :
    ValueGroupWithZero.mk r s = valuation R r / valuation R (s : R) := by
  rw [eq_div_iff (valuation_posSubmonoid_ne_zero _)]
  simp [valuation, mk_eq_mk]

/-- Construct a valuative relation on a ring using a valuation. -/
@[instance_reducible]
/--
Definition of `ofValuation` / `ofValuation` 的定义

English:
definition ofValuation
  body: v x <= v y
  vle_total x y := le_total (v x) (v y)
  vle_trans := le_trans
  vle_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  mul_vle_mul_left _ h := by simp only [map_mul]; gcongr
  vle_mul_cancel h0 h := by
    simp only [map_mul] at h
    apply le_of_mul_le_mul_right h
    simpa

中文:
定义 ofValuation
  定义体: v x <= v y
  vle_total x y := le_total (v x) (v y)
  vle_trans := le_trans
  vle_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  mul_vle_mul_left _ h := by simp only [map_mul]; gcongr
  vle_mul_cancel h0 h := by
    simp only [map_mul] at h
    apply le_of_mul_le_mul_right h
    simpa
-/
def ofValuation
    {S Γ : Type*} [Ring S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  vle x y := v x <= v y
  vle_total x y := le_total (v x) (v y)
  vle_trans := le_trans
  vle_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  mul_vle_mul_left _ h := by simp only [map_mul]; gcongr
  vle_mul_cancel h0 h := by
    simp only [map_mul] at h
    apply le_of_mul_le_mul_right h
    simpa [pos_iff_ne_zero] using h0
  not_vle_one_zero := by simp
  vle_mul_comm := by simp [map_mul, mul_comm]

/--
lemma `_root_.Valuation.Compatible.ofValuation` / 引理 `_root_.Valuation.Compatible.ofValuation`

English:
lemma _root_.Valuation.Compatible.ofValuation
  proof: ValuativeRel.ofValuation v -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ => Iff.rfl⟩

中文:
引理 _root_.Valuation.Compatible.ofValuation
  证明: ValuativeRel.ofValuation v -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ => Iff.rfl⟩

Depends on / 依赖: ValuativeRel, ValuativeRel.ofValuation, declaration, directly, inlined, instance, ofValuation
-/
lemma _root_.Valuation.Compatible.ofValuation
    {S Γ : Type*} [Ring S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) :
    letI := ValuativeRel.ofValuation v -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ => Iff.rfl⟩

/--
lemma `isEquiv` / 引理 `isEquiv`

English:
lemma isEquiv
  statement: {Γ₁ Γ₂ : Type*}
  proof: by
  intro x y
  simp_rw [← Valuation.Compatible.vle_iff_le]

中文:
引理 isEquiv
  结论: {Γ₁ Γ₂ : 类型}
  证明: by
  intro x y
  simp_rw [← Valuation.Compatible.vle_iff_le]

Depends on / 依赖: Compatible, Valuation, Valuation.Compatible.vle_iff_le, simp_rw, vle_iff_le
-/
lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.vle_iff_le]

end Valuation

end ValuativeRel

namespace Valuation

open ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible]
variable {x y : R}

/--
lemma `vle_iff_le` / 引理 `vle_iff_le`

English:
lemma vle_iff_le
  statement: x <=ᵥ y ↔ v x <= v y
  proof: Compatible.vle_iff_le _ _

中文:
引理 vle_iff_le
  结论: x <=ᵥ y ↔ v x <= v y
  证明: Compatible.vle_iff_le _ _

Depends on / 依赖: Compatible, Compatible.vle_iff_le, vle_iff_le
-/
lemma vle_iff_le : x <=ᵥ y ↔ v x <= v y :=
  Compatible.vle_iff_le _ _

/--
lemma `vlt_iff_lt` / 引理 `vlt_iff_lt`

English:
lemma vlt_iff_lt
  statement: x <ᵥ y ↔ v x < v y
  proof: by
  simp [lt_iff_not_ge, ← Compatible.vle_iff_le]

中文:
引理 vlt_iff_lt
  结论: x <ᵥ y ↔ v x < v y
  证明: by
  simp [lt_iff_not_ge, ← Compatible.vle_iff_le]

Depends on / 依赖: Compatible, Compatible.vle_iff_le, lt_iff_not_ge, vle_iff_le
-/
lemma vlt_iff_lt : x <ᵥ y ↔ v x < v y := by
  simp [lt_iff_not_ge, ← Compatible.vle_iff_le]

/--
lemma `veq_iff_eq` / 引理 `veq_iff_eq`

English:
lemma veq_iff_eq
  statement: x =ᵥ y ↔ v x = v y
  proof: by
  simp_rw [veq_def, vle_iff_le v, antisymm_iff]

中文:
引理 veq_iff_eq
  结论: x =ᵥ y ↔ v x = v y
  证明: by
  simp_rw [veq_def, vle_iff_le v, antisymm_iff]

Depends on / 依赖: antisymm_iff, simp_rw, veq_def, vle_iff_le
-/
lemma veq_iff_eq : x =ᵥ y ↔ v x = v y := by
  simp_rw [veq_def, vle_iff_le v, antisymm_iff]

/--
lemma `vle_one_iff` / 引理 `vle_one_iff`

English:
lemma vle_one_iff
  statement: x <=ᵥ 1 ↔ v x <= 1
  proof: by simp [v.vle_iff_le]

中文:
引理 vle_one_iff
  结论: x <=ᵥ 1 ↔ v x <= 1
  证明: by simp [v.vle_iff_le]

Depends on / 依赖: v.vle_iff_le, vle_iff_le
-/
lemma vle_one_iff : x <=ᵥ 1 ↔ v x <= 1 := by simp [v.vle_iff_le]
/--
lemma `vlt_one_iff` / 引理 `vlt_one_iff`

English:
lemma vlt_one_iff
  statement: x <ᵥ 1 ↔ v x < 1
  proof: by simp [v.vlt_iff_lt]

中文:
引理 vlt_one_iff
  结论: x <ᵥ 1 ↔ v x < 1
  证明: by simp [v.vlt_iff_lt]

Depends on / 依赖: v.vlt_iff_lt, vlt_iff_lt
-/
lemma vlt_one_iff : x <ᵥ 1 ↔ v x < 1 := by simp [v.vlt_iff_lt]
/--
lemma `one_vle_iff` / 引理 `one_vle_iff`

English:
lemma one_vle_iff
  statement: 1 <=ᵥ x ↔ 1 <= v x
  proof: by simp [v.vle_iff_le]

中文:
引理 one_vle_iff
  结论: 1 <=ᵥ x ↔ 1 <= v x
  证明: by simp [v.vle_iff_le]

Depends on / 依赖: v.vle_iff_le, vle_iff_le
-/
lemma one_vle_iff : 1 <=ᵥ x ↔ 1 <= v x := by simp [v.vle_iff_le]
/--
lemma `one_vlt_iff` / 引理 `one_vlt_iff`

English:
lemma one_vlt_iff
  statement: 1 <ᵥ x ↔ 1 < v x
  proof: by simp [v.vlt_iff_lt]

@[simp]

中文:
引理 one_vlt_iff
  结论: 1 <ᵥ x ↔ 1 < v x
  证明: by simp [v.vlt_iff_lt]

@[simp]

Depends on / 依赖: v.vlt_iff_lt, vlt_iff_lt
-/
lemma one_vlt_iff : 1 <ᵥ x ↔ 1 < v x := by simp [v.vlt_iff_lt]

@[simp]
/--
lemma `apply_posSubmonoid_ne_zero` / 引理 `apply_posSubmonoid_ne_zero`

English:
lemma apply_posSubmonoid_ne_zero
  given: (x : posSubmonoid R)
  statement: v (x : R) != 0
  proof: by
  simp [(isEquiv v (valuation R)).eq_zero, valuation_posSubmonoid_ne_zero]

@[simp]

中文:
引理 apply_posSubmonoid_ne_zero
  条件: (x : posSubmonoid R)
  结论: v (x : R) != 0
  证明: by
  simp [(isEquiv v (valuation R)).eq_zero, valuation_posSubmonoid_ne_zero]

@[simp]

Depends on / 依赖: eq_zero, isEquiv, valuation, valuation_posSubmonoid_ne_zero
-/
lemma apply_posSubmonoid_ne_zero (x : posSubmonoid R) : v (x : R) != 0 := by
  simp [(isEquiv v (valuation R)).eq_zero, valuation_posSubmonoid_ne_zero]

@[simp]
/--
lemma `apply_posSubmonoid_pos` / 引理 `apply_posSubmonoid_pos`

English:
lemma apply_posSubmonoid_pos
  given: (x : posSubmonoid R)
  statement: 0 < v x
  proof: zero_lt_iff.mpr v.apply_posSubmonoid_ne_zero x

中文:
引理 apply_posSubmonoid_pos
  条件: (x : posSubmonoid R)
  结论: 0 < v x
  证明: zero_lt_iff.mpr v.apply_posSubmonoid_ne_zero x

Depends on / 依赖: apply_posSubmonoid_ne_zero, v.apply_posSubmonoid_ne_zero, zero_lt_iff, zero_lt_iff.mpr
-/
lemma apply_posSubmonoid_pos (x : posSubmonoid R) : 0 < v x :=
zero_lt_iff.mpr v.apply_posSubmonoid_ne_zero x

end Valuation

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R]

variable (R) in
/--
Definition of `WithPreorder` / `WithPreorder` 的定义

English:
definition WithPreorder
  body: R

中文:
定义 WithPreorder
  定义体: R
-/
def WithPreorder := R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (WithPreorder R)
  body: inferInstanceAs (Semiring R)

中文:
实例 :
  签名: Semiring (WithPreorder R)
  定义体: inferInstanceAs (Semiring R)

Depends on / 依赖: Semiring
-/
instance : Semiring (WithPreorder R) := inferInstanceAs (Semiring R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (WithPreorder R)
  body: x <=ᵥ y
  le_refl _ := vle_refl _
  le_trans _ _ _ := vle_trans
  lt (x y : R) := x <ᵥ y
  lt_iff_le_not_ge (x y : R) := by have := vle_total x y; grind

中文:
实例 :
  签名: Preorder (WithPreorder R)
  定义体: x <=ᵥ y
  le_refl _ := vle_refl _
  le_trans _ _ _ := vle_trans
  lt (x y : R) := x <ᵥ y
  lt_iff_le_not_ge (x y : R) := by have := vle_total x y; grind
-/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x <=ᵥ y
  le_refl _ := vle_refl _
  le_trans _ _ _ := vle_trans
  lt (x y : R) := x <ᵥ y
  lt_iff_le_not_ge (x y : R) := by have := vle_total x y; grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativeRel (WithPreorder R)
  body: (· <= ·)
  vle_total := vle_total (R := R)
  vle_trans := vle_trans (R := R)
  vle_add := vle_add (R := R)
  mul_vle_mul_left := mul_vle_mul_left (R := R)
  vle_mul_cancel := vle_mul_cancel (R := R)
  not_vle_one_zero := not_vle_one_zero (R := R)
  vle_mul_comm := vle_mul_comm (R := R)

中文:
实例 :
  签名: ValuativeRel (WithPreorder R)
  定义体: (· <= ·)
  vle_total := vle_total (R := R)
  vle_trans := vle_trans (R := R)
  vle_add := vle_add (R := R)
  mul_vle_mul_left := mul_vle_mul_left (R := R)
  vle_mul_cancel := vle_mul_cancel (R := R)
  not_vle_one_zero := not_vle_one_zero (R := R)
  vle_mul_comm := vle_mul_comm (R := R)

Depends on / 依赖: ParacompactSpace, PseudoEMetricSpace, instParacompactSpace
-/
instance : ValuativeRel (WithPreorder R) where
  vle := (· <= ·)
  vle_total := vle_total (R := R)
  vle_trans := vle_trans (R := R)
  vle_add := vle_add (R := R)
  mul_vle_mul_left := mul_vle_mul_left (R := R)
  vle_mul_cancel := vle_mul_cancel (R := R)
  not_vle_one_zero := not_vle_one_zero (R := R)
  vle_mul_comm := vle_mul_comm (R := R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativePreorder (WithPreorder R)
  body: Iff.rfl

中文:
实例 :
  签名: ValuativePreorder (WithPreorder R)
  定义体: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
instance : ValuativePreorder (WithPreorder R) where
  vle_iff_le _ _ := Iff.rfl

variable (R) in
/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: : Ideal R where
  body: { x | x <=ᵥ 0 }
  add_mem' ha hb := vle_add ha hb
  zero_mem' := vle_refl _
  smul_mem' x _ h := by simpa using mul_vle_mul_right h _

中文:
定义 supp
  签名: : Ideal R where
  定义体: { x | x <=ᵥ 0 }
  add_mem' ha hb := vle_add ha hb
  zero_mem' := vle_refl _
  smul_mem' x _ h := by simpa using mul_vle_mul_right h _
-/
def supp : Ideal R where
  carrier := { x | x <=ᵥ 0 }
  add_mem' ha hb := vle_add ha hb
  zero_mem' := vle_refl _
  smul_mem' x _ h := by simpa using mul_vle_mul_right h _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (supp R).IsTwoSided
  body: by simpa [supp] using mul_vle_mul_left h _

@[simp]

中文:
实例 :
  签名: (supp R).IsTwoSided
  定义体: by simpa [supp] using mul_vle_mul_left h _

@[simp]

Depends on / 依赖: mul_vle_mul_left
-/
instance : (supp R).IsTwoSided where
  mul_mem_of_left _ h := by simpa [supp] using mul_vle_mul_left h _

@[simp]
/--
lemma `supp_def` / 引理 `supp_def`

English:
lemma supp_def
  given: (x : R)
  statement: x in supp R ↔ x <=ᵥ 0
  proof: Iff.refl _

中文:
引理 supp_def
  条件: (x : R)
  结论: x in supp R ↔ x <=ᵥ 0
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
lemma supp_def (x : R) : x in supp R ↔ x <=ᵥ 0 := Iff.refl _

/--
lemma `supp_eq_valuation_supp` / 引理 `supp_eq_valuation_supp`

English:
lemma supp_eq_valuation_supp
  given: {R : Type*} [CommRing R] [ValuativeRel R]
  proof: by
  ext
  simpa using valuation_eq_zero_iff.symm

中文:
引理 supp_eq_valuation_supp
  条件: {R : 类型} [CommRing R] [ValuativeRel R]
  证明: by
  ext
  simpa using valuation_eq_zero_iff.symm

Depends on / 依赖: valuation_eq_zero_iff, valuation_eq_zero_iff.symm
-/
lemma supp_eq_valuation_supp {R : Type*} [CommRing R] [ValuativeRel R] :
    supp R = (valuation R).supp := by
  ext
  simpa using valuation_eq_zero_iff.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (supp R).IsPrime
  body: by
    rw [Ideal.ne_top_iff_one]
    exact not_vle_one_zero
  mem_or_mem' h := by
    by_contra! h'
    simp only [supp_def, not_vle] at h h'
    exact vlt.not_vle (zero_vlt_mul h'.1 h'.2) h

中文:
实例 :
  签名: (supp R).IsPrime
  定义体: by
    rw [Ideal.ne_top_iff_one]
    exact not_vle_one_zero
  mem_or_mem' h := by
    by_contra! h'
    simp only [supp_def, not_vle] at h h'
    exact vlt.not_vle (zero_vlt_mul h'.1 h'.2) h

Depends on / 依赖: Ideal.ne_top_iff_one, mem_or_mem, ne_top_iff_one, not_vle, not_vle_one_zero, supp_def, vlt.not_vle, zero_vlt_mul
-/
instance : (supp R).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    exact not_vle_one_zero
  mem_or_mem' h := by
    by_contra! h'
    simp only [supp_def, not_vle] at h h'
    exact vlt.not_vle (zero_vlt_mul h'.1 h'.2) h

section Ring

variable {R : Type*} [Ring R] [ValuativeRel R] {a b c d : R}

@[deprecated (since := "2026-01-06")] alias vle_mul_right_iff := mul_vle_mul_iff_left

@[deprecated (since := "2026-01-06")] alias vle_mul_left_iff := mul_vle_mul_iff_right

@[deprecated (since := "2026-01-06")] alias vlt_mul_right_iff := mul_vlt_mul_iff_left

@[deprecated (since := "2026-01-06")] alias vlt_mul_left_iff := mul_vlt_mul_iff_right

/--
lemma `mul_vlt_mul_of_vlt_of_vle` / 引理 `mul_vlt_mul_of_vlt_of_vle`

English:
lemma mul_vlt_mul_of_vlt_of_vle
  given: (hab : a <ᵥ b) (hcd : c <=ᵥ d) (hd : 0 <ᵥ d)
  proof: (mul_vle_mul_right hcd _).trans_vlt (mul_vlt_mul_left hd hab)

中文:
引理 mul_vlt_mul_of_vlt_of_vle
  条件: (hab : a <ᵥ b) (hcd : c <=ᵥ d) (hd : 0 <ᵥ d)
  证明: (mul_vle_mul_right hcd _).trans_vlt (mul_vlt_mul_left hd hab)

Depends on / 依赖: mul_vle_mul_right, mul_vlt_mul_left, trans_vlt
-/
lemma mul_vlt_mul_of_vlt_of_vle (hab : a <ᵥ b) (hcd : c <=ᵥ d) (hd : 0 <ᵥ d) :
    a * c <ᵥ b * d :=
  (mul_vle_mul_right hcd _).trans_vlt (mul_vlt_mul_left hd hab)

/--
lemma `mul_vlt_mul_of_vle_of_vlt` / 引理 `mul_vlt_mul_of_vle_of_vlt`

English:
lemma mul_vlt_mul_of_vle_of_vlt
  given: (hab : a <=ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a)
  proof: (mul_vlt_mul_right ha hcd).trans_vle (mul_vle_mul_left hab _)

@[gcongr]

中文:
引理 mul_vlt_mul_of_vle_of_vlt
  条件: (hab : a <=ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a)
  证明: (mul_vlt_mul_right ha hcd).trans_vle (mul_vle_mul_left hab _)

@[gcongr]

Depends on / 依赖: mul_vle_mul_left, mul_vlt_mul_right, trans_vle
-/
lemma mul_vlt_mul_of_vle_of_vlt (hab : a <=ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a) :
    a * c <ᵥ b * d :=
  (mul_vlt_mul_right ha hcd).trans_vle (mul_vle_mul_left hab _)

@[gcongr]
/--
lemma `mul_vlt_mul` / 引理 `mul_vlt_mul`

English:
lemma mul_vlt_mul
  given: (hab : a <ᵥ b) (hcd : c <ᵥ d)
  statement: a * c <ᵥ b * d
  proof: (mul_vle_mul_right hcd.vle _).trans_vlt (mul_vlt_mul_left ((zero_vle c).trans_vlt hcd) hab)

中文:
引理 mul_vlt_mul
  条件: (hab : a <ᵥ b) (hcd : c <ᵥ d)
  结论: a * c <ᵥ b * d
  证明: (mul_vle_mul_right hcd.vle _).trans_vlt (mul_vlt_mul_left ((zero_vle c).trans_vlt hcd) hab)

Depends on / 依赖: hcd.vle, mul_vle_mul_right, mul_vlt_mul_left, trans_vlt, zero_vle
-/
lemma mul_vlt_mul (hab : a <ᵥ b) (hcd : c <ᵥ d) : a * c <ᵥ b * d :=
  (mul_vle_mul_right hcd.vle _).trans_vlt (mul_vlt_mul_left ((zero_vle c).trans_vlt hcd) hab)

/--
lemma `pow_vle_pow` / 引理 `pow_vle_pow`

English:
lemma pow_vle_pow
  given: (hab : a <=ᵥ b) (n : Nat)
  statement: a ^ n <=ᵥ b ^ n
  proof: by
  induction n with
  | zero => simp
  | succ _ hn => simp [pow_succ, mul_vle_mul hn hab]

中文:
引理 pow_vle_pow
  条件: (hab : a <=ᵥ b) (n : 自然数)
  结论: a ^ n <=ᵥ b ^ n
  证明: by
  induction n with
  | zero => simp
  | succ _ hn => simp [pow_succ, mul_vle_mul hn hab]

Depends on / 依赖: mul_vle_mul, pow_succ
-/
lemma pow_vle_pow (hab : a <=ᵥ b) (n : Nat) : a ^ n <=ᵥ b ^ n := by
  induction n with
  | zero => simp
  | succ _ hn => simp [pow_succ, mul_vle_mul hn hab]

/--
lemma `pow_vlt_pow` / 引理 `pow_vlt_pow`

English:
lemma pow_vlt_pow
  given: (hab : a <ᵥ b) {n : Nat} (hn : n != 0)
  statement: a ^ n <ᵥ b ^ n
  proof: by
  induction n using Nat.twoStepInduction with
  | zero => contradiction
  | one => simpa
  | more _ _ => simp_all [pow_succ, mul_vlt_mul]

中文:
引理 pow_vlt_pow
  条件: (hab : a <ᵥ b) {n : 自然数} (hn : n != 0)
  结论: a ^ n <ᵥ b ^ n
  证明: by
  induction n using Nat.twoStepInduction with
  | zero => contradiction
  | one => simpa
  | more _ _ => simp_all [pow_succ, mul_vlt_mul]

Depends on / 依赖: Nat.twoStepInduction, mul_vlt_mul, pow_succ, twoStepInduction
-/
lemma pow_vlt_pow (hab : a <ᵥ b) {n : Nat} (hn : n != 0) : a ^ n <ᵥ b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => contradiction
  | one => simpa
  | more _ _ => simp_all [pow_succ, mul_vlt_mul]

/--
lemma `pow_vle_pow_of_vle_one` / 引理 `pow_vle_pow_of_vle_one`

English:
lemma pow_vle_pow_of_vle_one
  given: (ha : a <=ᵥ 1) {n m : Nat} (hnm : n <= m)
  statement: a ^ m <=ᵥ a ^ n
  proof: by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

中文:
引理 pow_vle_pow_of_vle_one
  条件: (ha : a <=ᵥ 1) {n m : 自然数} (hnm : n <= m)
  结论: a ^ m <=ᵥ a ^ n
  证明: by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

Depends on / 依赖: exists_add_of_le, mul_vle_mul_right, pow_add, pow_vle_pow
-/
lemma pow_vle_pow_of_vle_one (ha : a <=ᵥ 1) {n m : Nat} (hnm : n <= m) : a ^ m <=ᵥ a ^ n := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

/--
lemma `pow_vle_pow_of_one_vle` / 引理 `pow_vle_pow_of_one_vle`

English:
lemma pow_vle_pow_of_one_vle
  given: (ha : 1 <=ᵥ a) {n m : Nat} (hnm : n <= m)
  statement: a ^ n <=ᵥ a ^ m
  proof: by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

中文:
引理 pow_vle_pow_of_one_vle
  条件: (ha : 1 <=ᵥ a) {n m : 自然数} (hnm : n <= m)
  结论: a ^ n <=ᵥ a ^ m
  证明: by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

Depends on / 依赖: exists_add_of_le, mul_vle_mul_right, pow_add, pow_vle_pow
-/
lemma pow_vle_pow_of_one_vle (ha : 1 <=ᵥ a) {n m : Nat} (hnm : n <= m) : a ^ n <=ᵥ a ^ m := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using mul_vle_mul_right (pow_vle_pow ha m) _

end Ring

section DivisionRing

variable {K : Type*} [DivisionRing K] [ValuativeRel K] {a b c x : K}

@[simp]
/--
lemma `vle_zero_iff` / 引理 `vle_zero_iff`

English:
lemma vle_zero_iff
  statement: a <=ᵥ 0 ↔ a = 0
  proof: by
  rw [← supp_def]; rw [Ideal.eq_bot_of_prime (supp K)]; rw [Ideal.mem_bot]

@[simp]

中文:
引理 vle_zero_iff
  结论: a <=ᵥ 0 ↔ a = 0
  证明: by
  rw [← supp_def]; rw [Ideal.eq_bot_of_prime (supp K)]; rw [Ideal.mem_bot]

@[simp]

Depends on / 依赖: Ideal.eq_bot_of_prime, Ideal.mem_bot, eq_bot_of_prime, mem_bot, supp_def
-/
lemma vle_zero_iff : a <=ᵥ 0 ↔ a = 0 := by
  rw [← supp_def]; rw [Ideal.eq_bot_of_prime (supp K)]; rw [Ideal.mem_bot]

@[simp]
/--
lemma `zero_vlt_iff` / 引理 `zero_vlt_iff`

English:
lemma zero_vlt_iff
  statement: 0 <ᵥ a ↔ a != 0
  proof: by
  simp [vlt]

@[simp]

中文:
引理 zero_vlt_iff
  结论: 0 <ᵥ a ↔ a != 0
  证明: by
  simp [vlt]

@[simp]
-/
lemma zero_vlt_iff : 0 <ᵥ a ↔ a != 0 := by
  simp [vlt]

@[simp]
/--
lemma `zero_veq_iff` / 引理 `zero_veq_iff`

English:
lemma zero_veq_iff
  statement: a =ᵥ 0 ↔ a = 0 where
  proof: vle_zero_iff.1 h.1
  mpr := by simp +contextual

@[simp]

中文:
引理 zero_veq_iff
  结论: a =ᵥ 0 ↔ a = 0 where
  证明: vle_zero_iff.1 h.1
  mpr := by simp +contextual

@[simp]

Depends on / 依赖: vle_zero_iff
-/
lemma zero_veq_iff : a =ᵥ 0 ↔ a = 0 where
  mp h := vle_zero_iff.1 h.1
  mpr := by simp +contextual

@[simp]
/--
lemma `veq_zero_iff` / 引理 `veq_zero_iff`

English:
lemma veq_zero_iff
  statement: 0 =ᵥ a ↔ 0 = a
  proof: by
  rw [veq_comm]; rw [eq_comm]; rw [zero_veq_iff]

中文:
引理 veq_zero_iff
  结论: 0 =ᵥ a ↔ 0 = a
  证明: by
  rw [veq_comm]; rw [eq_comm]; rw [zero_veq_iff]

Depends on / 依赖: eq_comm, veq_comm, zero_veq_iff
-/
lemma veq_zero_iff : 0 =ᵥ a ↔ 0 = a := by
  rw [veq_comm]; rw [eq_comm]; rw [zero_veq_iff]

/--
lemma `vle_div_iff` / 引理 `vle_div_iff`

English:
lemma vle_div_iff
  given: (hc : c != 0)
  statement: a <=ᵥ b / c ↔ a * c <=ᵥ b
  proof: by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

中文:
引理 vle_div_iff
  条件: (hc : c != 0)
  结论: a <=ᵥ b / c ↔ a * c <=ᵥ b
  证明: by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

Depends on / 依赖: mul_vle_mul_iff_left
-/
lemma vle_div_iff (hc : c != 0) : a <=ᵥ b / c ↔ a * c <=ᵥ b := by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

/--
lemma `div_vle_iff` / 引理 `div_vle_iff`

English:
lemma div_vle_iff
  given: (hc : c != 0)
  statement: a / c <=ᵥ b ↔ a <=ᵥ b * c
  proof: by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

中文:
引理 div_vle_iff
  条件: (hc : c != 0)
  结论: a / c <=ᵥ b ↔ a <=ᵥ b * c
  证明: by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

Depends on / 依赖: mul_vle_mul_iff_left
-/
lemma div_vle_iff (hc : c != 0) : a / c <=ᵥ b ↔ a <=ᵥ b * c := by
  rw [← mul_vle_mul_iff_left (by simpa)]; rw [div_mul_cancel₀ _ (by lia)]

/--
lemma `one_vle_div_iff` / 引理 `one_vle_div_iff`

English:
lemma one_vle_div_iff
  given: (hb : b != 0)
  statement: 1 <=ᵥ a / b ↔ b <=ᵥ a
  proof: by
  simp [vle_div_iff hb]

中文:
引理 one_vle_div_iff
  条件: (hb : b != 0)
  结论: 1 <=ᵥ a / b ↔ b <=ᵥ a
  证明: by
  simp [vle_div_iff hb]

Depends on / 依赖: vle_div_iff
-/
lemma one_vle_div_iff (hb : b != 0) : 1 <=ᵥ a / b ↔ b <=ᵥ a := by
  simp [vle_div_iff hb]

/--
lemma `div_vle_one_iff` / 引理 `div_vle_one_iff`

English:
lemma div_vle_one_iff
  given: (hb : b != 0)
  statement: a / b <=ᵥ 1 ↔ a <=ᵥ b
  proof: by
  simp [div_vle_iff hb]

中文:
引理 div_vle_one_iff
  条件: (hb : b != 0)
  结论: a / b <=ᵥ 1 ↔ a <=ᵥ b
  证明: by
  simp [div_vle_iff hb]

Depends on / 依赖: div_vle_iff, toEDist
-/
lemma div_vle_one_iff (hb : b != 0) : a / b <=ᵥ 1 ↔ a <=ᵥ b := by
  simp [div_vle_iff hb]

/--
lemma `one_vle_inv` / 引理 `one_vle_inv`

English:
lemma one_vle_inv
  given: (hx : x != 0)
  statement: 1 <=ᵥ x⁻¹ ↔ x <=ᵥ 1
  proof: by
  simpa using one_vle_div_iff (a := 1) hx

中文:
引理 one_vle_inv
  条件: (hx : x != 0)
  结论: 1 <=ᵥ x⁻¹ ↔ x <=ᵥ 1
  证明: by
  simpa using one_vle_div_iff (a := 1) hx

Depends on / 依赖: one_vle_div_iff
-/
lemma one_vle_inv (hx : x != 0) : 1 <=ᵥ x⁻¹ ↔ x <=ᵥ 1 := by
  simpa using one_vle_div_iff (a := 1) hx

/--
lemma `inv_vle_one` / 引理 `inv_vle_one`

English:
lemma inv_vle_one
  given: (hx : x != 0)
  statement: x⁻¹ <=ᵥ 1 ↔ 1 <=ᵥ x
  proof: by
  simpa using div_vle_one_iff (a := 1) hx

中文:
引理 inv_vle_one
  条件: (hx : x != 0)
  结论: x⁻¹ <=ᵥ 1 ↔ 1 <=ᵥ x
  证明: by
  simpa using div_vle_one_iff (a := 1) hx

Depends on / 依赖: div_vle_one_iff
-/
lemma inv_vle_one (hx : x != 0) : x⁻¹ <=ᵥ 1 ↔ 1 <=ᵥ x := by
  simpa using div_vle_one_iff (a := 1) hx

/--
lemma `inv_vlt_one` / 引理 `inv_vlt_one`

English:
lemma inv_vlt_one
  given: (hx : x != 0)
  statement: x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x
  proof: (one_vle_inv hx).not

中文:
引理 inv_vlt_one
  条件: (hx : x != 0)
  结论: x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x
  证明: (one_vle_inv hx).not

Depends on / 依赖: one_vle_inv
-/
lemma inv_vlt_one (hx : x != 0) : x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x :=
  (one_vle_inv hx).not

/--
lemma `one_vlt_inv` / 引理 `one_vlt_inv`

English:
lemma one_vlt_inv
  given: (hx : x != 0)
  statement: 1 <ᵥ x⁻¹ ↔ x <ᵥ 1
  proof: (inv_vle_one hx).not

中文:
引理 one_vlt_inv
  条件: (hx : x != 0)
  结论: 1 <ᵥ x⁻¹ ↔ x <ᵥ 1
  证明: (inv_vle_one hx).not

Depends on / 依赖: inv_vle_one
-/
lemma one_vlt_inv (hx : x != 0) : 1 <ᵥ x⁻¹ ↔ x <ᵥ 1 :=
  (inv_vle_one hx).not

end DivisionRing

open NNReal in variable (R) in
/--
Definition of `RankLeOneStruct` / `RankLeOneStruct` 的定义

English:
structure RankLeOneStruct
  parameters: where
  axioms and operations (2):
    - emb : ValueGroupWithZero R ->*₀ Real>=0
    - strictMono : StrictMono emb

中文:
结构 RankLeOneStruct
  参数: where
  公理与运算 (2 个):
    - emb : ValueGroupWithZero R ->*₀ 实数>=0
    - strictMono : StrictMono emb
-/
structure RankLeOneStruct where
  /-- The embedding of the value group-with-zero into the nonnegative reals. -/
  emb : ValueGroupWithZero R ->*₀ Real>=0
  strictMono : StrictMono emb

variable (R) in
/--
Definition of `IsRankLeOne` / `IsRankLeOne` 的定义

English:
class IsRankLeOne
  parameters: where
  axioms and operations (1):
    - nonempty : Nonempty (RankLeOneStruct R)

中文:
类 IsRankLeOne
  参数: where
  公理与运算 (1 个):
    - nonempty : Nonempty (RankLeOneStruct R)
-/
class IsRankLeOne where
  nonempty : Nonempty (RankLeOneStruct R)

variable (R) in
/--
Definition of `IsNontrivial` / `IsNontrivial` 的定义

English:
class IsNontrivial
  parameters: where
  axioms and operations (1):
    - condition : exists γ : ValueGroupWithZero R, γ != 0 ∧ γ != 1

中文:
类 IsNontrivial
  参数: where
  公理与运算 (1 个):
    - condition : 存在 γ : ValueGroupWithZero R, γ != 0 ∧ γ != 1
-/
class IsNontrivial where
  condition : exists γ : ValueGroupWithZero R, γ != 0 ∧ γ != 1

/--
lemma `IsNontrivial.exists_lt_one` / 引理 `IsNontrivial.exists_lt_one`

English:
lemma IsNontrivial.exists_lt_one
  given: [IsNontrivial R]
  proof: by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := R)
  obtain h1 | h1 := lt_or_lt_iff_ne.mpr h1
  · exact ⟨γ, zero_lt_iff.mpr h0, h1⟩
  · exact ⟨γ⁻¹, by simpa [zero_lt_iff], by simp [inv_lt_one_iff₀, h0, h1]⟩

中文:
引理 IsNontrivial.exists_lt_one
  条件: [IsNontrivial R]
  证明: by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := R)
  obtain h1 | h1 := lt_or_lt_iff_ne.mpr h1
  · exact ⟨γ, zero_lt_iff.mpr h0, h1⟩
  · exact ⟨γ⁻¹, by simpa [zero_lt_iff], by simp [inv_lt_one_iff₀, h0, h1]⟩
-/
lemma IsNontrivial.exists_lt_one [IsNontrivial R] :
    exists γ : ValueGroupWithZero R, 0 < γ ∧ γ < 1 := by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := R)
  obtain h1 | h1 := lt_or_lt_iff_ne.mpr h1
  · exact ⟨γ, zero_lt_iff.mpr h0, h1⟩
  · exact ⟨γ⁻¹, by simpa [zero_lt_iff], by simp [inv_lt_one_iff₀, h0, h1]⟩

/--
lemma `isNontrivial_iff_nontrivial_units` / 引理 `isNontrivial_iff_nontrivial_units`

English:
lemma isNontrivial_iff_nontrivial_units
  proof: by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

中文:
引理 isNontrivial_iff_nontrivial_units
  证明: by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

Depends on / 依赖: Units.mk0, Units.val_eq_one, eq_or_ne, h.symm, r.val, s.val, val_eq_one
-/
lemma isNontrivial_iff_nontrivial_units :
    IsNontrivial R ↔ Nontrivial (ValueGroupWithZero R)ˣ := by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

section Valuation

variable {R : Type*} [Ring R] [ValuativeRel R]

/--
lemma `isNontrivial_iff_isNontrivial` / 引理 `isNontrivial_iff_isNontrivial`

English:
lemma isNontrivial_iff_isNontrivial
  proof: by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    have hγ : v r != 0 := by simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr
    have hγ' : v r <= v s -> v r < v s := by
      simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr'
   

中文:
引理 isNontrivial_iff_isNontrivial
  证明: by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    have hγ : v r != 0 := by simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr
    have hγ' : v r <= v s -> v r < v s := by
      simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr'
   

Depends on / 依赖: Compatible, Valuation, Valuation.Compatible.vle_iff_le, ValueGroupWithZero, ValueGroupWithZero.ind, eq_zero, eq_zero.ne.mp, isEquiv, valuation, vle_iff_le
-/
lemma isNontrivial_iff_isNontrivial
    {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible] :
    IsNontrivial R ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    have hγ : v r != 0 := by simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr
    have hγ' : v r <= v s -> v r < v s := by
      simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr'
    by_cases hr : v r = 1
    · exact ⟨s, by simp, fun h => by simp [h, hr] at hγ'⟩
    · exact ⟨r, by simpa using hγ, hr⟩
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, (isEquiv v (valuation R)).eq_zero.ne.mp hr,
      by simpa [(isEquiv v (valuation R)).eq_one_iff_eq_one] using hr'⟩

instance {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [IsNontrivial R] (v : Valuation R Γ₀) [v.Compatible] :
    v.IsNontrivial := by rwa [← isNontrivial_iff_isNontrivial]

/--
lemma `ValueGroupWithZero.mk_eq_valuation` / 引理 `ValueGroupWithZero.mk_eq_valuation`

English:
lemma ValueGroupWithZero.mk_eq_valuation
  statement: {K : Type*} [DivisionRing K] [ValuativeRel K]
  proof: by
  rw [Valuation.map_div]; rw [ValueGroupWithZero.mk_eq_div]

中文:
引理 ValueGroupWithZero.mk_eq_valuation
  结论: {K : 类型} [DivisionRing K] [ValuativeRel K]
  证明: by
  rw [Valuation.map_div]; rw [ValueGroupWithZero.mk_eq_div]

Depends on / 依赖: Valuation, Valuation.map_div, ValueGroupWithZero, ValueGroupWithZero.mk_eq_div, map_div, mk_eq_div
-/
lemma ValueGroupWithZero.mk_eq_valuation {K : Type*} [DivisionRing K] [ValuativeRel K]
    (x : K) (y : posSubmonoid K) :
    ValueGroupWithZero.mk x y = valuation K (x / y) := by
  rw [Valuation.map_div]; rw [ValueGroupWithZero.mk_eq_div]

/--
lemma `exists_valuation_div_valuation_eq` / 引理 `exists_valuation_div_valuation_eq`

English:
lemma exists_valuation_div_valuation_eq
  given: (γ : ValueGroupWithZero R)
  proof: by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

中文:
引理 exists_valuation_div_valuation_eq
  条件: (γ : ValueGroupWithZero R)
  证明: by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind, ValueGroupWithZero.inv_mk, b.prop, div_eq_mul_inv, inv_mk, valuation
-/
lemma exists_valuation_div_valuation_eq (γ : ValueGroupWithZero R) :
    exists (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

/--
lemma `exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq` / 引理 `exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq`

English:
lemma exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq
  given: (γ : (ValueGroupWithZero R)ˣ)
  proof: by
  obtain ⟨a, b, hab⟩ := exists_valuation_div_valuation_eq γ.val
  lift a to posSubmonoid R using by
    contrapose! hab
    rw [posSubmonoid_def]; rw [not_vlt]; rw [← valuation_eq_zero_iff] at hab
    simp [hab, eq_comm]
  use a, b

中文:
引理 exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq
  条件: (γ : (ValueGroupWithZero R)ˣ)
  证明: by
  obtain ⟨a, b, hab⟩ := exists_valuation_div_valuation_eq γ.val
  lift a to posSubmonoid R using by
    contrapose! hab
    rw [posSubmonoid_def]; rw [not_vlt]; rw [← valuation_eq_zero_iff] at hab
    simp [hab, eq_comm]
  use a, b

Depends on / 依赖: contrapose, eq_comm, exists_valuation_div_valuation_eq, not_vlt, posSubmonoid, posSubmonoid_def, valuation_eq_zero_iff
-/
lemma exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGroupWithZero R)ˣ) :
    exists (a b : posSubmonoid R), valuation R a / valuation _ (b : R) = γ := by
  obtain ⟨a, b, hab⟩ := exists_valuation_div_valuation_eq γ.val
  lift a to posSubmonoid R using by
    contrapose! hab
    rw [posSubmonoid_def]; rw [not_vlt]; rw [← valuation_eq_zero_iff] at hab
    simp [hab, eq_comm]
  use a, b

-- See `exists_valuation_div_valuation_eq` for the version that works for all rings.
/--
theorem `valuation_surjective` / 定理 `valuation_surjective`

English:
theorem valuation_surjective
  given: {K : Type*} [DivisionRing K] [ValuativeRel K]
  proof: ValueGroupWithZero.ind (ValueGroupWithZero.mk_eq_valuation · · ▸ ⟨_, rfl⟩)

中文:
定理 valuation_surjective
  条件: {K : 类型} [DivisionRing K] [ValuativeRel K]
  证明: ValueGroupWithZero.ind (ValueGroupWithZero.mk_eq_valuation · · ▸ ⟨_, rfl⟩)

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind, ValueGroupWithZero.mk_eq_valuation, mk_eq_valuation
-/
theorem valuation_surjective {K : Type*} [DivisionRing K] [ValuativeRel K] :
    Function.Surjective (valuation K) :=
  ValueGroupWithZero.ind (ValueGroupWithZero.mk_eq_valuation · · ▸ ⟨_, rfl⟩)

end Valuation

variable (R) in
/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
class IsDiscrete
  parameters: where
  axioms and operations (1):
    - has_maximal_element : exists γ : ValueGroupWithZero R, γ < 1 ∧ (forall δ : ValueGroupWithZero R, δ < 1 -> δ <= γ)

中文:
类 IsDiscrete
  参数: where
  公理与运算 (1 个):
    - has_maximal_element : 存在 γ : ValueGroupWithZero R, γ < 1 ∧ (对任意 δ : ValueGroupWithZero R, δ < 1 -> δ <= γ)
-/
class IsDiscrete where
  has_maximal_element :
    exists γ : ValueGroupWithZero R, γ < 1 ∧ (forall δ : ValueGroupWithZero R, δ < 1 -> δ <= γ)

variable (R) in
/-- The maximal element that is `< 1` in the value group of a discrete valuation. -/
-- TODO: Link to `Valuation.IsUniformizer` once we connect `Valuation.IsRankOneDiscrete` with
-- `ValuativeRel`.
noncomputable
/--
Definition of `uniformizer` / `uniformizer` 的定义

English:
definition uniformizer
  signature: [IsDiscrete R]
  body: IsDiscrete.has_maximal_element.choose

中文:
定义 uniformizer
  签名: [IsDiscrete R]
  定义体: IsDiscrete.has_maximal_element.choose

Depends on / 依赖: IsDiscrete, IsDiscrete.has_maximal_element.choose, has_maximal_element
-/
def uniformizer [IsDiscrete R] : ValueGroupWithZero R :=
  IsDiscrete.has_maximal_element.choose

/--
lemma `uniformizer_lt_one` / 引理 `uniformizer_lt_one`

English:
lemma uniformizer_lt_one
  given: [IsDiscrete R]
  proof: IsDiscrete.has_maximal_element.choose_spec.1

中文:
引理 uniformizer_lt_one
  条件: [IsDiscrete R]
  证明: IsDiscrete.has_maximal_element.choose_spec.1

Depends on / 依赖: IsDiscrete, IsDiscrete.has_maximal_element.choose_spec, choose_spec, has_maximal_element
-/
lemma uniformizer_lt_one [IsDiscrete R] :
    uniformizer R < 1 := IsDiscrete.has_maximal_element.choose_spec.1

/--
lemma `le_uniformizer_iff` / 引理 `le_uniformizer_iff`

English:
lemma le_uniformizer_iff
  given: [IsDiscrete R] {a : ValueGroupWithZero R}
  proof: ⟨fun h => h.trans_lt uniformizer_lt_one,
    IsDiscrete.has_maximal_element.choose_spec.2 a⟩

中文:
引理 le_uniformizer_iff
  条件: [IsDiscrete R] {a : ValueGroupWithZero R}
  证明: ⟨fun h => h.trans_lt uniformizer_lt_one,
    IsDiscrete.has_maximal_element.choose_spec.2 a⟩

Depends on / 依赖: IsDiscrete, IsDiscrete.has_maximal_element.choose_spec, choose_spec, h.trans_lt, has_maximal_element, trans_lt, uniformizer_lt_one
-/
lemma le_uniformizer_iff [IsDiscrete R] {a : ValueGroupWithZero R} :
    a <= uniformizer R ↔ a < 1 :=
  ⟨fun h => h.trans_lt uniformizer_lt_one,
    IsDiscrete.has_maximal_element.choose_spec.2 a⟩

/--
lemma `uniformizer_pos` / 引理 `uniformizer_pos`

English:
lemma uniformizer_pos
  given: [IsDiscrete R] [IsNontrivial R]
  proof: by
  obtain ⟨γ, hγ, hγ'⟩ := IsNontrivial.exists_lt_one (R := R)
  exact hγ.trans_le (le_uniformizer_iff.mpr hγ')

@[simp]

中文:
引理 uniformizer_pos
  条件: [IsDiscrete R] [IsNontrivial R]
  证明: by
  obtain ⟨γ, hγ, hγ'⟩ := IsNontrivial.exists_lt_one (R := R)
  exact hγ.trans_le (le_uniformizer_iff.mpr hγ')

@[simp]

Depends on / 依赖: IsNontrivial, IsNontrivial.exists_lt_one, exists_lt_one, le_uniformizer_iff, le_uniformizer_iff.mpr, trans_le
-/
lemma uniformizer_pos [IsDiscrete R] [IsNontrivial R] :
    0 < uniformizer R := by
  obtain ⟨γ, hγ, hγ'⟩ := IsNontrivial.exists_lt_one (R := R)
  exact hγ.trans_le (le_uniformizer_iff.mpr hγ')

@[simp]
/--
lemma `uniformizer_ne_zero` / 引理 `uniformizer_ne_zero`

English:
lemma uniformizer_ne_zero
  given: [IsDiscrete R] [IsNontrivial R]
  proof: uniformizer_pos.ne'

中文:
引理 uniformizer_ne_zero
  条件: [IsDiscrete R] [IsNontrivial R]
  证明: uniformizer_pos.ne'

Depends on / 依赖: uniformizer_pos, uniformizer_pos.ne
-/
lemma uniformizer_ne_zero [IsDiscrete R] [IsNontrivial R] :
    uniformizer R != 0 :=
  uniformizer_pos.ne'

/--
lemma `uniformizer_inv_le_iff` / 引理 `uniformizer_inv_le_iff`

English:
lemma uniformizer_inv_le_iff
  given: [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWithZero R}
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  replace ha : 0 < a := bot_lt_iff_ne_bot.mpr ha
  rw [inv_le_comm₀ uniformizer_pos ha]; rw [le_uniformizer_iff]; rw [inv_lt_one₀ ha]

中文:
引理 uniformizer_inv_le_iff
  条件: [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWithZero R}
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  replace ha : 0 < a := bot_lt_iff_ne_bot.mpr ha
  rw [inv_le_comm₀ uniformizer_pos ha]; rw [le_uniformizer_iff]; rw [inv_lt_one₀ ha]

Depends on / 依赖: bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, le_uniformizer_iff, replace, uniformizer_pos
-/
lemma uniformizer_inv_le_iff [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWithZero R} :
    (uniformizer R)⁻¹ <= a ↔ 1 < a := by
  by_cases ha : a = 0
  · simp [ha]
  replace ha : 0 < a := bot_lt_iff_ne_bot.mpr ha
  rw [inv_le_comm₀ uniformizer_pos ha]; rw [le_uniformizer_iff]; rw [inv_lt_one₀ ha]

variable {R Γ : Type*} [Ring R] [ValuativeRel R] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ)

open MonoidWithZeroHom ValueGroup₀

namespace ValueGroupWithZero

/-- The `ValueGroupWithZero R` is the "minimal" value group (with zero) among all value groups
of valuations that are compatible with the valuative relation, in the sense that it is canonically
isomorphic to the subgroup (with zero) generated by `v '' R` for any compatible `v`.
`ValueGroupWithZero.embed v` is exactly this isomorphism map; it will later be upgraded to
`ValueGroupWithZero.orderMonoidIso v`. -/
noncomputable
/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: [v.Compatible]
  body: ValueGroupWithZero.lift
(fun r s => (restrict₀ (.ofClass v) r / (restrict₀ (.ofClass v) s))) by
    intro x y r s
    simp only [Valuation.Compatible.vle_iff_le (v := v), map_mul, ← and_imp, ← le_antisymm_iff]
    rw [div_eq_div_iff]
    · simp only [ValueGroup₀.restrict₀_apply, dite_mul, zero_mul]


中文:
定义 embed
  签名: [v.Compatible]
  定义体: ValueGroupWithZero.lift
(fun r s => (restrict₀ (.ofClass v) r / (restrict₀ (.ofClass v) s))) by
    intro x y r s
    simp only [Valuation.Compatible.vle_iff_le (v := v), map_mul, ← and_imp, ← le_antisymm_iff]
    rw [div_eq_div_iff]
    · simp only [ValueGroup₀.restrict₀_apply, dite_mul, zero_mul]


Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.lift
-/
def embed [v.Compatible] : ValueGroupWithZero R ->*₀ ValueGroup₀ (.ofClass v) where
  toFun := ValueGroupWithZero.lift
(fun r s => (restrict₀ (.ofClass v) r / (restrict₀ (.ofClass v) s))) by
    intro x y r s
    simp only [Valuation.Compatible.vle_iff_le (v := v), map_mul, ← and_imp, ← le_antisymm_iff]
    rw [div_eq_div_iff]
    · simp only [ValueGroup₀.restrict₀_apply, dite_mul, zero_mul]
      split_ifs with h1 h2 h3 <;>
      simp_all [← WithZero.coe_mul, ← Units.val_inj] <;> simpa
    all_goals simp [ValueGroup₀.restrict₀]
  map_zero' := by simp [lift_zero, ValueGroup₀.restrict₀]
  map_one' := by simp [ValueGroup₀.restrict₀]
  map_mul' _ _ := by
    apply lift_mul
    simp only [map_mul, ValueGroup₀.restrict₀_apply, mul_dite, mul_zero, dite_mul, zero_mul,
      Submonoid.coe_mul, Subtype.forall, posSubmonoid_def]
    intro x y z hz w hw
    split_ifs
    all_goals simp_all
    simp [field, ← WithZero.coe_mul, ← Units.val_inj]

/-- The element `.mk x s` in `ValueGroupWithZero R` is sent to `v x / v s` in the
image group of `v`. -/
@[simp]
/--
lemma `embed_mk` / 引理 `embed_mk`

English:
lemma embed_mk
  given: [v.Compatible] (x : R) (s : posSubmonoid R)
  proof: rfl

中文:
引理 embed_mk
  条件: [v.Compatible] (x : R) (s : posSubmonoid R)
  证明: rfl
-/
lemma embed_mk [v.Compatible] (x : R) (s : posSubmonoid R) :
    embed v (.mk x s) = (restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s)) :=
  rfl

/--
The triangle in the following diagram is commutative:
```
      restrict₀ v embedding
    R –––––––––––> ValueGroup₀ v –––––––––> Γ
    │ ∧
    │ /
    │ / embed v
    ∨ /
ValueGroupWithZero R
```
where the first row is the map `v` factored through its image group (with zero) in `Γ`.
-/
@[simp]
/--
lemma `embed_valuation_eq_restrict₀` / 引理 `embed_valuation_eq_restrict₀`

English:
lemma embed_valuation_eq_restrict₀
  given: [v.Compatible] (x : R)
  proof: by
  convert! embed_mk v x 1
  simp

中文:
引理 embed_valuation_eq_restrict₀
  条件: [v.Compatible] (x : R)
  证明: by
  convert! embed_mk v x 1
  simp

Depends on / 依赖: convert, embed_mk
-/
lemma embed_valuation_eq_restrict₀ [v.Compatible] (x : R) :
    embed v (valuation R x) = ValueGroup₀.restrict₀ (.ofClass v) x := by
  convert! embed_mk v x 1
  simp

/--
When `v` is `valuation R`, in the following commutative diagram where the first row is the map `v`
factored through its image group (with zero),
```
                                 embedding
    R –––––––––––> ValueGroup₀ v –––––-–––> ValueGroupWithZero R
    │ ∧
    │ /
    │ / embed v
    ∨ /
ValueGroupWithZero R
```
the map from `ValueGroupWithZero R` to itself is identity.
-/
@[simp]
/--
lemma `embedding_embed_valuation_eq` / 引理 `embedding_embed_valuation_eq`

English:
lemma embedding_embed_valuation_eq
  given: (γ : ValueGroupWithZero R)
  proof: by
  induction γ using ValueGroupWithZero.ind
  simp [mk_eq_div]

中文:
引理 embedding_embed_valuation_eq
  条件: (γ : ValueGroupWithZero R)
  证明: by
  induction γ using ValueGroupWithZero.ind
  simp [mk_eq_div]

Depends on / 依赖: ValueGroupWithZero, ValueGroupWithZero.ind, mk_eq_div
-/
lemma embedding_embed_valuation_eq (γ : ValueGroupWithZero R) :
    embedding (embed (valuation R) γ) = γ := by
  induction γ using ValueGroupWithZero.ind
  simp [mk_eq_div]

/--
lemma `embed_strictMono` / 引理 `embed_strictMono`

English:
lemma embed_strictMono
  given: [v.Compatible]
  statement: StrictMono (embed v)
  proof: by
  intro a b h
  obtain ⟨a, r, rfl⟩ := exists_valuation_div_valuation_eq a
  obtain ⟨b, s, rfl⟩ := exists_valuation_div_valuation_eq b
  rw [← embedding_strictMono.lt_iff_lt]
  simp only [map_div₀]
  rw [div_lt_div_iff₀] at h ⊢
  any_goals simp only [zero_lt_iff, ne_eq, Valuation.apply_posSubmonoi

中文:
引理 embed_strictMono
  条件: [v.Compatible]
  结论: StrictMono (embed v)
  证明: by
  intro a b h
  obtain ⟨a, r, rfl⟩ := exists_valuation_div_valuation_eq a
  obtain ⟨b, s, rfl⟩ := exists_valuation_div_valuation_eq b
  rw [← embedding_strictMono.lt_iff_lt]
  simp only [map_div₀]
  rw [div_lt_div_iff₀] at h ⊢
  any_goals simp only [zero_lt_iff, ne_eq, Valuation.apply_posSubmonoi

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, Valuation, Valuation.apply_posSubmonoid_ne_zero, ZeroHom, ZeroHom.coe_mk, any_goals, apply_posSubmonoid_ne_zero, coe_mk, coe_one, div_one, embedding_res, embedding_strictMono, embedding_strictMono.lt_iff_lt, exists_valuation_div_valuation_eq, isEquiv, lift_valuation, lt_iff_lt, map_mul, map_one
-/
lemma embed_strictMono [v.Compatible] : StrictMono (embed v) := by
  intro a b h
  obtain ⟨a, r, rfl⟩ := exists_valuation_div_valuation_eq a
  obtain ⟨b, s, rfl⟩ := exists_valuation_div_valuation_eq b
  rw [← embedding_strictMono.lt_iff_lt]
  simp only [map_div₀]
  rw [div_lt_div_iff₀] at h ⊢
  any_goals simp only [zero_lt_iff, ne_eq, Valuation.apply_posSubmonoid_ne_zero, not_false_eq_true]
  · rw [← map_mul, ← map_mul, (isEquiv (valuation R) v).lt_iff_lt] at h
    simp only [embed, coe_mk, ZeroHom.coe_mk, lift_valuation,
      OneMemClass.coe_one, map_one, div_one]
    rw [embedding_restrict₀ a]; rw [embedding_restrict₀ b]; rw [embedding_restrict₀ r.1]; rw [embedding_restrict₀ s.1]
    simpa using h
  · simp [restrict₀_apply, embed]
  · simp [restrict₀_apply, embed]

/--
When we have `h : w.IsEquiv v`, the image group (with zero) of `v` is
isomorphic to that of `w` via `h.orderMonoidIso`. Then the following diagram is commutative:
```
              ValueGroup₀ w
                ∧ |
       embed w / |
              / |
ValueGroupWithZero R | h.orderMonoidIso
              \ |
       embed v \ |
                ∨ ∨
              ValueGroup₀ v
```
-/
@[simp]
/--
theorem `orderMonoidIso_embed` / 定理 `orderMonoidIso_embed`

English:
theorem orderMonoidIso_embed
  statement: [v.Compatible] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
  proof: by
  simp only [embed, coe_mk, ZeroHom.coe_mk]
  induction x using ValueGroupWithZero.ind with
  | mk r s => simp [Valuation.IsEquiv.orderMonoidIso_spec₀]

中文:
定理 orderMonoidIso_embed
  结论: [v.Compatible] {Γ' : 类型} [LinearOrderedCommGroupWithZero Γ']
  证明: by
  simp only [embed, coe_mk, ZeroHom.coe_mk]
  induction x using ValueGroupWithZero.ind with
  | mk r s => simp [Valuation.IsEquiv.orderMonoidIso_spec₀]

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.orderMonoidIso_spec, ValueGroupWithZero, ValueGroupWithZero.ind, ZeroHom, ZeroHom.coe_mk, coe_mk
-/
theorem orderMonoidIso_embed [v.Compatible] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (w : Valuation R Γ') [w.Compatible] (x : ValueGroupWithZero R) (h : w.IsEquiv v) :
    h.orderMonoidIso
    (embed w x) = embed v x := by
  simp only [embed, coe_mk, ZeroHom.coe_mk]
  induction x using ValueGroupWithZero.ind with
  | mk r s => simp [Valuation.IsEquiv.orderMonoidIso_spec₀]

/-- If a valuation `v` is compatible with the valuative relation, then `ValueGroupWithZero R`
is isomorphic to the image group (with zero) of `v` as an ordered group with zero. -/
noncomputable
/--
Definition of `orderMonoidIso` / `orderMonoidIso` 的定义

English:
definition orderMonoidIso
  signature: [v.Compatible]
  body: embed v
  invFun x := embedding ((isEquiv v (valuation R)).orderMonoidIso x)
  left_inv x := by simp
  right_inv := Function.rightInverse_of_injective_of_leftInverse
      (by rw [← Function.comp_def, EquivLike.injective_comp]
          exact embedding_strictMono.injective) (fun x => by simp)
  map_

中文:
定义 orderMonoidIso
  签名: [v.Compatible]
  定义体: embed v
  invFun x := embedding ((isEquiv v (valuation R)).orderMonoidIso x)
  left_inv x := by simp
  right_inv := Function.rightInverse_of_injective_of_leftInverse
      (by rw [← Function.comp_def, EquivLike.injective_comp]
          exact embedding_strictMono.injective) (fun x => by simp)
  map_
-/
def orderMonoidIso [v.Compatible] : ValueGroupWithZero R ≃*o ValueGroup₀ (.ofClass v) where
  __ := embed v
  invFun x := embedding ((isEquiv v (valuation R)).orderMonoidIso x)
  left_inv x := by simp
  right_inv := Function.rightInverse_of_injective_of_leftInverse
      (by rw [← Function.comp_def, EquivLike.injective_comp]
          exact embedding_strictMono.injective) (fun x => by simp)
  map_le_map_iff' := (embed_strictMono v).le_iff_le

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embed_mk`, where `embed` is upgraded to
`orderMonoidIso`. -/
@[simp]
/--
lemma `orderMonoidIso_mk` / 引理 `orderMonoidIso_mk`

English:
lemma orderMonoidIso_mk
  given: [v.Compatible] (x : R) (s : posSubmonoid R)
  proof: rfl

中文:
引理 orderMonoidIso_mk
  条件: [v.Compatible] (x : R) (s : posSubmonoid R)
  证明: rfl
-/
lemma orderMonoidIso_mk [v.Compatible] (x : R) (s : posSubmonoid R) :
    orderMonoidIso v (.mk x s) = restrict₀ (.ofClass v) x / (restrict₀ (.ofClass v) s) :=
  rfl

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embed_valuation_eq_restrict₀`,
where `embed` is upgraded to `orderMonoidIso`. -/
@[simp]
/--
lemma `orderMonoidIso_valuation_eq_restrict₀` / 引理 `orderMonoidIso_valuation_eq_restrict₀`

English:
lemma orderMonoidIso_valuation_eq_restrict₀
  given: [v.Compatible] (x : R)
  proof: embed_valuation_eq_restrict₀ v x

中文:
引理 orderMonoidIso_valuation_eq_restrict₀
  条件: [v.Compatible] (x : R)
  证明: embed_valuation_eq_restrict₀ v x
-/
lemma orderMonoidIso_valuation_eq_restrict₀ [v.Compatible] (x : R) :
    orderMonoidIso v (valuation R x) = restrict₀ (.ofClass v) x :=
  embed_valuation_eq_restrict₀ v x

/-- This is the same as `ValuativeRel.ValueGroupWithZero.embedding_embed_valuation_eq`, where
`embed` is upgraded to `orderMonoidIso`. -/
@[simp]
/--
lemma `embedding_orderMonoidIso_valuation_eq` / 引理 `embedding_orderMonoidIso_valuation_eq`

English:
lemma embedding_orderMonoidIso_valuation_eq
  given: (γ : ValueGroupWithZero R)
  proof: embedding_embed_valuation_eq γ

中文:
引理 embedding_orderMonoidIso_valuation_eq
  条件: (γ : ValueGroupWithZero R)
  证明: embedding_embed_valuation_eq γ

Depends on / 依赖: embedding_embed_valuation_eq
-/
lemma embedding_orderMonoidIso_valuation_eq (γ : ValueGroupWithZero R) :
    embedding (orderMonoidIso (valuation R) γ) = γ :=
  embedding_embed_valuation_eq γ

/--
lemma `orderMonoidIso_strictMono` / 引理 `orderMonoidIso_strictMono`

English:
lemma orderMonoidIso_strictMono
  given: [v.Compatible]
  statement: StrictMono (orderMonoidIso v)
  proof: embed_strictMono v

中文:
引理 orderMonoidIso_strictMono
  条件: [v.Compatible]
  结论: StrictMono (orderMonoidIso v)
  证明: embed_strictMono v

Depends on / 依赖: embed_strictMono
-/
lemma orderMonoidIso_strictMono [v.Compatible] : StrictMono (orderMonoidIso v) :=
  embed_strictMono v

/--
lemma `leftInverse_embedding_orderMonoidIso` / 引理 `leftInverse_embedding_orderMonoidIso`

English:
lemma leftInverse_embedding_orderMonoidIso
  statement: Function.LeftInverse embedding
  proof: embedding_orderMonoidIso_valuation_eq

中文:
引理 leftInverse_embedding_orderMonoidIso
  结论: Function.LeftInverse embedding
  证明: embedding_orderMonoidIso_valuation_eq

Depends on / 依赖: embedding_orderMonoidIso_valuation_eq
-/
lemma leftInverse_embedding_orderMonoidIso : Function.LeftInverse embedding
    (orderMonoidIso (valuation R)) :=
  embedding_orderMonoidIso_valuation_eq

/-- The isomorphism between `ValueGroupWithZero R` and `ValueGroup₀ (valuation R)`. -/
@[deprecated "use ValueGroupWithZero.orderMonoidIso instead" (since := "2026-03-17")]
/--
Definition of `valueGroupWithZero_equiv_valueGroup₀` / `valueGroupWithZero_equiv_valueGroup₀` 的定义

English:
definition valueGroupWithZero_equiv_valueGroup₀
  body: orderMonoidIso (valuation R)

中文:
定义 valueGroupWithZero_equiv_valueGroup₀
  定义体: orderMonoidIso (valuation R)

Depends on / 依赖: orderMonoidIso, valuation
-/
def valueGroupWithZero_equiv_valueGroup₀ := orderMonoidIso (valuation R)

end ValueGroupWithZero

open ValueGroupWithZero

@[simp]
/--
lemma `valuation_lt_symm_orderMonoidIso` / 引理 `valuation_lt_symm_orderMonoidIso`

English:
lemma valuation_lt_symm_orderMonoidIso
  given: [v.Compatible] (γ : ValueGroup₀ (.ofClass v)) (x : R)
  proof: calc
    _ ↔ orderMonoidIso v _ < orderMonoidIso v _ := (map_lt_map_iff (orderMonoidIso v)).symm
    _ ↔ _ := by simp [v.restrict_def x]

@[simp]

中文:
引理 valuation_lt_symm_orderMonoidIso
  条件: [v.Compatible] (γ : ValueGroup₀ (.ofClass v)) (x : R)
  证明: calc
    _ ↔ orderMonoidIso v _ < orderMonoidIso v _ := (map_lt_map_iff (orderMonoidIso v)).symm
    _ ↔ _ := by simp [v.restrict_def x]

@[simp]

Depends on / 依赖: map_lt_map_iff, orderMonoidIso, restrict_def, v.restrict_def
-/
lemma valuation_lt_symm_orderMonoidIso [v.Compatible] (γ : ValueGroup₀ (.ofClass v)) (x : R) :
    valuation R x < (orderMonoidIso v).symm γ ↔ v.restrict x < γ :=
  calc
    _ ↔ orderMonoidIso v _ < orderMonoidIso v _ := (map_lt_map_iff (orderMonoidIso v)).symm
    _ ↔ _ := by simp [v.restrict_def x]

@[simp]
/--
lemma `restrict_lt_orderMonoidIso` / 引理 `restrict_lt_orderMonoidIso`

English:
lemma restrict_lt_orderMonoidIso
  given: [v.Compatible] (γ : ValueGroupWithZero R) (x : R)
  proof: by
  simpa using (valuation_lt_symm_orderMonoidIso v (orderMonoidIso v γ) x).symm

中文:
引理 restrict_lt_orderMonoidIso
  条件: [v.Compatible] (γ : ValueGroupWithZero R) (x : R)
  证明: by
  simpa using (valuation_lt_symm_orderMonoidIso v (orderMonoidIso v γ) x).symm

Depends on / 依赖: orderMonoidIso, valuation_lt_symm_orderMonoidIso
-/
lemma restrict_lt_orderMonoidIso [v.Compatible] (γ : ValueGroupWithZero R) (x : R) :
    v.restrict x < (orderMonoidIso v) γ ↔ (valuation R) x < γ := by
  simpa using (valuation_lt_symm_orderMonoidIso v (orderMonoidIso v γ) x).symm

/--
lemma `one_apply_posSubmonoid` / 引理 `one_apply_posSubmonoid`

English:
lemma one_apply_posSubmonoid
  statement: [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R => x = 0]
  proof: Valuation.one_apply_of_ne_zero (by simp)

中文:
引理 one_apply_posSubmonoid
  结论: [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R => x = 0]
  证明: Valuation.one_apply_of_ne_zero (by simp)

Depends on / 依赖: Valuation, Valuation.one_apply_of_ne_zero, one_apply_of_ne_zero
-/
lemma one_apply_posSubmonoid [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R => x = 0]
    (x : posSubmonoid R) : (1 : Valuation R Γ) x = 1 :=
  Valuation.one_apply_of_ne_zero (by simp)

end ValuativeRel

/--
Definition of `ValuativeExtension` / `ValuativeExtension` 的定义

English:
class ValuativeExtension
  parameters: (A B : Type*) [CommSemiring A] [Semiring B] [ValuativeRel A]
  axioms and operations (1):
    - vle_iff_vle((a b : A)) : algebraMap A B a <=ᵥ algebraMap A B b ↔ a <=ᵥ b

中文:
类 ValuativeExtension
  参数: (A B : 类型) [CommSemiring A] [Semiring B] [ValuativeRel A]
  公理与运算 (1 个):
    - vle_iff_vle((a b : A)) : algebraMap A B a <=ᵥ algebraMap A B b ↔ a <=ᵥ b
-/
class ValuativeExtension (A B : Type*) [CommSemiring A] [Semiring B] [ValuativeRel A]
    [ValuativeRel B] [Algebra A B] where
  vle_iff_vle (a b : A) : algebraMap A B a <=ᵥ algebraMap A B b ↔ a <=ᵥ b

namespace ValuativeExtension

open ValuativeRel ValueGroupWithZero MonoidWithZeroHom ValueGroup₀

variable {A B : Type*}

section Semiring

variable [CommSemiring A] [Semiring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/--
lemma `vlt_iff_vlt` / 引理 `vlt_iff_vlt`

English:
lemma vlt_iff_vlt
  given: {a b : A}
  statement: algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b
  proof: by
  rw [← not_vle]; rw [vle_iff_vle]; rw [not_vle]

中文:
引理 vlt_iff_vlt
  条件: {a b : A}
  结论: algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b
  证明: by
  rw [← not_vle]; rw [vle_iff_vle]; rw [not_vle]

Depends on / 依赖: not_vle, vle_iff_vle
-/
lemma vlt_iff_vlt {a b : A} : algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b := by
  rw [← not_vle]; rw [vle_iff_vle]; rw [not_vle]

variable (A B) in
/-- The morphism of `posSubmonoid`s associated to an algebra map.
  This is used in constructing `ValuativeExtension.mapValueGroupWithZero`. -/
@[simps]
/--
Definition of `mapPosSubmonoid` / `mapPosSubmonoid` 的定义

English:
definition mapPosSubmonoid
  signature: : posSubmonoid A ->* posSubmonoid B where
  body: fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, vlt_iff_vlt] using ha⟩
  map_one' := by simp
  map_mul' := by simp

中文:
定义 mapPosSubmonoid
  签名: : posSubmonoid A ->* posSubmonoid B where
  定义体: fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, vlt_iff_vlt] using ha⟩
  map_one' := by simp
  map_mul' := by simp

Depends on / 依赖: algebraMap
-/
def mapPosSubmonoid : posSubmonoid A ->* posSubmonoid B where
  toFun := fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, vlt_iff_vlt] using ha⟩
  map_one' := by simp
  map_mul' := by simp

end Semiring

section Ring

variable [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

variable (A) in
/--
Instance `compatible_comap` / 实例 `compatible_comap`

English:
instance compatible_comap
  signature: {Γ : Type*}
  body: by
  constructor
  simp [← vle_iff_vle (A := A) (B := B), Valuation.Compatible.vle_iff_le (v := w)]

中文:
实例 compatible_comap
  签名: {Γ : 类型}
  定义体: by
  constructor
  simp [← vle_iff_vle (A := A) (B := B), Valuation.Compatible.vle_iff_le (v := w)]

Depends on / 依赖: Compatible, Valuation, Valuation.Compatible.vle_iff_le, vle_iff_le, vle_iff_vle
-/
instance compatible_comap {Γ : Type*}
    [LinearOrderedCommMonoidWithZero Γ] (w : Valuation B Γ) [w.Compatible] :
    (w.comap (algebraMap A B)).Compatible := by
  constructor
  simp [← vle_iff_vle (A := A) (B := B), Valuation.Compatible.vle_iff_le (v := w)]

variable (A B) in
/--
Definition of `mapValueGroupWithZero` / `mapValueGroupWithZero` 的定义

English:
definition mapValueGroupWithZero
  signature: : ValueGroupWithZero A ->*₀ ValueGroupWithZero B
  body: have := compatible_comap A (valuation B)
  embedding.comp (orderMonoidIso ((valuation B).comap (algebraMap A B))).toMonoidWithZeroHom

@[simp]

中文:
定义 mapValueGroupWithZero
  签名: : ValueGroupWithZero A ->*₀ ValueGroupWithZero B
  定义体: have := compatible_comap A (valuation B)
  embedding.comp (orderMonoidIso ((valuation B).comap (algebraMap A B))).toMonoidWithZeroHom

@[simp]

Depends on / 依赖: algebraMap, compatible_comap, embedding, embedding.comp, orderMonoidIso, toMonoidWithZeroHom, valuation
-/
def mapValueGroupWithZero : ValueGroupWithZero A ->*₀ ValueGroupWithZero B :=
  have := compatible_comap A (valuation B)
  embedding.comp (orderMonoidIso ((valuation B).comap (algebraMap A B))).toMonoidWithZeroHom

@[simp]
/--
lemma `mapValueGroupWithZero_mk` / 引理 `mapValueGroupWithZero_mk`

English:
lemma mapValueGroupWithZero_mk
  given: (r : A) (s : posSubmonoid A)
  proof: by
  simp [mapValueGroupWithZero, mk_eq_div (R := B)]

@[simp]

中文:
引理 mapValueGroupWithZero_mk
  条件: (r : A) (s : posSubmonoid A)
  证明: by
  simp [mapValueGroupWithZero, mk_eq_div (R := B)]

@[simp]

Depends on / 依赖: mapValueGroupWithZero, mk_eq_div
-/
lemma mapValueGroupWithZero_mk (r : A) (s : posSubmonoid A) :
    mapValueGroupWithZero A B (.mk r s) = .mk (algebraMap A B r) (mapPosSubmonoid A B s) := by
  simp [mapValueGroupWithZero, mk_eq_div (R := B)]

@[simp]
/--
lemma `mapValueGroupWithZero_valuation` / 引理 `mapValueGroupWithZero_valuation`

English:
lemma mapValueGroupWithZero_valuation
  given: (a : A)
  proof: by
  simp [valuation]

中文:
引理 mapValueGroupWithZero_valuation
  条件: (a : A)
  证明: by
  simp [valuation]

Depends on / 依赖: valuation
-/
lemma mapValueGroupWithZero_valuation (a : A) :
    mapValueGroupWithZero A B (valuation _ a) = valuation _ (algebraMap _ _ a) := by
  simp [valuation]

/--
lemma `mapValueGroupWithZero_strictMono` / 引理 `mapValueGroupWithZero_strictMono`

English:
lemma mapValueGroupWithZero_strictMono
  statement: StrictMono (mapValueGroupWithZero A B)
  proof: embedding_strictMono.comp (embed_strictMono _)

中文:
引理 mapValueGroupWithZero_strictMono
  结论: StrictMono (mapValueGroupWithZero A B)
  证明: embedding_strictMono.comp (embed_strictMono _)

Depends on / 依赖: embed_strictMono, embedding_strictMono, embedding_strictMono.comp
-/
lemma mapValueGroupWithZero_strictMono : StrictMono (mapValueGroupWithZero A B) :=
  embedding_strictMono.comp (embed_strictMono _)

variable (B) in
/--
lemma `_root_.ValuativeRel.IsRankLeOne.of_valuativeExtension` / 引理 `_root_.ValuativeRel.IsRankLeOne.of_valuativeExtension`

English:
lemma _root_.ValuativeRel.IsRankLeOne.of_valuativeExtension
  given: [IsRankLeOne B]
  statement: IsRankLeOne A
  proof: by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := B)
  exact ⟨⟨f.comp (mapValueGroupWithZero _ _), hf.comp mapValueGroupWithZero_strictMono⟩⟩

中文:
引理 _root_.ValuativeRel.IsRankLeOne.of_valuativeExtension
  条件: [IsRankLeOne B]
  结论: IsRankLeOne A
  证明: by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := B)
  exact ⟨⟨f.comp (mapValueGroupWithZero _ _), hf.comp mapValueGroupWithZero_strictMono⟩⟩

Depends on / 依赖: IsRankLeOne, IsRankLeOne.nonempty, f.comp, hf.comp, mapValueGroupWithZero, mapValueGroupWithZero_strictMono, nonempty
-/
lemma _root_.ValuativeRel.IsRankLeOne.of_valuativeExtension [IsRankLeOne B] : IsRankLeOne A := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := B)
  exact ⟨⟨f.comp (mapValueGroupWithZero _ _), hf.comp mapValueGroupWithZero_strictMono⟩⟩

end Ring

end ValuativeExtension

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRankLeOne
  signature: R] : MulArchimedean (ValueGroupWithZero R)
  body: by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

中文:
实例 [IsRankLeOne
  签名: R] : MulArchimedean (ValueGroupWithZero R)
  定义体: by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

Depends on / 依赖: IsRankLeOne, IsRankLeOne.nonempty, f.toMonoidHom, nonempty, toMonoidHom
-/
instance [IsRankLeOne R] : MulArchimedean (ValueGroupWithZero R) := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

end ValuativeRel
