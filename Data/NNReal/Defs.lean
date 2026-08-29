/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Nonnegative real numbers

In this file we define `NNReal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `ConditionallyCompleteLinearOrderBot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `IsOrderedRing ℝ≥0`;
  - `OrderedCommSemiring ℝ≥0`;
  - `CanonicallyOrderedAdd ℝ≥0`;
  - `LinearOrderedCommGroupWithZero ℝ≥0`;
  - `CanonicallyLinearOrderedAddCommMonoid ℝ≥0`;
  - `Archimedean ℝ≥0`;
  - `ConditionallyCompleteLinearOrderBot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`, see `Mathlib/Algebra/Order/Nonneg/Ring.lean`.

* `Real.toNNReal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(Real.toNNReal x) = x` when `0 ≤ x` and
  `↑(Real.toNNReal x) = 0` otherwise.

We also define an instance `CanLift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

This file defines `ℝ≥0` as a localized notation for `NNReal`.
-/

@[expose] public section

assert_not_exists TrivialStar

open Function

/--
Definition of `NNReal` / `NNReal` 的定义

English:
definition NNReal
  body: { r : Real // 0 <= r }

中文:
定义 非负实数
  定义体: { r : Real // 0 <= r }
-/
def NNReal := { r : Real // 0 <= r }

namespace NNReal

@[inherit_doc] scoped notation "Real>=0" => NNReal

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: : Real>=0 -> Real
  body: Subtype.val

中文:
定义 to实数
  签名: : 实数>=0 -> 实数
  定义体: Subtype.val
-/
@[coe] def toReal : Real>=0 -> Real := Subtype.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Real>=0 Real
  body: ⟨toReal⟩

中文:
实例 :
  签名: Coe 实数>=0 实数
  定义体: ⟨toReal⟩

Depends on / 依赖: toReal
-/
instance : Coe Real>=0 Real := ⟨toReal⟩

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : Real) (hx : 0 <= x)
  body: ⟨x, hx⟩

中文:
定义 mk
  签名: (x : 实数) (hx : 0 <= x)
  定义体: ⟨x, hx⟩
-/
protected def mk (x : Real) (hx : 0 <= x) : Real>=0 := ⟨x, hx⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Real>=0
  body: ⟨.mk 0 le_rfl⟩

中文:
实例 :
  签名: 零 实数>=0
  定义体: ⟨.mk 0 le_rfl⟩

Depends on / 依赖: le_rfl
-/
instance : Zero Real>=0 := ⟨.mk 0 le_rfl⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Real>=0
  body: ⟨.mk 1 zero_le_one⟩

中文:
实例 :
  签名: 幺 实数>=0
  定义体: ⟨.mk 1 zero_le_one⟩

Depends on / 依赖: zero_le_one
-/
instance : One Real>=0 := ⟨.mk 1 zero_le_one⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot Real>=0
  body: ⟨0⟩

deriving instance
  Nontrivial, Inhabited,
  PartialOrder, SemilatticeSup, SemilatticeInf, DistribLattice,
  Semiring, CommMonoidWithZero, CommSemiring, AddCancelCommMonoid,
  Sub, OrderedSub, OrderBot,
  CanonicallyOrderedAdd, NoZeroDivisors, DenselyOrdered,
  Archimedean, MulArchimedean, IsOr

中文:
实例 :
  签名: 底元素 实数>=0
  定义体: ⟨0⟩

deriving instance
  Nontrivial, Inhabited,
  PartialOrder, SemilatticeSup, SemilatticeInf, DistribLattice,
  Semiring, CommMonoidWithZero, CommSemiring, AddCancelCommMonoid,
  Sub, OrderedSub, OrderBot,
  CanonicallyOrderedAdd, NoZeroDivisors, DenselyOrdered,
  Archimedean, MulArchimedean, IsOr
-/
instance : Bot Real>=0 := ⟨0⟩

deriving instance
  Nontrivial, Inhabited,
  PartialOrder, SemilatticeSup, SemilatticeInf, DistribLattice,
  Semiring, CommMonoidWithZero, CommSemiring, AddCancelCommMonoid,
  Sub, OrderedSub, OrderBot,
  CanonicallyOrderedAdd, NoZeroDivisors, DenselyOrdered,
  Archimedean, MulArchimedean, IsOrderedRing, IsStrictOrderedRing
  for NNReal

noncomputable section
deriving instance LinearOrder for NNReal
end

example : (0 : Real>=0) = ⊥ := by with_reducible_and_instances rfl

-- a computable copy of `Nonneg.instNNRatCast`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NNRatCast Real>=0
  body: ⟨r, r.cast_nonneg⟩

中文:
实例 :
  签名: 非负有理数嵌入 实数>=0
  定义体: ⟨r, r.cast_nonneg⟩

Depends on / 依赖: cast_nonneg, r.cast_nonneg
-/
instance : NNRatCast Real>=0 where nnratCast r := ⟨r, r.cast_nonneg⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv Real>=0
  body: .mk (x : Real)⁻¹ (inv_nonneg.mpr x.2)

中文:
实例 :
  签名: 取逆 实数>=0
  定义体: .mk (x : Real)⁻¹ (inv_nonneg.mpr x.2)

Depends on / 依赖: inv_nonneg, inv_nonneg.mpr
-/
noncomputable instance : Inv Real>=0 where
  inv x := .mk (x : Real)⁻¹ (inv_nonneg.mpr x.2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div Real>=0
  body: .mk ((x : Real) / (y : Real)) (div_nonneg x.2 y.2)

中文:
实例 :
  签名: 除法 实数>=0
  定义体: .mk ((x : Real) / (y : Real)) (div_nonneg x.2 y.2)

Depends on / 依赖: div_nonneg
-/
noncomputable instance : Div Real>=0 where
  div x y := .mk ((x : Real) / (y : Real)) (div_nonneg x.2 y.2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Rat>=0 Real>=0
  body: .mk (x • (y : Real)) (by rw [NNRat.smul_def]; exact mul_nonneg x.cast_nonneg y.2)

中文:
实例 :
  签名: 标量乘法 有理数>=0 实数>=0
  定义体: .mk (x • (y : Real)) (by rw [NNRat.smul_def]; exact mul_nonneg x.cast_nonneg y.2)

Depends on / 依赖: NNRat.smul_def, cast_nonneg, mul_nonneg, smul_def, x.cast_nonneg
-/
noncomputable instance : SMul Rat>=0 Real>=0 where
  smul x y := .mk (x • (y : Real)) (by rw [NNRat.smul_def]; exact mul_nonneg x.cast_nonneg y.2)

/--
Instance `zpow` / 实例 `zpow`

English:
instance zpow
  signature: : Pow Real>=0 Int where
  body: .mk ((x : Real) ^ n) (zpow_nonneg x.2 _)

中文:
实例 zpow
  签名: : 幂 实数>=0 整数 where
  定义体: .mk ((x : Real) ^ n) (zpow_nonneg x.2 _)

Depends on / 依赖: zpow_nonneg
-/
noncomputable instance zpow : Pow Real>=0 Int where
  pow x n := .mk ((x : Real) ^ n) (zpow_nonneg x.2 _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semifield Real>=0
  body: fast_instance%
  Function.Injective.semifield toReal Subtype.val_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

中文:
实例 :
  签名: 半域 实数>=0
  定义体: fast_instance%
  Function.Injective.semifield toReal Subtype.val_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: fast_instance
-/
noncomputable instance : Semifield Real>=0 := fast_instance%
  Function.Injective.semifield toReal Subtype.val_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing Real>=0
  body: Nonneg.isOrderedRing

中文:
实例 :
  签名: 是Ordered环 实数>=0
  定义体: Nonneg.isOrderedRing

Depends on / 依赖: Nonneg, Nonneg.isOrderedRing, isOrderedRing
-/
instance : IsOrderedRing Real>=0 :=
  Nonneg.isOrderedRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictOrderedRing Real>=0
  body: Nonneg.isStrictOrderedRing

中文:
实例 :
  签名: 是StrictOrdered环 实数>=0
  定义体: Nonneg.isStrictOrderedRing

Depends on / 依赖: Nonneg, Nonneg.isStrictOrderedRing, isStrictOrderedRing
-/
instance : IsStrictOrderedRing Real>=0 :=
  Nonneg.isStrictOrderedRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedCommGroupWithZero Real>=0
  body: h.2

example {p q : Real>=0} (h1p : 0 < p) (h2p : p <= q) : q⁻¹ <= p⁻¹ := by
  with_reducible_and_instances exact inv_anti₀ h1p h2p

中文:
实例 :
  签名: 带零LinearOrderedComm群 实数>=0
  定义体: h.2

example {p q : Real>=0} (h1p : 0 < p) (h2p : p <= q) : q⁻¹ <= p⁻¹ := by
  with_reducible_and_instances exact inv_anti₀ h1p h2p
-/
noncomputable instance : LinearOrderedCommGroupWithZero Real>=0 where
  bot_le h := h.2

example {p q : Real>=0} (h1p : 0 < p) (h2p : p <= q) : q⁻¹ <= p⁻¹ := by
  with_reducible_and_instances exact inv_anti₀ h1p h2p

/--
lemma `mk_coe` / 引理 `mk_coe`

English:
lemma mk_coe
  given: (a : Real>=0) (ha : 0 <= (a : Real))
  statement: NNReal.mk (a : Real) ha = a
  proof: rfl

中文:
引理 mk_coe
  条件: (a : 实数>=0) (ha : 0 <= (a : 实数))
  结论: 非负实数.mk (a : 实数) ha = a
  证明: rfl
-/
@[simp] lemma mk_coe (a : Real>=0) (ha : 0 <= (a : Real)) : NNReal.mk (a : Real) ha = a := rfl

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
/--
theorem `val_eq_coe` / 定理 `val_eq_coe`

English:
theorem val_eq_coe
  given: (n : Real>=0)
  statement: n.val = n
  proof: rfl

中文:
定理 val_eq_coe
  条件: (n : 实数>=0)
  结论: n.val = n
  证明: rfl
-/
theorem val_eq_coe (n : Real>=0) : n.val = n :=
  rfl

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Real Real>=0 toReal fun r => 0 <= r
  body: Subtype.canLift _

中文:
实例 canLift
  签名: : CanLift 实数 实数>=0 to实数 fun r => 0 <= r
  定义体: Subtype.canLift _

Depends on / 依赖: Subtype, Subtype.canLift, canLift
-/
instance canLift : CanLift Real Real>=0 toReal fun r => 0 <= r :=
  Subtype.canLift _

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {n m : Real>=0}
  statement: (n : Real) = (m : Real) -> n = m
  proof: Subtype.ext

中文:
定理 eq
  条件: {n m : 实数>=0}
  结论: (n : 实数) = (m : 实数) -> n = m
  证明: Subtype.ext
-/
@[ext] protected theorem eq {n m : Real>=0} : (n : Real) = (m : Real) -> n = m :=
  Subtype.ext

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {x y : Real>=0}
  statement: (x : Real) != (y : Real) ↔ x != y
  proof: not_congr NNReal.eq_iff.symm

中文:
定理 ne_iff
  条件: {x y : 实数>=0}
  结论: (x : 实数) != (y : 实数) ↔ x != y
  证明: not_congr NNReal.eq_iff.symm

Depends on / 依赖: NNReal, NNReal.eq_iff.symm, eq_iff, not_congr
-/
theorem ne_iff {x y : Real>=0} : (x : Real) != (y : Real) ↔ x != y :=
not_congr NNReal.eq_iff.symm

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : Real>=0 -> Prop}
  proof: Subtype.forall

中文:
定理 «对任意»
  条件: {p : 实数>=0 -> 命题}
  证明: Subtype.forall
-/
protected theorem «forall» {p : Real>=0 -> Prop} :
    (forall x : Real>=0, p x) ↔ forall (x : Real) (hx : 0 <= x), p (.mk x hx) :=
  Subtype.forall

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : Real>=0 -> Prop}
  proof: Subtype.exists

中文:
定理 «存在»
  条件: {p : 实数>=0 -> 命题}
  证明: Subtype.exists
-/
protected theorem «exists» {p : Real>=0 -> Prop} :
    (exists x : Real>=0, p x) ↔ exists (x : Real) (hx : 0 <= x), p (.mk x hx) :=
  Subtype.exists

/--
Definition of `_root_.Real.toNNReal` / `_root_.Real.toNNReal` 的定义

English:
definition _root_.Real.toNNReal
  signature: (r : Real)
  body: .mk (max r 0) (le_max_right _ _)

中文:
定义 _root_.实数.toNN实数
  签名: (r : 实数)
  定义体: .mk (max r 0) (le_max_right _ _)

Depends on / 依赖: le_max_right
-/
def _root_.Real.toNNReal (r : Real) : Real>=0 :=
  .mk (max r 0) (le_max_right _ _)

/--
theorem `_root_.Real.coe_toNNReal` / 定理 `_root_.Real.coe_toNNReal`

English:
theorem _root_.Real.coe_toNNReal
  given: (r : Real) (hr : 0 <= r)
  statement: (Real.toNNReal r : Real) = r
  proof: max_eq_left hr

中文:
定理 _root_.实数.coe_toNN实数
  条件: (r : 实数) (hr : 0 <= r)
  结论: (实数.toNN实数 r : 实数) = r
  证明: max_eq_left hr

Depends on / 依赖: max_eq_left
-/
theorem _root_.Real.coe_toNNReal (r : Real) (hr : 0 <= r) : (Real.toNNReal r : Real) = r :=
  max_eq_left hr

/--
theorem `_root_.Real.toNNReal_of_nonneg` / 定理 `_root_.Real.toNNReal_of_nonneg`

English:
theorem _root_.Real.toNNReal_of_nonneg
  given: {r : Real} (hr : 0 <= r)
  statement: r.toNNReal = .mk r hr
  proof: by
  simp_rw [Real.toNNReal, max_eq_left hr]

中文:
定理 _root_.实数.toNN实数_of_nonneg
  条件: {r : 实数} (hr : 0 <= r)
  结论: r.toNN实数 = .mk r hr
  证明: by
  simp_rw [Real.toNNReal, max_eq_left hr]

Depends on / 依赖: Real.toNNReal, max_eq_left, simp_rw, toNNReal
-/
theorem _root_.Real.toNNReal_of_nonneg {r : Real} (hr : 0 <= r) : r.toNNReal = .mk r hr := by
  simp_rw [Real.toNNReal, max_eq_left hr]

/--
theorem `_root_.Real.le_coe_toNNReal` / 定理 `_root_.Real.le_coe_toNNReal`

English:
theorem _root_.Real.le_coe_toNNReal
  given: (r : Real)
  statement: r <= Real.toNNReal r
  proof: le_max_left r 0

中文:
定理 _root_.实数.le_coe_toNN实数
  条件: (r : 实数)
  结论: r <= 实数.toNN实数 r
  证明: le_max_left r 0

Depends on / 依赖: le_max_left
-/
theorem _root_.Real.le_coe_toNNReal (r : Real) : r <= Real.toNNReal r :=
  le_max_left r 0

/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: (r : Real>=0)
  statement: (0 : Real) <= r
  proof: r.2

中文:
定理 coe_nonneg
  条件: (r : 实数>=0)
  结论: (0 : 实数) <= r
  证明: r.2
-/
@[bound] theorem coe_nonneg (r : Real>=0) : (0 : Real) <= r := r.2
/--
lemma `not_toReal_neg` / 引理 `not_toReal_neg`

English:
lemma not_toReal_neg
  given: {r : Real>=0}
  statement: ¬ r.toReal < 0
  proof: r.coe_nonneg.not_gt

中文:
引理 not_to实数_neg
  条件: {r : 实数>=0}
  结论: ¬ r.to实数 < 0
  证明: r.coe_nonneg.not_gt
-/
@[simp] lemma not_toReal_neg {r : Real>=0} : ¬ r.toReal < 0 := r.coe_nonneg.not_gt

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (a : Real) (ha)
  statement: toReal (.mk a ha) = a
  proof: rfl

example : Zero Real>=0 := by infer_instance

example : One Real>=0 := by infer_instance

example : Add Real>=0 := by infer_instance

example : Sub Real>=0 := by infer_instance

example : Mul Real>=0 := by infer_instance

noncomputable example : Inv Real>=0 := by infer_instance

noncomputable ex

中文:
定理 coe_mk
  条件: (a : 实数) (ha)
  结论: to实数 (.mk a ha) = a
  证明: rfl

example : Zero Real>=0 := by infer_instance

example : One Real>=0 := by infer_instance

example : Add Real>=0 := by infer_instance

example : Sub Real>=0 := by infer_instance

example : Mul Real>=0 := by infer_instance

noncomputable example : Inv Real>=0 := by infer_instance

noncomputable ex
-/
@[simp, norm_cast] theorem coe_mk (a : Real) (ha) : toReal (.mk a ha) = a := rfl

example : Zero Real>=0 := by infer_instance

example : One Real>=0 := by infer_instance

example : Add Real>=0 := by infer_instance

example : Sub Real>=0 := by infer_instance

example : Mul Real>=0 := by infer_instance

noncomputable example : Inv Real>=0 := by infer_instance

noncomputable example : Div Real>=0 := by infer_instance

example : LE Real>=0 := by infer_instance

example : Bot Real>=0 := by infer_instance

example : Inhabited Real>=0 := by infer_instance

example : Nontrivial Real>=0 := by infer_instance

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Real>=0 -> Real)
  proof: Subtype.coe_injective

中文:
定理 coe_injective
  结论: 单射 ((↑) : 实数>=0 -> 实数)
  证明: Subtype.coe_injective
-/
protected theorem coe_injective : Injective ((↑) : Real>=0 -> Real) := Subtype.coe_injective

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: {r₁ r₂ : Real>=0}
  statement: (r₁ : Real) = r₂ ↔ r₁ = r₂
  proof: NNReal.coe_injective.eq_iff

中文:
引理 coe_inj
  条件: {r₁ r₂ : 实数>=0}
  结论: (r₁ : 实数) = r₂ ↔ r₁ = r₂
  证明: NNReal.coe_injective.eq_iff
-/
@[simp, norm_cast] lemma coe_inj {r₁ r₂ : Real>=0} : (r₁ : Real) = r₂ ↔ r₁ = r₂ :=
  NNReal.coe_injective.eq_iff


/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : Real>=0) : Real) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ((0 : 实数>=0) : 实数) = 0
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ((0 : Real>=0) : Real) = 0 := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : Real>=0) : Real) = 1
  proof: rfl

中文:
引理 coe_one
  结论: ((1 : 实数>=0) : 实数) = 1
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ((1 : Real>=0) : Real) = 1 := rfl

/--
lemma `mk_zero` / 引理 `mk_zero`

English:
lemma mk_zero
  statement: NNReal.mk 0 le_rfl = 0
  proof: rfl

中文:
引理 mk_zero
  结论: 非负实数.mk 0 le_rfl = 0
  证明: rfl
-/
@[simp] lemma mk_zero : NNReal.mk 0 le_rfl = 0 := rfl
/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  statement: NNReal.mk 1 zero_le_one = 1
  proof: rfl

@[simp, norm_cast]

中文:
引理 mk_one
  结论: 非负实数.mk 1 zero_le_one = 1
  证明: rfl

@[simp, norm_cast]
-/
@[simp] lemma mk_one : NNReal.mk 1 zero_le_one = 1 := rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (r₁ r₂ : Real>=0)
  statement: ((r₁ + r₂ : Real>=0) : Real) = r₁ + r₂
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (r₁ r₂ : 实数>=0)
  结论: ((r₁ + r₂ : 实数>=0) : 实数) = r₁ + r₂
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_add (r₁ r₂ : Real>=0) : ((r₁ + r₂ : Real>=0) : Real) = r₁ + r₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (r₁ r₂ : Real>=0)
  statement: ((r₁ * r₂ : Real>=0) : Real) = r₁ * r₂
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (r₁ r₂ : 实数>=0)
  结论: ((r₁ * r₂ : 实数>=0) : 实数) = r₁ * r₂
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_mul (r₁ r₂ : Real>=0) : ((r₁ * r₂ : Real>=0) : Real) = r₁ * r₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (r : Real>=0)
  statement: ((r⁻¹ : Real>=0) : Real) = (r : Real)⁻¹
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: (r : 实数>=0)
  结论: ((r⁻¹ : 实数>=0) : 实数) = (r : 实数)⁻¹
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_inv (r : Real>=0) : ((r⁻¹ : Real>=0) : Real) = (r : Real)⁻¹ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (r₁ r₂ : Real>=0)
  statement: ((r₁ / r₂ : Real>=0) : Real) = (r₁ : Real) / r₂
  proof: rfl

中文:
定理 coe_div
  条件: (r₁ r₂ : 实数>=0)
  结论: ((r₁ / r₂ : 实数>=0) : 实数) = (r₁ : 实数) / r₂
  证明: rfl
-/
protected theorem coe_div (r₁ r₂ : Real>=0) : ((r₁ / r₂ : Real>=0) : Real) = (r₁ : Real) / r₂ :=
  rfl

/--
theorem `coe_two` / 定理 `coe_two`

English:
theorem coe_two
  statement: ((2 : Real>=0) : Real) = 2
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_two
  结论: ((2 : 实数>=0) : 实数) = 2
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_two : ((2 : Real>=0) : Real) = 2 := rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: {r₁ r₂ : Real>=0} (h : r₂ <= r₁)
  statement: ((r₁ - r₂ : Real>=0) : Real) = ↑r₁ - ↑r₂
  proof: max_eq_left le_sub_comm.2 by simp [show (r₂ : Real) <= r₁ from h]

中文:
定理 coe_sub
  条件: {r₁ r₂ : 实数>=0} (h : r₂ <= r₁)
  结论: ((r₁ - r₂ : 实数>=0) : 实数) = ↑r₁ - ↑r₂
  证明: max_eq_left le_sub_comm.2 by simp [show (r₂ : Real) <= r₁ from h]
-/
protected theorem coe_sub {r₁ r₂ : Real>=0} (h : r₂ <= r₁) : ((r₁ - r₂ : Real>=0) : Real) = ↑r₁ - ↑r₂ :=
max_eq_left le_sub_comm.2 by simp [show (r₂ : Real) <= r₁ from h]

variable {r r₁ r₂ : Real>=0} {x y : Real}

/--
lemma `coe_eq_zero` / 引理 `coe_eq_zero`

English:
lemma coe_eq_zero
  statement: (r : Real) = 0 ↔ r = 0
  proof: by rw [← coe_zero, coe_inj]

中文:
引理 coe_eq_zero
  结论: (r : 实数) = 0 ↔ r = 0
  证明: by rw [← coe_zero, coe_inj]
-/
@[simp, norm_cast] lemma coe_eq_zero : (r : Real) = 0 ↔ r = 0 := by rw [← coe_zero, coe_inj]

/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: (r : Real) = 1 ↔ r = 1
  proof: by rw [← coe_one, coe_inj]

中文:
引理 coe_eq_one
  结论: (r : 实数) = 1 ↔ r = 1
  证明: by rw [← coe_one, coe_inj]
-/
@[simp, norm_cast] lemma coe_eq_one : (r : Real) = 1 ↔ r = 1 := by rw [← coe_one, coe_inj]

/--
lemma `coe_ne_zero` / 引理 `coe_ne_zero`

English:
lemma coe_ne_zero
  statement: (r : Real) != 0 ↔ r != 0
  proof: coe_eq_zero.not

中文:
引理 coe_ne_zero
  结论: (r : 实数) != 0 ↔ r != 0
  证明: coe_eq_zero.not
-/
@[norm_cast] lemma coe_ne_zero : (r : Real) != 0 ↔ r != 0 := coe_eq_zero.not

/--
lemma `coe_ne_one` / 引理 `coe_ne_one`

English:
lemma coe_ne_one
  statement: (r : Real) != 1 ↔ r != 1
  proof: coe_eq_one.not

example : CommSemiring Real>=0 := by infer_instance

中文:
引理 coe_ne_one
  结论: (r : 实数) != 1 ↔ r != 1
  证明: coe_eq_one.not

example : CommSemiring Real>=0 := by infer_instance
-/
@[norm_cast] lemma coe_ne_one : (r : Real) != 1 ↔ r != 1 := coe_eq_one.not

example : CommSemiring Real>=0 := by infer_instance

/--
Definition of `toRealHom` / `toRealHom` 的定义

English:
definition toRealHom
  signature: : Real>=0 ->+* Real where
  body: (↑)
  map_one' := NNReal.coe_one
  map_mul' := NNReal.coe_mul
  map_zero' := NNReal.coe_zero
  map_add' := NNReal.coe_add

中文:
定义 to实数Hom
  签名: : 实数>=0 ->+* 实数 where
  定义体: (↑)
  map_one' := NNReal.coe_one
  map_mul' := NNReal.coe_mul
  map_zero' := NNReal.coe_zero
  map_add' := NNReal.coe_add
-/
def toRealHom : Real>=0 ->+* Real where
  toFun := (↑)
  map_one' := NNReal.coe_one
  map_mul' := NNReal.coe_mul
  map_zero' := NNReal.coe_zero
  map_add' := NNReal.coe_add

/--
theorem `coe_toRealHom` / 定理 `coe_toRealHom`

English:
theorem coe_toRealHom
  statement: ⇑toRealHom = toReal
  proof: rfl

中文:
定理 coe_to实数Hom
  结论: ⇑to实数Hom = to实数
  证明: rfl
-/
@[simp] theorem coe_toRealHom : ⇑toRealHom = toReal := rfl

section Actions

/-- A scalar multiplication over `ℝ` restricts to a scalar multiplication over `ℝ≥0`. -/
instance {M : Type*} [SMul Real M] : SMul Real>=0 M :=
  ⟨fun c m => (c : Real) • m⟩

/-- A `MulAction` over `ℝ` restricts to a `MulAction` over `ℝ≥0`. -/
instance {M : Type*} [MulAction Real M] : MulAction Real>=0 M :=
  fast_instance% MulAction.compHom M toRealHom.toMonoidHom

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: {M : Type*} [SMul Real M] (c : Real>=0) (x : M)
  statement: c • x = (c : Real) • x
  proof: rfl

中文:
定理 smul_def
  条件: {M : 类型} [标量乘法 实数 M] (c : 实数>=0) (x : M)
  结论: c • x = (c : 实数) • x
  证明: rfl
-/
theorem smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M) : c • x = (c : Real) • x :=
  rfl

instance {M N : Type*} [MulAction Real M] [MulAction Real N] [SMul M N] [IsScalarTower Real M N] :
    IsScalarTower Real>=0 M N where smul_assoc r := smul_assoc (r : Real)

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommClass Real M N]
  body: smul_comm (r : Real)

中文:
实例 smulCommClass_left
  签名: {M N : 类型} [乘法作用 实数 N] [标量乘法 M N] [标量交换类 实数 M N]
  定义体: smul_comm (r : Real)

Depends on / 依赖: smul_comm
-/
instance smulCommClass_left {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommClass Real M N] :
    SMulCommClass Real>=0 M N where smul_comm r := smul_comm (r : Real)

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommClass M Real N]
  body: smul_comm m (r : Real)

中文:
实例 smulCommClass_right
  签名: {M N : 类型} [乘法作用 实数 N] [标量乘法 M N] [标量交换类 M 实数 N]
  定义体: smul_comm m (r : Real)

Depends on / 依赖: smul_comm
-/
instance smulCommClass_right {M N : Type*} [MulAction Real N] [SMul M N] [SMulCommClass M Real N] :
    SMulCommClass M Real>=0 N where smul_comm m r := smul_comm m (r : Real)

/-- A `DistribMulAction` over `ℝ` restricts to a `DistribMulAction` over `ℝ≥0`. -/
instance {M : Type*} [AddMonoid M] [DistribMulAction Real M] : DistribMulAction Real>=0 M :=
  fast_instance% DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `Module` over `ℝ` restricts to a `Module` over `ℝ≥0`. -/
instance {M : Type*} [AddCommMonoid M] [Module Real M] : Module Real>=0 M :=
  fast_instance% Module.compHom M toRealHom

/-- An `Algebra` over `ℝ` restricts to an `Algebra` over `ℝ≥0`. -/
instance {A : Type*} [Semiring A] [Algebra Real A] : Algebra Real>=0 A where
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : Real) x, smul_def]
  algebraMap := (algebraMap Real A).comp (toRealHom : Real>=0 ->+* Real)

-- verify that the above produces instances we might care about
example : Algebra Real>=0 Real := by infer_instance

example : DistribMulAction Real>=0ˣ Real := by infer_instance

end Actions

example : MonoidWithZero Real>=0 := by infer_instance

example : CommMonoidWithZero Real>=0 := by infer_instance

noncomputable example : CommGroupWithZero Real>=0 := by infer_instance

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (r : Real>=0) (n : Nat)
  statement: ((r ^ n : Real>=0) : Real) = (r : Real) ^ n
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_pow
  条件: (r : 实数>=0) (n : 自然数)
  结论: ((r ^ n : 实数>=0) : 实数) = (r : 实数) ^ n
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : Real) = (r : Real) ^ n := rfl

@[simp, norm_cast]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (r : Real>=0) (n : Int)
  statement: ((r ^ n : Real>=0) : Real) = (r : Real) ^ n
  proof: rfl

中文:
定理 coe_zpow
  条件: (r : 实数>=0) (n : 整数)
  结论: ((r ^ n : 实数>=0) : 实数) = (r : 实数) ^ n
  证明: rfl
-/
theorem coe_zpow (r : Real>=0) (n : Int) : ((r ^ n : Real>=0) : Real) = (r : Real) ^ n := rfl

variable {ι : Type*} {f : ι -> Real}

/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (r : Real>=0) (n : Nat)
  statement: ↑(n • r) = n • (r : Real)
  proof: rfl

中文:
引理 coe_nsmul
  条件: (r : 实数>=0) (n : 自然数)
  结论: ↑(n • r) = n • (r : 实数)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nsmul (r : Real>=0) (n : Nat) : ↑(n • r) = n • (r : Real) := rfl
/--
lemma `coe_nnqsmul` / 引理 `coe_nnqsmul`

English:
lemma coe_nnqsmul
  given: (q : Rat>=0) (x : Real>=0)
  statement: ↑(q • x) = (q • x : Real)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_nnqsmul
  条件: (q : 有理数>=0) (x : 实数>=0)
  结论: ↑(q • x) = (q • x : 实数)
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_nnqsmul (q : Rat>=0) (x : Real>=0) : ↑(q • x) = (q • x : Real) := rfl

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: (↑(↑n : Real>=0) : Real) = n
  proof: map_natCast toRealHom n

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: (↑(↑n : 实数>=0) : 实数) = n
  证明: map_natCast toRealHom n

@[simp, norm_cast]
-/
protected theorem coe_natCast (n : Nat) : (↑(↑n : Real>=0) : Real) = n :=
  map_natCast toRealHom n

@[simp, norm_cast]
/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ((ofNat(n) : Real>=0) : Real) = ofNat(n)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ((of自然数(n) : 实数>=0) : 实数) = of自然数(n)
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real>=0) : Real) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ofScientific` / 定理 `coe_ofScientific`

English:
theorem coe_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    ↑(OfScientific.ofScientific m s e : Real>=0) = (OfScientific.ofScientific m s e : Real) :=
  rfl

@[simp, norm_cast]
/--
lemma `algebraMap_eq_coe` / 引理 `algebraMap_eq_coe`

English:
lemma algebraMap_eq_coe
  statement: (algebraMap Real>=0 Real : Real>=0 -> Real) = (↑)
  proof: rfl

noncomputable example : LinearOrder Real>=0 := by infer_instance

中文:
引理 algebraMap_eq_coe
  结论: (algebraMap 实数>=0 实数 : 实数>=0 -> 实数) = (↑)
  证明: rfl

noncomputable example : LinearOrder Real>=0 := by infer_instance
-/
lemma algebraMap_eq_coe : (algebraMap Real>=0 Real : Real>=0 -> Real) = (↑) := rfl

noncomputable example : LinearOrder Real>=0 := by infer_instance

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: (r₁ : Real) <= r₂ ↔ r₁ <= r₂
  proof: Iff.rfl

中文:
引理 coe_le_coe
  结论: (r₁ : 实数) <= r₂ ↔ r₁ <= r₂
  证明: Iff.rfl
-/
@[simp, norm_cast, gcongr] lemma coe_le_coe : (r₁ : Real) <= r₂ ↔ r₁ <= r₂ := Iff.rfl

/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: (r₁ : Real) < r₂ ↔ r₁ < r₂
  proof: Iff.rfl

@[bound] private alias ⟨_, Bound.coe_lt_coe_of_lt⟩ := coe_lt_coe

中文:
引理 coe_lt_coe
  结论: (r₁ : 实数) < r₂ ↔ r₁ < r₂
  证明: Iff.rfl

@[bound] private alias ⟨_, Bound.coe_lt_coe_of_lt⟩ := coe_lt_coe
-/
@[simp, norm_cast, gcongr] lemma coe_lt_coe : (r₁ : Real) < r₂ ↔ r₁ < r₂ := Iff.rfl

@[bound] private alias ⟨_, Bound.coe_lt_coe_of_lt⟩ := coe_lt_coe

/--
lemma `coe_pos` / 引理 `coe_pos`

English:
lemma coe_pos
  statement: (0 : Real) < r ↔ 0 < r
  proof: Iff.rfl

@[bound] private alias ⟨_, Bound.coe_pos_of_pos⟩ := coe_pos

中文:
引理 coe_pos
  结论: (0 : 实数) < r ↔ 0 < r
  证明: Iff.rfl

@[bound] private alias ⟨_, Bound.coe_pos_of_pos⟩ := coe_pos
-/
@[simp, norm_cast] lemma coe_pos : (0 : Real) < r ↔ 0 < r := Iff.rfl

@[bound] private alias ⟨_, Bound.coe_pos_of_pos⟩ := coe_pos

/--
lemma `one_le_coe` / 引理 `one_le_coe`

English:
lemma one_le_coe
  statement: 1 <= (r : Real) ↔ 1 <= r
  proof: by rw [← coe_le_coe, coe_one]

中文:
引理 one_le_coe
  结论: 1 <= (r : 实数) ↔ 1 <= r
  证明: by rw [← coe_le_coe, coe_one]
-/
@[simp, norm_cast] lemma one_le_coe : 1 <= (r : Real) ↔ 1 <= r := by rw [← coe_le_coe, coe_one]
/--
lemma `one_lt_coe` / 引理 `one_lt_coe`

English:
lemma one_lt_coe
  statement: 1 < (r : Real) ↔ 1 < r
  proof: by rw [← coe_lt_coe, coe_one]

中文:
引理 one_lt_coe
  结论: 1 < (r : 实数) ↔ 1 < r
  证明: by rw [← coe_lt_coe, coe_one]
-/
@[simp, norm_cast] lemma one_lt_coe : 1 < (r : Real) ↔ 1 < r := by rw [← coe_lt_coe, coe_one]
/--
lemma `coe_le_one` / 引理 `coe_le_one`

English:
lemma coe_le_one
  statement: (r : Real) <= 1 ↔ r <= 1
  proof: by rw [← coe_le_coe, coe_one]

中文:
引理 coe_le_one
  结论: (r : 实数) <= 1 ↔ r <= 1
  证明: by rw [← coe_le_coe, coe_one]
-/
@[simp, norm_cast] lemma coe_le_one : (r : Real) <= 1 ↔ r <= 1 := by rw [← coe_le_coe, coe_one]
/--
lemma `coe_lt_one` / 引理 `coe_lt_one`

English:
lemma coe_lt_one
  statement: (r : Real) < 1 ↔ r < 1
  proof: by rw [← coe_lt_coe, coe_one]

中文:
引理 coe_lt_one
  结论: (r : 实数) < 1 ↔ r < 1
  证明: by rw [← coe_lt_coe, coe_one]
-/
@[simp, norm_cast] lemma coe_lt_one : (r : Real) < 1 ↔ r < 1 := by rw [← coe_lt_coe, coe_one]

/--
lemma `coe_mono` / 引理 `coe_mono`

English:
lemma coe_mono
  statement: Monotone ((↑) : Real>=0 -> Real)
  proof: fun _ _ => NNReal.coe_le_coe.2

中文:
引理 coe_mono
  结论: 递增 ((↑) : 实数>=0 -> 实数)
  证明: fun _ _ => NNReal.coe_le_coe.2
-/
@[gcongr, mono] lemma coe_mono : Monotone ((↑) : Real>=0 -> Real) := fun _ _ => NNReal.coe_le_coe.2

/--
theorem `_root_.Real.toNNReal_monotone` / 定理 `_root_.Real.toNNReal_monotone`

English:
theorem _root_.Real.toNNReal_monotone
  statement: Monotone Real.toNNReal
  proof: fun _ _ h =>
  max_le_max_right _ h

@[gcongr]

中文:
定理 _root_.实数.toNN实数_monotone
  结论: 递增 实数.toNN实数
  证明: fun _ _ h =>
  max_le_max_right _ h

@[gcongr]
-/
protected theorem _root_.Real.toNNReal_monotone : Monotone Real.toNNReal := fun _ _ h =>
  max_le_max_right _ h

@[gcongr]
/--
theorem `_root_.Real.toNNReal_mono` / 定理 `_root_.Real.toNNReal_mono`

English:
theorem _root_.Real.toNNReal_mono
  given: {r₁ r₂ : Real} (h : r₁ <= r₂)
  statement: r₁.toNNReal <= r₂.toNNReal
  proof: Real.toNNReal_monotone h

@[simp]

中文:
定理 _root_.实数.toNN实数_mono
  条件: {r₁ r₂ : 实数} (h : r₁ <= r₂)
  结论: r₁.toNN实数 <= r₂.toNN实数
  证明: Real.toNNReal_monotone h

@[simp]
-/
protected theorem _root_.Real.toNNReal_mono {r₁ r₂ : Real} (h : r₁ <= r₂) : r₁.toNNReal <= r₂.toNNReal :=
  Real.toNNReal_monotone h

@[simp]
/--
theorem `_root_.Real.toNNReal_coe` / 定理 `_root_.Real.toNNReal_coe`

English:
theorem _root_.Real.toNNReal_coe
  given: {r : Real>=0}
  statement: Real.toNNReal r = r
  proof: NNReal.eq max_eq_left r.2

@[simp]

中文:
定理 _root_.实数.toNN实数_coe
  条件: {r : 实数>=0}
  结论: 实数.toNN实数 r = r
  证明: NNReal.eq max_eq_left r.2

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, max_eq_left
-/
theorem _root_.Real.toNNReal_coe {r : Real>=0} : Real.toNNReal r = r :=
NNReal.eq max_eq_left r.2

@[simp]
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: (n : Nat)
  statement: NNReal.mk (n : Real) (n.cast_nonneg) = n
  proof: NNReal.eq (NNReal.coe_natCast n).symm

@[simp]

中文:
定理 mk_natCast
  条件: (n : 自然数)
  结论: 非负实数.mk (n : 实数) (n.cast_nonneg) = n
  证明: NNReal.eq (NNReal.coe_natCast n).symm

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_natCast, NNReal.eq, coe_natCast
-/
theorem mk_natCast (n : Nat) : NNReal.mk (n : Real) (n.cast_nonneg) = n :=
  NNReal.eq (NNReal.coe_natCast n).symm

@[simp]
/--
theorem `_root_.Real.toNNReal_natCast` / 定理 `_root_.Real.toNNReal_natCast`

English:
theorem _root_.Real.toNNReal_natCast
  given: (n : Nat)
  statement: Real.toNNReal n = n
  proof: NNReal.eq by simp [Real.coe_toNNReal]

@[deprecated (since := "2026-05-19")] alias _root_.Real.toNNReal_coe_nat := Real.toNNReal_natCast

@[simp]

中文:
定理 _root_.实数.toNN实数_natCast
  条件: (n : 自然数)
  结论: 实数.toNN实数 n = n
  证明: NNReal.eq by simp [Real.coe_toNNReal]

@[deprecated (since := "2026-05-19")] alias _root_.Real.toNNReal_coe_nat := Real.toNNReal_natCast

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, Real.coe_toNNReal, coe_toNNReal
-/
theorem _root_.Real.toNNReal_natCast (n : Nat) : Real.toNNReal n = n :=
NNReal.eq by simp [Real.coe_toNNReal]

@[deprecated (since := "2026-05-19")] alias _root_.Real.toNNReal_coe_nat := Real.toNNReal_natCast

@[simp]
/--
theorem `_root_.Real.toNNReal_ofNat` / 定理 `_root_.Real.toNNReal_ofNat`

English:
theorem _root_.Real.toNNReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: Real.toNNReal_natCast n

中文:
定理 _root_.实数.toNN实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: Real.toNNReal_natCast n

Depends on / 依赖: Real.toNNReal_natCast, toNNReal_natCast
-/
theorem _root_.Real.toNNReal_ofNat (n : Nat) [n.AtLeastTwo] :
    Real.toNNReal ofNat(n) = OfNat.ofNat n :=
  Real.toNNReal_natCast n

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion Real.toNNReal (↑)
  body: GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_monotone Real.le_coe_toNNReal
    fun _ => Real.toNNReal_coe

中文:
定义 gi
  签名: : Galois嵌入 实数.toNN实数 (↑)
  定义体: GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_monotone Real.le_coe_toNNReal
    fun _ => Real.toNNReal_coe

Depends on / 依赖: GaloisInsertion, GaloisInsertion.monotoneIntro, NNReal, NNReal.coe_mono, Real.le_coe_toNNReal, Real.toNNReal_coe, Real.toNNReal_monotone, coe_mono, le_coe_toNNReal, monotoneIntro, toNNReal_coe, toNNReal_monotone
-/
def gi : GaloisInsertion Real.toNNReal (↑) :=
  GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_monotone Real.le_coe_toNNReal
    fun _ => Real.toNNReal_coe

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : OrderBot Real>=0 := by infer_instance

example : PartialOrder Real>=0 := by infer_instance

example : AddCommMonoid Real>=0 := by infer_instance

example : IsOrderedAddMonoid Real>=0 := by infer_instance

example : DistribLattice Real>=0 := by infer_instance

example : SemilatticeInf Real>=0 := by infer_instance

example : SemilatticeSup Real>=0 := by infer_instance

example : Semiring Real>=0 := by infer_instance

example : CommMonoid Real>=0 := by infer_instance

example : IsOrderedMonoid Real>=0 := instLinearOrderedCommGroupWithZero.toIsOrderedMonoid

noncomputable example : LinearOrderedCommMonoidWithZero Real>=0 := by infer_instance

example : DenselyOrdered Real>=0 := by infer_instance

example : NoMaxOrder Real>=0 := by infer_instance

/--
Instance `instPosSMulStrictMono` / 实例 `instPosSMulStrictMono`

English:
instance instPosSMulStrictMono
  signature: {α} [Preorder α] [MulAction Real α] [PosSMulStrictMono Real α]
  body: (smul_lt_smul_of_pos_left ha (coe_pos.2 hr) :)

中文:
实例 instPosSMulStrictMono
  签名: {α} [预序 α] [乘法作用 实数 α] [正标量乘严格递增 实数 α]
  定义体: (smul_lt_smul_of_pos_left ha (coe_pos.2 hr) :)

Depends on / 依赖: coe_pos, smul_lt_smul_of_pos_left
-/
instance instPosSMulStrictMono {α} [Preorder α] [MulAction Real α] [PosSMulStrictMono Real α] :
    PosSMulStrictMono Real>=0 α where
  smul_lt_smul_of_pos_left _r hr _a₁ _a₂ ha := (smul_lt_smul_of_pos_left ha (coe_pos.2 hr) :)

/--
Instance `instSMulPosStrictMono` / 实例 `instSMulPosStrictMono`

English:
instance instSMulPosStrictMono
  signature: {α} [Zero α] [Preorder α] [MulAction Real α] [SMulPosStrictMono Real α]
  body: (smul_lt_smul_of_pos_right (coe_lt_coe.2 hr) ha :)

中文:
实例 instSMulPosStrictMono
  签名: {α} [零 α] [预序 α] [乘法作用 实数 α] [标量乘正严格递增 实数 α]
  定义体: (smul_lt_smul_of_pos_right (coe_lt_coe.2 hr) ha :)

Depends on / 依赖: coe_lt_coe, smul_lt_smul_of_pos_right
-/
instance instSMulPosStrictMono {α} [Zero α] [Preorder α] [MulAction Real α] [SMulPosStrictMono Real α] :
    SMulPosStrictMono Real>=0 α where
  smul_lt_smul_of_pos_right _a ha _r₁ _r₂ hr := (smul_lt_smul_of_pos_right (coe_lt_coe.2 hr) ha :)

-- TODO: if we use `@[simps!]` it will look through the `NNReal = Subtype _` definition,
-- but if we use `@[simps]` it will not look through the `Equiv.Set.sep` definition.
-- Turning `NNReal` into a structure may be the best way to go here.
-- @[simps!? apply_coe_coe]
/--
Definition of `orderIsoIccZeroCoe` / `orderIsoIccZeroCoe` 的定义

English:
definition orderIsoIccZeroCoe
  signature: (a : Real>=0)
  body: Equiv.Set.sep (Set.Ici 0) fun x : Real => x <= a
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 orderIsoIccZeroCoe
  签名: (a : 实数>=0)
  定义体: Equiv.Set.sep (Set.Ici 0) fun x : Real => x <= a
  map_rel_iff' := Iff.rfl

@[simp]

Depends on / 依赖: Equiv.Set.sep, Set.Ici
-/
def orderIsoIccZeroCoe (a : Real>=0) : Set.Icc (0 : Real) a ≃o Set.Iic a where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x : Real => x <= a
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `orderIsoIccZeroCoe_apply_coe_coe` / 定理 `orderIsoIccZeroCoe_apply_coe_coe`

English:
theorem orderIsoIccZeroCoe_apply_coe_coe
  given: (a : Real>=0) (b : Set.Icc (0 : Real) a)
  proof: rfl

@[simp]

中文:
定理 orderIsoIccZeroCoe_apply_coe_coe
  条件: (a : 实数>=0) (b : 集合.闭区间 (0 : 实数) a)
  证明: rfl

@[simp]
-/
theorem orderIsoIccZeroCoe_apply_coe_coe (a : Real>=0) (b : Set.Icc (0 : Real) a) :
    (orderIsoIccZeroCoe a b : Real) = b :=
  rfl

@[simp]
/--
theorem `orderIsoIccZeroCoe_symm_apply_coe` / 定理 `orderIsoIccZeroCoe_symm_apply_coe`

English:
theorem orderIsoIccZeroCoe_symm_apply_coe
  given: (a : Real>=0) (b : Set.Iic a)
  proof: rfl

中文:
定理 orderIsoIccZeroCoe_symm_apply_coe
  条件: (a : 实数>=0) (b : 集合.左无界右闭区间 a)
  证明: rfl
-/
theorem orderIsoIccZeroCoe_symm_apply_coe (a : Real>=0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : Real) = b :=
  rfl

/--
theorem `coe_image` / 定理 `coe_image`

English:
theorem coe_image
  given: {s : Set Real>=0}
  proof: Subtype.coe_image

中文:
定理 coe_image
  条件: {s : 集合 实数>=0}
  证明: Subtype.coe_image

Depends on / 依赖: Subtype, Subtype.coe_image, coe_image
-/
theorem coe_image {s : Set Real>=0} :
    (↑) '' s = { x : Real | exists h : 0 <= x, .mk x h in s } :=
  Subtype.coe_image

/--
theorem `bddAbove_coe` / 定理 `bddAbove_coe`

English:
theorem bddAbove_coe
  given: {s : Set Real>=0}
  statement: BddAbove (((↑) : Real>=0 -> Real) '' s) ↔ BddAbove s
  proof: Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from le_max_of_le_left hb Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, eq⟩ => eq ▸ hb hx⟩

中文:
定理 bddAbove_coe
  条件: {s : 集合 实数>=0}
  结论: BddAbove (((↑) : 实数>=0 -> 实数) '' s) ↔ BddAbove s
  证明: Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from le_max_of_le_left hb Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, eq⟩ => eq ▸ hb hx⟩

Depends on / 依赖: Iff.intro, Real.toNNReal, Set.mem_image_of_mem, le_max_of_le_left, mem_image_of_mem, toNNReal
-/
theorem bddAbove_coe {s : Set Real>=0} : BddAbove (((↑) : Real>=0 -> Real) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from le_max_of_le_left hb Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, eq⟩ => eq ▸ hb hx⟩

/--
theorem `bddBelow_coe` / 定理 `bddBelow_coe`

English:
theorem bddBelow_coe
  given: (s : Set Real>=0)
  statement: BddBelow (((↑) : Real>=0 -> Real) '' s)
  proof: ⟨0, fun _ ⟨q, _, eq⟩ => eq ▸ q.2⟩

中文:
定理 bddBelow_coe
  条件: (s : 集合 实数>=0)
  结论: BddBelow (((↑) : 实数>=0 -> 实数) '' s)
  证明: ⟨0, fun _ ⟨q, _, eq⟩ => eq ▸ q.2⟩
-/
theorem bddBelow_coe (s : Set Real>=0) : BddBelow (((↑) : Real>=0 -> Real) '' s) :=
  ⟨0, fun _ ⟨q, _, eq⟩ => eq ▸ q.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrderBot Real>=0
  body: fast_instance% Nonneg.conditionallyCompleteLinearOrderBot 0

@[norm_cast]

中文:
实例 :
  签名: 余nditionallyCompleteLinearOrderBot 实数>=0
  定义体: fast_instance% Nonneg.conditionallyCompleteLinearOrderBot 0

@[norm_cast]

Depends on / 依赖: Nonneg, Nonneg.conditionallyCompleteLinearOrderBot, conditionallyCompleteLinearOrderBot, fast_instance
-/
noncomputable instance : ConditionallyCompleteLinearOrderBot Real>=0 :=
  fast_instance% Nonneg.conditionallyCompleteLinearOrderBot 0

@[norm_cast]
/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: (s : Set Real>=0)
  statement: (↑(sSup s) : Real) = sSup (((↑) : Real>=0 -> Real) '' s)
  proof: by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp
  by_cases H : BddAbove s
  · have A : sSup (Subtype.val '' s) in Set.Ici 0 := by
      apply Real.sSup_nonneg
      rintro - ⟨y, -, rfl⟩
      exact y.2
    exact (@subset_sSup_of_within Real (Set.Ici (0 : Real)) _ _ (_) s hs H A).symm
 

中文:
定理 coe_sSup
  条件: (s : 集合 实数>=0)
  结论: (↑(sSup s) : 实数) = sSup (((↑) : 实数>=0 -> 实数) '' s)
  证明: by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp
  by_cases H : BddAbove s
  · have A : sSup (Subtype.val '' s) in Set.Ici 0 := by
      apply Real.sSup_nonneg
      rintro - ⟨y, -, rfl⟩
      exact y.2
    exact (@subset_sSup_of_within Real (Set.Ici (0 : Real)) _ _ (_) s hs H A).symm
 

Depends on / 依赖: BddAbove, IsScalarTower, NNReal, NNReal.coe_zero, Real.sSup_nonneg, Real.sSup_of_not_bddAbove, Set.Ici, Set.eq_empty_or_nonempty, Subtype, Subtype.val, bddAbove_coe, bot_eq_zero, coe_zero, contrapose, csSup_empty, csSup_of_not_bddAbove, eq_empty_or_nonempty, sSup_nonneg, sSup_of_not_bddAbove, subset_sSup_of_within
-/
theorem coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup (((↑) : Real>=0 -> Real) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp
  by_cases H : BddAbove s
  · have A : sSup (Subtype.val '' s) in Set.Ici 0 := by
      apply Real.sSup_nonneg
      rintro - ⟨y, -, rfl⟩
      exact y.2
    exact (@subset_sSup_of_within Real (Set.Ici (0 : Real)) _ _ (_) s hs H A).symm
  · simp only [csSup_of_not_bddAbove H, csSup_empty, bot_eq_zero', NNReal.coe_zero]
    apply (Real.sSup_of_not_bddAbove ?_).symm
    contrapose H
    exact bddAbove_coe.1 H

@[simp, norm_cast]
/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι : Sort*} (s : ι -> Real>=0)
  statement: (↑(⨆ i, s i) : Real) = ⨆ i, ↑(s i)
  proof: by
  rw [iSup]; rw [iSup]; rw [coe_sSup]; rw [← Set.range_comp]; rfl

@[norm_cast]

中文:
定理 coe_iSup
  条件: {ι : 类型层*} (s : ι -> 实数>=0)
  结论: (↑(⨆ i, s i) : 实数) = ⨆ i, ↑(s i)
  证明: by
  rw [iSup]; rw [iSup]; rw [coe_sSup]; rw [← Set.range_comp]; rfl

@[norm_cast]

Depends on / 依赖: Set.range_comp, coe_sSup, range_comp
-/
theorem coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) : Real) = ⨆ i, ↑(s i) := by
  rw [iSup]; rw [iSup]; rw [coe_sSup]; rw [← Set.range_comp]; rfl

@[norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (s : Set Real>=0)
  statement: (↑(sInf s) : Real) = sInf (((↑) : Real>=0 -> Real) '' s)
  proof: by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp only [Set.image_empty, Real.sInf_empty, coe_eq_zero]
    exact @subset_sInf_emptyset Real (Set.Ici (0 : Real)) _ _ (_)
  have A : sInf (Subtype.val '' s) in Set.Ici 0 := by
    apply Real.sInf_nonneg
    rintro - ⟨y, -, rfl⟩
    exact y.2

中文:
定理 coe_sInf
  条件: (s : 集合 实数>=0)
  结论: (↑(sInf s) : 实数) = sInf (((↑) : 实数>=0 -> 实数) '' s)
  证明: by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp only [Set.image_empty, Real.sInf_empty, coe_eq_zero]
    exact @subset_sInf_emptyset Real (Set.Ici (0 : Real)) _ _ (_)
  have A : sInf (Subtype.val '' s) in Set.Ici 0 := by
    apply Real.sInf_nonneg
    rintro - ⟨y, -, rfl⟩
    exact y.2

Depends on / 依赖: OrderBot, OrderBot.bddBelow, Real.sInf_empty, Real.sInf_nonneg, Set.Ici, Set.eq_empty_or_nonempty, Set.image_empty, Subtype, Subtype.val, bddBelow, coe_eq_zero, eq_empty_or_nonempty, image_empty, sInf_empty, sInf_nonneg, subset_sInf_emptyset, subset_sInf_of_within
-/
theorem coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf (((↑) : Real>=0 -> Real) '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl | hs
  · simp only [Set.image_empty, Real.sInf_empty, coe_eq_zero]
    exact @subset_sInf_emptyset Real (Set.Ici (0 : Real)) _ _ (_)
  have A : sInf (Subtype.val '' s) in Set.Ici 0 := by
    apply Real.sInf_nonneg
    rintro - ⟨y, -, rfl⟩
    exact y.2
  exact (@subset_sInf_of_within Real (Set.Ici (0 : Real)) _ _ (_) s hs (OrderBot.bddBelow s) A).symm

@[simp]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  statement: sInf (∅ : Set Real>=0) = 0
  proof: by
  rw [← coe_eq_zero]; rw [coe_sInf]; rw [Set.image_empty]; rw [Real.sInf_empty]

@[norm_cast]

中文:
定理 sInf_empty
  结论: sInf (∅ : 集合 实数>=0) = 0
  证明: by
  rw [← coe_eq_zero]; rw [coe_sInf]; rw [Set.image_empty]; rw [Real.sInf_empty]

@[norm_cast]

Depends on / 依赖: Real.sInf_empty, Set.image_empty, coe_eq_zero, coe_sInf, image_empty, sInf_empty
-/
theorem sInf_empty : sInf (∅ : Set Real>=0) = 0 := by
  rw [← coe_eq_zero]; rw [coe_sInf]; rw [Set.image_empty]; rw [Real.sInf_empty]

@[norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} (s : ι -> Real>=0)
  statement: (↑(⨅ i, s i) : Real) = ⨅ i, ↑(s i)
  proof: by
  rw [iInf]; rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rfl

中文:
定理 coe_iInf
  条件: {ι : 类型层*} (s : ι -> 实数>=0)
  结论: (↑(⨅ i, s i) : 实数) = ⨅ i, ↑(s i)
  证明: by
  rw [iInf]; rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rfl

Depends on / 依赖: Set.range_comp, coe_sInf, range_comp
-/
theorem coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) : Real) = ⨅ i, ↑(s i) := by
  rw [iInf]; rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rfl

-- Short-circuit instance search
/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: : AddLeftMono Real>=0
  body: inferInstance

中文:
实例 addLeftMono
  签名: : AddLeftMono 实数>=0
  定义体: inferInstance
-/
instance addLeftMono : AddLeftMono Real>=0 := inferInstance
/--
Instance `addLeftReflectLT` / 实例 `addLeftReflectLT`

English:
instance addLeftReflectLT
  signature: : AddLeftReflectLT Real>=0
  body: inferInstance

中文:
实例 addLeftReflectLT
  签名: : AddLeftReflectLT 实数>=0
  定义体: inferInstance
-/
instance addLeftReflectLT : AddLeftReflectLT Real>=0 := inferInstance
/--
Instance `mulLeftMono` / 实例 `mulLeftMono`

English:
instance mulLeftMono
  signature: : MulLeftMono Real>=0
  body: inferInstance

中文:
实例 mulLeftMono
  签名: : MulLeftMono 实数>=0
  定义体: inferInstance
-/
instance mulLeftMono : MulLeftMono Real>=0 := inferInstance

/--
theorem `lt_iff_exists_rat_btwn` / 定理 `lt_iff_exists_rat_btwn`

English:
theorem lt_iff_exists_rat_btwn
  given: (a b : Real>=0)
  proof: Iff.intro
    (fun h : (↑a : Real) < (↑b : Real) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
have : 0 <= (q : Real) := le_trans a.2 le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨_, _, haq, hqb⟩ => lt_trans h

中文:
定理 lt_iff_存在_rat_btwn
  条件: (a b : 实数>=0)
  证明: Iff.intro
    (fun h : (↑a : Real) < (↑b : Real) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
have : 0 <= (q : Real) := le_trans a.2 le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨_, _, haq, hqb⟩ => lt_trans h

Depends on / 依赖: Iff.intro, NNReal, NNReal.coe_lt_coe.symm, Rat.cast_nonneg, Real.coe_toNNReal, cast_nonneg, coe_lt_coe, coe_toNNReal, exists_rat_btwn, le_of_lt, le_trans, lt_trans
-/
theorem lt_iff_exists_rat_btwn (a b : Real>=0) :
    a < b ↔ exists q : Rat, 0 <= q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : Real) < (↑b : Real) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
have : 0 <= (q : Real) := le_trans a.2 le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨_, _, haq, hqb⟩ => lt_trans haq hqb

/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : Real>=0) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  结论: (⊥ : 实数>=0) = 0
  证明: rfl
-/
theorem bot_eq_zero : (⊥ : Real>=0) = 0 := rfl

/--
theorem `mul_sup` / 定理 `mul_sup`

English:
theorem mul_sup
  given: (a b c : Real>=0)
  statement: a * (b ⊔ c) = a * b ⊔ a * c
  proof: mul_max_of_nonneg _ _ zero_le

中文:
定理 mul_sup
  条件: (a b c : 实数>=0)
  结论: a * (b ⊔ c) = a * b ⊔ a * c
  证明: mul_max_of_nonneg _ _ zero_le

Depends on / 依赖: mul_max_of_nonneg, zero_le
-/
theorem mul_sup (a b c : Real>=0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ zero_le

/--
theorem `sup_mul` / 定理 `sup_mul`

English:
theorem sup_mul
  given: (a b c : Real>=0)
  statement: (a ⊔ b) * c = a * c ⊔ b * c
  proof: max_mul_of_nonneg _ _ zero_le

@[simp, norm_cast]

中文:
定理 sup_mul
  条件: (a b c : 实数>=0)
  结论: (a ⊔ b) * c = a * c ⊔ b * c
  证明: max_mul_of_nonneg _ _ zero_le

@[simp, norm_cast]

Depends on / 依赖: max_mul_of_nonneg, zero_le
-/
theorem sup_mul (a b c : Real>=0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ zero_le

@[simp, norm_cast]
/--
theorem `coe_max` / 定理 `coe_max`

English:
theorem coe_max
  given: (x y : Real>=0)
  statement: ((max x y : Real>=0) : Real) = max (x : Real) (y : Real)
  proof: NNReal.coe_mono.map_max

@[simp, norm_cast]

中文:
定理 coe_max
  条件: (x y : 实数>=0)
  结论: ((最大值 x y : 实数>=0) : 实数) = 最大值 (x : 实数) (y : 实数)
  证明: NNReal.coe_mono.map_max

@[simp, norm_cast]

Depends on / 依赖: NNReal, NNReal.coe_mono.map_max, coe_mono, map_max
-/
theorem coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) = max (x : Real) (y : Real) :=
  NNReal.coe_mono.map_max

@[simp, norm_cast]
/--
theorem `coe_min` / 定理 `coe_min`

English:
theorem coe_min
  given: (x y : Real>=0)
  statement: ((min x y : Real>=0) : Real) = min (x : Real) (y : Real)
  proof: NNReal.coe_mono.map_min

@[simp]

中文:
定理 coe_min
  条件: (x y : 实数>=0)
  结论: ((最小值 x y : 实数>=0) : 实数) = 最小值 (x : 实数) (y : 实数)
  证明: NNReal.coe_mono.map_min

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_mono.map_min, coe_mono, map_min
-/
theorem coe_min (x y : Real>=0) : ((min x y : Real>=0) : Real) = min (x : Real) (y : Real) :=
  NNReal.coe_mono.map_min

@[simp]
/--
theorem `zero_le_coe` / 定理 `zero_le_coe`

English:
theorem zero_le_coe
  given: {q : Real>=0}
  statement: 0 <= (q : Real)
  proof: q.2

中文:
定理 zero_le_coe
  条件: {q : 实数>=0}
  结论: 0 <= (q : 实数)
  证明: q.2
-/
theorem zero_le_coe {q : Real>=0} : 0 <= (q : Real) :=
  q.2

/--
Instance `instIsStrictOrderedModule` / 实例 `instIsStrictOrderedModule`

English:
instance instIsStrictOrderedModule
  signature: {M : Type*} [AddCommMonoid M] [PartialOrder M]
  body: inferInstanceAs IsStrictOrderedModule (Subtype _) M

中文:
实例 instIsStrictOrderedModule
  签名: {M : 类型} [加法交换幺半群 M] [偏序 M]
  定义体: inferInstanceAs IsStrictOrderedModule (Subtype _) M

Depends on / 依赖: IsStrictOrderedModule, Subtype
-/
instance instIsStrictOrderedModule {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [Module Real M] [IsStrictOrderedModule Real M] :
IsStrictOrderedModule Real>=0 M := inferInstanceAs IsStrictOrderedModule (Subtype _) M

end NNReal

open NNReal

namespace Real

section ToNNReal

@[simp]
/--
theorem `coe_toNNReal'` / 定理 `coe_toNNReal'`

English:
theorem coe_toNNReal'
  given: (r : Real)
  statement: (Real.toNNReal r : Real) = max r 0
  proof: rfl

@[simp]

中文:
定理 coe_toNN实数'
  条件: (r : 实数)
  结论: (实数.toNN实数 r : 实数) = 最大值 r 0
  证明: rfl

@[simp]
-/
theorem coe_toNNReal' (r : Real) : (Real.toNNReal r : Real) = max r 0 :=
  rfl

@[simp]
/--
theorem `toNNReal_zero` / 定理 `toNNReal_zero`

English:
theorem toNNReal_zero
  statement: Real.toNNReal 0 = 0
  proof: NNReal.eq coe_toNNReal _ le_rfl

@[simp]

中文:
定理 toNN实数_zero
  结论: 实数.toNN实数 0 = 0
  证明: NNReal.eq coe_toNNReal _ le_rfl

@[simp]

Depends on / 依赖: Algebra, NNReal, NNReal.eq, S.toSubalgebra, coe_toNNReal, le_rfl, toSubalgebra
-/
theorem toNNReal_zero : Real.toNNReal 0 = 0 := NNReal.eq coe_toNNReal _ le_rfl

@[simp]
/--
theorem `toNNReal_one` / 定理 `toNNReal_one`

English:
theorem toNNReal_one
  statement: Real.toNNReal 1 = 1
  proof: NNReal.eq coe_toNNReal _ zero_le_one

@[simp]

中文:
定理 toNN实数_one
  结论: 实数.toNN实数 1 = 1
  证明: NNReal.eq coe_toNNReal _ zero_le_one

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, coe_toNNReal, zero_le_one
-/
theorem toNNReal_one : Real.toNNReal 1 = 1 := NNReal.eq coe_toNNReal _ zero_le_one

@[simp]
/--
theorem `toNNReal_pos` / 定理 `toNNReal_pos`

English:
theorem toNNReal_pos
  given: {r : Real}
  statement: 0 < Real.toNNReal r ↔ 0 < r
  proof: by
  simp [← NNReal.coe_lt_coe]

@[simp]

中文:
定理 toNN实数_pos
  条件: {r : 实数}
  结论: 0 < 实数.toNN实数 r ↔ 0 < r
  证明: by
  simp [← NNReal.coe_lt_coe]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_lt_coe, coe_lt_coe
-/
theorem toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r := by
  simp [← NNReal.coe_lt_coe]

@[simp]
/--
theorem `toNNReal_eq_zero` / 定理 `toNNReal_eq_zero`

English:
theorem toNNReal_eq_zero
  given: {r : Real}
  statement: Real.toNNReal r = 0 ↔ r <= 0
  proof: by
  simpa [-toNNReal_pos] using not_iff_not.2 (@toNNReal_pos r)

中文:
定理 toNN实数_eq_zero
  条件: {r : 实数}
  结论: 实数.toNN实数 r = 0 ↔ r <= 0
  证明: by
  simpa [-toNNReal_pos] using not_iff_not.2 (@toNNReal_pos r)

Depends on / 依赖: not_iff_not, toNNReal_pos
-/
theorem toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0 ↔ r <= 0 := by
  simpa [-toNNReal_pos] using not_iff_not.2 (@toNNReal_pos r)

/--
theorem `toNNReal_of_nonpos` / 定理 `toNNReal_of_nonpos`

English:
theorem toNNReal_of_nonpos
  given: {r : Real}
  statement: r <= 0 -> Real.toNNReal r = 0
  proof: toNNReal_eq_zero.2

中文:
定理 toNN实数_of_nonpos
  条件: {r : 实数}
  结论: r <= 0 -> 实数.toNN实数 r = 0
  证明: toNNReal_eq_zero.2

Depends on / 依赖: toNNReal_eq_zero
-/
theorem toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.toNNReal r = 0 :=
  toNNReal_eq_zero.2

/--
lemma `toNNReal_eq_iff_eq_coe` / 引理 `toNNReal_eq_iff_eq_coe`

English:
lemma toNNReal_eq_iff_eq_coe
  given: {r : Real} {p : Real>=0} (hp : p != 0)
  statement: r.toNNReal = p ↔ r = p
  proof: ⟨fun h => h ▸ (coe_toNNReal _ <| not_lt.1 fun hlt => hp <| h ▸ toNNReal_of_nonpos hlt.le).symm,
    fun h => h.symm ▸ toNNReal_coe⟩

@[simp]

中文:
引理 toNN实数_eq_iff_eq_coe
  条件: {r : 实数} {p : 实数>=0} (hp : p != 0)
  结论: r.toNN实数 = p ↔ r = p
  证明: ⟨fun h => h ▸ (coe_toNNReal _ <| not_lt.1 fun hlt => hp <| h ▸ toNNReal_of_nonpos hlt.le).symm,
    fun h => h.symm ▸ toNNReal_coe⟩

@[simp]

Depends on / 依赖: coe_toNNReal, h.symm, hlt.le, not_lt, toNNReal_coe, toNNReal_of_nonpos
-/
lemma toNNReal_eq_iff_eq_coe {r : Real} {p : Real>=0} (hp : p != 0) : r.toNNReal = p ↔ r = p :=
  ⟨fun h => h ▸ (coe_toNNReal _ <| not_lt.1 fun hlt => hp <| h ▸ toNNReal_of_nonpos hlt.le).symm,
    fun h => h.symm ▸ toNNReal_coe⟩

@[simp]
/--
lemma `toNNReal_eq_one` / 引理 `toNNReal_eq_one`

English:
lemma toNNReal_eq_one
  given: {r : Real}
  statement: r.toNNReal = 1 ↔ r = 1
  proof: toNNReal_eq_iff_eq_coe one_ne_zero

@[simp]

中文:
引理 toNN实数_eq_one
  条件: {r : 实数}
  结论: r.toNN实数 = 1 ↔ r = 1
  证明: toNNReal_eq_iff_eq_coe one_ne_zero

@[simp]

Depends on / 依赖: one_ne_zero, toNNReal_eq_iff_eq_coe
-/
lemma toNNReal_eq_one {r : Real} : r.toNNReal = 1 ↔ r = 1 := toNNReal_eq_iff_eq_coe one_ne_zero

@[simp]
/--
lemma `toNNReal_eq_natCast` / 引理 `toNNReal_eq_natCast`

English:
lemma toNNReal_eq_natCast
  given: {r : Real} {n : Nat} (hn : n != 0)
  statement: r.toNNReal = n ↔ r = n
  proof: mod_cast toNNReal_eq_iff_eq_coe Nat.cast_ne_zero.2 hn

@[simp]

中文:
引理 toNN实数_eq_natCast
  条件: {r : 实数} {n : 自然数} (hn : n != 0)
  结论: r.toNN实数 = n ↔ r = n
  证明: mod_cast toNNReal_eq_iff_eq_coe Nat.cast_ne_zero.2 hn

@[simp]

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, mod_cast, toNNReal_eq_iff_eq_coe
-/
lemma toNNReal_eq_natCast {r : Real} {n : Nat} (hn : n != 0) : r.toNNReal = n ↔ r = n :=
mod_cast toNNReal_eq_iff_eq_coe Nat.cast_ne_zero.2 hn

@[simp]
/--
lemma `toNNReal_eq_ofNat` / 引理 `toNNReal_eq_ofNat`

English:
lemma toNNReal_eq_ofNat
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: toNNReal_eq_natCast (NeZero.ne n)

@[simp]

中文:
引理 toNN实数_eq_of自然数
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: toNNReal_eq_natCast (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, toNNReal_eq_natCast
-/
lemma toNNReal_eq_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] :
    r.toNNReal = ofNat(n) ↔ r = OfNat.ofNat n :=
  toNNReal_eq_natCast (NeZero.ne n)

@[simp]
/--
theorem `toNNReal_le_toNNReal_iff` / 定理 `toNNReal_le_toNNReal_iff`

English:
theorem toNNReal_le_toNNReal_iff
  given: {r p : Real} (hp : 0 <= p)
  proof: by simp [← NNReal.coe_le_coe, hp]

@[simp]

中文:
定理 toNN实数_le_toNN实数_iff
  条件: {r p : 实数} (hp : 0 <= p)
  证明: by simp [← NNReal.coe_le_coe, hp]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe
-/
theorem toNNReal_le_toNNReal_iff {r p : Real} (hp : 0 <= p) :
    toNNReal r <= toNNReal p ↔ r <= p := by simp [← NNReal.coe_le_coe, hp]

@[simp]
/--
lemma `toNNReal_le_one` / 引理 `toNNReal_le_one`

English:
lemma toNNReal_le_one
  given: {r : Real}
  statement: r.toNNReal <= 1 ↔ r <= 1
  proof: by
  simpa using toNNReal_le_toNNReal_iff zero_le_one

@[simp]

中文:
引理 toNN实数_le_one
  条件: {r : 实数}
  结论: r.toNN实数 <= 1 ↔ r <= 1
  证明: by
  simpa using toNNReal_le_toNNReal_iff zero_le_one

@[simp]

Depends on / 依赖: toNNReal_le_toNNReal_iff, zero_le_one
-/
lemma toNNReal_le_one {r : Real} : r.toNNReal <= 1 ↔ r <= 1 := by
  simpa using toNNReal_le_toNNReal_iff zero_le_one

@[simp]
/--
lemma `one_lt_toNNReal` / 引理 `one_lt_toNNReal`

English:
lemma one_lt_toNNReal
  given: {r : Real}
  statement: 1 < r.toNNReal ↔ 1 < r
  proof: by
  simpa only [not_le] using toNNReal_le_one.not

@[simp]

中文:
引理 one_lt_toNN实数
  条件: {r : 实数}
  结论: 1 < r.toNN实数 ↔ 1 < r
  证明: by
  simpa only [not_le] using toNNReal_le_one.not

@[simp]

Depends on / 依赖: not_le, toNNReal_le_one, toNNReal_le_one.not
-/
lemma one_lt_toNNReal {r : Real} : 1 < r.toNNReal ↔ 1 < r := by
  simpa only [not_le] using toNNReal_le_one.not

@[simp]
/--
lemma `toNNReal_le_natCast` / 引理 `toNNReal_le_natCast`

English:
lemma toNNReal_le_natCast
  given: {r : Real} {n : Nat}
  statement: r.toNNReal <= n ↔ r <= n
  proof: by
  simpa using toNNReal_le_toNNReal_iff n.cast_nonneg

@[simp]

中文:
引理 toNN实数_le_natCast
  条件: {r : 实数} {n : 自然数}
  结论: r.toNN实数 <= n ↔ r <= n
  证明: by
  simpa using toNNReal_le_toNNReal_iff n.cast_nonneg

@[simp]

Depends on / 依赖: cast_nonneg, n.cast_nonneg, toNNReal_le_toNNReal_iff
-/
lemma toNNReal_le_natCast {r : Real} {n : Nat} : r.toNNReal <= n ↔ r <= n := by
  simpa using toNNReal_le_toNNReal_iff n.cast_nonneg

@[simp]
/--
lemma `natCast_lt_toNNReal` / 引理 `natCast_lt_toNNReal`

English:
lemma natCast_lt_toNNReal
  given: {r : Real} {n : Nat}
  statement: n < r.toNNReal ↔ n < r
  proof: by
  simpa only [not_le] using toNNReal_le_natCast.not

@[simp]

中文:
引理 natCast_lt_toNN实数
  条件: {r : 实数} {n : 自然数}
  结论: n < r.toNN实数 ↔ n < r
  证明: by
  simpa only [not_le] using toNNReal_le_natCast.not

@[simp]

Depends on / 依赖: not_le, toNNReal_le_natCast, toNNReal_le_natCast.not
-/
lemma natCast_lt_toNNReal {r : Real} {n : Nat} : n < r.toNNReal ↔ n < r := by
  simpa only [not_le] using toNNReal_le_natCast.not

@[simp]
/--
lemma `toNNReal_le_ofNat` / 引理 `toNNReal_le_ofNat`

English:
lemma toNNReal_le_ofNat
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: toNNReal_le_natCast

@[simp]

中文:
引理 toNN实数_le_of自然数
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: toNNReal_le_natCast

@[simp]

Depends on / 依赖: toNNReal_le_natCast
-/
lemma toNNReal_le_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] :
    r.toNNReal <= ofNat(n) ↔ r <= n :=
  toNNReal_le_natCast

@[simp]
/--
lemma `ofNat_lt_toNNReal` / 引理 `ofNat_lt_toNNReal`

English:
lemma ofNat_lt_toNNReal
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: natCast_lt_toNNReal

@[simp]

中文:
引理 of自然数_lt_toNN实数
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: natCast_lt_toNNReal

@[simp]

Depends on / 依赖: natCast_lt_toNNReal
-/
lemma ofNat_lt_toNNReal {r : Real} {n : Nat} [n.AtLeastTwo] :
    ofNat(n) < r.toNNReal ↔ n < r :=
  natCast_lt_toNNReal

@[simp]
/--
theorem `toNNReal_eq_toNNReal_iff` / 定理 `toNNReal_eq_toNNReal_iff`

English:
theorem toNNReal_eq_toNNReal_iff
  given: {r p : Real} (hr : 0 <= r) (hp : 0 <= p)
  proof: by simp [← coe_inj, hr, hp]

@[simp]

中文:
定理 toNN实数_eq_toNN实数_iff
  条件: {r p : 实数} (hr : 0 <= r) (hp : 0 <= p)
  证明: by simp [← coe_inj, hr, hp]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem toNNReal_eq_toNNReal_iff {r p : Real} (hr : 0 <= r) (hp : 0 <= p) :
    toNNReal r = toNNReal p ↔ r = p := by simp [← coe_inj, hr, hp]

@[simp]
/--
theorem `toNNReal_lt_toNNReal_iff'` / 定理 `toNNReal_lt_toNNReal_iff'`

English:
theorem toNNReal_lt_toNNReal_iff'
  given: {r p : Real}
  statement: Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p
  proof: NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff

中文:
定理 toNN实数_lt_toNN实数_iff'
  条件: {r p : 实数}
  结论: 实数.toNN实数 r < 实数.toNN实数 p ↔ r < p ∧ 0 < p
  证明: NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff

Depends on / 依赖: NNReal, NNReal.coe_lt_coe.symm.trans, coe_lt_coe, max_lt_max_left_iff
-/
theorem toNNReal_lt_toNNReal_iff' {r p : Real} : Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p :=
  NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff

/--
theorem `toNNReal_lt_toNNReal_iff` / 定理 `toNNReal_lt_toNNReal_iff`

English:
theorem toNNReal_lt_toNNReal_iff
  given: {r p : Real} (h : 0 < p)
  proof: toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)

中文:
定理 toNN实数_lt_toNN实数_iff
  条件: {r p : 实数} (h : 0 < p)
  证明: toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)

Depends on / 依赖: and_iff_left, toNNReal_lt_toNNReal_iff
-/
theorem toNNReal_lt_toNNReal_iff {r p : Real} (h : 0 < p) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)

/--
theorem `lt_of_toNNReal_lt` / 定理 `lt_of_toNNReal_lt`

English:
theorem lt_of_toNNReal_lt
  given: {r p : Real} (h : r.toNNReal < p.toNNReal)
  statement: r < p
  proof: (Real.toNNReal_lt_toNNReal_iff <| Real.toNNReal_pos.1 (ne_bot_of_gt h).bot_lt).1 h

中文:
定理 lt_of_toNN实数_lt
  条件: {r p : 实数} (h : r.toNN实数 < p.toNN实数)
  结论: r < p
  证明: (Real.toNNReal_lt_toNNReal_iff <| Real.toNNReal_pos.1 (ne_bot_of_gt h).bot_lt).1 h

Depends on / 依赖: Real.toNNReal_lt_toNNReal_iff, Real.toNNReal_pos, bot_lt, ne_bot_of_gt, toNNReal_lt_toNNReal_iff, toNNReal_pos
-/
theorem lt_of_toNNReal_lt {r p : Real} (h : r.toNNReal < p.toNNReal) : r < p :=
  (Real.toNNReal_lt_toNNReal_iff <| Real.toNNReal_pos.1 (ne_bot_of_gt h).bot_lt).1 h

/--
theorem `toNNReal_lt_toNNReal_iff_of_nonneg` / 定理 `toNNReal_lt_toNNReal_iff_of_nonneg`

English:
theorem toNNReal_lt_toNNReal_iff_of_nonneg
  given: {r p : Real} (hr : 0 <= r)
  proof: toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩

中文:
定理 toNN实数_lt_toNN实数_iff_of_nonneg
  条件: {r p : 实数} (hr : 0 <= r)
  证明: toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩

Depends on / 依赖: And.left, lt_of_le_of_lt, toNNReal_lt_toNNReal_iff
-/
theorem toNNReal_lt_toNNReal_iff_of_nonneg {r p : Real} (hr : 0 <= r) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩

/--
lemma `toNNReal_le_toNNReal_iff'` / 引理 `toNNReal_le_toNNReal_iff'`

English:
lemma toNNReal_le_toNNReal_iff'
  given: {r p : Real}
  statement: r.toNNReal <= p.toNNReal ↔ r <= p ∨ r <= 0
  proof: by
  simp_rw [← not_lt, toNNReal_lt_toNNReal_iff', not_and_or]

中文:
引理 toNN实数_le_toNN实数_iff'
  条件: {r p : 实数}
  结论: r.toNN实数 <= p.toNN实数 ↔ r <= p ∨ r <= 0
  证明: by
  simp_rw [← not_lt, toNNReal_lt_toNNReal_iff', not_and_or]

Depends on / 依赖: not_and_or, not_lt, simp_rw, toNNReal_lt_toNNReal_iff
-/
lemma toNNReal_le_toNNReal_iff' {r p : Real} : r.toNNReal <= p.toNNReal ↔ r <= p ∨ r <= 0 := by
  simp_rw [← not_lt, toNNReal_lt_toNNReal_iff', not_and_or]

/--
lemma `toNNReal_le_toNNReal_iff_of_pos` / 引理 `toNNReal_le_toNNReal_iff_of_pos`

English:
lemma toNNReal_le_toNNReal_iff_of_pos
  given: {r p : Real} (hr : 0 < r)
  statement: r.toNNReal <= p.toNNReal ↔ r <= p
  proof: by
  simp [toNNReal_le_toNNReal_iff', hr.not_ge]

@[simp]

中文:
引理 toNN实数_le_toNN实数_iff_of_pos
  条件: {r p : 实数} (hr : 0 < r)
  结论: r.toNN实数 <= p.toNN实数 ↔ r <= p
  证明: by
  simp [toNNReal_le_toNNReal_iff', hr.not_ge]

@[simp]

Depends on / 依赖: hr.not_ge, not_ge, toNNReal_le_toNNReal_iff
-/
lemma toNNReal_le_toNNReal_iff_of_pos {r p : Real} (hr : 0 < r) : r.toNNReal <= p.toNNReal ↔ r <= p := by
  simp [toNNReal_le_toNNReal_iff', hr.not_ge]

@[simp]
/--
lemma `one_le_toNNReal` / 引理 `one_le_toNNReal`

English:
lemma one_le_toNNReal
  given: {r : Real}
  statement: 1 <= r.toNNReal ↔ 1 <= r
  proof: by
  simpa using toNNReal_le_toNNReal_iff_of_pos one_pos

@[simp]

中文:
引理 one_le_toNN实数
  条件: {r : 实数}
  结论: 1 <= r.toNN实数 ↔ 1 <= r
  证明: by
  simpa using toNNReal_le_toNNReal_iff_of_pos one_pos

@[simp]

Depends on / 依赖: one_pos, toNNReal_le_toNNReal_iff_of_pos
-/
lemma one_le_toNNReal {r : Real} : 1 <= r.toNNReal ↔ 1 <= r := by
  simpa using toNNReal_le_toNNReal_iff_of_pos one_pos

@[simp]
/--
lemma `toNNReal_lt_one` / 引理 `toNNReal_lt_one`

English:
lemma toNNReal_lt_one
  given: {r : Real}
  statement: r.toNNReal < 1 ↔ r < 1
  proof: by simp only [← not_le, one_le_toNNReal]

@[simp]

中文:
引理 toNN实数_lt_one
  条件: {r : 实数}
  结论: r.toNN实数 < 1 ↔ r < 1
  证明: by simp only [← not_le, one_le_toNNReal]

@[simp]

Depends on / 依赖: not_le, one_le_toNNReal
-/
lemma toNNReal_lt_one {r : Real} : r.toNNReal < 1 ↔ r < 1 := by simp only [← not_le, one_le_toNNReal]

@[simp]
/--
lemma `natCastle_toNNReal'` / 引理 `natCastle_toNNReal'`

English:
lemma natCastle_toNNReal'
  given: {n : Nat} {r : Real}
  statement: ↑n <= r.toNNReal ↔ n <= r ∨ n = 0
  proof: by
  simpa [n.cast_nonneg.ge_iff_eq'] using toNNReal_le_toNNReal_iff' (r := n)

@[simp]

中文:
引理 natCastle_toNN实数'
  条件: {n : 自然数} {r : 实数}
  结论: ↑n <= r.toNN实数 ↔ n <= r ∨ n = 0
  证明: by
  simpa [n.cast_nonneg.ge_iff_eq'] using toNNReal_le_toNNReal_iff' (r := n)

@[simp]

Depends on / 依赖: cast_nonneg, ge_iff_eq, n.cast_nonneg.ge_iff_eq, toNNReal_le_toNNReal_iff
-/
lemma natCastle_toNNReal' {n : Nat} {r : Real} : ↑n <= r.toNNReal ↔ n <= r ∨ n = 0 := by
  simpa [n.cast_nonneg.ge_iff_eq'] using toNNReal_le_toNNReal_iff' (r := n)

@[simp]
/--
lemma `toNNReal_lt_natCast'` / 引理 `toNNReal_lt_natCast'`

English:
lemma toNNReal_lt_natCast'
  given: {n : Nat} {r : Real}
  statement: r.toNNReal < n ↔ r < n ∧ n != 0
  proof: by
  simpa [pos_iff_ne_zero] using toNNReal_lt_toNNReal_iff' (r := r) (p := n)

中文:
引理 toNN实数_lt_natCast'
  条件: {n : 自然数} {r : 实数}
  结论: r.toNN实数 < n ↔ r < n ∧ n != 0
  证明: by
  simpa [pos_iff_ne_zero] using toNNReal_lt_toNNReal_iff' (r := r) (p := n)

Depends on / 依赖: pos_iff_ne_zero, toNNReal_lt_toNNReal_iff
-/
lemma toNNReal_lt_natCast' {n : Nat} {r : Real} : r.toNNReal < n ↔ r < n ∧ n != 0 := by
  simpa [pos_iff_ne_zero] using toNNReal_lt_toNNReal_iff' (r := r) (p := n)

/--
lemma `natCast_le_toNNReal` / 引理 `natCast_le_toNNReal`

English:
lemma natCast_le_toNNReal
  given: {n : Nat} {r : Real} (hn : n != 0)
  statement: ↑n <= r.toNNReal ↔ n <= r
  proof: by simp [hn]

中文:
引理 natCast_le_toNN实数
  条件: {n : 自然数} {r : 实数} (hn : n != 0)
  结论: ↑n <= r.toNN实数 ↔ n <= r
  证明: by simp [hn]
-/
lemma natCast_le_toNNReal {n : Nat} {r : Real} (hn : n != 0) : ↑n <= r.toNNReal ↔ n <= r := by simp [hn]

/--
lemma `toNNReal_lt_natCast` / 引理 `toNNReal_lt_natCast`

English:
lemma toNNReal_lt_natCast
  given: {r : Real} {n : Nat} (hn : n != 0)
  statement: r.toNNReal < n ↔ r < n
  proof: by simp [hn]

@[simp]

中文:
引理 toNN实数_lt_natCast
  条件: {r : 实数} {n : 自然数} (hn : n != 0)
  结论: r.toNN实数 < n ↔ r < n
  证明: by simp [hn]

@[simp]
-/
lemma toNNReal_lt_natCast {r : Real} {n : Nat} (hn : n != 0) : r.toNNReal < n ↔ r < n := by simp [hn]

@[simp]
/--
lemma `toNNReal_lt_ofNat` / 引理 `toNNReal_lt_ofNat`

English:
lemma toNNReal_lt_ofNat
  given: {r : Real} {n : Nat} [n.AtLeastTwo]
  proof: toNNReal_lt_natCast (NeZero.ne n)

@[simp]

中文:
引理 toNN实数_lt_of自然数
  条件: {r : 实数} {n : 自然数} [n.AtLeastTwo]
  证明: toNNReal_lt_natCast (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, toNNReal_lt_natCast
-/
lemma toNNReal_lt_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] :
    r.toNNReal < ofNat(n) ↔ r < OfNat.ofNat n :=
  toNNReal_lt_natCast (NeZero.ne n)

@[simp]
/--
lemma `ofNat_le_toNNReal` / 引理 `ofNat_le_toNNReal`

English:
lemma ofNat_le_toNNReal
  given: {n : Nat} {r : Real} [n.AtLeastTwo]
  proof: natCast_le_toNNReal (NeZero.ne n)

@[simp]

中文:
引理 of自然数_le_toNN实数
  条件: {n : 自然数} {r : 实数} [n.AtLeastTwo]
  证明: natCast_le_toNNReal (NeZero.ne n)

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, natCast_le_toNNReal
-/
lemma ofNat_le_toNNReal {n : Nat} {r : Real} [n.AtLeastTwo] :
    ofNat(n) <= r.toNNReal ↔ OfNat.ofNat n <= r :=
  natCast_le_toNNReal (NeZero.ne n)

@[simp]
/--
theorem `toNNReal_add` / 定理 `toNNReal_add`

English:
theorem toNNReal_add
  given: {r p : Real} (hr : 0 <= r) (hp : 0 <= p)
  proof: NNReal.eq by simp [hr, hp, add_nonneg]

中文:
定理 toNN实数_add
  条件: {r p : 实数} (hr : 0 <= r) (hp : 0 <= p)
  证明: NNReal.eq by simp [hr, hp, add_nonneg]

Depends on / 依赖: NNReal, NNReal.eq, add_nonneg
-/
theorem toNNReal_add {r p : Real} (hr : 0 <= r) (hp : 0 <= p) :
    Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p :=
NNReal.eq by simp [hr, hp, add_nonneg]

/--
theorem `toNNReal_add_toNNReal` / 定理 `toNNReal_add_toNNReal`

English:
theorem toNNReal_add_toNNReal
  given: {r p : Real} (hr : 0 <= r) (hp : 0 <= p)
  proof: (Real.toNNReal_add hr hp).symm

中文:
定理 toNN实数_add_toNN实数
  条件: {r p : 实数} (hr : 0 <= r) (hp : 0 <= p)
  证明: (Real.toNNReal_add hr hp).symm

Depends on / 依赖: Real.toNNReal_add, toNNReal_add
-/
theorem toNNReal_add_toNNReal {r p : Real} (hr : 0 <= r) (hp : 0 <= p) :
    Real.toNNReal r + Real.toNNReal p = Real.toNNReal (r + p) :=
  (Real.toNNReal_add hr hp).symm

/--
theorem `toNNReal_le_toNNReal` / 定理 `toNNReal_le_toNNReal`

English:
theorem toNNReal_le_toNNReal
  given: {r p : Real} (h : r <= p)
  statement: Real.toNNReal r <= Real.toNNReal p
  proof: Real.toNNReal_mono h

中文:
定理 toNN实数_le_toNN实数
  条件: {r p : 实数} (h : r <= p)
  结论: 实数.toNN实数 r <= 实数.toNN实数 p
  证明: Real.toNNReal_mono h

Depends on / 依赖: Real.toNNReal_mono, toNNReal_mono
-/
theorem toNNReal_le_toNNReal {r p : Real} (h : r <= p) : Real.toNNReal r <= Real.toNNReal p :=
  Real.toNNReal_mono h

/--
theorem `toNNReal_add_le` / 定理 `toNNReal_add_le`

English:
theorem toNNReal_add_le
  given: {r p : Real}
  statement: Real.toNNReal (r + p) <= Real.toNNReal r + Real.toNNReal p
  proof: NNReal.coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe

中文:
定理 toNN实数_add_le
  条件: {r p : 实数}
  结论: 实数.toNN实数 (r + p) <= 实数.toNN实数 r + 实数.toNN实数 p
  证明: NNReal.coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.zero_le_coe, add_le_add, coe_le_coe, le_max_left, max_le, zero_le_coe
-/
theorem toNNReal_add_le {r p : Real} : Real.toNNReal (r + p) <= Real.toNNReal r + Real.toNNReal p :=
NNReal.coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe

/--
theorem `toNNReal_le_iff_le_coe` / 定理 `toNNReal_le_iff_le_coe`

English:
theorem toNNReal_le_iff_le_coe
  given: {r : Real} {p : Real>=0}
  statement: toNNReal r <= p ↔ r <= ↑p
  proof: NNReal.gi.gc r p

中文:
定理 toNN实数_le_iff_le_coe
  条件: {r : 实数} {p : 实数>=0}
  结论: toNN实数 r <= p ↔ r <= ↑p
  证明: NNReal.gi.gc r p

Depends on / 依赖: NNReal, NNReal.gi.gc
-/
theorem toNNReal_le_iff_le_coe {r : Real} {p : Real>=0} : toNNReal r <= p ↔ r <= ↑p :=
  NNReal.gi.gc r p

/--
theorem `le_toNNReal_iff_coe_le` / 定理 `le_toNNReal_iff_coe_le`

English:
theorem le_toNNReal_iff_coe_le
  given: {r : Real>=0} {p : Real} (hp : 0 <= p)
  statement: r <= Real.toNNReal p ↔ ↑r <= p
  proof: by
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal p hp]

中文:
定理 le_toNN实数_iff_coe_le
  条件: {r : 实数>=0} {p : 实数} (hp : 0 <= p)
  结论: r <= 实数.toNN实数 p ↔ ↑r <= p
  证明: by
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal p hp]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, Real.coe_toNNReal, coe_le_coe, coe_toNNReal
-/
theorem le_toNNReal_iff_coe_le {r : Real>=0} {p : Real} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p := by
  rw [← NNReal.coe_le_coe]; rw [Real.coe_toNNReal p hp]

/--
theorem `le_toNNReal_iff_coe_le'` / 定理 `le_toNNReal_iff_coe_le'`

English:
theorem le_toNNReal_iff_coe_le'
  given: {r : Real>=0} {p : Real} (hr : 0 < r)
  statement: r <= Real.toNNReal p ↔ ↑r <= p
  proof: (le_or_gt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_ge, toNNReal_eq_zero.2 hp.le, hr.not_ge]

中文:
定理 le_toNN实数_iff_coe_le'
  条件: {r : 实数>=0} {p : 实数} (hr : 0 < r)
  结论: r <= 实数.toNN实数 p ↔ ↑r <= p
  证明: (le_or_gt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_ge, toNNReal_eq_zero.2 hp.le, hr.not_ge]

Depends on / 依赖: coe_nonneg, hp.le, hp.trans_le, hr.not_ge, le_or_gt, le_toNNReal_iff_coe_le, not_ge, r.coe_nonneg, toNNReal_eq_zero, trans_le
-/
theorem le_toNNReal_iff_coe_le' {r : Real>=0} {p : Real} (hr : 0 < r) : r <= Real.toNNReal p ↔ ↑r <= p :=
  (le_or_gt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_ge, toNNReal_eq_zero.2 hp.le, hr.not_ge]

/--
theorem `toNNReal_lt_iff_lt_coe` / 定理 `toNNReal_lt_iff_lt_coe`

English:
theorem toNNReal_lt_iff_lt_coe
  given: {r : Real} {p : Real>=0} (ha : 0 <= r)
  statement: Real.toNNReal r < p ↔ r < ↑p
  proof: by
  rw [← NNReal.coe_lt_coe]; rw [Real.coe_toNNReal r ha]

中文:
定理 toNN实数_lt_iff_lt_coe
  条件: {r : 实数} {p : 实数>=0} (ha : 0 <= r)
  结论: 实数.toNN实数 r < p ↔ r < ↑p
  证明: by
  rw [← NNReal.coe_lt_coe]; rw [Real.coe_toNNReal r ha]

Depends on / 依赖: NNReal, NNReal.coe_lt_coe, Real.coe_toNNReal, coe_lt_coe, coe_toNNReal
-/
theorem toNNReal_lt_iff_lt_coe {r : Real} {p : Real>=0} (ha : 0 <= r) : Real.toNNReal r < p ↔ r < ↑p := by
  rw [← NNReal.coe_lt_coe]; rw [Real.coe_toNNReal r ha]

/--
theorem `lt_toNNReal_iff_coe_lt` / 定理 `lt_toNNReal_iff_coe_lt`

English:
theorem lt_toNNReal_iff_coe_lt
  given: {r : Real>=0} {p : Real}
  statement: r < Real.toNNReal p ↔ ↑r < p
  proof: lt_iff_lt_of_le_iff_le toNNReal_le_iff_le_coe

中文:
定理 lt_toNN实数_iff_coe_lt
  条件: {r : 实数>=0} {p : 实数}
  结论: r < 实数.toNN实数 p ↔ ↑r < p
  证明: lt_iff_lt_of_le_iff_le toNNReal_le_iff_le_coe

Depends on / 依赖: lt_iff_lt_of_le_iff_le, toNNReal_le_iff_le_coe
-/
theorem lt_toNNReal_iff_coe_lt {r : Real>=0} {p : Real} : r < Real.toNNReal p ↔ ↑r < p :=
  lt_iff_lt_of_le_iff_le toNNReal_le_iff_le_coe

/--
theorem `toNNReal_pow` / 定理 `toNNReal_pow`

English:
theorem toNNReal_pow
  given: {x : Real} (hx : 0 <= x) (n : Nat)
  statement: (x ^ n).toNNReal = x.toNNReal ^ n
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_pow]; rw [Real.coe_toNNReal _ (pow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

中文:
定理 toNN实数_pow
  条件: {x : 实数} (hx : 0 <= x) (n : 自然数)
  结论: (x ^ n).toNN实数 = x.toNN实数 ^ n
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_pow]; rw [Real.coe_toNNReal _ (pow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

Depends on / 依赖: NNReal, NNReal.coe_pow, Real.coe_toNNReal, coe_inj, coe_pow, coe_toNNReal, pow_nonneg
-/
theorem toNNReal_pow {x : Real} (hx : 0 <= x) (n : Nat) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← coe_inj]; rw [NNReal.coe_pow]; rw [Real.coe_toNNReal _ (pow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

/--
theorem `toNNReal_zpow` / 定理 `toNNReal_zpow`

English:
theorem toNNReal_zpow
  given: {x : Real} (hx : 0 <= x) (n : Int)
  statement: (x ^ n).toNNReal = x.toNNReal ^ n
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_zpow]; rw [Real.coe_toNNReal _ (zpow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

中文:
定理 toNN实数_zpow
  条件: {x : 实数} (hx : 0 <= x) (n : 整数)
  结论: (x ^ n).toNN实数 = x.toNN实数 ^ n
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_zpow]; rw [Real.coe_toNNReal _ (zpow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

Depends on / 依赖: NNReal, NNReal.coe_zpow, Real.coe_toNNReal, coe_inj, coe_toNNReal, coe_zpow, zpow_nonneg
-/
theorem toNNReal_zpow {x : Real} (hx : 0 <= x) (n : Int) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← coe_inj]; rw [NNReal.coe_zpow]; rw [Real.coe_toNNReal _ (zpow_nonneg hx _)]; rw [Real.coe_toNNReal x hx]

/--
theorem `toNNReal_mul` / 定理 `toNNReal_mul`

English:
theorem toNNReal_mul
  given: {p q : Real} (hp : 0 <= p)
  proof: NNReal.eq by simp [mul_max_of_nonneg, hp]

中文:
定理 toNN实数_mul
  条件: {p q : 实数} (hp : 0 <= p)
  证明: NNReal.eq by simp [mul_max_of_nonneg, hp]

Depends on / 依赖: NNReal, NNReal.eq, mul_max_of_nonneg
-/
theorem toNNReal_mul {p q : Real} (hp : 0 <= p) :
    Real.toNNReal (p * q) = Real.toNNReal p * Real.toNNReal q :=
NNReal.eq by simp [mul_max_of_nonneg, hp]

end ToNNReal

end Real

open Real

namespace NNReal

section Mul

/--
theorem `mul_eq_mul_left` / 定理 `mul_eq_mul_left`

English:
theorem mul_eq_mul_left
  given: {a b c : Real>=0} (h : a != 0)
  statement: a * b = a * c ↔ b = c
  proof: by
  rw [mul_eq_mul_left_iff]; rw [or_iff_left h]

中文:
定理 mul_eq_mul_left
  条件: {a b c : 实数>=0} (h : a != 0)
  结论: a * b = a * c ↔ b = c
  证明: by
  rw [mul_eq_mul_left_iff]; rw [or_iff_left h]

Depends on / 依赖: mul_eq_mul_left_iff, or_iff_left
-/
theorem mul_eq_mul_left {a b c : Real>=0} (h : a != 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff]; rw [or_iff_left h]

end Mul

section Pow

/--
theorem `pow_antitone_exp` / 定理 `pow_antitone_exp`

English:
theorem pow_antitone_exp
  given: {a : Real>=0} (m n : Nat) (mn : m <= n) (a1 : a <= 1)
  statement: a ^ n <= a ^ m
  proof: pow_le_pow_of_le_one zero_le a1 mn

nonrec theorem exists_pow_lt_of_lt_one {a b : Real>=0} (ha : 0 < a) (hb : b < 1) :
    exists n : Nat, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)

nonrec theorem exis

中文:
定理 pow_antitone_exp
  条件: {a : 实数>=0} (m n : 自然数) (mn : m <= n) (a1 : a <= 1)
  结论: a ^ n <= a ^ m
  证明: pow_le_pow_of_le_one zero_le a1 mn

nonrec theorem exists_pow_lt_of_lt_one {a b : Real>=0} (ha : 0 < a) (hb : b < 1) :
    exists n : Nat, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)

nonrec theorem exis

Depends on / 依赖: pow_le_pow_of_le_one, zero_le
-/
theorem pow_antitone_exp {a : Real>=0} (m n : Nat) (mn : m <= n) (a1 : a <= 1) : a ^ n <= a ^ m :=
  pow_le_pow_of_le_one zero_le a1 mn

nonrec theorem exists_pow_lt_of_lt_one {a b : Real>=0} (ha : 0 < a) (hb : b < 1) :
    exists n : Nat, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)

nonrec theorem exists_mem_Ico_zpow {x : Real>=0} {y : Real>=0} (hx : x != 0) (hy : 1 < y) :
    exists n : Int, x in Set.Ico (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ico_zpow hx.bot_lt hy

nonrec theorem exists_mem_Ioc_zpow {x : Real>=0} {y : Real>=0} (hx : x != 0) (hy : 1 < y) :
    exists n : Int, x in Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ioc_zpow hx.bot_lt hy

end Pow

section Sub


/--
theorem `sub_def` / 定理 `sub_def`

English:
theorem sub_def
  given: {r p : Real>=0}
  statement: r - p = Real.toNNReal (r - p)
  proof: rfl

中文:
定理 sub_def
  条件: {r p : 实数>=0}
  结论: r - p = 实数.toNN实数 (r - p)
  证明: rfl
-/
theorem sub_def {r p : Real>=0} : r - p = Real.toNNReal (r - p) :=
  rfl

/--
theorem `coe_sub_def` / 定理 `coe_sub_def`

English:
theorem coe_sub_def
  given: {r p : Real>=0}
  statement: ↑(r - p) = max (r - p : Real) 0
  proof: rfl

example : OrderedSub Real>=0 := by infer_instance

中文:
定理 coe_sub_def
  条件: {r p : 实数>=0}
  结论: ↑(r - p) = 最大值 (r - p : 实数) 0
  证明: rfl

example : OrderedSub Real>=0 := by infer_instance
-/
theorem coe_sub_def {r p : Real>=0} : ↑(r - p) = max (r - p : Real) 0 :=
  rfl

example : OrderedSub Real>=0 := by infer_instance

end Sub

section Inv

@[simp]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: {r : Real} (hr : 0 <= r)
  statement: (NNReal.mk r hr)⁻¹ = .mk (r⁻¹) (inv_nonneg.2 hr)
  proof: rfl

@[simp]

中文:
定理 inv_mk
  条件: {r : 实数} (hr : 0 <= r)
  结论: (非负实数.mk r hr)⁻¹ = .mk (r⁻¹) (inv_nonneg.2 hr)
  证明: rfl

@[simp]
-/
theorem inv_mk {r : Real} (hr : 0 <= r) : (NNReal.mk r hr)⁻¹ = .mk (r⁻¹) (inv_nonneg.2 hr) := rfl

@[simp]
/--
theorem `inv_le` / 定理 `inv_le`

English:
theorem inv_le
  given: {r p : Real>=0} (h : r != 0)
  statement: r⁻¹ <= p ↔ 1 <= r * p
  proof: by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]

中文:
定理 inv_le
  条件: {r p : 实数>=0} (h : r != 0)
  结论: r⁻¹ <= p ↔ 1 <= r * p
  证明: by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem inv_le {r p : Real>=0} (h : r != 0) : r⁻¹ <= p ↔ 1 <= r * p := by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]

/--
theorem `inv_le_of_le_mul` / 定理 `inv_le_of_le_mul`

English:
theorem inv_le_of_le_mul
  given: {r p : Real>=0} (h : 1 <= r * p)
  statement: r⁻¹ <= p
  proof: by
  by_cases r = 0 <;> simp [*, inv_le]

@[simp]

中文:
定理 inv_le_of_le_mul
  条件: {r p : 实数>=0} (h : 1 <= r * p)
  结论: r⁻¹ <= p
  证明: by
  by_cases r = 0 <;> simp [*, inv_le]

@[simp]

Depends on / 依赖: inv_le
-/
theorem inv_le_of_le_mul {r p : Real>=0} (h : 1 <= r * p) : r⁻¹ <= p := by
  by_cases r = 0 <;> simp [*, inv_le]

@[simp]
/--
theorem `le_inv_iff_mul_le` / 定理 `le_inv_iff_mul_le`

English:
theorem le_inv_iff_mul_le
  given: {r p : Real>=0} (h : p != 0)
  statement: r <= p⁻¹ ↔ r * p <= 1
  proof: by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

@[simp]

中文:
定理 le_inv_iff_mul_le
  条件: {r p : 实数>=0} (h : p != 0)
  结论: r <= p⁻¹ ↔ r * p <= 1
  证明: by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

@[simp]

Depends on / 依赖: mul_comm, pos_iff_ne_zero
-/
theorem le_inv_iff_mul_le {r p : Real>=0} (h : p != 0) : r <= p⁻¹ ↔ r * p <= 1 := by
  rw [← mul_le_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

@[simp]
/--
theorem `lt_inv_iff_mul_lt` / 定理 `lt_inv_iff_mul_lt`

English:
theorem lt_inv_iff_mul_lt
  given: {r p : Real>=0} (h : p != 0)
  statement: r < p⁻¹ ↔ r * p < 1
  proof: by
  rw [← mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

中文:
定理 lt_inv_iff_mul_lt
  条件: {r p : 实数>=0} (h : p != 0)
  结论: r < p⁻¹ ↔ r * p < 1
  证明: by
  rw [← mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

Depends on / 依赖: mul_comm, pos_iff_ne_zero
-/
theorem lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 h)]; rw [mul_inv_cancel₀ h]; rw [mul_comm]

/--
theorem `div_le_of_le_mul` / 定理 `div_le_of_le_mul`

English:
theorem div_le_of_le_mul
  given: {a b c : Real>=0} (h : a <= b * c)
  statement: a / c <= b
  proof: if h0 : c = 0 then by simp [h0] else (div_le_iff₀ (pos_iff_ne_zero.2 h0)).2 h

中文:
定理 div_le_of_le_mul
  条件: {a b c : 实数>=0} (h : a <= b * c)
  结论: a / c <= b
  证明: if h0 : c = 0 then by simp [h0] else (div_le_iff₀ (pos_iff_ne_zero.2 h0)).2 h

Depends on / 依赖: pos_iff_ne_zero
-/
theorem div_le_of_le_mul {a b c : Real>=0} (h : a <= b * c) : a / c <= b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff₀ (pos_iff_ne_zero.2 h0)).2 h

/--
theorem `div_le_of_le_mul'` / 定理 `div_le_of_le_mul'`

English:
theorem div_le_of_le_mul'
  given: {a b c : Real>=0} (h : a <= b * c)
  statement: a / b <= c
  proof: div_le_of_le_mul mul_comm b c ▸ h

中文:
定理 div_le_of_le_mul'
  条件: {a b c : 实数>=0} (h : a <= b * c)
  结论: a / b <= c
  证明: div_le_of_le_mul mul_comm b c ▸ h

Depends on / 依赖: div_le_of_le_mul, mul_comm
-/
theorem div_le_of_le_mul' {a b c : Real>=0} (h : a <= b * c) : a / b <= c :=
div_le_of_le_mul mul_comm b c ▸ h

/--
theorem `mul_lt_of_lt_div` / 定理 `mul_lt_of_lt_div`

English:
theorem mul_lt_of_lt_div
  given: {a b r : Real>=0} (h : a < b / r)
  statement: a * r < b
  proof: (lt_div_iff₀ <| pos_iff_ne_zero.2 fun hr => False.elim <| by simp [hr] at h).1 h

中文:
定理 mul_lt_of_lt_div
  条件: {a b r : 实数>=0} (h : a < b / r)
  结论: a * r < b
  证明: (lt_div_iff₀ <| pos_iff_ne_zero.2 fun hr => False.elim <| by simp [hr] at h).1 h

Depends on / 依赖: False.elim, pos_iff_ne_zero
-/
theorem mul_lt_of_lt_div {a b r : Real>=0} (h : a < b / r) : a * r < b :=
  (lt_div_iff₀ <| pos_iff_ne_zero.2 fun hr => False.elim <| by simp [hr] at h).1 h

/--
theorem `le_of_forall_lt_one_mul_le` / 定理 `le_of_forall_lt_one_mul_le`

English:
theorem le_of_forall_lt_one_mul_le
  given: {x y : Real>=0} (h : forall a < 1, a * x <= y)
  statement: x <= y
  proof: le_of_forall_lt_imp_le_of_dense fun a ha => by
    have hx : x != 0 := ha.ne_zero
    have hx' : x⁻¹ != 0 := by rwa [Ne, inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x <= y := h _ this
    rwa [mul_assoc, inv_mul_cancel₀ hx, mul_one] at this



中文:
定理 le_of_对任意_lt_one_mul_le
  条件: {x y : 实数>=0} (h : 对任意 a < 1, a * x <= y)
  结论: x <= y
  证明: le_of_forall_lt_imp_le_of_dense fun a ha => by
    have hx : x != 0 := ha.ne_zero
    have hx' : x⁻¹ != 0 := by rwa [Ne, inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x <= y := h _ this
    rwa [mul_assoc, inv_mul_cancel₀ hx, mul_one] at this



Depends on / 依赖: ha.ne_zero, inv_eq_zero, inv_inv, le_of_forall_lt_imp_le_of_dense, lt_inv_iff_mul_lt, mul_assoc, mul_one, ne_zero
-/
theorem le_of_forall_lt_one_mul_le {x y : Real>=0} (h : forall a < 1, a * x <= y) : x <= y :=
  le_of_forall_lt_imp_le_of_dense fun a ha => by
    have hx : x != 0 := ha.ne_zero
    have hx' : x⁻¹ != 0 := by rwa [Ne, inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x <= y := h _ this
    rwa [mul_assoc, inv_mul_cancel₀ hx, mul_one] at this

nonrec theorem half_le_self (a : Real>=0) : a / 2 <= a :=
  half_le_self bot_le

nonrec theorem half_lt_self {a : Real>=0} (h : a != 0) : a / 2 < a :=
  half_lt_self h.bot_lt

/--
theorem `div_lt_one_of_lt` / 定理 `div_lt_one_of_lt`

English:
theorem div_lt_one_of_lt
  given: {a b : Real>=0} (h : a < b)
  statement: a / b < 1
  proof: by
  rwa [div_lt_iff₀ h.bot_lt, one_mul]

中文:
定理 div_lt_one_of_lt
  条件: {a b : 实数>=0} (h : a < b)
  结论: a / b < 1
  证明: by
  rwa [div_lt_iff₀ h.bot_lt, one_mul]

Depends on / 依赖: bot_lt, h.bot_lt, one_mul
-/
theorem div_lt_one_of_lt {a b : Real>=0} (h : a < b) : a / b < 1 := by
  rwa [div_lt_iff₀ h.bot_lt, one_mul]

/--
theorem `_root_.Real.toNNReal_inv` / 定理 `_root_.Real.toNNReal_inv`

English:
theorem _root_.Real.toNNReal_inv
  given: {x : Real}
  statement: Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹
  proof: by
  rcases le_total 0 x with hx | hx
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv]; rw [Real.toNNReal_coe]
  · rw [toNNReal_eq_zero.mpr hx, inv_zero, toNNReal_eq_zero.mpr (inv_nonpos.mpr hx)]

中文:
定理 _root_.实数.toNN实数_inv
  条件: {x : 实数}
  结论: 实数.toNN实数 x⁻¹ = (实数.toNN实数 x)⁻¹
  证明: by
  rcases le_total 0 x with hx | hx
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv]; rw [Real.toNNReal_coe]
  · rw [toNNReal_eq_zero.mpr hx, inv_zero, toNNReal_eq_zero.mpr (inv_nonpos.mpr hx)]

Depends on / 依赖: NNReal, NNReal.coe_inv, Real.coe_toNNReal, Real.toNNReal_coe, coe_inv, coe_toNNReal, inv_nonpos, inv_nonpos.mpr, inv_zero, le_total, nth_rw, toNNReal_coe, toNNReal_eq_zero, toNNReal_eq_zero.mpr
-/
theorem _root_.Real.toNNReal_inv {x : Real} : Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹ := by
  rcases le_total 0 x with hx | hx
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv]; rw [Real.toNNReal_coe]
  · rw [toNNReal_eq_zero.mpr hx, inv_zero, toNNReal_eq_zero.mpr (inv_nonpos.mpr hx)]

/--
theorem `_root_.Real.toNNReal_div` / 定理 `_root_.Real.toNNReal_div`

English:
theorem _root_.Real.toNNReal_div
  given: {x y : Real} (hx : 0 <= x)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← Real.toNNReal_inv]; rw [← Real.toNNReal_mul hx]

中文:
定理 _root_.实数.toNN实数_div
  条件: {x y : 实数} (hx : 0 <= x)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← Real.toNNReal_inv]; rw [← Real.toNNReal_mul hx]

Depends on / 依赖: Real.toNNReal_inv, Real.toNNReal_mul, div_eq_mul_inv, toNNReal_inv, toNNReal_mul
-/
theorem _root_.Real.toNNReal_div {x y : Real} (hx : 0 <= x) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← Real.toNNReal_inv]; rw [← Real.toNNReal_mul hx]

/--
theorem `_root_.Real.toNNReal_div'` / 定理 `_root_.Real.toNNReal_div'`

English:
theorem _root_.Real.toNNReal_div'
  given: {x y : Real} (hy : 0 <= y)
  proof: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [Real.toNNReal_mul (inv_nonneg.2 hy)]; rw [Real.toNNReal_inv]

中文:
定理 _root_.实数.toNN实数_div'
  条件: {x y : 实数} (hy : 0 <= y)
  证明: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [Real.toNNReal_mul (inv_nonneg.2 hy)]; rw [Real.toNNReal_inv]

Depends on / 依赖: Real.toNNReal_inv, Real.toNNReal_mul, div_eq_inv_mul, inv_nonneg, toNNReal_inv, toNNReal_mul
-/
theorem _root_.Real.toNNReal_div' {x y : Real} (hy : 0 <= y) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [Real.toNNReal_mul (inv_nonneg.2 hy)]; rw [Real.toNNReal_inv]

/--
theorem `inv_lt_one_iff` / 定理 `inv_lt_one_iff`

English:
theorem inv_lt_one_iff
  given: {x : Real>=0} (hx : x != 0)
  statement: x⁻¹ < 1 ↔ 1 < x
  proof: by
  rw [← one_div]; rw [div_lt_iff₀ hx.bot_lt]; rw [one_mul]

中文:
定理 inv_lt_one_iff
  条件: {x : 实数>=0} (hx : x != 0)
  结论: x⁻¹ < 1 ↔ 1 < x
  证明: by
  rw [← one_div]; rw [div_lt_iff₀ hx.bot_lt]; rw [one_mul]

Depends on / 依赖: bot_lt, hx.bot_lt, one_div, one_mul
-/
theorem inv_lt_one_iff {x : Real>=0} (hx : x != 0) : x⁻¹ < 1 ↔ 1 < x := by
  rw [← one_div]; rw [div_lt_iff₀ hx.bot_lt]; rw [one_mul]

/--
theorem `inv_lt_inv` / 定理 `inv_lt_inv`

English:
theorem inv_lt_inv
  given: {x y : Real>=0} (hx : x != 0) (h : x < y)
  statement: y⁻¹ < x⁻¹
  proof: inv_strictAnti₀ hx.bot_lt h

中文:
定理 inv_lt_inv
  条件: {x y : 实数>=0} (hx : x != 0) (h : x < y)
  结论: y⁻¹ < x⁻¹
  证明: inv_strictAnti₀ hx.bot_lt h

Depends on / 依赖: bot_lt, hx.bot_lt
-/
theorem inv_lt_inv {x y : Real>=0} (hx : x != 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx.bot_lt h

/--
lemma `exists_nat_pos_inv_lt` / 引理 `exists_nat_pos_inv_lt`

English:
lemma exists_nat_pos_inv_lt
  given: {b : Real>=0} (hb : 0 < b)
  proof: b.toReal.exists_nat_pos_inv_lt hb

中文:
引理 存在_nat_pos_inv_lt
  条件: {b : 实数>=0} (hb : 0 < b)
  证明: b.toReal.exists_nat_pos_inv_lt hb

Depends on / 依赖: b.toReal.exists_nat_pos_inv_lt, exists_nat_pos_inv_lt, toReal
-/
lemma exists_nat_pos_inv_lt {b : Real>=0} (hb : 0 < b) :
    exists (n : Nat), 0 < n ∧ (n : Real>=0)⁻¹ < b :=
  b.toReal.exists_nat_pos_inv_lt hb

end Inv

@[simp]
/--
theorem `abs_eq` / 定理 `abs_eq`

English:
theorem abs_eq
  given: (x : Real>=0)
  statement: |(x : Real)| = x
  proof: abs_of_nonneg x.property

中文:
定理 abs_eq
  条件: (x : 实数>=0)
  结论: |(x : 实数)| = x
  证明: abs_of_nonneg x.property

Depends on / 依赖: abs_of_nonneg, property, x.property
-/
theorem abs_eq (x : Real>=0) : |(x : Real)| = x :=
  abs_of_nonneg x.property

section Csupr

open Set

variable {ι : Sort*} {f : ι -> Real>=0}

/--
theorem `le_toNNReal_of_coe_le` / 定理 `le_toNNReal_of_coe_le`

English:
theorem le_toNNReal_of_coe_le
  given: {x : Real>=0} {y : Real} (h : ↑x <= y)
  statement: x <= y.toNNReal
  proof: (le_toNNReal_iff_coe_le <| x.2.trans h).2 h

nonrec theorem sSup_of_not_bddAbove {s : Set Real>=0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  grind [csSup_of_not_bddAbove, csSup_empty, bot_eq_zero']

中文:
定理 le_toNN实数_of_coe_le
  条件: {x : 实数>=0} {y : 实数} (h : ↑x <= y)
  结论: x <= y.toNN实数
  证明: (le_toNNReal_iff_coe_le <| x.2.trans h).2 h

nonrec theorem sSup_of_not_bddAbove {s : Set Real>=0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  grind [csSup_of_not_bddAbove, csSup_empty, bot_eq_zero']

Depends on / 依赖: le_toNNReal_iff_coe_le
-/
theorem le_toNNReal_of_coe_le {x : Real>=0} {y : Real} (h : ↑x <= y) : x <= y.toNNReal :=
  (le_toNNReal_iff_coe_le <| x.2.trans h).2 h

nonrec theorem sSup_of_not_bddAbove {s : Set Real>=0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  grind [csSup_of_not_bddAbove, csSup_empty, bot_eq_zero']

/--
theorem `iSup_of_not_bddAbove` / 定理 `iSup_of_not_bddAbove`

English:
theorem iSup_of_not_bddAbove
  given: (hf : ¬BddAbove (range f))
  statement: ⨆ i, f i = 0
  proof: sSup_of_not_bddAbove hf

中文:
定理 iSup_of_not_bddAbove
  条件: (hf : ¬BddAbove (range f))
  结论: ⨆ i, f i = 0
  证明: sSup_of_not_bddAbove hf

Depends on / 依赖: sSup_of_not_bddAbove
-/
theorem iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf

/--
theorem `iSup_empty` / 定理 `iSup_empty`

English:
theorem iSup_empty
  given: [IsEmpty ι] (f : ι -> Real>=0)
  statement: ⨆ i, f i = 0
  proof: ciSup_of_empty f

中文:
定理 iSup_empty
  条件: [是空 ι] (f : ι -> 实数>=0)
  结论: ⨆ i, f i = 0
  证明: ciSup_of_empty f

Depends on / 依赖: ciSup_of_empty
-/
theorem iSup_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨆ i, f i = 0 := ciSup_of_empty f

/--
theorem `iInf_empty` / 定理 `iInf_empty`

English:
theorem iInf_empty
  given: [IsEmpty ι] (f : ι -> Real>=0)
  statement: ⨅ i, f i = 0
  proof: by
  rw [_root_.iInf_of_isEmpty]; rw [sInf_empty]

中文:
定理 iInf_empty
  条件: [是空 ι] (f : ι -> 实数>=0)
  结论: ⨅ i, f i = 0
  证明: by
  rw [_root_.iInf_of_isEmpty]; rw [sInf_empty]

Depends on / 依赖: _root_, _root_.iInf_of_isEmpty, iInf_of_isEmpty, sInf_empty
-/
theorem iInf_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨅ i, f i = 0 := by
  rw [_root_.iInf_of_isEmpty]; rw [sInf_empty]

/--
lemma `iSup_eq_zero` / 引理 `iSup_eq_zero`

English:
lemma iSup_eq_zero
  given: (hf : BddAbove (range f))
  statement: ⨆ i, f i = 0 ↔ forall i, f i = 0
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

@[simp]

中文:
引理 iSup_eq_zero
  条件: (hf : BddAbove (range f))
  结论: ⨆ i, f i = 0 ↔ 对任意 i, f i = 0
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

@[simp]
-/
@[simp] lemma iSup_eq_zero (hf : BddAbove (range f)) : ⨆ i, f i = 0 ↔ forall i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

@[simp]
/--
theorem `iInf_const_zero` / 定理 `iInf_const_zero`

English:
theorem iInf_const_zero
  given: {α : Sort*}
  statement: ⨅ _ : α, (0 : Real>=0) = 0
  proof: by
  rw [← coe_inj]; rw [coe_iInf]
  exact Real.iInf_const_zero

中文:
定理 iInf_const_zero
  条件: {α : 类型层*}
  结论: ⨅ _ : α, (0 : 实数>=0) = 0
  证明: by
  rw [← coe_inj]; rw [coe_iInf]
  exact Real.iInf_const_zero

Depends on / 依赖: Real.iInf_const_zero, coe_iInf, coe_inj, iInf_const_zero
-/
theorem iInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : Real>=0) = 0 := by
  rw [← coe_inj]; rw [coe_iInf]
  exact Real.iInf_const_zero

end Csupr

end NNReal

namespace Set

namespace OrdConnected

variable {s : Set Real} {t : Set Real>=0}

/--
theorem `preimage_coe_nnreal_real` / 定理 `preimage_coe_nnreal_real`

English:
theorem preimage_coe_nnreal_real
  given: (h : s.OrdConnected)
  statement: ((↑) ⁻¹' s : Set Real>=0).OrdConnected
  proof: h.preimage_mono NNReal.coe_mono

中文:
定理 preimage_coe_nnreal_real
  条件: (h : s.序连通)
  结论: ((↑) ⁻¹' s : 集合 实数>=0).序连通
  证明: h.preimage_mono NNReal.coe_mono

Depends on / 依赖: NNReal, NNReal.coe_mono, coe_mono, h.preimage_mono, preimage_mono
-/
theorem preimage_coe_nnreal_real (h : s.OrdConnected) : ((↑) ⁻¹' s : Set Real>=0).OrdConnected :=
  h.preimage_mono NNReal.coe_mono

/--
theorem `image_coe_nnreal_real` / 定理 `image_coe_nnreal_real`

English:
theorem image_coe_nnreal_real
  given: (h : t.OrdConnected)
  statement: ((↑) '' t : Set Real).OrdConnected
  proof: ⟨forall_mem_image.2 fun x hx =>
      forall_mem_image.2 fun _y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

中文:
定理 image_coe_nnreal_real
  条件: (h : t.序连通)
  结论: ((↑) '' t : 集合 实数).序连通
  证明: ⟨forall_mem_image.2 fun x hx =>
      forall_mem_image.2 fun _y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

Depends on / 依赖: forall_mem_image, h.out
-/
theorem image_coe_nnreal_real (h : t.OrdConnected) : ((↑) '' t : Set Real).OrdConnected :=
  ⟨forall_mem_image.2 fun x hx =>
      forall_mem_image.2 fun _y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

-- TODO: does it generalize to a `GaloisInsertion`?
/--
theorem `image_real_toNNReal` / 定理 `image_real_toNNReal`

English:
theorem image_real_toNNReal
  given: (h : s.OrdConnected)
  statement: (Real.toNNReal '' s).OrdConnected
  proof: by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases le_total y 0 with hy₀ | hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (toNNReal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to Real>=0 using hy₀
    rw [toNNRea

中文:
定理 image_real_toNN实数
  条件: (h : s.序连通)
  结论: (实数.toNN实数 '' s).序连通
  证明: by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases le_total y 0 with hy₀ | hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (toNNReal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to Real>=0 using hy₀
    rw [toNNRea

Depends on / 依赖: Real.toNNReal_of_nonpos, forall_mem_image, h.out, le_total, mem_Icc, nonpos_iff_eq_zero, toNNReal_coe, toNNReal_le_iff_le_coe, toNNReal_of_nonpos
-/
theorem image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnected := by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases le_total y 0 with hy₀ | hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (toNNReal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to Real>=0 using hy₀
    rw [toNNReal_coe] at hz
    exact ⟨z, h.out hx hy ⟨toNNReal_le_iff_le_coe.1 hz.1, hz.2⟩, toNNReal_coe⟩

/--
theorem `preimage_real_toNNReal` / 定理 `preimage_real_toNNReal`

English:
theorem preimage_real_toNNReal
  given: (h : t.OrdConnected)
  statement: (Real.toNNReal ⁻¹' t).OrdConnected
  proof: h.preimage_mono Real.toNNReal_monotone

中文:
定理 preimage_real_toNN实数
  条件: (h : t.序连通)
  结论: (实数.toNN实数 ⁻¹' t).序连通
  证明: h.preimage_mono Real.toNNReal_monotone

Depends on / 依赖: Real.toNNReal_monotone, h.preimage_mono, preimage_mono, toNNReal_monotone
-/
theorem preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNNReal_monotone

end OrdConnected

end Set

namespace Real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
/--
Definition of `nnabs` / `nnabs` 的定义

English:
definition nnabs
  signature: : Real ->*₀ Real>=0 where
  body: ⟨|x|, abs_nonneg x⟩
  map_zero' := by simp; rfl
  map_one' := by simp; rfl
  map_mul' x y := by simp [abs_mul]; rfl

@[norm_cast, simp]

中文:
定义 nnabs
  签名: : 实数 ->*₀ 实数>=0 where
  定义体: ⟨|x|, abs_nonneg x⟩
  map_zero' := by simp; rfl
  map_one' := by simp; rfl
  map_mul' x y := by simp [abs_mul]; rfl

@[norm_cast, simp]

Depends on / 依赖: abs_nonneg
-/
def nnabs : Real ->*₀ Real>=0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by simp; rfl
  map_one' := by simp; rfl
  map_mul' x y := by simp [abs_mul]; rfl

@[norm_cast, simp]
/--
theorem `coe_nnabs` / 定理 `coe_nnabs`

English:
theorem coe_nnabs
  given: (x : Real)
  statement: (nnabs x : Real) = |x|
  proof: rfl

@[simp]

中文:
定理 coe_nnabs
  条件: (x : 实数)
  结论: (nnabs x : 实数) = |x|
  证明: rfl

@[simp]
-/
theorem coe_nnabs (x : Real) : (nnabs x : Real) = |x| :=
  rfl

@[simp]
/--
theorem `nnabs_of_nonneg` / 定理 `nnabs_of_nonneg`

English:
theorem nnabs_of_nonneg
  given: {x : Real} (h : 0 <= x)
  statement: nnabs x = toNNReal x
  proof: by
  ext
  rw [coe_toNNReal x h]; rw [coe_nnabs]; rw [abs_of_nonneg h]

中文:
定理 nnabs_of_nonneg
  条件: {x : 实数} (h : 0 <= x)
  结论: nnabs x = toNN实数 x
  证明: by
  ext
  rw [coe_toNNReal x h]; rw [coe_nnabs]; rw [abs_of_nonneg h]

Depends on / 依赖: abs_of_nonneg, coe_nnabs, coe_toNNReal
-/
theorem nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x = toNNReal x := by
  ext
  rw [coe_toNNReal x h]; rw [coe_nnabs]; rw [abs_of_nonneg h]

/--
theorem `nnabs_coe` / 定理 `nnabs_coe`

English:
theorem nnabs_coe
  given: (x : Real>=0)
  statement: nnabs x = x
  proof: by simp

中文:
定理 nnabs_coe
  条件: (x : 实数>=0)
  结论: nnabs x = x
  证明: by simp
-/
theorem nnabs_coe (x : Real>=0) : nnabs x = x := by simp

/--
theorem `coe_toNNReal_le` / 定理 `coe_toNNReal_le`

English:
theorem coe_toNNReal_le
  given: (x : Real)
  statement: (toNNReal x : Real) <= |x|
  proof: max_le (le_abs_self _) (abs_nonneg _)

中文:
定理 coe_toNN实数_le
  条件: (x : 实数)
  结论: (toNN实数 x : 实数) <= |x|
  证明: max_le (le_abs_self _) (abs_nonneg _)

Depends on / 依赖: abs_nonneg, le_abs_self, max_le
-/
theorem coe_toNNReal_le (x : Real) : (toNNReal x : Real) <= |x| :=
  max_le (le_abs_self _) (abs_nonneg _)

/--
lemma `toNNReal_abs` / 引理 `toNNReal_abs`

English:
lemma toNNReal_abs
  given: (x : Real)
  statement: |x|.toNNReal = nnabs x
  proof: NNReal.coe_injective by simp

中文:
引理 toNN实数_abs
  条件: (x : 实数)
  结论: |x|.toNN实数 = nnabs x
  证明: NNReal.coe_injective by simp
-/
@[simp] lemma toNNReal_abs (x : Real) : |x|.toNNReal = nnabs x := NNReal.coe_injective by simp

/--
lemma `nnabs_natCast` / 引理 `nnabs_natCast`

English:
lemma nnabs_natCast
  given: (n : Nat)
  statement: nnabs n = n
  proof: by simp

中文:
引理 nnabs_natCast
  条件: (n : 自然数)
  结论: nnabs n = n
  证明: by simp
-/
@[simp high] lemma nnabs_natCast (n : Nat) : nnabs n = n := by simp
/--
lemma `nnabs_ofNat` / 引理 `nnabs_ofNat`

English:
lemma nnabs_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: nnabs ofNat(n) = ofNat(n)
  proof: by simp

中文:
引理 nnabs_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: nnabs of自然数(n) = of自然数(n)
  证明: by simp
-/
@[simp high] lemma nnabs_ofNat (n : Nat) [n.AtLeastTwo] : nnabs ofNat(n) = ofNat(n) := by simp

/--
theorem `cast_natAbs_eq_nnabs_cast` / 定理 `cast_natAbs_eq_nnabs_cast`

English:
theorem cast_natAbs_eq_nnabs_cast
  given: (n : Int)
  statement: (n.natAbs : Real>=0) = nnabs n
  proof: by
  ext
  rw [NNReal.coe_natCast]; rw [Nat.cast_natAbs]; rw [Real.coe_nnabs]; rw [Int.cast_abs]

@[simp]

中文:
定理 cast_natAbs_eq_nnabs_cast
  条件: (n : 整数)
  结论: (n.natAbs : 实数>=0) = nnabs n
  证明: by
  ext
  rw [NNReal.coe_natCast]; rw [Nat.cast_natAbs]; rw [Real.coe_nnabs]; rw [Int.cast_abs]

@[simp]

Depends on / 依赖: Int.cast_abs, NNReal, NNReal.coe_natCast, Nat.cast_natAbs, Real.coe_nnabs, cast_abs, cast_natAbs, coe_natCast, coe_nnabs
-/
theorem cast_natAbs_eq_nnabs_cast (n : Int) : (n.natAbs : Real>=0) = nnabs n := by
  ext
  rw [NNReal.coe_natCast]; rw [Nat.cast_natAbs]; rw [Real.coe_nnabs]; rw [Int.cast_abs]

@[simp]
/--
theorem `nnabs_pos` / 定理 `nnabs_pos`

English:
theorem nnabs_pos
  given: {x : Real}
  statement: 0 < x.nnabs ↔ x != 0
  proof: by simp [← NNReal.coe_pos]

中文:
定理 nnabs_pos
  条件: {x : 实数}
  结论: 0 < x.nnabs ↔ x != 0
  证明: by simp [← NNReal.coe_pos]

Depends on / 依赖: NNReal, NNReal.coe_pos, coe_pos
-/
theorem nnabs_pos {x : Real} : 0 < x.nnabs ↔ x != 0 := by simp [← NNReal.coe_pos]

/--
lemma `nnreal_dichotomy` / 引理 `nnreal_dichotomy`

English:
lemma nnreal_dichotomy
  given: (r : Real)
  statement: exists x : Real>=0, r = x ∨ r = -x
  proof: by
  obtain (hr | hr) : 0 <= r ∨ 0 <= -r := by simpa using le_total ..
  all_goals
    rw [← neg_neg r]
    lift (_ : Real) to Real>=0 using hr with r
    aesop

中文:
引理 nnreal_dichotomy
  条件: (r : 实数)
  结论: 存在 x : 实数>=0, r = x ∨ r = -x
  证明: by
  obtain (hr | hr) : 0 <= r ∨ 0 <= -r := by simpa using le_total ..
  all_goals
    rw [← neg_neg r]
    lift (_ : Real) to Real>=0 using hr with r
    aesop

Depends on / 依赖: all_goals, le_total, neg_neg
-/
lemma nnreal_dichotomy (r : Real) : exists x : Real>=0, r = x ∨ r = -x := by
  obtain (hr | hr) : 0 <= r ∨ 0 <= -r := by simpa using le_total ..
  all_goals
    rw [← neg_neg r]
    lift (_ : Real) to Real>=0 using hr with r
    aesop

/--
lemma `nnreal_trichotomy` / 引理 `nnreal_trichotomy`

English:
lemma nnreal_trichotomy
  given: (r : Real)
  statement: r = 0 ∨ exists x : Real>=0, 0 < x ∧ (r = x ∨ r = -x)
  proof: by
  obtain ⟨x, hx⟩ := nnreal_dichotomy r
  rw [or_iff_not_imp_left]
  aesop (add simp pos_iff_ne_zero)

中文:
引理 nnreal_trichotomy
  条件: (r : 实数)
  结论: r = 0 ∨ 存在 x : 实数>=0, 0 < x ∧ (r = x ∨ r = -x)
  证明: by
  obtain ⟨x, hx⟩ := nnreal_dichotomy r
  rw [or_iff_not_imp_left]
  aesop (add simp pos_iff_ne_zero)

Depends on / 依赖: extendScalars, nnreal_dichotomy, or_iff_not_imp_left, pos_iff_ne_zero
-/
lemma nnreal_trichotomy (r : Real) : r = 0 ∨ exists x : Real>=0, 0 < x ∧ (r = x ∨ r = -x) := by
  obtain ⟨x, hx⟩ := nnreal_dichotomy r
  rw [or_iff_not_imp_left]
  aesop (add simp pos_iff_ne_zero)

/-- To prove a property holds for real numbers it suffices to show that it holds for `x : ℝ≥0`,
and if it holds for `x : ℝ≥0`, then it does also for `(-↑x : ℝ)`. -/
@[elab_as_elim]
/--
lemma `nnreal_induction_on` / 引理 `nnreal_induction_on`

English:
lemma nnreal_induction_on
  statement: {motive : Real -> Prop} (nonneg : forall x : Real>=0, motive x)
  proof: by
  obtain ⟨r, (rfl | rfl)⟩ := r.nnreal_dichotomy
  all_goals simp_all

中文:
引理 nnreal_induction_on
  结论: {motive : 实数 -> 命题} (nonneg : 对任意 x : 实数>=0, motive x)
  证明: by
  obtain ⟨r, (rfl | rfl)⟩ := r.nnreal_dichotomy
  all_goals simp_all

Depends on / 依赖: all_goals, nnreal_dichotomy, r.nnreal_dichotomy
-/
lemma nnreal_induction_on {motive : Real -> Prop} (nonneg : forall x : Real>=0, motive x)
    (nonpos : forall x : Real>=0, motive x -> motive (-x)) (r : Real) : motive r := by
  obtain ⟨r, (rfl | rfl)⟩ := r.nnreal_dichotomy
  all_goals simp_all

/-- A version of `nnreal_induction_on` which splits into three cases (zero, positive and negative)
instead of two. -/
@[elab_as_elim]
/--
lemma `nnreal_induction_on'` / 引理 `nnreal_induction_on'`

English:
lemma nnreal_induction_on'
  statement: {motive : Real -> Prop} (zero : motive 0) (pos : forall x : Real>=0, 0 < x -> motive x)
  proof: by
  obtain rfl | ⟨r, hr, (rfl | rfl)⟩ := r.nnreal_trichotomy
  all_goals simp_all

中文:
引理 nnreal_induction_on'
  结论: {motive : 实数 -> 命题} (zero : motive 0) (pos : 对任意 x : 实数>=0, 0 < x -> motive x)
  证明: by
  obtain rfl | ⟨r, hr, (rfl | rfl)⟩ := r.nnreal_trichotomy
  all_goals simp_all

Depends on / 依赖: all_goals, nnreal_trichotomy, r.nnreal_trichotomy
-/
lemma nnreal_induction_on' {motive : Real -> Prop} (zero : motive 0) (pos : forall x : Real>=0, 0 < x -> motive x)
    (neg : forall x : Real>=0, 0 < x -> motive x -> motive (-x)) (r : Real) : motive r := by
  obtain rfl | ⟨r, hr, (rfl | rfl)⟩ := r.nnreal_trichotomy
  all_goals simp_all

end Real

section StrictMono

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/--
theorem `NNReal.exists_lt_of_strictMono` / 定理 `NNReal.exists_lt_of_strictMono`

English:
theorem NNReal.exists_lt_of_strictMono
  statement: [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f)
  proof: by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [← map_one f]; exact hf hu1
    · have hfg0 : f g != 0 :=
        fun h0 => (Units.ne_zero g) ((map_eq_zero f).mp

中文:
定理 非负实数.存在_lt_of_strictMono
  结论: [h : 非平凡 Γ₀ˣ] {f : Γ₀ ->*₀ 实数>=0} (hf : 严格递增 f)
  证明: by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [← map_one f]; exact hf hu1
    · have hfg0 : f g != 0 :=
        fun h0 => (Units.ne_zero g) ((map_eq_zero f).mp

Depends on / 依赖: Units.ne_zero, Units.val_inv_eq_inv_val, exists_pow_lt_of_lt_one, hg1.symm, inv_lt_one_iff, lt_of_le_of_ne, map_eq_zero, map_one, ne_zero, nontrivial_iff_exists_ne, not_lt, not_lt.mp, split_ifs, val_inv_eq_inv_val
-/
theorem NNReal.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f)
    {r : Real>=0} (hr : 0 < r) : exists d : Γ₀ˣ, f d < r := by
  obtain ⟨g, hg1⟩ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mp h
  set u : Γ₀ˣ := if g < 1 then g else g⁻¹ with hu
  have hfu : f u < 1 := by
    rw [hu]
    split_ifs with hu1
    · rw [← map_one f]; exact hf hu1
    · have hfg0 : f g != 0 :=
        fun h0 => (Units.ne_zero g) ((map_eq_zero f).mp h0)
      have hg1' : 1 < g := lt_of_le_of_ne (not_lt.mp hu1) hg1.symm
      rw [Units.val_inv_eq_inv_val]; rw [map_inv₀]; rw [inv_lt_one_iff hfg0]; rw [← map_one f]
      exact hf hg1'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hfu
  use u ^ n
  rwa [Units.val_pow_eq_pow_val, map_pow]

/--
theorem `Real.exists_lt_of_strictMono` / 定理 `Real.exists_lt_of_strictMono`

English:
theorem Real.exists_lt_of_strictMono
  statement: [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f)
  proof: by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_lt_of_strictMono hf hs

中文:
定理 实数.存在_lt_of_strictMono
  结论: [h : 非平凡 Γ₀ˣ] {f : Γ₀ ->*₀ 实数>=0} (hf : 严格递增 f)
  证明: by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_lt_of_strictMono hf hs

Depends on / 依赖: NNReal, NNReal.exists_lt_of_strictMono, exists_lt_of_strictMono, le_of_lt
-/
theorem Real.exists_lt_of_strictMono [h : Nontrivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f)
    {r : Real} (hr : 0 < r) : exists d : Γ₀ˣ, (f d : Real) < r := by
  set s : NNReal := ⟨r, le_of_lt hr⟩
  have hs : 0 < s := hr
  exact NNReal.exists_lt_of_strictMono hf hs

end StrictMono

/-- While not very useful, this instance uses the same representation as `Real.instRepr`. -/
unsafe instance : Repr Real>=0 where
  reprPrec r _ := f!"({repr r.val}).toNNReal"

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

alias ⟨_, nnreal_coe_pos⟩ := coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity NNReal.toReal _]
meta def evalNNRealtoReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(NNReal.toReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(nnreal_coe_pos $pa))
    | _ => pure (.nonnegative q(NNReal.coe_nonneg $a))
  | _, _, _ => throwError "not NNReal.toReal"

/-- Extension for the `positivity` tactic: `Real.toNNReal` -/
@[positivity Real.toNNReal _]
meta def evalRealToNNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0), ~q(Real.toNNReal $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a) with
    | .positive pa => pure (.positive q(toNNReal_pos.mpr $pa))
    | _ => failure
  | _, _, _ => throwError "not Real.toNNReal"

alias ⟨_, nnabs_pos_of_pos⟩ := Real.nnabs_pos

/-- Extension for the `positivity` tactic: `Real.nnabs` -/
@[positivity Real.nnabs _]
meta def evalRealNNAbs : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0), ~q(Real.nnabs $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a).toNonzero with
    | some pa => pure (.positive q(nnabs_pos_of_pos $pa))
    | _ => failure
  | _, _, _ => throwError "not Real.nnabs"

end Mathlib.Meta.Positivity
