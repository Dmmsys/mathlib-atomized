/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Norms on `ℝ` and `ℝ≥0`

We equip `ℝ`, `ℝ≥0`, and `ℝ≥0∞` with their natural norms / enorms.

## Tags

normed group
-/

public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

namespace NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NNNorm Real>=0
  body: x

中文:
实例 :
  签名: NN范数 实数>=0
  定义体: x
-/
instance : NNNorm Real>=0 where
  nnnorm x := x

/--
lemma `nnnorm_eq_self` / 引理 `nnnorm_eq_self`

English:
lemma nnnorm_eq_self
  given: (x : Real>=0)
  statement: ‖x‖₊ = x
  proof: rfl

中文:
引理 nnnorm_eq_self
  条件: (x : 实数>=0)
  结论: ‖x‖₊ = x
  证明: rfl
-/
@[simp] lemma nnnorm_eq_self (x : Real>=0) : ‖x‖₊ = x := rfl

end NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ENorm Real>=0∞
  body: x

中文:
实例 :
  签名: E范数 实数>=0∞
  定义体: x
-/
instance : ENorm Real>=0∞ where
  enorm x := x

/--
lemma `enorm_eq_self` / 引理 `enorm_eq_self`

English:
lemma enorm_eq_self
  given: (x : Real>=0∞)
  statement: ‖x‖ₑ = x
  proof: rfl

中文:
引理 enorm_eq_self
  条件: (x : 实数>=0∞)
  结论: ‖x‖ₑ = x
  证明: rfl
-/
@[simp] lemma enorm_eq_self (x : Real>=0∞) : ‖x‖ₑ = x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ENormedAddCommMonoid Real>=0∞
  body: continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

中文:
实例 :
  签名: ENormedAddComm幺半群 实数>=0∞
  定义体: continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

Depends on / 依赖: continuous_id
-/
noncomputable instance : ENormedAddCommMonoid Real>=0∞ where
  continuous_enorm := continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

namespace Real

variable {r : Real}

/--
Instance `norm` / 实例 `norm`

English:
instance norm
  signature: : Norm Real where
  body: |r|

@[simp]

中文:
实例 norm
  签名: : 范数 实数 where
  定义体: |r|

@[simp]
-/
instance norm : Norm Real where
  norm r := |r|

@[simp]
/--
theorem `norm_eq_abs` / 定理 `norm_eq_abs`

English:
theorem norm_eq_abs
  given: (r : Real)
  statement: ‖r‖ = |r|
  proof: rfl

中文:
定理 norm_eq_abs
  条件: (r : 实数)
  结论: ‖r‖ = |r|
  证明: rfl
-/
theorem norm_eq_abs (r : Real) : ‖r‖ = |r| :=
  rfl

/--
Instance `normedAddCommGroup` / 实例 `normedAddCommGroup`

English:
instance normedAddCommGroup
  signature: : NormedAddCommGroup Real
  body: ⟨fun _r _y => by rw [Real.dist_eq, ← abs_neg, neg_sub, add_comm, sub_eq_add_neg, norm_eq_abs]⟩

中文:
实例 normedAddCommGroup
  签名: : 赋范交换加群 实数
  定义体: ⟨fun _r _y => by rw [Real.dist_eq, ← abs_neg, neg_sub, add_comm, sub_eq_add_neg, norm_eq_abs]⟩

Depends on / 依赖: Real.dist_eq, abs_neg, add_comm, dist_eq, neg_sub, norm_eq_abs, sub_eq_add_neg
-/
instance normedAddCommGroup : NormedAddCommGroup Real :=
  ⟨fun _r _y => by rw [Real.dist_eq, ← abs_neg, neg_sub, add_comm, sub_eq_add_neg, norm_eq_abs]⟩

/--
theorem `norm_of_nonneg` / 定理 `norm_of_nonneg`

English:
theorem norm_of_nonneg
  given: (hr : 0 <= r)
  statement: ‖r‖ = r
  proof: abs_of_nonneg hr

中文:
定理 norm_of_nonneg
  条件: (hr : 0 <= r)
  结论: ‖r‖ = r
  证明: abs_of_nonneg hr

Depends on / 依赖: abs_of_nonneg
-/
theorem norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r :=
  abs_of_nonneg hr

/--
theorem `norm_of_nonpos` / 定理 `norm_of_nonpos`

English:
theorem norm_of_nonpos
  given: (hr : r <= 0)
  statement: ‖r‖ = -r
  proof: abs_of_nonpos hr

中文:
定理 norm_of_nonpos
  条件: (hr : r <= 0)
  结论: ‖r‖ = -r
  证明: abs_of_nonpos hr

Depends on / 依赖: abs_of_nonpos
-/
theorem norm_of_nonpos (hr : r <= 0) : ‖r‖ = -r :=
  abs_of_nonpos hr

/--
theorem `le_norm_self` / 定理 `le_norm_self`

English:
theorem le_norm_self
  given: (r : Real)
  statement: r <= ‖r‖
  proof: le_abs_self r

中文:
定理 le_norm_self
  条件: (r : 实数)
  结论: r <= ‖r‖
  证明: le_abs_self r

Depends on / 依赖: le_abs_self
-/
theorem le_norm_self (r : Real) : r <= ‖r‖ :=
  le_abs_self r

/--
lemma `norm_natCast` / 引理 `norm_natCast`

English:
lemma norm_natCast
  given: (n : Nat)
  statement: ‖(n : Real)‖ = n
  proof: abs_of_nonneg n.cast_nonneg

中文:
引理 norm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 实数)‖ = n
  证明: abs_of_nonneg n.cast_nonneg

Depends on / 依赖: abs_of_nonneg, cast_nonneg, n.cast_nonneg
-/
lemma norm_natCast (n : Nat) : ‖(n : Real)‖ = n := abs_of_nonneg n.cast_nonneg
/--
lemma `nnnorm_natCast` / 引理 `nnnorm_natCast`

English:
lemma nnnorm_natCast
  given: (n : Nat)
  statement: ‖(n : Real)‖₊ = n
  proof: NNReal.eq norm_natCast _

中文:
引理 nnnorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 实数)‖₊ = n
  证明: NNReal.eq norm_natCast _
-/
@[simp 1100] lemma nnnorm_natCast (n : Nat) : ‖(n : Real)‖₊ = n := NNReal.eq norm_natCast _
/--
lemma `enorm_natCast` / 引理 `enorm_natCast`

English:
lemma enorm_natCast
  given: (n : Nat)
  statement: ‖(n : Real)‖ₑ = n
  proof: by simp [enorm]

中文:
引理 enorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 实数)‖ₑ = n
  证明: by simp [enorm]
-/
@[simp 1100] lemma enorm_natCast (n : Nat) : ‖(n : Real)‖ₑ = n := by simp [enorm]

/--
lemma `norm_ofNat` / 引理 `norm_ofNat`

English:
lemma norm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: norm_natCast n

中文:
引理 norm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: norm_natCast n
-/
@[simp 1100] lemma norm_ofNat (n : Nat) [n.AtLeastTwo] :
    ‖(ofNat(n) : Real)‖ = ofNat(n) := norm_natCast n

/--
lemma `nnnorm_ofNat` / 引理 `nnnorm_ofNat`

English:
lemma nnnorm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: nnnorm_natCast n

中文:
引理 nnnorm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: nnnorm_natCast n
-/
@[simp 1100] lemma nnnorm_ofNat (n : Nat) [n.AtLeastTwo] :
    ‖(ofNat(n) : Real)‖₊ = ofNat(n) := nnnorm_natCast n

/--
lemma `norm_two` / 引理 `norm_two`

English:
lemma norm_two
  statement: ‖(2 : Real)‖ = 2
  proof: abs_of_pos zero_lt_two

中文:
引理 norm_two
  结论: ‖(2 : 实数)‖ = 2
  证明: abs_of_pos zero_lt_two

Depends on / 依赖: abs_of_pos, zero_lt_two
-/
lemma norm_two : ‖(2 : Real)‖ = 2 := abs_of_pos zero_lt_two
/--
lemma `nnnorm_two` / 引理 `nnnorm_two`

English:
lemma nnnorm_two
  statement: ‖(2 : Real)‖₊ = 2
  proof: NNReal.eq by simp

@[simp 1100, norm_cast]

中文:
引理 nnnorm_two
  结论: ‖(2 : 实数)‖₊ = 2
  证明: NNReal.eq by simp

@[simp 1100, norm_cast]

Depends on / 依赖: NNReal, NNReal.eq
-/
lemma nnnorm_two : ‖(2 : Real)‖₊ = 2 := NNReal.eq by simp

@[simp 1100, norm_cast]
/--
lemma `norm_nnratCast` / 引理 `norm_nnratCast`

English:
lemma norm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : Real)‖ = q
  proof: norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]

中文:
引理 norm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : 实数)‖ = q
  证明: norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]

Depends on / 依赖: cast_nonneg, norm_of_nonneg, q.cast_nonneg
-/
lemma norm_nnratCast (q : Rat>=0) : ‖(q : Real)‖ = q := norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
/--
lemma `nnnorm_nnratCast` / 引理 `nnnorm_nnratCast`

English:
lemma nnnorm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : Real)‖₊ = q
  proof: by
  simp [nnnorm]
  rfl

中文:
引理 nnnorm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : 实数)‖₊ = q
  证明: by
  simp [nnnorm]
  rfl

Depends on / 依赖: nnnorm
-/
lemma nnnorm_nnratCast (q : Rat>=0) : ‖(q : Real)‖₊ = q := by
  simp [nnnorm]
  rfl

/--
theorem `nnnorm_of_nonneg` / 定理 `nnnorm_of_nonneg`

English:
theorem nnnorm_of_nonneg
  given: (hr : 0 <= r)
  statement: ‖r‖₊ = .mk r hr
  proof: NNReal.eq norm_of_nonneg hr

中文:
定理 nnnorm_of_nonneg
  条件: (hr : 0 <= r)
  结论: ‖r‖₊ = .mk r hr
  证明: NNReal.eq norm_of_nonneg hr

Depends on / 依赖: NNReal, NNReal.eq, norm_of_nonneg
-/
theorem nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr :=
NNReal.eq norm_of_nonneg hr

/--
lemma `enorm_of_nonneg` / 引理 `enorm_of_nonneg`

English:
lemma enorm_of_nonneg
  given: (hr : 0 <= r)
  statement: ‖r‖ₑ = .ofReal r
  proof: by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

中文:
引理 enorm_of_nonneg
  条件: (hr : 0 <= r)
  结论: ‖r‖ₑ = .of实数 r
  证明: by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

Depends on / 依赖: ENNReal, ENNReal.ofReal, nnnorm_of_nonneg, ofReal, toNNReal
-/
lemma enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r := by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

/--
lemma `enorm_ofReal_of_nonneg` / 引理 `enorm_ofReal_of_nonneg`

English:
lemma enorm_ofReal_of_nonneg
  given: {a : Real} (ha : 0 <= a)
  statement: ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ
  proof: by
  simp [Real.enorm_of_nonneg, ha]

中文:
引理 enorm_of实数_of_nonneg
  条件: {a : 实数} (ha : 0 <= a)
  结论: ‖广义非负实数.of实数 a‖ₑ = ‖a‖ₑ
  证明: by
  simp [Real.enorm_of_nonneg, ha]

Depends on / 依赖: Real.enorm_of_nonneg, enorm_of_nonneg
-/
lemma enorm_ofReal_of_nonneg {a : Real} (ha : 0 <= a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.enorm_of_nonneg, ha]

/--
lemma `nnnorm_abs` / 引理 `nnnorm_abs`

English:
lemma nnnorm_abs
  given: (r : Real)
  statement: ‖|r|‖₊ = ‖r‖₊
  proof: by simp [nnnorm]

中文:
引理 nnnorm_abs
  条件: (r : 实数)
  结论: ‖|r|‖₊ = ‖r‖₊
  证明: by simp [nnnorm]
-/
@[simp] lemma nnnorm_abs (r : Real) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]
/--
lemma `enorm_abs` / 引理 `enorm_abs`

English:
lemma enorm_abs
  given: (r : Real)
  statement: ‖|r|‖ₑ = ‖r‖ₑ
  proof: by simp [enorm]

中文:
引理 enorm_abs
  条件: (r : 实数)
  结论: ‖|r|‖ₑ = ‖r‖ₑ
  证明: by simp [enorm]
-/
@[simp] lemma enorm_abs (r : Real) : ‖|r|‖ₑ = ‖r‖ₑ := by simp [enorm]

/--
theorem `enorm_eq_ofReal` / 定理 `enorm_eq_ofReal`

English:
theorem enorm_eq_ofReal
  given: (hr : 0 <= r)
  statement: ‖r‖ₑ = .ofReal r
  proof: by
  rw [← ofReal_norm]; rw [norm_of_nonneg hr]

中文:
定理 enorm_eq_of实数
  条件: (hr : 0 <= r)
  结论: ‖r‖ₑ = .of实数 r
  证明: by
  rw [← ofReal_norm]; rw [norm_of_nonneg hr]

Depends on / 依赖: norm_of_nonneg, ofReal_norm
-/
theorem enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r := by
  rw [← ofReal_norm]; rw [norm_of_nonneg hr]

/--
lemma `enorm_toReal` / 引理 `enorm_toReal`

English:
lemma enorm_toReal
  given: {a : Real>=0∞} (ha : a != ∞)
  statement: ‖a.toReal‖ₑ = a
  proof: by
  simp [enorm_eq_ofReal, ha]

中文:
引理 enorm_to实数
  条件: {a : 实数>=0∞} (ha : a != ∞)
  结论: ‖a.to实数‖ₑ = a
  证明: by
  simp [enorm_eq_ofReal, ha]
-/
@[simp] lemma enorm_toReal {a : Real>=0∞} (ha : a != ∞) : ‖a.toReal‖ₑ = a := by
  simp [enorm_eq_ofReal, ha]

/--
theorem `enorm_eq_ofReal_abs` / 定理 `enorm_eq_ofReal_abs`

English:
theorem enorm_eq_ofReal_abs
  given: (r : Real)
  statement: ‖r‖ₑ = ENNReal.ofReal |r|
  proof: by
  rw [← enorm_eq_ofReal (abs_nonneg _)]; rw [enorm_abs]

中文:
定理 enorm_eq_of实数_abs
  条件: (r : 实数)
  结论: ‖r‖ₑ = 广义非负实数.of实数 |r|
  证明: by
  rw [← enorm_eq_ofReal (abs_nonneg _)]; rw [enorm_abs]

Depends on / 依赖: abs_nonneg, enorm_abs, enorm_eq_ofReal
-/
theorem enorm_eq_ofReal_abs (r : Real) : ‖r‖ₑ = ENNReal.ofReal |r| := by
  rw [← enorm_eq_ofReal (abs_nonneg _)]; rw [enorm_abs]

/--
theorem `toNNReal_eq_nnnorm_of_nonneg` / 定理 `toNNReal_eq_nnnorm_of_nonneg`

English:
theorem toNNReal_eq_nnnorm_of_nonneg
  given: (hr : 0 <= r)
  statement: r.toNNReal = ‖r‖₊
  proof: by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r]; rw [abs_of_nonneg hr]

中文:
定理 toNN实数_eq_nnnorm_of_nonneg
  条件: (hr : 0 <= r)
  结论: r.toNN实数 = ‖r‖₊
  证明: by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r]; rw [abs_of_nonneg hr]

Depends on / 依赖: Real.norm_eq_abs, Real.toNNReal_of_nonneg, abs_of_nonneg, norm_eq_abs, toNNReal_of_nonneg
-/
theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 <= r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r]; rw [abs_of_nonneg hr]

/--
theorem `ofReal_le_enorm` / 定理 `ofReal_le_enorm`

English:
theorem ofReal_le_enorm
  given: (r : Real)
  statement: ENNReal.ofReal r <= ‖r‖ₑ
  proof: by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

中文:
定理 of实数_le_enorm
  条件: (r : 实数)
  结论: 广义非负实数.of实数 r <= ‖r‖ₑ
  证明: by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

Depends on / 依赖: enorm_eq_ofReal_abs, le_abs_self
-/
theorem ofReal_le_enorm (r : Real) : ENNReal.ofReal r <= ‖r‖ₑ := by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

end Real

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : Real}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive (attr := simp high) norm_norm] -- Higher priority as a shortcut lemma.
/--
lemma `norm_norm'` / 引理 `norm_norm'`

English:
lemma norm_norm'
  given: (x : E)
  statement: ‖‖x‖‖ = ‖x‖
  proof: Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]

中文:
引理 norm_norm'
  条件: (x : E)
  结论: ‖‖x‖‖ = ‖x‖
  证明: Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]

Depends on / 依赖: Real.norm_of_nonneg, norm_nonneg, norm_of_nonneg
-/
lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]
/--
lemma `nnnorm_norm'` / 引理 `nnnorm_norm'`

English:
lemma nnnorm_norm'
  given: (x : E)
  statement: ‖‖x‖‖₊ = ‖x‖₊
  proof: by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]

中文:
引理 nnnorm_norm'
  条件: (x : E)
  结论: ‖‖x‖‖₊ = ‖x‖₊
  证明: by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]

Depends on / 依赖: nnnorm
-/
lemma nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊ := by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]
/--
lemma `enorm_norm'` / 引理 `enorm_norm'`

English:
lemma enorm_norm'
  given: (x : E)
  statement: ‖‖x‖‖ₑ = ‖x‖ₑ
  proof: by simp [enorm]

中文:
引理 enorm_norm'
  条件: (x : E)
  结论: ‖‖x‖‖ₑ = ‖x‖ₑ
  证明: by simp [enorm]
-/
lemma enorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ := by simp [enorm]

/--
lemma `enorm_enorm` / 引理 `enorm_enorm`

English:
lemma enorm_enorm
  given: {ε : Type*} [ENorm ε] (x : ε)
  statement: ‖‖x‖ₑ‖ₑ = ‖x‖ₑ
  proof: by simp [enorm]

中文:
引理 enorm_enorm
  条件: {ε : 类型} [E范数 ε] (x : ε)
  结论: ‖‖x‖ₑ‖ₑ = ‖x‖ₑ
  证明: by simp [enorm]
-/
lemma enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ := by simp [enorm]

end SeminormedCommGroup

/--
lemma `tendsto_norm_atTop_atTop` / 引理 `tendsto_norm_atTop_atTop`

English:
lemma tendsto_norm_atTop_atTop
  statement: Tendsto (norm : Real -> Real) atTop atTop
  proof: tendsto_abs_atTop_atTop

中文:
引理 tendsto_norm_atTop_atTop
  结论: 收敛 (norm : 实数 -> 实数) atTop atTop
  证明: tendsto_abs_atTop_atTop

Depends on / 依赖: tendsto_abs_atTop_atTop
-/
lemma tendsto_norm_atTop_atTop : Tendsto (norm : Real -> Real) atTop atTop := tendsto_abs_atTop_atTop
