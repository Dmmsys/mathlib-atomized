/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Sign.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Absolute value, sign, inversion and division on extended real numbers

This file defines an absolute value and sign function on `EReal` and uses them to provide a
`CommMonoidWithZero` instance, based on the absolute value and sign characterising all `EReal`s.
Then it defines the inverse of an `EReal` as `⊤⁻¹ = ⊥⁻¹ = 0`, which leads to a
`DivInvMonoid` instance and division.
-/

@[expose] public section

open ENNReal Set SignType

noncomputable section

namespace EReal

/-! ### Absolute value -/

-- TODO: use `Real.nnabs` for the case `(x : ℝ)`
/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: : EReal -> Real>=0∞

中文:
定义 abs
  签名: : E实数 -> 实数>=0∞
-/
protected def abs : EReal -> Real>=0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : Real) => ENNReal.ofReal |x|

/--
theorem `abs_top` / 定理 `abs_top`

English:
theorem abs_top
  statement: (⊤ : EReal).abs = ⊤
  proof: rfl

中文:
定理 abs_top
  结论: (⊤ : E实数).abs = ⊤
  证明: rfl
-/
@[simp] theorem abs_top : (⊤ : EReal).abs = ⊤ := rfl

/--
theorem `abs_bot` / 定理 `abs_bot`

English:
theorem abs_bot
  statement: (⊥ : EReal).abs = ⊤
  proof: rfl

中文:
定理 abs_bot
  结论: (⊥ : E实数).abs = ⊤
  证明: rfl
-/
@[simp] theorem abs_bot : (⊥ : EReal).abs = ⊤ := rfl

/--
theorem `abs_def` / 定理 `abs_def`

English:
theorem abs_def
  given: (x : Real)
  statement: (x : EReal).abs = ENNReal.ofReal |x|
  proof: rfl

中文:
定理 abs_def
  条件: (x : 实数)
  结论: (x : E实数).abs = 广义非负实数.of实数 |x|
  证明: rfl
-/
theorem abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x| := rfl

/--
theorem `abs_coe_lt_top` / 定理 `abs_coe_lt_top`

English:
theorem abs_coe_lt_top
  given: (x : Real)
  statement: (x : EReal).abs < ⊤
  proof: ENNReal.ofReal_lt_top

@[simp]

中文:
定理 abs_coe_lt_top
  条件: (x : 实数)
  结论: (x : E实数).abs < ⊤
  证明: ENNReal.ofReal_lt_top

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, ofReal_lt_top
-/
theorem abs_coe_lt_top (x : Real) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top

@[simp]
/--
theorem `abs_eq_zero_iff` / 定理 `abs_eq_zero_iff`

English:
theorem abs_eq_zero_iff
  given: {x : EReal}
  statement: x.abs = 0 ↔ x = 0
  proof: by
  induction x
  · simp
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]

中文:
定理 abs_eq_zero_iff
  条件: {x : E实数}
  结论: x.abs = 0 ↔ x = 0
  证明: by
  induction x
  · simp
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.top_ne_zero, abs_def, abs_nonpos_iff, abs_top, coe_eq_zero, ofReal_eq_zero, top_ne_zero
-/
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x
  · simp
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]
/--
theorem `abs_zero` / 定理 `abs_zero`

English:
theorem abs_zero
  statement: (0 : EReal).abs = 0
  proof: by rw [abs_eq_zero_iff]

@[simp]

中文:
定理 abs_zero
  结论: (0 : E实数).abs = 0
  证明: by rw [abs_eq_zero_iff]

@[simp]

Depends on / 依赖: abs_eq_zero_iff
-/
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]

@[simp]
/--
theorem `coe_abs` / 定理 `coe_abs`

English:
theorem coe_abs
  given: (x : Real)
  statement: ((x : EReal).abs : EReal) = (|x| : Real)
  proof: by
  rw [abs_def]; rw [← Real.coe_nnabs]; rw [ENNReal.ofReal_coe_nnreal]; rfl

@[simp]

中文:
定理 coe_abs
  条件: (x : 实数)
  结论: ((x : E实数).abs : E实数) = (|x| : 实数)
  证明: by
  rw [abs_def]; rw [← Real.coe_nnabs]; rw [ENNReal.ofReal_coe_nnreal]; rfl

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, Real.coe_nnabs, abs_def, coe_nnabs, ofReal_coe_nnreal
-/
theorem coe_abs (x : Real) : ((x : EReal).abs : EReal) = (|x| : Real) := by
  rw [abs_def]; rw [← Real.coe_nnabs]; rw [ENNReal.ofReal_coe_nnreal]; rfl

@[simp]
/--
theorem `abs_neg` / 定理 `abs_neg`

English:
theorem abs_neg
  statement: forall x : EReal, (-x).abs = x.abs

中文:
定理 abs_neg
  结论: 对任意 x : E实数, (-x).abs = x.abs
-/
protected theorem abs_neg : forall x : EReal, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : Real) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]

@[simp]
/--
theorem `abs_mul` / 定理 `abs_mul`

English:
theorem abs_mul
  given: (x y : EReal)
  statement: (x * y).abs = x.abs * y.abs
  proof: by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [abs_top]; rw [ENNReal.top_mul]
    rw [Ne]; rw [abs_eq_zero_iff]; rw [coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

中文:
定理 abs_mul
  条件: (x y : E实数)
  结论: (x * y).abs = x.abs * y.abs
  证明: by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [abs_top]; rw [ENNReal.top_mul]
    rw [Ne]; rw [abs_eq_zero_iff]; rw [coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, ENNReal.top_mul, EReal.abs_neg, EReal.mul_comm, _root_, _root_.abs_mul, abs_def, abs_eq_zero_iff, abs_mul, abs_neg, abs_nonneg, abs_top, abs_zero, coe_coe, coe_eq_zero, coe_mul, h.ne, mul_comm, mul_zero
-/
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [abs_top]; rw [ENNReal.top_mul]
    rw [Ne]; rw [abs_eq_zero_iff]; rw [coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

/-! ### Sign -/

open SignType (sign)

/--
theorem `sign_top` / 定理 `sign_top`

English:
theorem sign_top
  statement: sign (⊤ : EReal) = 1
  proof: rfl

中文:
定理 sign_top
  结论: sign (⊤ : E实数) = 1
  证明: rfl
-/
theorem sign_top : sign (⊤ : EReal) = 1 := rfl

/--
theorem `sign_bot` / 定理 `sign_bot`

English:
theorem sign_bot
  statement: sign (⊥ : EReal) = -1
  proof: rfl

中文:
定理 sign_bot
  结论: sign (⊥ : E实数) = -1
  证明: rfl
-/
theorem sign_bot : sign (⊥ : EReal) = -1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sign_coe` / 定理 `sign_coe`

English:
theorem sign_coe
  given: (x : Real)
  statement: sign (x : EReal) = sign x
  proof: by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]

中文:
定理 sign_coe
  条件: (x : 实数)
  结论: sign (x : E实数) = sign x
  证明: by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]

Depends on / 依赖: EReal.coe_neg, EReal.coe_pos, OrderHom, OrderHom.coe_mk, coe_mk, coe_neg, coe_pos
-/
theorem sign_coe (x : Real) : sign (x : EReal) = sign x := by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]
/--
theorem `coe_coe_sign` / 定理 `coe_coe_sign`

English:
theorem coe_coe_sign
  given: (x : SignType)
  statement: ((x : Real) : EReal) = x
  proof: by cases x <;> rfl

中文:
定理 coe_coe_sign
  条件: (x : SignType)
  结论: ((x : 实数) : E实数) = x
  证明: by cases x <;> rfl
-/
theorem coe_coe_sign (x : SignType) : ((x : Real) : EReal) = x := by cases x <;> rfl

/--
theorem `sign_neg` / 定理 `sign_neg`

English:
theorem sign_neg
  statement: forall x : EReal, sign (-x) = -sign x

中文:
定理 sign_neg
  结论: 对任意 x : E实数, sign (-x) = -sign x
-/
@[simp] theorem sign_neg : forall x : EReal, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : Real) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

@[simp]
/--
theorem `sign_mul` / 定理 `sign_mul`

English:
theorem sign_mul
  given: (x y : EReal)
  statement: sign (x * y) = sign x * sign y
  proof: by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [sign_top]; rw [one_mul]; rw [sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]

中文:
定理 sign_mul
  条件: (x y : E实数)
  结论: sign (x * y) = sign x * sign y
  证明: by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [sign_top]; rw [one_mul]; rw [sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]

Depends on / 依赖: EReal.coe_pos, EReal.mul_comm, _root_, _root_.sign_mul, coe_coe, coe_mul, coe_pos, mul_comm, mul_zero, neg_left, neg_mul, one_mul, sign_coe, sign_mul, sign_neg, sign_pos, sign_top, sign_zero, top_mul_coe_of_pos, top_pos
-/
theorem sign_mul (x y : EReal) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h]; rw [sign_top]; rw [one_mul]; rw [sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]

/--
theorem `sign_mul_abs` / 定理 `sign_mul_abs`

English:
theorem sign_mul_abs
  statement: forall x : EReal, (sign x * x.abs : EReal) = x

中文:
定理 sign_mul_abs
  结论: 对任意 x : E实数, (sign x * x.abs : E实数) = x
-/
@[simp] protected theorem sign_mul_abs : forall x : EReal, (sign x * x.abs : EReal) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : Real) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]

/--
theorem `abs_mul_sign` / 定理 `abs_mul_sign`

English:
theorem abs_mul_sign
  given: (x : EReal)
  statement: (x.abs * sign x : EReal) = x
  proof: by
  rw [EReal.mul_comm]; rw [EReal.sign_mul_abs]

中文:
定理 abs_mul_sign
  条件: (x : E实数)
  结论: (x.abs * sign x : E实数) = x
  证明: by
  rw [EReal.mul_comm]; rw [EReal.sign_mul_abs]
-/
@[simp] protected theorem abs_mul_sign (x : EReal) : (x.abs * sign x : EReal) = x := by
  rw [EReal.mul_comm]; rw [EReal.sign_mul_abs]

/--
theorem `sign_eq_and_abs_eq_iff_eq` / 定理 `sign_eq_and_abs_eq_iff_eq`

English:
theorem sign_eq_and_abs_eq_iff_eq
  given: {x y : EReal}
  proof: by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs]; rw [habs]; rw [hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

中文:
定理 sign_eq_and_abs_eq_iff_eq
  条件: {x y : E实数}
  证明: by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs]; rw [habs]; rw [hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

Depends on / 依赖: sign_mul_abs, x.sign_mul_abs, y.sign_mul_abs
-/
theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs]; rw [habs]; rw [hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

/--
theorem `le_iff_sign` / 定理 `le_iff_sign`

English:
theorem le_iff_sign
  given: {x y : EReal}
  proof: by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

中文:
定理 le_iff_sign
  条件: {x y : E实数}
  证明: by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

Depends on / 依赖: all_goals, imp_right, lt_or_eq, lt_or_eq.imp_right, monotone, reflect_lt, sign.monotone, sign.monotone.reflect_lt, sign_mul_abs, x.sign_mul_abs, y.sign_mul_abs
-/
theorem le_iff_sign {x y : EReal} :
    x <= y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs <= x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs <= y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs]; rw [← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero EReal
  body: { (inferInstance : MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

中文:
实例 :
  签名: 带零交换幺半群 E实数
  定义体: { (inferInstance : MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

Depends on / 依赖: EReal.mul_comm, MulZeroOneClass, abs_mul, and_self_iff, mul_assoc, mul_comm, sign_eq_and_abs_eq_iff_eq, sign_mul
-/
instance : CommMonoidWithZero EReal :=
  { (inferInstance : MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulMono EReal
  body: posMulMono_iff_covariant_pos.2 .mk by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
exact h.imp_right Or.imp (And.imp_right <| And.imp_right (mul_le_mul_right · _))
Or.imp_right And.imp_right And.imp_right (mul_le_mul_right · _)

中文:
实例 :
  签名: 正乘递增 E实数
  定义体: posMulMono_iff_covariant_pos.2 .mk by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
exact h.imp_right Or.imp (And.imp_right <| And.imp_right (mul_le_mul_right · _))
Or.imp_right And.imp_right And.imp_right (mul_le_mul_right · _)

Depends on / 依赖: And.imp_right, EReal.abs_mul, EReal.sign_mul, Or.imp, Or.imp_right, abs_mul, h.imp_right, imp_right, le_iff_sign, mul_le_mul_right, one_mul, posMulMono_iff_covariant_pos, sign_mul, sign_pos
-/
instance : PosMulMono EReal := posMulMono_iff_covariant_pos.2 .mk by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
exact h.imp_right Or.imp (And.imp_right <| And.imp_right (mul_le_mul_right · _))
Or.imp_right And.imp_right And.imp_right (mul_le_mul_right · _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulPosMono EReal
  body: posMulMono_iff_mulPosMono.1 inferInstance

中文:
实例 :
  签名: 乘正递增 E实数
  定义体: posMulMono_iff_mulPosMono.1 inferInstance

Depends on / 依赖: posMulMono_iff_mulPosMono
-/
instance : MulPosMono EReal := posMulMono_iff_mulPosMono.1 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosMulReflectLT EReal
  body: PosMulMono.toPosMulReflectLT

中文:
实例 :
  签名: 正乘反映严格偏序 E实数
  定义体: PosMulMono.toPosMulReflectLT

Depends on / 依赖: PosMulMono, PosMulMono.toPosMulReflectLT, toPosMulReflectLT
-/
instance : PosMulReflectLT EReal := PosMulMono.toPosMulReflectLT

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulPosReflectLT EReal
  body: MulPosMono.toMulPosReflectLT

中文:
实例 :
  签名: 乘正反映严格偏序 E实数
  定义体: MulPosMono.toMulPosReflectLT

Depends on / 依赖: MulPosMono, MulPosMono.toMulPosReflectLT, toMulPosReflectLT
-/
instance : MulPosReflectLT EReal := MulPosMono.toMulPosReflectLT

/--
lemma `mul_le_mul_of_nonpos_right` / 引理 `mul_le_mul_of_nonpos_right`

English:
lemma mul_le_mul_of_nonpos_right
  given: {a b c : EReal} (h : b <= a) (hc : c <= 0)
  statement: a * c <= b * c
  proof: by
  rw [mul_comm a c]; rw [mul_comm b c]; rw [← neg_le_neg_iff]; rw [← neg_mul c b]; rw [← neg_mul c a]
  rw [← neg_zero]; rw [EReal.le_neg] at hc
  gcongr

@[simp, norm_cast]

中文:
引理 mul_le_mul_of_nonpos_right
  条件: {a b c : E实数} (h : b <= a) (hc : c <= 0)
  结论: a * c <= b * c
  证明: by
  rw [mul_comm a c]; rw [mul_comm b c]; rw [← neg_le_neg_iff]; rw [← neg_mul c b]; rw [← neg_mul c a]
  rw [← neg_zero]; rw [EReal.le_neg] at hc
  gcongr

@[simp, norm_cast]

Depends on / 依赖: EReal.le_neg, le_neg, mul_comm, neg_le_neg_iff, neg_mul, neg_zero
-/
lemma mul_le_mul_of_nonpos_right {a b c : EReal} (h : b <= a) (hc : c <= 0) : a * c <= b * c := by
  rw [mul_comm a c]; rw [mul_comm b c]; rw [← neg_le_neg_iff]; rw [← neg_mul c b]; rw [← neg_mul c a]
  rw [← neg_zero]; rw [EReal.le_neg] at hc
  gcongr

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : Real) (n : Nat)
  statement: (↑(x ^ n) : EReal) = (x : EReal) ^ n
  proof: map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : Real ->* EReal) _ _

@[simp, norm_cast]

中文:
定理 coe_pow
  条件: (x : 实数) (n : 自然数)
  结论: (↑(x ^ n) : E实数) = (x : E实数) ^ n
  证明: map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : Real ->* EReal) _ _

@[simp, norm_cast]

Depends on / 依赖: coe_mul, coe_one, map_pow
-/
theorem coe_pow (x : Real) (n : Nat) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : Real ->* EReal) _ _

@[simp, norm_cast]
/--
theorem `coe_ennreal_pow` / 定理 `coe_ennreal_pow`

English:
theorem coe_ennreal_pow
  given: (x : Real>=0∞) (n : Nat)
  statement: (↑(x ^ n) : EReal) = (x : EReal) ^ n
  proof: map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : Real>=0∞ ->* EReal) _ _

中文:
定理 coe_ennreal_pow
  条件: (x : 实数>=0∞) (n : 自然数)
  结论: (↑(x ^ n) : E实数) = (x : E实数) ^ n
  证明: map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : Real>=0∞ ->* EReal) _ _

Depends on / 依赖: coe_ennreal_mul, coe_ennreal_one, map_pow
-/
theorem coe_ennreal_pow (x : Real>=0∞) (n : Nat) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : Real>=0∞ ->* EReal) _ _

/--
lemma `exists_nat_ge_mul` / 引理 `exists_nat_ge_mul`

English:
lemma exists_nat_ge_mul
  given: {a : EReal} (ha : a != ⊤) (n : Nat)
  proof: match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := EReal) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : Real) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← EReal.coe_mul, EReal.coe_le_coe_iff]

中文:
引理 存在_nat_ge_mul
  条件: {a : E实数} (ha : a != ⊤) (n : 自然数)
  证明: match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := EReal) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : Real) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← EReal.coe_mul, EReal.coe_le_coe_iff]

Depends on / 依赖: EReal.coe_le_coe_iff, EReal.coe_mul, Nat.cast_zero, an_m, bot_le, cast_nonneg, cast_zero, coe_coe_eq_natCast, coe_le_coe_iff, coe_mul, exists_nat_ge, ha.irrefl.rec, irrefl, mul_nonpos_iff, n.cast_nonneg
-/
lemma exists_nat_ge_mul {a : EReal} (ha : a != ⊤) (n : Nat) :
    exists m : Nat, a * n <= m :=
  match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := EReal) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : Real) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← EReal.coe_mul, EReal.coe_le_coe_iff]


/--
lemma `min_neg_neg` / 引理 `min_neg_neg`

English:
lemma min_neg_neg
  given: (x y : EReal)
  statement: min (-x) (-y) = -max x y
  proof: by
  rcases le_total x y with (h | h) <;> simp_all

中文:
引理 min_neg_neg
  条件: (x y : E实数)
  结论: 最小值 (-x) (-y) = -最大值 x y
  证明: by
  rcases le_total x y with (h | h) <;> simp_all

Depends on / 依赖: le_total
-/
lemma min_neg_neg (x y : EReal) : min (-x) (-y) = -max x y := by
  rcases le_total x y with (h | h) <;> simp_all

/--
lemma `max_neg_neg` / 引理 `max_neg_neg`

English:
lemma max_neg_neg
  given: (x y : EReal)
  statement: max (-x) (-y) = -min x y
  proof: by
  rcases le_total x y with (h | h) <;> simp_all

中文:
引理 max_neg_neg
  条件: (x y : E实数)
  结论: 最大值 (-x) (-y) = -最小值 x y
  证明: by
  rcases le_total x y with (h | h) <;> simp_all

Depends on / 依赖: le_total
-/
lemma max_neg_neg (x y : EReal) : max (-x) (-y) = -min x y := by
  rcases le_total x y with (h | h) <;> simp_all

/-! ### Inverse -/

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : EReal -> EReal

中文:
定义 inv
  签名: : E实数 -> E实数
-/
protected def inv : EReal -> EReal
  | ⊥ => 0
  | ⊤ => 0
  | (x : Real) => (x⁻¹ : Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (EReal)
  body: ⟨EReal.inv⟩

中文:
实例 :
  签名: 取逆 (E实数)
  定义体: ⟨EReal.inv⟩

Depends on / 依赖: EReal.inv
-/
instance : Inv (EReal) := ⟨EReal.inv⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvMonoid EReal
  body: EReal.inv

@[simp]

中文:
实例 :
  签名: 除逆幺半群 E实数
  定义体: EReal.inv

@[simp]

Depends on / 依赖: EReal.inv
-/
noncomputable instance : DivInvMonoid EReal where inv := EReal.inv

@[simp]
/--
lemma `inv_bot` / 引理 `inv_bot`

English:
lemma inv_bot
  statement: (⊥ : EReal)⁻¹ = 0
  proof: rfl

@[simp]

中文:
引理 inv_bot
  结论: (⊥ : E实数)⁻¹ = 0
  证明: rfl

@[simp]
-/
lemma inv_bot : (⊥ : EReal)⁻¹ = 0 := rfl

@[simp]
/--
lemma `inv_top` / 引理 `inv_top`

English:
lemma inv_top
  statement: (⊤ : EReal)⁻¹ = 0
  proof: rfl

中文:
引理 inv_top
  结论: (⊤ : E实数)⁻¹ = 0
  证明: rfl
-/
lemma inv_top : (⊤ : EReal)⁻¹ = 0 := rfl

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (x : Real)
  statement: (x⁻¹ : Real) = (x : EReal)⁻¹
  proof: rfl

@[simp]

中文:
引理 coe_inv
  条件: (x : 实数)
  结论: (x⁻¹ : 实数) = (x : E实数)⁻¹
  证明: rfl

@[simp]
-/
lemma coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹ := rfl

@[simp]
/--
lemma `inv_zero` / 引理 `inv_zero`

English:
lemma inv_zero
  statement: (0 : EReal)⁻¹ = 0
  proof: by
  change (0 : Real)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero]; rw [coe_zero]

中文:
引理 inv_zero
  结论: (0 : E实数)⁻¹ = 0
  证明: by
  change (0 : Real)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero]; rw [coe_zero]

Depends on / 依赖: GroupWithZero, GroupWithZero.inv_zero, coe_zero, inv_zero
-/
lemma inv_zero : (0 : EReal)⁻¹ = 0 := by
  change (0 : Real)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero]; rw [coe_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvOneMonoid EReal
  body: by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

中文:
实例 :
  签名: DivInvOne幺半群 E实数
  定义体: by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

Depends on / 依赖: _root_, _root_.inv_one, coe_inv, coe_one, inv_one, nth_rw
-/
noncomputable instance : DivInvOneMonoid EReal where
  inv_one := by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

/--
lemma `inv_neg` / 引理 `inv_neg`

English:
lemma inv_neg
  given: (a : EReal)
  statement: (-a)⁻¹ = -a⁻¹
  proof: by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

中文:
引理 inv_neg
  条件: (a : E实数)
  结论: (-a)⁻¹ = -a⁻¹
  证明: by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

Depends on / 依赖: EReal.coe_eq_coe_iff, _root_, _root_.inv_neg, coe_eq_coe_iff, coe_inv, coe_neg, inv_bot, inv_neg, inv_top, neg_bot, neg_top, neg_zero
-/
lemma inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹ := by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

/--
lemma `inv_inv` / 引理 `inv_inv`

English:
lemma inv_inv
  given: {a : EReal} (h : a != ⊥) (h' : a != ⊤)
  statement: (a⁻¹)⁻¹ = a
  proof: by
  rw [← coe_toReal h' h]; rw [← coe_inv a.toReal]; rw [← coe_inv a.toReal⁻¹]; rw [_root_.inv_inv a.toReal]

中文:
引理 inv_inv
  条件: {a : E实数} (h : a != ⊥) (h' : a != ⊤)
  结论: (a⁻¹)⁻¹ = a
  证明: by
  rw [← coe_toReal h' h]; rw [← coe_inv a.toReal]; rw [← coe_inv a.toReal⁻¹]; rw [_root_.inv_inv a.toReal]

Depends on / 依赖: _root_, _root_.inv_inv, a.toReal, coe_inv, coe_toReal, inv_inv, toReal
-/
lemma inv_inv {a : EReal} (h : a != ⊥) (h' : a != ⊤) : (a⁻¹)⁻¹ = a := by
  rw [← coe_toReal h' h]; rw [← coe_inv a.toReal]; rw [← coe_inv a.toReal⁻¹]; rw [_root_.inv_inv a.toReal]

/--
lemma `mul_inv` / 引理 `mul_inv`

English:
lemma mul_inv
  given: (a b : EReal)
  statement: (a * b)⁻¹ = a⁻¹ * b⁻¹
  proof: by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

中文:
引理 mul_inv
  条件: (a b : E实数)
  结论: (a * b)⁻¹ = a⁻¹ * b⁻¹
  证明: by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

Depends on / 依赖: EReal.coe_neg, EReal.coe_pos, EReal.induction, _root_, _root_.mul_inv, bot_bot, coe_coe, coe_inv, coe_mu, coe_mul, coe_neg, coe_pos, inv_bot, inv_top, mul_bot_of_pos, mul_comm, mul_inv, mul_zero, pos_bot, top_bot
-/
lemma mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]


/--
lemma `sign_mul_inv_abs` / 引理 `sign_mul_inv_abs`

English:
lemma sign_mul_inv_abs
  given: (a : EReal)
  statement: (sign a) * (a.abs : EReal)⁻¹ = a⁻¹
  proof: by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos

中文:
引理 sign_mul_inv_abs
  条件: (a : E实数)
  结论: (sign a) * (a.abs : E实数)⁻¹ = a⁻¹
  证明: by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos

Depends on / 依赖: SignType, SignType.coe_one, _root_, _root_.sign_neg, _root_.sign_pos, a_neg, a_pos, abs_def, abs_nonneg, abs_of_neg, abs_of_pos, coe_ennreal_ofReal, coe_neg, coe_neg_one, coe_one, inv_neg, lt_trichotomy, max_eq_left, neg_neg, neg_one_mul
-/
lemma sign_mul_inv_abs (a : EReal) : (sign a) * (a.abs : EReal)⁻¹ = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos

/--
lemma `sign_mul_inv_abs'` / 引理 `sign_mul_inv_abs'`

English:
lemma sign_mul_inv_abs'
  given: (a : EReal)
  statement: (sign a) * ((a.abs⁻¹ : Real>=0∞) : EReal) = a⁻¹
  proof: by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

中文:
引理 sign_mul_inv_abs'
  条件: (a : E实数)
  结论: (sign a) * ((a.abs⁻¹ : 实数>=0∞) : E实数) = a⁻¹
  证明: by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

Depends on / 依赖: SignType, SignType.coe_one, _root_, _root_.inv_neg, _root_.sign_neg, _root_.sign_pos, a_neg, a_pos, abs_def, abs_nonneg, abs_of_neg, abs_pos_of_neg, abs_pos_of_pos, coe_ennreal, coe_ennreal_ofReal, coe_inv, coe_neg, coe_neg_one, coe_one, inv_neg
-/
lemma sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : Real>=0∞) : EReal) = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos


/--
lemma `bot_lt_inv` / 引理 `bot_lt_inv`

English:
lemma bot_lt_inv
  given: (x : EReal)
  statement: ⊥ < x⁻¹
  proof: by
  cases x with
  | bot => exact inv_bot ▸ bot_lt_zero
  | top => exact EReal.inv_top ▸ bot_lt_zero
  | coe x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)

中文:
引理 bot_lt_inv
  条件: (x : E实数)
  结论: ⊥ < x⁻¹
  证明: by
  cases x with
  | bot => exact inv_bot ▸ bot_lt_zero
  | top => exact EReal.inv_top ▸ bot_lt_zero
  | coe x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)

Depends on / 依赖: EReal.inv_top, bot_lt_coe, bot_lt_zero, coe_inv, inv_bot, inv_top
-/
lemma bot_lt_inv (x : EReal) : ⊥ < x⁻¹ := by
  cases x with
  | bot => exact inv_bot ▸ bot_lt_zero
  | top => exact EReal.inv_top ▸ bot_lt_zero
  | coe x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)

/--
lemma `inv_lt_top` / 引理 `inv_lt_top`

English:
lemma inv_lt_top
  given: (x : EReal)
  statement: x⁻¹ < ⊤
  proof: by
  cases x with
  | bot => exact inv_bot ▸ zero_lt_top
  | top => exact EReal.inv_top ▸ zero_lt_top
  | coe x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)

中文:
引理 inv_lt_top
  条件: (x : E实数)
  结论: x⁻¹ < ⊤
  证明: by
  cases x with
  | bot => exact inv_bot ▸ zero_lt_top
  | top => exact EReal.inv_top ▸ zero_lt_top
  | coe x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)

Depends on / 依赖: EReal.inv_top, coe_inv, coe_lt_top, inv_bot, inv_top, zero_lt_top
-/
lemma inv_lt_top (x : EReal) : x⁻¹ < ⊤ := by
  cases x with
  | bot => exact inv_bot ▸ zero_lt_top
  | top => exact EReal.inv_top ▸ zero_lt_top
  | coe x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)

/--
lemma `inv_nonneg_of_nonneg` / 引理 `inv_nonneg_of_nonneg`

English:
lemma inv_nonneg_of_nonneg
  given: {a : EReal} (h : 0 <= a)
  statement: 0 <= a⁻¹
  proof: by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]; exact EReal.coe_nonneg.1 h

中文:
引理 inv_nonneg_of_nonneg
  条件: {a : E实数} (h : 0 <= a)
  结论: 0 <= a⁻¹
  证明: by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]; exact EReal.coe_nonneg.1 h

Depends on / 依赖: EReal.coe_nonneg, coe_inv, coe_nonneg, inv_nonneg
-/
lemma inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a) : 0 <= a⁻¹ := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]; exact EReal.coe_nonneg.1 h

/--
lemma `inv_nonpos_of_nonpos` / 引理 `inv_nonpos_of_nonpos`

English:
lemma inv_nonpos_of_nonpos
  given: {a : EReal} (h : a <= 0)
  statement: a⁻¹ <= 0
  proof: by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]; exact EReal.coe_nonpos.1 h

中文:
引理 inv_nonpos_of_nonpos
  条件: {a : E实数} (h : a <= 0)
  结论: a⁻¹ <= 0
  证明: by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]; exact EReal.coe_nonpos.1 h

Depends on / 依赖: EReal.coe_nonpos, coe_inv, coe_nonpos, inv_nonpos
-/
lemma inv_nonpos_of_nonpos {a : EReal} (h : a <= 0) : a⁻¹ <= 0 := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]; exact EReal.coe_nonpos.1 h

/--
lemma `inv_pos_of_pos_ne_top` / 引理 `inv_pos_of_pos_ne_top`

English:
lemma inv_pos_of_pos_ne_top
  given: {a : EReal} (h : 0 < a) (h' : a != ⊤)
  statement: 0 < a⁻¹
  proof: by
  lift a to Real using ⟨h', ne_bot_of_gt h⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h

中文:
引理 inv_pos_of_pos_ne_top
  条件: {a : E实数} (h : 0 < a) (h' : a != ⊤)
  结论: 0 < a⁻¹
  证明: by
  lift a to Real using ⟨h', ne_bot_of_gt h⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h

Depends on / 依赖: coe_inv, inv_pos_of_pos, ne_bot_of_gt
-/
lemma inv_pos_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : 0 < a⁻¹ := by
  lift a to Real using ⟨h', ne_bot_of_gt h⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h

/--
lemma `inv_neg_of_neg_ne_bot` / 引理 `inv_neg_of_neg_ne_bot`

English:
lemma inv_neg_of_neg_ne_bot
  given: {a : EReal} (h : a < 0) (h' : a != ⊥)
  statement: a⁻¹ < 0
  proof: by
  lift a to Real using ⟨ne_top_of_lt h, h'⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h

中文:
引理 inv_neg_of_neg_ne_bot
  条件: {a : E实数} (h : a < 0) (h' : a != ⊥)
  结论: a⁻¹ < 0
  证明: by
  lift a to Real using ⟨ne_top_of_lt h, h'⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h

Depends on / 依赖: coe_inv, inv_lt_zero, ne_top_of_lt
-/
lemma inv_neg_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : a⁻¹ < 0 := by
  lift a to Real using ⟨ne_top_of_lt h, h'⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h

/--
lemma `inv_strictAntiOn` / 引理 `inv_strictAntiOn`

English:
lemma inv_strictAntiOn
  statement: StrictAntiOn (fun (x : EReal) => x⁻¹) (Ioi 0)
  proof: by
  intro a a_0 b b_0 a_b
  push _ in _ at *
  lift a to Real using ⟨ne_top_of_lt a_b, ne_bot_of_gt a_0⟩
  match b with
  | ⊤ => exact inv_top ▸ inv_pos_of_pos_ne_top a_0 (coe_ne_top a)
  | ⊥ => exact (not_lt_bot b_0).rec
  | (b : Real) =>
    rw [← coe_inv a]; rw [← coe_inv b]; rw [EReal.coe_lt_coe_iff]
    exact _root_.inv_strictAntiOn (EReal.coe_pos.1 a_0) (EReal.coe_pos.1 b_0)
      (EReal.coe_lt_coe_iff.1 a_b)

中文:
引理 inv_strictAntiOn
  结论: StrictAntiOn (fun (x : E实数) => x⁻¹) (左开右无界区间 0)
  证明: by
  intro a a_0 b b_0 a_b
  push _ in _ at *
  lift a to Real using ⟨ne_top_of_lt a_b, ne_bot_of_gt a_0⟩
  match b with
  | ⊤ => exact inv_top ▸ inv_pos_of_pos_ne_top a_0 (coe_ne_top a)
  | ⊥ => exact (not_lt_bot b_0).rec
  | (b : Real) =>
    rw [← coe_inv a]; rw [← coe_inv b]; rw [EReal.coe_lt_coe_iff]
    exact _root_.inv_strictAntiOn (EReal.coe_pos.1 a_0) (EReal.coe_pos.1 b_0)
      (EReal.coe_lt_coe_iff.1 a_b)

Depends on / 依赖: EReal.coe_lt_coe_iff, EReal.coe_pos, _root_, _root_.inv_strictAntiOn, coe_inv, coe_lt_coe_iff, coe_ne_top, coe_pos, inv_pos_of_pos_ne_top, inv_strictAntiOn, inv_top, ne_bot_of_gt, ne_top_of_lt, not_lt_bot
-/
lemma inv_strictAntiOn : StrictAntiOn (fun (x : EReal) => x⁻¹) (Ioi 0) := by
  intro a a_0 b b_0 a_b
  push _ in _ at *
  lift a to Real using ⟨ne_top_of_lt a_b, ne_bot_of_gt a_0⟩
  match b with
  | ⊤ => exact inv_top ▸ inv_pos_of_pos_ne_top a_0 (coe_ne_top a)
  | ⊥ => exact (not_lt_bot b_0).rec
  | (b : Real) =>
    rw [← coe_inv a]; rw [← coe_inv b]; rw [EReal.coe_lt_coe_iff]
    exact _root_.inv_strictAntiOn (EReal.coe_pos.1 a_0) (EReal.coe_pos.1 b_0)
      (EReal.coe_lt_coe_iff.1 a_b)


/--
lemma `div_eq_inv_mul` / 引理 `div_eq_inv_mul`

English:
lemma div_eq_inv_mul
  given: (a b : EReal)
  statement: a / b = b⁻¹ * a
  proof: EReal.mul_comm a b⁻¹

中文:
引理 div_eq_inv_mul
  条件: (a b : E实数)
  结论: a / b = b⁻¹ * a
  证明: EReal.mul_comm a b⁻¹
-/
protected lemma div_eq_inv_mul (a b : EReal) : a / b = b⁻¹ * a := EReal.mul_comm a b⁻¹

/--
lemma `coe_div` / 引理 `coe_div`

English:
lemma coe_div
  given: (a b : Real)
  statement: (a / b : Real) = (a : EReal) / (b : EReal)
  proof: rfl

中文:
引理 coe_div
  条件: (a b : 实数)
  结论: (a / b : 实数) = (a : E实数) / (b : E实数)
  证明: rfl
-/
lemma coe_div (a b : Real) : (a / b : Real) = (a : EReal) / (b : EReal) := rfl

/--
theorem `natCast_div_le` / 定理 `natCast_div_le`

English:
theorem natCast_div_le
  given: (m n : Nat)
  proof: by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_div]; rw [EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]

中文:
定理 natCast_div_le
  条件: (m n : 自然数)
  证明: by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_div]; rw [EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]

Depends on / 依赖: EReal.coe_le_coe_iff, Nat.cast_div_le, cast_div_le, coe_coe_eq_natCast, coe_div, coe_le_coe_iff
-/
theorem natCast_div_le (m n : Nat) :
    (m / n : Nat) <= (m : EReal) / (n : EReal) := by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_div]; rw [EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]
/--
lemma `div_bot` / 引理 `div_bot`

English:
lemma div_bot
  given: {a : EReal}
  statement: a / ⊥ = 0
  proof: inv_bot ▸ mul_zero a

@[simp]

中文:
引理 div_bot
  条件: {a : E实数}
  结论: a / ⊥ = 0
  证明: inv_bot ▸ mul_zero a

@[simp]

Depends on / 依赖: inv_bot, mul_zero
-/
lemma div_bot {a : EReal} : a / ⊥ = 0 := inv_bot ▸ mul_zero a

@[simp]
/--
lemma `div_top` / 引理 `div_top`

English:
lemma div_top
  given: {a : EReal}
  statement: a / ⊤ = 0
  proof: inv_top ▸ mul_zero a

@[simp]

中文:
引理 div_top
  条件: {a : E实数}
  结论: a / ⊤ = 0
  证明: inv_top ▸ mul_zero a

@[simp]

Depends on / 依赖: inv_top, mul_zero
-/
lemma div_top {a : EReal} : a / ⊤ = 0 := inv_top ▸ mul_zero a

@[simp]
/--
lemma `div_zero` / 引理 `div_zero`

English:
lemma div_zero
  given: {a : EReal}
  statement: a / 0 = 0
  proof: by
  change a * 0⁻¹ = 0
  rw [inv_zero]; rw [mul_zero a]

@[simp]

中文:
引理 div_zero
  条件: {a : E实数}
  结论: a / 0 = 0
  证明: by
  change a * 0⁻¹ = 0
  rw [inv_zero]; rw [mul_zero a]

@[simp]

Depends on / 依赖: inv_zero, mul_zero
-/
lemma div_zero {a : EReal} : a / 0 = 0 := by
  change a * 0⁻¹ = 0
  rw [inv_zero]; rw [mul_zero a]

@[simp]
/--
lemma `zero_div` / 引理 `zero_div`

English:
lemma zero_div
  given: {a : EReal}
  statement: 0 / a = 0
  proof: zero_mul a⁻¹

中文:
引理 zero_div
  条件: {a : E实数}
  结论: 0 / a = 0
  证明: zero_mul a⁻¹

Depends on / 依赖: zero_mul
-/
lemma zero_div {a : EReal} : 0 / a = 0 := zero_mul a⁻¹

/--
lemma `top_div_of_pos_ne_top` / 引理 `top_div_of_pos_ne_top`

English:
lemma top_div_of_pos_ne_top
  given: {a : EReal} (h : 0 < a) (h' : a != ⊤)
  statement: ⊤ / a = ⊤
  proof: top_mul_of_pos (inv_pos_of_pos_ne_top h h')

中文:
引理 top_div_of_pos_ne_top
  条件: {a : E实数} (h : 0 < a) (h' : a != ⊤)
  结论: ⊤ / a = ⊤
  证明: top_mul_of_pos (inv_pos_of_pos_ne_top h h')

Depends on / 依赖: inv_pos_of_pos_ne_top, top_mul_of_pos
-/
lemma top_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : ⊤ / a = ⊤ :=
  top_mul_of_pos (inv_pos_of_pos_ne_top h h')

/--
lemma `top_div_of_neg_ne_bot` / 引理 `top_div_of_neg_ne_bot`

English:
lemma top_div_of_neg_ne_bot
  given: {a : EReal} (h : a < 0) (h' : a != ⊥)
  statement: ⊤ / a = ⊥
  proof: top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

中文:
引理 top_div_of_neg_ne_bot
  条件: {a : E实数} (h : a < 0) (h' : a != ⊥)
  结论: ⊤ / a = ⊥
  证明: top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

Depends on / 依赖: inv_neg_of_neg_ne_bot, top_mul_of_neg
-/
lemma top_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : ⊤ / a = ⊥ :=
  top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

/--
lemma `bot_div_of_pos_ne_top` / 引理 `bot_div_of_pos_ne_top`

English:
lemma bot_div_of_pos_ne_top
  given: {a : EReal} (h : 0 < a) (h' : a != ⊤)
  statement: ⊥ / a = ⊥
  proof: bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

中文:
引理 bot_div_of_pos_ne_top
  条件: {a : E实数} (h : 0 < a) (h' : a != ⊤)
  结论: ⊥ / a = ⊥
  证明: bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

Depends on / 依赖: bot_mul_of_pos, inv_pos_of_pos_ne_top
-/
lemma bot_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : ⊥ / a = ⊥ :=
  bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

/--
lemma `bot_div_of_neg_ne_bot` / 引理 `bot_div_of_neg_ne_bot`

English:
lemma bot_div_of_neg_ne_bot
  given: {a : EReal} (h : a < 0) (h' : a != ⊥)
  statement: ⊥ / a = ⊤
  proof: bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

中文:
引理 bot_div_of_neg_ne_bot
  条件: {a : E实数} (h : a < 0) (h' : a != ⊥)
  结论: ⊥ / a = ⊤
  证明: bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

Depends on / 依赖: bot_mul_of_neg, inv_neg_of_neg_ne_bot
-/
lemma bot_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : ⊥ / a = ⊤ :=
  bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')


/--
lemma `div_self` / 引理 `div_self`

English:
lemma div_self
  given: {a : EReal} (h₁ : a != ⊥) (h₂ : a != ⊤) (h₃ : a != 0)
  statement: a / a = 1
  proof: by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div]; rw [_root_.div_self (coe_ne_zero.1 h₃)]; rw [coe_one]

中文:
引理 div_self
  条件: {a : E实数} (h₁ : a != ⊥) (h₂ : a != ⊤) (h₃ : a != 0)
  结论: a / a = 1
  证明: by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div]; rw [_root_.div_self (coe_ne_zero.1 h₃)]; rw [coe_one]

Depends on / 依赖: _root_, _root_.div_self, coe_div, coe_ne_zero, coe_one, coe_toReal, div_self
-/
lemma div_self {a : EReal} (h₁ : a != ⊥) (h₂ : a != ⊤) (h₃ : a != 0) : a / a = 1 := by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div]; rw [_root_.div_self (coe_ne_zero.1 h₃)]; rw [coe_one]

/--
lemma `mul_div` / 引理 `mul_div`

English:
lemma mul_div
  given: (a b c : EReal)
  statement: a * (b / c) = (a * b) / c
  proof: by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

中文:
引理 mul_div
  条件: (a b c : E实数)
  结论: a * (b / c) = (a * b) / c
  证明: by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mul_div (a b c : EReal) : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

/--
lemma `mul_div_right` / 引理 `mul_div_right`

English:
lemma mul_div_right
  given: (a b c : EReal)
  statement: a / b * c = a * c / b
  proof: by
  rw [mul_comm]; rw [EReal.mul_div]; rw [mul_comm]

中文:
引理 mul_div_right
  条件: (a b c : E实数)
  结论: a / b * c = a * c / b
  证明: by
  rw [mul_comm]; rw [EReal.mul_div]; rw [mul_comm]

Depends on / 依赖: EReal.mul_div, mul_comm, mul_div
-/
lemma mul_div_right (a b c : EReal) : a / b * c = a * c / b := by
  rw [mul_comm]; rw [EReal.mul_div]; rw [mul_comm]

/--
lemma `mul_div_left_comm` / 引理 `mul_div_left_comm`

English:
lemma mul_div_left_comm
  given: (a b c : EReal)
  statement: a * (b / c) = b * (a / c)
  proof: by
  rw [mul_div a b c]; rw [mul_comm a b]; rw [← mul_div b a c]

中文:
引理 mul_div_left_comm
  条件: (a b c : E实数)
  结论: a * (b / c) = b * (a / c)
  证明: by
  rw [mul_div a b c]; rw [mul_comm a b]; rw [← mul_div b a c]

Depends on / 依赖: mul_comm, mul_div
-/
lemma mul_div_left_comm (a b c : EReal) : a * (b / c) = b * (a / c) := by
  rw [mul_div a b c]; rw [mul_comm a b]; rw [← mul_div b a c]

/--
lemma `div_div` / 引理 `div_div`

English:
lemma div_div
  given: (a b c : EReal)
  statement: a / b / c = a / (b * c)
  proof: by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹]; rw [mul_inv]

中文:
引理 div_div
  条件: (a b c : E实数)
  结论: a / b / c = a / (b * c)
  证明: by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹]; rw [mul_inv]

Depends on / 依赖: mul_assoc, mul_inv
-/
lemma div_div (a b c : EReal) : a / b / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹]; rw [mul_inv]

/--
lemma `div_mul_div_comm` / 引理 `div_mul_div_comm`

English:
lemma div_mul_div_comm
  given: (a b c d : EReal)
  statement: a / b * (c / d) = a * c / (b * d)
  proof: by
  rw [← mul_div a]; rw [mul_comm b d]; rw [← div_div c]; rw [← mul_div_left_comm (c / d)]; rw [mul_comm (a / b)]

中文:
引理 div_mul_div_comm
  条件: (a b c d : E实数)
  结论: a / b * (c / d) = a * c / (b * d)
  证明: by
  rw [← mul_div a]; rw [mul_comm b d]; rw [← div_div c]; rw [← mul_div_left_comm (c / d)]; rw [mul_comm (a / b)]

Depends on / 依赖: div_div, mul_comm, mul_div, mul_div_left_comm
-/
lemma div_mul_div_comm (a b c d : EReal) : a / b * (c / d) = a * c / (b * d) := by
  rw [← mul_div a]; rw [mul_comm b d]; rw [← div_div c]; rw [← mul_div_left_comm (c / d)]; rw [mul_comm (a / b)]

variable {a b c : EReal}

/--
lemma `div_mul_cancel` / 引理 `div_mul_cancel`

English:
lemma div_mul_cancel
  given: (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0)
  statement: a / b * b = a
  proof: by
  rw [mul_comm (a / b) b]; rw [← mul_div_left_comm a b b]; rw [div_self h₁ h₂ h₃]; rw [mul_one]

中文:
引理 div_mul_cancel
  条件: (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0)
  结论: a / b * b = a
  证明: by
  rw [mul_comm (a / b) b]; rw [← mul_div_left_comm a b b]; rw [div_self h₁ h₂ h₃]; rw [mul_one]

Depends on / 依赖: div_self, mul_comm, mul_div_left_comm, mul_one
-/
lemma div_mul_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0) : a / b * b = a := by
  rw [mul_comm (a / b) b]; rw [← mul_div_left_comm a b b]; rw [div_self h₁ h₂ h₃]; rw [mul_one]

/--
lemma `mul_div_cancel` / 引理 `mul_div_cancel`

English:
lemma mul_div_cancel
  given: (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0)
  statement: b * (a / b) = a
  proof: by
  rw [mul_comm]; rw [div_mul_cancel h₁ h₂ h₃]

中文:
引理 mul_div_cancel
  条件: (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0)
  结论: b * (a / b) = a
  证明: by
  rw [mul_comm]; rw [div_mul_cancel h₁ h₂ h₃]

Depends on / 依赖: div_mul_cancel, mul_comm
-/
lemma mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0) : b * (a / b) = a := by
  rw [mul_comm]; rw [div_mul_cancel h₁ h₂ h₃]

/--
lemma `mul_div_mul_cancel` / 引理 `mul_div_mul_cancel`

English:
lemma mul_div_mul_cancel
  given: (h₁ : c != ⊥) (h₂ : c != ⊤) (h₃ : c != 0)
  statement: a * c / (b * c) = a / b
  proof: by
  rw [← mul_div_right a (b * c) c]; rw [← div_div a b c]; rw [div_mul_cancel h₁ h₂ h₃]

中文:
引理 mul_div_mul_cancel
  条件: (h₁ : c != ⊥) (h₂ : c != ⊤) (h₃ : c != 0)
  结论: a * c / (b * c) = a / b
  证明: by
  rw [← mul_div_right a (b * c) c]; rw [← div_div a b c]; rw [div_mul_cancel h₁ h₂ h₃]

Depends on / 依赖: div_div, div_mul_cancel, mul_div_right
-/
lemma mul_div_mul_cancel (h₁ : c != ⊥) (h₂ : c != ⊤) (h₃ : c != 0) : a * c / (b * c) = a / b := by
  rw [← mul_div_right a (b * c) c]; rw [← div_div a b c]; rw [div_mul_cancel h₁ h₂ h₃]

/--
lemma `div_eq_iff` / 引理 `div_eq_iff`

English:
lemma div_eq_iff
  given: (hbot : b != ⊥) (htop : b != ⊤) (hzero : b != 0)
  statement: c / b = a ↔ c = a * b
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← @mul_div_cancel c b hbot htop hzero, h, mul_comm a b]
  · rw [h, mul_comm a b, ← mul_div b a b, @mul_div_cancel a b hbot htop hzero]

中文:
引理 div_eq_iff
  条件: (hbot : b != ⊥) (htop : b != ⊤) (hzero : b != 0)
  结论: c / b = a ↔ c = a * b
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← @mul_div_cancel c b hbot htop hzero, h, mul_comm a b]
  · rw [h, mul_comm a b, ← mul_div b a b, @mul_div_cancel a b hbot htop hzero]

Depends on / 依赖: mul_comm, mul_div, mul_div_cancel
-/
lemma div_eq_iff (hbot : b != ⊥) (htop : b != ⊤) (hzero : b != 0) : c / b = a ↔ c = a * b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← @mul_div_cancel c b hbot htop hzero, h, mul_comm a b]
  · rw [h, mul_comm a b, ← mul_div b a b, @mul_div_cancel a b hbot htop hzero]


/--
lemma `monotone_div_right_of_nonneg` / 引理 `monotone_div_right_of_nonneg`

English:
lemma monotone_div_right_of_nonneg
  given: (h : 0 <= b)
  statement: Monotone fun a => a / b
  proof: fun _ _ h' => mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

@[gcongr]

中文:
引理 monotone_div_right_of_nonneg
  条件: (h : 0 <= b)
  结论: 递增 fun a => a / b
  证明: fun _ _ h' => mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

@[gcongr]

Depends on / 依赖: inv_nonneg_of_nonneg, mul_le_mul_of_nonneg_right
-/
lemma monotone_div_right_of_nonneg (h : 0 <= b) : Monotone fun a => a / b :=
  fun _ _ h' => mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

@[gcongr]
/--
lemma `div_le_div_right_of_nonneg` / 引理 `div_le_div_right_of_nonneg`

English:
lemma div_le_div_right_of_nonneg
  given: (h : 0 <= c) (h' : a <= b)
  statement: a / c <= b / c
  proof: monotone_div_right_of_nonneg h h'

中文:
引理 div_le_div_right_of_nonneg
  条件: (h : 0 <= c) (h' : a <= b)
  结论: a / c <= b / c
  证明: monotone_div_right_of_nonneg h h'

Depends on / 依赖: monotone_div_right_of_nonneg
-/
lemma div_le_div_right_of_nonneg (h : 0 <= c) (h' : a <= b) : a / c <= b / c :=
  monotone_div_right_of_nonneg h h'

/--
lemma `strictMono_div_right_of_pos` / 引理 `strictMono_div_right_of_pos`

English:
lemma strictMono_div_right_of_pos
  given: (h : 0 < b) (h' : b != ⊤)
  statement: StrictMono fun a => a / b
  proof: by
  intro a a' a_lt_a'
apply lt_of_le_of_ne div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']; rw [hyp]; rw [@EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' h.ne']

@[gcongr]

中文:
引理 strictMono_div_right_of_pos
  条件: (h : 0 < b) (h' : b != ⊤)
  结论: 严格递增 fun a => a / b
  证明: by
  intro a a' a_lt_a'
apply lt_of_le_of_ne div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']; rw [hyp]; rw [@EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' h.ne']

@[gcongr]

Depends on / 依赖: EReal.mul_div_cancel, a_lt_a, div_le_div_right_of_nonneg, h.ne, le_of_lt, lt_of_le_of_ne, mul_div_cancel, ne_bot_of_gt, ne_of_lt
-/
lemma strictMono_div_right_of_pos (h : 0 < b) (h' : b != ⊤) : StrictMono fun a => a / b := by
  intro a a' a_lt_a'
apply lt_of_le_of_ne div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']; rw [hyp]; rw [@EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' h.ne']

@[gcongr]
/--
lemma `div_lt_div_right_of_pos` / 引理 `div_lt_div_right_of_pos`

English:
lemma div_lt_div_right_of_pos
  given: (h₁ : 0 < c) (h₂ : c != ⊤) (h₃ : a < b)
  statement: a / c < b / c
  proof: strictMono_div_right_of_pos h₁ h₂ h₃

中文:
引理 div_lt_div_right_of_pos
  条件: (h₁ : 0 < c) (h₂ : c != ⊤) (h₃ : a < b)
  结论: a / c < b / c
  证明: strictMono_div_right_of_pos h₁ h₂ h₃

Depends on / 依赖: strictMono_div_right_of_pos
-/
lemma div_lt_div_right_of_pos (h₁ : 0 < c) (h₂ : c != ⊤) (h₃ : a < b) : a / c < b / c :=
  strictMono_div_right_of_pos h₁ h₂ h₃

/--
lemma `antitone_div_right_of_nonpos` / 引理 `antitone_div_right_of_nonpos`

English:
lemma antitone_div_right_of_nonpos
  given: (h : b <= 0)
  statement: Antitone fun a => a / b
  proof: by
  intro a a' h'
  change a' * b⁻¹ <= a * b⁻¹
  rw [← neg_neg (a * b⁻¹)]; rw [← neg_neg (a' * b⁻¹)]; rw [neg_le_neg_iff]; rw [mul_comm a b⁻¹]; rw [mul_comm a' b⁻¹]; rw [← neg_mul b⁻¹ a]; rw [← neg_mul b⁻¹ a']; rw [mul_comm (-b⁻¹) a]; rw [mul_comm (-b⁻¹) a']; rw [← inv_neg b]
  have : 0 <= -b := by apply EReal.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'

中文:
引理 antitone_div_right_of_nonpos
  条件: (h : b <= 0)
  结论: 递减 fun a => a / b
  证明: by
  intro a a' h'
  change a' * b⁻¹ <= a * b⁻¹
  rw [← neg_neg (a * b⁻¹)]; rw [← neg_neg (a' * b⁻¹)]; rw [neg_le_neg_iff]; rw [mul_comm a b⁻¹]; rw [mul_comm a' b⁻¹]; rw [← neg_mul b⁻¹ a]; rw [← neg_mul b⁻¹ a']; rw [mul_comm (-b⁻¹) a]; rw [mul_comm (-b⁻¹) a']; rw [← inv_neg b]
  have : 0 <= -b := by apply EReal.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'

Depends on / 依赖: EReal.le_neg_of_le_neg, div_le_div_right_of_nonneg, inv_neg, le_neg_of_le_neg, mul_comm, neg_le_neg_iff, neg_mul, neg_neg
-/
lemma antitone_div_right_of_nonpos (h : b <= 0) : Antitone fun a => a / b := by
  intro a a' h'
  change a' * b⁻¹ <= a * b⁻¹
  rw [← neg_neg (a * b⁻¹)]; rw [← neg_neg (a' * b⁻¹)]; rw [neg_le_neg_iff]; rw [mul_comm a b⁻¹]; rw [mul_comm a' b⁻¹]; rw [← neg_mul b⁻¹ a]; rw [← neg_mul b⁻¹ a']; rw [mul_comm (-b⁻¹) a]; rw [mul_comm (-b⁻¹) a']; rw [← inv_neg b]
  have : 0 <= -b := by apply EReal.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'

/--
lemma `div_le_div_right_of_nonpos` / 引理 `div_le_div_right_of_nonpos`

English:
lemma div_le_div_right_of_nonpos
  given: (h : c <= 0) (h' : a <= b)
  statement: b / c <= a / c
  proof: antitone_div_right_of_nonpos h h'

中文:
引理 div_le_div_right_of_nonpos
  条件: (h : c <= 0) (h' : a <= b)
  结论: b / c <= a / c
  证明: antitone_div_right_of_nonpos h h'

Depends on / 依赖: antitone_div_right_of_nonpos
-/
lemma div_le_div_right_of_nonpos (h : c <= 0) (h' : a <= b) : b / c <= a / c :=
  antitone_div_right_of_nonpos h h'

/--
lemma `strictAnti_div_right_of_neg` / 引理 `strictAnti_div_right_of_neg`

English:
lemma strictAnti_div_right_of_neg
  given: (h : b < 0) (h' : b != ⊥)
  statement: StrictAnti fun a => a / b
  proof: by
  intro a a' a_lt_a'
  simp only
apply lt_of_le_of_ne div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h)]; rw [← hyp]; rw [@EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

中文:
引理 strictAnti_div_right_of_neg
  条件: (h : b < 0) (h' : b != ⊥)
  结论: 严格递减 fun a => a / b
  证明: by
  intro a a' a_lt_a'
  simp only
apply lt_of_le_of_ne div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h)]; rw [← hyp]; rw [@EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

Depends on / 依赖: EReal.mul_div_cancel, a_lt_a, div_le_div_right_of_nonpos, le_of_lt, lt_of_le_of_ne, mul_div_cancel, ne_of_lt, ne_top_of_lt
-/
lemma strictAnti_div_right_of_neg (h : b < 0) (h' : b != ⊥) : StrictAnti fun a => a / b := by
  intro a a' a_lt_a'
  simp only
apply lt_of_le_of_ne div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h)]; rw [← hyp]; rw [@EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

/--
lemma `div_lt_div_right_of_neg` / 引理 `div_lt_div_right_of_neg`

English:
lemma div_lt_div_right_of_neg
  given: (h₁ : c < 0) (h₂ : c != ⊥) (h₃ : a < b)
  statement: b / c < a / c
  proof: strictAnti_div_right_of_neg h₁ h₂ h₃

中文:
引理 div_lt_div_right_of_neg
  条件: (h₁ : c < 0) (h₂ : c != ⊥) (h₃ : a < b)
  结论: b / c < a / c
  证明: strictAnti_div_right_of_neg h₁ h₂ h₃

Depends on / 依赖: strictAnti_div_right_of_neg
-/
lemma div_lt_div_right_of_neg (h₁ : c < 0) (h₂ : c != ⊥) (h₃ : a < b) : b / c < a / c :=
  strictAnti_div_right_of_neg h₁ h₂ h₃

/--
lemma `le_div_iff_mul_le` / 引理 `le_div_iff_mul_le`

English:
lemma le_div_iff_mul_le
  given: (h : b > 0) (h' : b != ⊤)
  statement: a <= c / b ↔ a * b <= c
  proof: by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b a b]; rw [mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

中文:
引理 le_div_iff_mul_le
  条件: (h : b > 0) (h' : b != ⊤)
  结论: a <= c / b ↔ a * b <= c
  证明: by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b a b]; rw [mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

Depends on / 依赖: StrictMono, StrictMono.le_iff_le, h.ne, le_iff_le, mul_comm, mul_div, mul_div_cancel, ne_bot_of_gt, nth_rw, strictMono_div_right_of_pos
-/
lemma le_div_iff_mul_le (h : b > 0) (h' : b != ⊤) : a <= c / b ↔ a * b <= c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b a b]; rw [mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

/--
lemma `div_le_iff_le_mul` / 引理 `div_le_iff_le_mul`

English:
lemma div_le_iff_le_mul
  given: (h : 0 < b) (h' : b != ⊤)
  statement: a / b <= c ↔ a <= b * c
  proof: by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b c b]; rw [mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

中文:
引理 div_le_iff_le_mul
  条件: (h : 0 < b) (h' : b != ⊤)
  结论: a / b <= c ↔ a <= b * c
  证明: by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b c b]; rw [mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

Depends on / 依赖: StrictMono, StrictMono.le_iff_le, h.ne, le_iff_le, mul_comm, mul_div, mul_div_cancel, ne_bot_of_gt, nth_rw, strictMono_div_right_of_pos
-/
lemma div_le_iff_le_mul (h : 0 < b) (h' : b != ⊤) : a / b <= c ↔ a <= b * c := by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b c b]; rw [mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

/--
lemma `lt_div_iff` / 引理 `lt_div_iff`

English:
lemma lt_div_iff
  given: (h : 0 < b) (h' : b != ⊤)
  statement: a < c / b ↔ a * b < c
  proof: by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div b a b]; rw [mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

中文:
引理 lt_div_iff
  条件: (h : 0 < b) (h' : b != ⊤)
  结论: a < c / b ↔ a * b < c
  证明: by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div b a b]; rw [mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

Depends on / 依赖: EReal.mul_div, h.ne, lt_iff_lt, mul_comm, mul_div, mul_div_cancel, ne_bot_of_gt, nth_rw, strictMono_div_right_of_pos
-/
lemma lt_div_iff (h : 0 < b) (h' : b != ⊤) : a < c / b ↔ a * b < c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div b a b]; rw [mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

/--
lemma `div_lt_iff` / 引理 `div_lt_iff`

English:
lemma div_lt_iff
  given: (h : 0 < c) (h' : c != ⊤)
  statement: b / c < a ↔ b < a * c
  proof: by
  nth_rw 1 [← @mul_div_cancel a c (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div c a c]; rw [mul_comm a c]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

中文:
引理 div_lt_iff
  条件: (h : 0 < c) (h' : c != ⊤)
  结论: b / c < a ↔ b < a * c
  证明: by
  nth_rw 1 [← @mul_div_cancel a c (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div c a c]; rw [mul_comm a c]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

Depends on / 依赖: EReal.mul_div, h.ne, lt_iff_lt, mul_comm, mul_div, mul_div_cancel, ne_bot_of_gt, nth_rw, strictMono_div_right_of_pos
-/
lemma div_lt_iff (h : 0 < c) (h' : c != ⊤) : b / c < a ↔ b < a * c := by
  nth_rw 1 [← @mul_div_cancel a c (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div c a c]; rw [mul_comm a c]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

/--
lemma `div_nonneg` / 引理 `div_nonneg`

English:
lemma div_nonneg
  given: (h : 0 <= a) (h' : 0 <= b)
  statement: 0 <= a / b
  proof: mul_nonneg h (inv_nonneg_of_nonneg h')

中文:
引理 div_nonneg
  条件: (h : 0 <= a) (h' : 0 <= b)
  结论: 0 <= a / b
  证明: mul_nonneg h (inv_nonneg_of_nonneg h')

Depends on / 依赖: inv_nonneg_of_nonneg, mul_nonneg
-/
lemma div_nonneg (h : 0 <= a) (h' : 0 <= b) : 0 <= a / b :=
  mul_nonneg h (inv_nonneg_of_nonneg h')

/--
lemma `div_pos` / 引理 `div_pos`

English:
lemma div_pos
  given: (ha : 0 < a) (hb : 0 < b) (hb' : b != ⊤)
  statement: 0 < a / b
  proof: EReal.mul_pos ha (inv_pos_of_pos_ne_top hb hb')

中文:
引理 div_pos
  条件: (ha : 0 < a) (hb : 0 < b) (hb' : b != ⊤)
  结论: 0 < a / b
  证明: EReal.mul_pos ha (inv_pos_of_pos_ne_top hb hb')

Depends on / 依赖: EReal.mul_pos, inv_pos_of_pos_ne_top, mul_pos
-/
lemma div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b != ⊤) : 0 < a / b :=
  EReal.mul_pos ha (inv_pos_of_pos_ne_top hb hb')

/--
lemma `div_nonpos_of_nonpos_of_nonneg` / 引理 `div_nonpos_of_nonpos_of_nonneg`

English:
lemma div_nonpos_of_nonpos_of_nonneg
  given: (h : a <= 0) (h' : 0 <= b)
  statement: a / b <= 0
  proof: mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

中文:
引理 div_nonpos_of_nonpos_of_nonneg
  条件: (h : a <= 0) (h' : 0 <= b)
  结论: a / b <= 0
  证明: mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

Depends on / 依赖: inv_nonneg_of_nonneg, mul_nonpos_of_nonpos_of_nonneg
-/
lemma div_nonpos_of_nonpos_of_nonneg (h : a <= 0) (h' : 0 <= b) : a / b <= 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

/--
lemma `div_nonpos_of_nonneg_of_nonpos` / 引理 `div_nonpos_of_nonneg_of_nonpos`

English:
lemma div_nonpos_of_nonneg_of_nonpos
  given: (h : 0 <= a) (h' : b <= 0)
  statement: a / b <= 0
  proof: mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

中文:
引理 div_nonpos_of_nonneg_of_nonpos
  条件: (h : 0 <= a) (h' : b <= 0)
  结论: a / b <= 0
  证明: mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

Depends on / 依赖: inv_nonpos_of_nonpos, mul_nonpos_of_nonneg_of_nonpos
-/
lemma div_nonpos_of_nonneg_of_nonpos (h : 0 <= a) (h' : b <= 0) : a / b <= 0 :=
  mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

/--
lemma `div_nonneg_of_nonpos_of_nonpos` / 引理 `div_nonneg_of_nonpos_of_nonpos`

English:
lemma div_nonneg_of_nonpos_of_nonpos
  given: (h : a <= 0) (h' : b <= 0)
  statement: 0 <= a / b
  proof: le_of_eq_of_le zero_div.symm (div_le_div_right_of_nonpos h' h)

中文:
引理 div_nonneg_of_nonpos_of_nonpos
  条件: (h : a <= 0) (h' : b <= 0)
  结论: 0 <= a / b
  证明: le_of_eq_of_le zero_div.symm (div_le_div_right_of_nonpos h' h)

Depends on / 依赖: div_le_div_right_of_nonpos, le_of_eq_of_le, zero_div, zero_div.symm
-/
lemma div_nonneg_of_nonpos_of_nonpos (h : a <= 0) (h' : b <= 0) : 0 <= a / b :=
  le_of_eq_of_le zero_div.symm (div_le_div_right_of_nonpos h' h)

/--
lemma `exists_lt_mul_left_of_nonneg` / 引理 `exists_lt_mul_left_of_nonneg`

English:
lemma exists_lt_mul_left_of_nonneg
  given: (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  proof: by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩

中文:
引理 存在_lt_mul_left_of_nonneg
  条件: (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  证明: by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩
-/
private lemma exists_lt_mul_left_of_nonneg (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b) :
    exists a' in Ioo 0 a, c < a' * b := by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩

/--
lemma `exists_lt_mul_right_of_nonneg` / 引理 `exists_lt_mul_right_of_nonneg`

English:
lemma exists_lt_mul_right_of_nonneg
  given: (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  proof: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

中文:
引理 存在_lt_mul_right_of_nonneg
  条件: (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b)
  证明: by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h
-/
private lemma exists_lt_mul_right_of_nonneg (ha : 0 <= a) (hc : 0 <= c) (h : c < a * b) :
    exists b' in Ioo 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

/--
lemma `exists_mul_left_lt` / 引理 `exists_mul_left_lt`

English:
lemma exists_mul_left_lt
  given: (h₁ : a != 0 ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b) (hc : a * b < c)
  proof: by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩

中文:
引理 存在_mul_left_lt
  条件: (h₁ : a != 0 ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b) (hc : a * b < c)
  证明: by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩
-/
private lemma exists_mul_left_lt (h₁ : a != 0 ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b) (hc : a * b < c) :
    exists a' in Ioo a ⊤, a' * b < c := by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩

/--
lemma `exists_mul_right_lt` / 引理 `exists_mul_right_lt`

English:
lemma exists_mul_right_lt
  given: (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != 0) (hc : a * b < c)
  proof: by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc

中文:
引理 存在_mul_right_lt
  条件: (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != 0) (hc : a * b < c)
  证明: by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc
-/
private lemma exists_mul_right_lt (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != 0) (hc : a * b < c) :
    exists b' in Ioo b ⊤, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc

/--
lemma `le_mul_of_forall_lt` / 引理 `le_mul_of_forall_lt`

English:
lemma le_mul_of_forall_lt
  statement: (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b)
  proof: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b != ⊤ := h₁.imp_left fun a0 => a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' != ⊤ ∨ b != 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le

中文:
引理 le_mul_of_对任意_lt
  结论: (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b)
  证明: by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b != ⊤ := h₁.imp_left fun a0 => a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' != ⊤ ∨ b != 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le

Depends on / 依赖: Or.inl, a0.trans, exists_mul_left_lt, exists_mul_right_lt, hd.le, imp_left, le_of_forall_gt_imp_ge_of_dense, mem_Ioo, ne_of_gt, replace
-/
lemma le_mul_of_forall_lt (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b)
    (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b != ⊤ := h₁.imp_left fun a0 => a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' != ⊤ ∨ b != 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le

/--
lemma `mul_le_of_forall_lt_of_nonneg` / 引理 `mul_le_of_forall_lt_of_nonneg`

English:
lemma mul_le_of_forall_lt_of_nonneg
  statement: (ha : 0 <= a) (hc : 0 <= c)
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun d dab => ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')

中文:
引理 mul_le_of_对任意_lt_of_nonneg
  结论: (ha : 0 <= a) (hc : 0 <= c)
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun d dab => ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')

Depends on / 依赖: d0.le.trans, dab.le.trans, exists_lt_mul_left_of_nonneg, exists_lt_mul_right_of_nonneg, le_of_forall_lt_imp_le_of_dense, lt_or_ge
-/
lemma mul_le_of_forall_lt_of_nonneg (ha : 0 <= a) (hc : 0 <= c)
    (h : forall a' in Ioo 0 a, forall b' in Ioo 0 b, a' * b' <= c) : a * b <= c := by
  refine le_of_forall_lt_imp_le_of_dense fun d dab => ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')


/--
lemma `div_right_distrib_of_nonneg` / 引理 `div_right_distrib_of_nonneg`

English:
lemma div_right_distrib_of_nonneg
  given: (h : 0 <= a) (h' : 0 <= b)
  proof: EReal.right_distrib_of_nonneg h h'

中文:
引理 div_right_distrib_of_nonneg
  条件: (h : 0 <= a) (h' : 0 <= b)
  证明: EReal.right_distrib_of_nonneg h h'

Depends on / 依赖: EReal.right_distrib_of_nonneg, right_distrib_of_nonneg
-/
lemma div_right_distrib_of_nonneg (h : 0 <= a) (h' : 0 <= b) :
    (a + b) / c = a / c + b / c :=
  EReal.right_distrib_of_nonneg h h'

/--
lemma `add_div_of_nonneg_right` / 引理 `add_div_of_nonneg_right`

English:
lemma add_div_of_nonneg_right
  given: (h : 0 <= c)
  proof: by
  apply right_distrib_of_nonneg_of_ne_top (inv_nonneg_of_nonneg h) (inv_lt_top c).ne

中文:
引理 add_div_of_nonneg_right
  条件: (h : 0 <= c)
  证明: by
  apply right_distrib_of_nonneg_of_ne_top (inv_nonneg_of_nonneg h) (inv_lt_top c).ne

Depends on / 依赖: inv_lt_top, inv_nonneg_of_nonneg, right_distrib_of_nonneg_of_ne_top
-/
lemma add_div_of_nonneg_right (h : 0 <= c) :
    (a + b) / c = a / c + b / c := by
  apply right_distrib_of_nonneg_of_ne_top (inv_nonneg_of_nonneg h) (inv_lt_top c).ne

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: inverse of an `EReal`. -/
@[positivity (_⁻¹ : EReal)]
meta def evalERealInv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a⁻¹) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa => pure (.nonnegative q(EReal.inv_nonneg_of_nonneg <| $pa))
    | none => pure .none
  | _, _, _ => throwError "not an inverse of an `EReal`"

/-- Extension for the `positivity` tactic: ratio of two `EReal`s. -/
@[positivity (_ / _ : EReal)]
meta def evalERealDiv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a / $b) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(EReal.div_nonneg $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a ratio of 2 `EReal`s"

end Mathlib.Meta.Positivity
