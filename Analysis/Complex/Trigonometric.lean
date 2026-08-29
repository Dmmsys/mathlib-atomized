/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

@[expose] public section

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

noncomputable section

/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
/--
Definition of `sin` / `sin` 的定义

English:
definition sin
  signature: (z : Complex)
  body: (exp (-z * I) - exp (z * I)) * I / 2

中文:
定义 sin
  签名: (z : Complex)
  定义体: (exp (-z * I) - exp (z * I)) * I / 2
-/
def sin (z : Complex) : Complex :=
  (exp (-z * I) - exp (z * I)) * I / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
/--
Definition of `cos` / `cos` 的定义

English:
definition cos
  signature: (z : Complex)
  body: (exp (z * I) + exp (-z * I)) / 2

中文:
定义 cos
  签名: (z : Complex)
  定义体: (exp (z * I) + exp (-z * I)) / 2
-/
def cos (z : Complex) : Complex :=
  (exp (z * I) + exp (-z * I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
/--
Definition of `tan` / `tan` 的定义

English:
definition tan
  signature: (z : Complex)
  body: sin z / cos z

中文:
定义 tan
  签名: (z : Complex)
  定义体: sin z / cos z
-/
def tan (z : Complex) : Complex :=
  sin z / cos z

/--
Definition of `cot` / `cot` 的定义

English:
definition cot
  signature: (z : Complex)
  body: cos z / sin z

中文:
定义 cot
  签名: (z : Complex)
  定义体: cos z / sin z
-/
def cot (z : Complex) : Complex :=
  cos z / sin z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
/--
Definition of `sinh` / `sinh` 的定义

English:
definition sinh
  signature: (z : Complex)
  body: (exp z - exp (-z)) / 2

中文:
定义 sinh
  签名: (z : Complex)
  定义体: (exp z - exp (-z)) / 2
-/
def sinh (z : Complex) : Complex :=
  (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
/--
Definition of `cosh` / `cosh` 的定义

English:
definition cosh
  signature: (z : Complex)
  body: (exp z + exp (-z)) / 2

中文:
定义 cosh
  签名: (z : Complex)
  定义体: (exp z + exp (-z)) / 2
-/
def cosh (z : Complex) : Complex :=
  (exp z + exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
/--
Definition of `tanh` / `tanh` 的定义

English:
definition tanh
  signature: (z : Complex)
  body: sinh z / cosh z

中文:
定义 tanh
  签名: (z : Complex)
  定义体: sinh z / cosh z
-/
def tanh (z : Complex) : Complex :=
  sinh z / cosh z

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : Real) : Real :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : Real) : Real :=
  (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
nonrec def tan (x : Real) : Real :=
  (tan x).re

/-- The real cotangent function, defined as the real part of the complex cotangent -/
nonrec def cot (x : Real) : Real :=
  (cot x).re

/-- The real hyperbolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
nonrec def sinh (x : Real) : Real :=
  (sinh x).re

/-- The real hyperbolic cosine function, defined as the real part of the complex hyperbolic cosine
-/
@[pp_nodot]
nonrec def cosh (x : Real) : Real :=
  (cosh x).re

/-- The real hyperbolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
nonrec def tanh (x : Real) : Real :=
  (tanh x).re

end

end Real

namespace Complex

variable (x y : Complex)

/--
theorem `two_sinh` / 定理 `two_sinh`

English:
theorem two_sinh
  statement: 2 * sinh x = exp x - exp (-x)
  proof: mul_div_cancel₀ _ two_ne_zero

中文:
定理 two_sinh
  结论: 2 * sinh x = exp x - exp (-x)
  证明: mul_div_cancel₀ _ two_ne_zero

Depends on / 依赖: two_ne_zero
-/
theorem two_sinh : 2 * sinh x = exp x - exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

/--
theorem `two_cosh` / 定理 `two_cosh`

English:
theorem two_cosh
  statement: 2 * cosh x = exp x + exp (-x)
  proof: mul_div_cancel₀ _ two_ne_zero

@[simp]

中文:
定理 two_cosh
  结论: 2 * cosh x = exp x + exp (-x)
  证明: mul_div_cancel₀ _ two_ne_zero

@[simp]

Depends on / 依赖: two_ne_zero
-/
theorem two_cosh : 2 * cosh x = exp x + exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

@[simp]
/--
theorem `sinh_zero` / 定理 `sinh_zero`

English:
theorem sinh_zero
  statement: sinh 0 = 0
  proof: by simp [sinh]

@[simp]

中文:
定理 sinh_zero
  结论: sinh 0 = 0
  证明: by simp [sinh]

@[simp]
-/
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
/--
theorem `sinh_neg` / 定理 `sinh_neg`

English:
theorem sinh_neg
  statement: sinh (-x) = -sinh x
  proof: by simp [sinh, exp_neg, (neg_div _ _).symm]

中文:
定理 sinh_neg
  结论: sinh (-x) = -sinh x
  证明: by simp [sinh, exp_neg, (neg_div _ _).symm]

Depends on / 依赖: exp_neg, neg_div
-/
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm]

/--
theorem `sinh_add_aux` / 定理 `sinh_add_aux`

English:
theorem sinh_add_aux
  given: {a b c d : Complex}
  proof: by ring

中文:
定理 sinh_add_aux
  条件: {a b c d : Complex}
  证明: by ring
-/
private theorem sinh_add_aux {a b c d : Complex} :
    (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

/--
theorem `sinh_add` / 定理 `sinh_add`

English:
theorem sinh_add
  statement: sinh (x + y) = sinh x * cosh y + cosh x * sinh y
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_sinh]; rw [mul_left_comm]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh

中文:
定理 sinh_add
  结论: sinh (x + y) = sinh x * cosh y + cosh x * sinh y
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_sinh]; rw [mul_left_comm]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh

Depends on / 依赖: eq_comm, exp_add, mul_add, mul_assoc, mul_left_comm, mul_right_inj, neg_add, sinh_add_aux, two_cosh, two_ne_zero, two_sinh
-/
theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_sinh]; rw [mul_left_comm]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh]; rw [← mul_assoc]; rw [two_cosh]
  exact sinh_add_aux

@[simp]
/--
theorem `cosh_zero` / 定理 `cosh_zero`

English:
theorem cosh_zero
  statement: cosh 0 = 1
  proof: by simp [cosh]

@[simp]

中文:
定理 cosh_zero
  结论: cosh 0 = 1
  证明: by simp [cosh]

@[simp]
-/
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
/--
theorem `cosh_neg` / 定理 `cosh_neg`

English:
theorem cosh_neg
  statement: cosh (-x) = cosh x
  proof: by simp [add_comm, cosh, exp_neg]

中文:
定理 cosh_neg
  结论: cosh (-x) = cosh x
  证明: by simp [add_comm, cosh, exp_neg]

Depends on / 依赖: add_comm, exp_neg
-/
theorem cosh_neg : cosh (-x) = cosh x := by simp [add_comm, cosh, exp_neg]

/--
theorem `cosh_add_aux` / 定理 `cosh_add_aux`

English:
theorem cosh_add_aux
  given: {a b c d : Complex}
  proof: by ring

中文:
定理 cosh_add_aux
  条件: {a b c d : Complex}
  证明: by ring
-/
private theorem cosh_add_aux {a b c d : Complex} :
    (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

/--
theorem `cosh_add` / 定理 `cosh_add`

English:
theorem cosh_add
  statement: cosh (x + y) = cosh x * cosh y + sinh x * sinh y
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_cosh]; rw [← mul_assoc]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh];

中文:
定理 cosh_add
  结论: cosh (x + y) = cosh x * cosh y + sinh x * sinh y
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_cosh]; rw [← mul_assoc]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh];

Depends on / 依赖: cosh_add_aux, eq_comm, exp_add, mul_add, mul_assoc, mul_left_comm, mul_right_inj, neg_add, two_cosh, two_ne_zero, two_sinh
-/
theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [exp_add]; rw [neg_add]; rw [exp_add]; rw [eq_comm]; rw [mul_add]; rw [←
    mul_assoc]; rw [two_cosh]; rw [← mul_assoc]; rw [two_sinh]; rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [mul_left_comm]; rw [two_cosh]; rw [mul_left_comm]; rw [two_sinh]
  exact cosh_add_aux

/--
theorem `sinh_sub` / 定理 `sinh_sub`

English:
theorem sinh_sub
  statement: sinh (x - y) = sinh x * cosh y - cosh x * sinh y
  proof: by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

中文:
定理 sinh_sub
  结论: sinh (x - y) = sinh x * cosh y - cosh x * sinh y
  证明: by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

Depends on / 依赖: cosh_neg, sinh_add, sinh_neg, sub_eq_add_neg
-/
theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

/--
theorem `cosh_sub` / 定理 `cosh_sub`

English:
theorem cosh_sub
  statement: cosh (x - y) = cosh x * cosh y - sinh x * sinh y
  proof: by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

中文:
定理 cosh_sub
  结论: cosh (x - y) = cosh x * cosh y - sinh x * sinh y
  证明: by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

Depends on / 依赖: cosh_add, cosh_neg, sinh_neg, sub_eq_add_neg
-/
theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

/--
theorem `sinh_conj` / 定理 `sinh_conj`

English:
theorem sinh_conj
  statement: sinh (conj x) = conj (sinh x)
  proof: by
  rw [sinh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_sub]; rw [sinh]; rw [map_div₀]; rw [map_ofNat]

@[simp]

中文:
定理 sinh_conj
  结论: sinh (conj x) = conj (sinh x)
  证明: by
  rw [sinh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_sub]; rw [sinh]; rw [map_div₀]; rw [map_ofNat]

@[simp]

Depends on / 依赖: exp_conj, map_neg, map_ofNat, map_sub
-/
theorem sinh_conj : sinh (conj x) = conj (sinh x) := by
  rw [sinh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_sub]; rw [sinh]; rw [map_div₀]; rw [map_ofNat]

@[simp]
/--
theorem `ofReal_sinh_ofReal_re` / 定理 `ofReal_sinh_ofReal_re`

English:
theorem ofReal_sinh_ofReal_re
  given: (x : Real)
  statement: ((sinh x).re : Complex) = sinh x
  proof: conj_eq_iff_re.1 by rw [← sinh_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_sinh_ofReal_re
  条件: (x : 实数)
  结论: ((sinh x).re : Complex) = sinh x
  证明: conj_eq_iff_re.1 by rw [← sinh_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, sinh_conj
-/
theorem ofReal_sinh_ofReal_re (x : Real) : ((sinh x).re : Complex) = sinh x :=
conj_eq_iff_re.1 by rw [← sinh_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_sinh` / 定理 `ofReal_sinh`

English:
theorem ofReal_sinh
  given: (x : Real)
  statement: (Real.sinh x : Complex) = sinh x
  proof: ofReal_sinh_ofReal_re _

@[simp]

中文:
定理 ofReal_sinh
  条件: (x : 实数)
  结论: (实数.sinh x : Complex) = sinh x
  证明: ofReal_sinh_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_sinh_ofReal_re
-/
theorem ofReal_sinh (x : Real) : (Real.sinh x : Complex) = sinh x :=
  ofReal_sinh_ofReal_re _

@[simp]
/--
theorem `sinh_ofReal_im` / 定理 `sinh_ofReal_im`

English:
theorem sinh_ofReal_im
  given: (x : Real)
  statement: (sinh x).im = 0
  proof: by rw [← ofReal_sinh_ofReal_re, ofReal_im]

中文:
定理 sinh_ofReal_im
  条件: (x : 实数)
  结论: (sinh x).im = 0
  证明: by rw [← ofReal_sinh_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_sinh_ofReal_re
-/
theorem sinh_ofReal_im (x : Real) : (sinh x).im = 0 := by rw [← ofReal_sinh_ofReal_re, ofReal_im]

/--
theorem `sinh_ofReal_re` / 定理 `sinh_ofReal_re`

English:
theorem sinh_ofReal_re
  given: (x : Real)
  statement: (sinh x).re = Real.sinh x
  proof: rfl

中文:
定理 sinh_ofReal_re
  条件: (x : 实数)
  结论: (sinh x).re = 实数.sinh x
  证明: rfl
-/
theorem sinh_ofReal_re (x : Real) : (sinh x).re = Real.sinh x :=
  rfl

/--
theorem `cosh_conj` / 定理 `cosh_conj`

English:
theorem cosh_conj
  statement: cosh (conj x) = conj (cosh x)
  proof: by
  rw [cosh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_add]; rw [cosh]; rw [map_div₀]; rw [map_ofNat]

中文:
定理 cosh_conj
  结论: cosh (conj x) = conj (cosh x)
  证明: by
  rw [cosh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_add]; rw [cosh]; rw [map_div₀]; rw [map_ofNat]

Depends on / 依赖: exp_conj, map_add, map_neg, map_ofNat
-/
theorem cosh_conj : cosh (conj x) = conj (cosh x) := by
  rw [cosh]; rw [← map_neg]; rw [exp_conj]; rw [exp_conj]; rw [← map_add]; rw [cosh]; rw [map_div₀]; rw [map_ofNat]

/--
theorem `ofReal_cosh_ofReal_re` / 定理 `ofReal_cosh_ofReal_re`

English:
theorem ofReal_cosh_ofReal_re
  given: (x : Real)
  statement: ((cosh x).re : Complex) = cosh x
  proof: conj_eq_iff_re.1 by rw [← cosh_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_cosh_ofReal_re
  条件: (x : 实数)
  结论: ((cosh x).re : Complex) = cosh x
  证明: conj_eq_iff_re.1 by rw [← cosh_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, cosh_conj
-/
theorem ofReal_cosh_ofReal_re (x : Real) : ((cosh x).re : Complex) = cosh x :=
conj_eq_iff_re.1 by rw [← cosh_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_cosh` / 定理 `ofReal_cosh`

English:
theorem ofReal_cosh
  given: (x : Real)
  statement: (Real.cosh x : Complex) = cosh x
  proof: ofReal_cosh_ofReal_re _

@[simp]

中文:
定理 ofReal_cosh
  条件: (x : 实数)
  结论: (实数.cosh x : Complex) = cosh x
  证明: ofReal_cosh_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_cosh_ofReal_re
-/
theorem ofReal_cosh (x : Real) : (Real.cosh x : Complex) = cosh x :=
  ofReal_cosh_ofReal_re _

@[simp]
/--
theorem `cosh_ofReal_im` / 定理 `cosh_ofReal_im`

English:
theorem cosh_ofReal_im
  given: (x : Real)
  statement: (cosh x).im = 0
  proof: by rw [← ofReal_cosh_ofReal_re, ofReal_im]

@[simp]

中文:
定理 cosh_ofReal_im
  条件: (x : 实数)
  结论: (cosh x).im = 0
  证明: by rw [← ofReal_cosh_ofReal_re, ofReal_im]

@[simp]

Depends on / 依赖: ofReal_cosh_ofReal_re, ofReal_im
-/
theorem cosh_ofReal_im (x : Real) : (cosh x).im = 0 := by rw [← ofReal_cosh_ofReal_re, ofReal_im]

@[simp]
/--
theorem `cosh_ofReal_re` / 定理 `cosh_ofReal_re`

English:
theorem cosh_ofReal_re
  given: (x : Real)
  statement: (cosh x).re = Real.cosh x
  proof: rfl

中文:
定理 cosh_ofReal_re
  条件: (x : 实数)
  结论: (cosh x).re = 实数.cosh x
  证明: rfl
-/
theorem cosh_ofReal_re (x : Real) : (cosh x).re = Real.cosh x :=
  rfl

/--
theorem `tanh_eq_sinh_div_cosh` / 定理 `tanh_eq_sinh_div_cosh`

English:
theorem tanh_eq_sinh_div_cosh
  statement: tanh x = sinh x / cosh x
  proof: rfl

@[simp]

中文:
定理 tanh_eq_sinh_div_cosh
  结论: tanh x = sinh x / cosh x
  证明: rfl

@[simp]
-/
theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl

@[simp]
/--
theorem `tanh_zero` / 定理 `tanh_zero`

English:
theorem tanh_zero
  statement: tanh 0 = 0
  proof: by simp [tanh]

@[simp]

中文:
定理 tanh_zero
  结论: tanh 0 = 0
  证明: by simp [tanh]

@[simp]
-/
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
/--
theorem `tanh_neg` / 定理 `tanh_neg`

English:
theorem tanh_neg
  statement: tanh (-x) = -tanh x
  proof: by simp [tanh, neg_div]

中文:
定理 tanh_neg
  结论: tanh (-x) = -tanh x
  证明: by simp [tanh, neg_div]

Depends on / 依赖: neg_div
-/
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

/--
theorem `tanh_conj` / 定理 `tanh_conj`

English:
theorem tanh_conj
  statement: tanh (conj x) = conj (tanh x)
  proof: by
  rw [tanh]; rw [sinh_conj]; rw [cosh_conj]; rw [← map_div₀]; rw [tanh]

@[simp]

中文:
定理 tanh_conj
  结论: tanh (conj x) = conj (tanh x)
  证明: by
  rw [tanh]; rw [sinh_conj]; rw [cosh_conj]; rw [← map_div₀]; rw [tanh]

@[simp]

Depends on / 依赖: cosh_conj, sinh_conj
-/
theorem tanh_conj : tanh (conj x) = conj (tanh x) := by
  rw [tanh]; rw [sinh_conj]; rw [cosh_conj]; rw [← map_div₀]; rw [tanh]

@[simp]
/--
theorem `ofReal_tanh_ofReal_re` / 定理 `ofReal_tanh_ofReal_re`

English:
theorem ofReal_tanh_ofReal_re
  given: (x : Real)
  statement: ((tanh x).re : Complex) = tanh x
  proof: conj_eq_iff_re.1 by rw [← tanh_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_tanh_ofReal_re
  条件: (x : 实数)
  结论: ((tanh x).re : Complex) = tanh x
  证明: conj_eq_iff_re.1 by rw [← tanh_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, tanh_conj
-/
theorem ofReal_tanh_ofReal_re (x : Real) : ((tanh x).re : Complex) = tanh x :=
conj_eq_iff_re.1 by rw [← tanh_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_tanh` / 定理 `ofReal_tanh`

English:
theorem ofReal_tanh
  given: (x : Real)
  statement: (Real.tanh x : Complex) = tanh x
  proof: ofReal_tanh_ofReal_re _

@[simp]

中文:
定理 ofReal_tanh
  条件: (x : 实数)
  结论: (实数.tanh x : Complex) = tanh x
  证明: ofReal_tanh_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_tanh_ofReal_re
-/
theorem ofReal_tanh (x : Real) : (Real.tanh x : Complex) = tanh x :=
  ofReal_tanh_ofReal_re _

@[simp]
/--
theorem `tanh_ofReal_im` / 定理 `tanh_ofReal_im`

English:
theorem tanh_ofReal_im
  given: (x : Real)
  statement: (tanh x).im = 0
  proof: by rw [← ofReal_tanh_ofReal_re, ofReal_im]

中文:
定理 tanh_ofReal_im
  条件: (x : 实数)
  结论: (tanh x).im = 0
  证明: by rw [← ofReal_tanh_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_tanh_ofReal_re
-/
theorem tanh_ofReal_im (x : Real) : (tanh x).im = 0 := by rw [← ofReal_tanh_ofReal_re, ofReal_im]

/--
theorem `tanh_ofReal_re` / 定理 `tanh_ofReal_re`

English:
theorem tanh_ofReal_re
  given: (x : Real)
  statement: (tanh x).re = Real.tanh x
  proof: rfl

@[simp]

中文:
定理 tanh_ofReal_re
  条件: (x : 实数)
  结论: (tanh x).re = 实数.tanh x
  证明: rfl

@[simp]
-/
theorem tanh_ofReal_re (x : Real) : (tanh x).re = Real.tanh x :=
  rfl

@[simp]
/--
theorem `cosh_add_sinh` / 定理 `cosh_add_sinh`

English:
theorem cosh_add_sinh
  statement: cosh x + sinh x = exp x
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [two_cosh]; rw [two_sinh]; rw [add_add_sub_cancel]; rw [two_mul]

@[simp]

中文:
定理 cosh_add_sinh
  结论: cosh x + sinh x = exp x
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [two_cosh]; rw [two_sinh]; rw [add_add_sub_cancel]; rw [two_mul]

@[simp]

Depends on / 依赖: add_add_sub_cancel, mul_add, mul_right_inj, two_cosh, two_mul, two_ne_zero, two_sinh
-/
theorem cosh_add_sinh : cosh x + sinh x = exp x := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_add]; rw [two_cosh]; rw [two_sinh]; rw [add_add_sub_cancel]; rw [two_mul]

@[simp]
/--
theorem `sinh_add_cosh` / 定理 `sinh_add_cosh`

English:
theorem sinh_add_cosh
  statement: sinh x + cosh x = exp x
  proof: by rw [add_comm, cosh_add_sinh]

@[simp]

中文:
定理 sinh_add_cosh
  结论: sinh x + cosh x = exp x
  证明: by rw [add_comm, cosh_add_sinh]

@[simp]

Depends on / 依赖: add_comm, cosh_add_sinh
-/
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
/--
theorem `exp_sub_cosh` / 定理 `exp_sub_cosh`

English:
theorem exp_sub_cosh
  statement: exp x - cosh x = sinh x
  proof: sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]

中文:
定理 exp_sub_cosh
  结论: exp x - cosh x = sinh x
  证明: sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]

Depends on / 依赖: sinh_add_cosh, sub_eq_iff_eq_add
-/
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
/--
theorem `exp_sub_sinh` / 定理 `exp_sub_sinh`

English:
theorem exp_sub_sinh
  statement: exp x - sinh x = cosh x
  proof: sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]

中文:
定理 exp_sub_sinh
  结论: exp x - sinh x = cosh x
  证明: sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]

Depends on / 依赖: cosh_add_sinh, sub_eq_iff_eq_add
-/
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
/--
theorem `cosh_sub_sinh` / 定理 `cosh_sub_sinh`

English:
theorem cosh_sub_sinh
  statement: cosh x - sinh x = exp (-x)
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_sub]; rw [two_cosh]; rw [two_sinh]; rw [add_sub_sub_cancel]; rw [two_mul]

@[simp]

中文:
定理 cosh_sub_sinh
  结论: cosh x - sinh x = exp (-x)
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_sub]; rw [two_cosh]; rw [two_sinh]; rw [add_sub_sub_cancel]; rw [two_mul]

@[simp]

Depends on / 依赖: add_sub_sub_cancel, mul_right_inj, mul_sub, two_cosh, two_mul, two_ne_zero, two_sinh
-/
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [mul_sub]; rw [two_cosh]; rw [two_sinh]; rw [add_sub_sub_cancel]; rw [two_mul]

@[simp]
/--
theorem `sinh_sub_cosh` / 定理 `sinh_sub_cosh`

English:
theorem sinh_sub_cosh
  statement: sinh x - cosh x = -exp (-x)
  proof: by rw [← neg_sub, cosh_sub_sinh]

@[simp]

中文:
定理 sinh_sub_cosh
  结论: sinh x - cosh x = -exp (-x)
  证明: by rw [← neg_sub, cosh_sub_sinh]

@[simp]

Depends on / 依赖: cosh_sub_sinh, neg_sub
-/
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
/--
theorem `cosh_sq_sub_sinh_sq` / 定理 `cosh_sq_sub_sinh_sq`

English:
theorem cosh_sq_sub_sinh_sq
  statement: cosh x ^ 2 - sinh x ^ 2 = 1
  proof: by
  rw [sq_sub_sq]; rw [cosh_add_sinh]; rw [cosh_sub_sinh]; rw [← exp_add]; rw [add_neg_cancel]; rw [exp_zero]

中文:
定理 cosh_sq_sub_sinh_sq
  结论: cosh x ^ 2 - sinh x ^ 2 = 1
  证明: by
  rw [sq_sub_sq]; rw [cosh_add_sinh]; rw [cosh_sub_sinh]; rw [← exp_add]; rw [add_neg_cancel]; rw [exp_zero]

Depends on / 依赖: add_neg_cancel, cosh_add_sinh, cosh_sub_sinh, exp_add, exp_zero, sq_sub_sq
-/
theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [sq_sub_sq]; rw [cosh_add_sinh]; rw [cosh_sub_sinh]; rw [← exp_add]; rw [add_neg_cancel]; rw [exp_zero]

/--
theorem `cosh_sq` / 定理 `cosh_sq`

English:
theorem cosh_sq
  statement: cosh x ^ 2 = sinh x ^ 2 + 1
  proof: by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

中文:
定理 cosh_sq
  结论: cosh x ^ 2 = sinh x ^ 2 + 1
  证明: by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

Depends on / 依赖: cosh_sq_sub_sinh_sq
-/
theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

/--
theorem `sinh_sq` / 定理 `sinh_sq`

English:
theorem sinh_sq
  statement: sinh x ^ 2 = cosh x ^ 2 - 1
  proof: by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

中文:
定理 sinh_sq
  结论: sinh x ^ 2 = cosh x ^ 2 - 1
  证明: by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

Depends on / 依赖: cosh_sq_sub_sinh_sq
-/
theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

/--
theorem `cosh_two_mul` / 定理 `cosh_two_mul`

English:
theorem cosh_two_mul
  statement: cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2
  proof: by rw [two_mul, cosh_add, sq, sq]

中文:
定理 cosh_two_mul
  结论: cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2
  证明: by rw [two_mul, cosh_add, sq, sq]

Depends on / 依赖: cosh_add, two_mul
-/
theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by rw [two_mul, cosh_add, sq, sq]

/--
theorem `sinh_two_mul` / 定理 `sinh_two_mul`

English:
theorem sinh_two_mul
  statement: sinh (2 * x) = 2 * sinh x * cosh x
  proof: by
  rw [two_mul]; rw [sinh_add]
  ring

中文:
定理 sinh_two_mul
  结论: sinh (2 * x) = 2 * sinh x * cosh x
  证明: by
  rw [two_mul]; rw [sinh_add]
  ring

Depends on / 依赖: sinh_add, two_mul
-/
theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [two_mul]; rw [sinh_add]
  ring

/--
theorem `cosh_three_mul` / 定理 `cosh_three_mul`

English:
theorem cosh_three_mul
  statement: cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x
  proof: by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2]; rw [sinh_sq]
  ring

中文:
定理 cosh_three_mul
  结论: cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x
  证明: by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2]; rw [sinh_sq]
  ring

Depends on / 依赖: cosh_add, cosh_two_mul, sinh_sq, sinh_two_mul
-/
theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2]; rw [sinh_sq]
  ring

/--
theorem `sinh_three_mul` / 定理 `sinh_three_mul`

English:
theorem sinh_three_mul
  statement: sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x
  proof: by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2]; rw [cosh_sq]
  ring

@[simp]

中文:
定理 sinh_three_mul
  结论: sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x
  证明: by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2]; rw [cosh_sq]
  ring

@[simp]

Depends on / 依赖: cosh_sq, cosh_two_mul, sinh_add, sinh_two_mul
-/
theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1]; rw [sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2]; rw [cosh_sq]
  ring

@[simp]
/--
theorem `sin_zero` / 定理 `sin_zero`

English:
theorem sin_zero
  statement: sin 0 = 0
  proof: by simp [sin]

@[simp]

中文:
定理 sin_zero
  结论: sin 0 = 0
  证明: by simp [sin]

@[simp]
-/
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
/--
theorem `sin_neg` / 定理 `sin_neg`

English:
theorem sin_neg
  statement: sin (-x) = -sin x
  proof: by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

中文:
定理 sin_neg
  结论: sin (-x) = -sin x
  证明: by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

Depends on / 依赖: add_mul, exp_neg, neg_div, sub_eq_add_neg
-/
theorem sin_neg : sin (-x) = -sin x := by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

/--
theorem `two_sin` / 定理 `two_sin`

English:
theorem two_sin
  statement: 2 * sin x = (exp (-x * I) - exp (x * I)) * I
  proof: mul_div_cancel₀ _ two_ne_zero

中文:
定理 two_sin
  结论: 2 * sin x = (exp (-x * I) - exp (x * I)) * I
  证明: mul_div_cancel₀ _ two_ne_zero

Depends on / 依赖: two_ne_zero
-/
theorem two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel₀ _ two_ne_zero

/--
theorem `two_cos` / 定理 `two_cos`

English:
theorem two_cos
  statement: 2 * cos x = exp (x * I) + exp (-x * I)
  proof: mul_div_cancel₀ _ two_ne_zero

中文:
定理 two_cos
  结论: 2 * cos x = exp (x * I) + exp (-x * I)
  证明: mul_div_cancel₀ _ two_ne_zero

Depends on / 依赖: two_ne_zero
-/
theorem two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel₀ _ two_ne_zero

/--
theorem `sinh_mul_I` / 定理 `sinh_mul_I`

English:
theorem sinh_mul_I
  statement: sinh (x * I) = sin x * I
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [← mul_assoc]; rw [two_sin]; rw [mul_assoc]; rw [I_mul_I]; rw [mul_neg_one]; rw [neg_sub]; rw [neg_mul_eq_neg_mul]

中文:
定理 sinh_mul_I
  结论: sinh (x * I) = sin x * I
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [← mul_assoc]; rw [two_sin]; rw [mul_assoc]; rw [I_mul_I]; rw [mul_neg_one]; rw [neg_sub]; rw [neg_mul_eq_neg_mul]

Depends on / 依赖: I_mul_I, mul_assoc, mul_neg_one, mul_right_inj, neg_mul_eq_neg_mul, neg_sub, two_ne_zero, two_sin, two_sinh
-/
theorem sinh_mul_I : sinh (x * I) = sin x * I := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_sinh]; rw [← mul_assoc]; rw [two_sin]; rw [mul_assoc]; rw [I_mul_I]; rw [mul_neg_one]; rw [neg_sub]; rw [neg_mul_eq_neg_mul]

/--
theorem `cosh_mul_I` / 定理 `cosh_mul_I`

English:
theorem cosh_mul_I
  statement: cosh (x * I) = cos x
  proof: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [two_cos]; rw [neg_mul_eq_neg_mul]

中文:
定理 cosh_mul_I
  结论: cosh (x * I) = cos x
  证明: by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [two_cos]; rw [neg_mul_eq_neg_mul]

Depends on / 依赖: mul_right_inj, neg_mul_eq_neg_mul, two_cos, two_cosh, two_ne_zero
-/
theorem cosh_mul_I : cosh (x * I) = cos x := by
  rw [← mul_right_inj' (two_ne_zero' Complex)]; rw [two_cosh]; rw [two_cos]; rw [neg_mul_eq_neg_mul]

/--
theorem `tanh_mul_I` / 定理 `tanh_mul_I`

English:
theorem tanh_mul_I
  statement: tanh (x * I) = tan x * I
  proof: by
  rw [tanh_eq_sinh_div_cosh]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [mul_div_right_comm]; rw [tan]

中文:
定理 tanh_mul_I
  结论: tanh (x * I) = tan x * I
  证明: by
  rw [tanh_eq_sinh_div_cosh]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [mul_div_right_comm]; rw [tan]

Depends on / 依赖: cosh_mul_I, mul_div_right_comm, sinh_mul_I, tanh_eq_sinh_div_cosh
-/
theorem tanh_mul_I : tanh (x * I) = tan x * I := by
  rw [tanh_eq_sinh_div_cosh]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [mul_div_right_comm]; rw [tan]

/--
theorem `cos_mul_I` / 定理 `cos_mul_I`

English:
theorem cos_mul_I
  statement: cos (x * I) = cosh x
  proof: by rw [← cosh_mul_I]; ring_nf; simp

中文:
定理 cos_mul_I
  结论: cos (x * I) = cosh x
  证明: by rw [← cosh_mul_I]; ring_nf; simp

Depends on / 依赖: cosh_mul_I, ring_nf
-/
theorem cos_mul_I : cos (x * I) = cosh x := by rw [← cosh_mul_I]; ring_nf; simp

/--
theorem `sin_mul_I` / 定理 `sin_mul_I`

English:
theorem sin_mul_I
  statement: sin (x * I) = sinh x * I
  proof: by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm]; rw [← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x)]; rw [← h]
  apply Complex.ext <;> simp

中文:
定理 sin_mul_I
  结论: sin (x * I) = sinh x * I
  证明: by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm]; rw [← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x)]; rw [← h]
  apply Complex.ext <;> simp

Depends on / 依赖: Complex.ext, mul_comm, neg_neg, ring_nf, sinh_mul_I
-/
theorem sin_mul_I : sin (x * I) = sinh x * I := by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm]; rw [← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x)]; rw [← h]
  apply Complex.ext <;> simp

/--
theorem `tan_mul_I` / 定理 `tan_mul_I`

English:
theorem tan_mul_I
  statement: tan (x * I) = tanh x * I
  proof: by
  rw [tan]; rw [sin_mul_I]; rw [cos_mul_I]; rw [mul_div_right_comm]; rw [tanh_eq_sinh_div_cosh]

中文:
定理 tan_mul_I
  结论: tan (x * I) = tanh x * I
  证明: by
  rw [tan]; rw [sin_mul_I]; rw [cos_mul_I]; rw [mul_div_right_comm]; rw [tanh_eq_sinh_div_cosh]

Depends on / 依赖: cos_mul_I, mul_div_right_comm, sin_mul_I, tanh_eq_sinh_div_cosh
-/
theorem tan_mul_I : tan (x * I) = tanh x * I := by
  rw [tan]; rw [sin_mul_I]; rw [cos_mul_I]; rw [mul_div_right_comm]; rw [tanh_eq_sinh_div_cosh]

/--
theorem `sin_add` / 定理 `sin_add`

English:
theorem sin_add
  statement: sin (x + y) = sin x * cos y + cos x * sin y
  proof: by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [← sinh_mul_I]; rw [mul_assoc]; rw [← sinh_mul_I]; rw [← cosh_mul_I]; rw [← cosh_mul_I]; rw [sinh_add]

@[simp]

中文:
定理 sin_add
  结论: sin (x + y) = sin x * cos y + cos x * sin y
  证明: by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [← sinh_mul_I]; rw [mul_assoc]; rw [← sinh_mul_I]; rw [← cosh_mul_I]; rw [← cosh_mul_I]; rw [sinh_add]

@[simp]

Depends on / 依赖: I_ne_zero, add_mul, cosh_mul_I, mul_assoc, mul_left_inj, mul_right_comm, sinh_add, sinh_mul_I
-/
theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [add_mul]; rw [add_mul]; rw [mul_right_comm]; rw [← sinh_mul_I]; rw [mul_assoc]; rw [← sinh_mul_I]; rw [← cosh_mul_I]; rw [← cosh_mul_I]; rw [sinh_add]

@[simp]
/--
theorem `cos_zero` / 定理 `cos_zero`

English:
theorem cos_zero
  statement: cos 0 = 1
  proof: by simp [cos]

@[simp]

中文:
定理 cos_zero
  结论: cos 0 = 1
  证明: by simp [cos]

@[simp]
-/
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
/--
theorem `cos_neg` / 定理 `cos_neg`

English:
theorem cos_neg
  statement: cos (-x) = cos x
  proof: by simp [cos, exp_neg, add_comm]

中文:
定理 cos_neg
  结论: cos (-x) = cos x
  证明: by simp [cos, exp_neg, add_comm]

Depends on / 依赖: add_comm, exp_neg
-/
theorem cos_neg : cos (-x) = cos x := by simp [cos, exp_neg, add_comm]

/--
theorem `cos_add` / 定理 `cos_add`

English:
theorem cos_add
  statement: cos (x + y) = cos x * cos y - sin x * sin y
  proof: by
  rw [← cosh_mul_I]; rw [add_mul]; rw [cosh_add]; rw [cosh_mul_I]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [sinh_mul_I]; rw [mul_mul_mul_comm]; rw [I_mul_I]; rw [mul_neg_one]; rw [sub_eq_add_neg]

中文:
定理 cos_add
  结论: cos (x + y) = cos x * cos y - sin x * sin y
  证明: by
  rw [← cosh_mul_I]; rw [add_mul]; rw [cosh_add]; rw [cosh_mul_I]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [sinh_mul_I]; rw [mul_mul_mul_comm]; rw [I_mul_I]; rw [mul_neg_one]; rw [sub_eq_add_neg]

Depends on / 依赖: I_mul_I, add_mul, cosh_add, cosh_mul_I, mul_mul_mul_comm, mul_neg_one, sinh_mul_I, sub_eq_add_neg
-/
theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← cosh_mul_I]; rw [add_mul]; rw [cosh_add]; rw [cosh_mul_I]; rw [cosh_mul_I]; rw [sinh_mul_I]; rw [sinh_mul_I]; rw [mul_mul_mul_comm]; rw [I_mul_I]; rw [mul_neg_one]; rw [sub_eq_add_neg]

/--
theorem `sin_sub` / 定理 `sin_sub`

English:
theorem sin_sub
  statement: sin (x - y) = sin x * cos y - cos x * sin y
  proof: by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

中文:
定理 sin_sub
  结论: sin (x - y) = sin x * cos y - cos x * sin y
  证明: by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

Depends on / 依赖: cos_neg, sin_add, sin_neg, sub_eq_add_neg
-/
theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

/--
theorem `cos_sub` / 定理 `cos_sub`

English:
theorem cos_sub
  statement: cos (x - y) = cos x * cos y + sin x * sin y
  proof: by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

中文:
定理 cos_sub
  结论: cos (x - y) = cos x * cos y + sin x * sin y
  证明: by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

Depends on / 依赖: cos_add, cos_neg, sin_neg, sub_eq_add_neg
-/
theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

/--
theorem `sin_add_mul_I` / 定理 `sin_add_mul_I`

English:
theorem sin_add_mul_I
  given: (x y : Complex)
  statement: sin (x + y * I) = sin x * cosh y + cos x * sinh y * I
  proof: by
  rw [sin_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

中文:
定理 sin_add_mul_I
  条件: (x y : Complex)
  结论: sin (x + y * I) = sin x * cosh y + cos x * sinh y * I
  证明: by
  rw [sin_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

Depends on / 依赖: cos_mul_I, mul_assoc, sin_add, sin_mul_I
-/
theorem sin_add_mul_I (x y : Complex) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := by
  rw [sin_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

/--
theorem `sin_eq` / 定理 `sin_eq`

English:
theorem sin_eq
  given: (z : Complex)
  statement: sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I
  proof: by
  convert! sin_add_mul_I z.re z.im; exact (re_add_im z).symm

中文:
定理 sin_eq
  条件: (z : Complex)
  结论: sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I
  证明: by
  convert! sin_add_mul_I z.re z.im; exact (re_add_im z).symm

Depends on / 依赖: convert, re_add_im, sin_add_mul_I, z.im, z.re
-/
theorem sin_eq (z : Complex) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I := by
  convert! sin_add_mul_I z.re z.im; exact (re_add_im z).symm

/--
theorem `cos_add_mul_I` / 定理 `cos_add_mul_I`

English:
theorem cos_add_mul_I
  given: (x y : Complex)
  statement: cos (x + y * I) = cos x * cosh y - sin x * sinh y * I
  proof: by
  rw [cos_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

中文:
定理 cos_add_mul_I
  条件: (x y : Complex)
  结论: cos (x + y * I) = cos x * cosh y - sin x * sinh y * I
  证明: by
  rw [cos_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

Depends on / 依赖: cos_add, cos_mul_I, mul_assoc, sin_mul_I
-/
theorem cos_add_mul_I (x y : Complex) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := by
  rw [cos_add]; rw [cos_mul_I]; rw [sin_mul_I]; rw [mul_assoc]

/--
theorem `cos_eq` / 定理 `cos_eq`

English:
theorem cos_eq
  given: (z : Complex)
  statement: cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I
  proof: by
  convert! cos_add_mul_I z.re z.im; exact (re_add_im z).symm

中文:
定理 cos_eq
  条件: (z : Complex)
  结论: cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I
  证明: by
  convert! cos_add_mul_I z.re z.im; exact (re_add_im z).symm

Depends on / 依赖: convert, cos_add_mul_I, re_add_im, z.im, z.re
-/
theorem cos_eq (z : Complex) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I := by
  convert! cos_add_mul_I z.re z.im; exact (re_add_im z).symm

/--
theorem `sin_sub_sin` / 定理 `sin_sub_sin`

English:
theorem sin_sub_sin
  statement: sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2)
  proof: by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at

中文:
定理 sin_sub_sin
  结论: sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2)
  证明: by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at

Depends on / 依赖: add_div, add_right_comm, add_self_div_two, add_sub, add_sub_cancel_left, add_sub_cancel_right, div_sub_div_same, sin_add, sin_sub, sub_add
-/
theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) := by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at s2
  rw [s1]; rw [s2]
  ring

/--
theorem `cos_sub_cos` / 定理 `cos_sub_cos`

English:
theorem cos_sub_cos
  statement: cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2)
  proof: by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at

中文:
定理 cos_sub_cos
  结论: cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2)
  证明: by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at

Depends on / 依赖: add_div, add_right_comm, add_self_div_two, add_sub, add_sub_cancel_left, add_sub_cancel_right, cos_add, cos_sub, div_sub_div_same, sub_add
-/
theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [← add_div]; rw [add_sub]; rw [add_right_comm]; rw [add_sub_cancel_right]; rw [add_self_div_two] at s1
  rw [div_sub_div_same]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two] at s2
  rw [s1]; rw [s2]
  ring

/--
theorem `sin_add_sin` / 定理 `sin_add_sin`

English:
theorem sin_add_sin
  statement: sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2)
  proof: by
  simpa using! sin_sub_sin x (-y)

中文:
定理 sin_add_sin
  结论: sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2)
  证明: by
  simpa using! sin_sub_sin x (-y)

Depends on / 依赖: sin_sub_sin
-/
theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) := by
  simpa using! sin_sub_sin x (-y)

/--
theorem `cos_add_cos` / 定理 `cos_add_cos`

English:
theorem cos_add_cos
  statement: cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)
  proof: by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_


中文:
定理 cos_add_cos
  结论: cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)
  证明: by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_


Depends on / 依赖: cos_add, cos_sub
-/
theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := ?_
  · congr <;> field
  · rw [cos_add, cos_sub]
  ring

/--
theorem `sin_conj` / 定理 `sin_conj`

English:
theorem sin_conj
  statement: sin (conj x) = conj (sin x)
  proof: by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← map_mul]; rw [sinh_conj]; rw [mul_neg]; rw [sinh_neg]; rw [sinh_mul_I]; rw [mul_neg]

@[simp]

中文:
定理 sin_conj
  结论: sin (conj x) = conj (sin x)
  证明: by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← map_mul]; rw [sinh_conj]; rw [mul_neg]; rw [sinh_neg]; rw [sinh_mul_I]; rw [mul_neg]

@[simp]

Depends on / 依赖: I_ne_zero, conj_neg_I, map_mul, mul_left_inj, mul_neg, sinh_conj, sinh_mul_I, sinh_neg
-/
theorem sin_conj : sin (conj x) = conj (sin x) := by
  rw [← mul_left_inj' I_ne_zero]; rw [← sinh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← map_mul]; rw [sinh_conj]; rw [mul_neg]; rw [sinh_neg]; rw [sinh_mul_I]; rw [mul_neg]

@[simp]
/--
theorem `ofReal_sin_ofReal_re` / 定理 `ofReal_sin_ofReal_re`

English:
theorem ofReal_sin_ofReal_re
  given: (x : Real)
  statement: ((sin x).re : Complex) = sin x
  proof: conj_eq_iff_re.1 by rw [← sin_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_sin_ofReal_re
  条件: (x : 实数)
  结论: ((sin x).re : Complex) = sin x
  证明: conj_eq_iff_re.1 by rw [← sin_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, sin_conj
-/
theorem ofReal_sin_ofReal_re (x : Real) : ((sin x).re : Complex) = sin x :=
conj_eq_iff_re.1 by rw [← sin_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_sin` / 定理 `ofReal_sin`

English:
theorem ofReal_sin
  given: (x : Real)
  statement: (Real.sin x : Complex) = sin x
  proof: ofReal_sin_ofReal_re _

@[simp]

中文:
定理 ofReal_sin
  条件: (x : 实数)
  结论: (实数.sin x : Complex) = sin x
  证明: ofReal_sin_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_sin_ofReal_re
-/
theorem ofReal_sin (x : Real) : (Real.sin x : Complex) = sin x :=
  ofReal_sin_ofReal_re _

@[simp]
/--
theorem `sin_ofReal_im` / 定理 `sin_ofReal_im`

English:
theorem sin_ofReal_im
  given: (x : Real)
  statement: (sin x).im = 0
  proof: by rw [← ofReal_sin_ofReal_re, ofReal_im]

中文:
定理 sin_ofReal_im
  条件: (x : 实数)
  结论: (sin x).im = 0
  证明: by rw [← ofReal_sin_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_sin_ofReal_re
-/
theorem sin_ofReal_im (x : Real) : (sin x).im = 0 := by rw [← ofReal_sin_ofReal_re, ofReal_im]

/--
theorem `sin_ofReal_re` / 定理 `sin_ofReal_re`

English:
theorem sin_ofReal_re
  given: (x : Real)
  statement: (sin x).re = Real.sin x
  proof: rfl

中文:
定理 sin_ofReal_re
  条件: (x : 实数)
  结论: (sin x).re = 实数.sin x
  证明: rfl
-/
theorem sin_ofReal_re (x : Real) : (sin x).re = Real.sin x :=
  rfl

/--
theorem `cos_conj` / 定理 `cos_conj`

English:
theorem cos_conj
  statement: cos (conj x) = conj (cos x)
  proof: by
  rw [← cosh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← cosh_mul_I]; rw [cosh_conj]; rw [mul_neg]; rw [cosh_neg]

@[simp]

中文:
定理 cos_conj
  结论: cos (conj x) = conj (cos x)
  证明: by
  rw [← cosh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← cosh_mul_I]; rw [cosh_conj]; rw [mul_neg]; rw [cosh_neg]

@[simp]

Depends on / 依赖: conj_neg_I, cosh_conj, cosh_mul_I, cosh_neg, map_mul, mul_neg
-/
theorem cos_conj : cos (conj x) = conj (cos x) := by
  rw [← cosh_mul_I]; rw [← conj_neg_I]; rw [← map_mul]; rw [← cosh_mul_I]; rw [cosh_conj]; rw [mul_neg]; rw [cosh_neg]

@[simp]
/--
theorem `ofReal_cos_ofReal_re` / 定理 `ofReal_cos_ofReal_re`

English:
theorem ofReal_cos_ofReal_re
  given: (x : Real)
  statement: ((cos x).re : Complex) = cos x
  proof: conj_eq_iff_re.1 by rw [← cos_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_cos_ofReal_re
  条件: (x : 实数)
  结论: ((cos x).re : Complex) = cos x
  证明: conj_eq_iff_re.1 by rw [← cos_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, cos_conj
-/
theorem ofReal_cos_ofReal_re (x : Real) : ((cos x).re : Complex) = cos x :=
conj_eq_iff_re.1 by rw [← cos_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_cos` / 定理 `ofReal_cos`

English:
theorem ofReal_cos
  given: (x : Real)
  statement: (Real.cos x : Complex) = cos x
  proof: ofReal_cos_ofReal_re _

@[simp]

中文:
定理 ofReal_cos
  条件: (x : 实数)
  结论: (实数.cos x : Complex) = cos x
  证明: ofReal_cos_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_cos_ofReal_re
-/
theorem ofReal_cos (x : Real) : (Real.cos x : Complex) = cos x :=
  ofReal_cos_ofReal_re _

@[simp]
/--
theorem `cos_ofReal_im` / 定理 `cos_ofReal_im`

English:
theorem cos_ofReal_im
  given: (x : Real)
  statement: (cos x).im = 0
  proof: by rw [← ofReal_cos_ofReal_re, ofReal_im]

中文:
定理 cos_ofReal_im
  条件: (x : 实数)
  结论: (cos x).im = 0
  证明: by rw [← ofReal_cos_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_cos_ofReal_re, ofReal_im
-/
theorem cos_ofReal_im (x : Real) : (cos x).im = 0 := by rw [← ofReal_cos_ofReal_re, ofReal_im]

/--
theorem `cos_ofReal_re` / 定理 `cos_ofReal_re`

English:
theorem cos_ofReal_re
  given: (x : Real)
  statement: (cos x).re = Real.cos x
  proof: rfl

@[simp]

中文:
定理 cos_ofReal_re
  条件: (x : 实数)
  结论: (cos x).re = 实数.cos x
  证明: rfl

@[simp]
-/
theorem cos_ofReal_re (x : Real) : (cos x).re = Real.cos x :=
  rfl

@[simp]
/--
theorem `tan_zero` / 定理 `tan_zero`

English:
theorem tan_zero
  statement: tan 0 = 0
  proof: by simp [tan]

中文:
定理 tan_zero
  结论: tan 0 = 0
  证明: by simp [tan]
-/
theorem tan_zero : tan 0 = 0 := by simp [tan]

/--
theorem `tan_eq_sin_div_cos` / 定理 `tan_eq_sin_div_cos`

English:
theorem tan_eq_sin_div_cos
  statement: tan x = sin x / cos x
  proof: rfl

中文:
定理 tan_eq_sin_div_cos
  结论: tan x = sin x / cos x
  证明: rfl
-/
theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl

/--
theorem `cot_eq_cos_div_sin` / 定理 `cot_eq_cos_div_sin`

English:
theorem cot_eq_cos_div_sin
  statement: cot x = cos x / sin x
  proof: rfl

中文:
定理 cot_eq_cos_div_sin
  结论: cot x = cos x / sin x
  证明: rfl
-/
theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
  rfl

/--
theorem `tan_mul_cos` / 定理 `tan_mul_cos`

English:
theorem tan_mul_cos
  given: {x : Complex} (hx : cos x != 0)
  statement: tan x * cos x = sin x
  proof: by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]

中文:
定理 tan_mul_cos
  条件: {x : Complex} (hx : cos x != 0)
  结论: tan x * cos x = sin x
  证明: by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]

Depends on / 依赖: tan_eq_sin_div_cos
-/
theorem tan_mul_cos {x : Complex} (hx : cos x != 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]
/--
theorem `tan_inv_eq_cot` / 定理 `tan_inv_eq_cot`

English:
theorem tan_inv_eq_cot
  statement: (tan x)⁻¹ = cot x
  proof: inv_div ..

@[simp]

中文:
定理 tan_inv_eq_cot
  结论: (tan x)⁻¹ = cot x
  证明: inv_div ..

@[simp]

Depends on / 依赖: inv_div
-/
theorem tan_inv_eq_cot : (tan x)⁻¹ = cot x :=
  inv_div ..

@[simp]
/--
theorem `cot_inv_eq_tan` / 定理 `cot_inv_eq_tan`

English:
theorem cot_inv_eq_tan
  statement: (cot x)⁻¹ = tan x
  proof: inv_div ..

@[simp]

中文:
定理 cot_inv_eq_tan
  结论: (cot x)⁻¹ = tan x
  证明: inv_div ..

@[simp]

Depends on / 依赖: inv_div
-/
theorem cot_inv_eq_tan : (cot x)⁻¹ = tan x :=
  inv_div ..

@[simp]
/--
theorem `tan_neg` / 定理 `tan_neg`

English:
theorem tan_neg
  statement: tan (-x) = -tan x
  proof: by simp [tan, neg_div]

中文:
定理 tan_neg
  结论: tan (-x) = -tan x
  证明: by simp [tan, neg_div]

Depends on / 依赖: neg_div
-/
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

/--
theorem `tan_conj` / 定理 `tan_conj`

English:
theorem tan_conj
  statement: tan (conj x) = conj (tan x)
  proof: by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]

中文:
定理 tan_conj
  结论: tan (conj x) = conj (tan x)
  证明: by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]

Depends on / 依赖: cos_conj, sin_conj
-/
theorem tan_conj : tan (conj x) = conj (tan x) := by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]

/--
theorem `cot_conj` / 定理 `cot_conj`

English:
theorem cot_conj
  statement: cot (conj x) = conj (cot x)
  proof: by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

@[simp]

中文:
定理 cot_conj
  结论: cot (conj x) = conj (cot x)
  证明: by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

@[simp]

Depends on / 依赖: cos_conj, sin_conj
-/
theorem cot_conj : cot (conj x) = conj (cot x) := by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

@[simp]
/--
theorem `ofReal_tan_ofReal_re` / 定理 `ofReal_tan_ofReal_re`

English:
theorem ofReal_tan_ofReal_re
  given: (x : Real)
  statement: ((tan x).re : Complex) = tan x
  proof: conj_eq_iff_re.1 by rw [← tan_conj, conj_ofReal]

@[simp]

中文:
定理 ofReal_tan_ofReal_re
  条件: (x : 实数)
  结论: ((tan x).re : Complex) = tan x
  证明: conj_eq_iff_re.1 by rw [← tan_conj, conj_ofReal]

@[simp]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, tan_conj
-/
theorem ofReal_tan_ofReal_re (x : Real) : ((tan x).re : Complex) = tan x :=
conj_eq_iff_re.1 by rw [← tan_conj, conj_ofReal]

@[simp]
/--
theorem `ofReal_cot_ofReal_re` / 定理 `ofReal_cot_ofReal_re`

English:
theorem ofReal_cot_ofReal_re
  given: (x : Real)
  statement: ((cot x).re : Complex) = cot x
  proof: conj_eq_iff_re.1 by rw [← cot_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 ofReal_cot_ofReal_re
  条件: (x : 实数)
  结论: ((cot x).re : Complex) = cot x
  证明: conj_eq_iff_re.1 by rw [← cot_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, cot_conj
-/
theorem ofReal_cot_ofReal_re (x : Real) : ((cot x).re : Complex) = cot x :=
conj_eq_iff_re.1 by rw [← cot_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_tan` / 定理 `ofReal_tan`

English:
theorem ofReal_tan
  given: (x : Real)
  statement: (Real.tan x : Complex) = tan x
  proof: ofReal_tan_ofReal_re _

@[simp, norm_cast]

中文:
定理 ofReal_tan
  条件: (x : 实数)
  结论: (实数.tan x : Complex) = tan x
  证明: ofReal_tan_ofReal_re _

@[simp, norm_cast]

Depends on / 依赖: ofReal_tan_ofReal_re
-/
theorem ofReal_tan (x : Real) : (Real.tan x : Complex) = tan x :=
  ofReal_tan_ofReal_re _

@[simp, norm_cast]
/--
theorem `ofReal_cot` / 定理 `ofReal_cot`

English:
theorem ofReal_cot
  given: (x : Real)
  statement: (Real.cot x : Complex) = cot x
  proof: ofReal_cot_ofReal_re _

@[simp]

中文:
定理 ofReal_cot
  条件: (x : 实数)
  结论: (实数.cot x : Complex) = cot x
  证明: ofReal_cot_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_cot_ofReal_re
-/
theorem ofReal_cot (x : Real) : (Real.cot x : Complex) = cot x :=
  ofReal_cot_ofReal_re _

@[simp]
/--
theorem `tan_ofReal_im` / 定理 `tan_ofReal_im`

English:
theorem tan_ofReal_im
  given: (x : Real)
  statement: (tan x).im = 0
  proof: by rw [← ofReal_tan_ofReal_re, ofReal_im]

中文:
定理 tan_ofReal_im
  条件: (x : 实数)
  结论: (tan x).im = 0
  证明: by rw [← ofReal_tan_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_im, ofReal_tan_ofReal_re
-/
theorem tan_ofReal_im (x : Real) : (tan x).im = 0 := by rw [← ofReal_tan_ofReal_re, ofReal_im]

/--
theorem `tan_ofReal_re` / 定理 `tan_ofReal_re`

English:
theorem tan_ofReal_re
  given: (x : Real)
  statement: (tan x).re = Real.tan x
  proof: rfl

中文:
定理 tan_ofReal_re
  条件: (x : 实数)
  结论: (tan x).re = 实数.tan x
  证明: rfl
-/
theorem tan_ofReal_re (x : Real) : (tan x).re = Real.tan x :=
  rfl

/--
theorem `cos_add_sin_I` / 定理 `cos_add_sin_I`

English:
theorem cos_add_sin_I
  statement: cos x + sin x * I = exp (x * I)
  proof: by
  rw [← cosh_add_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

中文:
定理 cos_add_sin_I
  结论: cos x + sin x * I = exp (x * I)
  证明: by
  rw [← cosh_add_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

Depends on / 依赖: cosh_add_sinh, cosh_mul_I, sinh_mul_I
-/
theorem cos_add_sin_I : cos x + sin x * I = exp (x * I) := by
  rw [← cosh_add_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

/--
theorem `cos_sub_sin_I` / 定理 `cos_sub_sin_I`

English:
theorem cos_sub_sin_I
  statement: cos x - sin x * I = exp (-x * I)
  proof: by
  rw [neg_mul]; rw [← cosh_sub_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

@[simp]

中文:
定理 cos_sub_sin_I
  结论: cos x - sin x * I = exp (-x * I)
  证明: by
  rw [neg_mul]; rw [← cosh_sub_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

@[simp]

Depends on / 依赖: cosh_mul_I, cosh_sub_sinh, neg_mul, sinh_mul_I
-/
theorem cos_sub_sin_I : cos x - sin x * I = exp (-x * I) := by
  rw [neg_mul]; rw [← cosh_sub_sinh]; rw [sinh_mul_I]; rw [cosh_mul_I]

@[simp]
/--
theorem `sin_sq_add_cos_sq` / 定理 `sin_sq_add_cos_sq`

English:
theorem sin_sq_add_cos_sq
  statement: sin x ^ 2 + cos x ^ 2 = 1
  proof: Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))

@[simp]

中文:
定理 sin_sq_add_cos_sq
  结论: sin x ^ 2 + cos x ^ 2 = 1
  证明: Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))

@[simp]

Depends on / 依赖: Eq.trans, I_sq, add_comm, cosh_mul_I, cosh_sq_sub_sinh_sq, mul_neg_one, mul_pow, sinh_mul_I, sub_neg_eq_add
-/
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))

@[simp]
/--
theorem `cos_sq_add_sin_sq` / 定理 `cos_sq_add_sin_sq`

English:
theorem cos_sq_add_sin_sq
  statement: cos x ^ 2 + sin x ^ 2 = 1
  proof: by rw [add_comm, sin_sq_add_cos_sq]

中文:
定理 cos_sq_add_sin_sq
  结论: cos x ^ 2 + sin x ^ 2 = 1
  证明: by rw [add_comm, sin_sq_add_cos_sq]

Depends on / 依赖: add_comm, sin_sq_add_cos_sq
-/
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

/--
theorem `cos_two_mul'` / 定理 `cos_two_mul'`

English:
theorem cos_two_mul'
  statement: cos (2 * x) = cos x ^ 2 - sin x ^ 2
  proof: by rw [two_mul, cos_add, ← sq, ← sq]

中文:
定理 cos_two_mul'
  结论: cos (2 * x) = cos x ^ 2 - sin x ^ 2
  证明: by rw [two_mul, cos_add, ← sq, ← sq]

Depends on / 依赖: cos_add, two_mul
-/
theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [two_mul, cos_add, ← sq, ← sq]

/--
theorem `cos_two_mul` / 定理 `cos_two_mul`

English:
theorem cos_two_mul
  statement: cos (2 * x) = 2 * cos x ^ 2 - 1
  proof: by
  rw [cos_two_mul']; rw [eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x)]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [two_mul]

中文:
定理 cos_two_mul
  结论: cos (2 * x) = 2 * cos x ^ 2 - 1
  证明: by
  rw [cos_two_mul']; rw [eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x)]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [two_mul]

Depends on / 依赖: cos_two_mul, eq_sub_iff_add_eq, sin_sq_add_cos_sq, sub_add, sub_add_eq_add_sub, two_mul
-/
theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [cos_two_mul']; rw [eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x)]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [two_mul]

/--
theorem `cos_two_mul_eq_one_sub` / 定理 `cos_two_mul_eq_one_sub`

English:
theorem cos_two_mul_eq_one_sub
  statement: cos (2 * x) = 1 - 2 * sin x ^ 2
  proof: by
  grind [cos_two_mul, sin_sq_add_cos_sq]

中文:
定理 cos_two_mul_eq_one_sub
  结论: cos (2 * x) = 1 - 2 * sin x ^ 2
  证明: by
  grind [cos_two_mul, sin_sq_add_cos_sq]

Depends on / 依赖: cos_two_mul, sin_sq_add_cos_sq
-/
theorem cos_two_mul_eq_one_sub : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
  grind [cos_two_mul, sin_sq_add_cos_sq]

/--
theorem `sin_two_mul` / 定理 `sin_two_mul`

English:
theorem sin_two_mul
  statement: sin (2 * x) = 2 * sin x * cos x
  proof: by
  rw [two_mul]; rw [sin_add]; rw [two_mul]; rw [add_mul]; rw [mul_comm]

中文:
定理 sin_two_mul
  结论: sin (2 * x) = 2 * sin x * cos x
  证明: by
  rw [two_mul]; rw [sin_add]; rw [two_mul]; rw [add_mul]; rw [mul_comm]

Depends on / 依赖: add_mul, mul_comm, sin_add, two_mul
-/
theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [two_mul]; rw [sin_add]; rw [two_mul]; rw [add_mul]; rw [mul_comm]

/--
theorem `cos_sq` / 定理 `cos_sq`

English:
theorem cos_sq
  statement: cos x ^ 2 = 1 / 2 + cos (2 * x) / 2
  proof: by
  simp [cos_two_mul, ← add_div, mul_div_cancel_left₀, -one_div]

中文:
定理 cos_sq
  结论: cos x ^ 2 = 1 / 2 + cos (2 * x) / 2
  证明: by
  simp [cos_two_mul, ← add_div, mul_div_cancel_left₀, -one_div]

Depends on / 依赖: add_div, cos_two_mul, one_div
-/
theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by
  simp [cos_two_mul, ← add_div, mul_div_cancel_left₀, -one_div]

/--
theorem `cos_sq'` / 定理 `cos_sq'`

English:
theorem cos_sq'
  statement: cos x ^ 2 = 1 - sin x ^ 2
  proof: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

中文:
定理 cos_sq'
  结论: cos x ^ 2 = 1 - sin x ^ 2
  证明: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, sin_sq_add_cos_sq
-/
theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

/--
theorem `sin_sq` / 定理 `sin_sq`

English:
theorem sin_sq
  statement: sin x ^ 2 = 1 - cos x ^ 2
  proof: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_right]

中文:
定理 sin_sq
  结论: sin x ^ 2 = 1 - cos x ^ 2
  证明: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, sin_sq_add_cos_sq
-/
theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_right]

/--
theorem `one_add_tan_sq_mul_cos_sq_eq_one` / 定理 `one_add_tan_sq_mul_cos_sq_eq_one`

English:
theorem one_add_tan_sq_mul_cos_sq_eq_one
  given: {x : Complex} (h : cos x != 0)
  proof: by
  conv_rhs => rw [← sin_sq_add_cos_sq x, ← tan_mul_cos h]
  ring

中文:
定理 one_add_tan_sq_mul_cos_sq_eq_one
  条件: {x : Complex} (h : cos x != 0)
  证明: by
  conv_rhs => rw [← sin_sq_add_cos_sq x, ← tan_mul_cos h]
  ring

Depends on / 依赖: conv_rhs, sin_sq_add_cos_sq, tan_mul_cos
-/
theorem one_add_tan_sq_mul_cos_sq_eq_one {x : Complex} (h : cos x != 0) :
    (1 + tan x ^ 2) * cos x ^ 2 = 1 := by
  conv_rhs => rw [← sin_sq_add_cos_sq x, ← tan_mul_cos h]
  ring

/--
theorem `inv_one_add_tan_sq` / 定理 `inv_one_add_tan_sq`

English:
theorem inv_one_add_tan_sq
  given: {x : Complex} (hx : cos x != 0)
  statement: (1 + tan x ^ 2)⁻¹ = cos x ^ 2
  proof: by
  rw [tan_eq_sin_div_cos]; rw [div_pow]
  simp [field]

中文:
定理 inv_one_add_tan_sq
  条件: {x : Complex} (hx : cos x != 0)
  结论: (1 + tan x ^ 2)⁻¹ = cos x ^ 2
  证明: by
  rw [tan_eq_sin_div_cos]; rw [div_pow]
  simp [field]

Depends on / 依赖: div_pow, tan_eq_sin_div_cos
-/
theorem inv_one_add_tan_sq {x : Complex} (hx : cos x != 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 := by
  rw [tan_eq_sin_div_cos]; rw [div_pow]
  simp [field]

/--
theorem `tan_sq_div_one_add_tan_sq` / 定理 `tan_sq_div_one_add_tan_sq`

English:
theorem tan_sq_div_one_add_tan_sq
  given: {x : Complex} (hx : cos x != 0)
  proof: by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

中文:
定理 tan_sq_div_one_add_tan_sq
  条件: {x : Complex} (hx : cos x != 0)
  证明: by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, inv_one_add_tan_sq, mul_pow, tan_mul_cos
-/
theorem tan_sq_div_one_add_tan_sq {x : Complex} (hx : cos x != 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

/--
theorem `cos_three_mul` / 定理 `cos_three_mul`

English:
theorem cos_three_mul
  statement: cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x
  proof: by
  rw [← cosh_mul_I]; rw [mul_assoc]; rw [cosh_three_mul]; rw [cosh_mul_I]

中文:
定理 cos_three_mul
  结论: cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x
  证明: by
  rw [← cosh_mul_I]; rw [mul_assoc]; rw [cosh_three_mul]; rw [cosh_mul_I]

Depends on / 依赖: cosh_mul_I, cosh_three_mul, mul_assoc
-/
theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← cosh_mul_I]; rw [mul_assoc]; rw [cosh_three_mul]; rw [cosh_mul_I]

/--
theorem `sin_three_mul` / 定理 `sin_three_mul`

English:
theorem sin_three_mul
  statement: sin (3 * x) = 3 * sin x - 4 * sin x ^ 3
  proof: by
  rw [← two_add_one_eq_three]; rw [add_one_mul]; rw [sin_add (2 * x) x]
  simp only [cos_two_mul, sin_two_mul, cos_sq', mul_assoc, ← sq]
  ring

中文:
定理 sin_three_mul
  结论: sin (3 * x) = 3 * sin x - 4 * sin x ^ 3
  证明: by
  rw [← two_add_one_eq_three]; rw [add_one_mul]; rw [sin_add (2 * x) x]
  simp only [cos_two_mul, sin_two_mul, cos_sq', mul_assoc, ← sq]
  ring

Depends on / 依赖: add_one_mul, cos_sq, cos_two_mul, mul_assoc, sin_add, sin_two_mul, two_add_one_eq_three
-/
theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← two_add_one_eq_three]; rw [add_one_mul]; rw [sin_add (2 * x) x]
  simp only [cos_two_mul, sin_two_mul, cos_sq', mul_assoc, ← sq]
  ring

/--
theorem `exp_mul_I` / 定理 `exp_mul_I`

English:
theorem exp_mul_I
  statement: exp (x * I) = cos x + sin x * I
  proof: (cos_add_sin_I _).symm

中文:
定理 exp_mul_I
  结论: exp (x * I) = cos x + sin x * I
  证明: (cos_add_sin_I _).symm

Depends on / 依赖: cos_add_sin_I
-/
theorem exp_mul_I : exp (x * I) = cos x + sin x * I :=
  (cos_add_sin_I _).symm

/--
theorem `exp_add_mul_I` / 定理 `exp_add_mul_I`

English:
theorem exp_add_mul_I
  statement: exp (x + y * I) = exp x * (cos y + sin y * I)
  proof: by rw [exp_add, exp_mul_I]

中文:
定理 exp_add_mul_I
  结论: exp (x + y * I) = exp x * (cos y + sin y * I)
  证明: by rw [exp_add, exp_mul_I]

Depends on / 依赖: exp_add, exp_mul_I
-/
theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]

/--
theorem `exp_eq_exp_re_mul_sin_add_cos` / 定理 `exp_eq_exp_re_mul_sin_add_cos`

English:
theorem exp_eq_exp_re_mul_sin_add_cos
  statement: exp x = exp x.re * (cos x.im + sin x.im * I)
  proof: by
  rw [← exp_add_mul_I]; rw [re_add_im]

中文:
定理 exp_eq_exp_re_mul_sin_add_cos
  结论: exp x = exp x.re * (cos x.im + sin x.im * I)
  证明: by
  rw [← exp_add_mul_I]; rw [re_add_im]

Depends on / 依赖: exp_add_mul_I, re_add_im
-/
theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) := by
  rw [← exp_add_mul_I]; rw [re_add_im]

/--
theorem `exp_re` / 定理 `exp_re`

English:
theorem exp_re
  statement: (exp x).re = Real.exp x.re * Real.cos x.im
  proof: by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]

中文:
定理 exp_re
  结论: (exp x).re = 实数.exp x.re * 实数.cos x.im
  证明: by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]

Depends on / 依赖: cos_ofReal_re, exp_eq_exp_re_mul_sin_add_cos, exp_ofReal_re
-/
theorem exp_re : (exp x).re = Real.exp x.re * Real.cos x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]

/--
theorem `exp_im` / 定理 `exp_im`

English:
theorem exp_im
  statement: (exp x).im = Real.exp x.re * Real.sin x.im
  proof: by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]

@[simp]

中文:
定理 exp_im
  结论: (exp x).im = 实数.exp x.re * 实数.sin x.im
  证明: by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]

@[simp]

Depends on / 依赖: exp_eq_exp_re_mul_sin_add_cos, exp_ofReal_re, sin_ofReal_re
-/
theorem exp_im : (exp x).im = Real.exp x.re * Real.sin x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]

@[simp]
/--
theorem `exp_ofReal_mul_I_re` / 定理 `exp_ofReal_mul_I_re`

English:
theorem exp_ofReal_mul_I_re
  given: (x : Real)
  statement: (exp (x * I)).re = Real.cos x
  proof: by
  simp [exp_mul_I, cos_ofReal_re]

@[simp]

中文:
定理 exp_ofReal_mul_I_re
  条件: (x : 实数)
  结论: (exp (x * I)).re = 实数.cos x
  证明: by
  simp [exp_mul_I, cos_ofReal_re]

@[simp]

Depends on / 依赖: cos_ofReal_re, exp_mul_I
-/
theorem exp_ofReal_mul_I_re (x : Real) : (exp (x * I)).re = Real.cos x := by
  simp [exp_mul_I, cos_ofReal_re]

@[simp]
/--
theorem `exp_ofReal_mul_I_im` / 定理 `exp_ofReal_mul_I_im`

English:
theorem exp_ofReal_mul_I_im
  given: (x : Real)
  statement: (exp (x * I)).im = Real.sin x
  proof: by
  simp [exp_mul_I, sin_ofReal_re]

中文:
定理 exp_ofReal_mul_I_im
  条件: (x : 实数)
  结论: (exp (x * I)).im = 实数.sin x
  证明: by
  simp [exp_mul_I, sin_ofReal_re]

Depends on / 依赖: exp_mul_I, sin_ofReal_re
-/
theorem exp_ofReal_mul_I_im (x : Real) : (exp (x * I)).im = Real.sin x := by
  simp [exp_mul_I, sin_ofReal_re]

/--
theorem `exp_ofReal_mul_I` / 定理 `exp_ofReal_mul_I`

English:
theorem exp_ofReal_mul_I
  given: (x : Real)
  statement: exp (x * I) = Real.cos x + (Real.sin x) * I
  proof: by
  simp [exp_mul_I]

中文:
定理 exp_ofReal_mul_I
  条件: (x : 实数)
  结论: exp (x * I) = 实数.cos x + (实数.sin x) * I
  证明: by
  simp [exp_mul_I]

Depends on / 依赖: exp_mul_I
-/
theorem exp_ofReal_mul_I (x : Real) : exp (x * I) = Real.cos x + (Real.sin x) * I := by
  simp [exp_mul_I]

/--
theorem `cos_add_sin_mul_I_pow` / 定理 `cos_add_sin_mul_I_pow`

English:
theorem cos_add_sin_mul_I_pow
  given: (n : Nat) (z : Complex)
  proof: by
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_nat_mul]; rw [mul_assoc]

中文:
定理 cos_add_sin_mul_I_pow
  条件: (n : 自然数) (z : Complex)
  证明: by
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_nat_mul]; rw [mul_assoc]

Depends on / 依赖: exp_mul_I, exp_nat_mul, mul_assoc
-/
theorem cos_add_sin_mul_I_pow (n : Nat) (z : Complex) :
    (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I := by
  rw [← exp_mul_I]; rw [← exp_mul_I]; rw [← exp_nat_mul]; rw [mul_assoc]

open Finset

/--
theorem `cos_bound` / 定理 `cos_bound`

English:
theorem cos_bound
  given: {x : Complex} (hx : ‖x‖ <= 1)
  statement: ‖cos x - (1 - x ^ 2 / 2)‖ <= ‖x‖ ^ 4 * (5 / 96)
  proof: calc
    ‖cos x - (1 - x ^ 2 / 2)‖ =
        ‖(exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <= ‖exp (-

中文:
定理 cos_bound
  条件: {x : Complex} (hx : ‖x‖ <= 1)
  结论: ‖cos x - (1 - x ^ 2 / 2)‖ <= ‖x‖ ^ 4 * (5 / 96)
  证明: calc
    ‖cos x - (1 - x ^ 2 / 2)‖ =
        ‖(exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <= ‖exp (-

Depends on / 依赖: Finset, Finset.sum_range_succ, I_sq, Nat.factorial, Nat.succ, factorial, m.factorial, norm_add_le, sum_range_succ, two_ne_zero
-/
theorem cos_bound {x : Complex} (hx : ‖x‖ <= 1) : ‖cos x - (1 - x ^ 2 / 2)‖ <= ‖x‖ ^ 4 * (5 / 96) :=
  calc
    ‖cos x - (1 - x ^ 2 / 2)‖ =
        ‖(exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2 +
         (exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2‖ := by
      simp [cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <= ‖exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ <= ‖-x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : Nat) : Real)⁻¹) / 2 +
        ‖x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : Nat) : Real)⁻¹) / 2 := by
      grw [exp_bound (by simpa) (by simp), exp_bound (by simpa) (by simp)]
    _ <= ‖x‖ ^ 4 * (5 / 96) := by norm_num

/--
theorem `sin_bound` / 定理 `sin_bound`

English:
theorem sin_bound
  given: {x : Complex} (hx : ‖x‖ <= 1)
  statement: ‖sin x - (x - x ^ 3 / 6)‖ <= ‖x‖ ^ 5 / 100
  proof: calc
    ‖sin x - (x - x ^ 3 / 6)‖ =
        ‖(exp (-x * I) - ∑ m in range 5, (-x * I) ^ m / m.factorial) * I / 2 -
         (exp (x * I) - ∑ m in range 5, (x * I) ^ m / m.factorial) * I / 2‖ := by
      simp [sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <=

中文:
定理 sin_bound
  条件: {x : Complex} (hx : ‖x‖ <= 1)
  结论: ‖sin x - (x - x ^ 3 / 6)‖ <= ‖x‖ ^ 5 / 100
  证明: calc
    ‖sin x - (x - x ^ 3 / 6)‖ =
        ‖(exp (-x * I) - ∑ m in range 5, (-x * I) ^ m / m.factorial) * I / 2 -
         (exp (x * I) - ∑ m in range 5, (x * I) ^ m / m.factorial) * I / 2‖ := by
      simp [sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <=

Depends on / 依赖: Finset, Finset.sum_range_succ, I_sq, Nat.factorial, Nat.succ, factorial, m.factorial, norm_sub_le, sum_range_succ, two_ne_zero
-/
theorem sin_bound {x : Complex} (hx : ‖x‖ <= 1) : ‖sin x - (x - x ^ 3 / 6)‖ <= ‖x‖ ^ 5 / 100 :=
  calc
    ‖sin x - (x - x ^ 3 / 6)‖ =
        ‖(exp (-x * I) - ∑ m in range 5, (-x * I) ^ m / m.factorial) * I / 2 -
         (exp (x * I) - ∑ m in range 5, (x * I) ^ m / m.factorial) * I / 2‖ := by
      simp [sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [I_sq, two_ne_zero]
    _ <= ‖exp (-x * I) - ∑ m in range 5, (-x * I) ^ m / m.factorial‖ / 2 +
        ‖exp (x * I) - ∑ m in range 5, (x * I) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ <= ‖-x * I‖ ^ 5 * (Nat.succ 5 * (Nat.factorial 5 * (5 : Nat) : Real)⁻¹) / 2 +
        ‖x * I‖ ^ 5 * (Nat.succ 5 * (Nat.factorial 5 * (5 : Nat) : Real)⁻¹) / 2 := by
      grw [exp_bound (by simpa) (by simp), exp_bound (by simpa) (by simp)]
    _ = ‖x‖ ^ 5 / 100 := by norm_num [mul_one_div]

end Complex

namespace Real

open Complex

variable (x y : Real)

@[simp]
/--
theorem `sin_zero` / 定理 `sin_zero`

English:
theorem sin_zero
  statement: sin 0 = 0
  proof: by simp [sin]

@[simp]

中文:
定理 sin_zero
  结论: sin 0 = 0
  证明: by simp [sin]

@[simp]
-/
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
/--
theorem `sin_neg` / 定理 `sin_neg`

English:
theorem sin_neg
  statement: sin (-x) = -sin x
  proof: by simp [sin]

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
ofReal_injective by simp [sin_add]

@[simp]

中文:
定理 sin_neg
  结论: sin (-x) = -sin x
  证明: by simp [sin]

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
ofReal_injective by simp [sin_add]

@[simp]
-/
theorem sin_neg : sin (-x) = -sin x := by simp [sin]

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
ofReal_injective by simp [sin_add]

@[simp]
/--
theorem `cos_zero` / 定理 `cos_zero`

English:
theorem cos_zero
  statement: cos 0 = 1
  proof: by simp [cos]

@[simp]

中文:
定理 cos_zero
  结论: cos 0 = 1
  证明: by simp [cos]

@[simp]
-/
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
/--
theorem `cos_neg` / 定理 `cos_neg`

English:
theorem cos_neg
  statement: cos (-x) = cos x
  proof: by simp [cos]

@[simp]

中文:
定理 cos_neg
  结论: cos (-x) = cos x
  证明: by simp [cos]

@[simp]
-/
theorem cos_neg : cos (-x) = cos x := by simp [cos]

@[simp]
/--
theorem `cos_abs` / 定理 `cos_abs`

English:
theorem cos_abs
  statement: cos |x| = cos x
  proof: by
  cases le_total x 0 <;> simp only [*, abs_of_nonneg, abs_of_nonpos, cos_neg]

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
ofReal_injective by simp [cos_add]

中文:
定理 cos_abs
  结论: cos |x| = cos x
  证明: by
  cases le_total x 0 <;> simp only [*, abs_of_nonneg, abs_of_nonpos, cos_neg]

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
ofReal_injective by simp [cos_add]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, cos_neg, le_total
-/
theorem cos_abs : cos |x| = cos x := by
  cases le_total x 0 <;> simp only [*, abs_of_nonneg, abs_of_nonpos, cos_neg]

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
ofReal_injective by simp [cos_add]

/--
theorem `sin_sub` / 定理 `sin_sub`

English:
theorem sin_sub
  statement: sin (x - y) = sin x * cos y - cos x * sin y
  proof: by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

中文:
定理 sin_sub
  结论: sin (x - y) = sin x * cos y - cos x * sin y
  证明: by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

Depends on / 依赖: cos_neg, sin_add, sin_neg, sub_eq_add_neg
-/
theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

/--
theorem `cos_sub` / 定理 `cos_sub`

English:
theorem cos_sub
  statement: cos (x - y) = cos x * cos y + sin x * sin y
  proof: by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

nonrec theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) :=
ofReal_injective by simp [sin_add_sin]

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
ofReal_injective by simp 

中文:
定理 cos_sub
  结论: cos (x - y) = cos x * cos y + sin x * sin y
  证明: by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

nonrec theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) :=
ofReal_injective by simp [sin_add_sin]

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
ofReal_injective by simp 

Depends on / 依赖: cos_add, cos_neg, sin_neg, sub_eq_add_neg
-/
theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

nonrec theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) :=
ofReal_injective by simp [sin_add_sin]

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
ofReal_injective by simp [sin_sub_sin]

nonrec theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
ofReal_injective by simp [cos_add_cos]

nonrec theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
ofReal_injective by simp [cos_sub_cos]

/--
theorem `two_mul_sin_mul_sin` / 定理 `two_mul_sin_mul_sin`

English:
theorem two_mul_sin_mul_sin
  given: (x y : Real)
  statement: 2 * sin x * sin y = cos (x - y) - cos (x + y)
  proof: by
  simp [cos_add, cos_sub]
  ring

中文:
定理 two_mul_sin_mul_sin
  条件: (x y : 实数)
  结论: 2 * sin x * sin y = cos (x - y) - cos (x + y)
  证明: by
  simp [cos_add, cos_sub]
  ring

Depends on / 依赖: cos_add, cos_sub
-/
theorem two_mul_sin_mul_sin (x y : Real) : 2 * sin x * sin y = cos (x - y) - cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

/--
theorem `two_mul_cos_mul_cos` / 定理 `two_mul_cos_mul_cos`

English:
theorem two_mul_cos_mul_cos
  given: (x y : Real)
  statement: 2 * cos x * cos y = cos (x - y) + cos (x + y)
  proof: by
  simp [cos_add, cos_sub]
  ring

中文:
定理 two_mul_cos_mul_cos
  条件: (x y : 实数)
  结论: 2 * cos x * cos y = cos (x - y) + cos (x + y)
  证明: by
  simp [cos_add, cos_sub]
  ring

Depends on / 依赖: cos_add, cos_sub
-/
theorem two_mul_cos_mul_cos (x y : Real) : 2 * cos x * cos y = cos (x - y) + cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

/--
theorem `two_mul_sin_mul_cos` / 定理 `two_mul_sin_mul_cos`

English:
theorem two_mul_sin_mul_cos
  given: (x y : Real)
  statement: 2 * sin x * cos y = sin (x - y) + sin (x + y)
  proof: by
  simp [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
ofReal_injective by simp only [ofReal_tan, tan_eq_sin_div_cos, ofReal_div, ofReal_sin,
    ofReal_cos]

nonrec theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
ofReal_injective by simp [cot_eq_cos_

中文:
定理 two_mul_sin_mul_cos
  条件: (x y : 实数)
  结论: 2 * sin x * cos y = sin (x - y) + sin (x + y)
  证明: by
  simp [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
ofReal_injective by simp only [ofReal_tan, tan_eq_sin_div_cos, ofReal_div, ofReal_sin,
    ofReal_cos]

nonrec theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
ofReal_injective by simp [cot_eq_cos_

Depends on / 依赖: sin_add, sin_sub
-/
theorem two_mul_sin_mul_cos (x y : Real) : 2 * sin x * cos y = sin (x - y) + sin (x + y) := by
  simp [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
ofReal_injective by simp only [ofReal_tan, tan_eq_sin_div_cos, ofReal_div, ofReal_sin,
    ofReal_cos]

nonrec theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
ofReal_injective by simp [cot_eq_cos_div_sin]

/--
theorem `tan_mul_cos` / 定理 `tan_mul_cos`

English:
theorem tan_mul_cos
  given: {x : Real} (hx : cos x != 0)
  statement: tan x * cos x = sin x
  proof: by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]

中文:
定理 tan_mul_cos
  条件: {x : 实数} (hx : cos x != 0)
  结论: tan x * cos x = sin x
  证明: by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]

Depends on / 依赖: tan_eq_sin_div_cos
-/
theorem tan_mul_cos {x : Real} (hx : cos x != 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos]; rw [div_mul_cancel₀ _ hx]

@[simp]
/--
theorem `tan_inv_eq_cot` / 定理 `tan_inv_eq_cot`

English:
theorem tan_inv_eq_cot
  statement: (tan x)⁻¹ = cot x
  proof: ofReal_injective by simp

@[simp]

中文:
定理 tan_inv_eq_cot
  结论: (tan x)⁻¹ = cot x
  证明: ofReal_injective by simp

@[simp]

Depends on / 依赖: ofReal_injective
-/
theorem tan_inv_eq_cot : (tan x)⁻¹ = cot x :=
ofReal_injective by simp

@[simp]
/--
theorem `cot_inv_eq_tan` / 定理 `cot_inv_eq_tan`

English:
theorem cot_inv_eq_tan
  statement: (cot x)⁻¹ = tan x
  proof: ofReal_injective by simp

@[simp]

中文:
定理 cot_inv_eq_tan
  结论: (cot x)⁻¹ = tan x
  证明: ofReal_injective by simp

@[simp]

Depends on / 依赖: ofReal_injective
-/
theorem cot_inv_eq_tan : (cot x)⁻¹ = tan x :=
ofReal_injective by simp

@[simp]
/--
theorem `tan_zero` / 定理 `tan_zero`

English:
theorem tan_zero
  statement: tan 0 = 0
  proof: by simp [tan]

@[simp]

中文:
定理 tan_zero
  结论: tan 0 = 0
  证明: by simp [tan]

@[simp]
-/
theorem tan_zero : tan 0 = 0 := by simp [tan]

@[simp]
/--
theorem `tan_neg` / 定理 `tan_neg`

English:
theorem tan_neg
  statement: tan (-x) = -tan x
  proof: by simp [tan]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])

@[simp]

中文:
定理 tan_neg
  结论: tan (-x) = -tan x
  证明: by simp [tan]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])

@[simp]
-/
theorem tan_neg : tan (-x) = -tan x := by simp [tan]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])

@[simp]
/--
theorem `cos_sq_add_sin_sq` / 定理 `cos_sq_add_sin_sq`

English:
theorem cos_sq_add_sin_sq
  statement: cos x ^ 2 + sin x ^ 2 = 1
  proof: by rw [add_comm, sin_sq_add_cos_sq]

中文:
定理 cos_sq_add_sin_sq
  结论: cos x ^ 2 + sin x ^ 2 = 1
  证明: by rw [add_comm, sin_sq_add_cos_sq]

Depends on / 依赖: add_comm, sin_sq_add_cos_sq
-/
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

/--
theorem `sin_sq_le_one` / 定理 `sin_sq_le_one`

English:
theorem sin_sq_le_one
  statement: sin x ^ 2 <= 1
  proof: by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)

中文:
定理 sin_sq_le_one
  结论: sin x ^ 2 <= 1
  证明: by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)

Depends on / 依赖: le_add_of_nonneg_right, sin_sq_add_cos_sq, sq_nonneg
-/
theorem sin_sq_le_one : sin x ^ 2 <= 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)

/--
theorem `cos_sq_le_one` / 定理 `cos_sq_le_one`

English:
theorem cos_sq_le_one
  statement: cos x ^ 2 <= 1
  proof: by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)

中文:
定理 cos_sq_le_one
  结论: cos x ^ 2 <= 1
  证明: by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)

Depends on / 依赖: le_add_of_nonneg_left, sin_sq_add_cos_sq, sq_nonneg
-/
theorem cos_sq_le_one : cos x ^ 2 <= 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)

/--
theorem `abs_sin_le_one` / 定理 `abs_sin_le_one`

English:
theorem abs_sin_le_one
  statement: |sin x| <= 1
  proof: abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, sin_sq_le_one]

中文:
定理 abs_sin_le_one
  结论: |sin x| <= 1
  证明: abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, sin_sq_le_one]

Depends on / 依赖: abs_le_one_iff_mul_self_le_one, sin_sq_le_one
-/
theorem abs_sin_le_one : |sin x| <= 1 :=
abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, sin_sq_le_one]

/--
theorem `abs_cos_le_one` / 定理 `abs_cos_le_one`

English:
theorem abs_cos_le_one
  statement: |cos x| <= 1
  proof: abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, cos_sq_le_one]

中文:
定理 abs_cos_le_one
  结论: |cos x| <= 1
  证明: abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, cos_sq_le_one]

Depends on / 依赖: abs_le_one_iff_mul_self_le_one, cos_sq_le_one
-/
theorem abs_cos_le_one : |cos x| <= 1 :=
abs_le_one_iff_mul_self_le_one.2 by simp only [← sq, cos_sq_le_one]

/--
theorem `sin_le_one` / 定理 `sin_le_one`

English:
theorem sin_le_one
  statement: sin x <= 1
  proof: (abs_le.1 (abs_sin_le_one _)).2

中文:
定理 sin_le_one
  结论: sin x <= 1
  证明: (abs_le.1 (abs_sin_le_one _)).2

Depends on / 依赖: abs_le, abs_sin_le_one
-/
theorem sin_le_one : sin x <= 1 :=
  (abs_le.1 (abs_sin_le_one _)).2

/--
theorem `cos_le_one` / 定理 `cos_le_one`

English:
theorem cos_le_one
  statement: cos x <= 1
  proof: (abs_le.1 (abs_cos_le_one _)).2

中文:
定理 cos_le_one
  结论: cos x <= 1
  证明: (abs_le.1 (abs_cos_le_one _)).2

Depends on / 依赖: abs_cos_le_one, abs_le
-/
theorem cos_le_one : cos x <= 1 :=
  (abs_le.1 (abs_cos_le_one _)).2

/--
theorem `neg_one_le_sin` / 定理 `neg_one_le_sin`

English:
theorem neg_one_le_sin
  statement: -1 <= sin x
  proof: (abs_le.1 (abs_sin_le_one _)).1

中文:
定理 neg_one_le_sin
  结论: -1 <= sin x
  证明: (abs_le.1 (abs_sin_le_one _)).1

Depends on / 依赖: abs_le, abs_sin_le_one
-/
theorem neg_one_le_sin : -1 <= sin x :=
  (abs_le.1 (abs_sin_le_one _)).1

/--
theorem `neg_one_le_cos` / 定理 `neg_one_le_cos`

English:
theorem neg_one_le_cos
  statement: -1 <= cos x
  proof: (abs_le.1 (abs_cos_le_one _)).1

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
ofReal_injective by simp [cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
ofReal_injective by simp [cos_two_mul']

nonrec theorem cos_two_mul_eq_one_sub : cos (2 * x) =

中文:
定理 neg_one_le_cos
  结论: -1 <= cos x
  证明: (abs_le.1 (abs_cos_le_one _)).1

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
ofReal_injective by simp [cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
ofReal_injective by simp [cos_two_mul']

nonrec theorem cos_two_mul_eq_one_sub : cos (2 * x) =

Depends on / 依赖: abs_cos_le_one, abs_le
-/
theorem neg_one_le_cos : -1 <= cos x :=
  (abs_le.1 (abs_cos_le_one _)).1

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
ofReal_injective by simp [cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
ofReal_injective by simp [cos_two_mul']

nonrec theorem cos_two_mul_eq_one_sub : cos (2 * x) = 1 - 2 * sin x ^ 2 :=
ofReal_injective by simp [cos_two_mul_eq_one_sub]

nonrec theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
ofReal_injective by simp [sin_two_mul]

nonrec theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
ofReal_injective by simp [cos_sq]

/--
theorem `cos_sq'` / 定理 `cos_sq'`

English:
theorem cos_sq'
  statement: cos x ^ 2 = 1 - sin x ^ 2
  proof: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

中文:
定理 cos_sq'
  结论: cos x ^ 2 = 1 - sin x ^ 2
  证明: by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, sin_sq_add_cos_sq
-/
theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

/--
theorem `sin_sq` / 定理 `sin_sq`

English:
theorem sin_sq
  statement: sin x ^ 2 = 1 - cos x ^ 2
  proof: eq_sub_iff_add_eq.2 sin_sq_add_cos_sq _

中文:
定理 sin_sq
  结论: sin x ^ 2 = 1 - cos x ^ 2
  证明: eq_sub_iff_add_eq.2 sin_sq_add_cos_sq _

Depends on / 依赖: eq_sub_iff_add_eq, sin_sq_add_cos_sq
-/
theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
eq_sub_iff_add_eq.2 sin_sq_add_cos_sq _

/--
lemma `sin_sq_eq_half_sub` / 引理 `sin_sq_eq_half_sub`

English:
lemma sin_sq_eq_half_sub
  statement: sin x ^ 2 = 1 / 2 - cos (2 * x) / 2
  proof: by
  rw [sin_sq]; rw [cos_sq]; rw [← sub_sub]; rw [sub_half]

中文:
引理 sin_sq_eq_half_sub
  结论: sin x ^ 2 = 1 / 2 - cos (2 * x) / 2
  证明: by
  rw [sin_sq]; rw [cos_sq]; rw [← sub_sub]; rw [sub_half]

Depends on / 依赖: cos_sq, sin_sq, sub_half, sub_sub
-/
lemma sin_sq_eq_half_sub : sin x ^ 2 = 1 / 2 - cos (2 * x) / 2 := by
  rw [sin_sq]; rw [cos_sq]; rw [← sub_sub]; rw [sub_half]

/--
theorem `abs_sin_eq_sqrt_one_sub_cos_sq` / 定理 `abs_sin_eq_sqrt_one_sub_cos_sq`

English:
theorem abs_sin_eq_sqrt_one_sub_cos_sq
  given: (x : Real)
  statement: |sin x| = √(1 - cos x ^ 2)
  proof: by
  rw [← sin_sq]; rw [sqrt_sq_eq_abs]

中文:
定理 abs_sin_eq_sqrt_one_sub_cos_sq
  条件: (x : 实数)
  结论: |sin x| = √(1 - cos x ^ 2)
  证明: by
  rw [← sin_sq]; rw [sqrt_sq_eq_abs]

Depends on / 依赖: sin_sq, sqrt_sq_eq_abs
-/
theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : Real) : |sin x| = √(1 - cos x ^ 2) := by
  rw [← sin_sq]; rw [sqrt_sq_eq_abs]

/--
theorem `abs_cos_eq_sqrt_one_sub_sin_sq` / 定理 `abs_cos_eq_sqrt_one_sub_sin_sq`

English:
theorem abs_cos_eq_sqrt_one_sub_sin_sq
  given: (x : Real)
  statement: |cos x| = √(1 - sin x ^ 2)
  proof: by
  rw [← cos_sq']; rw [sqrt_sq_eq_abs]

中文:
定理 abs_cos_eq_sqrt_one_sub_sin_sq
  条件: (x : 实数)
  结论: |cos x| = √(1 - sin x ^ 2)
  证明: by
  rw [← cos_sq']; rw [sqrt_sq_eq_abs]

Depends on / 依赖: cos_sq, sqrt_sq_eq_abs
-/
theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : Real) : |cos x| = √(1 - sin x ^ 2) := by
  rw [← cos_sq']; rw [sqrt_sq_eq_abs]

/--
theorem `one_add_tan_sq_mul_cos_sq_eq_one` / 定理 `one_add_tan_sq_mul_cos_sq_eq_one`

English:
theorem one_add_tan_sq_mul_cos_sq_eq_one
  given: {x : Real} (h : cos x != 0)
  proof: mod_cast @Complex.one_add_tan_sq_mul_cos_sq_eq_one x (mod_cast h)

中文:
定理 one_add_tan_sq_mul_cos_sq_eq_one
  条件: {x : 实数} (h : cos x != 0)
  证明: mod_cast @Complex.one_add_tan_sq_mul_cos_sq_eq_one x (mod_cast h)

Depends on / 依赖: Complex.one_add_tan_sq_mul_cos_sq_eq_one, mod_cast, one_add_tan_sq_mul_cos_sq_eq_one
-/
theorem one_add_tan_sq_mul_cos_sq_eq_one {x : Real} (h : cos x != 0) :
    (1 + tan x ^ 2) * cos x ^ 2 = 1 :=
  mod_cast @Complex.one_add_tan_sq_mul_cos_sq_eq_one x (mod_cast h)

/--
theorem `inv_one_add_tan_sq` / 定理 `inv_one_add_tan_sq`

English:
theorem inv_one_add_tan_sq
  given: {x : Real} (hx : cos x != 0)
  statement: (1 + tan x ^ 2)⁻¹ = cos x ^ 2
  proof: have : Complex.cos x != 0 := mt (congr_arg re) hx
ofReal_inj.1 by simpa using Complex.inv_one_add_tan_sq this

中文:
定理 inv_one_add_tan_sq
  条件: {x : 实数} (hx : cos x != 0)
  结论: (1 + tan x ^ 2)⁻¹ = cos x ^ 2
  证明: have : Complex.cos x != 0 := mt (congr_arg re) hx
ofReal_inj.1 by simpa using Complex.inv_one_add_tan_sq this

Depends on / 依赖: Complex.cos, Complex.inv_one_add_tan_sq, congr_arg, inv_one_add_tan_sq, ofReal_inj
-/
theorem inv_one_add_tan_sq {x : Real} (hx : cos x != 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have : Complex.cos x != 0 := mt (congr_arg re) hx
ofReal_inj.1 by simpa using Complex.inv_one_add_tan_sq this

/--
theorem `tan_sq_div_one_add_tan_sq` / 定理 `tan_sq_div_one_add_tan_sq`

English:
theorem tan_sq_div_one_add_tan_sq
  given: {x : Real} (hx : cos x != 0)
  proof: by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

中文:
定理 tan_sq_div_one_add_tan_sq
  条件: {x : 实数} (hx : cos x != 0)
  证明: by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, inv_one_add_tan_sq, mul_pow, tan_mul_cos
-/
theorem tan_sq_div_one_add_tan_sq {x : Real} (hx : cos x != 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

/--
theorem `inv_sqrt_one_add_tan_sq` / 定理 `inv_sqrt_one_add_tan_sq`

English:
theorem inv_sqrt_one_add_tan_sq
  given: {x : Real} (hx : 0 < cos x)
  statement: (√(1 + tan x ^ 2))⁻¹ = cos x
  proof: by
  rw [← sqrt_sq hx.le]; rw [← sqrt_inv]; rw [inv_one_add_tan_sq hx.ne']

中文:
定理 inv_sqrt_one_add_tan_sq
  条件: {x : 实数} (hx : 0 < cos x)
  结论: (√(1 + tan x ^ 2))⁻¹ = cos x
  证明: by
  rw [← sqrt_sq hx.le]; rw [← sqrt_inv]; rw [inv_one_add_tan_sq hx.ne']

Depends on / 依赖: hx.le, hx.ne, inv_one_add_tan_sq, sqrt_inv, sqrt_sq
-/
theorem inv_sqrt_one_add_tan_sq {x : Real} (hx : 0 < cos x) : (√(1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← sqrt_sq hx.le]; rw [← sqrt_inv]; rw [inv_one_add_tan_sq hx.ne']

/--
theorem `tan_div_sqrt_one_add_tan_sq` / 定理 `tan_div_sqrt_one_add_tan_sq`

English:
theorem tan_div_sqrt_one_add_tan_sq
  given: {x : Real} (hx : 0 < cos x)
  proof: by
  rw [← tan_mul_cos hx.ne']; rw [← inv_sqrt_one_add_tan_sq hx]; rw [div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_

中文:
定理 tan_div_sqrt_one_add_tan_sq
  条件: {x : 实数} (hx : 0 < cos x)
  证明: by
  rw [← tan_mul_cos hx.ne']; rw [← inv_sqrt_one_add_tan_sq hx]; rw [div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_

Depends on / 依赖: div_eq_mul_inv, hx.ne, inv_sqrt_one_add_tan_sq, tan_mul_cos
-/
theorem tan_div_sqrt_one_add_tan_sq {x : Real} (hx : 0 < cos x) :
    tan x / √(1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne']; rw [← inv_sqrt_one_add_tan_sq hx]; rw [div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_inj]; simp [sin_three_mul]

/-- The definition of `sinh` in terms of `exp`. -/
nonrec theorem sinh_eq (x : Real) : sinh x = (exp x - exp (-x)) / 2 :=
ofReal_injective by simp [Complex.sinh]

@[simp]
/--
theorem `sinh_zero` / 定理 `sinh_zero`

English:
theorem sinh_zero
  statement: sinh 0 = 0
  proof: by simp [sinh]

@[simp]

中文:
定理 sinh_zero
  结论: sinh 0 = 0
  证明: by simp [sinh]

@[simp]
-/
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
/--
theorem `sinh_neg` / 定理 `sinh_neg`

English:
theorem sinh_neg
  statement: sinh (-x) = -sinh x
  proof: by simp [sinh]

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]

中文:
定理 sinh_neg
  结论: sinh (-x) = -sinh x
  证明: by simp [sinh]

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]
-/
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh]

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]

/--
theorem `cosh_eq` / 定理 `cosh_eq`

English:
theorem cosh_eq
  given: (x : Real)
  statement: cosh x = (exp x + exp (-x)) / 2
  proof: eq_div_of_mul_eq two_ne_zero by
    rw [cosh]; rw [exp]; rw [exp]; rw [Complex.ofReal_neg]; rw [Complex.cosh]; rw [mul_two]; rw [← Complex.add_re]; rw [← mul_two]; rw [div_mul_cancel₀ _ (two_ne_zero' Complex)]; rw [Complex.add_re]

@[simp]

中文:
定理 cosh_eq
  条件: (x : 实数)
  结论: cosh x = (exp x + exp (-x)) / 2
  证明: eq_div_of_mul_eq two_ne_zero by
    rw [cosh]; rw [exp]; rw [exp]; rw [Complex.ofReal_neg]; rw [Complex.cosh]; rw [mul_two]; rw [← Complex.add_re]; rw [← mul_two]; rw [div_mul_cancel₀ _ (two_ne_zero' Complex)]; rw [Complex.add_re]

@[simp]

Depends on / 依赖: Complex.add_re, Complex.cosh, Complex.ofReal_neg, add_re, eq_div_of_mul_eq, mul_two, ofReal_neg, two_ne_zero
-/
theorem cosh_eq (x : Real) : cosh x = (exp x + exp (-x)) / 2 :=
eq_div_of_mul_eq two_ne_zero by
    rw [cosh]; rw [exp]; rw [exp]; rw [Complex.ofReal_neg]; rw [Complex.cosh]; rw [mul_two]; rw [← Complex.add_re]; rw [← mul_two]; rw [div_mul_cancel₀ _ (two_ne_zero' Complex)]; rw [Complex.add_re]

@[simp]
/--
theorem `cosh_zero` / 定理 `cosh_zero`

English:
theorem cosh_zero
  statement: cosh 0 = 1
  proof: by simp [cosh]

@[simp]

中文:
定理 cosh_zero
  结论: cosh 0 = 1
  证明: by simp [cosh]

@[simp]
-/
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
/--
theorem `cosh_neg` / 定理 `cosh_neg`

English:
theorem cosh_neg
  statement: cosh (-x) = cosh x
  proof: ofReal_inj.1 by simp

@[simp]

中文:
定理 cosh_neg
  结论: cosh (-x) = cosh x
  证明: ofReal_inj.1 by simp

@[simp]

Depends on / 依赖: ofReal_inj
-/
theorem cosh_neg : cosh (-x) = cosh x :=
ofReal_inj.1 by simp

@[simp]
/--
theorem `cosh_abs` / 定理 `cosh_abs`

English:
theorem cosh_abs
  statement: cosh |x| = cosh x
  proof: by
  cases le_total x 0 <;> simp [*, abs_of_nonneg, abs_of_nonpos]

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]

中文:
定理 cosh_abs
  结论: cosh |x| = cosh x
  证明: by
  cases le_total x 0 <;> simp [*, abs_of_nonneg, abs_of_nonpos]

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_total
-/
theorem cosh_abs : cosh |x| = cosh x := by
  cases le_total x 0 <;> simp [*, abs_of_nonneg, abs_of_nonpos]

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]

/--
theorem `sinh_sub` / 定理 `sinh_sub`

English:
theorem sinh_sub
  statement: sinh (x - y) = sinh x * cosh y - cosh x * sinh y
  proof: by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

中文:
定理 sinh_sub
  结论: sinh (x - y) = sinh x * cosh y - cosh x * sinh y
  证明: by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

Depends on / 依赖: cosh_neg, sinh_add, sinh_neg, sub_eq_add_neg
-/
theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

/--
theorem `cosh_sub` / 定理 `cosh_sub`

English:
theorem cosh_sub
  statement: cosh (x - y) = cosh x * cosh y - sinh x * sinh y
  proof: by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
ofReal_inj.1 by simp [tanh_eq_sinh_div_cosh]

中文:
定理 cosh_sub
  结论: cosh (x - y) = cosh x * cosh y - sinh x * sinh y
  证明: by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
ofReal_inj.1 by simp [tanh_eq_sinh_div_cosh]

Depends on / 依赖: cosh_add, cosh_neg, sinh_neg, sub_eq_add_neg
-/
theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
ofReal_inj.1 by simp [tanh_eq_sinh_div_cosh]

/--
theorem `tanh_eq` / 定理 `tanh_eq`

English:
theorem tanh_eq
  given: (x : Real)
  statement: tanh x = (exp x - exp (-x)) / (exp x + exp (-x))
  proof: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_eq]; rw [cosh_eq]; rw [div_div_div_cancel_right₀ two_ne_zero]

@[simp]

中文:
定理 tanh_eq
  条件: (x : 实数)
  结论: tanh x = (exp x - exp (-x)) / (exp x + exp (-x))
  证明: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_eq]; rw [cosh_eq]; rw [div_div_div_cancel_right₀ two_ne_zero]

@[simp]

Depends on / 依赖: cosh_eq, sinh_eq, tanh_eq_sinh_div_cosh, two_ne_zero
-/
theorem tanh_eq (x : Real) : tanh x = (exp x - exp (-x)) / (exp x + exp (-x)) := by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_eq]; rw [cosh_eq]; rw [div_div_div_cancel_right₀ two_ne_zero]

@[simp]
/--
theorem `tanh_zero` / 定理 `tanh_zero`

English:
theorem tanh_zero
  statement: tanh 0 = 0
  proof: by simp [tanh]

@[simp]

中文:
定理 tanh_zero
  结论: tanh 0 = 0
  证明: by simp [tanh]

@[simp]
-/
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
/--
theorem `tanh_neg` / 定理 `tanh_neg`

English:
theorem tanh_neg
  statement: tanh (-x) = -tanh x
  proof: by simp [tanh]

@[simp]

中文:
定理 tanh_neg
  结论: tanh (-x) = -tanh x
  证明: by simp [tanh]

@[simp]
-/
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh]

@[simp]
/--
theorem `cosh_add_sinh` / 定理 `cosh_add_sinh`

English:
theorem cosh_add_sinh
  statement: cosh x + sinh x = exp x
  proof: by rw [← ofReal_inj]; simp

@[simp]

中文:
定理 cosh_add_sinh
  结论: cosh x + sinh x = exp x
  证明: by rw [← ofReal_inj]; simp

@[simp]

Depends on / 依赖: ofReal_inj
-/
theorem cosh_add_sinh : cosh x + sinh x = exp x := by rw [← ofReal_inj]; simp

@[simp]
/--
theorem `sinh_add_cosh` / 定理 `sinh_add_cosh`

English:
theorem sinh_add_cosh
  statement: sinh x + cosh x = exp x
  proof: by rw [add_comm, cosh_add_sinh]

@[simp]

中文:
定理 sinh_add_cosh
  结论: sinh x + cosh x = exp x
  证明: by rw [add_comm, cosh_add_sinh]

@[simp]

Depends on / 依赖: add_comm, cosh_add_sinh
-/
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
/--
theorem `exp_sub_cosh` / 定理 `exp_sub_cosh`

English:
theorem exp_sub_cosh
  statement: exp x - cosh x = sinh x
  proof: sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]

中文:
定理 exp_sub_cosh
  结论: exp x - cosh x = sinh x
  证明: sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]

Depends on / 依赖: sinh_add_cosh, sub_eq_iff_eq_add
-/
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
/--
theorem `exp_sub_sinh` / 定理 `exp_sub_sinh`

English:
theorem exp_sub_sinh
  statement: exp x - sinh x = cosh x
  proof: sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]

中文:
定理 exp_sub_sinh
  结论: exp x - sinh x = cosh x
  证明: sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]

Depends on / 依赖: cosh_add_sinh, sub_eq_iff_eq_add
-/
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
/--
theorem `cosh_sub_sinh` / 定理 `cosh_sub_sinh`

English:
theorem cosh_sub_sinh
  statement: cosh x - sinh x = exp (-x)
  proof: by
  rw [← ofReal_inj]
  simp

@[simp]

中文:
定理 cosh_sub_sinh
  结论: cosh x - sinh x = exp (-x)
  证明: by
  rw [← ofReal_inj]
  simp

@[simp]

Depends on / 依赖: ofReal_inj
-/
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← ofReal_inj]
  simp

@[simp]
/--
theorem `sinh_sub_cosh` / 定理 `sinh_sub_cosh`

English:
theorem sinh_sub_cosh
  statement: sinh x - cosh x = -exp (-x)
  proof: by rw [← neg_sub, cosh_sub_sinh]

@[simp]

中文:
定理 sinh_sub_cosh
  结论: sinh x - cosh x = -exp (-x)
  证明: by rw [← neg_sub, cosh_sub_sinh]

@[simp]

Depends on / 依赖: cosh_sub_sinh, neg_sub
-/
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
/--
theorem `cosh_sq_sub_sinh_sq` / 定理 `cosh_sq_sub_sinh_sq`

English:
theorem cosh_sq_sub_sinh_sq
  given: (x : Real)
  statement: cosh x ^ 2 - sinh x ^ 2 = 1
  proof: by rw [← ofReal_inj]; simp

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]

中文:
定理 cosh_sq_sub_sinh_sq
  条件: (x : 实数)
  结论: cosh x ^ 2 - sinh x ^ 2 = 1
  证明: by rw [← ofReal_inj]; simp

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]

Depends on / 依赖: ofReal_inj
-/
theorem cosh_sq_sub_sinh_sq (x : Real) : cosh x ^ 2 - sinh x ^ 2 = 1 := by rw [← ofReal_inj]; simp

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]

/--
theorem `cosh_sq'` / 定理 `cosh_sq'`

English:
theorem cosh_sq'
  statement: cosh x ^ 2 = 1 + sinh x ^ 2
  proof: (cosh_sq x).trans (add_comm _ _)

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x

中文:
定理 cosh_sq'
  结论: cosh x ^ 2 = 1 + sinh x ^ 2
  证明: (cosh_sq x).trans (add_comm _ _)

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x

Depends on / 依赖: add_comm, cosh_sq
-/
theorem cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
  (cosh_sq x).trans (add_comm _ _)

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [← ofReal_inj]; simp [sinh_two_mul]

nonrec theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  rw [← ofReal_inj]; simp [cosh_three_mul]

nonrec theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  rw [← ofReal_inj]; simp [sinh_three_mul]

open IsAbsoluteValue Nat

/--
theorem `cosh_pos` / 定理 `cosh_pos`

English:
theorem cosh_pos
  given: (x : Real)
  statement: 0 < Real.cosh x
  proof: (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

中文:
定理 cosh_pos
  条件: (x : 实数)
  结论: 0 < 实数.cosh x
  证明: (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

Depends on / 依赖: add_pos, cosh_eq, exp_pos, half_pos
-/
theorem cosh_pos (x : Real) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

/--
theorem `sinh_lt_cosh` / 定理 `sinh_lt_cosh`

English:
theorem sinh_lt_cosh
  statement: sinh x < cosh x
  proof: lt_of_pow_lt_pow_left₀ 2 (cosh_pos _).le (cosh_sq x).symm ▸ lt_add_one _

中文:
定理 sinh_lt_cosh
  结论: sinh x < cosh x
  证明: lt_of_pow_lt_pow_left₀ 2 (cosh_pos _).le (cosh_sq x).symm ▸ lt_add_one _

Depends on / 依赖: cosh_pos, cosh_sq, lt_add_one
-/
theorem sinh_lt_cosh : sinh x < cosh x :=
lt_of_pow_lt_pow_left₀ 2 (cosh_pos _).le (cosh_sq x).symm ▸ lt_add_one _

/--
theorem `tanh_lt_one` / 定理 `tanh_lt_one`

English:
theorem tanh_lt_one
  given: (x : Real)
  statement: tanh x < 1
  proof: by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

中文:
定理 tanh_lt_one
  条件: (x : 实数)
  结论: tanh x < 1
  证明: by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

Depends on / 依赖: exp_pos, tanh_eq
-/
theorem tanh_lt_one (x : Real) : tanh x < 1 := by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

/--
theorem `neg_one_lt_tanh` / 定理 `neg_one_lt_tanh`

English:
theorem neg_one_lt_tanh
  given: (x : Real)
  statement: -1 < tanh x
  proof: by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

中文:
定理 neg_one_lt_tanh
  条件: (x : 实数)
  结论: -1 < tanh x
  证明: by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

Depends on / 依赖: exp_pos, tanh_eq
-/
theorem neg_one_lt_tanh (x : Real) : -1 < tanh x := by
  rw [tanh_eq]
  field_simp
  grind [exp_pos]

/--
theorem `abs_tanh_lt_one` / 定理 `abs_tanh_lt_one`

English:
theorem abs_tanh_lt_one
  given: (x : Real)
  statement: |tanh x| < 1
  proof: abs_lt.mpr ⟨neg_one_lt_tanh x, tanh_lt_one x⟩

中文:
定理 abs_tanh_lt_one
  条件: (x : 实数)
  结论: |tanh x| < 1
  证明: abs_lt.mpr ⟨neg_one_lt_tanh x, tanh_lt_one x⟩

Depends on / 依赖: abs_lt, abs_lt.mpr, neg_one_lt_tanh, tanh_lt_one
-/
theorem abs_tanh_lt_one (x : Real) : |tanh x| < 1 :=
  abs_lt.mpr ⟨neg_one_lt_tanh x, tanh_lt_one x⟩

/--
theorem `tanh_sq_lt_one` / 定理 `tanh_sq_lt_one`

English:
theorem tanh_sq_lt_one
  given: (x : Real)
  statement: (tanh x) ^ 2 < 1
  proof: (sq_lt_one_iff_abs_lt_one (tanh x)).mpr (abs_tanh_lt_one x)

中文:
定理 tanh_sq_lt_one
  条件: (x : 实数)
  结论: (tanh x) ^ 2 < 1
  证明: (sq_lt_one_iff_abs_lt_one (tanh x)).mpr (abs_tanh_lt_one x)

Depends on / 依赖: abs_tanh_lt_one, sq_lt_one_iff_abs_lt_one
-/
theorem tanh_sq_lt_one (x : Real) : (tanh x) ^ 2 < 1 :=
  (sq_lt_one_iff_abs_lt_one (tanh x)).mpr (abs_tanh_lt_one x)

end Real

namespace Real

open Complex

/--
theorem `cos_bound` / 定理 `cos_bound`

English:
theorem cos_bound
  given: {x : Real} (hx : |x| <= 1)
  statement: |cos x - (1 - x ^ 2 / 2)| <= |x| ^ 4 * (5 / 96)
  proof: by
  simpa [← ofReal_cos, ← norm_eq_abs, ← norm_real] using Complex.cos_bound (x := x) (by simpa)

中文:
定理 cos_bound
  条件: {x : 实数} (hx : |x| <= 1)
  结论: |cos x - (1 - x ^ 2 / 2)| <= |x| ^ 4 * (5 / 96)
  证明: by
  simpa [← ofReal_cos, ← norm_eq_abs, ← norm_real] using Complex.cos_bound (x := x) (by simpa)

Depends on / 依赖: Complex.cos_bound, cos_bound, norm_eq_abs, norm_real, ofReal_cos
-/
theorem cos_bound {x : Real} (hx : |x| <= 1) : |cos x - (1 - x ^ 2 / 2)| <= |x| ^ 4 * (5 / 96) := by
  simpa [← ofReal_cos, ← norm_eq_abs, ← norm_real] using Complex.cos_bound (x := x) (by simpa)

/--
theorem `sin_bound` / 定理 `sin_bound`

English:
theorem sin_bound
  given: {x : Real} (hx : |x| <= 1)
  statement: |sin x - (x - x ^ 3 / 6)| <= |x| ^ 5 / 100
  proof: by
  simpa [← ofReal_sin, ← norm_eq_abs, ← norm_real] using Complex.sin_bound (x := x) (by simpa)

中文:
定理 sin_bound
  条件: {x : 实数} (hx : |x| <= 1)
  结论: |sin x - (x - x ^ 3 / 6)| <= |x| ^ 5 / 100
  证明: by
  simpa [← ofReal_sin, ← norm_eq_abs, ← norm_real] using Complex.sin_bound (x := x) (by simpa)

Depends on / 依赖: Complex.sin_bound, norm_eq_abs, norm_real, ofReal_sin, sin_bound
-/
theorem sin_bound {x : Real} (hx : |x| <= 1) : |sin x - (x - x ^ 3 / 6)| <= |x| ^ 5 / 100 := by
  simpa [← ofReal_sin, ← norm_eq_abs, ← norm_real] using Complex.sin_bound (x := x) (by simpa)

/--
theorem `cos_pos_of_le_one` / 定理 `cos_pos_of_le_one`

English:
theorem cos_pos_of_le_one
  given: {x : Real} (hx : |x| <= 1)
  statement: 0 < cos x
  proof: calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
sub_pos.2
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 <= 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one₀ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, a

中文:
定理 cos_pos_of_le_one
  条件: {x : 实数} (hx : |x| <= 1)
  结论: 0 < cos x
  证明: calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
sub_pos.2
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 <= 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one₀ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, a

Depends on / 依赖: abs_mul, abs_mul_self, abs_nonneg, abs_sub_le_iff, cos_bound, lt_sub_iff_add_lt, sub_le_comm, sub_pos
-/
theorem cos_pos_of_le_one {x : Real} (hx : |x| <= 1) : 0 < cos x :=
  calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
sub_pos.2
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 <= 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one₀ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, abs_mul]
                    exact mul_le_one₀ hx (abs_nonneg _) hx
            _ < 1 := by norm_num)
    _ <= cos x := sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2

/--
theorem `sin_pos_of_pos_of_le_one` / 定理 `sin_pos_of_pos_of_le_one`

English:
theorem sin_pos_of_pos_of_le_one
  given: {x : Real} (hx0 : 0 < x) (hx : x <= 1)
  statement: 0 < sin x
  proof: by
  calc 0 < x - x ^ 3 / 6 - |x| ^ 5 / 100 := by grind [pow_le_of_le_one]
    _ <= sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [abs_of_nonneg (le_of_lt hx0)]))).2

中文:
定理 sin_pos_of_pos_of_le_one
  条件: {x : 实数} (hx0 : 0 < x) (hx : x <= 1)
  结论: 0 < sin x
  证明: by
  calc 0 < x - x ^ 3 / 6 - |x| ^ 5 / 100 := by grind [pow_le_of_le_one]
    _ <= sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [abs_of_nonneg (le_of_lt hx0)]))).2

Depends on / 依赖: abs_of_nonneg, abs_sub_le_iff, le_of_lt, pow_le_of_le_one, sin_bound, sub_le_comm
-/
theorem sin_pos_of_pos_of_le_one {x : Real} (hx0 : 0 < x) (hx : x <= 1) : 0 < sin x := by
  calc 0 < x - x ^ 3 / 6 - |x| ^ 5 / 100 := by grind [pow_le_of_le_one]
    _ <= sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [abs_of_nonneg (le_of_lt hx0)]))).2

/--
theorem `sin_pos_of_pos_of_le_two` / 定理 `sin_pos_of_pos_of_le_two`

English:
theorem sin_pos_of_pos_of_le_two
  given: {x : Real} (hx0 : 0 < x) (hx : x <= 2)
  statement: 0 < sin x
  proof: have : x / 2 <= 1 := (div_le_iff₀ (by simp)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by simp) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_tw

中文:
定理 sin_pos_of_pos_of_le_two
  条件: {x : 实数} (hx0 : 0 < x) (hx : x <= 2)
  结论: 0 < sin x
  证明: have : x / 2 <= 1 := (div_le_iff₀ (by simp)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by simp) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_tw

Depends on / 依赖: abs_of_nonneg, add_halves, cos_pos_of_le_one, half_pos, le_of_lt, mul_pos, sin_pos_of_pos_of_le_one, sin_two_mul, two_mul
-/
theorem sin_pos_of_pos_of_le_two {x : Real} (hx0 : 0 < x) (hx : x <= 2) : 0 < sin x :=
  have : x / 2 <= 1 := (div_le_iff₀ (by simp)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by simp) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_two_mul, two_mul, add_halves]

/--
theorem `cos_one_le` / 定理 `cos_one_le`

English:
theorem cos_one_le
  statement: cos 1 <= 5 / 9
  proof: calc
    cos 1 <= |(1 : Real)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ <= 5 / 9 := by norm_num

中文:
定理 cos_one_le
  结论: cos 1 <= 5 / 9
  证明: calc
    cos 1 <= |(1 : Real)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ <= 5 / 9 := by norm_num

Depends on / 依赖: abs_sub_le_iff, cos_bound, sub_le_iff_le_add
-/
theorem cos_one_le : cos 1 <= 5 / 9 :=
  calc
    cos 1 <= |(1 : Real)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ <= 5 / 9 := by norm_num

/--
theorem `cos_one_pos` / 定理 `cos_one_pos`

English:
theorem cos_one_pos
  statement: 0 < cos 1
  proof: cos_pos_of_le_one (le_of_eq abs_one)

中文:
定理 cos_one_pos
  结论: 0 < cos 1
  证明: cos_pos_of_le_one (le_of_eq abs_one)

Depends on / 依赖: abs_one, cos_pos_of_le_one, le_of_eq
-/
theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eq abs_one)

/--
theorem `cos_two_neg` / 定理 `cos_two_neg`

English:
theorem cos_two_neg
  statement: cos 2 < 0
  proof: calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := Real.cos_two_mul 1
    _ <= 2 * (5 / 9) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num

中文:
定理 cos_two_neg
  结论: cos 2 < 0
  证明: calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := Real.cos_two_mul 1
    _ <= 2 * (5 / 9) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num

Depends on / 依赖: Real.cos_two_mul, congr_arg, cos_one_le, cos_one_pos, cos_one_pos.le, cos_two_mul, mul_one
-/
theorem cos_two_neg : cos 2 < 0 :=
  calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := Real.cos_two_mul 1
    _ <= 2 * (5 / 9) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.cosh` is always positive. -/
@[positivity Real.cosh _]
meta def evalCosh : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.cosh $a) =>
    assertInstancesCommute
    return .positive q(Real.cosh_pos $a)
  | _, _, _ => throwError "not Real.cosh"

example (x : Real) : 0 < x.cosh := by positivity

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
/--
theorem `norm_cos_add_sin_mul_I` / 定理 `norm_cos_add_sin_mul_I`

English:
theorem norm_cos_add_sin_mul_I
  given: (x : Real)
  statement: ‖cos x + sin x * I‖ = 1
  proof: by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, norm_def, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]

@[simp]

中文:
定理 norm_cos_add_sin_mul_I
  条件: (x : 实数)
  结论: ‖cos x + sin x * I‖ = 1
  证明: by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, norm_def, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]

@[simp]

Depends on / 依赖: Real.sin_sq_add_cos_sq, add_comm, cos_ofReal_re, mul_re, normSq, norm_def, sin_ofReal_re, sin_sq_add_cos_sq
-/
theorem norm_cos_add_sin_mul_I (x : Real) : ‖cos x + sin x * I‖ = 1 := by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, norm_def, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]

@[simp]
/--
theorem `norm_exp_ofReal_mul_I` / 定理 `norm_exp_ofReal_mul_I`

English:
theorem norm_exp_ofReal_mul_I
  given: (x : Real)
  statement: ‖exp (x * I)‖ = 1
  proof: by
  rw [exp_mul_I]; rw [norm_cos_add_sin_mul_I]

@[simp]

中文:
定理 norm_exp_ofReal_mul_I
  条件: (x : 实数)
  结论: ‖exp (x * I)‖ = 1
  证明: by
  rw [exp_mul_I]; rw [norm_cos_add_sin_mul_I]

@[simp]

Depends on / 依赖: exp_mul_I, norm_cos_add_sin_mul_I
-/
theorem norm_exp_ofReal_mul_I (x : Real) : ‖exp (x * I)‖ = 1 := by
  rw [exp_mul_I]; rw [norm_cos_add_sin_mul_I]

@[simp]
/--
theorem `norm_exp_I_mul_ofReal` / 定理 `norm_exp_I_mul_ofReal`

English:
theorem norm_exp_I_mul_ofReal
  given: (x : Real)
  statement: ‖exp (I * x)‖ = 1
  proof: by
  rw [mul_comm]; rw [norm_exp_ofReal_mul_I]

@[simp]

中文:
定理 norm_exp_I_mul_ofReal
  条件: (x : 实数)
  结论: ‖exp (I * x)‖ = 1
  证明: by
  rw [mul_comm]; rw [norm_exp_ofReal_mul_I]

@[simp]

Depends on / 依赖: mul_comm, norm_exp_ofReal_mul_I
-/
theorem norm_exp_I_mul_ofReal (x : Real) : ‖exp (I * x)‖ = 1 := by
  rw [mul_comm]; rw [norm_exp_ofReal_mul_I]

@[simp]
/--
theorem `nnnorm_exp_ofReal_mul_I` / 定理 `nnnorm_exp_ofReal_mul_I`

English:
theorem nnnorm_exp_ofReal_mul_I
  given: (x : Real)
  statement: ‖exp (x * I)‖₊ = 1
  proof: by
  rw [← nnnorm_norm]; rw [norm_exp_ofReal_mul_I]; rw [← NNReal.coe_eq_one]; simp

@[simp]

中文:
定理 nnnorm_exp_ofReal_mul_I
  条件: (x : 实数)
  结论: ‖exp (x * I)‖₊ = 1
  证明: by
  rw [← nnnorm_norm]; rw [norm_exp_ofReal_mul_I]; rw [← NNReal.coe_eq_one]; simp

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_eq_one, coe_eq_one, nnnorm_norm, norm_exp_ofReal_mul_I
-/
theorem nnnorm_exp_ofReal_mul_I (x : Real) : ‖exp (x * I)‖₊ = 1 := by
  rw [← nnnorm_norm]; rw [norm_exp_ofReal_mul_I]; rw [← NNReal.coe_eq_one]; simp

@[simp]
/--
theorem `nnnorm_exp_I_mul_ofReal` / 定理 `nnnorm_exp_I_mul_ofReal`

English:
theorem nnnorm_exp_I_mul_ofReal
  given: (x : Real)
  statement: ‖exp (I * x)‖₊ = 1
  proof: by
  rw [← nnnorm_norm]; rw [norm_exp_I_mul_ofReal]; rw [← NNReal.coe_eq_one]; simp

@[simp]

中文:
定理 nnnorm_exp_I_mul_ofReal
  条件: (x : 实数)
  结论: ‖exp (I * x)‖₊ = 1
  证明: by
  rw [← nnnorm_norm]; rw [norm_exp_I_mul_ofReal]; rw [← NNReal.coe_eq_one]; simp

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_eq_one, coe_eq_one, nnnorm_norm, norm_exp_I_mul_ofReal
-/
theorem nnnorm_exp_I_mul_ofReal (x : Real) : ‖exp (I * x)‖₊ = 1 := by
  rw [← nnnorm_norm]; rw [norm_exp_I_mul_ofReal]; rw [← NNReal.coe_eq_one]; simp

@[simp]
/--
theorem `enorm_exp_ofReal_mul_I` / 定理 `enorm_exp_ofReal_mul_I`

English:
theorem enorm_exp_ofReal_mul_I
  given: (x : Real)
  statement: ‖exp (x * I)‖ₑ = 1
  proof: by
  simp [← ENNReal.toReal_eq_one_iff]

@[simp]

中文:
定理 enorm_exp_ofReal_mul_I
  条件: (x : 实数)
  结论: ‖exp (x * I)‖ₑ = 1
  证明: by
  simp [← ENNReal.toReal_eq_one_iff]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, toReal_eq_one_iff
-/
theorem enorm_exp_ofReal_mul_I (x : Real) : ‖exp (x * I)‖ₑ = 1 := by
  simp [← ENNReal.toReal_eq_one_iff]

@[simp]
/--
theorem `enorm_exp_I_mul_ofReal` / 定理 `enorm_exp_I_mul_ofReal`

English:
theorem enorm_exp_I_mul_ofReal
  given: (x : Real)
  statement: ‖exp (I * x)‖ₑ = 1
  proof: by
  simp [← ENNReal.toReal_eq_one_iff]

中文:
定理 enorm_exp_I_mul_ofReal
  条件: (x : 实数)
  结论: ‖exp (I * x)‖ₑ = 1
  证明: by
  simp [← ENNReal.toReal_eq_one_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, toReal_eq_one_iff
-/
theorem enorm_exp_I_mul_ofReal (x : Real) : ‖exp (I * x)‖ₑ = 1 := by
  simp [← ENNReal.toReal_eq_one_iff]

/--
theorem `norm_exp_I_mul_ofReal_sub_one` / 定理 `norm_exp_I_mul_ofReal_sub_one`

English:
theorem norm_exp_I_mul_ofReal_sub_one
  given: (x : Real)
  statement: ‖exp (I * x) - 1‖ = ‖2 * Real.sin (x / 2)‖
  proof: by
  rw [show ‖2 * Real.sin (x / 2)‖ = ‖2 * sin (x / 2)‖ by norm_cast]; rw [two_sin]
  nth_rw 2 [← one_mul (_ - _), ← exp_zero]
  rw [← neg_add_cancel (x / 2 * I)]; rw [exp_add]; rw [mul_assoc _ _ (_ - _)]; rw [mul_sub]; rw [← exp_add]; rw [← exp_add]; rw [← add_mul]; rw [← add_mul]; norm_cast
  rw 

中文:
定理 norm_exp_I_mul_ofReal_sub_one
  条件: (x : 实数)
  结论: ‖exp (I * x) - 1‖ = ‖2 * 实数.sin (x / 2)‖
  证明: by
  rw [show ‖2 * Real.sin (x / 2)‖ = ‖2 * sin (x / 2)‖ by norm_cast]; rw [two_sin]
  nth_rw 2 [← one_mul (_ - _), ← exp_zero]
  rw [← neg_add_cancel (x / 2 * I)]; rw [exp_add]; rw [mul_assoc _ _ (_ - _)]; rw [mul_sub]; rw [← exp_add]; rw [← exp_add]; rw [← add_mul]; rw [← add_mul]; norm_cast
  rw 

Depends on / 依赖: Complex.norm_mul, Real.sin, add_halves, add_mul, add_neg_cancel, exp_add, exp_zero, mul_assoc, mul_one, mul_sub, neg_add_cancel, neg_mul, norm_I, norm_mul, nth_rw, ofReal, ofReal_zero, one_mul, two_sin, zero_mul
-/
theorem norm_exp_I_mul_ofReal_sub_one (x : Real) : ‖exp (I * x) - 1‖ = ‖2 * Real.sin (x / 2)‖ := by
  rw [show ‖2 * Real.sin (x / 2)‖ = ‖2 * sin (x / 2)‖ by norm_cast]; rw [two_sin]
  nth_rw 2 [← one_mul (_ - _), ← exp_zero]
  rw [← neg_add_cancel (x / 2 * I)]; rw [exp_add]; rw [mul_assoc _ _ (_ - _)]; rw [mul_sub]; rw [← exp_add]; rw [← exp_add]; rw [← add_mul]; rw [← add_mul]; norm_cast
  rw [add_neg_cancel]; rw [ofReal_zero]; rw [zero_mul]; rw [exp_zero]; rw [add_halves]; rw [← neg_mul]; rw [Complex.norm_mul]; rw [norm_I]; rw [mul_one]; rw [Complex.norm_mul]; rw [show -(ofReal (x / 2)) = ofReal (-x / 2) by norm_cast; exact neg_div' 2 x]; rw [norm_exp_ofReal_mul_I]; rw [one_mul]; rw [← norm_neg]; rw [neg_sub]; rw [mul_comm]

/--
theorem `norm_exp` / 定理 `norm_exp`

English:
theorem norm_exp
  given: (z : Complex)
  statement: ‖exp z‖ = Real.exp z.re
  proof: by
  rw [exp_eq_exp_re_mul_sin_add_cos]; rw [Complex.norm_mul]; rw [norm_exp_ofReal]; rw [norm_cos_add_sin_mul_I]; rw [mul_one]

中文:
定理 norm_exp
  条件: (z : Complex)
  结论: ‖exp z‖ = 实数.exp z.re
  证明: by
  rw [exp_eq_exp_re_mul_sin_add_cos]; rw [Complex.norm_mul]; rw [norm_exp_ofReal]; rw [norm_cos_add_sin_mul_I]; rw [mul_one]

Depends on / 依赖: Complex.norm_mul, exp_eq_exp_re_mul_sin_add_cos, mul_one, norm_cos_add_sin_mul_I, norm_exp_ofReal, norm_mul
-/
theorem norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re := by
  rw [exp_eq_exp_re_mul_sin_add_cos]; rw [Complex.norm_mul]; rw [norm_exp_ofReal]; rw [norm_cos_add_sin_mul_I]; rw [mul_one]

/--
theorem `norm_exp_eq_iff_re_eq` / 定理 `norm_exp_eq_iff_re_eq`

English:
theorem norm_exp_eq_iff_re_eq
  given: {x y : Complex}
  statement: ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re
  proof: by
  rw [norm_exp]; rw [norm_exp]; rw [Real.exp_eq_exp]

中文:
定理 norm_exp_eq_iff_re_eq
  条件: {x y : Complex}
  结论: ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re
  证明: by
  rw [norm_exp]; rw [norm_exp]; rw [Real.exp_eq_exp]

Depends on / 依赖: Real.exp_eq_exp, exp_eq_exp, norm_exp
-/
theorem norm_exp_eq_iff_re_eq {x y : Complex} : ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re := by
  rw [norm_exp]; rw [norm_exp]; rw [Real.exp_eq_exp]

end Complex
