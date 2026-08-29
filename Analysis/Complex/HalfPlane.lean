/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Half-planes in ℂ are open

We state that open left, right, upper and lower half-planes in the complex numbers are open sets,
where the bounding value of the real or imaginary part is given by a real or `EReal` `x`.
So this includes the full plane and the empty set for `x = ⊤`/`x = ⊥`.
-/

public section

namespace Complex

/--
lemma `isOpen_re_lt_EReal` / 引理 `isOpen_re_lt_EReal`

English:
lemma isOpen_re_lt_EReal
  given: (x : EReal)
  statement: IsOpen {z : Complex | z.re < x}
  proof: isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

中文:
引理 isOpen_re_lt_E实数
  条件: (x : E实数)
  结论: 是开集 {z : 复形 | z.re < x}
  证明: isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

Depends on / 依赖: EReal.continuous_coe_iff.mpr, continuous_coe_iff, continuous_const, continuous_re, isOpen_lt
-/
lemma isOpen_re_lt_EReal (x : EReal) : IsOpen {z : Complex | z.re < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_re) continuous_const

/--
lemma `isOpen_re_gt_EReal` / 引理 `isOpen_re_gt_EReal`

English:
lemma isOpen_re_gt_EReal
  given: (x : EReal)
  statement: IsOpen {z : Complex | x < z.re}
  proof: isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_re

中文:
引理 isOpen_re_gt_E实数
  条件: (x : E实数)
  结论: 是开集 {z : 复形 | x < z.re}
  证明: isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_re

Depends on / 依赖: EReal.continuous_coe_iff.mpr, continuous_coe_iff, continuous_const, continuous_re, isOpen_lt
-/
lemma isOpen_re_gt_EReal (x : EReal) : IsOpen {z : Complex | x < z.re} :=
isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_re

/--
lemma `isOpen_im_lt_EReal` / 引理 `isOpen_im_lt_EReal`

English:
lemma isOpen_im_lt_EReal
  given: (x : EReal)
  statement: IsOpen {z : Complex | z.im < x}
  proof: isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

中文:
引理 isOpen_im_lt_E实数
  条件: (x : E实数)
  结论: 是开集 {z : 复形 | z.im < x}
  证明: isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

Depends on / 依赖: EReal.continuous_coe_iff.mpr, continuous_coe_iff, continuous_const, continuous_im, isOpen_lt
-/
lemma isOpen_im_lt_EReal (x : EReal) : IsOpen {z : Complex | z.im < x} :=
  isOpen_lt (EReal.continuous_coe_iff.mpr continuous_im) continuous_const

/--
lemma `isOpen_im_gt_EReal` / 引理 `isOpen_im_gt_EReal`

English:
lemma isOpen_im_gt_EReal
  given: (x : EReal)
  statement: IsOpen {z : Complex | x < z.im}
  proof: isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_im

中文:
引理 isOpen_im_gt_E实数
  条件: (x : E实数)
  结论: 是开集 {z : 复形 | x < z.im}
  证明: isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_im

Depends on / 依赖: EReal.continuous_coe_iff.mpr, continuous_coe_iff, continuous_const, continuous_im, isOpen_lt
-/
lemma isOpen_im_gt_EReal (x : EReal) : IsOpen {z : Complex | x < z.im} :=
isOpen_lt continuous_const EReal.continuous_coe_iff.mpr continuous_im

/--
lemma `isOpen_re_lt` / 引理 `isOpen_re_lt`

English:
lemma isOpen_re_lt
  given: (x : Real)
  statement: IsOpen {z : Complex | z.re < x}
  proof: by
  simpa using isOpen_re_lt_EReal x

中文:
引理 isOpen_re_lt
  条件: (x : 实数)
  结论: 是开集 {z : 复形 | z.re < x}
  证明: by
  simpa using isOpen_re_lt_EReal x

Depends on / 依赖: isOpen_re_lt_EReal
-/
lemma isOpen_re_lt (x : Real) : IsOpen {z : Complex | z.re < x} := by
  simpa using isOpen_re_lt_EReal x

/--
lemma `isOpen_re_gt` / 引理 `isOpen_re_gt`

English:
lemma isOpen_re_gt
  given: (x : Real)
  statement: IsOpen {z : Complex | x < z.re}
  proof: by
  simpa using isOpen_re_gt_EReal x

中文:
引理 isOpen_re_gt
  条件: (x : 实数)
  结论: 是开集 {z : 复形 | x < z.re}
  证明: by
  simpa using isOpen_re_gt_EReal x

Depends on / 依赖: isOpen_re_gt_EReal
-/
lemma isOpen_re_gt (x : Real) : IsOpen {z : Complex | x < z.re} := by
  simpa using isOpen_re_gt_EReal x

/--
lemma `isOpen_im_lt` / 引理 `isOpen_im_lt`

English:
lemma isOpen_im_lt
  given: (x : Real)
  statement: IsOpen {z : Complex | z.im < x}
  proof: by
  simpa using isOpen_im_lt_EReal x

中文:
引理 isOpen_im_lt
  条件: (x : 实数)
  结论: 是开集 {z : 复形 | z.im < x}
  证明: by
  simpa using isOpen_im_lt_EReal x

Depends on / 依赖: isOpen_im_lt_EReal
-/
lemma isOpen_im_lt (x : Real) : IsOpen {z : Complex | z.im < x} := by
  simpa using isOpen_im_lt_EReal x

/--
lemma `isOpen_im_gt` / 引理 `isOpen_im_gt`

English:
lemma isOpen_im_gt
  given: (x : Real)
  statement: IsOpen {z : Complex | x < z.im}
  proof: by
  simpa using isOpen_im_gt_EReal x

中文:
引理 isOpen_im_gt
  条件: (x : 实数)
  结论: 是开集 {z : 复形 | x < z.im}
  证明: by
  simpa using isOpen_im_gt_EReal x

Depends on / 依赖: isOpen_im_gt_EReal
-/
lemma isOpen_im_gt (x : Real) : IsOpen {z : Complex | x < z.im} := by
  simpa using isOpen_im_gt_EReal x

end Complex
