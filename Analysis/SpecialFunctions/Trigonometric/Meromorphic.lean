/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

public section

namespace Complex

/--
theorem `meromorphicNFOn_tan` / 定理 `meromorphicNFOn_tan`

English:
theorem meromorphicNFOn_tan
  statement: MeromorphicNFOn tan Set.univ
  proof: by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

中文:
定理 meromorphicNFOn_tan
  结论: MeromorphicNFOn tan 集合.univ
  证明: by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

Depends on / 依赖: MeromorphicNFOn, MeromorphicNFOn.div, analyticAt_cos, analyticAt_cos.meromorphicNFAt, analyticAt_sin, meromorphicNFAt, sin_sq_add_cos_sq
-/
theorem meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

/-- The function `tan` is meromorphic at any `z`. -/
@[fun_prop]
/--
theorem `meromorphicAt_tan` / 定理 `meromorphicAt_tan`

English:
theorem meromorphicAt_tan
  given: (z : Complex)
  statement: MeromorphicAt tan z
  proof: (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

中文:
定理 meromorphicAt_tan
  条件: (z : 复形)
  结论: MeromorphicAt tan z
  证明: (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

Depends on / 依赖: Set.mem_univ, mem_univ, meromorphicAt, meromorphicNFOn_tan
-/
theorem meromorphicAt_tan (z : Complex) : MeromorphicAt tan z :=
  (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

/-- The function `tan` is meromorphic. -/
@[fun_prop]
/--
theorem `meromorphic_tan` / 定理 `meromorphic_tan`

English:
theorem meromorphic_tan
  statement: Meromorphic tan
  proof: meromorphicAt_tan

中文:
定理 meromorphic_tan
  结论: 亚纯 tan
  证明: meromorphicAt_tan

Depends on / 依赖: meromorphicAt_tan
-/
theorem meromorphic_tan : Meromorphic tan := meromorphicAt_tan

/--
theorem `meromorphicNFOn_tanh` / 定理 `meromorphicNFOn_tanh`

English:
theorem meromorphicNFOn_tanh
  statement: MeromorphicNFOn tanh Set.univ
  proof: by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

中文:
定理 meromorphicNFOn_tanh
  结论: MeromorphicNFOn tanh 集合.univ
  证明: by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

Depends on / 依赖: MeromorphicNFOn, MeromorphicNFOn.div, analyticAt_cosh, analyticAt_cosh.meromorphicNFAt, analyticAt_sinh, cosh_sq_sub_sinh_sq, meromorphicNFAt
-/
theorem meromorphicNFOn_tanh : MeromorphicNFOn tanh Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

/-- The function `tanh` is meromorphic at any `z`. -/
@[fun_prop]
/--
theorem `meromorphicAt_tanh` / 定理 `meromorphicAt_tanh`

English:
theorem meromorphicAt_tanh
  given: (z : Complex)
  statement: MeromorphicAt tanh z
  proof: (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

中文:
定理 meromorphicAt_tanh
  条件: (z : 复形)
  结论: MeromorphicAt tanh z
  证明: (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

Depends on / 依赖: Set.mem_univ, mem_univ, meromorphicAt, meromorphicNFOn_tanh
-/
theorem meromorphicAt_tanh (z : Complex) : MeromorphicAt tanh z :=
  (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

/-- The function `tanh` is meromorphic. -/
@[fun_prop]
/--
theorem `meromorphic_tanh` / 定理 `meromorphic_tanh`

English:
theorem meromorphic_tanh
  statement: Meromorphic tanh
  proof: meromorphicAt_tanh

中文:
定理 meromorphic_tanh
  结论: 亚纯 tanh
  证明: meromorphicAt_tanh

Depends on / 依赖: meromorphicAt_tanh
-/
theorem meromorphic_tanh : Meromorphic tanh := meromorphicAt_tanh

end Complex
