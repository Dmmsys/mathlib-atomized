/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Asymptotics.Theta

/-!
# Lemmas about asymptotics and the natural embedding `ℝ → ℂ`

In this file we prove several trivial lemmas about `Asymptotics.IsBigO` etc. and `(↑) : ℝ → ℂ`.
-/

public section

namespace Complex

variable {α E : Type*} [Norm E] {l : Filter α}

/--
theorem `isTheta_ofReal` / 定理 `isTheta_ofReal`

English:
theorem isTheta_ofReal
  given: (f : α -> Real) (l : Filter α)
  statement: (f · : α -> Complex) =Θ[l] f
  proof: .of_norm_left by simpa using (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]

中文:
定理 isTheta_of实数
  条件: (f : α -> 实数) (l : 滤子 α)
  结论: (f · : α -> 复形) =Θ[l] f
  证明: .of_norm_left by simpa using (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]

Depends on / 依赖: Asymptotics, Asymptotics.isTheta_rfl, isTheta_rfl, norm_left, of_norm_left
-/
theorem isTheta_ofReal (f : α -> Real) (l : Filter α) : (f · : α -> Complex) =Θ[l] f :=
.of_norm_left by simpa using (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]
/--
theorem `isLittleO_ofReal_left` / 定理 `isLittleO_ofReal_left`

English:
theorem isLittleO_ofReal_left
  given: {f : α -> Real} {g : α -> E}
  statement: (f · : α -> Complex) =o[l] g ↔ f =o[l] g
  proof: (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]

中文:
定理 isLittleO_of实数_left
  条件: {f : α -> 实数} {g : α -> E}
  结论: (f · : α -> 复形) =o[l] g ↔ f =o[l] g
  证明: (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]

Depends on / 依赖: isLittleO_congr_left, isTheta_ofReal
-/
theorem isLittleO_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) =o[l] g ↔ f =o[l] g :=
  (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]
/--
theorem `isLittleO_ofReal_right` / 定理 `isLittleO_ofReal_right`

English:
theorem isLittleO_ofReal_right
  given: {f : α -> E} {g : α -> Real}
  statement: f =o[l] (g · : α -> Complex) ↔ f =o[l] g
  proof: (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]

中文:
定理 isLittleO_of实数_right
  条件: {f : α -> E} {g : α -> 实数}
  结论: f =o[l] (g · : α -> 复形) ↔ f =o[l] g
  证明: (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]

Depends on / 依赖: isLittleO_congr_right, isTheta_ofReal
-/
theorem isLittleO_ofReal_right {f : α -> E} {g : α -> Real} : f =o[l] (g · : α -> Complex) ↔ f =o[l] g :=
  (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]
/--
theorem `isBigO_ofReal_left` / 定理 `isBigO_ofReal_left`

English:
theorem isBigO_ofReal_left
  given: {f : α -> Real} {g : α -> E}
  statement: (f · : α -> Complex) =O[l] g ↔ f =O[l] g
  proof: (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]

中文:
定理 isBigO_of实数_left
  条件: {f : α -> 实数} {g : α -> E}
  结论: (f · : α -> 复形) =O[l] g ↔ f =O[l] g
  证明: (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]

Depends on / 依赖: isBigO_congr_left, isTheta_ofReal
-/
theorem isBigO_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) =O[l] g ↔ f =O[l] g :=
  (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]
/--
theorem `isBigO_ofReal_right` / 定理 `isBigO_ofReal_right`

English:
theorem isBigO_ofReal_right
  given: {f : α -> E} {g : α -> Real}
  statement: f =O[l] (g · : α -> Complex) ↔ f =O[l] g
  proof: (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]

中文:
定理 isBigO_of实数_right
  条件: {f : α -> E} {g : α -> 实数}
  结论: f =O[l] (g · : α -> 复形) ↔ f =O[l] g
  证明: (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]

Depends on / 依赖: isBigO_congr_right, isTheta_ofReal
-/
theorem isBigO_ofReal_right {f : α -> E} {g : α -> Real} : f =O[l] (g · : α -> Complex) ↔ f =O[l] g :=
  (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]
/--
theorem `isTheta_ofReal_left` / 定理 `isTheta_ofReal_left`

English:
theorem isTheta_ofReal_left
  given: {f : α -> Real} {g : α -> E}
  statement: (f · : α -> Complex) =Θ[l] g ↔ f =Θ[l] g
  proof: (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]

中文:
定理 isTheta_of实数_left
  条件: {f : α -> 实数} {g : α -> E}
  结论: (f · : α -> 复形) =Θ[l] g ↔ f =Θ[l] g
  证明: (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]

Depends on / 依赖: isTheta_congr_left, isTheta_ofReal
-/
theorem isTheta_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) =Θ[l] g ↔ f =Θ[l] g :=
  (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]
/--
theorem `isTheta_ofReal_right` / 定理 `isTheta_ofReal_right`

English:
theorem isTheta_ofReal_right
  given: {f : α -> E} {g : α -> Real}
  statement: f =Θ[l] (g · : α -> Complex) ↔ f =Θ[l] g
  proof: (isTheta_ofReal g l).isTheta_congr_right

中文:
定理 isTheta_of实数_right
  条件: {f : α -> E} {g : α -> 实数}
  结论: f =Θ[l] (g · : α -> 复形) ↔ f =Θ[l] g
  证明: (isTheta_ofReal g l).isTheta_congr_right

Depends on / 依赖: isTheta_congr_right, isTheta_ofReal
-/
theorem isTheta_ofReal_right {f : α -> E} {g : α -> Real} : f =Θ[l] (g · : α -> Complex) ↔ f =Θ[l] g :=
  (isTheta_ofReal g l).isTheta_congr_right

open Topology

/--
lemma `isBigO_comp_ofReal_nhds` / 引理 `isBigO_comp_ofReal_nhds`

English:
lemma isBigO_comp_ofReal_nhds
  given: {f g : Complex -> Complex} {x : Real} (h : f =O[𝓝 (x : Complex)] g)
  proof: h.comp_tendsto continuous_ofReal.tendsto x

中文:
引理 isBigO_comp_of实数_nhds
  条件: {f g : 复形 -> 复形} {x : 实数} (h : f =O[𝓝 (x : 复形)] g)
  证明: h.comp_tendsto continuous_ofReal.tendsto x

Depends on / 依赖: comp_tendsto, continuous_ofReal, continuous_ofReal.tendsto, h.comp_tendsto, tendsto
-/
lemma isBigO_comp_ofReal_nhds {f g : Complex -> Complex} {x : Real} (h : f =O[𝓝 (x : Complex)] g) :
    (fun y : Real => f y) =O[𝓝 x] (fun y : Real => g y) :=
h.comp_tendsto continuous_ofReal.tendsto x

/--
lemma `isBigO_comp_ofReal_nhds_ne` / 引理 `isBigO_comp_ofReal_nhds_ne`

English:
lemma isBigO_comp_ofReal_nhds_ne
  given: {f g : Complex -> Complex} {x : Real} (h : f =O[𝓝[!=] (x : Complex)] g)
  proof: h.comp_tendsto continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ => by simp_all

中文:
引理 isBigO_comp_of实数_nhds_ne
  条件: {f g : 复形 -> 复形} {x : 实数} (h : f =O[𝓝[!=] (x : 复形)] g)
  证明: h.comp_tendsto continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ => by simp_all

Depends on / 依赖: comp_tendsto, continuousWithinAt, continuous_ofReal, continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin, h.comp_tendsto, tendsto_nhdsWithin
-/
lemma isBigO_comp_ofReal_nhds_ne {f g : Complex -> Complex} {x : Real} (h : f =O[𝓝[!=] (x : Complex)] g) :
    (fun y : Real => f y) =O[𝓝[!=] x] (fun y : Real => g y) :=
h.comp_tendsto continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ => by simp_all

/--
lemma `isBigO_re_sub_re` / 引理 `isBigO_re_sub_re`

English:
lemma isBigO_re_sub_re
  given: {z : Complex}
  statement: (fun (w : Complex) => w.re - z.re) =O[𝓝 z] fun w => w - z
  proof: Asymptotics.isBigO_of_le _ fun w => abs_re_le_norm (w - z)

中文:
引理 isBigO_re_sub_re
  条件: {z : 复形}
  结论: (fun (w : 复形) => w.re - z.re) =O[𝓝 z] fun w => w - z
  证明: Asymptotics.isBigO_of_le _ fun w => abs_re_le_norm (w - z)

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_of_le, abs_re_le_norm, isBigO_of_le
-/
lemma isBigO_re_sub_re {z : Complex} : (fun (w : Complex) => w.re - z.re) =O[𝓝 z] fun w => w - z :=
  Asymptotics.isBigO_of_le _ fun w => abs_re_le_norm (w - z)

/--
lemma `isBigO_im_sub_im` / 引理 `isBigO_im_sub_im`

English:
lemma isBigO_im_sub_im
  given: {z : Complex}
  statement: (fun (w : Complex) => w.im - z.im) =O[𝓝 z] fun w => w - z
  proof: Asymptotics.isBigO_of_le _ fun w => abs_im_le_norm (w - z)

中文:
引理 isBigO_im_sub_im
  条件: {z : 复形}
  结论: (fun (w : 复形) => w.im - z.im) =O[𝓝 z] fun w => w - z
  证明: Asymptotics.isBigO_of_le _ fun w => abs_im_le_norm (w - z)

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_of_le, abs_im_le_norm, isBigO_of_le
-/
lemma isBigO_im_sub_im {z : Complex} : (fun (w : Complex) => w.im - z.im) =O[𝓝 z] fun w => w - z :=
  Asymptotics.isBigO_of_le _ fun w => abs_im_le_norm (w - z)

end Complex

section Int

open Filter in
/--
lemma `Int.cast_complex_isTheta_cast_real` / 引理 `Int.cast_complex_isTheta_cast_real`

English:
lemma Int.cast_complex_isTheta_cast_real
  statement: Int.cast (R := Complex) =Θ[cofinite] Int.cast (R := Real)
  proof: by
  apply Asymptotics.IsTheta.of_norm_eventuallyEq_norm
  filter_upwards with n using by simp

中文:
引理 整数.cast_complex_isTheta_cast_real
  结论: 整数.cast (R := 复形) =Θ[cofinite] 整数.cast (R := 实数)
  证明: by
  apply Asymptotics.IsTheta.of_norm_eventuallyEq_norm
  filter_upwards with n using by simp

Depends on / 依赖: Asymptotics, Asymptotics.IsTheta.of_norm_eventuallyEq_norm, Int.cast, IsTheta, cofinite, filter_upwards, of_norm_eventuallyEq_norm
-/
lemma Int.cast_complex_isTheta_cast_real : Int.cast (R := Complex) =Θ[cofinite] Int.cast (R := Real) := by
  apply Asymptotics.IsTheta.of_norm_eventuallyEq_norm
  filter_upwards with n using by simp

end Int
