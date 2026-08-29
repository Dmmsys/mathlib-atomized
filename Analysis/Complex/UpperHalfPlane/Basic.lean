/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The upper half plane

This file defines `UpperHalfPlane` to be the upper half plane in `ℂ`.

We define the notation `ℍ` for the upper half plane available in the locale
`UpperHalfPlane` so as not to conflict with the quaternions.
-/

@[expose] public section

noncomputable section

/-- The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace -/
@[ext]
/--
Definition of `UpperHalfPlane` / `UpperHalfPlane` 的定义

English:
structure UpperHalfPlane
  parameters: where
  axioms and operations (2):
    - coe : Complex
    - coe_im_pos : 0 < coe.im

中文:
结构 UpperHalfPlane
  参数: where
  公理与运算 (2 个):
    - coe : 复形
    - coe_im_pos : 0 < coe.im
-/
structure UpperHalfPlane where
  /-- Canonical embedding of the upper half-plane into `ℂ`. -/
  protected coe : Complex
  coe_im_pos : 0 < coe.im

@[inherit_doc] scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

open UpperHalfPlane Complex

namespace UpperHalfPlane

attribute [coe] UpperHalfPlane.coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut ℍ Complex
  body: ⟨UpperHalfPlane.coe⟩

中文:
实例 :
  签名: CoeOut ℍ 复形
  定义体: ⟨UpperHalfPlane.coe⟩

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe
-/
instance : CoeOut ℍ Complex := ⟨UpperHalfPlane.coe⟩

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : ℍ
  body: ⟨Complex.I, by simp⟩

中文:
定义 I
  签名: : ℍ
  定义体: ⟨Complex.I, by simp⟩

Depends on / 依赖: Complex.I
-/
def I : ℍ := ⟨Complex.I, by simp⟩

/--
Definition of `ρ` / `ρ` 的定义

English:
definition ρ
  signature: : ℍ
  body: ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, by positivity⟩

中文:
定义 ρ
  签名: : ℍ
  定义体: ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, by positivity⟩

Depends on / 依赖: Real.sqrt
-/
def ρ : ℍ := ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, by positivity⟩

/--
lemma `ρ_sq` / 引理 `ρ_sq`

English:
lemma ρ_sq
  statement: (ρ : Complex) ^ 2 = -ρ - 1
  proof: by
  simp [Complex.ext_iff, pow_two, ρ]
  grind

中文:
引理 ρ_sq
  结论: (ρ : 复形) ^ 2 = -ρ - 1
  证明: by
  simp [Complex.ext_iff, pow_two, ρ]
  grind

Depends on / 依赖: Complex.ext_iff, ext_iff, pow_two
-/
lemma ρ_sq : (ρ : Complex) ^ 2 = -ρ - 1 := by
  simp [Complex.ext_iff, pow_two, ρ]
  grind

/--
lemma `norm_ρ` / 引理 `norm_ρ`

English:
lemma norm_ρ
  statement: ‖(ρ : Complex)‖ = 1
  proof: by norm_num [norm_def, normSq, ← pow_two, ρ, div_pow]

中文:
引理 norm_ρ
  结论: ‖(ρ : 复形)‖ = 1
  证明: by norm_num [norm_def, normSq, ← pow_two, ρ, div_pow]

Depends on / 依赖: div_pow, normSq, norm_def, pow_two
-/
lemma norm_ρ : ‖(ρ : Complex)‖ = 1 := by norm_num [norm_def, normSq, ← pow_two, ρ, div_pow]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ℍ
  body: ⟨.I⟩

中文:
实例 :
  签名: 可居 ℍ
  定义体: ⟨.I⟩
-/
instance : Inhabited ℍ := ⟨.I⟩

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : ℍ}
  statement: (a : Complex) = b ↔ a = b
  proof: UpperHalfPlane.ext_iff.symm

@[deprecated (since := "2026-01-31")] alias ext_iff' := coe_inj

中文:
定理 coe_inj
  条件: {a b : ℍ}
  结论: (a : 复形) = b ↔ a = b
  证明: UpperHalfPlane.ext_iff.symm

@[deprecated (since := "2026-01-31")] alias ext_iff' := coe_inj
-/
@[simp, norm_cast] theorem coe_inj {a b : ℍ} : (a : Complex) = b ↔ a = b := UpperHalfPlane.ext_iff.symm

@[deprecated (since := "2026-01-31")] alias ext_iff' := coe_inj

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective UpperHalfPlane.coe
  proof: fun _ _ => UpperHalfPlane.ext

中文:
定理 coe_injective
  结论: 函数.单射 UpperHalfPlane.coe
  证明: fun _ _ => UpperHalfPlane.ext

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.ext
-/
theorem coe_injective : Function.Injective UpperHalfPlane.coe := fun _ _ => UpperHalfPlane.ext

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Complex ℍ ((↑) : ℍ -> Complex) fun z => 0 < z.im where
  body: ⟨⟨z, hz⟩, rfl⟩

中文:
实例 canLift
  签名: : CanLift 复形 ℍ ((↑) : ℍ -> 复形) fun z => 0 < z.im where
  定义体: ⟨⟨z, hz⟩, rfl⟩
-/
instance canLift : CanLift Complex ℍ ((↑) : ℍ -> Complex) fun z => 0 < z.im where
  prf z hz := ⟨⟨z, hz⟩, rfl⟩

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {P : ℍ -> Prop}
  statement: (forall z, P z) ↔ forall z hz, P ⟨z, hz⟩
  proof: ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.1 z.2⟩

中文:
定理 «对任意»
  条件: {P : ℍ -> 命题}
  结论: (对任意 z, P z) ↔ 对任意 z hz, P ⟨z, hz⟩
  证明: ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.1 z.2⟩
-/
protected theorem «forall» {P : ℍ -> Prop} : (forall z, P z) ↔ forall z hz, P ⟨z, hz⟩ :=
  ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.1 z.2⟩

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {P : ℍ -> Prop}
  statement: (exists z, P z) ↔ exists z hz, P ⟨z, hz⟩
  proof: ⟨fun ⟨⟨z, hz⟩, hP⟩ => ⟨z, hz, hP⟩, fun ⟨z, hz, hP⟩ => ⟨⟨z, hz⟩, hP⟩⟩

中文:
定理 «存在»
  条件: {P : ℍ -> 命题}
  结论: (存在 z, P z) ↔ 存在 z hz, P ⟨z, hz⟩
  证明: ⟨fun ⟨⟨z, hz⟩, hP⟩ => ⟨z, hz, hP⟩, fun ⟨z, hz, hP⟩ => ⟨⟨z, hz⟩, hP⟩⟩
-/
protected theorem «exists» {P : ℍ -> Prop} : (exists z, P z) ↔ exists z hz, P ⟨z, hz⟩ :=
  ⟨fun ⟨⟨z, hz⟩, hP⟩ => ⟨z, hz, hP⟩, fun ⟨z, hz, hP⟩ => ⟨⟨z, hz⟩, hP⟩⟩

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (z : ℍ)
  body: (z : Complex).im

中文:
定义 im
  签名: (z : ℍ)
  定义体: (z : Complex).im
-/
def im (z : ℍ) :=
  (z : Complex).im

/--
Definition of `re` / `re` 的定义

English:
definition re
  signature: (z : ℍ)
  body: (z : Complex).re

中文:
定义 re
  签名: (z : ℍ)
  定义体: (z : Complex).re
-/
def re (z : ℍ) :=
  (z : Complex).re

/--
theorem `ext_re_im` / 定理 `ext_re_im`

English:
theorem ext_re_im
  given: {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im)
  statement: a = b
  proof: UpperHalfPlane.ext Complex.ext hre him

@[deprecated (since := "2026-01-29")]
alias ext' := ext_re_im

@[simp]

中文:
定理 ext_re_im
  条件: {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im)
  结论: a = b
  证明: UpperHalfPlane.ext Complex.ext hre him

@[deprecated (since := "2026-01-29")]
alias ext' := ext_re_im

@[simp]

Depends on / 依赖: Complex.ext, UpperHalfPlane, UpperHalfPlane.ext
-/
theorem ext_re_im {a b : ℍ} (hre : a.re = b.re) (him : a.im = b.im) : a = b :=
UpperHalfPlane.ext Complex.ext hre him

@[deprecated (since := "2026-01-29")]
alias ext' := ext_re_im

@[simp]
/--
theorem `coe_im` / 定理 `coe_im`

English:
theorem coe_im
  given: (z : ℍ)
  statement: (z : Complex).im = z.im
  proof: rfl

@[simp]

中文:
定理 coe_im
  条件: (z : ℍ)
  结论: (z : 复形).im = z.im
  证明: rfl

@[simp]
-/
theorem coe_im (z : ℍ) : (z : Complex).im = z.im :=
  rfl

@[simp]
/--
theorem `coe_re` / 定理 `coe_re`

English:
theorem coe_re
  given: (z : ℍ)
  statement: (z : Complex).re = z.re
  proof: rfl

@[simp]

中文:
定理 coe_re
  条件: (z : ℍ)
  结论: (z : 复形).re = z.re
  证明: rfl

@[simp]
-/
theorem coe_re (z : ℍ) : (z : Complex).re = z.re :=
  rfl

@[simp]
/--
theorem `mk_re` / 定理 `mk_re`

English:
theorem mk_re
  given: (z : Complex) (h : 0 < z.im)
  statement: (mk z h).re = z.re
  proof: rfl

@[simp]

中文:
定理 mk_re
  条件: (z : 复形) (h : 0 < z.im)
  结论: (mk z h).re = z.re
  证明: rfl

@[simp]
-/
theorem mk_re (z : Complex) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl

@[simp]
/--
theorem `mk_im` / 定理 `mk_im`

English:
theorem mk_im
  given: (z : Complex) (h : 0 < z.im)
  statement: (mk z h).im = z.im
  proof: rfl

中文:
定理 mk_im
  条件: (z : 复形) (h : 0 < z.im)
  结论: (mk z h).im = z.im
  证明: rfl
-/
theorem mk_im (z : Complex) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (z : Complex) (h : 0 < z.im)
  statement: (mk z h : Complex) = z
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (z : 复形) (h : 0 < z.im)
  结论: (mk z h : 复形) = z
  证明: rfl

@[simp]
-/
theorem coe_mk (z : Complex) (h : 0 < z.im) : (mk z h : Complex) = z :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (z : ℍ) (h : 0 < (z : Complex).im := z.2)
  statement: mk z h = z
  proof: rfl

@[simp]

中文:
定理 mk_coe
  条件: (z : ℍ) (h : 0 < (z : 复形).im := z.2)
  结论: mk z h = z
  证明: rfl

@[simp]
-/
theorem mk_coe (z : ℍ) (h : 0 < (z : Complex).im := z.2) : mk z h = z :=
  rfl

@[simp]
/--
lemma `I_im` / 引理 `I_im`

English:
lemma I_im
  statement: I.im = 1
  proof: Complex.I_im

@[simp]

中文:
引理 I_im
  结论: I.im = 1
  证明: Complex.I_im

@[simp]

Depends on / 依赖: Complex.I_im, I_im
-/
lemma I_im : I.im = 1 := Complex.I_im

@[simp]
/--
lemma `I_re` / 引理 `I_re`

English:
lemma I_re
  statement: I.re = 0
  proof: Complex.I_re

@[simp, norm_cast]

中文:
引理 I_re
  结论: I.re = 0
  证明: Complex.I_re

@[simp, norm_cast]

Depends on / 依赖: Complex.I_re, I_re
-/
lemma I_re : I.re = 0 := Complex.I_re

@[simp, norm_cast]
/--
lemma `coe_I` / 引理 `coe_I`

English:
lemma coe_I
  statement: I = Complex.I
  proof: rfl

@[deprecated coe_mk (since := "2026-01-29")]

中文:
引理 coe_I
  结论: I = 复形.I
  证明: rfl

@[deprecated coe_mk (since := "2026-01-29")]
-/
lemma coe_I : I = Complex.I := rfl

@[deprecated coe_mk (since := "2026-01-29")]
/--
lemma `coe_mk_subtype` / 引理 `coe_mk_subtype`

English:
lemma coe_mk_subtype
  given: {z : Complex} (hz : 0 < z.im)
  proof: rfl

中文:
引理 coe_mk_subtype
  条件: {z : 复形} (hz : 0 < z.im)
  证明: rfl
-/
lemma coe_mk_subtype {z : Complex} (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z :=
  rfl

/--
theorem `re_add_im` / 定理 `re_add_im`

English:
theorem re_add_im
  given: (z : ℍ)
  statement: (z.re + z.im * Complex.I : Complex) = z
  proof: Complex.re_add_im z

中文:
定理 re_add_im
  条件: (z : ℍ)
  结论: (z.re + z.im * 复形.I : 复形) = z
  证明: Complex.re_add_im z

Depends on / 依赖: Complex.re_add_im, re_add_im
-/
theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.I : Complex) = z :=
  Complex.re_add_im z

/--
theorem `im_pos` / 定理 `im_pos`

English:
theorem im_pos
  given: (z : ℍ)
  statement: 0 < z.im
  proof: z.coe_im_pos

中文:
定理 im_pos
  条件: (z : ℍ)
  结论: 0 < z.im
  证明: z.coe_im_pos

Depends on / 依赖: coe_im_pos, z.coe_im_pos
-/
theorem im_pos (z : ℍ) : 0 < z.im := z.coe_im_pos

/--
theorem `im_ne_zero` / 定理 `im_ne_zero`

English:
theorem im_ne_zero
  given: (z : ℍ)
  statement: z.im != 0
  proof: z.im_pos.ne'

中文:
定理 im_ne_zero
  条件: (z : ℍ)
  结论: z.im != 0
  证明: z.im_pos.ne'

Depends on / 依赖: im_pos, z.im_pos.ne
-/
theorem im_ne_zero (z : ℍ) : z.im != 0 :=
  z.im_pos.ne'

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (z : ℍ)
  statement: (z : Complex) != 0
  proof: mt (congr_arg Complex.im) z.im_ne_zero

中文:
定理 ne_zero
  条件: (z : ℍ)
  结论: (z : 复形) != 0
  证明: mt (congr_arg Complex.im) z.im_ne_zero

Depends on / 依赖: Complex.im, congr_arg, im_ne_zero, z.im_ne_zero
-/
theorem ne_zero (z : ℍ) : (z : Complex) != 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero

/--
lemma `mem_slitPlane` / 引理 `mem_slitPlane`

English:
lemma mem_slitPlane
  given: (z : ℍ)
  statement: (z : Complex) in Complex.slitPlane
  proof: by
  simp [Complex.slitPlane, im_ne_zero z]

中文:
引理 mem_slitPlane
  条件: (z : ℍ)
  结论: (z : 复形) in 复形.slitPlane
  证明: by
  simp [Complex.slitPlane, im_ne_zero z]

Depends on / 依赖: Complex.slitPlane, im_ne_zero, slitPlane
-/
lemma mem_slitPlane (z : ℍ) : (z : Complex) in Complex.slitPlane := by
  simp [Complex.slitPlane, im_ne_zero z]

/--
lemma `eq_of_re_of_norm` / 引理 `eq_of_re_of_norm`

English:
lemma eq_of_re_of_norm
  given: {τ τ' : ℍ} (hre : τ.re = τ'.re) (hnorm : ‖(τ : Complex)‖ = ‖(τ' : Complex)‖)
  proof: by
  apply_fun (· ^ 2) at hnorm
  simpa [UpperHalfPlane.ext_iff, Complex.ext_iff, hre, Complex.normSq, Complex.sq_norm,
    ← pow_two, pow_left_inj₀ τ.im_pos.le τ'.im_pos.le two_ne_zero] using hnorm

中文:
引理 eq_of_re_of_norm
  条件: {τ τ' : ℍ} (hre : τ.re = τ'.re) (hnorm : ‖(τ : 复形)‖ = ‖(τ' : 复形)‖)
  证明: by
  apply_fun (· ^ 2) at hnorm
  simpa [UpperHalfPlane.ext_iff, Complex.ext_iff, hre, Complex.normSq, Complex.sq_norm,
    ← pow_two, pow_left_inj₀ τ.im_pos.le τ'.im_pos.le two_ne_zero] using hnorm

Depends on / 依赖: Complex.ext_iff, Complex.normSq, Complex.sq_norm, UpperHalfPlane, UpperHalfPlane.ext_iff, apply_fun, ext_iff, im_pos, im_pos.le, normSq, pow_two, sq_norm, two_ne_zero
-/
lemma eq_of_re_of_norm {τ τ' : ℍ} (hre : τ.re = τ'.re) (hnorm : ‖(τ : Complex)‖ = ‖(τ' : Complex)‖) :
    τ = τ' := by
  apply_fun (· ^ 2) at hnorm
  simpa [UpperHalfPlane.ext_iff, Complex.ext_iff, hre, Complex.normSq, Complex.sq_norm,
    ← pow_two, pow_left_inj₀ τ.im_pos.le τ'.im_pos.le two_ne_zero] using hnorm

end UpperHalfPlane

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `UpperHalfPlane.im`. -/
@[positivity UpperHalfPlane.im _]
meta def evalUpperHalfPlaneIm : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(UpperHalfPlane.im $a) =>
    assertInstancesCommute
    pure (.positive q(@UpperHalfPlane.im_pos $a))
  | _, _, _ => throwError "not UpperHalfPlane.im"

/-- Extension for the `positivity` tactic: `UpperHalfPlane.coe`. -/
@[positivity UpperHalfPlane.coe _]
meta def evalUpperHalfPlaneCoe : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Complex), ~q(UpperHalfPlane.coe $a) =>
    assertInstancesCommute
    pure (.nonzero q(@UpperHalfPlane.ne_zero $a))
  | _, _, _ => throwError "not UpperHalfPlane.coe"

end Mathlib.Meta.Positivity

namespace UpperHalfPlane

/--
theorem `normSq_pos` / 定理 `normSq_pos`

English:
theorem normSq_pos
  given: (z : ℍ)
  statement: 0 < Complex.normSq (z : Complex)
  proof: by
  rw [Complex.normSq_pos]; exact z.ne_zero

中文:
定理 normSq_pos
  条件: (z : ℍ)
  结论: 0 < 复形.normSq (z : 复形)
  证明: by
  rw [Complex.normSq_pos]; exact z.ne_zero

Depends on / 依赖: Complex.normSq_pos, ne_zero, normSq_pos, z.ne_zero
-/
theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : Complex) := by
  rw [Complex.normSq_pos]; exact z.ne_zero

/--
theorem `normSq_ne_zero` / 定理 `normSq_ne_zero`

English:
theorem normSq_ne_zero
  given: (z : ℍ)
  statement: Complex.normSq (z : Complex) != 0
  proof: (normSq_pos z).ne'

中文:
定理 normSq_ne_zero
  条件: (z : ℍ)
  结论: 复形.normSq (z : 复形) != 0
  证明: (normSq_pos z).ne'

Depends on / 依赖: normSq_pos
-/
theorem normSq_ne_zero (z : ℍ) : Complex.normSq (z : Complex) != 0 :=
  (normSq_pos z).ne'

/--
theorem `im_inv_neg_coe_pos` / 定理 `im_inv_neg_coe_pos`

English:
theorem im_inv_neg_coe_pos
  given: (z : ℍ)
  statement: 0 < (-z : Complex)⁻¹.im
  proof: by
  simpa [neg_div] using div_pos z.im_pos (normSq_pos z)

中文:
定理 im_inv_neg_coe_pos
  条件: (z : ℍ)
  结论: 0 < (-z : 复形)⁻¹.im
  证明: by
  simpa [neg_div] using div_pos z.im_pos (normSq_pos z)

Depends on / 依赖: div_pos, im_pos, neg_div, normSq_pos, z.im_pos
-/
theorem im_inv_neg_coe_pos (z : ℍ) : 0 < (-z : Complex)⁻¹.im := by
  simpa [neg_div] using div_pos z.im_pos (normSq_pos z)

/--
lemma `im_pnat_div_pos` / 引理 `im_pnat_div_pos`

English:
lemma im_pnat_div_pos
  given: (n : Nat) [NeZero n] (z : ℍ)
  statement: 0 < (-(n : Complex) / z).im
  proof: by
  suffices 0 < n * z.im / Complex.normSq z by simpa [Complex.div_im, neg_div]
  positivity [NeZero.ne n, z.normSq_pos]

中文:
引理 im_pnat_div_pos
  条件: (n : 自然数) [NeZero n] (z : ℍ)
  结论: 0 < (-(n : 复形) / z).im
  证明: by
  suffices 0 < n * z.im / Complex.normSq z by simpa [Complex.div_im, neg_div]
  positivity [NeZero.ne n, z.normSq_pos]

Depends on / 依赖: Complex.div_im, Complex.normSq, NeZero, NeZero.ne, div_im, neg_div, normSq, normSq_pos, z.im, z.normSq_pos
-/
lemma im_pnat_div_pos (n : Nat) [NeZero n] (z : ℍ) : 0 < (-(n : Complex) / z).im := by
  suffices 0 < n * z.im / Complex.normSq z by simpa [Complex.div_im, neg_div]
  positivity [NeZero.ne n, z.normSq_pos]

/--
lemma `ne_ofReal` / 引理 `ne_ofReal`

English:
lemma ne_ofReal
  given: (z : ℍ) (x : Real)
  statement: (z : Complex) != x
  proof: ne_of_apply_ne Complex.im by simp [im_ne_zero]

中文:
引理 ne_of实数
  条件: (z : ℍ) (x : 实数)
  结论: (z : 复形) != x
  证明: ne_of_apply_ne Complex.im by simp [im_ne_zero]

Depends on / 依赖: Complex.im, im_ne_zero, ne_of_apply_ne
-/
lemma ne_ofReal (z : ℍ) (x : Real) : (z : Complex) != x :=
ne_of_apply_ne Complex.im by simp [im_ne_zero]

/--
lemma `ne_intCast` / 引理 `ne_intCast`

English:
lemma ne_intCast
  given: (z : ℍ) (n : Int)
  statement: (z : Complex) != n
  proof: mod_cast ne_ofReal z n

@[deprecated (since := "2026-01-29")] alias ne_int := ne_intCast

中文:
引理 ne_intCast
  条件: (z : ℍ) (n : 整数)
  结论: (z : 复形) != n
  证明: mod_cast ne_ofReal z n

@[deprecated (since := "2026-01-29")] alias ne_int := ne_intCast

Depends on / 依赖: mod_cast, ne_ofReal
-/
lemma ne_intCast (z : ℍ) (n : Int) : (z : Complex) != n := mod_cast ne_ofReal z n

@[deprecated (since := "2026-01-29")] alias ne_int := ne_intCast

/--
lemma `ne_natCast` / 引理 `ne_natCast`

English:
lemma ne_natCast
  given: (z : ℍ) (n : Nat)
  statement: (z : Complex) != n
  proof: mod_cast ne_intCast z n

@[deprecated (since := "2026-01-29")] alias ne_nat := ne_natCast

中文:
引理 ne_natCast
  条件: (z : ℍ) (n : 自然数)
  结论: (z : 复形) != n
  证明: mod_cast ne_intCast z n

@[deprecated (since := "2026-01-29")] alias ne_nat := ne_natCast

Depends on / 依赖: mod_cast, ne_intCast
-/
lemma ne_natCast (z : ℍ) (n : Nat) : (z : Complex) != n := mod_cast ne_intCast z n

@[deprecated (since := "2026-01-29")] alias ne_nat := ne_natCast

section PosRealAction

/--
Instance `posRealAction` / 实例 `posRealAction`

English:
instance posRealAction
  signature: : MulAction {x : Real // 0 < x} ℍ where
  body: mk ((x : Real) • (z : Complex)) by simpa using mul_pos x.2 z.im_pos
one_smul _ := UpperHalfPlane.ext one_smul _ _
mul_smul x y z := UpperHalfPlane.ext mul_smul (x : Real) y (z : Complex)

中文:
实例 pos实数Action
  签名: : 乘法作用 {x : 实数 // 0 < x} ℍ where
  定义体: mk ((x : Real) • (z : Complex)) by simpa using mul_pos x.2 z.im_pos
one_smul _ := UpperHalfPlane.ext one_smul _ _
mul_smul x y z := UpperHalfPlane.ext mul_smul (x : Real) y (z : Complex)

Depends on / 依赖: im_pos, mul_pos, z.im_pos
-/
instance posRealAction : MulAction {x : Real // 0 < x} ℍ where
smul x z := mk ((x : Real) • (z : Complex)) by simpa using mul_pos x.2 z.im_pos
one_smul _ := UpperHalfPlane.ext one_smul _ _
mul_smul x y z := UpperHalfPlane.ext mul_smul (x : Real) y (z : Complex)

variable (x : {x : Real // 0 < x}) (z : ℍ)

@[simp]
/--
theorem `coe_pos_real_smul` / 定理 `coe_pos_real_smul`

English:
theorem coe_pos_real_smul
  statement: ↑(x • z) = (x : Real) • (z : Complex)
  proof: rfl

@[simp]

中文:
定理 coe_pos_real_smul
  结论: ↑(x • z) = (x : 实数) • (z : 复形)
  证明: rfl

@[simp]
-/
theorem coe_pos_real_smul : ↑(x • z) = (x : Real) • (z : Complex) :=
  rfl

@[simp]
/--
theorem `pos_real_im` / 定理 `pos_real_im`

English:
theorem pos_real_im
  statement: (x • z).im = x * z.im
  proof: Complex.smul_im _ _

@[simp]

中文:
定理 pos_real_im
  结论: (x • z).im = x * z.im
  证明: Complex.smul_im _ _

@[simp]

Depends on / 依赖: Complex.smul_im, smul_im
-/
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _

@[simp]
/--
theorem `pos_real_re` / 定理 `pos_real_re`

English:
theorem pos_real_re
  statement: (x • z).re = x * z.re
  proof: Complex.smul_re _ _

中文:
定理 pos_real_re
  结论: (x • z).re = x * z.re
  证明: Complex.smul_re _ _

Depends on / 依赖: Complex.smul_re, smul_re
-/
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _

/--
theorem `pos_real_smul_injective` / 定理 `pos_real_smul_injective`

English:
theorem pos_real_smul_injective
  given: (z : ℍ)
  proof: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp_all [UpperHalfPlane.ext_iff, ne_zero]

中文:
定理 pos_real_smul_injective
  条件: (z : ℍ)
  证明: by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp_all [UpperHalfPlane.ext_iff, ne_zero]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.ext_iff, ext_iff, ne_zero
-/
theorem pos_real_smul_injective (z : ℍ) :
    Function.Injective fun x : {x : Real // 0 < x} => x • z := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp_all [UpperHalfPlane.ext_iff, ne_zero]

end PosRealAction

section RealAddAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddAction Real ℍ
  body: mk (x + z) by simpa using z.im_pos
  zero_vadd _ := by simp [HVAdd.hVAdd]
  add_vadd x y z := by simp [HVAdd.hVAdd, add_assoc]

中文:
实例 :
  签名: 加法作用 实数 ℍ
  定义体: mk (x + z) by simpa using z.im_pos
  zero_vadd _ := by simp [HVAdd.hVAdd]
  add_vadd x y z := by simp [HVAdd.hVAdd, add_assoc]

Depends on / 依赖: im_pos, z.im_pos
-/
instance : AddAction Real ℍ where
vadd x z := mk (x + z) by simpa using z.im_pos
  zero_vadd _ := by simp [HVAdd.hVAdd]
  add_vadd x y z := by simp [HVAdd.hVAdd, add_assoc]

variable (x : Real) (z : ℍ)

@[simp]
/--
theorem `coe_vadd` / 定理 `coe_vadd`

English:
theorem coe_vadd
  statement: ↑(x +ᵥ z) = (x + z : Complex)
  proof: rfl

@[simp]

中文:
定理 coe_vadd
  结论: ↑(x +ᵥ z) = (x + z : 复形)
  证明: rfl

@[simp]
-/
theorem coe_vadd : ↑(x +ᵥ z) = (x + z : Complex) :=
  rfl

@[simp]
/--
theorem `vadd_re` / 定理 `vadd_re`

English:
theorem vadd_re
  statement: (x +ᵥ z).re = x + z.re
  proof: rfl

@[simp]

中文:
定理 vadd_re
  结论: (x +ᵥ z).re = x + z.re
  证明: rfl

@[simp]
-/
theorem vadd_re : (x +ᵥ z).re = x + z.re :=
  rfl

@[simp]
/--
theorem `vadd_im` / 定理 `vadd_im`

English:
theorem vadd_im
  statement: (x +ᵥ z).im = z.im
  proof: zero_add _

@[simp]

中文:
定理 vadd_im
  结论: (x +ᵥ z).im = z.im
  证明: zero_add _

@[simp]

Depends on / 依赖: zero_add
-/
theorem vadd_im : (x +ᵥ z).im = z.im :=
  zero_add _

@[simp]
/--
theorem `vadd_right_cancel_iff` / 定理 `vadd_right_cancel_iff`

English:
theorem vadd_right_cancel_iff
  given: {x y : Real} (z : ℍ)
  statement: x +ᵥ z = y +ᵥ z ↔ x = y
  proof: by
  simp [UpperHalfPlane.ext_iff]

中文:
定理 vadd_right_cancel_iff
  条件: {x y : 实数} (z : ℍ)
  结论: x +ᵥ z = y +ᵥ z ↔ x = y
  证明: by
  simp [UpperHalfPlane.ext_iff]
-/
protected theorem vadd_right_cancel_iff {x y : Real} (z : ℍ) : x +ᵥ z = y +ᵥ z ↔ x = y := by
  simp [UpperHalfPlane.ext_iff]

/--
theorem `vadd_left_injective` / 定理 `vadd_left_injective`

English:
theorem vadd_left_injective
  given: (z : ℍ)
  statement: Function.Injective fun x : Real => x +ᵥ z
  proof: by
  simp [Function.Injective]

中文:
定理 vadd_left_injective
  条件: (z : ℍ)
  结论: 函数.单射 fun x : 实数 => x +ᵥ z
  证明: by
  simp [Function.Injective]
-/
protected theorem vadd_left_injective (z : ℍ) : Function.Injective fun x : Real => x +ᵥ z := by
  simp [Function.Injective]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Infinite ℍ
  body: .of_injective _ UpperHalfPlane.vadd_left_injective I

中文:
实例 :
  签名: 无限 ℍ
  定义体: .of_injective _ UpperHalfPlane.vadd_left_injective I

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.vadd_left_injective, of_injective, vadd_left_injective
-/
instance : Infinite ℍ :=
.of_injective _ UpperHalfPlane.vadd_left_injective I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial ℍ
  body: inferInstance

中文:
实例 :
  签名: 非平凡 ℍ
  定义体: inferInstance
-/
instance : Nontrivial ℍ := inferInstance

end RealAddAction

section upperHalfPlaneSet

/--
Definition of `upperHalfPlaneSet` / `upperHalfPlaneSet` 的定义

English:
abbreviation upperHalfPlaneSet
  body: {z : Complex | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet

中文:
缩写 upperHalfPlaneSet
  定义体: {z : Complex | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet

Depends on / 依赖: z.im
-/
abbrev upperHalfPlaneSet := {z : Complex | 0 < z.im}

local notation "ℍₒ" => upperHalfPlaneSet

/--
lemma `isOpen_upperHalfPlaneSet` / 引理 `isOpen_upperHalfPlaneSet`

English:
lemma isOpen_upperHalfPlaneSet
  statement: IsOpen ℍₒ
  proof: isOpen_lt continuous_const Complex.continuous_im

@[simp]

中文:
引理 isOpen_upperHalfPlaneSet
  结论: 是开集 ℍₒ
  证明: isOpen_lt continuous_const Complex.continuous_im

@[simp]

Depends on / 依赖: Complex.continuous_im, continuous_const, continuous_im, isOpen_lt
-/
lemma isOpen_upperHalfPlaneSet : IsOpen ℍₒ := isOpen_lt continuous_const Complex.continuous_im

@[simp]
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: Set.range UpperHalfPlane.coe = ℍₒ
  proof: by
  ext; simp [UpperHalfPlane.exists]

中文:
定理 range_coe
  结论: 集合.range UpperHalfPlane.coe = ℍₒ
  证明: by
  ext; simp [UpperHalfPlane.exists]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.exists
-/
theorem range_coe : Set.range UpperHalfPlane.coe = ℍₒ := by
  ext; simp [UpperHalfPlane.exists]

end upperHalfPlaneSet

end UpperHalfPlane
