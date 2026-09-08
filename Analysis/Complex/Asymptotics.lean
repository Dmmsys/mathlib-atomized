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

/-
**Complex.isTheta_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_ofReal (f : α -> Real) (l : Filter α) : (f · : α -> Complex) =Θ[l]
 f
参数：f : α -> Real；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : 
Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f'
 : α → E'} {l : Filter…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Asymptotics.IsTheta.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Typ
e u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : 
α → E'} {l : Filter…
· 使用定理 `Asymptotics.isTheta_rfl`：isTheta_rfl : f =Θ[l] f
-/
theorem isTheta_ofReal (f : α → ℝ) (l : Filter α) : (f · : α → ℂ) =Θ[l] f :=
  .of_norm_left <| by simpa using (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]
/-
**Complex.isLittleO_ofReal_left** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isLittleO_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) 
=o[l] g ↔ f =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isLittleO_congr_left`：∀ {α : Type u_1} {G : Type u_5
} {E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGro
up E']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isLittleO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =o[l] g ↔ f =o[l] g :=
  (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]
/-
**Complex.isLittleO_ofReal_right** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isLittleO_ofReal_right {f : α -> E} {g : α -> Real} : f =o[l] (g · : α -> 
Complex) ↔ f =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isLittleO_congr_right`：∀ {α : Type u_1} {E : Type u_
3} {F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGr
oup F']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isLittleO_ofReal_right {f : α → E} {g : α → ℝ} : f =o[l] (g · : α → ℂ) ↔ f =o[l] g :=
  (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]
/-
**Complex.isBigO_ofReal_left** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isBigO_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) =O[
l] g ↔ f =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_left`：∀ {α : Type u_1} {G : Type u_5} {
E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGroup 
E']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isBigO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =O[l] g ↔ f =O[l] g :=
  (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]
/-
**Complex.isBigO_ofReal_right** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isBigO_ofReal_right {f : α -> E} {g : α -> Real} : f =O[l] (g · : α -> Com
plex) ↔ f =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isBigO_congr_right`：∀ {α : Type u_1} {E : Type u_3} 
{F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGroup
 F']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isBigO_ofReal_right {f : α → E} {g : α → ℝ} : f =O[l] (g · : α → ℂ) ↔ f =O[l] g :=
  (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]
/-
**Complex.isTheta_ofReal_left** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_ofReal_left {f : α -> Real} {g : α -> E} : (f · : α -> Complex) =Θ
[l] g ↔ f =Θ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isTheta_congr_left`：∀ {α : Type u_1} {G : Type u_5} 
{E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGroup
 E']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isTheta_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =Θ[l] g ↔ f =Θ[l] g :=
  (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]
/-
**Complex.isTheta_ofReal_right** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_ofReal_right {f : α -> E} {g : α -> Real} : f =Θ[l] (g · : α -> Co
mplex) ↔ f =Θ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isTheta_congr_right`：∀ {α : Type u_1} {G : Type u_5}
 {E' : Type u_6} {F' : Type u_7} [inst : Norm G] [inst_1 : SeminormedAddCommGrou
p E']   [inst_2 : SeminormedA…
· 使用定理 `Complex.isTheta_ofReal`：isTheta_ofReal (f : α -> Real) (l : Filter α) : 
(f · : α -> Complex) =Θ[l] f
-/
theorem isTheta_ofReal_right {f : α → E} {g : α → ℝ} : f =Θ[l] (g · : α → ℂ) ↔ f =Θ[l] g :=
  (isTheta_ofReal g l).isTheta_congr_right

open Topology
/-
**Complex.isBigO_comp_ofReal_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isBigO_comp_ofReal_nhds {f g : Complex -> Complex} {x : Real} (h : f =O[𝓝 
(x : Complex)] g) : (fun y : Real => f y) =O[𝓝 x] (fun y : Real => g y)
参数：h : f =O[𝓝 (x : Complex)] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
lemma isBigO_comp_ofReal_nhds {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝 (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝 x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| continuous_ofReal.tendsto x
/-
**Complex.isBigO_comp_ofReal_nhds_ne** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isBigO_comp_ofReal_nhds_ne {f g : Complex -> Complex} {x : Real} (h : f =O
[𝓝[!=] (x : Complex)] g) : (fun y : Real => f y) =O[𝓝[!=] x] (fun y : Real => g 
y)
参数：h : f =O[𝓝[!=] (x : Complex)] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma isBigO_comp_ofReal_nhds_ne {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝[≠] (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝[≠] x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ ↦ by simp_all
/-
**Complex.isBigO_re_sub_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isBigO_re_sub_re {z : Complex} : (fun (w : Complex) => w.re - z.re) =O[𝓝 z
] fun w => w - z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
-/
lemma isBigO_re_sub_re {z : ℂ} : (fun (w : ℂ) ↦ w.re - z.re) =O[𝓝 z] fun w ↦ w - z :=
  Asymptotics.isBigO_of_le _ fun w ↦ abs_re_le_norm (w - z)
/-
**Complex.isBigO_im_sub_im** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isBigO_im_sub_im {z : Complex} : (fun (w : Complex) => w.im - z.im) =O[𝓝 z
] fun w => w - z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
-/
lemma isBigO_im_sub_im {z : ℂ} : (fun (w : ℂ) ↦ w.im - z.im) =O[𝓝 z] fun w ↦ w - z :=
  Asymptotics.isBigO_of_le _ fun w ↦ abs_im_le_norm (w - z)

end Complex

section Int

open Filter in
/-
**Int.cast_complex_isTheta_cast_real** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.cast_complex_isTheta_cast_real : Int.cast (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.of_norm_eventuallyEq_norm`：∀ {α : Type u_1} {E : Typ
e u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} 
{l : Filter α},   ((fun x => ‖f x‖)…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Int.cast_complex_isTheta_cast_real : Int.cast (R := ℂ) =Θ[cofinite] Int.cast (R := ℝ) := by
  apply Asymptotics.IsTheta.of_norm_eventuallyEq_norm
  filter_upwards with n using by simp

end Int

