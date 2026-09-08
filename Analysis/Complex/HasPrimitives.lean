/-
Copyright (c) 2024 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich, Oliver Nash
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex

/-!
# Primitives of Holomorphic Functions

In this file, we give conditions under which holomorphic functions have primitives. The main goal
is to prove that holomorphic functions on simply connected domains have primitives. As a first step,
we prove that holomorphic functions on disks have primitives. The approach is based on Morera's
theorem, that a continuous function (on a disk) whose integral round a rectangle vanishes on all
rectangles contained in the disk has a primitive. (Coupled with the fact that holomorphic functions
satisfy this property.) To prove Morera's theorem, we first define the `Complex.wedgeIntegral`,
which is the integral of a function over a "wedge" (a horizontal segment followed by a vertical
segment in the disk), and compute its derivative.

## Main results

* `Complex.IsConservativeOn.isExactOn_ball`: **Morera's Theorem**: On a disk, a continuous function
  whose integrals on rectangles vanish, has primitives.
* `DifferentiableOn.isExactOn_ball`: On a disk, a holomorphic function has primitives.

TODO: Extend to holomorphic functions on simply connected domains.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

namespace Complex

section AuxiliaryLemmata

variable {c z : ℂ} {r x y : ℝ}

/-
**Complex.re_add_im_mul_mem_ball** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma re_add_im_mul_mem_ball (hz : z ∈ ball c r) :
    z.re + c.im * I ∈ ball c r := by
  suffices dist (z.re + c.im * I) c ≤ dist z c from lt_of_le_of_lt this hz
  rw [dist_eq_re_im, dist_eq_re_im, Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  simp [sq_nonneg _]
/-
**Complex.mem_ball_re_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_ball_re_aux (hx : x ∈ Ioo (z.re - (r - dist z c)) (z.re + (r - dist z c))) :
    x + z.im * I ∈ ball c r := by
  set r₁ := r - dist z c
  set s := Ioo (z.re - r₁) (z.re + r₁)
  have s_ball₁ : s ×ℂ {z.im} ⊆ ball z r₁ := by
    rintro y ⟨yRe : y.re ∈ s, yIm : y.im = z.im⟩
    rw [mem_ball, dist_eq_re_im, yIm, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
    grind [abs_lt]
  suffices s ×ℂ {z.im} ⊆ ball c r from this <| by simp [mem_reProdIm, hx]
  exact s_ball₁.trans <| ball_subset_ball' <| by simp [r₁]
/-
**Complex.mem_closedBall_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_closedBall_aux (z_in_ball : z ∈ closedBall c r) (y_in_I : y ∈ Ι c.im z.im) :
    z.re + y * I ∈ closedBall c r := by
  refine le_trans ?_ (mem_closedBall.mp z_in_ball)
  rw [dist_eq_re_im, dist_eq_re_im, Real.le_sqrt (by positivity) (by positivity),
    Real.sq_sqrt (by positivity)]
  suffices (y - c.im) ^ 2 ≤ (z.im - c.im) ^ 2 by simpa
  cases mem_uIoc.mp y_in_I <;> nlinarith
/-
**Complex.mem_ball_of_map_re_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_ball_of_map_re_aux {a₁ a₂ b : ℝ} (ha₁ : a₁ + b * I ∈ ball c r)
    (ha₂ : a₂ + b * I ∈ ball c r) : (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] ⊆ ball c r := by
  convert Convex.rectangle_subset (convex_ball c r) ha₁ ha₂ ?_ ?_ <;>
  simp [horizontalSegment_eq a₁ a₂ b, ha₁, ha₂, Rectangle]
/-
**Complex.mem_ball_of_map_im_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_ball_of_map_im_aux₁ {a b₁ b₂ : ℝ} (hb₁ : a + b₁ * I ∈ ball c r)
    (hb₂ : a + b₂ * I ∈ ball c r) : (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] ⊆ ball c r := by
  convert Convex.rectangle_subset (convex_ball c r) hb₁ hb₂ ?_ ?_ <;>
  simp [verticalSegment_eq a b₁ b₂, hb₁, hb₂, Rectangle]
/-
**Complex.mem_ball_of_map_im_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mem_ball_of_map_im_aux₂ {w : ℂ} (hw : w ∈ ball z (r - dist z c)) :
    (fun (y : ℝ) ↦ w.re + y * I) '' [[z.im, w.im]] ⊆ ball c r := by
  apply mem_ball_of_map_im_aux₁ <;>
  apply mem_of_subset_of_mem (ball_subset_ball' (by simp) : ball z (r - dist z c) ⊆ ball c r)
  · exact re_add_im_mul_mem_ball hw
  · simpa using hw

end AuxiliaryLemmata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `(z, w)`-wedge-integral of `f`, is the integral of `f` over two sides of the rectangle
  determined by `z` and `w`. -/
/-
**Complex.wedgeIntegral** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：wedgeIntegral (z w : Complex) (f : Complex -> E) : E
参数：z w : Complex；f : Complex -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `(z, w)`-wedge-integral of `f`, is the integral of `f` over two sides of the
 rectangle
  determined by `z` and `w`.
-/
def wedgeIntegral (z w : ℂ) (f : ℂ → E) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I))
/-
**Complex.wedgeIntegral_add_wedgeIntegral_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`
。
形式化陈述：wedgeIntegral_add_wedgeIntegral_eq (z w : Complex) (f : Complex -> E) : we
dgeIntegral z w f + wedgeIntegral w z f = (∫ x : Real in z.re..w.re, f (x + z.im
 * I)) - (∫ x : Real in z.re..w.re, f (x + w.im * I)) + I • (∫ y : Real in z.im.
.w.im, f (w.re + y * I)) - I • (∫ y : Real in z.im..w.im, f (z.re + y * I))
参数：z w : Complex；f : Complex -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `_private.Mathlib.Analysis.Complex.HasPrimitives.0.Complex.wedgeIntegral_
add_wedgeIntegral_eq._abel_1_2`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [
inst_1 : NormedSpace ℂ E] (z w : ℂ) (f : ℂ → E),   ((∫ (x : ℝ) in z.re..w.re, f 
(↑x + ↑z.im …
-/
lemma wedgeIntegral_add_wedgeIntegral_eq (z w : ℂ) (f : ℂ → E) :
    wedgeIntegral z w f + wedgeIntegral w z f =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) := by
  simp only [wedgeIntegral, intervalIntegral.integral_symm z.re w.re,
    intervalIntegral.integral_symm z.im w.im, smul_neg]
  abel

/-- A function `f` `IsConservativeOn` in `U` if, for any rectangle contained in `U`
  the integral of `f` over the rectangle is zero. -/
/-
**Complex.IsConservativeOn** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：IsConservativeOn (f : Complex -> E) (U : Set Complex) : Prop
参数：f : Complex -> E；U : Set Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` `IsConservativeOn` in `U` if, for any rectangle contained in `U`
  the integral of `f` over the rectangle is zero.
-/
def IsConservativeOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ z w, Rectangle z w ⊆ U → wedgeIntegral z w f = - wedgeIntegral w z f

/-- A function `f` `IsExactOn` in `U` if it is the complex derivative of a function on `U`.

In complex variable theory, this is also referred to as "having a primitive". -/
/-
**Complex.IsExactOn** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：IsExactOn (f : Complex -> E) (U : Set Complex) : Prop
参数：f : Complex -> E；U : Set Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` `IsExactOn` in `U` if it is the complex derivative of a function 
on `U`.

In complex variable theory, this is also referred to as "having a primitive".
-/
def IsExactOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∃ g, ∀ z ∈ U, HasDerivAt g (f z) z
/-
**Complex.IsExactOn.with_val_at** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsExactOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} {s : Set ℂ},   Complex.IsExactOn f s → ∀ (x₀ : ℂ) (y : E), ∃ g, g x₀
 = y ∧ ∀ x ∈ s, HasDerivAt g (f x) x
参数：x₀ : ℂ；y : E；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsExactOn.with_val_at {f : ℂ → E} {s : Set ℂ} (h : IsExactOn f s) (x₀ : ℂ) (y : E) :
    ∃ g, g x₀ = y ∧ ∀ x ∈ s, HasDerivAt g (f x) x := by
  obtain ⟨η, hη⟩ := h
  use fun z ↦ η z - η x₀ + y, by simp, by simpa using hη

variable {c : ℂ} {r : ℝ} {f : ℂ → E}
/-
**Complex.IsConservativeOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsConservativ
eOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} {U V : Set ℂ},   U ⊆ V → Complex.IsConservativeOn f V → Complex.IsCo
nservativeOn f U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma IsConservativeOn.mono {U V : Set ℂ} (h : U ⊆ V) (hf : IsConservativeOn f V) :
    IsConservativeOn f U :=
  fun z w hzw ↦ hf z w (hzw.trans h)
/-
**Complex._root_.DifferentiableOn.isConservativeOn** 是 Mathlib 中的一个定理，位于命名空间 `Co
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableOn.isConservativeOn {U : Set ℂ} (hf : DifferentiableOn ℂ f U) :
    IsConservativeOn f U := by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  exact integral_boundary_rect_eq_zero_of_differentiableOn f z w <| hf.mono hzw

variable [CompleteSpace E]
/-
**Complex.IsExactOn.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsExactO
n`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} [CompleteSpace E] {U : Set ℂ},   IsOpen U → Complex.IsExactOn f U → 
DifferentiableOn ℂ f U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableOn_congr`：differentiableOn_congr (h' : forall x in s, f₁ x
 = f x) : DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `DifferentiableOn.deriv`：∀ {E : Type u} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Differentia
bleOn ℂ f s …
-/
lemma IsExactOn.differentiableOn {U : Set ℂ} (hU : IsOpen U) (hf : IsExactOn f U) :
    DifferentiableOn ℂ f U := by
  obtain ⟨g, hg⟩ := hf
  have hg' : DifferentiableOn ℂ g U := fun z hz ↦ (hg z hz).differentiableAt.differentiableWithinAt
  exact (differentiableOn_congr <| fun z hz ↦ (hg z hz).deriv).mp <| hg'.deriv hU

section ContinuousOnBall

variable (f_cont : ContinuousOn f (ball c r)) {z : ℂ} (hz : z ∈ ball c r)
include f_cont hz

set_option linter.style.whitespace false in -- manual alignment is not recognised
omit [CompleteSpace E] in
/-- If a function `f` `IsConservativeOn` on a disk of center `c`, then for points `z` in this disk,
the wedge integral from `c` to `z` is additive under a detour through a nearby point `w`. -/
/-
**Complex.IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral** 是 M
athlib 中的一个定理，位于命名空间 `Complex.IsConservativeOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{c : ℂ} {r : ℝ} {f : ℂ → E},   ContinuousOn f (Metric.ball c r) →     ∀ {z : ℂ},
       z ∈ Metric.ball c r →         Complex.IsConservativeOn f (Metric.ball c r
) →           ∀ᶠ (w : ℂ) in nhds z, c.wedgeIntegral w f - c.wedgeIntegral z f = 
z.wedgeIntegral w f
参数：Metric.ball c r；Metric.ball c r；w : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.ball_subset_ball'`：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : 
ball x ε₁ subseteq ball y ε₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `_private.Mathlib.Analysis.Complex.HasPrimitives.0.Complex.mem_ball_of_ma
p_re_aux`：∀ {c : ℂ} {r a₁ a₂ b : ℝ},   ↑a₁ + ↑b * Complex.I ∈ Metric.ball c r → 
    ↑a₂ + ↑b * Complex.I ∈ Metric.ball c r → (fun x => ↑x + ↑b * Compl…
· 使用定理 `ContinuousOn.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f` `IsConservativeOn` on a disk of center `c`, then for points `z
` in this disk,
the wedge integral from `c` to `z` is additive under a detour through a nearby p
oint `w`.
-/
lemma IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
    (hf : IsConservativeOn f (ball c r)) :
    ∀ᶠ w in 𝓝 z, wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w w_in_z_ball ↦ ?_⟩
  set I₁ :=     ∫ x in c.re..w.re, f (x + c.im * I)
  set I₂ := I • ∫ y in c.im..w.im, f (w.re + y * I)
  set I₃ :=     ∫ x in c.re..z.re, f (x + c.im * I)
  set I₄ := I • ∫ y in c.im..z.im, f (z.re + y * I)
  set I₅ :=     ∫ x in z.re..w.re, f (x + z.im * I)
  set I₆ := I • ∫ y in z.im..w.im, f (w.re + y * I)
  set I₇ :=     ∫ x in z.re..w.re, f (x + c.im * I)
  set I₈ := I • ∫ y in c.im..z.im, f (w.re + y * I)
  have z_ball : ball z (r - dist z c) ⊆ ball c r := ball_subset_ball' (by simp)
  have w_mem : w ∈ ball c r := mem_of_subset_of_mem z_ball w_in_z_ball
  have integrableHoriz (a₁ a₂ b : ℝ) (ha₁ : a₁ + b * I ∈ ball c r) (ha₂ : a₂ + b * I ∈ ball c r) :
      IntervalIntegrable (fun x ↦ f (x + b * I)) volume a₁ a₂ :=
    ((f_cont.mono (mem_ball_of_map_re_aux ha₁ ha₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have integrableVert (a b₁ b₂ : ℝ) (hb₁ : a + b₁ * I ∈ ball c r) (hb₂ : a + b₂ * I ∈ ball c r) :
      IntervalIntegrable (fun y ↦ f (a + y * I)) volume b₁ b₂ :=
    ((f_cont.mono (mem_ball_of_map_im_aux₁ hb₁ hb₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableHoriz
    · exact re_add_im_mul_mem_ball <| mem_ball_self (pos_of_mem_ball hz)
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball hz
    · exact re_add_im_mul_mem_ball w_mem
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrableVert
    · exact re_add_im_mul_mem_ball w_mem
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · exact mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    · simpa using w_mem
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have wzInBall : w.re + z.im * I ∈ ball c r :=
      mem_of_subset_of_mem z_ball (re_add_im_mul_mem_ball w_in_z_ball)
    have wcInBall : w.re + c.im * I ∈ ball c r := re_add_im_mul_mem_ball w_mem
    have hU : Rectangle (z.re + c.im * I) (w.re + z.im * I) ⊆ ball c r :=
      (convex_ball c r).rectangle_subset (re_add_im_mul_mem_ball hz) wzInBall
        (by simpa using hz) (by simpa using wcInBall)
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf (z.re + c.im * I) (w.re + z.im * I) hU
  grind [wedgeIntegral]

/- The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z).re * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
/-
**Complex.hasDerivAt_wedgeIntegral_re_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal integral of `f` from `z` to `z.re + w.im * I` is equal to `(w - z
).re * f z`
  up to `o(w - z)`, as `w` tends to `z`.
-/
private lemma hasDerivAt_wedgeIntegral_re_aux :
    (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun x ↦ (∫ t in z.re..x, f (t + z.im * I)) - (x - z.re) • f z) =o[𝓝 z.re]
      fun x ↦ x - z.re from
    this.comp_tendsto (continuous_re.tendsto z) |>.trans_isBigO isBigO_re_sub_re
  let r₁ := r - dist z c
  have r₁_pos : 0 < r₁ := by simpa only [mem_ball, sub_pos, r₁] using hz
  let s : Set ℝ := Ioo (z.re - r₁) (z.re + r₁)
  have zRe_mem_s : z.re ∈ s := by simp [s, r₁_pos]
  have f_contOn : ContinuousOn (fun (x : ℝ) ↦ f (x + z.im * I)) s :=
    f_cont.comp ((continuous_add_const _).comp continuous_ofReal).continuousOn <|
      fun _ ↦ mem_ball_re_aux
  have int1 : IntervalIntegrable (fun (x : ℝ) ↦ f (x + z.im * I)) volume z.re z.re :=
    ContinuousOn.intervalIntegrable <| f_contOn.mono <| by simpa
  have int2 : StronglyMeasurableAtFilter (fun (x : ℝ) ↦ f (x + z.im * I)) (𝓝 z.re) :=
    f_contOn.stronglyMeasurableAtFilter isOpen_Ioo _ zRe_mem_s
  have int3 : ContinuousAt (fun (x : ℝ) ↦ f (x + z.im * I)) z.re :=
    isOpen_Ioo.continuousOn_iff.mp f_contOn zRe_mem_s
  simpa using intervalIntegral.integral_hasDerivAt_right int1 int2 int3 |>.isLittleO

/-- The vertical integral of `f` from `w.re + z.im * I` to `w` is equal to `(w - z).im * f z`
  up to `o(w - z)`, as `w` tends to `z`. -/
/-
**Complex.hasDerivAt_wedgeIntegral_im_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical integral of `f` from `w.re + z.im * I` to `w` is equal to `(w - z).
im * f z`
  up to `o(w - z)`, as `w` tends to `z`.
-/
private lemma hasDerivAt_wedgeIntegral_im_aux :
    (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) =o[𝓝 z] fun w ↦ w - z := by
  suffices (fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z) =o[𝓝 z] fun w ↦ w - z by
    calc
      _ = fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (∫ _ in z.im..w.im, f z) := by simp
      _ =ᶠ[𝓝 z] fun w ↦ ∫ y in z.im..w.im, f (w.re + y * I) - f z := ?_
      _ =o[𝓝 z] fun w ↦ w - z := this
    refine eventually_nhds_iff_ball.mpr ⟨r - dist z c, by simpa using hz, fun w hw ↦ ?_⟩
    exact (intervalIntegral.integral_sub
      ((f_cont.mono (mem_ball_of_map_im_aux₂ hw)).comp (by fun_prop)
        (mapsTo_image _ _)).intervalIntegrable intervalIntegrable_const).symm
  have : (fun w ↦ f w - f z) =o[𝓝 z] fun _ ↦ (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
    exact f_cont.continuousAt <| _root_.mem_nhds_iff.mpr ⟨ball c r, le_refl _, isOpen_ball, hz⟩
  rw [Asymptotics.IsLittleO] at this ⊢
  intro ε ε_pos
  replace := this ε_pos
  simp only [Asymptotics.isBigOWith_iff, norm_one, mul_one] at this ⊢
  replace this : ∀ᶠ w in 𝓝 z, ∀ y ∈ Ι z.im w.im, ‖f (w.re + y * I) - f z‖ ≤ ε := by
    rw [Metric.nhds_basis_closedBall.eventually_iff] at this ⊢
    obtain ⟨i, i_pos, hi⟩ := this
    exact ⟨i, i_pos, fun w w_in_ball y y_in_I ↦ hi (mem_closedBall_aux w_in_ball y_in_I)⟩
  filter_upwards [this] with w hw
  calc
    _ ≤ ε * ‖w.im - z.im‖ := intervalIntegral.norm_integral_le_of_norm_le_const hw
    _ = ε * ‖(w - z).im‖ := by simp
    _ ≤ ε * ‖w - z‖ := (mul_le_mul_iff_of_pos_left ε_pos).mpr (abs_im_le_norm _)

/-- The `wedgeIntegral` has derivative at `z` equal to `f z`. -/
/-
**Complex.IsConservativeOn.hasDerivAt_wedgeIntegral** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex.IsConservativeOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{c : ℂ} {r : ℝ} {f : ℂ → E} [CompleteSpace E],   ContinuousOn f (Metric.ball c r
) →     ∀ {z : ℂ},       z ∈ Metric.ball c r →         Complex.IsConservativeOn 
f (Metric.ball c r) → HasDerivAt (fun w => c.wedgeIntegral w f) (f z) z
参数：Metric.ball c r；Metric.ball c r；fun w => c.wedgeIntegral w f；f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_isLittleO`：hasDerivAt_iff_isLittleO : HasDerivAt f f' x ↔
 (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral
`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {c :
 ℂ} {r : ℝ} {f : ℂ → E},   ContinuousOn f (Metric.ball c r) → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `_private.Mathlib.Analysis.Complex.HasPrimitives.0.Complex.IsConservative
On.hasDerivAt_wedgeIntegral._abel_1_1`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} (w : ℂ),   ((∫ (x : ℝ) in z
.re..w.re, f (↑x + …
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `_private.Mathlib.Analysis.Complex.HasPrimitives.0.Complex.hasDerivAt_wed
geIntegral_re_aux`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E} [CompleteSpace E],   ContinuousOn f (M…
· 使用定理 `Asymptotics.IsLittleO.const_smul_left`：∀ {α : Type u_1} {F : Type u_4} {
E' : Type u_6} {R : Type u_13} [inst : Norm F] [inst_1 : SeminormedAddCommGroup 
E']   [inst_2 : SeminormedR…
· 使用定理 `_private.Mathlib.Analysis.Complex.HasPrimitives.0.Complex.hasDerivAt_wed
geIntegral_im_aux`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E} [CompleteSpace E],   ContinuousOn f (M…

--- 原说明 ---
The `wedgeIntegral` has derivative at `z` equal to `f z`.
-/
theorem IsConservativeOn.hasDerivAt_wedgeIntegral (h : IsConservativeOn f (ball c r)) :
    HasDerivAt (fun w ↦ wedgeIntegral c w f) (f z) z := by
  rw [hasDerivAt_iff_isLittleO]
  calc
    _ =ᶠ[𝓝 z] (fun w ↦ wedgeIntegral z w f - (w - z) • f z) := ?_
    _ = (fun w ↦ (∫ x in z.re..w.re, f (x + z.im * I)) - (w - z).re • f z)
        + I • (fun w ↦ (∫ y in z.im..w.im, f (w.re + y * I)) - (w - z).im • f z) := ?_
    _ =o[𝓝 z] fun w ↦ w - z := (hasDerivAt_wedgeIntegral_re_aux f_cont hz).add
        ((hasDerivAt_wedgeIntegral_im_aux f_cont hz).const_smul_left I)
  · exact (h.eventually_nhds_wedgeIntegral_sub_wedgeIntegral f_cont hz).mono <| by simp
  ext w
  set I₁ := ∫ x in z.re..w.re, f (x + z.im * I)
  set I₂ := ∫ y in z.im..w.im, f (w.re + y * I)
  calc
    _ = I₁ + I • I₂ - ((w - z).re + (w - z).im * I) • f z := by congr; rw [re_add_im]
    _ = I₁ + I • I₂ - ((w.re - z.re : ℂ) + (w.im - z.im) * I) • f z := by simp
    _ = I₁ - (w.re - z.re : ℂ) • f z + I • (I₂ - (w.im - z.im : ℂ) • f z) := ?_
  · rw [add_smul, smul_sub, smul_smul, mul_comm I]; abel
  · congr <;> simp

end ContinuousOnBall

/-- **Morera's theorem for a disk** On a disk, a continuous function whose integrals on rectangles
  vanish, has primitives. -/
/-
**Complex.IsConservativeOn.isExactOn_ball** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsC
onservativeOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{c : ℂ} {r : ℝ} {f : ℂ → E} [CompleteSpace E],   ContinuousOn f (Metric.ball c r
) →     Complex.IsConservativeOn f (Metric.ball c r) → Complex.IsExactOn f (Metr
ic.ball c r)
参数：Metric.ball c r；Metric.ball c r；Metric.ball c r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.IsConservativeOn.hasDerivAt_wedgeIntegral`：∀ {E : Type u_1} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E}
 [CompleteSpace E],   ContinuousOn f (M…

--- 原说明 ---
**Morera's theorem for a disk** On a disk, a continuous function whose integrals
 on rectangles
  vanish, has primitives.
-/
theorem IsConservativeOn.isExactOn_ball (hf' : ContinuousOn f (ball c r))
    (hf : IsConservativeOn f (ball c r)) :
    IsExactOn f (ball c r) :=
  ⟨fun z ↦ wedgeIntegral c z f, fun _ ↦ hf.hasDerivAt_wedgeIntegral hf'⟩
/-
**Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn** 是 Mathlib 中
的一个定理，位于命名空间 `Complex`。
形式化陈述：isConservativeOn_and_continuousOn_iff_isDifferentiableOn {U : Set Complex}
 (hU : IsOpen U) : IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn Co
mplex f U
参数：hU : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Complex.IsExactOn.differentiableOn`：∀ {E : Type u_1} [inst : NormedAddCo
mmGroup E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} [CompleteSpace E] {U : Set ℂ},
   IsOpen U → Complex.Is…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Complex.IsConservativeOn.isExactOn_ball`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E} [Complete
Space E],   ContinuousOn f (M…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Complex.IsConservativeOn.mono`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {U V : Set ℂ},   U ⊆ V → Complex.Is
ConservativeOn f V …
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `DifferentiableOn.isConservativeOn`：∀ {E : Type u_1} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {U : Set ℂ},   DifferentiableOn
 ℂ f U → Complex.IsCons…
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    {U : Set ℂ} (hU : IsOpen U) :
    IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn ℂ f U := by
  refine ⟨fun ⟨hf, hf'⟩ z hz ↦ ?_, fun hf ↦ ⟨hf.isConservativeOn, hf.continuousOn⟩⟩
  obtain ⟨r, h₀, h₁⟩ : ∃ r > 0, ball z r ⊆ U := Metric.isOpen_iff.mp hU z hz
  have : DifferentiableOn ℂ f (ball z r) :=
    (IsConservativeOn.isExactOn_ball (hf'.mono h₁) (hf.mono h₁)).differentiableOn isOpen_ball
  apply (this z (mem_ball_self h₀)).mono_of_mem_nhdsWithin
  exact mem_nhdsWithin.mpr ⟨ball z r, isOpen_ball, mem_ball_self h₀, inter_subset_left⟩

/-- **Morera's theorem for a disk** On a disk, a holomorphic function has primitives. -/
/-
**Complex._root_.DifferentiableOn.isExactOn_ball** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Morera's theorem for a disk** On a disk, a holomorphic function has primitives
.
-/
theorem _root_.DifferentiableOn.isExactOn_ball (hf : DifferentiableOn ℂ f (ball c r)) :
    IsExactOn f (ball c r) :=
  hf.isConservativeOn.isExactOn_ball hf.continuousOn

/--
**Morera's theorem for the complex plane** A continuous function on `ℂ` whose integrals on
rectangles vanish, has primitives.
-/
/-
**Complex.IsConservativeOn.isExactOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsC
onservativeOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} [CompleteSpace E],   Continuous f → Complex.IsConservativeOn f Set.u
niv → Complex.IsExactOn f Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.IsConservativeOn.mono`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {U V : Set ℂ},   U ⊆ V → Complex.Is
ConservativeOn f V …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Complex.IsConservativeOn.hasDerivAt_wedgeIntegral`：∀ {E : Type u_1} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {c : ℂ} {r : ℝ} {f : ℂ → E}
 [CompleteSpace E],   ContinuousOn f (M…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
**Morera's theorem for the complex plane** A continuous function on `ℂ` whose in
tegrals on
rectangles vanish, has primitives.
-/
theorem IsConservativeOn.isExactOn_univ (h₁ : Continuous f) (h₂ : IsConservativeOn f univ) :
    IsExactOn f univ := by
  use (wedgeIntegral 0 · f)
  intro z _
  have h₃ : IsConservativeOn f (ball 0 (‖z‖ + 1)) := h₂.mono (subset_univ _)
  exact h₃.hasDerivAt_wedgeIntegral (by fun_prop) (by aesop)

/--
**Morera's theorem for the complex plane** A holomorphic function on `ℂ` has
primitives.
-/
/-
**Complex._root_.Differentiable.isExactOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Morera's theorem for the complex plane** A holomorphic function on `ℂ` has
primitives.
-/
theorem _root_.Differentiable.isExactOn_univ (hf : Differentiable ℂ f) : IsExactOn f univ := by
  apply IsConservativeOn.isExactOn_univ hf.continuous
    ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2 hf.differentiableOn).1

end Complex

