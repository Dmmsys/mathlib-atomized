/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Tactic.SuppressCompilation

/-!
# Operator norm on the space of continuous linear maps

Define the operator (semi)-norm on the space of continuous (semi)linear maps between (semi)-normed
spaces, and prove its basic properties. In particular, show that this space is itself a semi-normed
space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup`. Later we will specialize to `NormedAddCommGroup` in the
file `NormedSpace.lean`.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

## Main Results
* `ball_subset_range_iff_surjective` (and its variants) shows that a semi-linear map between normed
  spaces is surjective if and only if it contains a ball.

-/

@[expose] public section

suppress_compilation

open Bornology Metric
open Filter hiding map_smul
open scoped NNReal Topology Uniformity ENNReal

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Fₗ]
  [SeminormedAddCommGroup G]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

section

variable [SemilinearMapClass 𝓕 σ₁₂ E F]

/-
**ball_zero_subset_range_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_zero_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {r :
 Real} (hr : 0 < r) : ball 0 r subseteq Set.range f ↔ (⇑f).Surjective
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbent.subset_range_iff_surjective`：Absorbent.subset_range_iff_surjec
tive [RingHomSurjective σ] {f : F ->ₛₗ[σ] E} {s : Set E} (hs_abs : Absorbent 𝕜 s
) : s subseteq f.range ↔ (⇑…
· 使用定理 `absorbent_ball`：absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball
 x r)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem ball_zero_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {r : ℝ}
    (hr : 0 < r) : ball 0 r ⊆ Set.range f ↔ (⇑f).Surjective :=
  absorbent_ball (by simpa) |>.subset_range_iff_surjective (f := (f : E →ₛₗ[σ₁₂] F))
/-
**ball_subset_range_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {
r : Real} (hr : 0 < r) : ball x r subseteq Set.range f ↔ (⇑f).Surjective
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_zero_subset_range_iff_surjective`：ball_zero_subset_range_iff_surjec
tive [RingHomSurjective σ₁₂] {f : 𝓕} {r : Real} (hr : 0 < r) : ball 0 r subseteq
 Set.range f ↔ (⇑f).Surject…
· 使用引理 `LinearMap.coe_coe`：coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapCl
ass F σ M M₃] {f : F} : ⇑(f : M ->ₛₗ[σ] M₃) = f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_add_self_left`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (
a b : E), dist (b + a) a = ‖b‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ball_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : ℝ}
    (hr : 0 < r) : ball x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr, ← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E →ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all
/-
**closedBall_subset_range_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} (x 
: F) {r : Real} (hr : 0 < r) : closedBall (x : F) r subseteq Set.range f ↔ (⇑f).
Surjective
参数：x : F；hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ball_subset_range_iff_surjective`：ball_subset_range_iff_surjective [Ring
HomSurjective σ₁₂] {f : 𝓕} {x : F} {r : Real} (hr : 0 < r) : ball x r subseteq S
et.range f ↔ (⇑f).Surj…
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem closedBall_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : ℝ}
    (hr : 0 < r) : closedBall (x : F) r ⊆ Set.range f ↔ (⇑f).Surjective :=
  ⟨fun h ↦ (ball_subset_range_iff_surjective hr).mp <| subset_trans ball_subset_closedBall h,
    by simp_all⟩

variable {F' 𝓕' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [Nontrivial F']
  {τ : 𝕜 →+* ℝ} [FunLike 𝓕' E F'] [SemilinearMapClass 𝓕' τ E F']
/-
**sphere_subset_range_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_subset_range_iff_surjective [RingHomSurjective τ] {f : 𝓕'} {x : F'}
 {r : Real} (hr : 0 < r) : sphere x r subseteq Set.range f ↔ (⇑f).Surjective
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closedBall_subset_range_iff_surjective`：closedBall_subset_range_iff_surj
ective [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : Real} (hr : 0 < r) : closedB
all (x : F) r subseteq Set.r…
· 使用定理 `convexHull_sphere_eq_closedBall`：convexHull_sphere_eq_closedBall {F : Ty
pe*} [NormedAddCommGroup F] [NormedSpace Real F] [Nontrivial F] (x : F) {r : Rea
l} (hr : 0 <= r) : co…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `convexHull_eq_self`：convexHull_eq_self : convexHull 𝕜 s = s ↔ Convex 𝕜 s
· 使用定理 `Submodule.Convex.semilinear_range`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
_root_.Module 𝕜 E] {𝕜' …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sphere_subset_range_iff_surjective [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : ℝ}
    (hr : 0 < r) : sphere x r ⊆ Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := ℝ) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

end

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
/-
**norm_image_of_norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_image_of_norm_eq_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Co
ntinuous f) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0
参数：f : 𝓕；hf : Continuous f；hx : ‖x‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_closure_zero_iff_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E
] {x : E}, x ∈ closure {0} ↔ ‖x‖ = 0
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y

--- 原说明 ---
If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`.
-/
theorem norm_image_of_norm_eq_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f)
    {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map hf

section

variable [RingHomIsometric σ₁₂]

/-
**SemilinearMapClass.bound_of_shell_semi_normed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E 
F] (f : 𝓕) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε
 / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖) {x : E} (hx : ‖x‖ != 0) : ‖f x‖ <=
 C * ‖x‖
参数：f : 𝓕；ε_pos : 0 < ε；hc : 1 < ‖c‖；hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> 
‖f x‖ <= C * ‖x‖；hx : ‖x‖ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.bound_of_shell`：bound_of_shell (p q : Seminorm 𝕜 E) {ε C : Real
} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= p x -> p x <
 ε -> q x <= …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * ‖x‖ :=
  (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
/-
**SemilinearMapClass.bound_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f :
 𝓕) (hf : Continuous f) : exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖
参数：f : 𝓕；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `Seminorm.bound_of_continuous_normedSpace`：bound_of_continuous_normedSpac
e (q : Seminorm 𝕜 F) (hq : Continuous q) : exists C, 0 < C ∧ (forall x : F, q x 
<= C * ‖x‖)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖

--- 原说明 ---
A continuous linear map between seminormed spaces is bounded when the field is n
ontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The non
triviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, 
whose image has a
controlled norm. The norm control for the original element follows by rescaling.
-/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  let φ : E →ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)
/-
**SemilinearMapClass.nnbound_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilinearMapClass.nnbound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f
 : 𝓕) (hf : Continuous f) : exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖₊ <= 
C * ‖x‖₊
参数：f : 𝓕；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.bound_of_continuous`：SemilinearMapClass.bound_of_cont
inuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) : exists C, 0 
< C ∧ forall x : E, ‖f x‖ <=…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem SemilinearMapClass.nnbound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.bound_of_continuous f hf; ⟨⟨c, hc.le⟩, hc, hcf⟩
/-
**SemilinearMapClass.ebound_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilinearMapClass.ebound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f 
: 𝓕) (hf : Continuous f) : exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖ₑ <= C
 * ‖x‖ₑ
参数：f : 𝓕；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.nnbound_of_continuous`：SemilinearMapClass.nnbound_of_
continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) : exists C
 : Real>=0, 0 < C ∧ forall x :…
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
-/
theorem SemilinearMapClass.ebound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖ₑ ≤ C * ‖x‖ₑ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.nnbound_of_continuous f hf
  ⟨c, hc, fun x => ENNReal.coe_mono <| hcf x⟩

end

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：bound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) : exists C, 0 < C ∧ foral
l x : E, ‖f x‖ <= C * ‖x‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.bound_of_continuous`：SemilinearMapClass.bound_of_cont
inuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) : exists C, 0 
< C ∧ forall x : E, ‖f x‖ <=…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
theorem bound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2
/-
**ContinuousLinearMap.nnbound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：nnbound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) : exists C : Real>=0, 0
 < C ∧ forall x : E, ‖f x‖₊ <= C * ‖x‖₊
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.nnbound_of_continuous`：SemilinearMapClass.nnbound_of_
continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) : exists C
 : Real>=0, 0 < C ∧ forall x :…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
theorem nnbound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  SemilinearMapClass.nnbound_of_continuous f f.2
/-
**ContinuousLinearMap.ebound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：ebound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) : exists C : Real>=0, 0 
< C ∧ forall x : E, ‖f x‖ₑ <= C * ‖x‖ₑ
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.ebound_of_continuous`：SemilinearMapClass.ebound_of_co
ntinuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) : exists C :
 Real>=0, 0 < C ∧ forall x : …
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
theorem ebound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x : E, ‖f x‖ₑ ≤ C * ‖x‖ₑ :=
  SemilinearMapClass.ebound_of_continuous f f.2

section

open Filter

variable (𝕜 E)

/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
isometry map from `𝕜` to `E` by taking multiples of `x`. -/
/-
**ContinuousLinearMap._root_.LinearIsometry.toSpanSingleton** 是 Mathlib 中的一个定义，位
于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natu
ral linear
isometry map from `𝕜` to `E` by taking multiples of `x`.
-/
def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }

variable {𝕜 E}

@[simp]
/-
**ContinuousLinearMap._root_.LinearIsometry.toSpanSingleton_apply** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl

@[simp]
/-
**ContinuousLinearMap._root_.LinearIsometry.coe_toSpanSingleton** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl

end

section OpNorm

open Set Real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
/-
**ContinuousLinearMap.opNorm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：opNorm (f : E ->SL[σ₁₂] F)
参数：f : E ->SL[σ₁₂] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operator norm of a continuous linear map is the inf of all its bounds.
-/
def opNorm (f : E →SL[σ₁₂] F) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
/-
**ContinuousLinearMap.hasOpNorm** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
形式化陈述：hasOpNorm : Norm (E ->SL[σ₁₂] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasOpNorm : Norm (E →SL[σ₁₂] F) :=
  ⟨opNorm⟩
/-
**ContinuousLinearMap.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：norm_def (f : E ->SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <
= c * ‖x‖ }
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/-
**ContinuousLinearMap.bounds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：bounds_nonempty [RingHomIsometric σ₁₂] {f : E ->SL[σ₁₂] F} : exists c, c i
n { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.bound`：bound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂]
 F) : exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E →SL[σ₁₂] F} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
/-
**ContinuousLinearMap.bounds_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：bounds_bddBelow {f : E ->SL[σ₁₂] F} : BddBelow { c | 0 <= c ∧ forall x, ‖f
 x‖ <= c * ‖x‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bounds_bddBelow {f : E →SL[σ₁₂] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
/-
**ContinuousLinearMap.isLeast_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isLeast_opNorm [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) : IsLeast {c | 0
 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖} ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isLeast_csInf`：IsClosed.isLeast_csInf {s : Set α} (hc : IsClose
d s) (hs : s.Nonempty) (B : BddBelow s) : IsLeast s (sInf s)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousLinearMap.bounds_nonempty`：bounds_nonempty [RingHomIsometric σ
₁₂] {f : E ->SL[σ₁₂] F} : exists c, c in { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖
x‖ }
· 使用定理 `ContinuousLinearMap.bounds_bddBelow`：bounds_bddBelow {f : E ->SL[σ₁₂] F}
 : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
theorem isLeast_opNorm [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [ofPred_and, ofPred_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> fun_prop

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
/-
**ContinuousLinearMap.opNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opNorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M) (hM : forall
 x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
参数：f : E ->SL[σ₁₂] F；hMp : 0 <= M；hM : forall x, ‖f x‖ <= M * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `ContinuousLinearMap.bounds_bddBelow`：bounds_bddBelow {f : E ->SL[σ₁₂] F}
 : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

--- 原说明 ---
If one controls the norm of every `A x`, then one controls the norm of `A`.
-/
theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
/-
**ContinuousLinearMap.opNorm_le_bound'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opNorm_le_bound' (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M) (hM : foral
l x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
参数：f : E ->SL[σ₁₂] F；hMp : 0 <= M；hM : forall x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_image_of_norm_eq_zero`：norm_image_of_norm_eq_zero [SemilinearMapCla
ss 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm o
f `A`.
-/
theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f f.2 h, le_refl]
/-
**ContinuousLinearMap.opNorm_eq_of_bounds** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：opNorm_eq_of_bounds {φ : E ->SL[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_
above : forall x, ‖φ x‖ <= M * ‖x‖) (h_below : forall N >= 0, (forall x, ‖φ x‖ <
= N * ‖x‖) -> M <= N) : ‖φ‖ = M
参数：M_nonneg : 0 <= M；h_above : forall x, ‖φ x‖ <= M * ‖x‖；h_below : forall N >= 
0, (forall x, ‖φ x‖ <= N * ‖x‖) -> M <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_csInf_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {
s : Set α} {a : α},   BddBelow s → s.Nonempty → (a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b)
· 使用定理 `ContinuousLinearMap.bounds_bddBelow`：bounds_bddBelow {f : E ->SL[σ₁₂] F}
 : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
theorem opNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
/-
**ContinuousLinearMap.opNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：opNorm_neg (f : E ->SL[σ₁₂] F) : ‖-f‖ = ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNorm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]
/-
**ContinuousLinearMap.opNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0 <= ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sInf_nonneg`：sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem opNorm_nonneg (f : E →SL[σ₁₂] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ ↦ And.left

/-- The norm of the `0` operator is `0`. -/
/-
**ContinuousLinearMap.opNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：opNorm_zero : ‖(0 : E ->SL[σ₁₂] F)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖

--- 原说明 ---
The norm of the `0` operator is `0`.
-/
theorem opNorm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun _ ↦ by simp) (opNorm_nonneg _)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one cannot do better than an inequality in general. -/
/-
**ContinuousLinearMap.norm_id_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The norm of the identity is at most `1`. It is in fact `1`, except when the spac
e is trivial
where it is `0`. It means that one cannot do better than an inequality in genera
l.
-/
theorem norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
/-
**ContinuousLinearMap.le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousLinearMap.isLeast_opNorm`：isLeast_opNorm [RingHomIsometric σ₁₂
] (f : E ->SL[σ₁₂] F) : IsLeast {c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖} ‖f‖

--- 原说明 ---
The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`.
-/
theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
/-
**ContinuousLinearMap.dist_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：dist_le_opNorm (x y : E) : dist (f x) (f y) <= ‖f‖ * dist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem dist_le_opNorm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]
/-
**ContinuousLinearMap.le_of_opNorm_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：le_of_opNorm_le_of_le {x} {a b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) : ‖
f x‖ <= a * b
参数：hf : ‖f‖ <= a；hx : ‖x‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖
-/
theorem le_of_opNorm_le_of_le {x} {a b : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) :
    ‖f x‖ ≤ a * b :=
  (f.le_opNorm x).trans <| by gcongr; exact (opNorm_nonneg f).trans hf
/-
**ContinuousLinearMap.le_opNorm_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：le_opNorm_of_le {c : Real} {x} (h : ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
参数：h : ‖x‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le_of_le`：le_of_opNorm_le_of_le {x} {a 
b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) : ‖f x‖ <= a * b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  f.le_of_opNorm_le_of_le le_rfl h
/-
**ContinuousLinearMap.le_of_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：le_of_opNorm_le {c : Real} (h : ‖f‖ <= c) (x : E) : ‖f x‖ <= c * ‖x‖
参数：h : ‖f‖ <= c；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le_of_le`：le_of_opNorm_le_of_le {x} {a 
b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) : ‖f x‖ <= a * b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_of_opNorm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  f.le_of_opNorm_le_of_le h le_rfl
/-
**ContinuousLinearMap.opNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M : Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ f
orall x, ‖f x‖ <= M * ‖x‖
参数：hMp : 0 <= M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
-/
theorem opNorm_le_iff {f : E →SL[σ₁₂] F} {M : ℝ} (hMp : 0 ≤ M) :
    ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩
/-
**ContinuousLinearMap.ratio_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：ratio_le_opNorm : ‖f x‖ / ‖x‖ <= ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem ratio_le_opNorm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

/-- The image of the unit ball under a continuous linear map is bounded. -/
/-
**ContinuousLinearMap.unit_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <= ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The image of the unit ball under a continuous linear map is bounded.
-/
theorem unit_le_opNorm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_opNorm_of_le

/--
Continuous linear maps are locally bounded. In other words, they map bounded sets to bounded sets.
-/
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear maps are locally bounded. In other words, they map bounded set
s to bounded sets.
-/
instance : LocallyBoundedMapClass (E →SL[σ₁₂] F) E F where
  comap_cobounded_le := by
    intro ℓ
    rw [Bornology.comap_cobounded_le_iff]
    intro s hs
    obtain ⟨M, hM⟩ := hs.exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    use ‖ℓ‖ * M
    intro y hy
    obtain ⟨σ, hσ⟩ := (mem_image _ _ _).1 hy
    calc ‖y‖
      _ ≤ ‖ℓ σ‖ := by rw [hσ.2]
      _ ≤ ‖ℓ‖ * ‖σ‖ := ContinuousLinearMap.le_opNorm ℓ σ
      _ ≤ ‖ℓ‖ * M := mul_le_mul (by rfl) (hM σ hσ.1) (norm_nonneg σ) (opNorm_nonneg ℓ)
/-
**ContinuousLinearMap.opNorm_le_of_shell** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：opNorm_le_of_shell {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 
0 <= C) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x
‖ <= C * ‖x‖) : ‖f‖ <= C
参数：ε_pos : 0 < ε；hC : 0 <= C；hc : 1 < ‖c‖；hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ <
 ε -> ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound'`：opNorm_le_bound' (f : E ->SL[σ₁₂] 
F) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖) : ‖f‖
 <= M
· 使用定理 `SemilinearMapClass.bound_of_shell_semi_normed`：SemilinearMapClass.bound_
of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) {ε C : Real} (ε_pos 
: 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem opNorm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx
/-
**ContinuousLinearMap.opNorm_le_of_ball** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：opNorm_le_of_ball {f : E ->SL[σ₁₂] F} {ε : Real} {C : Real} (ε_pos : 0 < ε
) (hC : 0 <= C) (hf : forall x in ball (0 : E) ε, ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C
参数：ε_pos : 0 < ε；hC : 0 <= C；hf : forall x in ball (0 : E) ε, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `ContinuousLinearMap.opNorm_le_of_shell`：opNorm_le_of_shell {f : E ->SL[σ
₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜} (hc : 1 < ‖c‖) (hf : f
orall x, ε / ‖c‖ <= ‖x‖ -> ‖…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
-/
theorem opNorm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]
/-
**ContinuousLinearMap.opNorm_le_of_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：opNorm_le_of_nhds_zero {f : E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C) (hf : 
forallᶠ x in 𝓝 (0 : E), ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C
参数：hC : 0 <= C；hf : forallᶠ x in 𝓝 (0 : E), ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `ContinuousLinearMap.opNorm_le_of_ball`：opNorm_le_of_ball {f : E ->SL[σ₁₂
] F} {ε : Real} {C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) (hf : forall x in ball 
(0 : E) ε, ‖f x‖ <= C * ‖x‖…
-/
theorem opNorm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε
/-
**ContinuousLinearMap.opNorm_le_of_shell'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：opNorm_le_of_shell' {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC :
 0 <= C) {c : 𝕜} (hc : ‖c‖ < 1) (hf : forall x, ε * ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f 
x‖ <= C * ‖x‖) : ‖f‖ <= C
参数：ε_pos : 0 < ε；hC : 0 <= C；hc : ‖c‖ < 1；hf : forall x, ε * ‖c‖ <= ‖x‖ -> ‖x‖ <
 ε -> ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_of_ball`：opNorm_le_of_ball {f : E ->SL[σ₁₂
] F} {ε : Real} {C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) (hf : forall x in ball 
(0 : E) ε, ‖f x‖ <= C * ‖x‖…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `ContinuousLinearMap.opNorm_le_of_shell`：opNorm_le_of_shell {f : E ->SL[σ
₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜} (hc : 1 < ‖c‖) (hf : f
orall x, ε / ‖c‖ <= ‖x‖ -> ‖…
· 使用引理 `inv_lt_one₀`：inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem opNorm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C := by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one₀ (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
/-
**ContinuousLinearMap.opNorm_le_of_unit_norm** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：opNorm_le_of_unit_norm [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Rea
l} (hC : 0 <= C) (hf : forall x, ‖x‖ = 1 -> ‖f x‖ <= C) : ‖f‖ <= C
参数：hC : 0 <= C；hf : forall x, ‖x‖ = 1 -> ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound'`：opNorm_le_bound' (f : E ->SL[σ₁₂] 
F) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖) : ‖f‖
 <= M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.map_smulₛₗ`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a

--- 原说明 ---
For a continuous real linear map `f`, if one controls the norm of every `f x`, `
‖x‖ = 1`, then
one controls the norm of `f`.
-/
theorem opNorm_le_of_unit_norm [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖algebraMap _ 𝕜 ‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hx]
  have H₂ : ‖x‖⁻¹ * ‖f x‖ ≤ C := by simpa [norm_smul] using hf _ H₁
  rwa [← div_eq_inv_mul, div_le_iff₀] at H₂
  exact (norm_nonneg x).lt_of_ne' hx

/-- The operator norm satisfies the triangle inequality. -/
/-
**ContinuousLinearMap.opNorm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_add_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ + a₂‖ ≤ r₁ + r₂
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R

--- 原说明 ---
The operator norm satisfies the triangle inequality.
-/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/-
**ContinuousLinearMap.norm_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：norm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.norm_id_le`：norm_id_le : ‖ContinuousLinearMap.id 𝕜 E
‖ <= 1
· 使用定理 `exists_norm_ne_zero`：∀ (E : Type u_5) [inst : SeminormedAddGroup E] [Non
trivialTopology E], ∃ x, ‖x‖ ≠ 0
· 使用定理 `ContinuousLinearMap.ratio_le_opNorm`：ratio_le_opNorm : ‖f x‖ / ‖x‖ <= ‖f
‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `ContinuousLinearMap.id_apply`：id_apply (x : M₁) : ContinuousLinearMap.id
 R₁ M₁ x = x

--- 原说明 ---
If a normed space is (topologically) non-trivial, then the norm of the identity 
equals `1`.
-/
theorem norm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := exists_norm_ne_zero E
    have := (ContinuousLinearMap.id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this
/-
**ContinuousLinearMap.normOneClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：normOneClass [NontrivialTopology E] : NormOneClass (E ->L[𝕜] E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1
-/
instance normOneClass [NontrivialTopology E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩
/-
**ContinuousLinearMap.opNorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：opNorm_smul_le {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] [Se
minormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F] (c : 𝕜') (f : E ->SL[σ₁₂] F) : ‖c 
• f‖ <= ‖c‖ * ‖f‖
参数：c : 𝕜'；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem opNorm_smul_le {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    [SeminormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]
/-
**ContinuousLinearMap.opNorm_le_iff_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：opNorm_le_iff_lipschitz {f : E ->SL[σ₁₂] F} {K : Real>=0} : ‖f‖ <= K ↔ Lip
schitzWith K f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `AddMonoidHomClass.lipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [in
st_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LipschitzWith.norm_le_mul`：∀ {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F} {K : NNReal},   Lip
schitzWith K f …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
-/
theorem opNorm_le_iff_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} :
    ‖f‖ ≤ K ↔ LipschitzWith K f :=
  ⟨fun h ↦ by simpa using AddMonoidHomClass.lipschitz_of_bound f K <| le_of_opNorm_le f h,
    fun hf ↦ f.opNorm_le_bound K.2 <| hf.norm_le_mul (map_zero f)⟩

alias ⟨lipschitzWith_of_opNorm_le, opNorm_le_of_lipschitz⟩ := opNorm_le_iff_lipschitz

/-- Operator seminorm on the space of continuous (semi)linear maps, as `Seminorm`.

We use this seminorm to define a `SeminormedGroup` structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `F`. -/
/-
**ContinuousLinearMap.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：{𝕜 : Type u_1} →   {𝕜₂ : Type u_2} →     {E : Type u_4} →       {F : Type 
u_5} →         [inst : SeminormedAddCommGroup E] →           [inst_1 : Seminorme
dAddCommGroup F] →             [inst_2 : NontriviallyNormedField 𝕜] →           
    [inst_3 : NontriviallyNormedField 𝕜₂] →                 [inst_4 : NormedSpac
e 𝕜 E] →                   [inst_5 : NormedSpace 𝕜₂ F] → {σ₁₂ : 𝕜 →+* 𝕜₂} → [Rin
gHomIsometric σ₁₂] → Seminorm 𝕜₂ (E →SL[σ₁₂] F)
参数：E →SL[σ₁₂] F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.opNorm_zero`：opNorm_zero : ‖(0 : E ->SL[σ₁₂] F)‖ = 0
· 使用定理 `ContinuousLinearMap.opNorm_add_le`：opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖

--- 原说明 ---
Operator seminorm on the space of continuous (semi)linear maps, as `Seminorm`.

We use this seminorm to define a `SeminormedGroup` structure on `E →SL[σ] F`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` 
and `F`.
-/
protected noncomputable def seminorm : Seminorm 𝕜₂ (E →SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

set_option backward.privateInPublic true in
/-
**ContinuousLinearMap.uniformity_eq_seminorm** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformity_eq_seminorm :
    𝓤 (E →SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r} := by
  have A (f : (E →SL[σ₁₂] F) × (E →SL[σ₁₂] F)) : ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by
    rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F) |>.uniformity_eq_of_hasBasis
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices ∀ f : E →SL[σ₁₂] F, (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) → ‖f‖ ≤ ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using! this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx ↦ ?_
    exact (hf x hx.le).trans ((div_le_iff₀' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ContinuousLinearMap.toPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：toPseudoMetricSpace : PseudoMetricSpace (E ->SL[σ₁₂] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Basic.0.ContinuousLinearMap.un
iformity_eq_seminorm`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type 
u_5} [inst : SeminormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup F] [in
st…
-/
instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm

/-- Continuous linear maps themselves form a seminormed space with respect to the operator norm. -/
/-
**ContinuousLinearMap.toSeminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：{𝕜 : Type u_1} →   {𝕜₂ : Type u_2} →     {E : Type u_4} →       {F : Type 
u_5} →         [inst : SeminormedAddCommGroup E] →           [inst_1 : Seminorme
dAddCommGroup F] →             [inst_2 : NontriviallyNormedField 𝕜] →           
    [inst_3 : NontriviallyNormedField 𝕜₂] →                 [inst_4 : NormedSpac
e 𝕜 E] →                   [inst_5 : NormedSpace 𝕜₂ F] →                     {σ₁
₂ : 𝕜 →+* 𝕜₂} → [RingHomIsometric σ₁₂] → SeminormedAddCommGroup (E →SL[σ₁₂] F)
参数：E →SL[σ₁₂] F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Continuous linear maps themselves form a seminormed space with respect to the op
erator norm.
-/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) where

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/-
**ContinuousLinearMap.nnnorm_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：nnnorm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1

--- 原说明 ---
If a normed space is (topologically) non-trivial, then the norm of the identity 
equals `1`.
-/
theorem nnnorm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖₊ = 1 :=
  NNReal.eq norm_id
/-
**ContinuousLinearMap.toNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommCl
ass 𝕜₂ 𝕜' F] : NormedSpace 𝕜' (E ->SL[σ₁₂] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨opNorm_smul_le⟩

/-- The operator norm is submultiplicative. -/
/-
**ContinuousLinearMap.opNorm_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：opNorm_comp_le (f : E ->SL[σ₁₂] F) : ‖h.comp f‖ <= ‖h‖ * ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `ContinuousLinearMap.bounds_bddBelow`：bounds_bddBelow {f : E ->SL[σ₁₂] F}
 : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖

--- 原说明 ---
The operator norm is submultiplicative.
-/
theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow ⟨by positivity, fun x => by
    rw [mul_assoc]
    exact h.le_opNorm_of_le (f.le_opNorm x)⟩

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
/-
**ContinuousLinearMap.toSeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：toSeminormedRing : SeminormedRing (E ->L[𝕜] E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Continuous linear maps form a seminormed ring with respect to the operator norm.
-/
instance toSeminormedRing : SeminormedRing (E →L[𝕜] E) :=
  { toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }

/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
/-
**ContinuousLinearMap.toNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：toNormedAlgebra : NormedAlgebra 𝕜 (E ->L[𝕜] E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
For a normed space `E`, continuous linear endomorphisms form a normed algebra wi
th
respect to the operator norm.
-/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E →L[𝕜] E) := { toNormedSpace, algebra with }

end

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F)

@[simp, nontriviality]
/-
**ContinuousLinearMap.opNorm_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_of_subsingleton`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] [Su
bsingleton E] (a : E), ‖a‖ = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0 := norm_of_subsingleton f

variable {f} in
/-
**ContinuousLinearMap.homothety_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：homothety_norm [NontrivialTopology E] (f : E ->SL[σ₁₂] F) {a : Real} (hf :
 forall x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a
参数：f : E ->SL[σ₁₂] F；hf : forall x, ‖f x‖ = a * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_norm_ne_zero`：∀ (E : Type u_5) [inst : SeminormedAddGroup E] [Non
trivialTopology E], ∃ x, ‖x‖ ≠ 0
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem homothety_norm [NontrivialTopology E] (f : E →SL[σ₁₂] F) {a : ℝ}
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a := by
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  replace hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hx
  have ha : 0 ≤ a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_iff_left₀] using f.le_opNorm x

end OpNorm

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]
variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

@[simp]
/-
**ContinuousLinearMap.norm_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：norm_restrictScalars (f : E ->L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖
参数：f : E ->L[𝕜] Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem norm_restrictScalars (f : E →L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)

variable (𝕜 E Fₗ 𝕜') (𝕜'' : Type*) [Ring 𝕜'']
variable [Module 𝕜'' Fₗ] [ContinuousConstSMul 𝕜'' Fₗ]
  [SMulCommClass 𝕜 𝕜'' Fₗ] [SMulCommClass 𝕜' 𝕜'' Fₗ]

/-- `ContinuousLinearMap.restrictScalars` as a `LinearIsometry`. -/
/-
**ContinuousLinearMap.restrictScalarsIsometry** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：restrictScalarsIsometry : (E ->L[𝕜] Fₗ) ->ₗᵢ[𝕜''] E ->L[𝕜'] Fₗ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_restrictScalars`：norm_restrictScalars (f : E ->
L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖

--- 原说明 ---
`ContinuousLinearMap.restrictScalars` as a `LinearIsometry`.
-/
def restrictScalarsIsometry : (E →L[𝕜] Fₗ) →ₗᵢ[𝕜''] E →L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩

variable {𝕜''}

@[simp]
/-
**ContinuousLinearMap.coe_restrictScalarsIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：coe_restrictScalarsIsometry : ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = r
estrictScalars 𝕜'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_restrictScalarsIsometry :
    ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

@[simp]
/-
**ContinuousLinearMap.restrictScalarsIsometry_toLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：restrictScalarsIsometry_toLinearMap : (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜
'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜''
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem restrictScalarsIsometry_toLinearMap :
    (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl

end RestrictScalars

/-
**ContinuousLinearMap.norm_pi_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：norm_pi_le_of_le {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, Semin
ormedAddCommGroup (M i)] [forall i, NormedSpace 𝕜 (M i)] {C : Real} {L : (i : ι)
 -> (E ->L[𝕜] M i)} (hL : forall i, ‖L i‖ <= C) (hC : 0 <= C) : ‖pi L‖ <= C
参数：M i；M i；i : ι；E ->L[𝕜] M i；hL : forall i, ‖L i‖ <= C；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
-/
lemma norm_pi_le_of_le {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, SeminormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)] {C : ℝ}
    {L : (i : ι) → (E →L[𝕜] M i)} (hL : ∀ i, ‖L i‖ ≤ C) (hC : 0 ≤ C) :
    ‖pi L‖ ≤ C := by
  refine opNorm_le_bound _ hC (fun x ↦ ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i ↦ ?_)
  exact (L i).le_of_opNorm_le (hL i) _
/-
**ContinuousLinearMap.norm_postcomp_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：norm_postcomp_le [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] [RingHomIso
metric σ₂₃] (L : F ->SL[σ₂₃] G) : ‖L.postcomp (σ
参数：L : F ->SL[σ₂₃] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
-/
lemma norm_postcomp_le [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
    (L : F →SL[σ₂₃] G) : ‖L.postcomp (σ := σ₁₂) E‖ ≤ ‖L‖ :=
  L.postcomp (σ := σ₁₂) E |>.opNorm_le_bound (by positivity) <| opNorm_comp_le L

end ContinuousLinearMap

namespace LinearMap

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
/-
**LinearMap.mkContinuous_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F) {C : Real} (hC : 0 <= C) (h : for
all x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h‖ <= C
参数：f : E ->ₛₗ[σ₁₂] F；hC : 0 <= C；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M

--- 原说明 ---
If a continuous linear map is constructed from a linear map via the constructor 
`mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegat
ive.
-/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
/-
**LinearMap.mkContinuous_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mkContinuous_norm_le' (f : E ->ₛₗ[σ₁₂] F) {C : Real} (h : forall x, ‖f x‖ 
<= C * ‖x‖) : ‖f.mkContinuous C h‖ <= max C 0
参数：f : E ->ₛₗ[σ₁₂] F；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If a continuous linear map is constructed from a linear map via the constructor 
`mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative.
-/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans <| by
    gcongr; apply le_max_left

end LinearMap

namespace LinearIsometry

/-
**LinearIsometry.norm_toContinuousLinearMap_le** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Isometry`。
形式化陈述：norm_toContinuousLinearMap_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinear
Map‖ <= 1
参数：f : E ->ₛₗᵢ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_toContinuousLinearMap_le (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ ≤ 1 :=
  f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp

end LinearIsometry

namespace Submodule

/-
**Submodule.norm_subtypeL_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ <= 1
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap_le`：norm_toContinuousLinearMap
_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1
-/
theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le

end Submodule

end SemiNormed

