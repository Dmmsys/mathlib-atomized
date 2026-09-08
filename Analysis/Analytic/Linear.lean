/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.CPolynomialDef

/-!
# Linear functions are analytic

In this file we prove that a `ContinuousLinearMap` defines an analytic function with
the formal power series `f x = f a + f (x - a)`. We also prove similar results for bilinear maps.

We deduce this fact from the stronger result that continuous linear maps are continuously
polynomial, i.e., they admit a finite power series.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology NNReal ENNReal
open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

@[simp]
/-
**ContinuousLinearMap.fpowerSeries_radius** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：fpowerSeries_radius (f : E ->L[𝕜] F) (x : E) : (f.fpowerSeries x).radius =
 ∞
参数：f : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`：radiu
s_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) : 
p.radius = ∞
-/
theorem fpowerSeries_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl
/-
**ContinuousLinearMap.hasFiniteFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (x : E), HasFi
niteFPowerSeriesOnBall (⇑f) (f.fpowerSeries x) x 2 ⊤
参数：f : E →L[𝕜] F；x : E；⇑f；f.fpowerSeries x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.fpowerSeries_radius`：fpowerSeries_radius (f : E ->L[
𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
ries.match_1.eq_3`：∀ (motive : ℕ → Sort u_1) (x : ℕ) (h_1 : Unit → motive 0) (h_
2 : Unit → motive 1) (h_3 : (x : ℕ) → motive x),   (x = 0 → False) →     (x = 1…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
ries.match_1.eq_1`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit
 → motive 1) (h_3 : (x : ℕ) → motive x),   (match 0 with     | 0 => h_1 ()     …
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
ries.match_1.eq_2`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit
 → motive 1) (h_3 : (x : ℕ) → motive x),   (match 1 with     | 0 => h_1 ()     …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 65 条，此处仅展示前 30 条）
-/
protected theorem hasFiniteFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFiniteFPowerSeriesOnBall f (f.fpowerSeries x) x 2 ∞ where
  r_le := by simp
  r_pos := ENNReal.coe_lt_top
  hasSum := fun _ => (hasSum_nat_add_iff' 2).1 <| by
    simp [Finset.sum_range_succ, hasSum_zero, fpowerSeries]
  finite := by
    intro m hm
    match m with
    | 0 | 1 => linarith
    | n + 2 => simp [fpowerSeries]
/-
**ContinuousLinearMap.hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (x : E), HasFP
owerSeriesOnBall (⇑f) (f.fpowerSeries x) x ⊤
参数：f : E →L[𝕜] F；x : E；⇑f；f.fpowerSeries x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousLinearMap.hasFiniteFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  (f.hasFiniteFPowerSeriesOnBall x).toHasFPowerSeriesOnBall
/-
**ContinuousLinearMap.hasFPowerSeriesAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (x : E), HasFP
owerSeriesAt (⇑f) (f.fpowerSeries x) x
参数：f : E →L[𝕜] F；x : E；⇑f；f.fpowerSeries x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} [inst : Nont
riviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasFPowerSeriesAt (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall x⟩
/-
**ContinuousLinearMap.cpolynomialAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (x : E), CPoly
nomialAt 𝕜 (⇑f) x
参数：f : E →L[𝕜] F；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt`：HasFiniteFPowerSeriesOnBall.c
polynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : CPolynomialAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFiniteFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem cpolynomialAt (f : E →L[𝕜] F) (x : E) : CPolynomialAt 𝕜 f x :=
  (f.hasFiniteFPowerSeriesOnBall x).cpolynomialAt
/-
**ContinuousLinearMap.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (x : E), Analy
ticAt 𝕜 (⇑f) x
参数：f : E →L[𝕜] F；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.hasFPowerSeriesAt x).analyticAt
/-
**ContinuousLinearMap.cpolynomialOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (s : Set E), C
PolynomialOn 𝕜 (⇑f) s
参数：f : E →L[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cpolynomialAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
protected theorem cpolynomialOn (f : E →L[𝕜] F) (s : Set E) : CPolynomialOn 𝕜 f s :=
  fun x _ ↦ f.cpolynomialAt x
/-
**ContinuousLinearMap.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (s : Set E), A
nalyticOnNhd 𝕜 (⇑f) s
参数：f : E →L[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem analyticOnNhd (f : E →L[𝕜] F) (s : Set E) : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x
/-
**ContinuousLinearMap.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (s : Set E) (x
 : E), AnalyticWithinAt 𝕜 (⇑f) s x
参数：f : E →L[𝕜] F；s : Set E；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem analyticWithinAt (f : E →L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt
/-
**ContinuousLinearMap.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E →L[𝕜] F)   (s : Set E), A
nalyticOn 𝕜 (⇑f) s
参数：f : E →L[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOn (f : E →L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurryBilinear ![(x, y), (x', y')] = f x y'`. -/
/-
**ContinuousLinearMap.uncurryBilinear** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：uncurryBilinear (f : E ->L[𝕜] F ->L[𝕜] G) : E × F [×2]->L[𝕜] G
参数：f : E ->L[𝕜] F ->L[𝕜] G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurryBilinear ![(x, y), (x', y')] = f x y'`.
-/
def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F [×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]
/-
**ContinuousLinearMap.uncurryBilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：uncurryBilinear_apply (f : E ->L[𝕜] F ->L[𝕜] G) (m : Fin 2 -> E × F) : f.u
ncurryBilinear m = f (m 0).1 (m 1).2
参数：f : E ->L[𝕜] F ->L[𝕜] G；m : Fin 2 -> E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem uncurryBilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Fin 2 → E × F) :
    f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
/-
**ContinuousLinearMap.fpowerSeriesBilinear** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
LinearMap`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {G : Type u_4} →            
       [inst_5 : NormedAddCommGroup G] →                     [inst_6 : NormedSpa
ce 𝕜 G] → (E →L[𝕜] F →L[𝕜] G) → E × F → FormalMultilinearSeries 𝕜 (E × F) G
参数：E →L[𝕜] F →L[𝕜] G；E × F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] 
G`.
-/
def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0

@[simp]
/-
**ContinuousLinearMap.fpowerSeriesBilinear_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：fpowerSeriesBilinear_apply_zero (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : fp
owerSeriesBilinear f x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
参数：f : E ->L[𝕜] F ->L[𝕜] G；x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fpowerSeriesBilinear_apply_zero (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeriesBilinear_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：fpowerSeriesBilinear_apply_one (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : fpo
werSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.d
eriv₂ x)
参数：f : E ->L[𝕜] F ->L[𝕜] G；x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fpowerSeriesBilinear_apply_one (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeriesBilinear_apply_two** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：fpowerSeriesBilinear_apply_two (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : fpo
werSeriesBilinear f x 2 = f.uncurryBilinear
参数：f : E ->L[𝕜] F ->L[𝕜] G；x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fpowerSeriesBilinear_apply_two (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 2 = f.uncurryBilinear :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：fpowerSeriesBilinear_apply_add_three (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F)
 (n) : fpowerSeriesBilinear f x (n + 3) = 0
参数：f : E ->L[𝕜] F ->L[𝕜] G；x : E × F；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fpowerSeriesBilinear_apply_add_three (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) (n) :
    fpowerSeriesBilinear f x (n + 3) = 0 :=
  rfl

@[simp]
/-
**ContinuousLinearMap.fpowerSeriesBilinear_radius** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：fpowerSeriesBilinear_radius (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : (f.fpo
werSeriesBilinear x).radius = ∞
参数：f : E ->L[𝕜] F ->L[𝕜] G；x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`：radiu
s_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) : 
p.radius = ∞
-/
theorem fpowerSeriesBilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl
/-
**ContinuousLinearMap.hasFPowerSeriesOnBall_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (x : E × F),
   HasFPowerSeriesOnBall (fun x => (f x.1) x.2) (f.fpowerSeriesBilinear x) x ⊤
参数：f : E →L[𝕜] F →L[𝕜] G；x : E × F；fun x => (f x.1) x.2；f.fpowerSeriesBilinear x
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.fpowerSeriesBilinear_radius`：fpowerSeriesBilinear_ra
dius (f : E ->L[𝕜] F ->L[𝕜] G) (x : E × F) : (f.fpowerSeriesBilinear x).radius =
 ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.map_add_add`：map_add_add (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
 (x x' : E) (y y' : Fₗ) : f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y')
 + f x' y'
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
riesBilinear.match_1.eq_4`：∀ (motive : ℕ → Sort u_1) (x : ℕ) (h_1 : Unit → motiv
e 0) (h_2 : Unit → motive 1) (h_3 : Unit → motive 2)   (h_4 : (x : ℕ) → motive x
),   (x…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
riesBilinear.match_1.eq_1`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_
2 : Unit → motive 1) (h_3 : Unit → motive 2)   (h_4 : (x : ℕ) → motive x),   (ma
tch 0 w…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
riesBilinear.match_1.eq_2`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_
2 : Unit → motive 1) (h_3 : Unit → motive 2)   (h_4 : (x : ℕ) → motive x),   (ma
tch 1 w…
· 使用定理 `_private.Mathlib.Analysis.Analytic.Linear.0.ContinuousLinearMap.fpowerSe
riesBilinear.match_1.eq_3`：∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_
2 : Unit → motive 1) (h_3 : Unit → motive 2)   (h_4 : (x : ℕ) → motive x),   (ma
tch 2 w…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
protected theorem hasFPowerSeriesOnBall_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
      (hasSum_nat_add_iff' 3).1 <| by
        simp only [Finset.sum_range_succ, Prod.fst_add, Prod.snd_add, f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }
/-
**ContinuousLinearMap.hasFPowerSeriesAt_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (x : E × F),
   HasFPowerSeriesAt (fun x => (f x.1) x.2) (f.fpowerSeriesBilinear x) x
参数：f : E →L[𝕜] F →L[𝕜] G；x : E × F；fun x => (f x.1) x.2；f.fpowerSeriesBilinear x
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesOnBall_bilinear`：∀ {𝕜 : Type u_1} [in
st : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasFPowerSeriesAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩
/-
**ContinuousLinearMap.analyticAt_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (x : E × F),
   AnalyticAt 𝕜 (fun x => (f x.1) x.2) x
参数：f : E →L[𝕜] F →L[𝕜] G；x : E × F；fun x => (f x.1) x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesAt_bilinear`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFPowerSeriesAt_bilinear x).analyticAt
/-
**ContinuousLinearMap.analyticWithinAt_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E 
× F)) (x : E × F),   AnalyticWithinAt 𝕜 (fun x => (f x.1) x.2) s x
参数：f : E →L[𝕜] F →L[𝕜] G；s : Set (E × F)；x : E × F；fun x => (f x.1) x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearMap.analyticAt_bilinear`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticWithinAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) (x : E × F) :
    AnalyticWithinAt 𝕜 (fun x : E × F => f x.1 x.2) s x :=
  (f.analyticAt_bilinear x).analyticWithinAt
/-
**ContinuousLinearMap.analyticOnNhd_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E 
× F)),   AnalyticOnNhd 𝕜 (fun x => (f x.1) x.2) s
参数：f : E →L[𝕜] F →L[𝕜] G；s : Set (E × F)；fun x => (f x.1) x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.analyticAt_bilinear`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOnNhd_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOnNhd 𝕜 (fun x : E × F => f x.1 x.2) s :=
  fun x _ ↦ f.analyticAt_bilinear x
/-
**ContinuousLinearMap.analyticOn_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E 
× F)),   AnalyticOn 𝕜 (fun x => (f x.1) x.2) s
参数：f : E →L[𝕜] F →L[𝕜] G；s : Set (E × F)；fun x => (f x.1) x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `ContinuousLinearMap.analyticOnNhd_bilinear`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOn_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOn 𝕜 (fun x : E × F => f x.1 x.2) s :=
  (f.analyticOnNhd_bilinear s).analyticOn

end ContinuousLinearMap

variable {s : Set E} {z : E} {t : Set (E × F)} {p : E × F}

@[fun_prop]
/-
**analyticAt_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
lemma analyticAt_id : AnalyticAt 𝕜 (id : E → E) z :=
  (ContinuousLinearMap.id 𝕜 E).analyticAt z
/-
**analyticWithinAt_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E -> E) s z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
-/
lemma analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E → E) s z :=
  analyticAt_id.analyticWithinAt

/-- `id` is entire -/
/-
**analyticOnNhd_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z

--- 原说明 ---
`id` is entire
-/
theorem analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticAt_id
/-
**analyticOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_id : AnalyticOn 𝕜 (fun x : E => x) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticWithinAt_id`：analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E ->
 E) s z
-/
theorem analyticOn_id : AnalyticOn 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticWithinAt_id

/-- `fst` is analytic -/
/-
**analyticAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F => p.fst) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…

--- 原说明 ---
`fst` is analytic
-/
theorem analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F ↦ p.fst) p :=
  (ContinuousLinearMap.fst 𝕜 E F).analyticAt p
/-
**analyticWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticWithinAt_fst : AnalyticWithinAt 𝕜 (fun p : E × F => p.fst) t p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_fst`：analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F => p.fst) p
-/
theorem analyticWithinAt_fst : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.fst) t p :=
  analyticAt_fst.analyticWithinAt

/-- `snd` is analytic -/
/-
**analyticAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F => p.snd) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…

--- 原说明 ---
`snd` is analytic
-/
theorem analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F ↦ p.snd) p :=
  (ContinuousLinearMap.snd 𝕜 E F).analyticAt p
/-
**analyticWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p : E × F => p.snd) t p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_snd`：analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F => p.snd) p
-/
theorem analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.snd) t p :=
  analyticAt_snd.analyticWithinAt

/-- `fst` is entire -/
/-
**analyticOnNhd_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_fst : AnalyticOnNhd 𝕜 (fun p : E × F => p.fst) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_fst`：analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F => p.fst) p

--- 原说明 ---
`fst` is entire
-/
theorem analyticOnNhd_fst : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticAt_fst
/-
**analyticOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_fst : AnalyticOn 𝕜 (fun p : E × F => p.fst) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticWithinAt_fst`：analyticWithinAt_fst : AnalyticWithinAt 𝕜 (fun p :
 E × F => p.fst) t p
-/
theorem analyticOn_fst : AnalyticOn 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticWithinAt_fst

/-- `snd` is entire -/
/-
**analyticOnNhd_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOnNhd_snd : AnalyticOnNhd 𝕜 (fun p : E × F => p.snd) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_snd`：analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F => p.snd) p

--- 原说明 ---
`snd` is entire
-/
theorem analyticOnNhd_snd : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticAt_snd
/-
**analyticOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_snd : AnalyticOn 𝕜 (fun p : E × F => p.snd) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticWithinAt_snd`：analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p :
 E × F => p.snd) t p
-/
theorem analyticOn_snd : AnalyticOn 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticWithinAt_snd

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] F) (s : Set E) (x : E)

/-
**ContinuousLinearEquiv.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃L[𝕜] F)   (x : E), Analy
ticAt 𝕜 (⇑f) x
参数：f : E ≃L[𝕜] F；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt
/-
**ContinuousLinearEquiv.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃L[𝕜] F)   (s : Set E), A
nalyticOnNhd 𝕜 (⇑f) s
参数：f : E ≃L[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x
/-
**ContinuousLinearEquiv.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃L[𝕜] F)   (s : Set E) (x
 : E), AnalyticWithinAt 𝕜 (⇑f) s x
参数：f : E ≃L[𝕜] F；s : Set E；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearEquiv.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt
/-
**ContinuousLinearEquiv.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃L[𝕜] F)   (s : Set E), A
nalyticOn 𝕜 (⇑f) s
参数：f : E ≃L[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[𝕜] F) (s : Set E) (x : E)

/-
**LinearIsometryEquiv.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   (x : E), Anal
yticAt 𝕜 (⇑f) x
参数：f : E ≃ₗᵢ[𝕜] F；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt
/-
**LinearIsometryEquiv.analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   (s : Set E), 
AnalyticOnNhd 𝕜 (⇑f) s
参数：f : E ≃ₗᵢ[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x
/-
**LinearIsometryEquiv.analyticWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   (s : Set E) (
x : E), AnalyticWithinAt 𝕜 (⇑f) s x
参数：f : E ≃ₗᵢ[𝕜] F；s : Set E；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `LinearIsometryEquiv.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt
/-
**LinearIsometryEquiv.analyticOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   (s : Set E), 
AnalyticOn 𝕜 (⇑f) s
参数：f : E ≃ₗᵢ[𝕜] F；s : Set E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.analyticWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

end LinearIsometryEquiv

