/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Various complex special functions are analytic

`log`, and `cpow` are analytic, since they are differentiable.
-/

public section

open Complex Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
/-
**analyticAt_clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticAt_clog (m : z in slitPlane) : AnalyticAt Complex log z
参数：m : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.analyticAt_iff_eventually_differentiableAt`：analyticAt_iff_event
ually_differentiableAt {f : Complex -> E} {c : Complex} : AnalyticAt Complex f c
 ↔ forallᶠ z in 𝓝 c, DifferentiableAt Co…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `Complex.isOpen_slitPlane`：IsOpen Complex.slitPlane
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableAt.clog`：DifferentiableAt.clog {f : E -> Complex} {x : E} 
(h₁ : DifferentiableAt Complex f x) (h₂ : f x in slitPlane) : DifferentiableAt C
omplex (fun…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x

--- 原说明 ---
`log` is analytic away from nonpositive reals
-/
theorem analyticAt_clog (m : z ∈ slitPlane) : AnalyticAt ℂ log z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
/-
**AnalyticAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.clog (fa : AnalyticAt Complex f x) (m : f x in slitPlane) : Ana
lyticAt Complex (fun z => log (f z)) x
参数：fa : AnalyticAt Complex f x；m : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_clog`：analyticAt_clog (m : z in slitPlane) : AnalyticAt Compl
ex log z

--- 原说明 ---
`log` is analytic away from nonpositive reals
-/
theorem AnalyticAt.clog (fa : AnalyticAt ℂ f x) (m : f x ∈ slitPlane) :
    AnalyticAt ℂ (fun z ↦ log (f z)) x :=
  (analyticAt_clog m).comp fa
/-
**AnalyticWithinAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.clog (fa : AnalyticWithinAt Complex f s x) (m : f x in sl
itPlane) : AnalyticWithinAt Complex (fun z => log (f z)) s x
参数：fa : AnalyticWithinAt Complex f s x；m : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用定理 `analyticAt_clog`：analyticAt_clog (m : z in slitPlane) : AnalyticAt Compl
ex log z
-/
theorem AnalyticWithinAt.clog (fa : AnalyticWithinAt ℂ f s x) (m : f x ∈ slitPlane) :
    AnalyticWithinAt ℂ (fun z ↦ log (f z)) s x :=
  (analyticAt_clog m).comp_analyticWithinAt fa

/-- `log` is analytic away from nonpositive reals -/
/-
**AnalyticOnNhd.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.clog (fs : AnalyticOnNhd Complex f s) (m : forall z in s, f 
z in slitPlane) : AnalyticOnNhd Complex (fun z => log (f z)) s
参数：fs : AnalyticOnNhd Complex f s；m : forall z in s, f z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `analyticAt_clog`：analyticAt_clog (m : z in slitPlane) : AnalyticAt Compl
ex log z

--- 原说明 ---
`log` is analytic away from nonpositive reals
-/
theorem AnalyticOnNhd.clog (fs : AnalyticOnNhd ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).comp (fs z n)
/-
**AnalyticOn.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.clog (fs : AnalyticOn Complex f s) (m : forall z in s, f z in s
litPlane) : AnalyticOn Complex (fun z => log (f z)) s
参数：fs : AnalyticOn Complex f s；m : forall z in s, f z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `analyticAt_clog`：analyticAt_clog (m : z in slitPlane) : AnalyticAt Compl
ex log z
-/
theorem AnalyticOn.clog (fs : AnalyticOn ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOn ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
/-
**AnalyticWithinAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.cpow (fa : AnalyticWithinAt Complex f s x) (ga : Analytic
WithinAt Complex g s x) (m : f x in slitPlane) : AnalyticWithinAt Complex (fun z
 => f z ^ g z) s x
参数：fa : AnalyticWithinAt Complex f s x；ga : AnalyticWithinAt Complex g s x；m : f
 x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AnalyticWithinAt.continuousWithinAt_insert`：∀ {𝕜 : Type u_1} {E : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGro
up E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AnalyticWithinAt.congr_of_eventuallyEq_insert`：AnalyticWithinAt.congr_of
_eventuallyEq_insert {f g : E -> F} {s : Set E} {x : E} (hf : AnalyticWithinAt 𝕜
 f s x) (hs : g =ᶠ[𝓝[insert x s] x]…
· 使用定理 `AnalyticWithinAt.cexp`：AnalyticWithinAt.cexp (fa : AnalyticWithinAt Comp
lex f s x) : AnalyticWithinAt Complex (fun z => exp (f z)) s x
· 使用引理 `AnalyticWithinAt.mul`：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z
 : E} (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : Analytic
WithinAt 𝕜…
· 使用定理 `AnalyticWithinAt.clog`：AnalyticWithinAt.clog (fa : AnalyticWithinAt Comp
lex f s x) (m : f x in slitPlane) : AnalyticWithinAt Complex (fun z => log (f z)
) s x

--- 原说明 ---
`f z ^ g z` is analytic if `f z` is not a nonpositive real
-/
theorem AnalyticWithinAt.cpow (fa : AnalyticWithinAt ℂ f s x) (ga : AnalyticWithinAt ℂ g s x)
    (m : f x ∈ slitPlane) : AnalyticWithinAt ℂ (fun z ↦ f z ^ g z) s x := by
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z ↦ exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact ((fa.clog m).mul ga).cexp

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
@[fun_prop]
/-
**AnalyticAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.cpow (fa : AnalyticAt Complex f x) (ga : AnalyticAt Complex g x
) (m : f x in slitPlane) : AnalyticAt Complex (fun z => f z ^ g z) x
参数：fa : AnalyticAt Complex f x；ga : AnalyticAt Complex g x；m : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `AnalyticWithinAt.cpow`：AnalyticWithinAt.cpow (fa : AnalyticWithinAt Comp
lex f s x) (ga : AnalyticWithinAt Complex g s x) (m : f x in slitPlane) : Analyt
icWithinAt …

--- 原说明 ---
`f z ^ g z` is analytic if `f z` is not a nonpositive real
-/
theorem AnalyticAt.cpow (fa : AnalyticAt ℂ f x) (ga : AnalyticAt ℂ g x)
    (m : f x ∈ slitPlane) : AnalyticAt ℂ (fun z ↦ f z ^ g z) x := by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
/-
**AnalyticOn.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.cpow (fs : AnalyticOn Complex f s) (gs : AnalyticOn Complex g s
) (m : forall z in s, f z in slitPlane) : AnalyticOn Complex (fun z => f z ^ g z
) s
参数：fs : AnalyticOn Complex f s；gs : AnalyticOn Complex g s；m : forall z in s, f 
z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.cpow`：AnalyticWithinAt.cpow (fa : AnalyticWithinAt Comp
lex f s x) (ga : AnalyticWithinAt Complex g s x) (m : f x in slitPlane) : Analyt
icWithinAt …

--- 原说明 ---
`f z ^ g z` is analytic if `f z` avoids nonpositive reals
-/
theorem AnalyticOn.cpow (fs : AnalyticOn ℂ f s) (gs : AnalyticOn ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOn ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
/-
**AnalyticOnNhd.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.cpow (fs : AnalyticOnNhd Complex f s) (gs : AnalyticOnNhd Co
mplex g s) (m : forall z in s, f z in slitPlane) : AnalyticOnNhd Complex (fun z 
=> f z ^ g z) s
参数：fs : AnalyticOnNhd Complex f s；gs : AnalyticOnNhd Complex g s；m : forall z in
 s, f z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.cpow`：AnalyticAt.cpow (fa : AnalyticAt Complex f x) (ga : Ana
lyticAt Complex g x) (m : f x in slitPlane) : AnalyticAt Complex (fun z => f z ^
 g z)…

--- 原说明 ---
`f z ^ g z` is analytic if `f z` avoids nonpositive reals
-/
theorem AnalyticOnNhd.cpow (fs : AnalyticOnNhd ℂ f s) (gs : AnalyticOnNhd ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOnNhd ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

section ReOfReal

variable {f : ℂ → ℂ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
/-
**AnalyticAt.re_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.re_ofReal (hf : AnalyticAt Complex f x) : AnalyticAt Real (fun 
x : Real => (f x).re) x
参数：hf : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticAt.re_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]
/-
**AnalyticAt.im_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.im_ofReal (hf : AnalyticAt Complex f x) : AnalyticAt Real (fun 
x : Real => (f x).im) x
参数：hf : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AnalyticAt.im_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).im) x :=
  (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))
/-
**AnalyticWithinAt.re_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.re_ofReal (hf : AnalyticWithinAt Complex f (ofReal '' s) 
x) : AnalyticWithinAt Real (fun x : Real => (f x).re) s x
参数：hf : AnalyticWithinAt Complex f (ofReal '' s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `ContinuousLinearMap.analyticWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticWithinAt.restrictScalars`：AnalyticWithinAt.restrictScalars (hf :
 AnalyticWithinAt 𝕜' f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticWithinAt.re_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).re) s x :=
  ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)
/-
**AnalyticWithinAt.im_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.im_ofReal (hf : AnalyticWithinAt Complex f (ofReal '' s) 
x) : AnalyticWithinAt Real (fun x : Real => (f x).im) s x
参数：hf : AnalyticWithinAt Complex f (ofReal '' s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用定理 `ContinuousLinearMap.analyticWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticWithinAt.restrictScalars`：AnalyticWithinAt.restrictScalars (hf :
 AnalyticWithinAt 𝕜' f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticWithinAt.im_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).im) s x :=
  ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)
/-
**AnalyticOn.re_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.re_ofReal (hf : AnalyticOn Complex f (ofReal '' s)) : AnalyticO
n Real (fun x : Real => (f x).re) s
参数：hf : AnalyticOn Complex f (ofReal '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOn.comp`：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {
t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s
) : A…
· 使用定理 `ContinuousLinearMap.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOn.restrictScalars`：AnalyticOn.restrictScalars (hf : AnalyticOn 
𝕜' f s) : AnalyticOn 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticOn.re_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)
/-
**AnalyticOn.im_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.im_ofReal (hf : AnalyticOn Complex f (ofReal '' s)) : AnalyticO
n Real (fun x : Real => (f x).im) s
参数：hf : AnalyticOn Complex f (ofReal '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOn.comp`：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {
t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s
) : A…
· 使用定理 `ContinuousLinearMap.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOn.restrictScalars`：AnalyticOn.restrictScalars (hf : AnalyticOn 
𝕜' f s) : AnalyticOn 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticOn.im_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)
/-
**AnalyticOnNhd.re_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.re_ofReal (hf : AnalyticOnNhd Complex f (ofReal '' s)) : Ana
lyticOnNhd Real (fun x : Real => (f x).re) s
参数：hf : AnalyticOnNhd Complex f (ofReal '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.comp`：AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F ->
 G} {f : E -> F} (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set
.MapsTo …
· 使用定理 `ContinuousLinearMap.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOnNhd.restrictScalars`：AnalyticOnNhd.restrictScalars (hf : Analy
ticOnNhd 𝕜' f s) : AnalyticOnNhd 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticOnNhd.re_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)
/-
**AnalyticOnNhd.im_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.im_ofReal (hf : AnalyticOnNhd Complex f (ofReal '' s)) : Ana
lyticOnNhd Real (fun x : Real => (f x).im) s
参数：hf : AnalyticOnNhd Complex f (ofReal '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.comp`：AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F ->
 G} {f : E -> F} (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : Set
.MapsTo …
· 使用定理 `ContinuousLinearMap.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOnNhd.restrictScalars`：AnalyticOnNhd.restrictScalars (hf : Analy
ticOnNhd 𝕜' f s) : AnalyticOnNhd 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma AnalyticOnNhd.im_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

end ReOfReal

section Real

variable {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
/-
**analyticAt_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.log_ofReal_re`：log_ofReal_re (x : Real) : (log (x : Complex)).re
 = Real.log x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.re_ofReal`：AnalyticAt.re_ofReal (hf : AnalyticAt Complex f x)
 : AnalyticAt Real (fun x : Real => (f x).re) x
· 使用定理 `analyticAt_clog`：analyticAt_clog (m : z in slitPlane) : AnalyticAt Compl
ex log z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma analyticAt_log (hx : 0 < x) : AnalyticAt ℝ Real.log x := by
  have : Real.log = fun x : ℝ ↦ (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
  refine AnalyticAt.re_ofReal <| analyticAt_clog ?_
  simp [hx]
/-
**analyticOnNhd_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOnNhd_log : AnalyticOnNhd Real Real.log (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_log`：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
-/
lemma analyticOnNhd_log : AnalyticOnNhd ℝ Real.log (Set.Ioi 0) := fun _ hx ↦ analyticAt_log hx
/-
**analyticOn_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_log : AnalyticOn Real Real.log (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `analyticOnNhd_log`：analyticOnNhd_log : AnalyticOnNhd Real Real.log (Set.
Ioi 0)
-/
lemma analyticOn_log : AnalyticOn ℝ Real.log (Set.Ioi 0) := analyticOnNhd_log.analyticOn

@[fun_prop]
/-
**AnalyticAt.log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.log (fa : AnalyticAt Real f x) (m : 0 < f x) : AnalyticAt Real 
(fun z => Real.log (f z)) x
参数：fa : AnalyticAt Real f x；m : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `analyticAt_log`：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
-/
lemma AnalyticAt.log (fa : AnalyticAt ℝ f x) (m : 0 < f x) :
    AnalyticAt ℝ (fun z ↦ Real.log (f z)) x :=
  (analyticAt_log m).comp fa
/-
**AnalyticWithinAt.log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.log (fa : AnalyticWithinAt Real f s x) (m : 0 < f x) : An
alyticWithinAt Real (fun z => Real.log (f z)) s x
参数：fa : AnalyticWithinAt Real f s x；m : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用引理 `analyticAt_log`：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
-/
lemma AnalyticWithinAt.log (fa : AnalyticWithinAt ℝ f s x) (m : 0 < f x) :
    AnalyticWithinAt ℝ (fun z ↦ Real.log (f z)) s x :=
  (analyticAt_log m).comp_analyticWithinAt fa
/-
**AnalyticOnNhd.log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.log (fs : AnalyticOnNhd Real f s) (m : forall x in s, 0 < f 
x) : AnalyticOnNhd Real (fun z => Real.log (f z)) s
参数：fs : AnalyticOnNhd Real f s；m : forall x in s, 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `analyticAt_log`：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
-/
lemma AnalyticOnNhd.log (fs : AnalyticOnNhd ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOnNhd ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).comp (fs z n)
/-
**AnalyticOn.log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.log (fs : AnalyticOn Real f s) (m : forall x in s, 0 < f x) : A
nalyticOn Real (fun z => Real.log (f z)) s
参数：fs : AnalyticOn Real f s；m : forall x in s, 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.comp`：AnalyticWithinAt.comp {g : F -> G} {f : E -> F} {
x : E} {t : Set F} {s : Set E} (hg : AnalyticWithinAt 𝕜 g t (f x)) (hf : Analyti
cWithinAt 𝕜…
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `analyticAt_log`：analyticAt_log (hx : 0 < x) : AnalyticAt Real Real.log x
-/
lemma AnalyticOn.log (fs : AnalyticOn ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOn ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m
/-
**iteratedDeriv_succ_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_succ_log {n : Nat} {x : Complex} (hx : x in slitPlane) : ite
ratedDeriv (n + 1) log x = (-1 : Complex) ^ n * n.factorial * x ^ (-(n : Int) - 
1)
参数：hx : x in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Complex.isOpen_slitPlane`：IsOpen Complex.slitPlane
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.deriv_log`：deriv_log {x : Complex} (h : x in slitPlane) : deriv 
log x = x⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ'`：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = ite
ratedDeriv n (deriv f)
· 使用引理 `Filter.EventuallyEq.iteratedDeriv_eq`：Filter.EventuallyEq.iteratedDeriv_
eq (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) : iteratedDeriv n f x = 
iteratedDeriv n g x
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `iter_deriv_inv`：iter_deriv_inv (k : Nat) (x : 𝕜) : deriv^[k] Inv.inv x =
 (-1) ^ k * k ! * x ^ (-1 - k : Int)
-/
theorem iteratedDeriv_succ_log {n : ℕ} {x : ℂ} (hx : x ∈ slitPlane) :
    iteratedDeriv (n + 1) log x = (-1 : ℂ) ^ n * n.factorial * x ^ (-(n : ℤ) - 1) := by
  have h_eq : deriv log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [isOpen_slitPlane.mem_nhds hx] with y hy
    simp [Complex.deriv_log hy]
  rw [iteratedDeriv_succ', h_eq.iteratedDeriv_eq, iteratedDeriv_eq_iterate, iter_deriv_inv]
  grind
/-
**hasFPowerSeriesAt_clog_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_clog_one : HasFPowerSeriesAt log (.ofScalars Complex (fu
n n => -(-1 : Complex) ^ n / n)) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `Complex.log_one`：log_one : log 1 = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
（共 84 条，此处仅展示前 30 条）
-/
theorem hasFPowerSeriesAt_clog_one :
    HasFPowerSeriesAt log (.ofScalars ℂ (fun n ↦ -(-1 : ℂ) ^ n / n)) 1 := by
  suffices ((FormalMultilinearSeries.ofScalars ℂ (fun n ↦ -(-1 : ℂ) ^ n / n)) =
      FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n log 1 / (n.factorial : ℂ))) by
    convert! AnalyticAt.hasFPowerSeriesAt _ using 1 <;> try infer_instance
    exact analyticAt_clog (by simp)
  ext n
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const_one,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, one_mul]
  obtain _ | n := n
  · simp
  simp [iteratedDeriv_succ_log one_mem_slitPlane, Nat.factorial_succ, pow_succ]
  field_simp [show n.factorial ≠ 0 by positivity]
/-
**hasFPowerSeriesAt_clog_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_clog_one_add : HasFPowerSeriesAt (fun x => log (1 + x)) 
(.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 38 条，此处仅展示前 30 条）
-/
theorem hasFPowerSeriesAt_clog_one_add :
    HasFPowerSeriesAt (fun x ↦ log (1 + x)) (.ofScalars ℂ (fun n ↦ -(-1 : ℂ) ^ n / n)) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_clog_one (-1) using 3 <;> ring
/-
**hasFPowerSeriesAt_log_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_log_one : HasFPowerSeriesAt Real.log (.ofScalars Real (f
un n => -(-1 : Real) ^ n / n)) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasFPowerSeriesAt_clog_one`：hasFPowerSeriesAt_clog_one : HasFPowerSeries
At log (.ofScalars Complex (fun n => -(-1 : Complex) ^ n / n)) 1
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `HasFPowerSeriesOnBall.restrictScalars`：HasFPowerSeriesOnBall.restrictSca
lars (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesOnBall f (p.restrictS
calars 𝕜) x r
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 40 条，此处仅展示前 30 条）
-/
theorem hasFPowerSeriesAt_log_one :
    HasFPowerSeriesAt Real.log (.ofScalars ℝ (fun n ↦ -(-1 : ℝ) ^ n / n)) 1 := by
  obtain ⟨r, hp⟩ := hasFPowerSeriesAt_clog_one
  have : HasFPowerSeriesOnBall log
      ((FormalMultilinearSeries.ofScalars ℂ (fun n ↦ -(-1 : ℂ) ^ n / n)).restrictScalars ℝ)
      (ofRealCLM 1) r := by
    simpa using hp.restrictScalars
  convert ((reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr
    (fun x _ ↦ log_ofReal_re x)).hasFPowerSeriesAt
  ext n
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  simp
  norm_cast
/-
**hasFPowerSeriesAt_log_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFPowerSeriesAt_log_one_add : HasFPowerSeriesAt (fun x => Real.log (1 + 
x)) (.ofScalars Real (fun n => -(-1 : Real) ^ n / n)) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 37 条，此处仅展示前 30 条）
-/
theorem hasFPowerSeriesAt_log_one_add :
    HasFPowerSeriesAt (fun x ↦ Real.log (1 + x)) (.ofScalars ℝ (fun n ↦ -(-1 : ℝ) ^ n / n)) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_log_one (-1) using 3 <;> ring

end Real

