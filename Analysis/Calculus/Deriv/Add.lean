/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section

universe u v w

open scoped Topology Filter ENNReal

open Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : 𝕜 → F}
variable {f' g' : F}
variable {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
/-
**HasDerivAtFilter.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter
 g g' L) : HasDerivAtFilter (f + g) (f' + g') L
参数：hf : HasDerivAtFilter f f' L；hg : HasDerivAtFilter g g' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.add`：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
· 使用定理 `HasDerivAtFilter.hasFDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
### Derivative of the sum of two functions
-/
theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L)
    (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L := by
  simpa using (hf.hasFDerivAtFilter.add hg.hasFDerivAtFilter).hasDerivAtFilter

@[to_fun]
/-
**HasStrictDerivAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt
 g g' x) : HasStrictDerivAt (f + g) (f' + g') x
参数：hf : HasStrictDerivAt f f' x；hg : HasStrictDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.add`：HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L
-/
theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
/-
**HasDerivWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithin
At g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x
参数：hf : HasDerivWithinAt f f' s x；hg : HasDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.add`：HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L
-/
theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x :=
  HasDerivAtFilter.add hf hg

@[to_fun]
/-
**HasDerivAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDeri
vAt (f + g) (f' + g') x
参数：hf : HasDerivAt f f' x；hg : HasDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.add`：HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L
-/
theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f + g) (f' + g') x :=
  HasDerivAtFilter.add hf hg
/-
**derivWithin_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Differenti
ableWithinAt 𝕜 g s x) : derivWithin (fun y => f y + g y) s x = derivWithin f s x
 + derivWithin g s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.add`：HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s
 x) (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f + g) (f' + g') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y ↦ f y + g y) s x = derivWithin f s x + derivWithin g s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_add (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Differentiable
WithinAt 𝕜 g s x) : derivWithin (f + g) s x = derivWithin f s x + derivWithin g 
s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_add`：derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 
f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : derivWithin (fun y => f y + g y) 
s x = der…
-/
theorem derivWithin_add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f + g) s x = derivWithin f s x + derivWithin g s x :=
  derivWithin_fun_add hf hg

@[simp]
/-
**deriv_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) 
: deriv (fun y => f y + g y) x = deriv f x + deriv g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.add`：HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f + g) (f' + g') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y ↦ f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
/-
**deriv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : de
riv (f + g) x = deriv f x + deriv g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.add`：HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f + g) (f' + g') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
/-
**hasDerivAtFilter_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_add_const_iff (c : F) : HasDerivAtFilter (f · + c) f' L ↔
 HasDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_add_const_iff`：hasFDerivAtFilter_add_const_iff (c : F)
 : HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_add_const_iff (c : F) :
    HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]
/-
**hasStrictDerivAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_add_const_iff (c : F) : HasStrictDerivAt (f · + c) f' x ↔
 HasStrictDerivAt f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_add_const_iff`：hasDerivAtFilter_add_const_iff (c : F) :
 HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasStrictDerivAt_add_const_iff (c : F) :
    HasStrictDerivAt (f · + c) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]
/-
**hasDerivWithinAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_add_const_iff (c : F) : HasDerivWithinAt (f · + c) f' s x
 ↔ HasDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_add_const_iff`：hasDerivAtFilter_add_const_iff (c : F) :
 HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivWithinAt_add_const_iff (c : F) :
    HasDerivWithinAt (f · + c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]
/-
**hasDerivAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_add_const_iff (c : F) : HasDerivAt (f · + c) f' x ↔ HasDerivAt 
f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_add_const_iff`：hasDerivAtFilter_add_const_iff (c : F) :
 HasDerivAtFilter (f · + c) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivAt_add_const_iff (c : F) : HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff
/-
**derivWithin_add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_add_const (c : F) : derivWithin (fun y => f y + c) s x = deriv
Within f s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_add_const`：fderivWithin_add_const (c : F) : fderivWithin 𝕜 
(fun y => f y + c) s x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_add_const (c : F) :
    derivWithin (fun y ↦ f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const]
/-
**deriv_add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_add_const`：fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c)
 x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_add_const (c : F) : deriv (fun y ↦ f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]

@[simp]
/-
**deriv_add_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_add_const`：deriv_add_const (c : F) : deriv (fun y => f y + c) x = 
deriv f x
-/
theorem deriv_add_const' (c : F) : (deriv fun y ↦ f y + c) = deriv f :=
  funext fun _ ↦ deriv_add_const c
/-
**hasDerivAtFilter_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_const_add_iff (c : F) : HasDerivAtFilter (c + f ·) f' L ↔
 HasDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const_add_iff`：hasFDerivAtFilter_const_add_iff (c : F)
 : HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_const_add_iff (c : F) :
    HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]
/-
**hasStrictDerivAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_const_add_iff (c : F) : HasStrictDerivAt (c + f ·) f' x ↔
 HasStrictDerivAt f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const_add_iff`：hasDerivAtFilter_const_add_iff (c : F) :
 HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasStrictDerivAt_const_add_iff (c : F) :
    HasStrictDerivAt (c + f ·) f' x ↔ HasStrictDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]
/-
**hasDerivWithinAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_const_add_iff (c : F) : HasDerivWithinAt (c + f ·) f' s x
 ↔ HasDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const_add_iff`：hasDerivAtFilter_const_add_iff (c : F) :
 HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivWithinAt_const_add_iff (c : F) :
    HasDerivWithinAt (c + f ·) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]
/-
**hasDerivAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_const_add_iff (c : F) : HasDerivAt (c + f ·) f' x ↔ HasDerivAt 
f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_const_add_iff`：hasDerivAtFilter_const_add_iff (c : F) :
 HasDerivAtFilter (c + f ·) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivAt_const_add_iff (c : F) : HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff
/-
**derivWithin_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_add (c : F) : derivWithin (c + f ·) s x = derivWithin f 
s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_const_add`：fderivWithin_const_add (c : F) : fderivWithin 𝕜 
(fun y => c + f y) s x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_const_add (c : F) :
    derivWithin (c + f ·) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]
/-
**derivWithin_const_add_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_add_fun (c : F) : derivWithin (c + f ·) = derivWithin f
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin_const_add`：derivWithin_const_add (c : F) : derivWithin (c + 
f ·) s x = derivWithin f s x
-/
theorem derivWithin_const_add_fun (c : F) :
    derivWithin (c + f ·) = derivWithin f := by
  ext
  apply derivWithin_const_add
/-
**deriv_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_const_add`：fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y)
 x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x := by
  simp only [deriv, fderiv_const_add]

@[simp]
/-
**deriv_const_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const_add`：deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x
-/
theorem deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f :=
  funext fun _ ↦ deriv_const_add c
/-
**deriv_const_add_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_add_id (c : 𝕜) : deriv (c + ·) x = 1
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_add`：deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
-/
theorem deriv_const_add_id (c : 𝕜) : deriv (c + ·) x = 1 := by
  rw [deriv_const_add c, deriv_id'']

@[simp]
/-
**deriv_const_add_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_add_id' (c : 𝕜) : (deriv (c + ·)) = fun _ => 1
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const_add_id`：deriv_const_add_id (c : 𝕜) : deriv (c + ·) x = 1
-/
theorem deriv_const_add_id' (c : 𝕜) : (deriv (c + ·)) = fun _ => 1 :=
  funext fun _ ↦ deriv_const_add_id c
/-
**differentiableAt_comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_add_const {a b : 𝕜} : DifferentiableAt 𝕜 (fun x => f
 (x + b)) a ↔ DifferentiableAt 𝕜 f (a + b)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiableAt_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (x + b)) a ↔ DifferentiableAt 𝕜 f (a + b) := by
  grind [add_comm, differentiableAt_comp_add_left]
/-
**differentiableAt_iff_comp_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_comp_const_add {a b : 𝕜} : DifferentiableAt 𝕜 f a ↔ D
ifferentiableAt 𝕜 (fun x => f (b + x)) (-b + a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a +
 (-a + b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_iff_comp_const_add {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (b + x)) (-b + a) := by
  simp [differentiableAt_comp_add_left]
/-
**differentiableAt_iff_comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_comp_add_const {a b : 𝕜} : DifferentiableAt 𝕜 f a ↔ D
ifferentiableAt 𝕜 (fun x => f (x + b)) (a - b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_iff_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (x + b)) (a - b) := by
  simp [differentiableAt_comp_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/

variable {ι : Type*} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

/-
**HasDerivAtFilter.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.fun_sum (h : forall i in u, HasDerivAtFilter (A i) (A' i)
 L) : HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) L
参数：h : forall i in u, HasDerivAtFilter (A i) (A' i) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.fun_sum`：HasFDerivAtFilter.fun_sum (h : forall i in u,
 HasFDerivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (fun y => ∑ i in u, A i y
) (∑ i in u, A'…
-/
theorem HasDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter
/-
**HasDerivAtFilter.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.sum (h : forall i in u, HasDerivAtFilter (A i) (A' i) L) 
: HasDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L
参数：h : forall i in u, HasDerivAtFilter (A i) (A' i) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAtFilter.fun_sum`：HasDerivAtFilter.fun_sum (h : forall i in u, H
asDerivAtFilter (A i) (A' i) L) : HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑
 i in u, A' i)…
-/
theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) L) :
    HasDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) L := by
  convert! HasDerivAtFilter.fun_sum h
  simp
/-
**HasStrictDerivAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.fun_sum (h : forall i in u, HasStrictDerivAt (A i) (A' i)
 x) : HasStrictDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
参数：h : forall i in u, HasStrictDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.fun_sum`：HasDerivAtFilter.fun_sum (h : forall i in u, H
asDerivAtFilter (A i) (A' i) L) : HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑
 i in u, A' i)…
-/
theorem HasStrictDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.fun_sum h
/-
**HasStrictDerivAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.sum (h : forall i in u, HasStrictDerivAt (A i) (A' i) x) 
: HasStrictDerivAt (∑ i in u, A i) (∑ i in u, A' i) x
参数：h : forall i in u, HasStrictDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sum`：HasDerivAtFilter.sum (h : forall i in u, HasDerivA
tFilter (A i) (A' i) L) : HasDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L
-/
theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.sum h
/-
**HasDerivWithinAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.fun_sum (h : forall i in u, HasDerivWithinAt (A i) (A' i)
 s x) : HasDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x
参数：h : forall i in u, HasDerivWithinAt (A i) (A' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.fun_sum`：HasDerivAtFilter.fun_sum (h : forall i in u, H
asDerivAtFilter (A i) (A' i) L) : HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑
 i in u, A' i)…
-/
theorem HasDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasDerivAtFilter.fun_sum h
/-
**HasDerivWithinAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.sum (h : forall i in u, HasDerivWithinAt (A i) (A' i) s x
) : HasDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i) s x
参数：h : forall i in u, HasDerivWithinAt (A i) (A' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sum`：HasDerivAtFilter.sum (h : forall i in u, HasDerivA
tFilter (A i) (A' i) L) : HasDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L
-/
theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) s x :=
  HasDerivAtFilter.sum h
/-
**HasDerivAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.fun_sum (h : forall i in u, HasDerivAt (A i) (A' i) x) : HasDer
ivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
参数：h : forall i in u, HasDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.fun_sum`：HasDerivAtFilter.fun_sum (h : forall i in u, H
asDerivAtFilter (A i) (A' i) L) : HasDerivAtFilter (fun y => ∑ i in u, A i y) (∑
 i in u, A' i)…
-/
theorem HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.fun_sum h
/-
**HasDerivAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.sum (h : forall i in u, HasDerivAt (A i) (A' i) x) : HasDerivAt
 (∑ i in u, A i) (∑ i in u, A' i) x
参数：h : forall i in u, HasDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sum`：HasDerivAtFilter.sum (h : forall i in u, HasDerivA
tFilter (A i) (A' i) L) : HasDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L
-/
theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasDerivAtFilter.sum h
/-
**derivWithin_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x
) : derivWithin (fun y => ∑ i in u, A i y) s x = ∑ i in u, derivWithin (A i) s x
参数：h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.fun_sum`：HasDerivWithinAt.fun_sum (h : forall i in u, H
asDerivWithinAt (A i) (A' i) s x) : HasDerivWithinAt (fun y => ∑ i in u, A i y) 
(∑ i in u, A' …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (fun y ↦ ∑ i ∈ u, A i y) s x = ∑ i ∈ u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_sum fun i hi ↦ (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x) : 
derivWithin (∑ i in u, A i) s x = ∑ i in u, derivWithin (A i) s x
参数：h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.sum`：HasDerivWithinAt.sum (h : forall i in u, HasDerivW
ithinAt (A i) (A' i) s x) : HasDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i) s 
x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin (∑ i ∈ u, A i) s x = ∑ i ∈ u, derivWithin (A i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.sum fun i hi ↦ (h i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[simp]
/-
**deriv_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) : deriv (fun
 y => ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.fun_sum`：HasDerivAt.fun_sum (h : forall i in u, HasDerivAt (A
 i) (A' i) x) : HasDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (fun y ↦ ∑ i ∈ u, A i y) x = ∑ i ∈ u, deriv (A i) x :=
  (HasDerivAt.fun_sum fun i hi ↦ (h i hi).hasDerivAt).deriv

@[simp]
/-
**deriv_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) : deriv (∑ i in 
u, A i) x = ∑ i in u, deriv (A i) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.sum`：HasDerivAt.sum (h : forall i in u, HasDerivAt (A i) (A' 
i) x) : HasDerivAt (∑ i in u, A i) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv (∑ i ∈ u, A i) x = ∑ i ∈ u, deriv (A i) x :=
  (HasDerivAt.sum fun i hi ↦ (h i hi).hasDerivAt).deriv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/

@[to_fun]
/-
**HasDerivAtFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L) : HasDerivAtFilter (-f)
 (-f') L
参数：h : HasDerivAtFilter f f' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L

--- 原说明 ---
### Derivative of the negative of a function
-/
theorem HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (-f) (-f') L := by simpa using (HasFDerivAtFilter.neg h).hasDerivAtFilter

@[to_fun]
/-
**HasDerivWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) : HasDerivWithinAt (-
f) (-f') s x
参数：h : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L
-/
theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (-f) (-f') s x :=
  HasDerivAtFilter.neg h

@[to_fun]
/-
**HasDerivAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f) (-f') x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L
-/
theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
/-
**HasStrictDerivAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (-f)
 (-f') x
参数：h : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L
-/
theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (-f) (-f') x :=
  HasDerivAtFilter.neg h

@[to_fun]
/-
**derivWithin.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin.neg : derivWithin (-f) s x = -derivWithin f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderivWithin_neg`：fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : fd
erivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem derivWithin.neg : derivWithin (-f) s x = -derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp only [derivWithin, fderivWithin_neg hsx, neg_apply]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[to_fun]
/-
**deriv.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv.neg : deriv (-f) x = -deriv f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderiv_neg`：fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv.neg : deriv (-f) x = -deriv f x := by
  simp only [deriv, fderiv_neg, neg_apply]

@[to_fun (attr := simp)]
/-
**deriv.neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv.neg`：deriv.neg : deriv (-f) x = -deriv f x
-/
theorem deriv.neg' : (deriv (-f)) = fun x ↦ -deriv f x :=
  funext fun _ ↦ deriv.neg

end Neg

section Neg2

/-! ### Derivative of the negation function (i.e `Neg.neg`) -/

variable (s x L)

/-
**hasDerivAtFilter_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L
· 使用定理 `hasDerivAtFilter_id`：hasDerivAtFilter_id : HasDerivAtFilter id 1 L
-/
theorem hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-1) L :=
  HasDerivAtFilter.neg <| hasDerivAtFilter_id _
/-
**hasDerivWithinAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_neg`：hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-
1) L
-/
theorem hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-1) s x :=
  hasDerivAtFilter_neg _
/-
**hasDerivAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_neg : HasDerivAt Neg.neg (-1) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_neg`：hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-
1) L
-/
theorem hasDerivAt_neg : HasDerivAt Neg.neg (-1) x :=
  hasDerivAtFilter_neg _
/-
**hasDerivAt_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_neg`：hasDerivAtFilter_neg : HasDerivAtFilter Neg.neg (-
1) L
-/
theorem hasDerivAt_neg' : HasDerivAt (fun x ↦ -x) (-1) x :=
  hasDerivAtFilter_neg _
/-
**hasStrictDerivAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.neg`：HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x)
 : HasStrictDerivAt (-f) (-f') x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
-/
theorem hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-1) x :=
  HasStrictDerivAt.neg <| hasStrictDerivAt_id _
/-
**deriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_neg : deriv Neg.neg x = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_neg`：hasDerivAt_neg : HasDerivAt Neg.neg (-1) x
-/
theorem deriv_neg : deriv Neg.neg x = -1 :=
  HasDerivAt.deriv (hasDerivAt_neg x)

@[simp]
/-
**deriv_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_neg' : deriv (Neg.neg : 𝕜 -> 𝕜) = fun _ => -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_neg`：deriv_neg : deriv Neg.neg x = -1
-/
theorem deriv_neg' : deriv (Neg.neg : 𝕜 → 𝕜) = fun _ ↦ -1 :=
  funext deriv_neg

@[simp]
/-
**deriv_neg''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_neg'' : deriv (fun x : 𝕜 => -x) x = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_neg`：deriv_neg : deriv Neg.neg x = -1
-/
theorem deriv_neg'' : deriv (fun x : 𝕜 ↦ -x) x = -1 :=
  deriv_neg x
/-
**derivWithin_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x
 = -1
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `hasDerivWithinAt_neg`：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-
1) s x
-/
theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin Neg.neg s x = -1 :=
  (hasDerivWithinAt_neg x s).derivWithin hxs
/-
**differentiable_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -> 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.neg`：Differentiable.neg (h : Differentiable 𝕜 f) : Differ
entiable 𝕜 (-f)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
theorem differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 → 𝕜) :=
  Differentiable.neg differentiable_id
/-
**differentiableOn_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 -> 𝕜) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
-/
theorem differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg : 𝕜 → 𝕜) s :=
  DifferentiableOn.neg differentiableOn_id
/-
**differentiableAt_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_neg {a : 𝕜} : DifferentiableAt 𝕜 (fun x => f (-x)) a
 ↔ DifferentiableAt 𝕜 f (-a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `differentiable_neg`：differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -
> 𝕜)
-/
lemma differentiableAt_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (-x)) a ↔ DifferentiableAt 𝕜 f (-a) := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.comp a differentiable_neg.differentiableAt⟩
  convert! ((neg_neg a).symm ▸ H).comp (-a) differentiable_neg.differentiableAt
  ext
  simp only [Function.comp_apply, neg_neg]
/-
**differentiableAt_iff_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_comp_neg {a : 𝕜} : DifferentiableAt 𝕜 f a ↔ Different
iableAt 𝕜 (fun x => f (-x)) (-a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_iff_comp_neg {a : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (-x)) (-a) := by
  simp_rw [← differentiableAt_comp_neg, neg_neg]

end Neg2

section Sub

/-! ### Derivative of the difference of two functions -/

@[to_fun]
/-
**HasDerivAtFilter.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter
 g g' L) : HasDerivAtFilter (f - g) (f' - g') L
参数：hf : HasDerivAtFilter f f' L；hg : HasDerivAtFilter g g' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasDerivAtFilter.add`：HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f + g) (f' + g') L
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L

--- 原说明 ---
### Derivative of the difference of two functions
-/
theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L) :
    HasDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]
/-
**HasDerivWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithin
At g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x
参数：hf : HasDerivWithinAt f f' s x；hg : HasDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sub`：HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f - g) (f' - g') L
-/
theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
/-
**HasDerivAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDeri
vAt (f - g) (f' - g') x
参数：hf : HasDerivAt f f' x；hg : HasDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sub`：HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f - g) (f' - g') L
-/
theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg

@[to_fun]
/-
**HasStrictDerivAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt
 g g' x) : HasStrictDerivAt (f - g) (f' - g') x
参数：hf : HasStrictDerivAt f f' x；hg : HasStrictDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.sub`：HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L
) (hg : HasDerivAtFilter g g' L) : HasDerivAtFilter (f - g) (f' - g') L
-/
theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (f - g) (f' - g') x :=
  HasDerivAtFilter.sub hf hg
/-
**derivWithin_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_sub (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Differenti
ableWithinAt 𝕜 g s x) : derivWithin (fun y => f y - g y) s x = derivWithin f s x
 - derivWithin g s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `derivWithin_fun_add`：derivWithin_fun_add (hf : DifferentiableWithinAt 𝕜 
f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : derivWithin (fun y => f y + g y) 
s x = der…
· 使用定理 `DifferentiableWithinAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `derivWithin.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {
F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 
→ F} {x :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y ↦ f y - g y) s x = derivWithin f s x - derivWithin g s x := by
  simp only [sub_eq_add_neg, derivWithin_fun_add hf hg.fun_neg, derivWithin.fun_neg]
/-
**derivWithin_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sub (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Differentiable
WithinAt 𝕜 g s x) : derivWithin (f - g) s x = derivWithin f s x - derivWithin g 
s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_sub`：derivWithin_fun_sub (hf : DifferentiableWithinAt 𝕜 
f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : derivWithin (fun y => f y - g y) 
s x = der…
-/
theorem derivWithin_sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (f - g) s x = derivWithin f s x - derivWithin g s x :=
  derivWithin_fun_sub hf hg

@[simp]
/-
**deriv_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) 
: deriv (fun y => f y - g y) x = deriv f x - deriv g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y ↦ f y - g y) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
/-
**deriv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : de
riv (f - g) x = deriv f x - deriv g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (f - g) x = deriv f x - deriv g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

@[simp]
/-
**hasDerivAtFilter_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_sub_const_iff (c : F) : HasDerivAtFilter (fun x => f x - 
c) f' L ↔ HasDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_sub_const_iff`：hasFDerivAtFilter_sub_const_iff (c : F)
 : HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_sub_const_iff (c : F) :
    HasDerivAtFilter (fun x ↦ f x - c) f' L ↔ HasDerivAtFilter f f' L :=
  hasFDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAtFilter.sub_const⟩ := hasDerivAtFilter_sub_const_iff

@[simp]
/-
**hasDerivWithinAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_sub_const_iff (c : F) : HasDerivWithinAt (f · - c) f' s x
 ↔ HasDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_sub_const_iff`：hasDerivAtFilter_sub_const_iff (c : F) :
 HasDerivAtFilter (fun x => f x - c) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivWithinAt_sub_const_iff (c : F) :
    HasDerivWithinAt (f · - c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivWithinAt.sub_const⟩ := hasDerivWithinAt_sub_const_iff

@[simp]
/-
**hasDerivAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_sub_const_iff (c : F) : HasDerivAt (f · - c) f' x ↔ HasDerivAt 
f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_sub_const_iff`：hasDerivAtFilter_sub_const_iff (c : F) :
 HasDerivAtFilter (fun x => f x - c) f' L ↔ HasDerivAtFilter f f' L
-/
theorem hasDerivAt_sub_const_iff (c : F) : HasDerivAt (f · - c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_sub_const_iff c

alias ⟨_, HasDerivAt.sub_const⟩ := hasDerivAt_sub_const_iff
/-
**derivWithin_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sub_const (c : F) : derivWithin (fun y => f y - c) s x = deriv
Within f s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_sub_const`：fderivWithin_sub_const (c : F) : fderivWithin 𝕜 
(fun y => f y - c) s x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_sub_const (c : F) :
    derivWithin (fun y ↦ f y - c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_sub_const]

@[simp]
/-
**derivWithin_sub_const_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sub_const_fun (c : F) : derivWithin (f · - c) = derivWithin f
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin_sub_const`：derivWithin_sub_const (c : F) : derivWithin (fun 
y => f y - c) s x = derivWithin f s x
-/
theorem derivWithin_sub_const_fun (c : F) : derivWithin (f · - c) = derivWithin f := by
  ext
  apply derivWithin_sub_const
/-
**deriv_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sub_const (c : F) : deriv (fun y => f y - c) x = deriv f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_sub_const`：fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c)
 x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_sub_const (c : F) : deriv (fun y ↦ f y - c) x = deriv f x := by
  simp only [deriv, fderiv_sub_const]

@[simp]
/-
**deriv_sub_const_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sub_const_fun (c : F) : deriv (f · - c) = deriv f
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_sub_const`：deriv_sub_const (c : F) : deriv (fun y => f y - c) x = 
deriv f x
-/
theorem deriv_sub_const_fun (c : F) : deriv (f · - c) = deriv f := by
  ext
  apply deriv_sub_const
/-
**HasDerivAtFilter.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' L) : HasDer
ivAtFilter (fun x => c - f x) (-f') L
参数：c : F；hf : HasDerivAtFilter f f' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasDerivAtFilter.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{f : 𝕜 → F} {f' …
· 使用定理 `HasDerivAtFilter.neg`：HasDerivAtFilter.neg (h : HasDerivAtFilter f f' L)
 : HasDerivAtFilter (-f) (-f') L
-/
theorem HasDerivAtFilter.const_sub (c : F) (hf : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x ↦ c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c
/-
**HasDerivWithinAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) : HasD
erivWithinAt (fun x => c - f x) (-f') s x
参数：c : F；hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.const_sub`：HasDerivAtFilter.const_sub (c : F) (hf : Has
DerivAtFilter f f' L) : HasDerivAtFilter (fun x => c - f x) (-f') L
-/
theorem HasDerivWithinAt.const_sub (c : F) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x ↦ c - f x) (-f') s x :=
  HasDerivAtFilter.const_sub c hf
/-
**HasStrictDerivAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) : HasStr
ictDerivAt (fun x => c - f x) (-f') x
参数：c : F；hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.const_sub`：HasDerivAtFilter.const_sub (c : F) (hf : Has
DerivAtFilter f f' L) : HasDerivAtFilter (fun x => c - f x) (-f') L
-/
theorem HasStrictDerivAt.const_sub (c : F) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x ↦ c - f x) (-f') x :=
  HasDerivAtFilter.const_sub c hf

nonrec theorem HasDerivAt.const_sub (c : F) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x ↦ c - f x) (-f') x :=
  hf.const_sub c
/-
**derivWithin_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_sub (c : F) : derivWithin (fun y => c - f y) s x = -deri
vWithin f s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `derivWithin_const_add_fun`：derivWithin_const_add_fun (c : F) : derivWith
in (c + f ·) = derivWithin f
· 使用定理 `derivWithin.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {
F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 
→ F} {x :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_const_sub (c : F) :
    derivWithin (fun y ↦ c - f y) s x = -derivWithin f s x := by
  simp [sub_eq_add_neg, derivWithin.fun_neg]
/-
**deriv_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `derivWithin_const_sub`：derivWithin_const_sub (c : F) : derivWithin (fun 
y => c - f y) s x = -derivWithin f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f x := by
  simp only [← derivWithin_univ, derivWithin_const_sub]

@[simp]
/-
**deriv_const_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_sub' (c : F) : deriv (c - f ·) = (-deriv f ·)
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const_sub`：deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f 
x
-/
theorem deriv_const_sub' (c : F) : deriv (c - f ·) = (-deriv f ·) :=
  funext fun _ => deriv_const_sub c
/-
**deriv_const_sub_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_sub_id (c : 𝕜) : deriv (c - ·) x = -1
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_sub`：deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f 
x
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
-/
theorem deriv_const_sub_id (c : 𝕜) : deriv (c - ·) x = -1 := by
  rw [deriv_const_sub c, deriv_id'']

@[simp]
/-
**deriv_const_sub_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_sub_id' (c : 𝕜) : deriv (c - ·) = fun _ => -1
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const_sub_id`：deriv_const_sub_id (c : 𝕜) : deriv (c - ·) x = -1
-/
theorem deriv_const_sub_id' (c : 𝕜) : deriv (c - ·) = fun _ => -1 :=
  funext fun _ => deriv_const_sub_id c
/-
**differentiableAt_comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_sub_const {a b : 𝕜} : DifferentiableAt 𝕜 (fun x => f
 (x - b)) a ↔ DifferentiableAt 𝕜 f (a - b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (x - b)) a ↔ DifferentiableAt 𝕜 f (a - b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]
/-
**differentiableAt_comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_const_sub {a b : 𝕜} : DifferentiableAt 𝕜 (fun x => f
 (b - x)) a ↔ DifferentiableAt 𝕜 f (b - a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Differentiable.const_sub`：Differentiable.const_sub (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => c - f y
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
lemma differentiableAt_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (b - x)) a ↔ DifferentiableAt 𝕜 f (b - a) := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.comp a (differentiable_id.const_sub _).differentiableAt⟩
  convert!
    ((sub_sub_cancel _ a).symm ▸ H).comp (b - a) (differentiable_id.const_sub _).differentiableAt
  ext
  simp
/-
**differentiableAt_iff_comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_comp_sub_const {a b : 𝕜} : DifferentiableAt 𝕜 f a ↔ D
ifferentiableAt 𝕜 (fun x => f (x - b)) (a + b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_iff_comp_sub_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (x - b)) (a + b) := by
  simp [sub_eq_add_neg, differentiableAt_comp_add_const]
/-
**differentiableAt_iff_comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_comp_const_sub {a b : 𝕜} : DifferentiableAt 𝕜 f a ↔ D
ifferentiableAt 𝕜 (fun x => f (b - x)) (b - a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentiableAt_iff_comp_const_sub {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (b - x)) (b - a) := by
  simp [differentiableAt_comp_const_sub]

end Sub

