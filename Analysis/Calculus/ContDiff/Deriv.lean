/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher differentiability in one dimension

The general theory of higher derivatives in Mathlib is developed using the Fréchet derivative
`fderiv`; but for maps defined on the field, the one-dimensional derivative `deriv` is often easier
to use. In this file, we reformulate some higher smoothness results in terms of `deriv`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open scoped ContDiff

open Set

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m n : ℕ∞ω} {f : 𝕜 → F} {s : Set 𝕜}

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `derivWithin`) is `C^n`. -/
/-
**contDiffOn_succ_iff_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n 
+ 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n
 (derivWithin f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingletonCLE_symm_apply`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_
2 : _root_.Module 𝕜 E] [inst_3 : Topolo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is `C^(n + 1)` on a domain with unique derivatives if and only if it 
is
differentiable there, and its derivative (formulated with `derivWithin`) is `C^n
`.
-/
theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (derivWithin f s) s := by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]
/-
**contDiffOn_one_iff_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_one_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 1 f 
s ↔ DifferentiableOn 𝕜 f s ∧ ContinuousOn (derivWithin f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_one_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 1 f s ↔ DifferentiableOn 𝕜 f s ∧ ContinuousOn (derivWithin f s) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs]
  simp
/-
**contDiffOn_infty_iff_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 ∞ 
f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (derivWithin f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (derivWithin f s) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
/-
**contDiffOn_succ_iff_deriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1)
 f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (de
riv f) s
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `contDiffOn_congr`：contDiffOn_congr (h₁ : forall x in s, f₁ x = f x) : Co
ntDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x

--- 原说明 ---
A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`.
-/
theorem contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (deriv f) s := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))
/-
**contDiffOn_infty_iff_deriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s) : ContDiffOn 𝕜 ∞ f s 
↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (deriv f) s
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_deriv_of_isOpen`：contDiffOn_succ_iff_deriv_of_isOpen
 (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ Cont…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (deriv f) s := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp
/-
**ContDiffOn.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffOn`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {m n : WithTop ℕ∞} {f : 𝕜 
→ F} {s : Set 𝕜},   ContDiffOn 𝕜 n f s → UniqueDiffOn 𝕜 s → m + 1 ≤ n → ContDiff
On 𝕜 m (derivWithin f s) s
参数：derivWithin f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
-/
protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f s) s :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2
/-
**ContDiffOn.deriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn 
: m + 1 <= n) : ContDiffOn 𝕜 m (deriv f) s
参数：hf : ContDiffOn 𝕜 n f s；hs : IsOpen s；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `ContDiffOn.derivWithin`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{m n : WithT…
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x
-/
theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f) s :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm
/-
**ContDiffOn.continuousOn_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueD
iffOn 𝕜 s) (hn : 1 <= n) : ContinuousOn (derivWithin f s) s
参数：h : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_derivWithin`：contDiffOn_succ_iff_derivWithin (hs : U
niqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ …
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f s) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn
/-
**ContDiffOn.continuousOn_deriv_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsO
pen s) (hn : 1 <= n) : ContinuousOn (deriv f) s
参数：h : ContDiffOn 𝕜 n f s；hs : IsOpen s；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_succ_iff_deriv_of_isOpen`：contDiffOn_succ_iff_deriv_of_isOpen
 (hs : IsOpen s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω ->
 AnalyticOn 𝕜 f s) ∧ Cont…
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (deriv f) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]
/-
**ContDiffWithinAt.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {m n : WithTop ℕ∞} {f : 𝕜 
→ F} {s : Set 𝕜} {x : 𝕜},   ContDiffWithinAt 𝕜 n f s x → UniqueDiffOn 𝕜 s → m + 
1 ≤ n → x ∈ s → ContDiffWithinAt 𝕜 m (derivWithin f s) s x
参数：derivWithin f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `ContDiffWithinAt.clm_apply`：ContDiffWithinAt.clm_apply {f : E -> F ->L[𝕜
] G} {g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g
 s x) : ContDiff…
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `trivial`：True
-/
protected lemma ContDiffWithinAt.derivWithin {x : 𝕜}
    (H : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (derivWithin f s) s x := by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f ↦ f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ ↦ trivial)

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
/-
**contDiff_succ_iff_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_succ_iff_deriv : ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n =
 ω -> AnalyticOn 𝕜 f univ) ∧ ContDiff 𝕜 n (deriv f)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`.
-/
theorem contDiff_succ_iff_deriv :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω → AnalyticOn 𝕜 f univ) ∧
      ContDiff 𝕜 n (deriv f) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]
/-
**contDiff_one_iff_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_one_iff_deriv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous 
(deriv f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_succ_iff_deriv`：contDiff_succ_iff_deriv : ContDiff 𝕜 (n + 1) f 
↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOn 𝕜 f univ) ∧ ContDiff 𝕜 n (deriv f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_one_iff_deriv :
    ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (deriv f) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  simp
/-
**contDiff_infty_iff_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_infty_iff_deriv : ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 
𝕜 ∞ (deriv f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_succ_iff_deriv`：contDiff_succ_iff_deriv : ContDiff 𝕜 (n + 1) f 
↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOn 𝕜 f univ) ∧ ContDiff 𝕜 n (deriv f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_infty_iff_deriv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (deriv f) := by
  rw [show (∞ : ℕ∞ω) = ∞ + 1 from rfl, contDiff_succ_iff_deriv]
  simp
/-
**ContDiff.continuous_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_deriv (h : ContDiff 𝕜 n f) (hn : 1 <= n) : Continuous 
(deriv f)
参数：h : ContDiff 𝕜 n f；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_succ_iff_deriv`：contDiff_succ_iff_deriv : ContDiff 𝕜 (n + 1) f 
↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOn 𝕜 f univ) ∧ ContDiff 𝕜 n (deriv f)
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Continuous (deriv f) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]
/-
**ContDiff.continuous_deriv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f) : Continuous (deriv f)
参数：h : ContDiff 𝕜 1 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous_deriv`：ContDiff.continuous_deriv (h : ContDiff 𝕜 n f
) (hn : 1 <= n) : Continuous (deriv f)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f) : Continuous (deriv f) :=
  ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]
/-
**ContDiff.differentiable_deriv_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable_deriv_two (h : ContDiff 𝕜 2 f) : Differentiable 𝕜 
(deriv f)
参数：h : ContDiff 𝕜 2 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Differentiable.clm_apply`：Differentiable.clm_apply (hc : Differentiable 
𝕜 c) (hu : Differentiable 𝕜 u) : Differentiable 𝕜 fun y => (c y) (u y)
· 使用定理 `Differentiable.fderiv_two`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} {G : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGro
up E] [inst_2 :…
· 使用定理 `ContDiff.fun_comp`：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : Con
tDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
· 使用定理 `ContDiff.snd`：ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).2
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem ContDiff.differentiable_deriv_two (h : ContDiff 𝕜 2 f) : Differentiable 𝕜 (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
/-
**ContDiffAt.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {m n : WithTop ℕ∞} {f : 𝕜 
→ F} {x : 𝕜},   ContDiffAt 𝕜 n f x → m + 1 ≤ n → ContDiffAt 𝕜 m (deriv f) x
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ContDiffWithinAt.derivWithin`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : No
ntriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace
 𝕜 F] {m n : WithT…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
protected lemma ContDiffAt.derivWithin {x : 𝕜} (H : ContDiffAt 𝕜 n f x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (deriv f) x := by
  simpa using! ContDiffWithinAt.derivWithin (s := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]
/-
**ContDiff.deriv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n (deriv f)
参数：h : ContDiff 𝕜 (n + 1) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.clm_apply`：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F
} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x
)
· 使用定理 `ContDiff.fderiv_succ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G 
: Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E]
 [inst_2 :…
· 使用定理 `ContDiff.fun_comp`：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : Con
tDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
· 使用定理 `ContDiff.snd`：ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).2
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
/-
**ContDiff.iterate_deriv** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n : ℕ) {f : 𝕜 → F}, ContD
iff 𝕜 (↑⊤) f → ContDiff 𝕜 (↑⊤) (deriv^[n] f)
参数：n : ℕ；↑⊤；↑⊤；deriv^[n] f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContDiff.iterate_deriv :
    ∀ (n : ℕ) {f : 𝕜 → F}, ContDiff 𝕜 ∞ f → ContDiff 𝕜 ∞ (deriv^[n] f)
  | 0, _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_infty_iff_deriv.mp hf).2

@[fun_prop]
/-
**ContDiff.iterate_deriv'** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n k : ℕ) {f : 𝕜 → F}, Con
tDiff 𝕜 (↑(n + k)) f → ContDiff 𝕜 (↑n) (deriv^[k] f)
参数：n k : ℕ；↑(n + k)；↑n；deriv^[k] f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContDiff.iterate_deriv' (n : ℕ) :
    ∀ (k : ℕ) {f : 𝕜 → F}, ContDiff 𝕜 (n + k : ℕ) f → ContDiff 𝕜 n (deriv^[k] f)
  | 0, _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2.2

end

