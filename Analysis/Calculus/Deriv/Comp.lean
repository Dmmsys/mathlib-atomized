/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# One-dimensional derivatives of compositions of functions

In this file we prove the chain rule for the following cases:

* `HasDerivAt.comp` etc: `f : 𝕜' → 𝕜'` composed with `g : 𝕜 → 𝕜'`;
* `HasDerivAt.scomp` etc: `f : 𝕜' → E` composed with `g : 𝕜 → 𝕜'`;
* `HasFDerivAt.comp_hasDerivAt` etc: `f : E → F` composed with `g : 𝕜 → E`;

Here `𝕜` is the base normed field, `E` and `F` are normed spaces over `𝕜` and `𝕜'` is an algebra
over `𝕜` (e.g., `𝕜'=𝕜` or `𝕜=ℝ`, `𝕜'=ℂ`).

We also give versions with the `of_eq` suffix, which require an equality proof instead
of definitional equality of the different points used in the composition. These versions are
often more flexible to use.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, chain rule
-/

public section


universe u v w

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section Composition

/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector-valued and scalar-valued functions, and `comp`
in lemmas on composition of scalar-valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/


/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter (𝕜' × 𝕜')} {y : 𝕜'} (x)

/-
**HasDerivAtFilter.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' L') (hh : HasDerivAtF
ilter h h' L) (hL : Tendsto (Prod.map h h) L L') : HasDerivAtFilter (g₁ ∘ h) (h'
 • g₁') L
参数：hg : HasDerivAtFilter g₁ g₁' L'；hh : HasDerivAtFilter h h' L；hL : Tendsto (Pr
od.map h h) L L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L
· 使用定理 `HasDerivAtFilter.hasFDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁ g₁' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') L := by
  simpa using ((hg.hasFDerivAtFilter.restrictScalars 𝕜).comp hh hL).hasDerivAtFilter

@[deprecated HasDerivAtFilter.scomp (since := "2026-02-17")]
/-
**HasDerivAtFilter.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.scomp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'} (hg : HasDeri
vAtFilter g₁ g₁' (L' ×ˢ pure y)) (hh : HasDerivAtFilter h h' (L ×ˢ pure x)) (hy 
: y = h x) (hL : Tendsto h L L') : HasDerivAtFilter (g₁ ∘ h) (h' • g₁') (L ×ˢ pu
re x)
参数：hg : HasDerivAtFilter g₁ g₁' (L' ×ˢ pure y)；hh : HasDerivAtFilter h h' (L ×ˢ 
pure x)；hy : y = h x；hL : Tendsto h L L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasDerivAtFilter.scomp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hg : HasDerivAtFilter g₁ g₁' (L' ×ˢ pure y)) (hh : HasDerivAtFilter h h' (L ×ˢ pure x))
    (hy : y = h x) (hL : Tendsto h L L') :
    HasDerivAtFilter (g₁ ∘ h) (h' • g₁') (L ×ˢ pure x) :=
  hg.scomp hh <| .prodMap hL <| by simp [hy]
/-
**HasDerivWithinAt.scomp_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x)) 
(hh : HasDerivAt h h' x) (hs : forall x, h x in s') : HasDerivAt (g₁ ∘ h) (h' • 
g₁') x
参数：hg : HasDerivWithinAt g₁ g₁' s' (h x)；hh : HasDerivAt h h' x；hs : forall x, h
 x in s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivWithinAt.scomp_hasDerivAt (hg : HasDerivWithinAt g₁ g₁' s' (h x))
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') : HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  hg.scomp hh <| .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, .of_forall hs⟩)
    (tendsto_pure_pure _ _)
/-
**HasDerivWithinAt.scomp_hasDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.scomp_hasDerivAt_of_eq (hg : HasDerivWithinAt g₁ g₁' s' y
) (hh : HasDerivAt h h' x) (hs : forall x, h x in s') (hy : y = h x) : HasDerivA
t (g₁ ∘ h) (h' • g₁') x
参数：hg : HasDerivWithinAt g₁ g₁' s' y；hh : HasDerivAt h h' x；hs : forall x, h x i
n s'；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.scomp_hasDerivAt`：HasDerivWithinAt.scomp_hasDerivAt (hg
 : HasDerivWithinAt g₁ g₁' s' (h x)) (hh : HasDerivAt h h' x) (hs : forall x, h 
x in s') : HasDerivAt (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivWithinAt.scomp_hasDerivAt_of_eq (hg : HasDerivWithinAt g₁ g₁' s' y)
    (hh : HasDerivAt h h' x) (hs : ∀ x, h x ∈ s') (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp_hasDerivAt x hh hs
/-
**HasDerivWithinAt.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x)) (hh : HasDe
rivWithinAt h h' s x) (hst : MapsTo h s t') : HasDerivWithinAt (g₁ ∘ h) (h' • g₁
') s x
参数：hg : HasDerivWithinAt g₁ g₁' t' (h x)；hh : HasDerivWithinAt h h' s x；hst : Ma
psTo h s t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁ g₁' t' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivAtFilter.scomp hg hh <| hh.continuousWithinAt.tendsto_nhdsWithin hst |>.prodMap <|
    tendsto_pure_pure ..
/-
**HasDerivWithinAt.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.scomp_of_eq (hg : HasDerivWithinAt g₁ g₁' t' y) (hh : Has
DerivWithinAt h h' s x) (hst : MapsTo h s t') (hy : y = h x) : HasDerivWithinAt 
(g₁ ∘ h) (h' • g₁') s x
参数：hg : HasDerivWithinAt g₁ g₁' t' y；hh : HasDerivWithinAt h h' s x；hst : MapsTo
 h s t'；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivWithinAt.scomp_of_eq (hg : HasDerivWithinAt g₁ g₁' t' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp x hh hst

/-- The chain rule. -/
/-
**HasDerivAt.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
 HasDerivAt (g₁ ∘ h) (h' • g₁') x
参数：hg : HasDerivAt g₁ g₁' (h x)；hh : HasDerivAt h h' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))

--- 原说明 ---
The chain rule.
-/
theorem HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x :=
  HasDerivAtFilter.scomp hg hh <| hh.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _

/-- The chain rule. -/
/-
**HasDerivAt.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.scomp_of_eq (hg : HasDerivAt g₁ g₁' y) (hh : HasDerivAt h h' x)
 (hy : y = h x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
参数：hg : HasDerivAt g₁ g₁' y；hh : HasDerivAt h h' x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The chain rule.
-/
theorem HasDerivAt.scomp_of_eq
    (hg : HasDerivAt g₁ g₁' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh
/-
**HasStrictDerivAt.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStric
tDerivAt h h' x) : HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x
参数：hg : HasStrictDerivAt g₁ g₁' (h x)；hh : HasStrictDerivAt h h' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `ContinuousAt.prodMap`：ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p 
: X × Y} (hf : ContinuousAt f p.fst) (hg : ContinuousAt g p.snd) : ContinuousAt 
(Prod.map …
· 使用定理 `HasStrictFDerivAt.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁ g₁' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x :=
  HasDerivAtFilter.scomp hg hh <|
    hh.hasStrictFDerivAt.continuousAt.prodMap hh.hasStrictFDerivAt.continuousAt
/-
**HasStrictDerivAt.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.scomp_of_eq (hg : HasStrictDerivAt g₁ g₁' y) (hh : HasStr
ictDerivAt h h' x) (hy : y = h x) : HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x
参数：hg : HasStrictDerivAt g₁ g₁' y；hh : HasStrictDerivAt h h' x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.scomp`：HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁
 g₁' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (g₁ ∘ h) (h' • g₁'
) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasStrictDerivAt.scomp_of_eq
    (hg : HasStrictDerivAt g₁ g₁' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (g₁ ∘ h) (h' • g₁') x := by
  rw [hy] at hg; exact hg.scomp x hh
/-
**HasDerivAt.scomp_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x)) (hh : Has
DerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x
参数：hg : HasDerivAt g₁ g₁' (h x)；hh : HasDerivWithinAt h h' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem HasDerivAt.scomp_hasDerivWithinAt (hg : HasDerivAt g₁ g₁' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x :=
  HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh (mapsTo_univ _ _)
/-
**HasDerivAt.scomp_hasDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.scomp_hasDerivWithinAt_of_eq (hg : HasDerivAt g₁ g₁' y) (hh : H
asDerivWithinAt h h' s x) (hy : y = h x) : HasDerivWithinAt (g₁ ∘ h) (h' • g₁') 
s x
参数：hg : HasDerivAt g₁ g₁' y；hh : HasDerivWithinAt h h' s x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.scomp_hasDerivWithinAt`：HasDerivAt.scomp_hasDerivWithinAt (hg
 : HasDerivAt g₁ g₁' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt 
(g₁ ∘ h) (h' • g₁') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivAt.scomp_hasDerivWithinAt_of_eq (hg : HasDerivAt g₁ g₁' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (g₁ ∘ h) (h' • g₁') s x := by
  rw [hy] at hg; exact hg.scomp_hasDerivWithinAt x hh
/-
**derivWithin.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x)) (hh : Diffe
rentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') : derivWithin (g₁ ∘ h) s x = der
ivWithin h s x • derivWithin g₁ t' (h x)
参数：hg : DifferentiableWithinAt 𝕜' g₁ t' (h x)；hh : DifferentiableWithinAt 𝕜 h s 
x；hs : MapsTo h s t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ t' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.scomp x hg.hasDerivWithinAt hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin.scomp_of_eq (hg : DifferentiableWithinAt 𝕜' g₁ t' y) (hh : Dif
ferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') (hy : y = h x) : derivWithin (
g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x)
参数：hg : DifferentiableWithinAt 𝕜' g₁ t' y；hh : DifferentiableWithinAt 𝕜 h s x；hs
 : MapsTo h s t'；hy : y = h x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin.scomp`：derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ 
t' (h x)) (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') : derivWith
in (g₁ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem derivWithin.scomp_of_eq (hg : DifferentiableWithinAt 𝕜' g₁ t' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t')
    (hy : y = h x) :
    derivWithin (g₁ ∘ h) s x = derivWithin h s x • derivWithin g₁ t' (h x) := by
  rw [hy] at hg; exact derivWithin.scomp x hg hh hs
/-
**deriv.scomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h
 x) : deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x)
参数：hg : DifferentiableAt 𝕜' g₁ (h x)；hh : DifferentiableAt 𝕜 h x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
  (HasDerivAt.scomp x hg.hasDerivAt hh.hasDerivAt).deriv
/-
**deriv.scomp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv.scomp_of_eq (hg : DifferentiableAt 𝕜' g₁ y) (hh : DifferentiableAt 𝕜
 h x) (hy : y = h x) : deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x)
参数：hg : DifferentiableAt 𝕜' g₁ y；hh : DifferentiableAt 𝕜 h x；hy : y = h x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv.scomp`：deriv.scomp (hg : DifferentiableAt 𝕜' g₁ (h x)) (hh : Diffe
rentiableAt 𝕜 h x) : deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem deriv.scomp_of_eq
    (hg : DifferentiableAt 𝕜' g₁ y) (hh : DifferentiableAt 𝕜 h x) (hy : y = h x) :
    deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) := by
  rw [hy] at hg; exact deriv.scomp x hg hh

/-! ### Derivative of the composition of a scalar and vector functions -/

/-
**HasDerivAtFilter.comp_hasFDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.comp_hasFDerivAtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {
L'' : Filter (E × E)} (hh₂ : HasDerivAtFilter h₂ h₂' L') (hf : HasFDerivAtFilter
 f f' L'') (hL : Tendsto (Prod.map f f) L'' L') : HasFDerivAtFilter (h₂ ∘ f) (h₂
' • f') L''
参数：E × E；hh₂ : HasDerivAtFilter h₂ h₂' L'；hf : HasFDerivAtFilter f f' L''；hL : T
endsto (Prod.map f f) L'' L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L

--- 原说明 ---
### Derivative of the composition of a scalar and vector functions
-/
theorem HasDerivAtFilter.comp_hasFDerivAtFilter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'}
    {L'' : Filter (E × E)} (hh₂ : HasDerivAtFilter h₂ h₂' L') (hf : HasFDerivAtFilter f f' L'')
    (hL : Tendsto (Prod.map f f) L'' L') :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') L'' := by
  convert! (hh₂.restrictScalars 𝕜).comp hf hL
  ext x
  simp [mul_comm]

@[deprecated HasDerivAtFilter.comp_hasFDerivAtFilter (since := "2026-02-17")]
/-
**HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜]
 𝕜'} (x) {L' : Filter 𝕜'} {L'' : Filter E} (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ
 pure y)) (hf : HasFDerivAtFilter f f' (L'' ×ˢ pure x)) (hL : Tendsto f L'' L') 
(hy : y = f x) : HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') (L'' ×ˢ pure x)
参数：x；hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y)；hf : HasFDerivAtFilter f f' (L
'' ×ˢ pure x)；hL : Tendsto f L'' L'；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq
    {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x) {L' : Filter 𝕜'} {L'' : Filter E}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y)) (hf : HasFDerivAtFilter f f' (L'' ×ˢ pure x))
    (hL : Tendsto f L'' L') (hy : y = f x) :
    HasFDerivAtFilter (h₂ ∘ f) (h₂' • f') (L'' ×ˢ pure x) :=
  hh₂.comp_hasFDerivAtFilter hf <| hL.prodMap <| by simp [hy]
/-
**HasStrictDerivAt.comp_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.comp_hasStrictFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (
x) (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) : HasStr
ictFDerivAt (h₂ ∘ f) (h₂' • f') x
参数：x；hh : HasStrictDerivAt h₂ h₂' (f x)；hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `ContinuousAt.prodMap`：ContinuousAt.prodMap {f : X -> Z} {g : Y -> W} {p 
: X × Y} (hf : ContinuousAt f p.fst) (hg : ContinuousAt g p.snd) : ContinuousAt 
(Prod.map …
· 使用定理 `HasStrictFDerivAt.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem HasStrictDerivAt.comp_hasStrictFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  HasDerivAtFilter.comp_hasFDerivAtFilter hh hf <| hf.continuousAt.prodMap hf.continuousAt
/-
**HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜]
 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' y) (hf : HasStrictFDerivAt f f' x) (hy : 
y = f x) : HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x
参数：x；hh : HasStrictDerivAt h₂ h₂' y；hf : HasStrictFDerivAt f f' x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasStrictDerivAt.comp_hasStrictFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasStrictDerivAt h₂ h₂' y) (hf : HasStrictFDerivAt f f' x) (hy : y = f x) :
    HasStrictFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasStrictFDerivAt x hf
/-
**HasDerivAt.comp_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : Has
DerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f'
) x
参数：x；hh : HasDerivAt h₂ h₂' (f x)；hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _
/-
**HasDerivAt.comp_hasFDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh
 : HasDerivAt h₂ h₂' y) (hf : HasFDerivAt f f' x) (hy : y = f x) : HasFDerivAt (
h₂ ∘ f) (h₂' • f') x
参数：x；hh : HasDerivAt h₂ h₂' y；hf : HasFDerivAt f f' x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivAt f f' x) (hy : y = f x) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  rw [hy] at hh; exact hh.comp_hasFDerivAt x hf
/-
**HasDerivAt.comp_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasFDerivWithinAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x)
 (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWit
hinAt (h₂ ∘ f) (h₂' • f') s x
参数：x；hh : HasDerivAt h₂ h₂' (f x)；hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousWithinAt.tendsto.prodMap <| tendsto_pure_pure _ _
/-
**HasDerivAt.comp_hasFDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {
s} (x) (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivWithinAt f f' s x) (hy : y = f 
x) : HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x
参数：x；hh : HasDerivAt h₂ h₂' y；hf : HasFDerivWithinAt f f' s x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
    (hh : HasDerivAt h₂ h₂' y) (hf : HasFDerivWithinAt f f' s x) (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf
/-
**HasDerivWithinAt.comp_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasFDerivWithinAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {
s t} (x) (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x
) (hst : MapsTo f s t) : HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x
参数：x；hh : HasDerivWithinAt h₂ h₂' t (f x)；hf : HasFDerivWithinAt f f' s x；hst : 
MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivWithinAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x :=
  hh.comp_hasFDerivAtFilter hf <| hf.continuousWithinAt.tendsto_nhdsWithin hst |>.prodMap <|
    tendsto_pure_pure _ _
/-
**HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜]
 𝕜'} {s t} (x) (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivWithinAt f f' s
 x) (hst : MapsTo f s t) (hy : y = f x) : HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') 
s x
参数：x；hh : HasDerivWithinAt h₂ h₂' t y；hf : HasFDerivWithinAt f f' s x；hst : Maps
To f s t；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivWithinAt.comp_hasFDerivWithinAt`：HasDerivWithinAt.comp_hasFDeriv
WithinAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s t} (x) (hh : HasDerivWithinAt h₂ h₂
' t (f x)) (hf : HasFDerivWit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivWithinAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t)
    (hy : y = f x) :
    HasFDerivWithinAt (h₂ ∘ f) (h₂' • f') s x := by
  rw [hy] at hh; exact hh.comp_hasFDerivWithinAt x hf hst
/-
**HasDerivWithinAt.comp_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasFDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x)
 (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivAt f f' x) (ht : forallᶠ 
x' in 𝓝 x, f x' in t) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x
参数：x；hh : HasDerivWithinAt h₂ h₂' t (f x)；hf : HasFDerivAt f f' x；ht : forallᶠ x
' in 𝓝 x, f x' in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasDerivAtFilter.comp_hasFDerivAtFilter`：HasDerivAtFilter.comp_hasFDeriv
AtFilter {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {L'' : Filter (E × E)} (hh₂ : HasDeriv
AtFilter h₂ h₂' L') (hf : Has…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `HasFDerivAt.continuousAt`：HasFDerivAt.continuousAt (h : HasFDerivAt f f'
 x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivWithinAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf : HasFDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) :
    HasFDerivAt (h₂ ∘ f) (h₂' • f') x :=
  hh.comp_hasFDerivAtFilter hf <| tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩ |>.prodMap <|
    tendsto_pure_pure _ _
/-
**HasDerivWithinAt.comp_hasFDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasFDerivAt_of_eq {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {
t} (x) (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivAt f f' x) (ht : forall
ᶠ x' in 𝓝 x, f x' in t) (hy : y = f x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x
参数：x；hh : HasDerivWithinAt h₂ h₂' t y；hf : HasFDerivAt f f' x；ht : forallᶠ x' in
 𝓝 x, f x' in t；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `HasDerivWithinAt.comp_hasFDerivAt`：HasDerivWithinAt.comp_hasFDerivAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {t} (x) (hh : HasDerivWithinAt h₂ h₂' t (f x)) (hf
 : HasFDerivAt f f' x) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasDerivWithinAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {t} (x)
    (hh : HasDerivWithinAt h₂ h₂' t y) (hf : HasFDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t)
    (hy : y = f x) : HasFDerivAt (h₂ ∘ f) (h₂' • f') x := by
  subst y; exact hh.comp_hasFDerivAt x hf ht

/-! ### Derivative of the composition of two scalar functions -/

/-
**HasDerivAtFilter.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' L') (hh : HasDerivAtF
ilter h h' L) (hL : Tendsto (Prod.map h h) L L') : HasDerivAtFilter (h₂ ∘ h) (h₂
' * h') L
参数：hh₂ : HasDerivAtFilter h₂ h₂' L'；hh : HasDerivAtFilter h h' L；hL : Tendsto (P
rod.map h h) L L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasDerivAtFilter.scomp`：HasDerivAtFilter.scomp (hg : HasDerivAtFilter g₁
 g₁' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : Has
DerivAtFilte…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
### Derivative of the composition of two scalar functions
-/
theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' L')
    (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') L := by
  rw [mul_comm]
  exact hh₂.scomp hh hL

@[deprecated HasDerivAtFilter.comp (since := "2026-07-17")]
/-
**HasDerivAtFilter.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.comp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'} (hh₂ : HasDeri
vAtFilter h₂ h₂' (L' ×ˢ pure y)) (hh : HasDerivAtFilter h h' (L ×ˢ pure x)) (hL 
: Tendsto h L L') (hy : y = h x) : HasDerivAtFilter (h₂ ∘ h) (h₂' * h') (L ×ˢ pu
re x)
参数：hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y)；hh : HasDerivAtFilter h h' (L ×ˢ
 pure x)；hL : Tendsto h L L'；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.comp`：HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ 
h₂' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : HasD
erivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasDerivAtFilter.comp_of_eq {L : Filter 𝕜} {L' : Filter 𝕜'}
    (hh₂ : HasDerivAtFilter h₂ h₂' (L' ×ˢ pure y))
    (hh : HasDerivAtFilter h h' (L ×ˢ pure x)) (hL : Tendsto h L L') (hy : y = h x) :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') (L ×ˢ pure x) :=
  hh₂.comp hh <| hL.prodMap <| by simp [hy]
/-
**HasDerivWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x)) (hh : HasDe
rivWithinAt h h' s x) (hst : MapsTo h s s') : HasDerivWithinAt (h₂ ∘ h) (h₂' * h
') s x
参数：hh₂ : HasDerivWithinAt h₂ h₂' s' (h x)；hh : HasDerivWithinAt h h' s x；hst : M
apsTo h s s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasDerivWithinAt.scomp`：HasDerivWithinAt.scomp (hg : HasDerivWithinAt g₁
 g₁' t' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s t') : HasDeriv
WithinAt (g₁…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [mul_comm]
  exact hh₂.scomp x hh hst
/-
**HasDerivWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_of_eq (hh₂ : HasDerivWithinAt h₂ h₂' s' y) (hh : Has
DerivWithinAt h h' s x) (hst : MapsTo h s s') (hy : y = h x) : HasDerivWithinAt 
(h₂ ∘ h) (h₂' * h') s x
参数：hh₂ : HasDerivWithinAt h₂ h₂' s' y；hh : HasDerivWithinAt h h' s x；hst : MapsT
o h s s'；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.comp`：HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ 
h₂' s' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') : HasDerivW
ithinAt (h₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivWithinAt.comp_of_eq (hh₂ : HasDerivWithinAt h₂ h₂' s' y)
    (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp x hh hst

/-- The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp`. -/
/-
**HasDerivAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
 HasDerivAt (h₂ ∘ h) (h₂' * h') x
参数：hh₂ : HasDerivAt h₂ h₂' (h x)；hh : HasDerivAt h h' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.comp`：HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ 
h₂' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : HasD
erivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))

--- 原说明 ---
The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for 
the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp`.
-/
theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  HasDerivAtFilter.comp hh₂ hh <| hh.continuousAt.tendsto.prodMap <| tendsto_pure_pure _ _

/-- The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp_of_eq`. -/
/-
**HasDerivAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_of_eq (hh₂ : HasDerivAt h₂ h₂' y) (hh : HasDerivAt h h' x)
 (hy : y = h x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
参数：hh₂ : HasDerivAt h₂ h₂' y；hh : HasDerivAt h h' x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The chain rule.

Note that the function `h₂` is a function on an algebra. If you are looking for 
the chain rule
with `h₂` taking values in a vector space, use `HasDerivAt.scomp_of_eq`.
-/
theorem HasDerivAt.comp_of_eq
    (hh₂ : HasDerivAt h₂ h₂' y) (hh : HasDerivAt h h' x) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh
/-
**HasStrictDerivAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStric
tDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x
参数：hh₂ : HasStrictDerivAt h₂ h₂' (h x)；hh : HasStrictDerivAt h h' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasStrictDerivAt.scomp`：HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁
 g₁' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (g₁ ∘ h) (h' • g₁'
) x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
/-
**HasStrictDerivAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.comp_of_eq (hh₂ : HasStrictDerivAt h₂ h₂' y) (hh : HasStr
ictDerivAt h h' x) (hy : y = h x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x
参数：hh₂ : HasStrictDerivAt h₂ h₂' y；hh : HasStrictDerivAt h h' x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasStrictDerivAt.comp_of_eq
    (hh₂ : HasStrictDerivAt h₂ h₂' y) (hh : HasStrictDerivAt h h' x) (hy : y = h x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [hy] at hh₂; exact hh₂.comp x hh
/-
**HasDerivAt.comp_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : Has
DerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x
参数：hh₂ : HasDerivAt h₂ h₂' (h x)；hh : HasDerivWithinAt h h' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.comp`：HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ 
h₂' s' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') : HasDerivW
ithinAt (h₂…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
    (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x :=
  hh₂.hasDerivWithinAt.comp x hh (mapsTo_univ _ _)
/-
**HasDerivAt.comp_hasDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y) (hh : H
asDerivWithinAt h h' s x) (hy : y = h x) : HasDerivWithinAt (h₂ ∘ h) (h₂' * h') 
s x
参数：hh₂ : HasDerivAt h₂ h₂' y；hh : HasDerivWithinAt h h' s x；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y)
    (hh : HasDerivWithinAt h h' s x) (hy : y = h x) :
    HasDerivWithinAt (h₂ ∘ h) (h₂' * h') s x := by
  rw [hy] at hh₂; exact hh₂.comp_hasDerivWithinAt x hh
/-
**HasDerivWithinAt.comp_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasDerivAt {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x
)) (hh : HasDerivAt h h' x) (ht : forallᶠ x' in 𝓝 x, h x' in t) : HasDerivAt (h₂
 ∘ h) (h₂' * h') x
参数：hh₂ : HasDerivWithinAt h₂ h₂' t (h x)；hh : HasDerivAt h h' x；ht : forallᶠ x' 
in 𝓝 x, h x' in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.comp`：HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ 
h₂' L') (hh : HasDerivAtFilter h h' L) (hL : Tendsto (Prod.map h h) L L') : HasD
erivAtFilte…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
-/
theorem HasDerivWithinAt.comp_hasDerivAt {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
    (hh : HasDerivAt h h' x) (ht : ∀ᶠ x' in 𝓝 x, h x' ∈ t) : HasDerivAt (h₂ ∘ h) (h₂' * h') x :=
  HasDerivAtFilter.comp hh₂ hh <| tendsto_nhdsWithin_iff.mpr ⟨hh.continuousAt, ht⟩ |>.prodMap <|
    tendsto_pure_pure _ _
/-
**HasDerivWithinAt.comp_hasDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.comp_hasDerivAt_of_eq {t} (hh₂ : HasDerivWithinAt h₂ h₂' 
t y) (hh : HasDerivAt h h' x) (ht : forallᶠ x' in 𝓝 x, h x' in t) (hy : y = h x)
 : HasDerivAt (h₂ ∘ h) (h₂' * h') x
参数：hh₂ : HasDerivWithinAt h₂ h₂' t y；hh : HasDerivAt h h' x；ht : forallᶠ x' in 𝓝
 x, h x' in t；hy : y = h x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.comp_hasDerivAt`：HasDerivWithinAt.comp_hasDerivAt {t} (
hh₂ : HasDerivWithinAt h₂ h₂' t (h x)) (hh : HasDerivAt h h' x) (ht : forallᶠ x'
 in 𝓝 x, h x' in t) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasDerivWithinAt.comp_hasDerivAt_of_eq {t} (hh₂ : HasDerivWithinAt h₂ h₂' t y)
    (hh : HasDerivAt h h' x) (ht : ∀ᶠ x' in 𝓝 x, h x' ∈ t) (hy : y = h x) :
    HasDerivAt (h₂ ∘ h) (h₂' * h') x := by
  subst y; exact hh₂.comp_hasDerivAt x hh ht
/-
**derivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x)) (hh : Diffe
rentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') : derivWithin (h₂ ∘ h) s x = der
ivWithin h₂ s' (h x) * derivWithin h s x
参数：hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x)；hh : DifferentiableWithinAt 𝕜 h s
 x；hs : MapsTo h s s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.comp`：HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ 
h₂' s' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') : HasDerivW
ithinAt (h₂…
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' (h x))
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hh₂.hasDerivWithinAt.comp x hh.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_comp_of_eq (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y) (hh : Dif
ferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') (hy : h x = y) : derivWithin (
h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x
参数：hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y；hh : DifferentiableWithinAt 𝕜 h s x；h
s : MapsTo h s s'；hy : h x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_comp`：derivWithin_comp (hh₂ : DifferentiableWithinAt 𝕜' h₂ s
' (h x)) (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s') : derivWithi
n (h₂ …
-/
theorem derivWithin_comp_of_eq (hh₂ : DifferentiableWithinAt 𝕜' h₂ s' y)
    (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s s')
    (hy : h x = y) :
    derivWithin (h₂ ∘ h) s x = derivWithin h₂ s' (h x) * derivWithin h s x := by
  subst hy; exact derivWithin_comp x hh₂ hh hs
/-
**deriv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h
 x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
参数：hh₂ : DifferentiableAt 𝕜' h₂ (h x)；hh : DifferentiableAt 𝕜 h x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : DifferentiableAt 𝕜 h x) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
  (hh₂.hasDerivAt.comp x hh.hasDerivAt).deriv
/-
**deriv_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_comp_of_eq (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜
 h x) (hy : h x = y) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
参数：hh₂ : DifferentiableAt 𝕜' h₂ y；hh : DifferentiableAt 𝕜 h x；hy : h x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_comp`：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : Differ
entiableAt 𝕜 h x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
-/
theorem deriv_comp_of_eq (hh₂ : DifferentiableAt 𝕜' h₂ y) (hh : DifferentiableAt 𝕜 h x)
    (hy : h x = y) :
    deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x := by
  subst hy; exact deriv_comp x hh₂ hh

protected nonrec theorem HasDerivAtFilter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : ℕ) :
    HasDerivAtFilter f^[n] (f' ^ n) L := by
  have := hf.hasFDerivAtFilter.iterate hL n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

protected nonrec theorem HasDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasDerivAt f^[n] (f' ^ n) x :=
  hf.iterate (by simpa [hx] using hf.continuousAt.tendsto.prodMap <| tendsto_pure_pure f x) _
/-
**HasDerivWithinAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (x : 𝕜) {s : Set 𝕜} {f :
 𝕜 → 𝕜} {f' : 𝕜},   HasDerivWithinAt f f' s x → f x = x → Set.MapsTo f s s → ∀ (
n : ℕ), HasDerivWithinAt f^[n] (f' ^ n) s x
参数：x : 𝕜；n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {x : E} {s :…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton_pow`：toSpanSingleton_pow [Topologica
lSpace R] [IsTopologicalRing R] (c : R) (n : Nat) : toSpanSingleton R c ^ n = to
SpanSingleton R (c ^ n)
-/
protected theorem HasDerivWithinAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜} (hf : HasDerivWithinAt f f' s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : HasDerivWithinAt f^[n] (f' ^ n) s x := by
  have := HasFDerivWithinAt.iterate hf hx hs n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this
/-
**HasStrictDerivAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictDerivAt`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (x : 𝕜) {f : 𝕜 → 𝕜} {f' 
: 𝕜},   HasStrictDerivAt f f' x → f x = x → ∀ (n : ℕ), HasStrictDerivAt f^[n] (f
' ^ n) x
参数：x : 𝕜；n : ℕ；f' ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasStrictFDerivAt.iterate`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {x : E} {f :…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton_pow`：toSpanSingleton_pow [Topologica
lSpace R] [IsTopologicalRing R] (c : R) (n : Nat) : toSpanSingleton R c ^ n = to
SpanSingleton R (c ^ n)
-/
protected theorem HasStrictDerivAt.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hx : f x = x) (n : ℕ) :
    HasStrictDerivAt f^[n] (f' ^ n) x := by
  have := hf.hasStrictFDerivAt.iterate hx n
  rwa [ContinuousLinearMap.toSpanSingleton_pow] at this

end Composition

section CompositionVector

/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open ContinuousLinearMap

variable {l : F → E} {l' : F →L[𝕜] E} {y : F}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
/-
**HasFDerivWithinAt.comp_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasDerivWithinAt {t : Set F} (hl : HasFDerivWithinA
t l l' t (f x)) (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) : HasDeriv
WithinAt (l ∘ f) (l' f') s x
参数：hl : HasFDerivWithinAt l l' t (f x)；hf : HasDerivWithinAt f f' s x；hst : Maps
To f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…

--- 原说明 ---
The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative with
in a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`.
-/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  simpa using (hl.comp x hf.hasFDerivWithinAt hst).hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
/-
**HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq {t : Set F} (hl : HasFDerivW
ithinAt l l' t y) (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : y 
= f x) : HasDerivWithinAt (l ∘ f) (l' f') s x
参数：hl : HasFDerivWithinAt l l' t y；hf : HasDerivWithinAt f f' s x；hst : MapsTo f
 s t；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative with
in a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`.
-/
theorem HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq {t : Set F}
    (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf hst
/-
**HasFDerivWithinAt.comp_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasDerivAt {t : Set F} (hl : HasFDerivWithinAt l l'
 t (f x)) (hf : HasDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t) : HasDeri
vAt (l ∘ f) (l' f') x
参数：hl : HasFDerivWithinAt l l' t (f x)；hf : HasDerivAt f f' x；ht : forallᶠ x' in
 𝓝 x, f x' in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivWithinAt.comp_hasFDerivAt`：HasFDerivWithinAt.comp_hasFDerivAt {
g : F -> G} {g' : F ->L[𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) 
(hf : HasFDerivAt f f' x…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasFDerivWithinAt.comp_hasDerivAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
    (hf : HasDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) : HasDerivAt (l ∘ f) (l' f') x := by
  simpa using (hl.comp_hasFDerivAt x hf.hasFDerivAt ht).hasDerivAt
/-
**HasFDerivWithinAt.comp_hasDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.comp_hasDerivAt_of_eq {t : Set F} (hl : HasFDerivWithinA
t l l' t y) (hf : HasDerivAt f f' x) (ht : forallᶠ x' in 𝓝 x, f x' in t) (hy : y
 = f x) : HasDerivAt (l ∘ f) (l' f') x
参数：hl : HasFDerivWithinAt l l' t y；hf : HasDerivAt f f' x；ht : forallᶠ x' in 𝓝 x
, f x' in t；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.comp_hasDerivAt`：HasFDerivWithinAt.comp_hasDerivAt {t 
: Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivAt f f' x) (ht : fo
rallᶠ x' in 𝓝 x, f x' i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasFDerivWithinAt.comp_hasDerivAt_of_eq {t : Set F} (hl : HasFDerivWithinAt l l' t y)
    (hf : HasDerivAt f f' x) (ht : ∀ᶠ x' in 𝓝 x, f x' ∈ t) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  subst y; exact hl.comp_hasDerivAt x hf ht
/-
**HasFDerivAt.comp_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x)) (hf : HasD
erivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x
参数：hl : HasFDerivAt l l' (f x)；hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem HasFDerivAt.comp_hasDerivWithinAt (hl : HasFDerivAt l l' (f x))
    (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (l ∘ f) (l' f') s x :=
  hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf (mapsTo_univ _ _)
/-
**HasFDerivAt.comp_hasDerivWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_hasDerivWithinAt_of_eq (hl : HasFDerivAt l l' y) (hf : Ha
sDerivWithinAt f f' s x) (hy : y = f x) : HasDerivWithinAt (l ∘ f) (l' f') s x
参数：hl : HasFDerivAt l l' y；hf : HasDerivWithinAt f f' s x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasFDerivAt.comp_hasDerivWithinAt_of_eq (hl : HasFDerivAt l l' y)
    (hf : HasDerivWithinAt f f' s x) (hy : y = f x) :
    HasDerivWithinAt (l ∘ f) (l' f') s x := by
  rw [hy] at hl; exact hl.comp_hasDerivWithinAt x hf

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
/-
**HasFDerivAt.comp_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt
 f f' x) : HasDerivAt (l ∘ f) (l' f') x
参数：hl : HasFDerivAt l l' (f x)；hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equa
l to the
Fréchet derivative of `l` applied to the derivative of `f`.
-/
theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x :=
  hasDerivWithinAt_univ.mp <| hl.comp_hasDerivWithinAt x hf.hasDerivWithinAt

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
/-
**HasFDerivAt.comp_hasDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.comp_hasDerivAt_of_eq (hl : HasFDerivAt l l' y) (hf : HasDeriv
At f f' x) (hy : y = f x) : HasDerivAt (l ∘ f) (l' f') x
参数：hl : HasFDerivAt l l' y；hf : HasDerivAt f f' x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equa
l to the
Fréchet derivative of `l` applied to the derivative of `f`.
-/
theorem HasFDerivAt.comp_hasDerivAt_of_eq
    (hl : HasFDerivAt l l' y) (hf : HasDerivAt f f' x) (hy : y = f x) :
    HasDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasDerivAt x hf
/-
**HasStrictFDerivAt.comp_hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x)
) (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x
参数：hl : HasStrictFDerivAt l l' (f x)；hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictFDerivAt.comp_hasStrictDerivAt (hl : HasStrictFDerivAt l l' (f x))
    (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (l ∘ f) (l' f') x := by
  simpa using! (hl.comp x hf.hasStrictFDerivAt).hasStrictDerivAt
/-
**HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq (hl : HasStrictFDerivAt l l'
 y) (hf : HasStrictDerivAt f f' x) (hy : y = f x) : HasStrictDerivAt (l ∘ f) (l'
 f') x
参数：hl : HasStrictFDerivAt l l' y；hf : HasStrictDerivAt f f' x；hy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.comp_hasStrictDerivAt`：HasStrictFDerivAt.comp_hasStric
tDerivAt (hl : HasStrictFDerivAt l l' (f x)) (hf : HasStrictDerivAt f f' x) : Ha
sStrictDerivAt (l ∘ f) (l' f'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasStrictFDerivAt.comp_hasStrictDerivAt_of_eq (hl : HasStrictFDerivAt l l' y)
    (hf : HasStrictDerivAt f f' x) (hy : y = f x) :
    HasStrictDerivAt (l ∘ f) (l' f') x := by
  rw [hy] at hl; exact hl.comp_hasStrictDerivAt x hf
/-
**fderivWithin_comp_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l
 t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) : derivWithi
n (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F -> E) (derivWithin f s x)
参数：hl : DifferentiableWithinAt 𝕜 l t (f x)；hf : DifferentiableWithinAt 𝕜 f s x；h
s : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_comp_derivWithin {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hl.hasFDerivWithinAt.comp_hasDerivWithinAt x hf.hasDerivWithinAt hs).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**fderivWithin_comp_derivWithin_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_derivWithin_of_eq {t : Set F} (hl : DifferentiableWithin
At 𝕜 l t y) (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hy : y = 
f x) : derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F -> E) (derivWithi
n f s x)
参数：hl : DifferentiableWithinAt 𝕜 l t y；hf : DifferentiableWithinAt 𝕜 f s x；hs : 
MapsTo f s t；hy : y = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_comp_derivWithin`：fderivWithin_comp_derivWithin {t : Set F}
 (hl : DifferentiableWithinAt 𝕜 l t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
 (hs : MapsTo f s t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fderivWithin_comp_derivWithin_of_eq {t : Set F} (hl : DifferentiableWithinAt 𝕜 l t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : MapsTo f s t) (hy : y = f x) :
    derivWithin (l ∘ f) s x = (fderivWithin 𝕜 l t (f x) : F → E) (derivWithin f s x) := by
  rw [hy] at hl; exact fderivWithin_comp_derivWithin x hl hf hs
/-
**fderiv_comp_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt
 𝕜 f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (deriv f x)
参数：hl : DifferentiableAt 𝕜 l (f x)；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (hf : DifferentiableAt 𝕜 f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
  (hl.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv
/-
**fderiv_comp_deriv_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_deriv_of_eq (hl : DifferentiableAt 𝕜 l y) (hf : Differentiable
At 𝕜 f x) (hy : y = f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (deriv 
f x)
参数：hl : DifferentiableAt 𝕜 l y；hf : DifferentiableAt 𝕜 f x；hy : y = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_comp_deriv`：fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (
hf : DifferentiableAt 𝕜 f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (de
riv f x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fderiv_comp_deriv_of_eq (hl : DifferentiableAt 𝕜 l y) (hf : DifferentiableAt 𝕜 f x)
    (hy : y = f x) :
    deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) := by
  rw [hy] at hl; exact fderiv_comp_deriv x hl hf

end CompositionVector

