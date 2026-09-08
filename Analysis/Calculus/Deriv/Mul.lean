/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivative of `f x * g x`

In this file we prove formulas for `(f x * g x)'` and `(f x • g x)'`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, multiplication
-/

public section

universe u v w

noncomputable section

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

/-! ### Derivative of bilinear maps -/

namespace ContinuousLinearMap

variable {B : E →L[𝕜] F →L[𝕜] G} {u : 𝕜 → E} {v : 𝕜 → F} {u' : E} {v' : F}

/-
**ContinuousLinearMap.hasDerivWithinAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：hasDerivWithinAt_of_bilinear (hu : HasDerivWithinAt u u' s x) (hv : HasDer
ivWithinAt v v' s x) : HasDerivWithinAt (fun x => B (u x) (v x)) (B (u x) v' + B
 u' (v x)) s x
参数：hu : HasDerivWithinAt u u' s x；hv : HasDerivWithinAt v v' s x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.precompR_apply`：∀ {𝕜 : Type u_1} {E : Type u_4} (Eₗ 
: Type u_5) {Fₗ : Type u_7} {Gₗ : Type u_9} [inst : SeminormedAddCommGroup E]   
[inst_1 : SeminormedAddC…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `ContinuousLinearMap.hasFDerivWithinAt_of_bilinear`：ContinuousLinearMap.h
asFDerivWithinAt_of_bilinear {f : G' -> E} {g : G' -> F} {f' : G' ->L[𝕜] E} {g' 
: G' ->L[𝕜] F} {x : G'} {s : Set G'} (h…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem hasDerivWithinAt_of_bilinear
    (hu : HasDerivWithinAt u u' s x) (hv : HasDerivWithinAt v v' s x) :
    HasDerivWithinAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) s x := by
  simpa using (B.hasFDerivWithinAt_of_bilinear
    hu.hasFDerivWithinAt hv.hasFDerivWithinAt).hasDerivWithinAt
/-
**ContinuousLinearMap.hasDerivAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：hasDerivAt_of_bilinear (hu : x in tsupport v -> HasDerivAt u u' x) (hv : x
 in tsupport u -> HasDerivAt v v' x) : HasDerivAt (fun x => B (u x) (v x)) (B (u
 x) v' + B u' (v x)) x
参数：hu : x in tsupport v -> HasDerivAt u u' x；hv : x in tsupport u -> HasDerivAt 
v v' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.precompR_apply`：∀ {𝕜 : Type u_1} {E : Type u_4} (Eₗ 
: Type u_5) {Fₗ : Type u_7} {Gₗ : Type u_9} [inst : SeminormedAddCommGroup E]   
[inst_1 : SeminormedAddC…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `ContinuousLinearMap.hasFDerivAt_of_bilinear`：ContinuousLinearMap.hasFDer
ivAt_of_bilinear {f : G' -> E} {g : G' -> F} {f' : G' ->L[𝕜] E} {g' : G' ->L[𝕜] 
F} {x : G'} (hf : HasFDerivAt f f…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivAt.unique`：HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : Has
DerivAt f f₁' x) : f₀' = f₁'
· 使用定理 `HasDerivAt.of_notMem_tsupport`：HasDerivAt.of_notMem_tsupport (h : x ∉ ts
upport f) : HasDerivAt f 0 x
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
（共 33 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_of_bilinear (hu : x ∈ tsupport v → HasDerivAt u u' x)
    (hv : x ∈ tsupport u → HasDerivAt v v' x) :
    HasDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  by_cases hxu : x ∈ tsupport u
  · by_cases hxv : x ∈ tsupport v
    · simpa using (B.hasFDerivAt_of_bilinear (hu hxv).hasFDerivAt (hv hxu).hasFDerivAt).hasDerivAt
    · have hx : x ∉ tsupport fun x ↦ B (u x) (v x) :=
        mt (closure_mono (fun x ↦ mt fun h ↦ by simp [h]) ·) hxv
      convert! HasDerivAt.of_notMem_tsupport hx
      simp [(hv hxu).unique <| .of_notMem_tsupport hxv, image_eq_zero_of_notMem_tsupport hxv]
  · have hx : x ∉ tsupport fun x ↦ B (u x) (v x) :=
      mt (closure_mono (fun x ↦ mt fun h ↦ by simp [h]) ·) hxu
    convert! HasDerivAt.of_notMem_tsupport hx
    by_cases hxv : x ∈ tsupport v
    · simp [image_eq_zero_of_notMem_tsupport hxu, (hu hxv).unique <| .of_notMem_tsupport hxu]
    · simp [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hxv]
/-
**ContinuousLinearMap.hasStrictDerivAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：hasStrictDerivAt_of_bilinear (hu : HasStrictDerivAt u u' x) (hv : HasStric
tDerivAt v v' x) : HasStrictDerivAt (fun x => B (u x) (v x)) (B (u x) v' + B u' 
(v x)) x
参数：hu : HasStrictDerivAt u u' x；hv : HasStrictDerivAt v v' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.precompR_apply`：∀ {𝕜 : Type u_1} {E : Type u_4} (Eₗ 
: Type u_5) {Fₗ : Type u_7} {Gₗ : Type u_9} [inst : SeminormedAddCommGroup E]   
[inst_1 : SeminormedAddC…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt_of_bilinear`：ContinuousLinearMap.h
asStrictFDerivAt_of_bilinear {f : G' -> E} {g : G' -> F} {f' : G' ->L[𝕜] E} {g' 
: G' ->L[𝕜] F} {x : G'} (hf : HasStrict…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem hasStrictDerivAt_of_bilinear (hu : HasStrictDerivAt u u' x) (hv : HasStrictDerivAt v v' x) :
    HasStrictDerivAt (fun x ↦ B (u x) (v x)) (B (u x) v' + B u' (v x)) x := by
  simpa using
    (B.hasStrictFDerivAt_of_bilinear hu.hasStrictFDerivAt hv.hasStrictFDerivAt).hasStrictDerivAt
/-
**ContinuousLinearMap.derivWithin_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：derivWithin_of_bilinear (hu : DifferentiableWithinAt 𝕜 u s x) (hv : Differ
entiableWithinAt 𝕜 v s x) : derivWithin (fun y => B (u y) (v y)) s x = B (u x) (
derivWithin v s x) + B (derivWithin u s x) (v x)
参数：hu : DifferentiableWithinAt 𝕜 u s x；hv : DifferentiableWithinAt 𝕜 v s x。
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
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `ContinuousLinearMap.hasDerivWithinAt_of_bilinear`：hasDerivWithinAt_of_bi
linear (hu : HasDerivWithinAt u u' s x) (hv : HasDerivWithinAt v v' s x) : HasDe
rivWithinAt (fun x => B (u x) (v x)) (…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_of_bilinear
    (hu : DifferentiableWithinAt 𝕜 u s x) (hv : DifferentiableWithinAt 𝕜 v s x) :
    derivWithin (fun y => B (u y) (v y)) s x =
      B (u x) (derivWithin v s x) + B (derivWithin u s x) (v x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (B.hasDerivWithinAt_of_bilinear hu.hasDerivWithinAt hv.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**ContinuousLinearMap.deriv_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：deriv_of_bilinear (hu : x in tsupport v -> DifferentiableAt 𝕜 u x) (hv : x
 in tsupport u -> DifferentiableAt 𝕜 v x) : deriv (fun y => B (u y) (v y)) x = B
 (u x) (deriv v x) + B (deriv u x) (v x)
参数：hu : x in tsupport v -> DifferentiableAt 𝕜 u x；hv : x in tsupport u -> Differ
entiableAt 𝕜 v x。
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
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `ContinuousLinearMap.hasDerivAt_of_bilinear`：hasDerivAt_of_bilinear (hu :
 x in tsupport v -> HasDerivAt u u' x) (hv : x in tsupport u -> HasDerivAt v v' 
x) : HasDerivAt (fun x => B (u x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_of_bilinear (hu : x ∈ tsupport v → DifferentiableAt 𝕜 u x)
    (hv : x ∈ tsupport u → DifferentiableAt 𝕜 v x) :
    deriv (fun y => B (u y) (v y)) x = B (u x) (deriv v x) + B (deriv u x) (v x) :=
  (B.hasDerivAt_of_bilinear (fun hx ↦ (hu hx).hasDerivAt) fun hx ↦ (hv hx).hasDerivAt).deriv

end ContinuousLinearMap

section SMul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

@[to_fun]
/-
**HasDerivWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithi
nAt f f' s x) : HasDerivWithinAt (c • f) (c x • f' + c' • f x) s x
参数：hc : HasDerivWithinAt c c' s x；hf : HasDerivWithinAt f f' s x。
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
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
-/
theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (c • f) (c x • f' + c' • f x) s x := by
  simpa using (HasFDerivWithinAt.smul hc hf).hasDerivWithinAt

@[to_fun]
/-
**HasDerivAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) : HasDer
ivAt (c • f) (c x • f' + c' • f x) x
参数：hc : HasDerivAt c c' x；hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.smul`：HasDerivWithinAt.smul (hc : HasDerivWithinAt c c'
 s x) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (c • f) (c x • f' + c'
 • f x) s x
-/
theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (c • f) (c x • f' + c' • f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul hf

@[to_fun]
/-
**HasStrictDerivAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivA
t f f' x) : HasStrictDerivAt (c • f) (c x • f' + c' • f x) x
参数：hc : HasStrictDerivAt c c' x；hf : HasStrictDerivAt f f' x。
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
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.smul`：HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c
 c' x) (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt (c • f) (c x • f' + c
'.smulRight …
-/
theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (c • f) (c x • f' + c' • f x) x := by
  simpa using (HasStrictFDerivAt.smul hc hf).hasStrictDerivAt
/-
**derivWithin_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_smul (hc : DifferentiableWithinAt 𝕜 c s x) (hf : Different
iableWithinAt 𝕜 f s x) : derivWithin (fun y => c y • f y) s x = c x • derivWithi
n f s x + derivWithin c s x • f x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.smul`：HasDerivWithinAt.smul (hc : HasDerivWithinAt c c'
 s x) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (c • f) (c x • f' + c'
 • f x) s x
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c y • f y) s x = c x • derivWithin f s x + derivWithin c s x • f x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul hf.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_smul (hc : DifferentiableWithinAt 𝕜 c s x) (hf : Differentiabl
eWithinAt 𝕜 f s x) : derivWithin (c • f) s x = c x • derivWithin f s x + derivWi
thin c s x • f x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_smul`：derivWithin_fun_smul (hc : DifferentiableWithinAt 
𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : derivWithin (fun y => c y • f y
) s x = c …
-/
theorem derivWithin_smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (c • f) s x = c x • derivWithin f s x + derivWithin c s x • f x :=
  derivWithin_fun_smul hc hf
/-
**deriv_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
 : deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x
参数：hc : DifferentiableAt 𝕜 c x；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.smul`：HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDeriv
At f f' x) : HasDerivAt (c • f) (c x • f' + c' • f x) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv
/-
**deriv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) : d
eriv (c • f) x = c x • deriv f x + deriv c x • f x
参数：hc : DifferentiableAt 𝕜 c x；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.smul`：HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDeriv
At f f' x) : HasDerivAt (c • f) (c x • f' + c' • f x) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    deriv (c • f) x = c x • deriv f x + deriv c x • f x :=
  (hc.hasDerivAt.smul hf.hasDerivAt).deriv
/-
**HasStrictDerivAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) : HasSt
rictDerivAt (fun y => c y • f) (c' • f) x
参数：hc : HasStrictDerivAt c c' x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.smul`：HasStrictDerivAt.smul (hc : HasStrictDerivAt c c'
 x) (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (c • f) (c x • f' + c' • f
 x) x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
    HasStrictDerivAt (fun y => c y • f) (c' • f) x := by
  have := hc.smul (hasStrictDerivAt_const x f)
  rwa [smul_zero, zero_add] at this
/-
**HasDerivWithinAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) : Has
DerivWithinAt (fun y => c y • f) (c' • f) s x
参数：hc : HasDerivWithinAt c c' s x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.smul`：HasDerivWithinAt.smul (hc : HasDerivWithinAt c c'
 s x) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (c • f) (c x • f' + c'
 • f x) s x
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
    HasDerivWithinAt (fun y => c y • f) (c' • f) s x := by
  have := hc.smul (hasDerivWithinAt_const x s f)
  rwa [smul_zero, zero_add] at this
/-
**HasDerivAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) : HasDerivAt (fun y
 => c y • f) (c' • f) x
参数：hc : HasDerivAt c c' x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.smul_const`：HasDerivWithinAt.smul_const (hc : HasDerivW
ithinAt c c' s x) (f : F) : HasDerivWithinAt (fun y => c y • f) (c' • f) s x
-/
theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
    HasDerivAt (fun y => c y • f) (c' • f) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.smul_const f

-- TODO: Version of this without differentiability assumptions when `c` takes values in a
-- division ring (seems non-trivial)
/-
**derivWithin_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) : der
ivWithin (fun y => c y • f) s x = derivWithin c s x • f
参数：hc : DifferentiableWithinAt 𝕜 c s x；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.smul_const`：HasDerivWithinAt.smul_const (hc : HasDerivW
ithinAt c c' s x) (f : F) : HasDerivWithinAt (fun y => c y • f) (c' • f) s x
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
theorem derivWithin_smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    derivWithin (fun y => c y • f) s x = derivWithin c s x • f := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.smul_const f).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**deriv_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) : deriv (fun y => c
 y • f) x = deriv c x • f
参数：hc : DifferentiableAt 𝕜 c x；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.smul_const`：HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f
 : F) : HasDerivAt (fun y => c y • f) (c' • f) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    deriv (fun y => c y • f) x = deriv c x • f :=
  (hc.hasDerivAt.smul_const f).deriv

end SMul

section ConstSMul

variable
  {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- TODO: all results involving `𝕝` would actually work for a `GroupWithZero` if we had a
  -- `DistribMulActionWithZero` typeclass
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]

@[to_fun]
/-
**HasStrictDerivAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) : HasSt
rictDerivAt (c • f) (c • f') x
参数：c : R；hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.const_smul`：HasStrictFDerivAt.const_smul (h : HasStric
tFDerivAt f f' x) (c : R) : HasStrictFDerivAt (c • f) (c • f') x
-/
theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (c • f) (c • f') x := by
  simpa using (HasStrictFDerivAt.const_smul hf c).hasStrictDerivAt

@[to_fun]
/-
**HasDerivAtFilter.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' L) : HasDe
rivAtFilter (c • f) (c • f') L
参数：c : R；hf : HasDerivAtFilter f f' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAtFilter.hasDerivAtFilter`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivAtFilter.const_smul`：HasFDerivAtFilter.const_smul (h : HasFDeri
vAtFilter f f' L) (c : R) : HasFDerivAtFilter (c • f) (c • f') L
-/
theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (c • f) (c • f') L := by
  simpa using (HasFDerivAtFilter.const_smul hf c).hasDerivAtFilter

@[to_fun]
/-
**HasDerivWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) : Has
DerivWithinAt (c • f) (c • f') s x
参数：c : R；hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.const_smul`：HasDerivAtFilter.const_smul (c : R) (hf : H
asDerivAtFilter f f' L) : HasDerivAtFilter (c • f) (c • f') L
-/
theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (c • f) (c • f') s x :=
  HasDerivAtFilter.const_smul c hf

@[to_fun]
/-
**HasDerivAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) : HasDerivAt (c • f
) (c • f') x
参数：c : R；hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.const_smul`：HasDerivAtFilter.const_smul (c : R) (hf : H
asDerivAtFilter f f' L) : HasDerivAtFilter (c • f) (c • f') L
-/
theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
    HasDerivAt (c • f) (c • f') x :=
  HasDerivAtFilter.const_smul c hf
/-
**derivWithin_fun_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
 derivWithin (fun y => c • f y) s x = c • derivWithin f s x
参数：c : R；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.const_smul`：HasDerivWithinAt.const_smul (c : R) (hf : H
asDerivWithinAt f f' s x) : HasDerivWithinAt (c • f) (c • f') s x
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (fun y => c • f y) s x = c • derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hf.hasDerivWithinAt.const_smul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) : der
ivWithin (c • f) s x = c • derivWithin f s x
参数：c : R；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_const_smul`：derivWithin_fun_const_smul (c : R) (hf : Dif
ferentiableWithinAt 𝕜 f s x) : derivWithin (fun y => c • f y) s x = c • derivWit
hin f s x
-/
theorem derivWithin_const_smul (c : R) (hf : DifferentiableWithinAt 𝕜 f s x) :
    derivWithin (c • f) s x = c • derivWithin f s x :=
  derivWithin_fun_const_smul c hf

/-- A variant of `derivWithin_fun_const_smul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**derivWithin_fun_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : derivWithin (fun y
 => c • f y) s x = c • derivWithin f s x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `fderivWithin_const_smul_field`：fderivWithin_const_smul_field (c : R) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f
 s x
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
A variant of `derivWithin_fun_const_smul` without differentiability assumption w
hen the scalar
multiplication is by division ring elements.
-/
lemma derivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    derivWithin (fun y ↦ c • f y) s x = c • derivWithin f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · simp [← fderivWithin_derivWithin, ← Pi.smul_def, fderivWithin_const_smul_field c hsx]
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-01-11")] alias derivWithin_fun_const_smul' :=
  derivWithin_fun_const_smul_field

/-- A variant of `derivWithin_const_smul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**derivWithin_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : derivWithin (c • f) s 
x = c • derivWithin f s x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `derivWithin_fun_const_smul_field`：derivWithin_fun_const_smul_field (c : 
𝕝) (f : 𝕜 -> F) : derivWithin (fun y => c • f y) s x = c • derivWithin f s x

--- 原说明 ---
A variant of `derivWithin_const_smul` without differentiability assumption when 
the scalar
multiplication is by division ring elements.
-/
lemma derivWithin_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    derivWithin (c • f) s x = c • derivWithin f s x :=
  derivWithin_fun_const_smul_field c f

@[deprecated (since := "2026-01-11")] alias derivWithin_const_smul' :=
  derivWithin_const_smul_field
/-
**deriv_fun_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) : deriv (fun y 
=> c • f y) x = c • deriv f x
参数：c : R；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.const_smul`：HasDerivAt.const_smul (c : R) (hf : HasDerivAt f 
f' x) : HasDerivAt (c • f) (c • f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (fun y => c • f y) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv
/-
**deriv_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) : deriv (c • f) x =
 c • deriv f x
参数：c : R；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.const_smul`：HasDerivAt.const_smul (c : R) (hf : HasDerivAt f 
f' x) : HasDerivAt (c • f) (c • f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_const_smul (c : R) (hf : DifferentiableAt 𝕜 f x) :
    deriv (c • f) x = c • deriv f x :=
  (hf.hasDerivAt.const_smul c).deriv

/-- A variant of `deriv_fun_const_smul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**deriv_fun_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : deriv (fun y => c • f y)
 x = c • deriv f x
参数：c : 𝕝；f : 𝕜 -> F。
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
· 使用引理 `derivWithin_fun_const_smul_field`：derivWithin_fun_const_smul_field (c : 
𝕝) (f : 𝕜 -> F) : derivWithin (fun y => c • f y) s x = c • derivWithin f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `deriv_fun_const_smul` without differentiability assumption when th
e scalar
multiplication is by division ring elements.
-/
lemma deriv_fun_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    deriv (fun y ↦ c • f y) x = c • deriv f x := by
  simp only [← derivWithin_univ, derivWithin_fun_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_fun_const_smul' := deriv_fun_const_smul_field

/-- A variant of `deriv_const_smul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**deriv_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : deriv (c • f) x = c • deriv 
f x
参数：c : 𝕝；f : 𝕜 -> F。
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
· 使用引理 `derivWithin_const_smul_field`：derivWithin_const_smul_field (c : 𝕝) (f : 
𝕜 -> F) : derivWithin (c • f) s x = c • derivWithin f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `deriv_const_smul` without differentiability assumption when the sc
alar
multiplication is by division ring elements.
-/
lemma deriv_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    deriv (c • f) x = c • deriv f x := by
  simp only [← derivWithin_univ, derivWithin_const_smul_field]

@[deprecated (since := "2026-01-11")] alias deriv_const_smul' := deriv_const_smul_field

end ConstSMul

section Mul

/-! ### Derivative of the multiplication of two functions -/


variable {𝕜' 𝔸 : Type*} [NormedDivisionRing 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜']
  [NormedAlgebra 𝕜 𝔸] {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

@[to_fun]
/-
**HasDerivWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithin
At d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x * d') s x
参数：hc : HasDerivWithinAt c c' s x；hd : HasDerivWithinAt d d' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
-/
theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (c * d) (c' * d x + c x * d') s x := by
  simpa [add_comm] using (HasFDerivWithinAt.mul' hc hd).hasDerivWithinAt

@[to_fun]
/-
**HasDerivAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) : HasDeri
vAt (c * d) (c' * d x + c x * d') x
参数：hc : HasDerivAt c c' x；hd : HasDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.mul`：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x 
* d') s x
-/
theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (c * d) (c' * d x + c x * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact HasDerivWithinAt.mul hc hd

@[to_fun]
/-
**HasStrictDerivAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt
 d d' x) : HasStrictDerivAt (c * d) (c' * d x + c x * d') x
参数：hc : HasStrictDerivAt c c' x；hd : HasStrictDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.mul'`：HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFD
erivAt a a' x) (hb : HasStrictFDerivAt b b' x) : HasStrictFDerivAt (a * b) (a x 
• b' + a' <•…
-/
theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (c * d) (c' * d x + c x * d') x := by
  simpa [add_comm] using (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt
/-
**derivWithin_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_mul (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Differenti
ableWithinAt 𝕜 d s x) : derivWithin (fun y => c y * d y) s x = derivWithin c s x
 * d x + c x * derivWithin d s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.mul`：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x 
* d') s x
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_mul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c y * d y) s x = derivWithin c s x * d x + c x * derivWithin d s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_mul (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Differentiable
WithinAt 𝕜 d s x) : derivWithin (c * d) s x = derivWithin c s x * d x + c x * de
rivWithin d s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_mul`：derivWithin_fun_mul (hc : DifferentiableWithinAt 𝕜 
c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : derivWithin (fun y => c y * d y) 
s x = der…
-/
theorem derivWithin_mul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (c * d) s x = derivWithin c s x * d x + c x * derivWithin d s x :=
  derivWithin_fun_mul hc hd

@[simp]
/-
**deriv_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) 
: deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv

@[simp]
/-
**deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) : de
riv (c * d) x = deriv c x * d x + c x * deriv d x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (c * d) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv
/-
**HasDerivWithinAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) : HasD
erivWithinAt (fun y => c y * d) (c' * d) s x
参数：hc : HasDerivWithinAt c c' s x；d : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HasDerivWithinAt.mul`：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x 
* d') s x
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
    HasDerivWithinAt (fun y => c y * d) (c' * d) s x := by
  convert! hc.mul (hasDerivWithinAt_const x s d) using 1
  rw [mul_zero, add_zero]
/-
**HasDerivAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) : HasDerivAt (fun y 
=> c y * d) (c' * d) x
参数：hc : HasDerivAt c c' x；d : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.mul_const`：HasDerivWithinAt.mul_const (hc : HasDerivWit
hinAt c c' s x) (d : 𝔸) : HasDerivWithinAt (fun y => c y * d) (c' * d) s x
-/
theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
    HasDerivAt (fun y => c y * d) (c' * d) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.mul_const d
/-
**hasDerivAt_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x
参数：c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasDerivAt.mul_const`：HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d :
 𝔸) : HasDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
-/
theorem hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x => x * c) c x := by
  simpa only [one_mul] using (hasDerivAt_id' x).mul_const c
/-
**HasStrictDerivAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) : HasStr
ictDerivAt (fun y => c y * d) (c' * d) x
参数：hc : HasStrictDerivAt c c' x；d : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HasStrictDerivAt.mul`：HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x
) (hd : HasStrictDerivAt d d' x) : HasStrictDerivAt (c * d) (c' * d x + c x * d'
) x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
    HasStrictDerivAt (fun y => c y * d) (c' * d) x := by
  convert! hc.mul (hasStrictDerivAt_const x d) using 1
  rw [mul_zero, add_zero]
/-
**derivWithin_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_mul_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) : deri
vWithin (fun y => c y * d) s x = derivWithin c s x * d
参数：hc : DifferentiableWithinAt 𝕜 c s x；d : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.mul_const`：HasDerivWithinAt.mul_const (hc : HasDerivWit
hinAt c c' s x) (d : 𝔸) : HasDerivWithinAt (fun y => c y * d) (c' * d) s x
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_mul_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = derivWithin c s x * d := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.mul_const d).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_mul_const_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_mul_const_field (u : 𝕜') : derivWithin (fun y => v y * u) s x 
= derivWithin v s x * u
参数：u : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_mul_const`：derivWithin_mul_const (hc : DifferentiableWithinA
t 𝕜 c s x) (d : 𝔸) : derivWithin (fun y => c y * d) s x = derivWithin c s x * d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `derivWithin_fun_const`：derivWithin_fun_const : derivWithin (fun _ => c) 
s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `DifferentiableWithinAt.mul_const`：DifferentiableWithinAt.mul_const (ha :
 DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) : DifferentiableWithinAt 𝕜 (fun y => a 
y * b) s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma derivWithin_mul_const_field (u : 𝕜') :
    derivWithin (fun y => v y * u) s x = derivWithin v s x * u := by
  by_cases hv : DifferentiableWithinAt 𝕜 v s x
  · rw [derivWithin_mul_const hv u]
  by_cases hu : u = 0
  · simp [hu]
  rw [derivWithin_zero_of_not_differentiableWithinAt hv, zero_mul,
      derivWithin_zero_of_not_differentiableWithinAt]
  have : v = fun x ↦ (v x * u) * u⁻¹ := by ext; simp [hu]
  exact fun h_diff ↦ hv <| this ▸ h_diff.mul_const _
/-
**deriv_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) : deriv (fun y => c 
y * d) x = deriv c x * d
参数：hc : DifferentiableAt 𝕜 c x；d : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.mul_const`：HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d :
 𝔸) : HasDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
    deriv (fun y => c y * d) x = deriv c x * d :=
  (hc.hasDerivAt.mul_const d).deriv
/-
**deriv_mul_const_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * 
v
参数：v : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_mul_const`：deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
 deriv (fun y => c y * d) x = deriv c x * d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `DifferentiableAt.mul_const`：DifferentiableAt.mul_const (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => a y * b) x
-/
theorem deriv_mul_const_field (v : 𝕜') : deriv (fun y => u y * v) x = deriv u x * v := by
  by_cases hu : DifferentiableAt 𝕜 u x
  · exact deriv_mul_const hu v
  · rw [deriv_zero_of_not_differentiableAt hu, zero_mul]
    rcases eq_or_ne v 0 with (rfl | hd)
    · simp only [mul_zero, deriv_const]
    · refine deriv_zero_of_not_differentiableAt (mt (fun H => ?_) hu)
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹

@[simp]
/-
**deriv_mul_const_field'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deri
v u x * v
参数：v : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_mul_const_field`：deriv_mul_const_field (v : 𝕜') : deriv (fun y => 
u y * v) x = deriv u x * v
-/
theorem deriv_mul_const_field' (v : 𝕜') : (deriv fun x => u x * v) = fun x => deriv u x * v :=
  funext fun _ => deriv_mul_const_field v
/-
**HasDerivWithinAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) : HasD
erivWithinAt (fun y => c * d y) (c * d') s x
参数：c : 𝔸；hd : HasDerivWithinAt d d' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasDerivWithinAt.mul`：HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (c * d) (c' * d x + c x 
* d') s x
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c * d y) (c * d') s x := by
  convert! (hasDerivWithinAt_const x s c).mul hd using 1
  rw [zero_mul, zero_add]
/-
**HasDerivAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) : HasDerivAt (fun y 
=> c * d y) (c * d') x
参数：c : 𝔸；hd : HasDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.const_mul`：HasDerivWithinAt.const_mul (c : 𝔸) (hd : Has
DerivWithinAt d d' s x) : HasDerivWithinAt (fun y => c * d y) (c * d') s x
-/
theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c * d y) (c * d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hd.const_mul c
/-
**hasDerivAt_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_const_mul (c : 𝕜) : HasDerivAt (fun y => c * y) c x
参数：c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
-/
theorem hasDerivAt_const_mul (c : 𝕜) : HasDerivAt (fun y => c * y) c x := by
  simpa only [mul_one] using (hasDerivAt_id' x).const_mul c
/-
**HasStrictDerivAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) : HasStr
ictDerivAt (fun y => c * d y) (c * d') x
参数：c : 𝔸；hd : HasStrictDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasStrictDerivAt.mul`：HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x
) (hd : HasStrictDerivAt d d' x) : HasStrictDerivAt (c * d) (c' * d x + c x * d'
) x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c * d y) (c * d') x := by
  convert! (hasStrictDerivAt_const _ _).mul hd using 1
  rw [zero_mul, zero_add]
/-
**derivWithin_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_mul (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x) : deri
vWithin (fun y => c * d y) s x = c * derivWithin d s x
参数：c : 𝔸；hd : DifferentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.const_mul`：HasDerivWithinAt.const_mul (c : 𝔸) (hd : Has
DerivWithinAt d d' s x) : HasDerivWithinAt (fun y => c * d y) (c * d') s x
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
theorem derivWithin_const_mul (c : 𝔸) (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => c * d y) s x = c * derivWithin d s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hd.hasDerivWithinAt.const_mul c).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

/-- A variant of `derivWithin_const_mul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**derivWithin_const_mul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_const_mul_field (u : 𝕜') : derivWithin (fun y => u * v y) s x 
= u * derivWithin v s x
参数：u : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `derivWithin_const_smul_field`：derivWithin_const_smul_field (c : 𝕝) (f : 
𝕜 -> F) : derivWithin (c • f) s x = c • derivWithin f s x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α

--- 原说明 ---
A variant of `derivWithin_const_mul` without differentiability assumption when t
he scalar
multiplication is by division ring elements.
-/
lemma derivWithin_const_mul_field (u : 𝕜') :
    derivWithin (fun y => u * v y) s x = u * derivWithin v s x := by
  apply derivWithin_const_smul_field (c := u)
/-
**deriv_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) : deriv (fun y => c 
* d y) x = c * deriv d x
参数：c : 𝔸；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => c * d y) x = c * deriv d x :=
  (hd.hasDerivAt.const_mul c).deriv

/-- A variant of `deriv_const_mul` without differentiability assumption when the scalar
multiplication is by division ring elements. -/
/-
**deriv_const_mul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v 
x
参数：u : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `derivWithin_const_mul_field`：derivWithin_const_mul_field (u : 𝕜') : deri
vWithin (fun y => u * v y) s x = u * derivWithin v s x

--- 原说明 ---
A variant of `deriv_const_mul` without differentiability assumption when the sca
lar
multiplication is by division ring elements.
-/
theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by
  simpa only [← derivWithin_univ] using derivWithin_const_mul_field u

@[simp]
/-
**deriv_const_mul_field'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * 
deriv v x
参数：u : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const_mul_field`：deriv_const_mul_field (u : 𝕜') : deriv (fun y => 
u * v y) x = u * deriv v x
-/
theorem deriv_const_mul_field' (u : 𝕜') : (deriv fun x => u * v x) = fun x => u * deriv v x :=
  funext fun _ => deriv_const_mul_field u
/-
**deriv_const_mul_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) x = c
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_mul`：deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x) :
 deriv (fun y => c * d y) x = c * deriv d x
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) x = c := by
  simp only [deriv_const_mul c differentiableAt_fun_id, deriv_id'', mul_one]

@[simp]
/-
**deriv_const_mul_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_mul_id' (c : 𝕜) : deriv (fun x => c * x) = fun _ => c
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_mul_id`：deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) 
x = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_mul_id' (c : 𝕜) : deriv (fun x => c * x) = fun _ => c :=
  funext fun _ => by simp only [deriv_const_mul_id]

end Mul

section Prod

section HasDeriv

variable {ι : Type*} [DecidableEq ι] {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → 𝕜 → 𝔸'} {f' : ι → 𝔸'}

/-
**HasDerivAt.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.fun_finsetProd (hf : forall i in u, HasDerivAt (f i) (f' i) x) 
: HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x
参数：hf : forall i in u, HasDerivAt (f i) (f' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.finsetProd`：HasFDerivAt.finsetProd [DecidableEq ι] {x : E} (
hg : forall i in u, HasFDerivAt (g i) (g' i) x) : HasFDerivAt (∏ i in u, g i ·) 
(∑ i in u, (…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.fun_finsetProd (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  simpa using (HasFDerivAt.finsetProd (hf · · |> hasFDerivAt)).hasDerivAt

@[deprecated (since := "2026-04-08")] alias HasDerivAt.fun_finset_prod := HasDerivAt.fun_finsetProd
/-
**HasDerivAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.finsetProd (hf : forall i in u, HasDerivAt (f i) (f' i) x) : Ha
sDerivAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x) • f' i) x
参数：hf : forall i in u, HasDerivAt (f i) (f' i) x。
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.fun_finsetProd`：HasDerivAt.fun_finsetProd (hf : forall i in u
, HasDerivAt (f i) (f' i) x) : HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u
.erase i, f j x…
-/
theorem HasDerivAt.finsetProd (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (∏ i ∈ u, f i) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  convert! HasDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias HasDerivAt.finset_prod := HasDerivAt.finsetProd
/-
**HasDerivWithinAt.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.fun_finsetProd (hf : forall i in u, HasDerivWithinAt (f i
) (f' i) s x) : HasDerivWithinAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i,
 f j x) • f' i) s x
参数：hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.finsetProd`：HasFDerivWithinAt.finsetProd [DecidableEq 
ι] {x : E} (hg : forall i in u, HasFDerivWithinAt (g i) (g' i) s x) : HasFDerivW
ithinAt (∏ i in u,…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.fun_finsetProd (hf : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) s x := by
  simpa using (HasFDerivWithinAt.finsetProd (hf · · |> hasFDerivWithinAt)).hasDerivWithinAt

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.fun_finset_prod := HasDerivWithinAt.fun_finsetProd
/-
**HasDerivWithinAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.finsetProd (hf : forall i in u, HasDerivWithinAt (f i) (f
' i) s x) : HasDerivWithinAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x
) • f' i) s x
参数：hf : forall i in u, HasDerivWithinAt (f i) (f' i) s x。
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivWithinAt.fun_finsetProd`：HasDerivWithinAt.fun_finsetProd (hf : f
orall i in u, HasDerivWithinAt (f i) (f' i) s x) : HasDerivWithinAt (∏ i in u, f
 i ·) (∑ i in u, (∏ j…
-/
theorem HasDerivWithinAt.finsetProd (hf : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (∏ i ∈ u, f i) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) s x := by
  convert! HasDerivWithinAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasDerivWithinAt.finset_prod := HasDerivWithinAt.finsetProd
/-
**HasStrictDerivAt.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.fun_finsetProd (hf : forall i in u, HasStrictDerivAt (f i
) (f' i) x) : HasStrictDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u.erase i, f
 j x) • f' i) x
参数：hf : forall i in u, HasStrictDerivAt (f i) (f' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.finsetProd`：HasStrictFDerivAt.finsetProd [DecidableEq 
ι] {x : E} (hg : forall i in u, HasStrictFDerivAt (g i) (g' i) x) : HasStrictFDe
rivAt (∏ i in u, g…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.fun_finsetProd (hf : ∀ i ∈ u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i ∈ u, f i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  simpa using (HasStrictFDerivAt.finsetProd (hf · · |> hasStrictFDerivAt)).hasStrictDerivAt

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.fun_finset_prod := HasStrictDerivAt.fun_finsetProd
/-
**HasStrictDerivAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.finsetProd (hf : forall i in u, HasStrictDerivAt (f i) (f
' i) x) : HasStrictDerivAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, f j x) 
• f' i) x
参数：hf : forall i in u, HasStrictDerivAt (f i) (f' i) x。
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictDerivAt.fun_finsetProd`：HasStrictDerivAt.fun_finsetProd (hf : f
orall i in u, HasStrictDerivAt (f i) (f' i) x) : HasStrictDerivAt (∏ i in u, f i
 ·) (∑ i in u, (∏ j i…
-/
theorem HasStrictDerivAt.finsetProd (hf : ∀ i ∈ u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (∏ i ∈ u, f i) (∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i) x := by
  convert! HasStrictDerivAt.fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")]
alias HasStrictDerivAt.finset_prod := HasStrictDerivAt.finsetProd
/-
**deriv_fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_finsetProd (hf : forall i in u, DifferentiableAt 𝕜 (f i) x) : de
riv (∏ i in u, f i ·) x = ∑ i in u, (∏ j in u.erase i, f j x) • deriv (f i) x
参数：hf : forall i in u, DifferentiableAt 𝕜 (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.fun_finsetProd`：HasDerivAt.fun_finsetProd (hf : forall i in u
, HasDerivAt (f i) (f' i) x) : HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u
.erase i, f j x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_finsetProd (hf : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i ∈ u, f i ·) x = ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.fun_finsetProd fun i hi ↦ (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_fun_finset_prod := deriv_fun_finsetProd
/-
**deriv_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_finsetProd (hf : forall i in u, DifferentiableAt 𝕜 (f i) x) : deriv 
(∏ i in u, f i) x = ∑ i in u, (∏ j in u.erase i, f j x) • deriv (f i) x
参数：hf : forall i in u, DifferentiableAt 𝕜 (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.finsetProd`：HasDerivAt.finsetProd (hf : forall i in u, HasDer
ivAt (f i) (f' i) x) : HasDerivAt (∏ i in u, f i) (∑ i in u, (∏ j in u.erase i, 
f j x) • f'…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_finsetProd (hf : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    deriv (∏ i ∈ u, f i) x = ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • deriv (f i) x :=
  (HasDerivAt.finsetProd fun i hi ↦ (hf i hi).hasDerivAt).deriv

@[deprecated (since := "2026-04-08")] alias deriv_finset_prod := deriv_finsetProd
/-
**derivWithin_fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_finsetProd (hf : forall i in u, DifferentiableWithinAt 𝕜 (
f i) s x) : derivWithin (∏ i in u, f i ·) s x = ∑ i in u, (∏ j in u.erase i, f j
 x) • derivWithin (f i) s x
参数：hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.fun_finsetProd`：HasDerivWithinAt.fun_finsetProd (hf : f
orall i in u, HasDerivWithinAt (f i) (f' i) s x) : HasDerivWithinAt (∏ i in u, f
 i ·) (∑ i in u, (∏ j…
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_finsetProd (hf : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i ∈ u, f i ·) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • derivWithin (f i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (HasDerivWithinAt.fun_finsetProd fun i hi ↦ (hf i hi).hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

@[deprecated (since := "2026-04-08")]
alias derivWithin_fun_finset_prod := derivWithin_fun_finsetProd
/-
**derivWithin_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_finsetProd (hf : forall i in u, DifferentiableWithinAt 𝕜 (f i)
 s x) : derivWithin (∏ i in u, f i) s x = ∑ i in u, (∏ j in u.erase i, f j x) • 
derivWithin (f i) s x
参数：hf : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `derivWithin_fun_finsetProd`：derivWithin_fun_finsetProd (hf : forall i in
 u, DifferentiableWithinAt 𝕜 (f i) s x) : derivWithin (∏ i in u, f i ·) s x = ∑ 
i in u, (∏ j in …
-/
theorem derivWithin_finsetProd (hf : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    derivWithin (∏ i ∈ u, f i) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • derivWithin (f i) s x := by
  convert! derivWithin_fun_finsetProd hf; simp

@[deprecated (since := "2026-04-08")] alias derivWithin_finset_prod := derivWithin_finsetProd

end HasDeriv

variable {ι : Type*} {𝔸' : Type*} [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸']
  {u : Finset ι} {f : ι → 𝕜 → 𝔸'}

@[fun_prop]
/-
**DifferentiableAt.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fun_finsetProd (hd : forall i in u, DifferentiableAt 𝕜 (f
 i) x) : DifferentiableAt 𝕜 (∏ i in u, f i ·) x
参数：hd : forall i in u, DifferentiableAt 𝕜 (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.fun_finsetProd`：HasDerivAt.fun_finsetProd (hf : forall i in u
, HasDerivAt (f i) (f' i) x) : HasDerivAt (∏ i in u, f i ·) (∑ i in u, (∏ j in u
.erase i, f j x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem DifferentiableAt.fun_finsetProd (hd : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (∏ i ∈ u, f i ·) x := by
  classical
  exact
    (HasDerivAt.fun_finsetProd (fun i hi ↦ DifferentiableAt.hasDerivAt (hd i hi))).differentiableAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.fun_finset_prod := DifferentiableAt.fun_finsetProd

@[fun_prop]
/-
**DifferentiableAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.finsetProd (hd : forall i in u, DifferentiableAt 𝕜 (f i) 
x) : DifferentiableAt 𝕜 (∏ i in u, f i) x
参数：hd : forall i in u, DifferentiableAt 𝕜 (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.fun_finsetProd`：DifferentiableAt.fun_finsetProd (hd : f
orall i in u, DifferentiableAt 𝕜 (f i) x) : DifferentiableAt 𝕜 (∏ i in u, f i ·)
 x
-/
theorem DifferentiableAt.finsetProd (hd : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (∏ i ∈ u, f i) x := by
  convert! DifferentiableAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableAt.finset_prod := DifferentiableAt.finsetProd

@[fun_prop]
/-
**DifferentiableWithinAt.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fun_finsetProd (hd : forall i in u, DifferentiableW
ithinAt 𝕜 (f i) s x) : DifferentiableWithinAt 𝕜 (∏ i in u, f i ·) s x
参数：hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivWithinAt.fun_finsetProd`：HasDerivWithinAt.fun_finsetProd (hf : f
orall i in u, HasDerivWithinAt (f i) (f' i) s x) : HasDerivWithinAt (∏ i in u, f
 i ·) (∑ i in u, (∏ j…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem DifferentiableWithinAt.fun_finsetProd (hd : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (∏ i ∈ u, f i ·) s x := by
  classical
  exact (HasDerivWithinAt.fun_finsetProd (fun i hi ↦
    DifferentiableWithinAt.hasDerivWithinAt (hd i hi))).differentiableWithinAt

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.fun_finset_prod := DifferentiableWithinAt.fun_finsetProd

@[fun_prop]
/-
**DifferentiableWithinAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.finsetProd (hd : forall i in u, DifferentiableWithi
nAt 𝕜 (f i) s x) : DifferentiableWithinAt 𝕜 (∏ i in u, f i) s x
参数：hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableWithinAt.fun_finsetProd`：DifferentiableWithinAt.fun_finset
Prod (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) : DifferentiableWi
thinAt 𝕜 (∏ i in u, f i ·) …
-/
theorem DifferentiableWithinAt.finsetProd (hd : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (f i) s x) :
    DifferentiableWithinAt 𝕜 (∏ i ∈ u, f i) s x := by
  convert! DifferentiableWithinAt.fun_finsetProd hd; simp

@[deprecated (since := "2026-04-08")]
alias DifferentiableWithinAt.finset_prod := DifferentiableWithinAt.finsetProd

@[fun_prop]
/-
**DifferentiableOn.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.fun_finsetProd (hd : forall i in u, DifferentiableOn 𝕜 (f
 i) s) : DifferentiableOn 𝕜 (∏ i in u, f i ·) s
参数：hd : forall i in u, DifferentiableOn 𝕜 (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.fun_finsetProd`：DifferentiableWithinAt.fun_finset
Prod (hd : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) : DifferentiableWi
thinAt 𝕜 (∏ i in u, f i ·) …
-/
theorem DifferentiableOn.fun_finsetProd (hd : ∀ i ∈ u, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (∏ i ∈ u, f i ·) s :=
  fun x hx ↦ .fun_finsetProd (fun i hi ↦ hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.fun_finset_prod := DifferentiableOn.fun_finsetProd

@[fun_prop]
/-
**DifferentiableOn.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.finsetProd (hd : forall i in u, DifferentiableOn 𝕜 (f i) 
s) : DifferentiableOn 𝕜 (∏ i in u, f i) s
参数：hd : forall i in u, DifferentiableOn 𝕜 (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.finsetProd`：DifferentiableWithinAt.finsetProd (hd
 : forall i in u, DifferentiableWithinAt 𝕜 (f i) s x) : DifferentiableWithinAt 𝕜
 (∏ i in u, f i) s x
-/
theorem DifferentiableOn.finsetProd (hd : ∀ i ∈ u, DifferentiableOn 𝕜 (f i) s) :
    DifferentiableOn 𝕜 (∏ i ∈ u, f i) s :=
  fun x hx ↦ .finsetProd (fun i hi ↦ hd i hi x hx)

@[deprecated (since := "2026-04-08")]
alias DifferentiableOn.finset_prod := DifferentiableOn.finsetProd

@[fun_prop]
/-
**Differentiable.fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.fun_finsetProd (hd : forall i in u, Differentiable 𝕜 (f i))
 : Differentiable 𝕜 (∏ i in u, f i ·)
参数：hd : forall i in u, Differentiable 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.fun_finsetProd`：DifferentiableAt.fun_finsetProd (hd : f
orall i in u, DifferentiableAt 𝕜 (f i) x) : DifferentiableAt 𝕜 (∏ i in u, f i ·)
 x
-/
theorem Differentiable.fun_finsetProd (hd : ∀ i ∈ u, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (∏ i ∈ u, f i ·) :=
  fun x ↦ .fun_finsetProd (fun i hi ↦ hd i hi x)

@[deprecated (since := "2026-04-08")]
alias Differentiable.fun_finset_prod := Differentiable.fun_finsetProd

@[fun_prop]
/-
**Differentiable.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.finsetProd (hd : forall i in u, Differentiable 𝕜 (f i)) : D
ifferentiable 𝕜 (∏ i in u, f i)
参数：hd : forall i in u, Differentiable 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.finsetProd`：DifferentiableAt.finsetProd (hd : forall i 
in u, DifferentiableAt 𝕜 (f i) x) : DifferentiableAt 𝕜 (∏ i in u, f i) x
-/
theorem Differentiable.finsetProd (hd : ∀ i ∈ u, Differentiable 𝕜 (f i)) :
    Differentiable 𝕜 (∏ i ∈ u, f i) :=
  fun x ↦ .finsetProd (fun i hi ↦ hd i hi x)

@[deprecated (since := "2026-04-08")] alias Differentiable.finset_prod := Differentiable.finsetProd

end Prod

section Div

variable {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

/-
**HasDerivAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') : HasDerivAt (fun x
 => c x / d) (c' / d) x
参数：hc : HasDerivAt c c' x；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasDerivAt.mul_const`：HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d :
 𝔸) : HasDerivAt (fun y => c y * d) (c' * d) x
-/
theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
    HasDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
/-
**HasDerivWithinAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') : Has
DerivWithinAt (fun x => c x / d) (c' / d) s x
参数：hc : HasDerivWithinAt c c' s x；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasDerivWithinAt.mul_const`：HasDerivWithinAt.mul_const (hc : HasDerivWit
hinAt c c' s x) (d : 𝔸) : HasDerivWithinAt (fun y => c y * d) (c' * d) s x
-/
theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
    HasDerivWithinAt (fun x => c x / d) (c' / d) s x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹
/-
**HasStrictDerivAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') : HasSt
rictDerivAt (fun x => c x / d) (c' / d) x
参数：hc : HasStrictDerivAt c c' x；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasStrictDerivAt.mul_const`：HasStrictDerivAt.mul_const (hc : HasStrictDe
rivAt c c' x) (d : 𝔸) : HasStrictDerivAt (fun y => c y * d) (c' * d) x
-/
theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
    HasStrictDerivAt (fun x => c x / d) (c' / d) x := by
  simpa only [div_eq_mul_inv] using hc.mul_const d⁻¹

@[fun_prop]
/-
**DifferentiableWithinAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d 
: 𝕜') : DifferentiableWithinAt 𝕜 (fun x => c x / d) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivWithinAt.div_const`：HasDerivWithinAt.div_const (hc : HasDerivWit
hinAt c c' s x) (d : 𝕜') : HasDerivWithinAt (fun x => c x / d) (c' / d) s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
    DifferentiableWithinAt 𝕜 (fun x => c x / d) s x :=
  (hc.hasDerivWithinAt.div_const _).differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') : Differ
entiableAt 𝕜 (fun x => c x / d) x
参数：hc : DifferentiableAt 𝕜 c x；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') :
    DifferentiableAt 𝕜 (fun x => c x / d) x :=
  (hc.hasDerivAt.div_const _).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') : Differ
entiableOn 𝕜 (fun x => c x / d) s
参数：hc : DifferentiableOn 𝕜 c s；d : 𝕜'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.div_const`：DifferentiableWithinAt.div_const (hc :
 DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') : DifferentiableWithinAt 𝕜 (fun x => c
 x / d) s x
-/
theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') :
    DifferentiableOn 𝕜 (fun x => c x / d) s := fun x hx => (hc x hx).div_const d

@[simp, fun_prop]
/-
**Differentiable.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') : Differentiab
le 𝕜 fun x => c x / d
参数：hc : Differentiable 𝕜 c；d : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.div_const`：DifferentiableAt.div_const (hc : Differentia
bleAt 𝕜 c x) (d : 𝕜') : DifferentiableAt 𝕜 (fun x => c x / d) x
-/
theorem Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') :
    Differentiable 𝕜 fun x => c x / d := fun x => (hc x).div_const d
/-
**derivWithin_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_div_const (c : 𝕜 -> 𝕜') (d : 𝕜') : derivWithin (fun x => c x /
 d) s x = derivWithin c s x / d
参数：c : 𝕜 -> 𝕜'；d : 𝕜'。
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
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `derivWithin_mul_const_field`：derivWithin_mul_const_field (u : 𝕜') : deri
vWithin (fun y => v y * u) s x = derivWithin v s x * u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_div_const (c : 𝕜 → 𝕜') (d : 𝕜') :
    derivWithin (fun x => c x / d) s x = derivWithin c s x / d := by
  simp [div_eq_mul_inv, derivWithin_mul_const_field]

@[simp]
/-
**deriv_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d
参数：d : 𝕜'。
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
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `deriv_mul_const_field`：deriv_mul_const_field (v : 𝕜') : deriv (fun y => 
u y * v) x = deriv u x * v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x = deriv c x / d := by
  simp only [div_eq_mul_inv, deriv_mul_const_field]

end Div

section CLMCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


open ContinuousLinearMap

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G}
  {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

/-
**HasStrictDerivAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDe
rivAt d d' x) : HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c
 x).comp d') x
参数：hc : HasStrictDerivAt c c' x；hd : HasStrictDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
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
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.clm_comp`：HasStrictFDerivAt.clm_comp (hc : HasStrictFD
erivAt c c' x) (hd : HasStrictFDerivAt d d' x) : HasStrictFDerivAt (fun y => (c 
y).comp (d y)) (…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.clm_comp (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_comp hd.hasStrictFDerivAt).hasStrictDerivAt
/-
**HasDerivWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x) (hd : HasDerivW
ithinAt d d' s x) : HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) 
+ (c x).comp d') s x
参数：hc : HasDerivWithinAt c c' s x；hd : HasDerivWithinAt d d' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
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
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.clm_comp`：HasFDerivWithinAt.clm_comp (hc : HasFDerivWi
thinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) : HasFDerivWithinAt (fun y =>
 (c y).comp (d y…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.clm_comp (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x := by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).hasDerivWithinAt
/-
**HasDerivAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) : Ha
sDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x
参数：hc : HasDerivAt c c' x；hd : HasDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.clm_comp`：HasDerivWithinAt.clm_comp (hc : HasDerivWithi
nAt c c' s x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (fun y => (c y
).comp (d y)) (…
-/
theorem HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.clm_comp hd
/-
**derivWithin_clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Different
iableWithinAt 𝕜 d s x) : derivWithin (fun y => (c y).comp (d y)) s x = (derivWit
hin c s x).comp (d x) + (c x).comp (derivWithin d s x)
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.clm_comp`：HasDerivWithinAt.clm_comp (hc : HasDerivWithi
nAt c c' s x) (hd : HasDerivWithinAt d d' s x) : HasDerivWithinAt (fun y => (c y
).comp (d y)) (…
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
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    derivWithin (fun y => (c y).comp (d y)) s x =
      (derivWithin c s x).comp (d x) + (c x).comp (derivWithin d s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_comp hd.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**deriv_clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
 : deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (de
riv d x)
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasDerivAt.clm_comp`：HasDerivAt.clm_comp (hc : HasDerivAt c c' x) (hd : 
HasDerivAt d d' x) : HasDerivAt (fun y => (c y).comp (d y)) (c'.comp (d x) + (c 
x).comp d…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (fun y => (c y).comp (d y)) x = (deriv c x).comp (d x) + (c x).comp (deriv d x) :=
  (hc.hasDerivAt.clm_comp hd.hasDerivAt).deriv
/-
**HasStrictDerivAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictD
erivAt u u' x) : HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x
参数：hc : HasStrictDerivAt c c' x；hu : HasStrictDerivAt u u' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.clm_apply`：HasStrictFDerivAt.clm_apply (hc : HasStrict
FDerivAt c c' x) (hu : HasStrictFDerivAt u u' x) : HasStrictFDerivAt (fun y => (
c y) (u y)) ((c x…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
    HasStrictDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  simpa [add_comm] using (hc.hasStrictFDerivAt.clm_apply hu.hasStrictFDerivAt).hasStrictDerivAt
/-
**HasDerivWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x) (hu : HasDeriv
WithinAt u u' s x) : HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u')
 s x
参数：hc : HasDerivWithinAt c c' s x；hu : HasDerivWithinAt u u' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.clm_apply`：HasFDerivWithinAt.clm_apply (hc : HasFDeriv
WithinAt c c' s x) (hu : HasFDerivWithinAt u u' s x) : HasFDerivWithinAt (fun y 
=> (c y) (u y)) (…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => (c y) (u y)) (c' (u x) + c x u') s x := by
  simpa [add_comm] using (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).hasDerivWithinAt
/-
**HasDerivAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) : H
asDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x
参数：hc : HasDerivAt c c' x；hu : HasDerivAt u u' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.clm_apply`：HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (
hu : HasFDerivAt u u' x) : HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c
'.flip (u x…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x := by
  simpa [add_comm] using (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).hasDerivAt
/-
**derivWithin_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_clm_apply (hc : DifferentiableWithinAt 𝕜 c s x) (hu : Differen
tiableWithinAt 𝕜 u s x) : derivWithin (fun y => (c y) (u y)) s x = derivWithin c
 s x (u x) + c x (derivWithin u s x)
参数：hc : DifferentiableWithinAt 𝕜 c s x；hu : DifferentiableWithinAt 𝕜 u s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.clm_apply`：HasDerivWithinAt.clm_apply (hc : HasDerivWit
hinAt c c' s x) (hu : HasDerivWithinAt u u' s x) : HasDerivWithinAt (fun y => (c
 y) (u y)) (c' (…
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) :
    derivWithin (fun y => (c y) (u y)) s x = derivWithin c s x (u x) + c x (derivWithin u s x) := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.clm_apply hu.hasDerivWithinAt).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**deriv_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x
) : deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x)
参数：hc : DifferentiableAt 𝕜 c x；hu : DifferentiableAt 𝕜 u x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.clm_apply`：HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu 
: HasDerivAt u u' x) : HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    deriv (fun y => (c y) (u y)) x = deriv c x (u x) + c x (deriv u x) :=
  (hc.hasDerivAt.clm_apply hu.hasDerivAt).deriv

end CLMCompApply

