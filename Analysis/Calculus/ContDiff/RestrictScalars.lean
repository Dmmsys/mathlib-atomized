/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
### Restricting Scalars in Iterated Fréchet Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The results are analogous to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

public section

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ} {s : Set E}

open ContinuousMultilinearMap Topology

/-- Derivation rule for compositions of scalar restriction with continuous multilinear maps. -/
/-
**fderivWithin_restrictScalars_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_restrictScalars_comp {φ : E -> (ContinuousMultilinearMap 𝕜' (
fun _ : Fin n => E) F)} (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWi
thinAt 𝕜 s x) : fderivWithin 𝕜 ((restrictScalars 𝕜) ∘ φ) s x = (restrictScalars 
𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜)
参数：ContinuousMultilinearMap 𝕜' (fun _ : Fin n => E) F；h : DifferentiableWithinAt
 𝕜' φ s x；hs : UniqueDiffWithinAt 𝕜 s x。
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
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `ContinuousMultilinearMap.instIsScalarTower`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderiv_comp_fderivWithin`：fderiv_comp_fderivWithin {g : F -> G} (hg : Di
fferentiableAt 𝕜 g (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDif
fWithinAt 𝕜 s …
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `DifferentiableWithinAt.restrictScalars`：DifferentiableWithinAt.restrictS
calars (h : DifferentiableWithinAt 𝕜' f s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] 
[inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMultilinearMap.restrictScalarsLinear_apply`：∀ {𝕜 : Type u_1} {
ι : Type u_2} {E : ι → Type u_3} {F : Type u_4} [inst : NormedField 𝕜]   [inst_1
 : (i : ι) → TopologicalSpace (E i)] [inst…
· 使用定理 `DifferentiableWithinAt.restrictScalars_fderivWithin`：DifferentiableWithi
nAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x) (hs : Un
iqueDiffWithinAt 𝕜 s x) : (fderivWithin 𝕜…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Derivation rule for compositions of scalar restriction with continuous multiline
ar maps.
-/
lemma fderivWithin_restrictScalars_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 ((restrictScalars 𝕜) ∘ φ) s x
      = (restrictScalars 𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜) := by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs, ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]

/--
If `f` is `n` times continuously differentiable at `x` within `s`, then the `n`th iterated Fréchet
derivative within `s` with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet
derivative within `s` with respect to `𝕜'`.
-/
/-
**ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq (h : Co
ntDiffWithinAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : (restrictScal
ars 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s) =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s
参数：h : ContDiffWithinAt 𝕜' n f s x；hs : UniqueDiffOn 𝕜 s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is `n` times continuously differentiable at `x` within `s`, then the `n`t
h iterated Fréchet
derivative within `s` with respect to `𝕜` equals scalar restriction of the `n`th
 iterated Fréchet
derivative within `s` with respect to `𝕜'`.
-/
theorem ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq
    (h : ContDiffWithinAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    (restrictScalars 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s)
      =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ : ∀ᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.eventually (by simp)
    filter_upwards [eventually_eventually_nhdsWithin.2 (hn t₀), t₁,
      eventually_mem_nhdsWithin (a := x) (s := s)] with a h₁a h₃a h₄a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [Function.comp_apply, coe_restrictScalars, iteratedFDerivWithin_succ_apply_left]
    rw [← (h₁a.fderivWithin' (by tauto)).eq_of_nhdsWithin h₄a,
      fderivWithin_restrictScalars_comp]
    · simp
    · apply h₃a.differentiableWithinAt_iteratedFDerivWithin
      · rw [Nat.cast_lt]
        simp
      · have : UniqueDiffOn 𝕜' s := hs.mono_field
        simpa [s.insert_eq_of_mem h₄a]
    apply hs a h₄a

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
/-
**ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' 
n f x) : (restrictScalars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 
n f
参数：h : ContDiffAt 𝕜' n f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq`：Cont
DiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq (h : ContDiffWith
inAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :…
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True

--- 原说明 ---
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated 
Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet deri
vative with respect
to `𝕜'`.
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' n f x) :
    (restrictScalars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f := by
  have h' : ContDiffWithinAt 𝕜' n f Set.univ x := h
  convert! (h'.restrictScalars_iteratedFDerivWithin_eventuallyEq _ trivial)
  <;> simp [iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ]

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
/-
**ContDiffAt.restrictScalars_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.restrictScalars_iteratedFDeriv (h : ContDiffAt 𝕜' n f x) : ((re
strictScalars 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x
参数：h : ContDiffAt 𝕜' n f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq`：ContDiffAt.restr
ictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' n f x) : (restrictScal
ars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] ite…

--- 原说明 ---
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated 
Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet deri
vative with respect
to `𝕜'`.
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv (h : ContDiffAt 𝕜' n f x) :
    ((restrictScalars 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x :=
  h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds
