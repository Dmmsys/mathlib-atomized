/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Higher differentiability in finite dimensions.

-/

public section


noncomputable section

universe uD uE uF

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {D : Type uD} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : D → E} {s : Set D}

/-! ### Finite-dimensional results -/

section FiniteDimensional

open Function Module

open scoped ContDiff

variable [CompleteSpace 𝕜]


/-- A family of continuous linear maps is `C^n` on `s` if all its applications are. -/
/-
**contDiffOn_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_clm_apply {f : D -> E ->L[𝕜] F} {s : Set D} [FiniteDimensional 
𝕜 E] : ContDiffOn 𝕜 n f s ↔ forall y, ContDiffOn 𝕜 n (fun x => f x y) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.clm_apply`：ContDiffOn.clm_apply {f : E -> F ->L[𝕜] G} {g : E 
-> F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun 
x => (f x)…
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fin_fun`：Module.finrank_fin_fun {n : Nat} : finrank R (Fi
n n -> R) = n
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `ContinuousLinearEquiv.symm_comp_self`：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂
) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_pi`：contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ forall i, ContDiffOn
 𝕜 n (fun x => Φ x i) s

--- 原说明 ---
A family of continuous linear maps is `C^n` on `s` if all its applications are.
-/
theorem contDiffOn_clm_apply {f : D → E →L[𝕜] F} {s : Set D} [FiniteDimensional 𝕜 E] :
    ContDiffOn 𝕜 n f s ↔ ∀ y, ContDiffOn 𝕜 n (fun x => f x y) s := by
  refine ⟨fun h y => h.clm_apply contDiffOn_const, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)
/-
**contDiff_clm_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_clm_apply_iff {f : D -> E ->L[𝕜] F} [FiniteDimensional 𝕜 E] : Con
tDiff 𝕜 n f ↔ forall y, ContDiff 𝕜 n fun x => f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiff_clm_apply_iff {f : D → E →L[𝕜] F} [FiniteDimensional 𝕜 E] :
    ContDiff 𝕜 n f ↔ ∀ y, ContDiff 𝕜 n fun x => f x y := by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

/-- This is a useful lemma to prove that a certain operation preserves functions being `C^n`.
When you do induction on `n`, this gives a useful characterization of a function being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version over
`contDiff_succ_iff_fderiv` is that both occurrences of `ContDiff` are for functions with the same
domain and codomain (`D` and `E`). This is not the case for `contDiff_succ_iff_fderiv`, which
often requires an inconvenient need to generalize `F`, which results in universe issues
(see the discussion in the section of `ContDiff.comp`).

This lemma avoids these universe issues, but only applies for finite-dimensional `D`. -/
/-
**contDiff_succ_iff_fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] : ContDiff 𝕜 (n + 1
) f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f Set.univ) ∧ forall y, Con
tDiff 𝕜 n fun x => fderiv 𝕜 f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiff_succ_iff_fderiv`：contDiff_succ_iff_fderiv : ContDiff 𝕜 (n + 1) 
f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderi
v 𝕜 f)
· 使用定理 `contDiff_clm_apply_iff`：contDiff_clm_apply_iff {f : D -> E ->L[𝕜] F} [Fi
niteDimensional 𝕜 E] : ContDiff 𝕜 n f ↔ forall y, ContDiff 𝕜 n fun x => f x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
This is a useful lemma to prove that a certain operation preserves functions bei
ng `C^n`.
When you do induction on `n`, this gives a useful characterization of a function
 being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version
 over
`contDiff_succ_iff_fderiv` is that both occurrences of `ContDiff` are for functi
ons with the same
domain and codomain (`D` and `E`). This is not the case for `contDiff_succ_iff_f
deriv`, which
often requires an inconvenient need to generalize `F`, which results in universe
 issues
(see the discussion in the section of `ContDiff.comp`).

This lemma avoids these universe issues, but only applies for finite-dimensional
 `D`.
-/
theorem contDiff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧
      (n = ω → AnalyticOnNhd 𝕜 f Set.univ) ∧ ∀ y, ContDiff 𝕜 n fun x => fderiv 𝕜 f x y := by
  rw [contDiff_succ_iff_fderiv, contDiff_clm_apply_iff]
/-
**contDiffOn_succ_of_fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_of_fderiv_apply [FiniteDimensional 𝕜 D] (hf : Differentiab
leOn 𝕜 f s) (h'f : n = ω -> AnalyticOn 𝕜 f s) (h : forall y, ContDiffOn 𝕜 n (fun
 x => fderivWithin 𝕜 f s x y) s) : ContDiffOn 𝕜 (n + 1) f s
参数：hf : DifferentiableOn 𝕜 f s；h'f : n = ω -> AnalyticOn 𝕜 f s；h : forall y, Con
tDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_succ_of_fderivWithin`：contDiffOn_succ_of_fderivWithin (hf : D
ifferentiableOn 𝕜 f s) (h' : n = ω -> AnalyticOn 𝕜 f s) (h : ContDiffOn 𝕜 n (fun
 y => fderivWithin 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_clm_apply`：contDiffOn_clm_apply {f : D -> E ->L[𝕜] F} {s : Se
t D} [FiniteDimensional 𝕜 E] : ContDiffOn 𝕜 n f s ↔ forall y, ContDiffOn 𝕜 n (fu
n x => f x…
-/
theorem contDiffOn_succ_of_fderiv_apply [FiniteDimensional 𝕜 D]
    (hf : DifferentiableOn 𝕜 f s) (h'f : n = ω → AnalyticOn 𝕜 f s)
    (h : ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s) :
    ContDiffOn 𝕜 (n + 1) f s :=
  contDiffOn_succ_of_fderivWithin hf h'f <| contDiffOn_clm_apply.mpr h
/-
**contDiffOn_succ_iff_fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] (hs : UniqueDiffO
n 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticO
n 𝕜 f s) ∧ forall y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_succ_iff_fderivWithin`：contDiffOn_succ_iff_fderivWithin (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1) f s ↔ DifferentiableOn 𝕜 f s ∧ (n = ω 
-> AnalyticOn 𝕜 f s) ∧…
· 使用定理 `contDiffOn_clm_apply`：contDiffOn_clm_apply {f : D -> E ->L[𝕜] F} {s : Se
t D} [FiniteDimensional 𝕜 E] : ContDiffOn 𝕜 n f s ↔ forall y, ContDiffOn 𝕜 n (fu
n x => f x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffOn_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧
      ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs, contDiffOn_clm_apply]

end FiniteDimensional

