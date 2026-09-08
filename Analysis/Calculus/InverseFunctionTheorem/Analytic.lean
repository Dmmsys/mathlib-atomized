/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Analyticity of local inverses
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
  [CompleteSpace 𝕜] [CharZero 𝕜]

namespace AnalyticAt

/-- The local inverse of an analytic function (at a point where its derivative does not vanish)
is itself analytic. -/
/-
**AnalyticAt.analyticAt_localInverse** 是 Mathlib 中的一个引理，位于命名空间 `AnalyticAt`。
形式化陈述：analyticAt_localInverse (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0) : A
nalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x)
参数：hf : AnalyticAt 𝕜 f x；hf' : deriv f x != 0。
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
· 使用引理 `AnalyticAt.hasStrictDerivAt`：AnalyticAt.hasStrictDerivAt {f : 𝕜 -> F} {x
 : 𝕜} (hf : AnalyticAt 𝕜 f x) : HasStrictDerivAt f (deriv f x) x
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
· 使用定理 `HasFPowerSeriesAt.analyticAt`：HasFPowerSeriesAt.analyticAt (hf : HasFPow
erSeriesAt f p x) : AnalyticAt 𝕜 f x
· 使用定理 `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`：OpenPartialHomeomorph.hasF
PowerSeriesAt_symm (f : OpenPartialHomeomorph E F) {a : E} {i : E ≃L[𝕜] F} (h0 :
 a in f.source) {p : FormalMultili…
· 使用引理 `AnalyticAt.hasFPowerSeriesAt`：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [
NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (
h : AnalyticAt 𝕜 f…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The local inverse of an analytic function (at a point where its derivative does 
not vanish)
is itself analytic.
-/
lemma analyticAt_localInverse (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x) := by
  let i : 𝕜 ≃L[𝕜] 𝕜 := .unitsEquivAut 𝕜 (.mk0 _ hf') -- multiplication by `deriv f a` as equiv
  have hfd : HasStrictFDerivAt f i.toContinuousLinearMap x := hf.hasStrictDerivAt
  let R : OpenPartialHomeomorph 𝕜 𝕜 := hfd.toOpenPartialHomeomorph _
  have hx : x ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  refine R.hasFPowerSeriesAt_symm hx hf.hasFPowerSeriesAt (i := i) ?_ |>.analyticAt
  ext
  simp [i]

end AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E}

/-
**analyticAt_comp_iff_of_deriv_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_comp_iff_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f x) (hf' : deriv 
f x != 0) : AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 g (f x)
参数：hf : AnalyticAt 𝕜 f x；hf' : deriv f x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.hasStrictDerivAt`：AnalyticAt.hasStrictDerivAt {f : 𝕜 -> F} {x
 : 𝕜} (hf : AnalyticAt 𝕜 f x) : HasStrictDerivAt f (deriv f x) x
· 使用引理 `AnalyticAt.analyticAt_localInverse`：analyticAt_localInverse (hf : Analyt
icAt 𝕜 f x) (hf' : deriv f x != 0) : AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInve
rse _ _ _ hf') (f x)
· 使用定理 `HasStrictFDerivAt.localInverse_apply_image`：localInverse_apply_image (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : hf.localInverse f f' a (f a) = a
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用引理 `HasStrictDerivAt.eventually_right_inverse`：eventually_right_inverse : fo
rallᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x
-/
lemma analyticAt_comp_iff_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 g (f x) := by
  refine ⟨fun hg ↦ ?_, (AnalyticAt.comp · hf)⟩
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hf'
  have hra : AnalyticAt 𝕜 r (f x) := hf.analyticAt_localInverse hf'
  have : r (f x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hg
  exact (hg.comp hra).congr <| .fun_comp (HasStrictDerivAt.eventually_right_inverse ..) g

end

