/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Bounds on higher derivatives

`norm_iteratedFDeriv_comp_le` gives the bound `n! * C * D ^ n` for the `n`-th derivative
  of `g ∘ f` assuming that the derivatives of `g` are bounded by `C` and the `i`-th
  derivative of `f` is bounded by `D ^ i`.
-/

public section

noncomputable section

open scoped NNReal Nat ContDiff

universe u uD uE uF uG

open Set Fin Filter Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {D : Type uD} [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s s₁ t u : Set E}

/-!## Quantitative bounds -/

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear. This lemma is an auxiliary version
assuming all spaces live in the same universe, to enable an induction. Use instead
`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` that removes this assumption. -/
/-
**ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu
 Gu : Type u} [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAddCommGroup Eu]
 [NormedSpace 𝕜 Eu] [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGro
up Gu] [NormedSpace 𝕜 Gu] (B : Eu ->L[𝕜] Fu ->L[𝕜] Gu) {f : Du -> Eu} {g : Du ->
 Fu} {n : Nat} {s : Set Du} {x : Du} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 
𝕜 n g s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) : ‖iteratedFDerivWithin 𝕜 n (fun 
y => B (f y) (g y)) s x‖ <
参数：B : Eu ->L[𝕜] Fu ->L[𝕜] Gu；hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s；hs
 : UniqueDiffOn 𝕜 s；hx : x in s。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDerivWithin_zero`：norm_iteratedFDerivWithin_zero : ‖iterat
edFDerivWithin 𝕜 0 f s x‖ = ‖f x‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `ContDiffOn.fderivWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type uF} […
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.norm_precompR_le`：norm_precompR_le (L : E ->L[𝕜] Fₗ 
->L[𝕜] Gₗ) : ‖precompR Eₗ L‖ <= ‖L‖
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in 
terms of the
iterated derivatives of `f` and `g` when `B` is bilinear. This lemma is an auxil
iary version
assuming all spaces live in the same universe, to enable an induction. Use inste
ad
`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` that removes this
 assumption.
-/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu Gu : Type u}
    [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAddCommGroup Eu] [NormedSpace 𝕜 Eu]
    [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu]
    (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : Set Du} {x : Du}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We argue by induction on `n`. The bound is trivial for `n = 0`. For `n + 1`, we write
    the `(n+1)`-th derivative as the `n`-th derivative of the derivative `B f g' + B f' g`,
    and apply the inductive assumption to each of those two terms. For this induction to make sense,
    the spaces of linear maps that appear in the induction should be in the same universe as the
    original spaces, which explains why we assume in the lemma that all spaces live in the same
    universe. -/
  induction n generalizing Eu Fu Gu with
  | zero =>
    simp only [norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
    apply B.le_opNorm₂
  | succ n IH =>
    have In : (n : ℕ∞ω) + 1 ≤ n.succ := by simp only [Nat.cast_succ, le_refl]
    have I1 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
            ‖iteratedFDerivWithin 𝕜 (n + 1 - i) g s x‖ := by
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
            ‖B.precompR Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ :=
          IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ := by
            gcongr; exact B.norm_precompR_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i hi => ?_
          rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
            ← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have I2 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 (i + 1) f s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
            ‖B.precompL Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
          IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
            n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
          gcongr; exact B.norm_precompL_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i _ => ?_
          rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have J : iteratedFDerivWithin 𝕜 n
        (fun y : Du => fderivWithin 𝕜 (fun y : Du => B (f y) (g y)) s y) s x =
          iteratedFDerivWithin 𝕜 n (fun y => B.precompR Du (f y)
            (fderivWithin 𝕜 g s y) + B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x := by
      apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
      exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
        (hg.differentiableOn (by positivity) y hy) (hs y hy)
    rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
    have A : ContDiffOn 𝕜 n (fun y => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s :=
      (B.precompR Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
    have A' : ContDiffOn 𝕜 n (fun y => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s :=
      (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
        (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    rw [fun_iteratedFDerivWithin_add_apply (A.contDiffWithinAt hx) (A'.contDiffWithinAt hx) hs hx]
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
    simp_rw [← mul_add, mul_assoc]
    congr 1
    exact (Finset.sum_choose_succ_mul
      (fun i j => ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 j g s x‖) n).symm

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
/-
**ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear (B : E ->L[𝕜]
 F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : Set D} {x : D} (hf : Con
tDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
 {n : Nat} (hn : n <= N) : ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s 
x‖ <= ‖B‖ * ∑ i in Finset.range (n + 1), (n.choose i : Real) * ‖iteratedFDerivWi
thin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖
参数：B : E ->L[𝕜] F ->L[𝕜] G；hf : ContDiffOn 𝕜 N f s；hg : ContDiffOn 𝕜 N g s；hs : 
UniqueDiffOn 𝕜 s；hx : x in s；hn : n <= N。
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
· 使用定理 `instContinuousAddULift`：∀ {M : Type u_3} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M], ContinuousAdd (ULift.{u, u_3} M)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.uniqueDiffOn_preimage_iff`：ContinuousLinearEquiv.u
niqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) : UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiff
On 𝕜 s
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `ContDiffOn.comp_continuousLinearMap`：ContDiffOn.comp_continuousLinearMap
 (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E) : ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s)
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left`：LinearIsometryE
quiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (hs : Uni
queDiffOn 𝕜 s) (hx : x in s) (i : Nat) : ‖ite…
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right`：LinearIsometry
Equiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (hs : U
niqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : …
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux`：Contin
uousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu Gu : Type u
} [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAd…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in 
terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖`
-/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear (B : E →L[𝕜] F →L[𝕜] G)
    {f : D → E} {g : D → F} {N : ℕ∞ω} {s : Set D} {x : D} (hf : ContDiffOn 𝕜 N f s)
    (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We reduce the bound to the case where all spaces live in the same universe (in which we
    already have proved the result), by using linear isometries between the spaces and their `ULift`
    to a common universe. These linear isometries preserve the norm of the iterated derivative. -/
  let Du : Type max uD uE uF uG := ULift.{max uE uF uG, uD} D
  let Eu : Type max uD uE uF uG := ULift.{max uD uF uG, uE} E
  let Fu : Type max uD uE uF uG := ULift.{max uD uE uG, uF} F
  let Gu : Type max uD uE uF uG := ULift.{max uD uE uF, uG} G
  have isoD : Du ≃ₗᵢ[𝕜] D := LinearIsometryEquiv.ulift 𝕜 D
  have isoE : Eu ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ulift 𝕜 E
  have isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  have isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  -- lift `f` and `g` to versions `fu` and `gu` on the lifted spaces.
  let fu : Du → Eu := isoE.symm ∘ f ∘ isoD
  let gu : Du → Fu := isoF.symm ∘ g ∘ isoD
  -- lift the bilinear map `B` to a bilinear map `Bu` on the lifted spaces.
  let Bu₀ : Eu →L[𝕜] Fu →L[𝕜] G := ((B.comp (isoE : Eu →L[𝕜] E)).flip.comp (isoF : Fu →L[𝕜] F)).flip
  let Bu : Eu →L[𝕜] Fu →L[𝕜] Gu :=
    ContinuousLinearMap.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
      (ContinuousLinearMap.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀
  have hBu : Bu = ContinuousLinearMap.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
      (ContinuousLinearMap.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀ := rfl
  have Bu_eq : (fun y => Bu (fu y) (gu y)) = isoG.symm ∘ (fun y => B (f y) (g y)) ∘ isoD := by
    ext1 y
    simp [Du, Eu, Fu, Gu, hBu, Bu₀, fu, gu]
  -- All norms are preserved by the lifting process.
  have Bu_le : ‖Bu‖ ≤ ‖B‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun y => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    simp only [Eu, Fu, Gu, hBu, Bu₀, compL_apply, comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, flip_apply, LinearIsometryEquiv.norm_map]
    calc
      ‖B (isoE y) (isoF x)‖ ≤ ‖B (isoE y)‖ * ‖isoF x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B‖ * ‖isoE y‖ * ‖isoF x‖ := by gcongr; apply ContinuousLinearMap.le_opNorm
      _ = ‖B‖ * ‖y‖ * ‖x‖ := by simp only [LinearIsometryEquiv.norm_map]
  let su := isoD ⁻¹' s
  have hsu : UniqueDiffOn 𝕜 su := isoD.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.2 hs
  let xu := isoD.symm x
  have hxu : xu ∈ su := by
    simpa only [xu, su, Set.mem_preimage, LinearIsometryEquiv.apply_symm_apply] using hx
  have xu_x : isoD xu = x := by simp only [xu, LinearIsometryEquiv.apply_symm_apply]
  have hfu : ContDiffOn 𝕜 n fu su :=
    isoE.symm.contDiff.comp_contDiffOn
      ((hf.of_le hn).comp_continuousLinearMap (isoD : Du →L[𝕜] D))
  have hgu : ContDiffOn 𝕜 n gu su :=
    isoF.symm.contDiff.comp_contDiffOn
      ((hg.of_le hn).comp_continuousLinearMap (isoD : Du →L[𝕜] D))
  have Nfu : ∀ i, ‖iteratedFDerivWithin 𝕜 i fu su xu‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
    intro i
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  have Ngu : ∀ i, ‖iteratedFDerivWithin 𝕜 i gu su xu‖ = ‖iteratedFDerivWithin 𝕜 i g s x‖ := by
    intro i
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  have NBu :
    ‖iteratedFDerivWithin 𝕜 n (fun y => Bu (fu y) (gu y)) su xu‖ =
      ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ := by
    rw [Bu_eq]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  -- state the bound for the lifted objects, and deduce the original bound from it.
  have : ‖iteratedFDerivWithin 𝕜 n (fun y => Bu (fu y) (gu y)) su xu‖ ≤
      ‖Bu‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i fu su xu‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) gu su xu‖ :=
    Bu.norm_iteratedFDerivWithin_le_of_bilinear_aux hfu hgu hsu hxu
  simp only [Nfu, Ngu, NBu] at this
  exact this.trans <| by gcongr

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
/-
**ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B : E ->L[𝕜] F ->L
[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} (hf : ContDiff 𝕜 N f) (hg : ContDif
f 𝕜 N g) (x : D) {n : Nat} (hn : n <= N) : ‖iteratedFDeriv 𝕜 n (fun y => B (f y)
 (g y)) x‖ <= ‖B‖ * ∑ i in Finset.range (n + 1), (n.choose i : Real) * ‖iterated
FDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖
参数：B : E ->L[𝕜] F ->L[𝕜] G；hf : ContDiff 𝕜 N f；hg : ContDiff 𝕜 N g；x : D；hn : n 
<= N。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`：Continuous
LinearMap.norm_iteratedFDerivWithin_le_of_bilinear (B : E ->L[𝕜] F ->L[𝕜] G) {f 
: D -> E} {g : D -> F} {N : Nat∞ω} {s : Set D} {x …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖`
-/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B : E →L[𝕜] F →L[𝕜] G) {f : D → E}
    {g : D → F} {N : ℕ∞ω} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : D) {n : ℕ}
    (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact B.norm_iteratedFDerivWithin_le_of_bilinear hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ
    (mem_univ x) hn

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
/-
**ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (B 
: E ->L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : Set D} {x : D}
 (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx
 : x in s) {n : Nat} (hn : n <= N) (hB : ‖B‖ <= 1) : ‖iteratedFDerivWithin 𝕜 n (
fun y => B (f y) (g y)) s x‖ <= ∑ i in Finset.range (n + 1), (n.choose i : Real)
 * ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖
参数：B : E ->L[𝕜] F ->L[𝕜] G；hf : ContDiffOn 𝕜 N f s；hg : ContDiffOn 𝕜 N g s；hs : 
UniqueDiffOn 𝕜 s；hx : x in s；hn : n <= N；hB : ‖B‖ <= 1。
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`：Continuous
LinearMap.norm_iteratedFDerivWithin_le_of_bilinear (B : E ->L[𝕜] F ->L[𝕜] G) {f 
: D -> E} {g : D -> F} {N : Nat∞ω} {s : Set D} {x …
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in 
terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖`
-/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : ℕ∞ω} {s : Set D} {x : D}
    (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ}
    (hn : n ≤ N) (hB : ‖B‖ ≤ 1) : ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  apply (B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hs hx hn).trans
  exact mul_le_of_le_one_left (by positivity) hB

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
/-
**ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (B : E ->
L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} (hf : ContDiff 𝕜 N f) (hg
 : ContDiff 𝕜 N g) (x : D) {n : Nat} (hn : n <= N) (hB : ‖B‖ <= 1) : ‖iteratedFD
eriv 𝕜 n (fun y => B (f y) (g y)) x‖ <= ∑ i in Finset.range (n + 1), (n.choose i
 : Real) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖
参数：B : E ->L[𝕜] F ->L[𝕜] G；hf : ContDiff 𝕜 N f；hg : ContDiff 𝕜 N g；x : D；hn : n 
<= N；hB : ‖B‖ <= 1。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one`：
ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (B : E ->
L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖`
-/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (B : E →L[𝕜] F →L[𝕜] G)
    {f : D → E} {g : D → F} {N : ℕ∞ω} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g)
    (x : D) {n : ℕ} (hn : n ≤ N) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf.contDiffOn hg.contDiffOn
    uniqueDiffOn_univ (mem_univ x) hn hB

section

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

/-
**norm_iteratedFDerivWithin_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_smul_le {f : E -> 𝕜'} {g : E -> F} {N : Nat∞ω} (
hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) {x : 
E} (hx : x in s) {n : Nat} (hn : n <= N) : ‖iteratedFDerivWithin 𝕜 n (fun y => f
 y • g y) s x‖ <= ∑ i in Finset.range (n + 1), (n.choose i : Real) * ‖iteratedFD
erivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖
参数：hf : ContDiffOn 𝕜 N f s；hg : ContDiffOn 𝕜 N g s；hs : UniqueDiffOn 𝕜 s；hx : x 
in s；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one`：
ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (B : E ->
L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : …
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_le`：opNorm_lsmul_le : ‖(lsmul 𝕜 R : R -
>L[𝕜] E ->L[𝕜] E)‖ <= 1
-/
theorem norm_iteratedFDerivWithin_smul_le {f : E → 𝕜'} {g : E → F} {N : ℕ∞ω}
    (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : n ≤ N) : ‖iteratedFDerivWithin 𝕜 n (fun y => f y • g y) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜' :
    𝕜' →L[𝕜] F →L[𝕜] F).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hf hg hs hx hn ContinuousLinearMap.opNorm_lsmul_le
/-
**norm_iteratedFDeriv_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_smul_le {f : E -> 𝕜'} {g : E -> F} {N : Nat∞ω} (hf : C
ontDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : E) {n : Nat} (hn : n <= N) : ‖iterated
FDeriv 𝕜 n (fun y => f y • g y) x‖ <= ∑ i in Finset.range (n + 1), (n.choose i :
 Real) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖
参数：hf : ContDiff 𝕜 N f；hg : ContDiff 𝕜 N g；x : E；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one`：Contin
uousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (B : E ->L[𝕜] F ->L[𝕜
] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} (hf : ContD…
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_le`：opNorm_lsmul_le : ‖(lsmul 𝕜 R : R -
>L[𝕜] E ->L[𝕜] E)‖ <= 1
-/
theorem norm_iteratedFDeriv_smul_le {f : E → 𝕜'} {g : E → F} {N : ℕ∞ω} (hf : ContDiff 𝕜 N f)
    (hg : ContDiff 𝕜 N g) (x : E) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y • g y) x‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    hf hg x hn ContinuousLinearMap.opNorm_lsmul_le

end

section

variable {ι : Type*} {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] {A' : Type*} [NormedCommRing A']
  [NormedAlgebra 𝕜 A']

/-
**norm_iteratedFDerivWithin_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_mul_le {f : E -> A} {g : E -> A} {N : Nat∞ω} (hf
 : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) {x : E}
 (hx : x in s) {n : Nat} (hn : n <= N) : ‖iteratedFDerivWithin 𝕜 n (fun y => f y
 * g y) s x‖ <= ∑ i in Finset.range (n + 1), (n.choose i : Real) * ‖iteratedFDer
ivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖
参数：hf : ContDiffOn 𝕜 N f s；hg : ContDiffOn 𝕜 N g s；hs : UniqueDiffOn 𝕜 s；hx : x 
in s；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one`：
ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (B : E ->
L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.opNorm_mul_le`：opNorm_mul_le : ‖mul 𝕜 R‖ <= 1
-/
theorem norm_iteratedFDerivWithin_mul_le {f : E → A} {g : E → A} {N : ℕ∞ω}
    (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s)
    {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => f y * g y) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
  (ContinuousLinearMap.mul 𝕜 A :
    A →L[𝕜] A →L[𝕜] A).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hf hg hs hx hn (ContinuousLinearMap.opNorm_mul_le _ _)
/-
**norm_iteratedFDeriv_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_mul_le {f : E -> A} {g : E -> A} {N : Nat∞ω} (hf : Con
tDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : E) {n : Nat} (hn : n <= N) : ‖iteratedFD
eriv 𝕜 n (fun y => f y * g y) x‖ <= ∑ i in Finset.range (n + 1), (n.choose i : R
eal) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖
参数：hf : ContDiff 𝕜 N f；hg : ContDiff 𝕜 N g；x : E；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `norm_iteratedFDerivWithin_mul_le`：norm_iteratedFDerivWithin_mul_le {f : 
E -> A} {g : E -> A} {N : Nat∞ω} (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N 
g s) (hs : UniqueDiffO…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem norm_iteratedFDeriv_mul_le {f : E → A} {g : E → A} {N : ℕ∞ω} (hf : ContDiff 𝕜 N f)
    (hg : ContDiff 𝕜 N g) (x : E) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_mul_le
    hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ (mem_univ x) hn

-- TODO: Add `norm_iteratedFDeriv[Within]_list_prod_le` for non-commutative `NormedRing A`.

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**norm_iteratedFDerivWithin_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_prod_le [DecidableEq ι] [NormOneClass A'] {u : F
inset ι} {f : ι -> E -> A'} {N : Nat∞ω} (hf : forall i in u, ContDiffOn 𝕜 N (f i
) s) (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x in s) {n : Nat} (hn : n <= N) : ‖it
eratedFDerivWithin 𝕜 n (∏ j in u, f j ·) s x‖ <= ∑ p in u.sym n, (p : Multiset ι
).countPerms * ∏ j in u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j p) (f j) s x‖
参数：hf : forall i in u, ContDiffOn 𝕜 N (f i) s；hs : UniqueDiffOn 𝕜 s；hx : x in s；
hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDerivWithin_zero`：norm_iteratedFDerivWithin_zero : ‖iterat
edFDerivWithin 𝕜 0 f s x‖ = ‖f x‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Sym.eq_nil_of_card_zero`：eq_nil_of_card_zero (s : Sym α 0) : s = nil
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.countPerms.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} 
[inst_1 : DecidableEq α] (m m_1 : Multiset α),   m = m_1 → m.countPerms = m_1.co
untPerms
· 使用定理 `Multiset.countPerms_zero`：countPerms_zero [DecidableEq α] : countPerms (
0 : Multiset α) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_succ_const`：iteratedFDerivWithin_succ_const (n : Na
t) (c : F) : iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E => c) s = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_iteratedFDerivWithin_mul_le`：norm_iteratedFDerivWithin_mul_le {f : 
E -> A} {g : E -> A} {N : Nat∞ω} (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N 
g s) (hs : UniqueDiffO…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `contDiffOn_prod`：contDiffOn_prod {t : Finset ι} {f : ι -> E -> 𝔸'} (h : 
forall i in t, ContDiffOn 𝕜 n (f i) s) : ContDiffOn 𝕜 n (fun y => ∏ i in t, f i 
y) s
（共 80 条，此处仅展示前 30 条）
-/
theorem norm_iteratedFDerivWithin_prod_le [DecidableEq ι] [NormOneClass A'] {u : Finset ι}
    {f : ι → E → A'} {N : ℕ∞ω} (hf : ∀ i ∈ u, ContDiffOn 𝕜 N (f i) s)
    (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (∏ j ∈ u, f j ·) s x‖ ≤
      ∑ p ∈ u.sym n, (p : Multiset ι).countPerms *
        ∏ j ∈ u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j p) (f j) s x‖ := by
  induction u using Finset.induction generalizing n with
  | empty =>
    cases n with
    | zero => simp [Sym.eq_nil_of_card_zero]
    | succ n => simp [iteratedFDerivWithin_succ_const]
  | insert i u hi IH =>
    conv => lhs; simp only [Finset.prod_insert hi]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    refine le_trans (norm_iteratedFDerivWithin_mul_le hf.1 (contDiffOn_prod hf.2) hs hx hn) ?_
    rw [← Finset.sum_coe_sort (Finset.sym _ _)]
    rw [Finset.sum_equiv (Finset.symInsertEquiv hi) (t := Finset.univ)
      (g := (fun v ↦ v.countPerms *
          ∏ j ∈ insert i u, ‖iteratedFDerivWithin 𝕜 (v.count j) (f j) s x‖) ∘
        Sym.toMultiset ∘ Subtype.val ∘ (Finset.symInsertEquiv hi).symm)
      (by simp) (by simp only [← comp_apply (g := Finset.symInsertEquiv hi), comp_assoc]; simp)]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_range]
    simp +instances only [comp_apply, Finset.symInsertEquiv_symm_apply_coe]
    gcongr with m _
    specialize IH hf.2 (n := n - m) (le_trans (by exact_mod_cast n.sub_le m) hn)
    grw [IH]
    rw [Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_le_sum ?_
    simp only [Finset.mem_univ, forall_true_left, Subtype.forall, Finset.mem_sym_iff]
    intro p hp
    refine le_of_eq ?_
    rw [Finset.prod_insert hi]
    have hip : i ∉ p := mt (hp i) hi
    rw [Sym.count_coe_fill_self_of_notMem hip, Sym.countPerms_coe_fill_of_notMem hip]
    suffices ∏ j ∈ u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j p) (f j) s x‖ =
        ∏ j ∈ u, ‖iteratedFDerivWithin 𝕜 (Multiset.count j (Sym.fill i m p)) (f j) s x‖ by
      rw [this, Nat.cast_mul]
      ring
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := mt (· ▸ hj) hi
    rw [Sym.count_coe_fill_of_ne hji]
/-
**norm_iteratedFDeriv_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_prod_le [DecidableEq ι] [NormOneClass A'] {u : Finset 
ι} {f : ι -> E -> A'} {N : Nat∞ω} (hf : forall i in u, ContDiff 𝕜 N (f i)) {x : 
E} {n : Nat} (hn : n <= N) : ‖iteratedFDeriv 𝕜 n (∏ j in u, f j ·) x‖ <= ∑ p in 
u.sym n, (p : Multiset ι).countPerms * ∏ j in u, ‖iteratedFDeriv 𝕜 ((p : Multise
t ι).count j) (f j) x‖
参数：hf : forall i in u, ContDiff 𝕜 N (f i)；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `norm_iteratedFDerivWithin_prod_le`：norm_iteratedFDerivWithin_prod_le [De
cidableEq ι] [NormOneClass A'] {u : Finset ι} {f : ι -> E -> A'} {N : Nat∞ω} (hf
 : forall i in u, ContD…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem norm_iteratedFDeriv_prod_le [DecidableEq ι] [NormOneClass A'] {u : Finset ι}
    {f : ι → E → A'} {N : ℕ∞ω} (hf : ∀ i ∈ u, ContDiff 𝕜 N (f i)) {x : E} {n : ℕ}
    (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (∏ j ∈ u, f j ·) x‖ ≤
      ∑ p ∈ u.sym n, (p : Multiset ι).countPerms *
        ∏ j ∈ u, ‖iteratedFDeriv 𝕜 ((p : Multiset ι).count j) (f j) x‖ := by
  simpa [iteratedFDerivWithin_univ] using
    norm_iteratedFDerivWithin_prod_le (fun i hi ↦ (hf i hi).contDiffOn) uniqueDiffOn_univ
      (mem_univ x) hn

end

/-- If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`.
This lemma proves this estimate assuming additionally that two of the spaces live in the same
universe, to make an induction possible. Use instead `norm_iteratedFDerivWithin_comp_le` that
removes this assumption. -/
/-
**norm_iteratedFDerivWithin_comp_le_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_comp_le_aux {Fu Gu : Type u} [NormedAddCommGroup
 Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu] {g : Fu -> Gu
} {f : E -> Fu} {n : Nat} {s : Set E} {t : Set Fu} {x : E} (hg : ContDiffOn 𝕜 n 
g t) (hf : ContDiffOn 𝕜 n f s) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (
hst : MapsTo f s t) (hx : x in s) {C : Real} {D : Real} (hC : forall i, i <= n -
> ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ <= C) (hD : forall i, 1 <= i -> i <= n ->
 ‖iteratedFDerivWithin 𝕜 i
参数：hg : ContDiffOn 𝕜 n g t；hf : ContDiffOn 𝕜 n f s；ht : UniqueDiffOn 𝕜 t；hs : Un
iqueDiffOn 𝕜 s；hst : MapsTo f s t；hx : x in s；hC : forall i, i <= n -> ‖iterated
FDerivWithin 𝕜 i g t (f x)‖ <= C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDerivWithin_zero`：norm_iteratedFDerivWithin_zero : ‖iterat
edFDerivWithin 𝕜 0 f s x‖ = ‖f x‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 137 条，此处仅展示前 30 条）

--- 原说明 ---
If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-
th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`
-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`.
This lemma proves this estimate assuming additionally that two of the spaces liv
e in the same
universe, to make an induction possible. Use instead `norm_iteratedFDerivWithin_
comp_le` that
removes this assumption.
-/
theorem norm_iteratedFDerivWithin_comp_le_aux {Fu Gu : Type u} [NormedAddCommGroup Fu]
    [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu] {g : Fu → Gu} {f : E → Fu} {n : ℕ}
    {s : Set E} {t : Set Fu} {x : E} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst : MapsTo f s t) (hx : x ∈ s) {C : ℝ}
    {D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * D ^ n := by
  /- We argue by induction on `n`, using that `D^(n+1) (g ∘ f) = D^n (g ' ∘ f ⬝ f')`. The successive
    derivatives of `g' ∘ f` are controlled thanks to the inductive assumption, and those of `f'` are
    controlled by assumption.
    As composition of linear maps is a bilinear map, one may use
    `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one` to get from these a bound
    on `D^n (g ' ∘ f ⬝ f')`. -/
  induction n using Nat.case_strong_induction_on generalizing Gu with
  | hz =>
    simpa [norm_iteratedFDerivWithin_zero, Nat.factorial_zero, algebraMap.coe_one, one_mul,
      pow_zero, mul_one, comp_apply] using! hC 0 le_rfl
  | hi n IH =>
  have M : (n : ℕ∞ω) < n.succ := Nat.cast_lt.2 n.lt_succ_self
  have Cnonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0 bot_le)
  have Dnonneg : 0 ≤ D := by
    have : 1 ≤ n + 1 := by simp
    simpa using (norm_nonneg _).trans (hD 1 le_rfl this)
  -- use the inductive assumption to bound the derivatives of `g' ∘ f`.
  have I : ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 g t ∘ f) s x‖ ≤ i ! * C * D ^ i := by
    intro i hi
    simp only [Finset.mem_range_succ_iff] at hi
    apply IH i hi
    · apply hg.fderivWithin ht
      grw [Nat.cast_succ, hi]
    · apply hf.of_le (Nat.cast_le.2 (hi.trans n.le_succ))
    · intro j hj
      have : ‖iteratedFDerivWithin 𝕜 j (fderivWithin 𝕜 g t) t (f x)‖ =
          ‖iteratedFDerivWithin 𝕜 (j + 1) g t (f x)‖ := by
        rw [iteratedFDerivWithin_succ_eq_comp_right ht (hst hx), comp_apply,
          LinearIsometryEquiv.norm_map]
      rw [this]
      exact hC (j + 1) (add_le_add (hj.trans hi) le_rfl)
    · intro j hj h'j
      exact hD j hj (h'j.trans (hi.trans n.le_succ))
  -- reformulate `hD` as a bound for the derivatives of `f'`.
  have J : ∀ i, ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 f s) s x‖ ≤ D ^ (n - i + 1) := by
    intro i
    have : ‖iteratedFDerivWithin 𝕜 (n - i + 1) f s x‖ ≤ D ^ (n - i + 1) :=
      hD (n - i + 1) (by simp) (Nat.succ_le_succ tsub_le_self)
    simpa [iteratedFDerivWithin_succ_eq_comp_right hs hx]
  -- Now put these together: first, notice that we have to bound `D^n (g' ∘ f ⬝ f')`.
  calc
    ‖iteratedFDerivWithin 𝕜 (n + 1) (g ∘ f) s x‖ =
        ‖iteratedFDerivWithin 𝕜 n (fun y : E => fderivWithin 𝕜 (g ∘ f) s y) s x‖ := by
      rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, comp_apply,
        LinearIsometryEquiv.norm_map]
    _ = ‖iteratedFDerivWithin 𝕜 n (fun y : E => ContinuousLinearMap.compL 𝕜 E Fu Gu
        (fderivWithin 𝕜 g t (f y)) (fderivWithin 𝕜 f s y)) s x‖ := by
      congr 1
      refine iteratedFDerivWithin_congr (fun y hy => ?_) hx _
      apply fderivWithin_comp _ _ _ hst (hs y hy)
      · exact hg.differentiableOn (by positivity) _ (hst hy)
      · exact hf.differentiableOn (by positivity) _ hy
    -- bound it using! the fact that the composition of linear maps is a bilinear operation,
    -- for which we have bounds for the`n`-th derivative.
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 g t ∘ f) s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 f s) s x‖ := by
      exact (ContinuousLinearMap.compL 𝕜 E Fu Gu).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
        ((hg.fderivWithin ht (by simp)).comp (hf.of_le M.le) hst) (hf.fderivWithin hs (by simp))
        hs hx le_rfl (ContinuousLinearMap.norm_compL_le 𝕜 E Fu Gu)
    -- bound each of the terms using the estimates on previous derivatives (that use the inductive
    -- assumption for `g' ∘ f`).
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (i ! * C * D ^ i) * D ^ (n - i + 1) := by
      gcongr with i hi
      · exact I i hi
      · exact J i
    -- We are left with trivial algebraic manipulations to see that this is smaller than
    -- the claimed bound.
    _ = ∑ i ∈ Finset.range (n + 1),
        (n ! : ℝ) * ((i ! : ℝ)⁻¹ * i !) * C * (D ^ i * D ^ (n - i + 1)) * ((n - i)! : ℝ)⁻¹ := by
      congr! 1 with i hi
      simp only [Nat.cast_choose ℝ (Finset.mem_range_succ_iff.1 hi), div_eq_inv_mul, mul_inv]
      ring
    _ = ∑ i ∈ Finset.range (n + 1), (n ! : ℝ) * 1 * C * D ^ (n + 1) * ((n - i)! : ℝ)⁻¹ := by
      congr! with i hi
      · exact inv_mul_cancel₀ (by positivity)
      · rw [← pow_add]
        congr 1
        rw [Nat.add_succ, Nat.succ_inj]
        exact Nat.add_sub_of_le (Finset.mem_range_succ_iff.1 hi)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n ! : ℝ) * 1 * C * D ^ (n + 1) * 1 := by
      gcongr with i
      apply inv_le_one_of_one_le₀
      simpa only [Nat.one_le_cast] using! (n - i).factorial_pos
    _ = (n + 1)! * C * D ^ (n + 1) := by
      simp only [mul_assoc, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.factorial_succ, Nat.cast_mul]

/-- If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`. -/
/-
**norm_iteratedFDerivWithin_comp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_comp_le {g : F -> G} {f : E -> F} {n : Nat} {s :
 Set E} {t : Set F} {x : E} {N : Nat∞ω} (hg : ContDiffOn 𝕜 N g t) (hf : ContDiff
On 𝕜 N f s) (hn : n <= N) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst :
 MapsTo f s t) (hx : x in s) {C : Real} {D : Real} (hC : forall i, i <= n -> ‖it
eratedFDerivWithin 𝕜 i g t (f x)‖ <= C) (hD : forall i, 1 <= i -> i <= n -> ‖ite
ratedFDerivWithin 𝕜 i f s x‖ <= D ^ i) : ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ 
<= n ! * C * D ^ n
参数：hg : ContDiffOn 𝕜 N g t；hf : ContDiffOn 𝕜 N f s；hn : n <= N；ht : UniqueDiffOn
 𝕜 t；hs : UniqueDiffOn 𝕜 s；hst : MapsTo f s t；hx : x in s；hC : forall i, i <= n 
-> ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ <= C；hD : forall i, 1 <= i -> i <= n -> 
‖iteratedFDerivWithin 𝕜 i f s x‖ <= D ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.uniqueDiffOn_preimage_iff`：ContinuousLinearEquiv.u
niqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) : UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiff
On 𝕜 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用定理 `ContDiffOn.comp_continuousLinearMap`：ContDiffOn.comp_continuousLinearMap
 (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E) : ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s)
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left`：LinearIsometryE
quiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (hs : Uni
queDiffOn 𝕜 s) (hx : x in s) (i : Nat) : ‖ite…
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right`：LinearIsometry
Equiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (hs : U
niqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `norm_iteratedFDerivWithin_comp_le_aux`：norm_iteratedFDerivWithin_comp_le
_aux {Fu Gu : Type u} [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommG
roup Gu] [NormedSpace 𝕜 Gu]…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-
th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`
-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`.
-/
theorem norm_iteratedFDerivWithin_comp_le {g : F → G} {f : E → F} {n : ℕ} {s : Set E} {t : Set F}
    {x : E} {N : ℕ∞ω} (hg : ContDiffOn 𝕜 N g t) (hf : ContDiffOn 𝕜 N f s) (hn : n ≤ N)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst : MapsTo f s t) (hx : x ∈ s) {C : ℝ}
    {D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * D ^ n := by
  /- We reduce the bound to the case where all spaces live in the same universe (in which we
    already have proved the result), by using linear isometries between the spaces and their `ULift`
    to a common universe. These linear isometries preserve the norm of the iterated derivative. -/
  let Fu : Type max uF uG := ULift.{uG, uF} F
  let Gu : Type max uF uG := ULift.{uF, uG} G
  have isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  have isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  -- lift `f` and `g` to versions `fu` and `gu` on the lifted spaces.
  let fu : E → Fu := isoF.symm ∘ f
  let gu : Fu → Gu := isoG.symm ∘ g ∘ isoF
  let tu := isoF ⁻¹' t
  have htu : UniqueDiffOn 𝕜 tu := isoF.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.2 ht
  have hstu : MapsTo fu s tu := fun y hy ↦ by
    simpa only [fu, tu, mem_preimage, comp_apply, LinearIsometryEquiv.apply_symm_apply] using hst hy
  have Ffu : isoF (fu x) = f x := by
    simp only [fu, comp_apply, LinearIsometryEquiv.apply_symm_apply]
  -- All norms are preserved by the lifting process.
  have hfu : ContDiffOn 𝕜 n fu s := isoF.symm.contDiff.comp_contDiffOn (hf.of_le hn)
  have hgu : ContDiffOn 𝕜 n gu tu :=
    isoG.symm.contDiff.comp_contDiffOn
      ((hg.of_le hn).comp_continuousLinearMap (isoF : Fu →L[𝕜] F))
  have Nfu : ∀ i, ‖iteratedFDerivWithin 𝕜 i fu s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := fun i ↦ by
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hs hx]
  simp_rw [← Nfu] at hD
  have Ngu : ∀ i,
      ‖iteratedFDerivWithin 𝕜 i gu tu (fu x)‖ = ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ := fun i ↦ by
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ htu (hstu hx)]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ ht, Ffu]
    rw [Ffu]
    exact hst hx
  simp_rw [← Ngu] at hC
  have Nfgu :
      ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 n (gu ∘ fu) s x‖ := by
    have : gu ∘ fu = isoG.symm ∘ g ∘ f := by
      ext x
      simp only [fu, gu, comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    rw [this, LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hs hx]
  -- deduce the required bound from the one for `gu ∘ fu`.
  rw [Nfgu]
  exact norm_iteratedFDerivWithin_comp_le_aux hgu hfu htu hs hstu hx hC hD

/-- If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`.

Version with the iterated derivative of `g` only bounded on the range of `f`. -/
/-
**norm_iteratedFDeriv_comp_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_comp_le' {g : F -> G} {f : E -> F} {n : Nat} {N : Nat∞
ω} {t : Set F} (ht : Set.range f subseteq t) (ht' : UniqueDiffOn 𝕜 t) (hg : Cont
DiffOn 𝕜 N g t) (hf : ContDiff 𝕜 N f) (hn : n <= N) (x : E) {C : Real} {D : Real
} (hC : forall i, i <= n -> ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ <= C) (hD : for
all i, 1 <= i -> i <= n -> ‖iteratedFDeriv 𝕜 i f x‖ <= D ^ i) : ‖iteratedFDeriv 
𝕜 n (g ∘ f) x‖ <= n ! * C * D ^ n
参数：ht : Set.range f subseteq t；ht' : UniqueDiffOn 𝕜 t；hg : ContDiffOn 𝕜 N g t；hf
 : ContDiff 𝕜 N f；hn : n <= N；x : E；hC : forall i, i <= n -> ‖iteratedFDerivWith
in 𝕜 i g t (f x)‖ <= C；hD : forall i, 1 <= i -> i <= n -> ‖iteratedFDeriv 𝕜 i f 
x‖ <= D ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `norm_iteratedFDerivWithin_comp_le`：norm_iteratedFDerivWithin_comp_le {g 
: F -> G} {f : E -> F} {n : Nat} {s : Set E} {t : Set F} {x : E} {N : Nat∞ω} (hg
 : ContDiffOn 𝕜 N g t) …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivativ
e
of `g ∘ f` is bounded by `n! * C * D^n`.

Version with the iterated derivative of `g` only bounded on the range of `f`.
-/
theorem norm_iteratedFDeriv_comp_le' {g : F → G} {f : E → F} {n : ℕ} {N : ℕ∞ω}
    {t : Set F} (ht : Set.range f ⊆ t) (ht' : UniqueDiffOn 𝕜 t)
    (hg : ContDiffOn 𝕜 N g t) (hf : ContDiff 𝕜 N f) (hn : n ≤ N) (x : E) {C : ℝ} {D : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ n ! * C * D ^ n := by
  simp_rw [← iteratedFDerivWithin_univ] at hD ⊢
  exact norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn hn ht' uniqueDiffOn_univ
    (by simp [mapsTo_iff_subset_preimage, ht]) (mem_univ x) hC hD

/-- If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`. -/
/-
**norm_iteratedFDeriv_comp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_comp_le {g : F -> G} {f : E -> F} {n : Nat} {N : Nat∞ω
} (hg : ContDiff 𝕜 N g) (hf : ContDiff 𝕜 N f) (hn : n <= N) (x : E) {C : Real} {
D : Real} (hC : forall i, i <= n -> ‖iteratedFDeriv 𝕜 i g (f x)‖ <= C) (hD : for
all i, 1 <= i -> i <= n -> ‖iteratedFDeriv 𝕜 i f x‖ <= D ^ i) : ‖iteratedFDeriv 
𝕜 n (g ∘ f) x‖ <= n ! * C * D ^ n
参数：hg : ContDiff 𝕜 N g；hf : ContDiff 𝕜 N f；hn : n <= N；x : E；hC : forall i, i <=
 n -> ‖iteratedFDeriv 𝕜 i g (f x)‖ <= C；hD : forall i, 1 <= i -> i <= n -> ‖iter
atedFDeriv 𝕜 i f x‖ <= D ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_iteratedFDeriv_comp_le'`：norm_iteratedFDeriv_comp_le' {g : F -> G} 
{f : E -> F} {n : Nat} {N : Nat∞ω} {t : Set F} (ht : Set.range f subseteq t) (ht
' : UniqueDiffOn 𝕜…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivativ
e
of `g ∘ f` is bounded by `n! * C * D^n`.
-/
theorem norm_iteratedFDeriv_comp_le {g : F → G} {f : E → F} {n : ℕ} {N : ℕ∞ω}
    (hg : ContDiff 𝕜 N g) (hf : ContDiff 𝕜 N f) (hn : n ≤ N) (x : E) {C : ℝ} {D : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ n ! * C * D ^ n := by
  simp_rw [← iteratedFDerivWithin_univ] at hC
  exact norm_iteratedFDeriv_comp_le' (subset_univ _) uniqueDiffOn_univ hg.contDiffOn hf hn x hC hD

section Apply

/-
**norm_iteratedFDerivWithin_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} {s 
: Set E} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffO
n 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hn : n <= N) : ‖iteratedFDeriv
Within 𝕜 n (fun y => (f y) (g y)) s x‖ <= ∑ i in Finset.range (n + 1), ↑(n.choos
e i) * ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖
参数：hf : ContDiffOn 𝕜 N f s；hg : ContDiffOn 𝕜 N g s；hs : UniqueDiffOn 𝕜 s；hx : x 
in s；hn : n <= N。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.opNorm_flip`：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃
] G) : ‖f.flip‖ = ‖f‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one`：
ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (B : E ->
L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} {N : Nat∞ω} {s : …
-/
theorem norm_iteratedFDerivWithin_clm_apply {f : E → F →L[𝕜] G} {g : E → F} {s : Set E} {x : E}
    {N : ℕ∞ω} {n : ℕ} (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => (f y) (g y)) s x‖ ≤
      ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  let B : (F →L[𝕜] G) →L[𝕜] F →L[𝕜] G := ContinuousLinearMap.flip (ContinuousLinearMap.apply 𝕜 G)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  exact B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf hg hs hx hn hB
/-
**norm_iteratedFDeriv_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} {N : Nat∞
ω} {n : Nat} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : E) (hn : n <= N) :
 ‖iteratedFDeriv 𝕜 n (fun y : E => (f y) (g y)) x‖ <= ∑ i in Finset.range (n + 1
), ↑(n.choose i) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖
参数：hf : ContDiff 𝕜 N f；hg : ContDiff 𝕜 N g；x : E；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `norm_iteratedFDerivWithin_clm_apply`：norm_iteratedFDerivWithin_clm_apply
 {f : E -> F ->L[𝕜] G} {g : E -> F} {s : Set E} {x : E} {N : Nat∞ω} {n : Nat} (h
f : ContDiffOn 𝕜 N f s) (…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem norm_iteratedFDeriv_clm_apply {f : E → F →L[𝕜] G} {g : E → F} {N : ℕ∞ω} {n : ℕ}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : E) (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y : E => (f y) (g y)) x‖ ≤ ∑ i ∈ Finset.range (n + 1),
      ↑(n.choose i) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_clm_apply hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ
    (Set.mem_univ x) hn
/-
**ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left (L : F ->L[𝕜] G) {
f : E -> F} {s : Set E} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDiffWithinAt 𝕜 N
 f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hn : n <= N) : ‖iteratedFDerivWit
hin 𝕜 n (L ∘ f) s x‖ <= ‖L‖ * ‖iteratedFDerivWithin 𝕜 n f s x‖
参数：L : F ->L[𝕜] G；hf : ContDiffWithinAt 𝕜 N f s x；hs : UniqueDiffOn 𝕜 s；hx : x i
n s；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`：norm_compConti
nuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) : 
‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
-/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left (L : F →L[𝕜] G) {f : E → F}
    {s : Set E} {x : E} {N : ℕ∞ω} {n : ℕ} (hf : ContDiffWithinAt 𝕜 N f s x)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (L ∘ f) s x‖ ≤ ‖L‖ * ‖iteratedFDerivWithin 𝕜 n f s x‖ := by
  have h := L.norm_compContinuousMultilinearMap_le (iteratedFDerivWithin 𝕜 n f s x)
  rwa [← L.iteratedFDerivWithin_comp_left hf hs hx hn] at h
/-
**ContinuousLinearMap.norm_iteratedFDeriv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L : F ->L[𝕜] G) {f : E 
-> F} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDiffAt 𝕜 N f x) (hn : n <= N) : ‖i
teratedFDeriv 𝕜 n (L ∘ f) x‖ <= ‖L‖ * ‖iteratedFDeriv 𝕜 n f x‖
参数：L : F ->L[𝕜] G；hf : ContDiffAt 𝕜 N f x；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left`：ContinuousLinea
rMap.norm_iteratedFDerivWithin_comp_left (L : F ->L[𝕜] G) {f : E -> F} {s : Set 
E} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDi…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L : F →L[𝕜] G) {f : E → F} {x : E}
    {N : ℕ∞ω} {n : ℕ} (hf : ContDiffAt 𝕜 N f x) (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (L ∘ f) x‖ ≤ ‖L‖ * ‖iteratedFDeriv 𝕜 n f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact L.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (Set.mem_univ x)
    hn
/-
**norm_iteratedFDerivWithin_clm_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDerivWithin_clm_apply_const {f : E -> F ->L[𝕜] G} {c : F} {s
 : Set E} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDiffWithinAt 𝕜 N f s x) (hs : 
UniqueDiffOn 𝕜 s) (hx : x in s) (hn : n <= N) : ‖iteratedFDerivWithin 𝕜 n (fun y
 : E => (f y) c) s x‖ <= ‖c‖ * ‖iteratedFDerivWithin 𝕜 n f s x‖
参数：hf : ContDiffWithinAt 𝕜 N f s x；hs : UniqueDiffOn 𝕜 s；hx : x in s；hn : n <= N
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
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
· 使用定理 `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left`：ContinuousLinea
rMap.norm_iteratedFDerivWithin_comp_left (L : F ->L[𝕜] G) {f : E -> F} {s : Set 
E} {x : E} {N : Nat∞ω} {n : Nat} (hf : ContDi…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.apply_apply`：apply_apply (v : E) (f : E ->L[𝕜] Fₗ) :
 apply 𝕜 Fₗ v f = f v
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem norm_iteratedFDerivWithin_clm_apply_const {f : E → F →L[𝕜] G} {c : F} {s : Set E} {x : E}
    {N : ℕ∞ω} {n : ℕ} (hf : ContDiffWithinAt 𝕜 N f s x) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) (hn : n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y : E => (f y) c) s x‖ ≤
      ‖c‖ * ‖iteratedFDerivWithin 𝕜 n f s x‖ := by
  apply ((ContinuousLinearMap.apply 𝕜 G c).norm_iteratedFDerivWithin_comp_left hf hs hx hn).trans
  gcongr
  refine (ContinuousLinearMap.apply 𝕜 G c).opNorm_le_bound (norm_nonneg _) fun f => ?_
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact f.le_opNorm c
/-
**norm_iteratedFDeriv_clm_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_clm_apply_const {f : E -> F ->L[𝕜] G} {c : F} {x : E} 
{N : Nat∞ω} {n : Nat} (hf : ContDiffAt 𝕜 N f x) (hn : n <= N) : ‖iteratedFDeriv 
𝕜 n (fun y : E => (f y) c) x‖ <= ‖c‖ * ‖iteratedFDeriv 𝕜 n f x‖
参数：hf : ContDiffAt 𝕜 N f x；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `norm_iteratedFDerivWithin_clm_apply_const`：norm_iteratedFDerivWithin_clm
_apply_const {f : E -> F ->L[𝕜] G} {c : F} {s : Set E} {x : E} {N : Nat∞ω} {n : 
Nat} (hf : ContDiffWithinAt 𝕜 N…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem norm_iteratedFDeriv_clm_apply_const {f : E → F →L[𝕜] G} {c : F} {x : E}
    {N : ℕ∞ω} {n : ℕ} (hf : ContDiffAt 𝕜 N f x) (hn : n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y : E => (f y) c) x‖ ≤ ‖c‖ * ‖iteratedFDeriv 𝕜 n f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_clm_apply_const hf.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ x) hn

end Apply

