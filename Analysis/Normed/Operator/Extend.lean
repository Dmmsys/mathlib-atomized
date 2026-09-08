/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend `f : E →SL[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map that is `IsUniformInducing`.
* `LinearMap.extendOfNorm`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.

Moreover, we can extend a linear equivalence:
* `LinearEquiv.extend`: Extend a linear equivalence between normed spaces to a continuous linear
  equivalence between Banach spaces with two dense maps `e₁` and `e₂` and the corresponding norm
  estimates.
* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
  `Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Banach spaces
  and `f` preserves the norm.

-/

@[expose] public section

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`. -/
/-
**ContinuousLinearMap.extend** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：extend : Eₗ ->SL[σ₁₂] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space
 and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`.
-/
def extend : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.uniformContinuous
  { toFun := (h.2.isDenseInducing h.1).extend f
    map_add' := by
      refine h.1.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h.1.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact map_smulₛₗ _ _ _
    cont }
  else 0

variable {e}

@[simp]
/-
**ContinuousLinearMap.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) : e
xtend f e (e x) = f x
参数：h_dense : DenseRange e；h_e : IsUniformInducing e；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
-/
theorem extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) :
    extend f e (e x) = f x := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _
/-
**ContinuousLinearMap.extend_unique** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ
 ->SL[σ₁₂] F) (H : g.comp e = f) : extend f e = g
参数：h_dense : DenseRange e；h_e : IsUniformInducing e；g : Eₗ ->SL[σ₁₂] F；H : g.com
p e = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ContinuousLinearMap.coeFn_injective`：coeFn_injective : @Function.Injecti
ve (M₁ ->SL[σ₁₂] M₂) (M₁ -> M₂) (↑)
· 使用定理 `uniformly_extend_unique`：uniformly_extend_unique {g : α -> γ} (hg : fora
ll b, g (e b) = f b) (hc : Continuous g) : ψ = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ →SL[σ₁₂] F)
    (H : g.comp e = f) : extend f e = g := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
  exact ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
/-
**ContinuousLinearMap.extend_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) : extend 
(0 : E ->SL[σ₁₂] F) e = 0
参数：h_dense : DenseRange e；h_e : IsUniformInducing e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.extend_unique`：extend_unique (h_dense : DenseRange e
) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F) (H : g.comp e = f) : extend f
 e = g
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
-/
theorem extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    extend (0 : E →SL[σ₁₂] F) e = 0 :=
  extend_unique _ h_dense h_e _ (zero_comp _)

end Ring

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) {e : E →L[𝕜] Eₗ}

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : ℝ≥0} [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
/-
**ContinuousLinearMap.opNorm_extend_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opNorm_extend_le (h_dense : DenseRange e) (h_e : forall x, ‖x‖ <= N * ‖e x
‖) : ‖f.extend e‖ <= N * ‖f‖
参数：h_dense : DenseRange e；h_e : forall x, ‖x‖ <= N * ‖e x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
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
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`
, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`.
-/
theorem opNorm_extend_le (h_dense : DenseRange e) (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) :
    ‖f.extend e‖ ≤ N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · rw [extend_eq _ h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := by gcongr; exact h_e x
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Composition of a semilinear map `f` with the left inverse of a linear map `g` as a continuous
linear map provided that the norm estimate `‖f x‖ ≤ C * ‖g x‖` holds for all `x : E`. -/
/-
**LinearMap.compLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compLeftInverse : range g ->SL[σ₁₂] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a semilinear map `f` with the left inverse of a linear map `g` as
 a continuous
linear map provided that the norm estimate `‖f x‖ ≤ C * ‖g x‖` holds for all `x 
: E`.
-/
def compLeftInverse : range g →SL[σ₁₂] F :=
  if h : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖ then
  (((LinearMap.ker g).liftQ f (by
    obtain ⟨C, h⟩ := h
    intro x hx
    specialize h x
    rw [hx] at h
    simpa using h)).comp
    g.quotKerEquivRange.symm.toLinearMap).mkContinuousOfExistsBound
  (by
    obtain ⟨C, h⟩ := h
    use C
    intro ⟨x, y, hxy⟩
    simpa [← hxy] using h y)
  else 0
/-
**LinearMap.compLeftInverse_apply_of_bdd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compLeftInverse_apply_of_bdd (h_norm : exists (C : Real), forall (x : E), 
‖f x‖ <= C * ‖g x‖) (x : E) (y : Eₗ) (hx : g x = y) : f.compLeftInverse g ⟨y, ⟨x
, hx⟩⟩ = f x
参数：h_norm : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖；x : E；y : Eₗ；h
x : g x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `LinearMap.quotKerEquivRange_symm_apply_image`：quotKerEquivRange_symm_app
ly_image (x : M) (h : f x in LinearMap.range f) : f.quotKerEquivRange.symm ⟨f x,
 h⟩ = (LinearMap.ker f).mkQ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compLeftInverse_apply_of_bdd (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖)
    (x : E) (y : Eₗ) (hx : g x = y) :
    f.compLeftInverse g ⟨y, ⟨x, hx⟩⟩ = f x := by
  simp [compLeftInverse, h_norm, ← hx]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

/-- Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`. -/
/-
**LinearMap.extendOfNorm** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：extendOfNorm : Eₗ ->SL[σ₁₂] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[
σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `
e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.
-/
def extendOfNorm : Eₗ →SL[σ₁₂] F := (f.compLeftInverse e).extend (LinearMap.range e).subtypeL

variable {f e}
/-
**LinearMap.extendOfNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：extendOfNorm_eq (h_dense : DenseRange e) (h_norm : exists C, forall x, ‖f 
x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) = f x
参数：h_dense : DenseRange e；h_norm : exists C, forall x, ‖f x‖ <= C * ‖e x‖；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
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
· 使用定理 `ContinuousLinearMap.extend_eq`：extend_eq (h_dense : DenseRange e) (h_e :
 IsUniformInducing e) (x : E) : extend f e (e x) = f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.compLeftInverse_apply_of_bdd`：compLeftInverse_apply_of_bdd (h_
norm : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖) (x : E) (y : Eₗ) (
hx : g x = y) : f.compLeftIn…
-/
theorem extendOfNorm_eq (h_dense : DenseRange e) (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖)
    (x : E) : f.extendOfNorm e (e x) = f x := by
  have := (f.compLeftInverse e).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ h_norm _ _ rfl).symm
/-
**LinearMap.norm_extendOfNorm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：norm_extendOfNorm_apply_le (h_dense : DenseRange e) (C : Real) (h_norm : f
orall (x : E), ‖f x‖ <= C * ‖e x‖) (x : Eₗ) : ‖f.extendOfNorm e x‖ <= C * ‖x‖
参数：h_dense : DenseRange e；C : Real；h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖；x
 : Eₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
· 使用引理 `Dense.induction`：Dense.induction (hs : Dense s) {P : X -> Prop} (mem : f
orall x in s, P x) (isClosed : IsClosed { x | P x }) (x : X) : P x
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem norm_extendOfNorm_apply_le (h_dense : DenseRange e) (C : ℝ)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : Eₗ) :
    ‖f.extendOfNorm e x‖ ≤ C * ‖x‖ := by
  have h_mem : ∀ (x : Eₗ) (hy : x ∈ (LinearMap.range e)), ‖extendOfNorm f e x‖ ≤ C * ‖x‖ := by
    intro x ⟨y, hxy⟩
    simpa only [← hxy, extendOfNorm_eq h_dense ⟨C, h_norm⟩ y] using h_norm y
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x
/-
**LinearMap.extendOfNorm_unique** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：extendOfNorm_unique (h_dense : DenseRange e) (C : Real) (h_norm : forall (
x : E), ‖f x‖ <= C * ‖e x‖) (g : Eₗ ->SL[σ₁₂] F) (H : g.toLinearMap.comp e = f) 
: extendOfNorm f e = g
参数：h_dense : DenseRange e；C : Real；h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖；g
 : Eₗ ->SL[σ₁₂] F；H : g.toLinearMap.comp e = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.extend_unique`：extend_unique (h_dense : DenseRange e
) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F) (H : g.comp e = f) : extend f
 e = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `LinearMap.compLeftInverse_apply_of_bdd`：compLeftInverse_apply_of_bdd (h_
norm : exists (C : Real), forall (x : E), ‖f x‖ <= C * ‖g x‖) (x : E) (y : Eₗ) (
hx : g x = y) : f.compLeftIn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendOfNorm_unique (h_dense : DenseRange e) (C : ℝ) (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖)
    (g : Eₗ →SL[σ₁₂] F) (H : g.toLinearMap.comp e = f) : extendOfNorm f e = g := by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ ⟨C, h_norm⟩ x y hxy]
  simp [← hxy, ← H]

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ}

/-
**LinearMap.opNorm_extendOfNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：opNorm_extendOfNorm_le (h_dense : DenseRange e) {C : Real} (hC : 0 <= C) (
h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) : ‖f.extendOfNorm e‖ <= C
参数：h_dense : DenseRange e；hC : 0 <= C；h_norm : forall (x : E), ‖f x‖ <= C * ‖e x
‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `LinearMap.norm_extendOfNorm_apply_le`：norm_extendOfNorm_apply_le (h_dens
e : DenseRange e) (C : Real) (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) (x : 
Eₗ) : ‖f.extendOfNorm e x‖…
-/
theorem opNorm_extendOfNorm_le (h_dense : DenseRange e) {C : ℝ} (hC : 0 ≤ C)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm e‖ ≤ C :=
  (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

end NormedField

end LinearMap

namespace LinearEquiv

section extend

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [NormedAddCommGroup Eₗ] [AddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ] [Module 𝕜₂ F] [Module 𝕜₂ Fₗ] [IsBoundedSMul 𝕜₂ Fₗ]
  [CompleteSpace Eₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of a linear equivalence `f : E ≃ₛₗ[σ₁₂] F` to a continuous linear equivalence
`Eₗ ≃SL[σ₁₂] Fₗ`, where `E` and `F` are normed spaces and `Eₗ` and `Fₗ` are Banach spaces,
using dense maps `e₁ : E →ₗ[𝕜₁] Eₗ` and `e₂ : F →ₗ[𝕜₂] F₂` together with bounds
`‖e₂ (f x)‖ ≤ C * ‖e₁ x‖` for all `x : E` and `‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖` for all `x : F`. -/
/-
**LinearEquiv.extend** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：extend (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f x)
‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e₁ (
f.symm x)‖ <= C * ‖e₂ x‖) : Eₗ ≃SL[σ₁₂] Fₗ where __
参数：h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ 
x‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C *
 ‖e₂ x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of a linear equivalence `f : E ≃ₛₗ[σ₁₂] F` to a continuous linear equi
valence
`Eₗ ≃SL[σ₁₂] Fₗ`, where `E` and `F` are normed spaces and `Eₗ` and `Fₗ` are Bana
ch spaces,
using dense maps `e₁ : E →ₗ[𝕜₁] Eₗ` and `e₂ : F →ₗ[𝕜₂] F₂` together with bounds
`‖e₂ (f x)‖ ≤ C * ‖e₁ x‖` for all `x : E` and `‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖` for
 all `x : F`.
-/
def extend (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) :
    Eₗ ≃SL[σ₁₂] Fₗ where
  __ := (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    refine h_dense₁.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  right_inv := by
    refine h_dense₂.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  continuous_invFun := ContinuousLinearMap.continuous _
/-
**LinearEquiv.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extend_apply (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂
 (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x,
 ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Eₗ) : (f.extend e₁ e₂ h_dense₁ h_norm₁ h_de
nse₂ h_norm₂) x = (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x
参数：h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ 
x‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C *
 ‖e₂ x‖；x : Eₗ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extend_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Eₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl
/-
**LinearEquiv.extend_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extend_symm_apply (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x
, ‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, fora
ll x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Fₗ) : (f.extend e₁ e₂ h_dense₁ h_norm₁
 h_dense₂ h_norm₂).symm x = (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x
参数：h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ 
x‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C *
 ‖e₂ x‖；x : Fₗ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extend_symm_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Fₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
/-
**LinearEquiv.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extend_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖e₂ (f
 x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall x, ‖e
₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : E) : f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ 
h_norm₂ (e₁ x) = e₂ (f x)
参数：h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ 
x‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C *
 ‖e₂ x‖；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
-/
theorem extend_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : E) :
    f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂ (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ h_norm₁ x

@[simp]
/-
**LinearEquiv.extend_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extend_symm_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : exists C, forall x, ‖
e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall 
x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : F) : (f.extend e₁ e₂ h_dense₁ h_norm₁ h_d
ense₂ h_norm₂).symm (e₂ x) = e₁ (f.symm x)
参数：h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ 
x‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C *
 ‖e₂ x‖；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
-/
theorem extend_symm_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : F) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm (e₂ x) = e₁ (f.symm x) :=
  LinearMap.extendOfNorm_eq h_dense₂ h_norm₂ x
/-
**LinearEquiv.norm_extend_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：norm_extend_le (C : Real) (h_dense₁ : DenseRange e₁) (h_norm₁ : forall x, 
‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : exists C, forall
 x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Eₗ) : ‖(f.extend e₁ e₂ h_dense₁ ⟨C, h_no
rm₁⟩ h_dense₂ h_norm₂) x‖ <= C * ‖x‖
参数：C : Real；h_dense₁ : DenseRange e₁；h_norm₁ : forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x
‖；h_dense₂ : DenseRange e₂；h_norm₂ : exists C, forall x, ‖e₁ (f.symm x)‖ <= C * 
‖e₂ x‖；x : Eₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.norm_extendOfNorm_apply_le`：norm_extendOfNorm_apply_le (h_dens
e : DenseRange e) (C : Real) (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) (x : 
Eₗ) : ‖f.extendOfNorm e x‖…
-/
theorem norm_extend_le (C : ℝ) (h_dense₁ : DenseRange e₁) (h_norm₁ : ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Eₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ ⟨C, h_norm₁⟩ h_dense₂ h_norm₂) x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₁ _ h_norm₁ _
/-
**LinearEquiv.norm_extend_symm_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：norm_extend_symm_le (C : Real) (h_dense₁ : DenseRange e₁) (h_norm₁ : exist
s C, forall x, ‖e₂ (f x)‖ <= C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂) (h_norm₂ : f
orall x, ‖e₁ (f.symm x)‖ <= C * ‖e₂ x‖) (x : Fₗ) : ‖(f.extend e₁ e₂ h_dense₁ h_n
orm₁ h_dense₂ ⟨C, h_norm₂⟩).symm x‖ <= C * ‖x‖
参数：C : Real；h_dense₁ : DenseRange e₁；h_norm₁ : exists C, forall x, ‖e₂ (f x)‖ <=
 C * ‖e₁ x‖；h_dense₂ : DenseRange e₂；h_norm₂ : forall x, ‖e₁ (f.symm x)‖ <= C * 
‖e₂ x‖；x : Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.norm_extendOfNorm_apply_le`：norm_extendOfNorm_apply_le (h_dens
e : DenseRange e) (C : Real) (h_norm : forall (x : E), ‖f x‖ <= C * ‖e x‖) (x : 
Eₗ) : ‖f.extendOfNorm e x‖…
-/
theorem norm_extend_symm_le (C : ℝ) (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Fₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ ⟨C, h_norm₂⟩).symm x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₂ _ h_norm₂ _

end extend

section extendOfIsometry

variable [NormedField 𝕜] [NormedField 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [CompleteSpace Eₗ]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

/-- Extend a densely defined operator that preserves the norm to a linear isometry equivalence. -/
/-
**LinearEquiv.extendOfIsometry** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：extendOfIsometry (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂) (h_
norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) : Eₗ ≃ₛₗᵢ[σ₁₂] Fₗ
参数：h_dense₁ : DenseRange e₁；h_dense₂ : DenseRange e₂；h_norm : forall x, ‖e₂ (f x
)‖ = ‖e₁ x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a densely defined operator that preserves the norm to a linear isometry e
quivalence.
-/
def extendOfIsometry (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) :
    Eₗ ≃ₛₗᵢ[σ₁₂] Fₗ :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ := fun x ↦ by simpa using (h_norm (f.symm x)).symm
  { __ := f.extend e₁ e₂ h_dense₁ ⟨1, by simp [h_norm]⟩ h_dense₂ ⟨1, by simp [h_norm₂]⟩
    norm_map' := by
      refine h_dense₁.induction ?_ (isClosed_eq (by
        simp only [ContinuousLinearEquiv.coe_toLinearEquiv]; fun_prop) continuous_norm)
      rintro x ⟨y, rfl⟩
      convert! h_norm y
      apply LinearMap.extendOfNorm_eq h_dense₁ (by use 1; simp [h_norm]) }
/-
**LinearEquiv.extendOfIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extendOfIsometry_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e
₂) (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Eₗ) : (f.extendOfIsometry e₁ e₂
 h_dense₁ h_dense₂ h_norm) x = (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x
参数：h_dense₁ : DenseRange e₁；h_dense₂ : DenseRange e₂；h_norm : forall x, ‖e₂ (f x
)‖ = ‖e₁ x‖；x : Eₗ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendOfIsometry_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Eₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl
/-
**LinearEquiv.extendOfIsometry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv
`。
形式化陈述：extendOfIsometry_symm_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRa
nge e₂) (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Fₗ) : (f.extendOfIsometry 
e₁ e₂ h_dense₁ h_dense₂ h_norm).symm x = (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNor
m e₂ x
参数：h_dense₁ : DenseRange e₁；h_dense₂ : DenseRange e₂；h_norm : forall x, ‖e₂ (f x
)‖ = ‖e₁ x‖；x : Fₗ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendOfIsometry_symm_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Fₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
/-
**LinearEquiv.extendOfIsometry_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extendOfIsometry_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂) 
(h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : E) : f.extendOfIsometry e₁ e₂ h_de
nse₁ h_dense₂ h_norm (e₁ x) = e₂ (f x)
参数：h_dense₁ : DenseRange e₁；h_dense₂ : DenseRange e₂；h_norm : forall x, ‖e₂ (f x
)‖ = ‖e₁ x‖；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem extendOfIsometry_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : E) :
    f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x ↦ by simp [h_norm x]⟩ x

@[simp]
/-
**LinearEquiv.extendOfIsometry_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：extendOfIsometry_symm_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange
 e₂) (h_norm : forall x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : F) : (f.extendOfIsometry e₁ e
₂ h_dense₁ h_dense₂ h_norm).symm (e₂ x) = e₁ (f.symm x)
参数：h_dense₁ : DenseRange e₁；h_dense₂ : DenseRange e₂；h_norm : forall x, ‖e₂ (f x
)‖ = ‖e₁ x‖；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem extendOfIsometry_symm_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : F) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm (e₂ x) = e₁ (f.symm x) :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x ↦ by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x ↦ by simp [h_norm₂ x]⟩ x

end extendOfIsometry

end LinearEquiv

