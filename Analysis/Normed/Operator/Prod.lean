/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Operator norm: Cartesian products

Interaction of operator norm with Cartesian products.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]

open Set Real Metric ContinuousLinearMap

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/-- The operator norm of the first projection `E × F → E` is at most 1. (It is 0 if `E` is zero, so
the inequality cannot be improved without further assumptions.) -/
/-
**ContinuousLinearMap.norm_fst_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：norm_fst_le : ‖fst 𝕜 E F‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
The operator norm of the first projection `E × F → E` is at most 1. (It is 0 if 
`E` is zero, so
the inequality cannot be improved without further assumptions.)
-/
lemma norm_fst_le : ‖fst 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using! le_max_left ‖e‖ ‖f‖)

/-- The operator norm of the second projection `E × F → F` is at most 1. (It is 0 if `F` is zero, so
the inequality cannot be improved without further assumptions.) -/
/-
**ContinuousLinearMap.norm_snd_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：norm_snd_le : ‖snd 𝕜 E F‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
The operator norm of the second projection `E × F → F` is at most 1. (It is 0 if
 `F` is zero, so
the inequality cannot be improved without further assumptions.)
-/
lemma norm_snd_le : ‖snd 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using! le_max_right ‖e‖ ‖f‖)

end FirstSecond

section OpNorm

@[simp]
/-
**ContinuousLinearMap.opNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：opNorm_prod (f : E ->L[𝕜] F) (g : E ->L[𝕜] G) : ‖f.prod g‖ = ‖(f, g)‖
参数：f : E ->L[𝕜] F；g : E ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem opNorm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ‖f.prod g‖ = ‖(f, g)‖ :=
  le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_opNorm f x) (le_opNorm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans ((f.prod g).le_opNorm x))
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_right _ _).trans ((f.prod g).le_opNorm x))


@[simp]
/-
**ContinuousLinearMap.opNNNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNNNorm_prod (f : E ->L[𝕜] F) (g : E ->L[𝕜] G) : ‖f.prod g‖₊ = ‖(f, g)‖₊
参数：f : E ->L[𝕜] F；g : E ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ContinuousLinearMap.opNorm_prod`：opNorm_prod (f : E ->L[𝕜] F) (g : E ->L
[𝕜] G) : ‖f.prod g‖ = ‖(f, g)‖
-/
theorem opNNNorm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ‖f.prod g‖₊ = ‖(f, g)‖₊ :=
  Subtype.ext <| opNorm_prod f g


/-- `ContinuousLinearMap.prod` as a `LinearIsometryEquiv`. -/
/-
**ContinuousLinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {M₁ : Type u_2} →       [inst
_1 : TopologicalSpace M₁] →         [inst_2 : AddCommMonoid M₁] →           [ins
t_3 : _root_.Module R M₁] →             {M₂ : Type u_3} →               [inst_4 
: TopologicalSpace M₂] →                 [inst_5 : AddCommMonoid M₂] →          
         [inst_6 : _root_.Module R M₂] →                     {M₃ : Type u_4} →  
                     [inst_7 : TopologicalSpace M₃] →                         [i
nst_8 : AddCommMonoid M₃] →                           [inst_9 : _root_.Module R 
M₃] → (M₁ →L[R] M₂) → (M₁ →L[R] M₃) → M₁ →L[R] M₂ × M₃
参数：M₁ →L[R] M₂；M₁ →L[R] M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.prod` as a `LinearIsometryEquiv`.
-/
noncomputable def prodₗᵢ (R : Type*)
    [Semiring R] [Module R F] [Module R G] [ContinuousConstSMul R F]
    [ContinuousConstSMul R G] [SMulCommClass 𝕜 R F] [SMulCommClass 𝕜 R G] :
    (E →L[𝕜] F) × (E →L[𝕜] G) ≃ₗᵢ[R] E →L[𝕜] F × G :=
  ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩

end OpNorm


section Prod

variable (𝕜)
variable (M₁ M₂ M₃ M₄ : Type*)
  [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁]
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂]
  [SeminormedAddCommGroup M₃] [NormedSpace 𝕜 M₃]
  [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

/-- `ContinuousLinearMap.prodMap` as a continuous linear map. -/
/-
**ContinuousLinearMap.prodMapL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：prodMapL : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₁ × M₃ ->L[𝕜] M₂ × M₄
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
`ContinuousLinearMap.prodMap` as a continuous linear map.
-/
noncomputable def prodMapL : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ × M₃ →L[𝕜] M₂ × M₄ :=
  ContinuousLinearMap.copy
    (have Φ₁ : (M₁ →L[𝕜] M₂) →L[𝕜] M₁ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜 M₂ M₄)
    have Φ₁' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₁ (M₂ × M₄)).flip (ContinuousLinearMap.fst 𝕜 M₁ M₃)
    have Φ₂' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₃ (M₂ × M₄)).flip (ContinuousLinearMap.snd 𝕜 M₁ M₃)
    have Ψ₁ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ →L[𝕜] M₂ :=
      ContinuousLinearMap.fst 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    have Ψ₂ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₄ :=
      ContinuousLinearMap.snd 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂)
    (fun p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) => p.1.prodMap p.2) (by
      apply funext
      rintro ⟨φ, ψ⟩
      refine ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ => ?_
      simp)

variable {M₁ M₂ M₃ M₄}

@[simp]
/-
**ContinuousLinearMap.prodMapL_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：prodMapL_apply (p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄)) : ContinuousLinearMap
.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.prodMap p.2
参数：p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem prodMapL_apply (p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄)) :
    ContinuousLinearMap.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.prodMap p.2 :=
  rfl

variable {X : Type*} [TopologicalSpace X]
/-
**ContinuousLinearMap._root_.Continuous.prod_mapL** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).prodMap (g x) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)
/-
**ContinuousLinearMap._root_.Continuous.prod_map_equivL** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄}
    (hf : Continuous fun x => (f x : M₁ →L[𝕜] M₂)) (hg : Continuous fun x => (g x : M₃ →L[𝕜] M₄)) :
    Continuous fun x => ((f x).prodCongr (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)
/-
**ContinuousLinearMap._root_.ContinuousOn.prod_mapL** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).prodMap (g x)) s :=
  ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prodMk hg) :)
/-
**ContinuousLinearMap._root_.ContinuousOn.prod_map_equivL** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn (fun x => (f x : M₁ →L[𝕜] M₂)) s)
    (hg : ContinuousOn (fun x => (g x : M₃ →L[𝕜] M₄)) s) :
    ContinuousOn (fun x => ((f x).prodCongr (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄)) s :=
  hf.prod_mapL _ hg

end Prod

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/-- The operator norm of the first projection `E × F → E` is exactly 1 if `E` is nontrivial. -/
/-
**ContinuousLinearMap.norm_fst** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : S
eminormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [Nontrivial E],   ‖Continuou
sLinearMap.fst 𝕜 E F‖ = 1
参数：𝕜 : Type u_1；E : Type u_2；F : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ContinuousLinearMap.norm_fst_le`：norm_fst_le : ‖fst 𝕜 E F‖ <= 1
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Z
ero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α] [MulPosReflectLE α],   0
 < a → (b * a ≤ c…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0

--- 原说明 ---
The operator norm of the first projection `E × F → E` is exactly 1 if `E` is non
trivial.
-/
@[simp] lemma norm_fst [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial E] :
    ‖fst 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_fst_le ..) ?_
  let ⟨e, he⟩ := exists_ne (0 : E)
  have : ‖e‖ ≤ _ * max ‖e‖ ‖(0 : F)‖ := (fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero, max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]

/-- The operator norm of the second projection `E × F → F` is exactly 1 if `F` is nontrivial. -/
/-
**ContinuousLinearMap.norm_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [Nontrivial F],   ‖Continuou
sLinearMap.snd 𝕜 E F‖ = 1
参数：𝕜 : Type u_1；E : Type u_2；F : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ContinuousLinearMap.norm_snd_le`：norm_snd_le : ‖snd 𝕜 E F‖ <= 1
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Z
ero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α] [MulPosReflectLE α],   0
 < a → (b * a ≤ c…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0

--- 原说明 ---
The operator norm of the second projection `E × F → F` is exactly 1 if `F` is no
ntrivial.
-/
@[simp] lemma norm_snd [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial F] :
    ‖snd 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_snd_le ..) ?_
  let ⟨f, hf⟩ := exists_ne (0 : F)
  have : ‖f‖ ≤ _ * max ‖(0 : E)‖ ‖f‖ := (snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero, max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]

end FirstSecond

end ContinuousLinearMap

end Normed

