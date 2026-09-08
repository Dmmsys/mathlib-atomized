/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic.Positivity.Finset

/-! # Hölder's inequality for `lp` spaces

This file proves Hölder's inequality for `lp` spaces. We follow the established pattern for
Hölder's inequality for `MeasureTheory.Lp` of generalizing multiplication to any continuous bilinear
map. Since `lp` is a dependent Π-type, we actually need a uniformly bounded family of bilinear maps.

## Implementation notes

Although it would be possible to bundle the uniformly bounded family of bilinear maps into a term
`B : lp (fun i ↦ E i →L[𝕜] F i →L[𝕜] G i) ∞`, this has some downsides. For example, we would
then have to bundle `fun i ↦ (B i).flip` into a term of this type in order to use it, so we opt to
leave `B` unbundled.

-/

@[expose] public section

open scoped lp ENNReal NNReal

namespace lp
-- the material in this section could be moved to `lpSpace`, but would require some extra imports

section NontriviallyNormedField

variable {α 𝕜 : Type*} {E F : α → Type*} [NontriviallyNormedField 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
variable {p q r : ℝ≥0∞}

set_option backward.isDefEq.respectTransparency.types false in
/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space. -/
@[simps!]
/-
**lp.mapCLM** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：mapCLM (p : Real>=0∞) [Fact (1 <= p)] (T : forall i, E i ->L[𝕜] F i) {K : 
Real} (hK : 0 <= K) (hTK : forall i, ‖T i‖ <= K) : lp E p ->L[𝕜] lp F p
参数：p : Real>=0∞；1 <= p；T : forall i, E i ->L[𝕜] F i；hK : 0 <= K；hTK : forall i, 
‖T i‖ <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space.
-/
noncomputable def mapCLM (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    lp E p →L[𝕜] lp F p :=
  haveI key (i : α) (x : E i) : ‖T i x‖ ≤ K * ‖x‖ := (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i ↦ T i (⇑x i), lp.memℓp x |>.norm.const_mul K |>.mono
        (fun _ ↦ by simpa [abs_of_nonneg hK] using key ..) |>.of_norm⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    K
    fun x ↦ by
      rw [← norm_toNorm]
      conv_rhs => rw [← norm_toNorm, ← abs_of_nonneg hK, ← Real.norm_eq_abs, ← norm_smul]
      apply norm_mono (zero_lt_one.trans_le Fact.out).ne' fun i ↦ ?_
      simpa [abs_of_nonneg hK] using key ..
/-
**lp.norm_mapCLM_le** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_mapCLM_le (p : Real>=0∞) [Fact (1 <= p)] (T : forall i, E i ->L[𝕜] F 
i) {K : Real} (hK : 0 <= K) (hTK : forall i, ‖T i‖ <= K) : ‖mapCLM p T hK hTK‖ <
= K
参数：p : Real>=0∞；1 <= p；T : forall i, E i ->L[𝕜] F i；hK : 0 <= K；hTK : forall i, 
‖T i‖ <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
-/
lemma norm_mapCLM_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    ‖mapCLM p T hK hTK‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ hK _

end NontriviallyNormedField

/-
**lp.norm_tsumCLM_le** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_tsumCLM_le {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddComm
Group E] [NormedSpace 𝕜 E] [CompleteSpace E] : ‖tsumCLM 𝕜 α E‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma norm_tsumCLM_le {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    ‖tsumCLM 𝕜 α E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end lp

variable {ι 𝕜 : Type*} {E F G : ι → Type*} [RCLike 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]

open ENNReal

variable {p q : ℝ≥0∞} (r : ℝ≥0∞) [hpqr : p.HolderTriple q r]

namespace Memℓp

/-
**Memℓp.bilin_of_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：bilin_of_top_left (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (h
BK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F i} (he : Memℓp e ∞) (hf : 
Memℓp f q) : Memℓp (fun i => B i (e i) (f i)) q
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <= K；he : Memℓ
p e ∞；hf : Memℓp f q。
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
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Memℓp.all`：Memℓp.all [Finite α] (f : forall i, E i) : Memℓp f p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Memℓp.mono`：mono {f : (i : α) -> E i} {g : α -> Real} (hg : Memℓp g p) (
hfg : forall i, ‖f i‖ <= g i) : Memℓp f p
· 使用定理 `Memℓp.const_mul`：const_mul {f : α -> 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp
 (fun x => c * f x) p
· 使用定理 `Memℓp.norm`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i
 : α) → NormedAddCommGroup (E i)] {f : (i : α) → E i},   Memℓp f p → Memℓp (fun 
…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem bilin_of_top_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e ∞) (hf : Memℓp f q) :
    Memℓp (fun i ↦ B i (e i) (f i)) q := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
  refine hf.norm.const_mul (K * C) |>.mono fun i ↦ ?_
  have hK_nonneg : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  calc
    ‖B i (e i) (f i)‖ ≤ ‖B i‖ * ‖e i‖ * ‖f i‖ := (B i (e i)).le_of_opNorm_le ((B i).le_opNorm _) _
    _ ≤ K * C * ‖f i‖ := by gcongr; exacts [hBK i, hC i]
/-
**Memℓp.bilin_of_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：bilin_of_top_right (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (
hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F i} (he : Memℓp e p) (hf :
 Memℓp f ∞) : Memℓp (fun i => B i (e i) (f i)) p
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <= K；he : Memℓ
p e p；hf : Memℓp f ∞。
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
· 使用定理 `Memℓp.bilin_of_top_left`：bilin_of_top_left (B : (i : ι) -> E i ->L[𝕜] F 
i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F
 i} (he : Mem…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_flip`：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃
] G) : ‖f.flip‖ = ‖f‖
-/
theorem bilin_of_top_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e p) (hf : Memℓp f ∞) :
    Memℓp (fun i ↦ B i (e i) (f i)) p :=
  hf.bilin_of_top_left (fun i ↦ (B i).flip) (by simpa using hBK) he
/-
**Memℓp.bilin_of_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：bilin_of_zero_left (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {e : Π i, E 
i} {f : Π i, F i} (he : Memℓp e 0) : Memℓp (fun i => B i (e i) (f i)) 0
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；he : Memℓp e 0。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `memℓp_zero_iff`：memℓp_zero_iff {f : forall i, E i} : Memℓp f 0 ↔ Set.Fin
ite { i | f i != 0 }
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bilin_of_zero_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 := by
  rw [memℓp_zero_iff] at he ⊢
  exact he.subset fun i hi h ↦ hi <| by simp [h]
/-
**Memℓp.bilin_of_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：bilin_of_zero_right (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {e : Π i, E
 i} {f : Π i, F i} (hf : Memℓp f 0) : Memℓp (fun i => B i (e i) (f i)) 0
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hf : Memℓp f 0。
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
· 使用定理 `Memℓp.bilin_of_zero_left`：bilin_of_zero_left (B : (i : ι) -> E i ->L[𝕜] 
F i ->L[𝕜] G i) {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) : Memℓp (fun i =>
 B i (e i) (f …
-/
theorem bilin_of_zero_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (hf : Memℓp f 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 :=
  hf.bilin_of_zero_left (fun i ↦ (B i).flip)
/-
**Memℓp.holder_top_left_bound** 是 Mathlib 中的一个引理，位于命名空间 `Memℓp`。
形式化陈述：holder_top_left_bound {e : (i : ι) -> E i} {f : (i : ι) -> F i} (B : (i : 
ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K C D : Real} (hBK : forall i, ‖B i‖ <= K) (hK
 : 0 <= K) (hC : 0 <= C) (hCe : forall i, ‖e i‖ <= C) (hDf : forall s, ∑ i in s,
 ‖f i‖ ^ q.toReal <= D) (s : Finset ι) : ∑ i in s, ‖B i (e i) (f i)‖ ^ q.toReal 
<= (K * C) ^ q.toReal * D
参数：i : ι；i : ι；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <=
 K；hK : 0 <= K；hC : 0 <= C；hCe : forall i, ‖e i‖ <= C；hDf : forall s, ∑ i in s, 
‖f i‖ ^ q.toReal <= D；s : Finset ι。
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
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le_of_le`：le_of_opNorm_le_of_le {x} {a 
b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) : ‖f x‖ <= a * b
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
lemma holder_top_left_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hCe : ∀ i, ‖e i‖ ≤ C) (hDf : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ q.toReal ≤ (K * C) ^ q.toReal * D := by
  grw [← hDf s, s.mul_sum]
  apply s.sum_le_sum fun i hi ↦ ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _
/-
**Memℓp.holder_top_right_bound** 是 Mathlib 中的一个引理，位于命名空间 `Memℓp`。
形式化陈述：holder_top_right_bound {e : (i : ι) -> E i} {f : (i : ι) -> F i} (B : (i :
 ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K C D : Real} (hBK : forall i, ‖B i‖ <= K) (h
K : 0 <= K) (hD : 0 <= D) (hCe : forall s, ∑ i in s, ‖e i‖ ^ p.toReal <= C) (hDf
 : forall i, ‖f i‖ <= D) (s : Finset ι) : ∑ i in s, ‖B i (e i) (f i)‖ ^ p.toReal
 <= (K * D) ^ p.toReal * C
参数：i : ι；i : ι；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <=
 K；hK : 0 <= K；hD : 0 <= D；hCe : forall s, ∑ i in s, ‖e i‖ ^ p.toReal <= C；hDf :
 forall i, ‖f i‖ <= D；s : Finset ι。
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
· 使用引理 `Memℓp.holder_top_left_bound`：holder_top_left_bound {e : (i : ι) -> E i} 
{f : (i : ι) -> F i} (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K C D : Real} (
hBK : forall i, ‖…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_flip`：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃
] G) : ‖f.flip‖ = ‖f‖
-/
lemma holder_top_right_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C) (hDf : ∀ i, ‖f i‖ ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ p.toReal ≤ (K * D) ^ p.toReal * C :=
  holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s
/-
**Memℓp.holder_gen_bound** 是 Mathlib 中的一个引理，位于命名空间 `Memℓp`。
形式化陈述：holder_gen_bound {e : (i : ι) -> E i} {f : (i : ι) -> F i} (hp : 0 < p.toR
eal) (hq : 0 < q.toReal) (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K C D : Rea
l} (hBK : forall i, ‖B i‖ <= K) (hK : 0 <= K) (hC : 0 <= C) (hCe : forall s, ∑ i
 in s, ‖e i‖ ^ p.toReal <= C) (hDf : forall s, ∑ i in s, ‖f i‖ ^ q.toReal <= D) 
(s : Finset ι) : ∑ i in s, ‖B i (e i) (f i)‖ ^ r.toReal <= K ^ r.toReal * C ^ (r
.toReal / p.toReal) * D ^ (r.toReal / q.toReal)
参数：i : ι；i : ι；hp : 0 < p.toReal；hq : 0 < q.toReal；B : (i : ι) -> E i ->L[𝕜] F i
 ->L[𝕜] G i；hBK : forall i, ‖B i‖ <= K；hK : 0 <= K；hC : 0 <= C；hCe : forall s, ∑
 i in s, ‖e i‖ ^ p.toReal <= C；hDf : forall s, ∑ i in s, ‖f i‖ ^ q.toReal <= D；s
 : Finset ι。
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
· 使用引理 `ENNReal.HolderTriple.toReal`：toReal (hp : 0 < p.toReal) (hq : 0 < q.toRe
al) [HolderTriple p q r] : Real.HolderTriple p.toReal q.toReal r.toReal
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg`：Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι :
 Type*} (s : Finset ι) {f g : ι -> Real} {p q r : Real} (hpqr : p.HolderTriple q
 r) (hf : forall i in s, …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
lemma holder_gen_bound {e : (i : ι) → E i} {f : (i : ι) → F i}
    (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C)
    (hDf : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal ≤
      K ^ r.toReal * C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) := by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal ≤
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ ≤ K ^ r.toReal * ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw [s.mul_sum]
      gcongr with i hi
      rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_assoc]
      gcongr
      exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le (hBK i) _) _
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
  calc
    _ ≤ (∑ i ∈ s, ‖e i‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
        (∑ i ∈ s, ‖f i‖ ^ q.toReal) ^ (r.toReal / q.toReal) := by
      apply Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s hpqr <;> (intros; positivity)
    _ ≤ _ := by
      gcongr
      · exact hCe s
      · exact hDf s
/-
**Memℓp.holder** 是 Mathlib 中的一个引理，位于命名空间 `Memℓp`。
形式化陈述：holder {e : (i : ι) -> E i} {f : (i : ι) -> F i} (he : Memℓp e p) (hf : Me
mℓp f q) (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall i, 
‖B i‖ <= K) : Memℓp (fun i => B i (e i) (f i)) r
参数：i : ι；i : ι；he : Memℓp e p；hf : Memℓp f q；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜
] G i；hBK : forall i, ‖B i‖ <= K。
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
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Memℓp.all`：Memℓp.all [Finite α] (f : forall i, E i) : Memℓp f p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `ENNReal.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Memℓp.bilin_of_zero_left`：bilin_of_zero_left (B : (i : ι) -> E i ->L[𝕜] 
F i ->L[𝕜] G i) {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) : Memℓp (fun i =>
 B i (e i) (f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Memℓp.bilin_of_top_left`：bilin_of_top_left (B : (i : ι) -> E i ->L[𝕜] F 
i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i, F
 i} (he : Mem…
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Memℓp.bilin_of_zero_right`：bilin_of_zero_right (B : (i : ι) -> E i ->L[𝕜
] F i ->L[𝕜] G i) {e : Π i, E i} {f : Π i, F i} (hf : Memℓp f 0) : Memℓp (fun i 
=> B i (e i) (f…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Memℓp.bilin_of_top_right`：bilin_of_top_right (B : (i : ι) -> E i ->L[𝕜] 
F i ->L[𝕜] G i) {K : Real} (hBK : forall i, ‖B i‖ <= K) {e : Π i, E i} {f : Π i,
 F i} (he : Me…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `memℓp_gen_iff''`：memℓp_gen_iff'' {f : (i : α) -> E i} (hp : 0 < p.toReal
) : Memℓp f p ↔ exists C, 0 <= C ∧ forall (s : Finset α), ∑ i in s, ‖f i‖ ^ p.to
Real …
· 使用定理 `memℓp_gen'`：memℓp_gen' {C : Real} {f : forall i, E i} (hf : forall s : F
inset α, ∑ i in s, ‖f i‖ ^ p.toReal <= C) : Memℓp f p
· 使用引理 `Memℓp.holder_gen_bound`：holder_gen_bound {e : (i : ι) -> E i} {f : (i : 
ι) -> F i} (hp : 0 < p.toReal) (hq : 0 < q.toReal) (B : (i : ι) -> E i ->L[𝕜] F 
i ->L[𝕜] G i…
-/
lemma holder {e : (i : ι) → E i} {f : (i : ι) → F i} (he : Memℓp e p) (hf : Memℓp f q)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) :
    Memℓp (fun i ↦ B i (e i) (f i)) r := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact all _
  have hK : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.bilin_of_zero_left B
  · simp_all only [inv_top, zero_add, inv_inj]
    exact he.bilin_of_top_left B hBK hf
  obtain (rfl | rfl | hq) := q.trichotomy
  · simp_all only [ENNReal.inv_zero, add_top, inv_eq_top]
    exact hf.bilin_of_zero_right B
  · simp_all only [inv_top, add_zero, inv_inj]
    exact he.bilin_of_top_right B hBK hf
  obtain ⟨C, hC, hCe⟩ := memℓp_gen_iff'' hp |>.mp he
  obtain ⟨D, hD, hDf⟩ := memℓp_gen_iff'' hq |>.mp hf
  exact memℓp_gen' <| holder_gen_bound r hp hq B hBK hK hC hCe hDf

end Memℓp

namespace lp

/-- The map between `lp` spaces satisfying `ENNReal.HolderTriple` induced by a
uniformly bounded family of continuous bilinear maps on the underlying spaces. -/
@[simps]
/-
**lp.holder** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：holder (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall
 i, ‖B i‖ <= K) (e : lp E p) (f : lp F q) : lp G r where val
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <= K；e : lp E 
p；f : lp F q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between `lp` spaces satisfying `ENNReal.HolderTriple` induced by a
uniformly bounded family of continuous bilinear maps on the underlying spaces.
-/
def holder (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    lp G r where
  val := fun i ↦ B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK

/-- `lp.holder` as a bilinear map. -/
@[simps!]
/-
**lp.holder** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：holder (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real} (hBK : forall
 i, ‖B i‖ <= K) (e : lp E p) (f : lp F q) : lp G r where val
参数：B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i, ‖B i‖ <= K；e : lp E 
p；f : lp F q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lp.holder` as a bilinear map.
-/
noncomputable def holderₗ (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →ₗ[𝕜] lp F q →ₗ[𝕜] lp G r :=
  .mk₂ 𝕜 (holder r B hBK) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

/-- `lp.holder` as a continuous bilinear map. -/
/-
**lp.holderL** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：holderL [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)] (B : (i : ι) -> E 
i ->L[𝕜] F i ->L[𝕜] G i) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) : lp E p ->L
[𝕜] lp F q ->L[𝕜] lp G r
参数：1 <= p；1 <= q；1 <= r；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i,
 ‖B i‖ <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lp.holder` as a continuous bilinear map.
-/
noncomputable def holderL [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] lp G r :=
  holderₗ r B hBK |>.mkContinuous₂ K fun e f ↦ by
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine norm_le_of_forall_le (by positivity) fun i ↦ ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?_
      all_goals exact norm_apply_le_norm (by simp) ..
    · obtain rfl : r = q := ENNReal.HolderTriple.unique ∞ q r q
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hq) (by positivity) fun s ↦ ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_left_bound B hBK
        (by positivity) (by positivity) (norm_apply_le_norm (by simp) _) ?_ s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hq) f
    · obtain rfl : r = p := ENNReal.HolderTriple.unique p ∞ r p
      refine norm_le_of_forall_sum_le (zero_lt_one.trans_le hp) (by positivity) fun s ↦ ?_
      rw [mul_right_comm, Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_right_bound B hBK
        (by positivity) (by positivity) ?_ (norm_apply_le_norm (by simp) _) s
      exact sum_rpow_le_norm_rpow (zero_lt_one.trans_le hp) e
    · have hpqr := hpqr.toReal r (zero_lt_one.trans_le hp) (zero_lt_one.trans_le hq)
      have hp := hpqr.pos
      have hq := hpqr.symm.pos
      refine norm_le_of_forall_sum_le hpqr.pos' (by positivity) fun s ↦ ?_
      simp only [holderₗ_apply_apply_coe]
      calc
        _ ≤ K ^ r.toReal * (‖e‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
          (‖f‖ ^ q.toReal) ^ (r.toReal / q.toReal) :=
          Memℓp.holder_gen_bound r hp hq B hBK (by positivity) (by positivity)
            (sum_rpow_le_norm_rpow hp e) (sum_rpow_le_norm_rpow hq f) s
        _ ≤ _ := by
          rw [← Real.rpow_mul, ← Real.rpow_mul]
          · simp only [← mul_div_assoc, ne_eq, hp.ne', not_false_eq_true, mul_div_cancel_left₀,
            hq.ne', fieldLe]
            rw [Real.mul_rpow, Real.mul_rpow]
            all_goals positivity
          all_goals positivity
/-
**lp.norm_holderL_le** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_holderL_le [Fact (1 <= p)] [Fact (1 <= q)] [Fact (1 <= r)] (B : (i : 
ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) : ‖h
olderL (p
参数：1 <= p；1 <= q；1 <= r；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i；hBK : forall i,
 ‖B i‖ <= K。
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
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma norm_holderL_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖holderL (p := p) (q := q) r B hBK‖ ≤ K :=
  LinearMap.mkContinuous₂_norm_le _ K.2 _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

variable (p q) in
/-- The natural pairing between `lp E p` and `lp F q` (for Hölder conjugate `p q : ℝ≥0∞`) with
values in a space `H` induced by a family of bilinear maps `B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H`.

This is given by `∑' i, B (e i) (f i)`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, which is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is the natural map
`lp (fun _ ↦ StrongDual 𝕜 E) p →L[𝕜] StrongDual 𝕜 (lp E q)`.
-/
/-
**lp.dualPairing** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：dualPairing [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q] (B : (i 
: ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K) : lp
 E p ->L[𝕜] lp F q ->L[𝕜] H
参数：1 <= p；1 <= q；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H；hBK : forall i, ‖B i‖ <=
 K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
The natural pairing between `lp E p` and `lp F q` (for Hölder conjugate `p q : ℝ
≥0∞`) with
values in a space `H` induced by a family of bilinear maps `B : (i : ι) → E i →L
[𝕜] F i →L[𝕜] H`.

This is given by `∑' i, B (e i) (f i)`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, wh
ich is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is 
the natural map
`lp (fun _ ↦ StrongDual 𝕜 E) p →L[𝕜] StrongDual 𝕜 (lp E q)`.
-/
noncomputable def dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] H :=
  (tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (holderL 1 B hBK)
/-
**lp.dualPairing_apply** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：dualPairing_apply [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q] (B
 : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K
) (e : lp E p) (f : lp F q) : dualPairing p q B hBK e f = ∑' i, B i (e i) (f i)
参数：1 <= p；1 <= q；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H；hBK : forall i, ‖B i‖ <=
 K；e : lp E p；f : lp F q。
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
-/
lemma dualPairing_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    dualPairing p q B hBK e f = ∑' i, B i (e i) (f i) :=
  rfl
/-
**lp.norm_dualPairing** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_dualPairing [Fact (1 <= p)] [Fact (1 <= q)] [p.HolderConjugate q] (B 
: (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H) {K : Real>=0} (hBK : forall i, ‖B i‖ <= K)
 : ‖dualPairing p q B hBK‖ <= K
参数：1 <= p；1 <= q；B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] H；hBK : forall i, ‖B i‖ <=
 K。
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
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `lp.instIsBoundedSMulSubtypePreLpMemAddSubgroup`：∀ {𝕜 : Type u_1} {α : Ty
pe u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → NormedAddCommGroup (E
 i)]   [inst_1 : NormedRing 𝕜] [inst…
· 使用定理 `lp.instSMulCommClassSubtypePreLpMemAddSubgroup`：∀ {𝕜 : Type u_1} {𝕜' : T
ype u_2} {α : Type u_3} {E : α → Type u_4} {p : ENNReal}   [inst : (i : α) → Nor
medAddCommGroup (E i)] [inst_1 : Nor…
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ContinuousLinearMap.norm_postcomp_le`：norm_postcomp_le [RingHomIsometric
 σ₁₂] [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃] (L : F ->SL[σ₂₃] G) : ‖L.pos
tcomp (σ
· 使用引理 `lp.norm_tsumCLM_le`：norm_tsumCLM_le {α 𝕜 E : Type*} [NontriviallyNormedF
ield 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] : ‖tsumCLM 𝕜 
α E‖ <= …
· 使用引理 `lp.norm_holderL_le`：norm_holderL_le [Fact (1 <= p)] [Fact (1 <= q)] [Fac
t (1 <= r)] (B : (i : ι) -> E i ->L[𝕜] F i ->L[𝕜] G i) {K : Real>=0} (hBK : fora
ll i, ‖B…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma norm_dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖dualPairing p q B hBK‖ ≤ K := calc
  ‖dualPairing p q B hBK‖
  _ ≤ ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ ≤ 1 * K := by
    gcongr
    · exact ContinuousLinearMap.norm_postcomp_le _ |>.trans norm_tsumCLM_le
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _

end lp

