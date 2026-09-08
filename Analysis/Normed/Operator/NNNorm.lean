/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Operator norm as an `NNNorm`

Operator norm as an `NNNorm`, i.e. taking values in non-negative reals.

-/

public section

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped NNReal Topology Uniformity ENNReal
open Metric ContinuousLinearMap
open Set Real

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}

section NontriviallySemiNormed

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：nnnorm_def (f : E ->SL[σ₁₂] F) : ‖f‖₊ = sInf { c | forall x, ‖f x‖₊ <= c *
 ‖x‖₊ }
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sInf`：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `ContinuousLinearMap.norm_def`：norm_def (f : E ->SL[σ₁₂] F) : ‖f‖ = sInf 
{ c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
· 使用定理 `NNReal.coe_image`：coe_image {s : Set Real>=0} : (↑) '' s = { x : Real | 
exists h : 0 <= x, .mk x h in s }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_ofPred_eq, NNReal.coe_mk,
    exists_prop]

@[simp, nontriviality]
/-
**ContinuousLinearMap.opNNNorm_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：opNNNorm_subsingleton [Subsingleton E] (f : E ->SL[σ₁₂] F) : ‖f‖₊ = 0
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousLinearMap.opNorm_subsingleton`：opNorm_subsingleton [Subsinglet
on E] : ‖f‖ = 0
-/
theorem opNNNorm_subsingleton [Subsingleton E] (f : E →SL[σ₁₂] F) : ‖f‖₊ = 0 :=
  NNReal.eq <| f.opNorm_subsingleton

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
/-
**ContinuousLinearMap.opNNNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：opNNNorm_le_bound (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖f x‖₊
 <= M * ‖x‖₊) : ‖f‖₊ <= M
参数：f : E ->SL[σ₁₂] F；M : Real>=0；hM : forall x, ‖f x‖₊ <= M * ‖x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
If one controls the norm of every `A x`, then one controls the norm of `A`.
-/
theorem opNNNorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  opNorm_le_bound f (zero_le (a := M)) hM

/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
/-
**ContinuousLinearMap.opNNNorm_le_bound'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：opNNNorm_le_bound' (f : E ->SL[σ₁₂] F) (M : Real>=0) (hM : forall x, ‖x‖₊ 
!= 0 -> ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M
参数：f : E ->SL[σ₁₂] F；M : Real>=0；hM : forall x, ‖x‖₊ != 0 -> ‖f x‖₊ <= M * ‖x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound'`：opNorm_le_bound' (f : E ->SL[σ₁₂] 
F) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖) : ‖f‖
 <= M
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0

--- 原说明 ---
If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm 
of `A`.
-/
theorem opNNNorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
    ‖f‖₊ ≤ M :=
  opNorm_le_bound' f (zero_le (a := M)) fun x hx => hM x <| by rwa [← NNReal.coe_ne_zero]

/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
/-
**ContinuousLinearMap.opNNNorm_le_of_unit_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：opNNNorm_le_of_unit_nnnorm [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C :
 Real>=0} (hf : forall x, ‖x‖₊ = 1 -> ‖f x‖₊ <= C) : ‖f‖₊ <= C
参数：hf : forall x, ‖x‖₊ = 1 -> ‖f x‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_of_unit_norm`：opNorm_le_of_unit_norm [Norm
edAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C) (hf : forall x, ‖
x‖ = 1 -> ‖f x‖ <= C) : ‖f‖ <= C
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_eq_one`：∀ {r : NNReal}, ↑r = 1 ↔ r = 1

--- 原说明 ---
For a continuous real linear map `f`, if one controls the norm of every `f x`, `
‖x‖₊ = 1`, then
one controls the norm of `f`.
-/
theorem opNNNorm_le_of_unit_nnnorm [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]
/-
**ContinuousLinearMap.opNNNorm_le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：opNNNorm_le_of_lipschitz {f : E ->SL[σ₁₂] F} {K : Real>=0} (hf : Lipschitz
With K f) : ‖f‖₊ <= K
参数：hf : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_of_lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type 
u_2} {E : Type u_4} {F : Type u_5} [inst : SeminormedAddCommGroup E]   [inst_1 :
 SeminormedAddCommGroup F] [inst…
-/
theorem opNNNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖₊ ≤ K :=
  opNorm_le_of_lipschitz hf
/-
**ContinuousLinearMap.opNNNorm_eq_of_bounds** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：opNNNorm_eq_of_bounds {φ : E ->SL[σ₁₂] F} (M : Real>=0) (h_above : forall 
x, ‖φ x‖₊ <= M * ‖x‖₊) (h_below : forall N, (forall x, ‖φ x‖₊ <= N * ‖x‖₊) -> M 
<= N) : ‖φ‖₊ = M
参数：M : Real>=0；h_above : forall x, ‖φ x‖₊ <= M * ‖x‖₊；h_below : forall N, (foral
l x, ‖φ x‖₊ <= N * ‖x‖₊) -> M <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ContinuousLinearMap.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {φ : E ->SL
[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (
h_below : forall N >= 0, (for…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
-/
theorem opNNNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖₊ ≤ M * ‖x‖₊)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| opNorm_eq_of_bounds (zero_le (a := M)) h_above <| Subtype.forall'.mpr h_below
/-
**ContinuousLinearMap.opNNNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opNNNorm_le_iff {f : E ->SL[σ₁₂] F} {C : Real>=0} : ‖f‖₊ <= C ↔ forall x, 
‖f x‖₊ <= C * ‖x‖₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_iff`：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M 
: Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem opNNNorm_le_iff {f : E →SL[σ₁₂] F} {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊ :=
  opNorm_le_iff C.2
/-
**ContinuousLinearMap.isLeast_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：isLeast_opNNNorm (f : E ->SL[σ₁₂] F) : IsLeast {C : Real>=0 | forall x, ‖f
 x‖₊ <= C * ‖x‖₊} ‖f‖₊
参数：f : E ->SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a
-/
theorem isLeast_opNNNorm (f : E →SL[σ₁₂] F) : IsLeast {C : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici
/-
**ContinuousLinearMap.opNNNorm_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opNNNorm_comp_le (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F) : ‖h.comp f‖₊ <= 
‖h‖₊ * ‖f‖₊
参数：h : F ->SL[σ₂₃] G；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
-/
theorem opNNNorm_comp_le (h : F →SL[σ₂₃] G) (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  opNorm_comp_le h f
/-
**ContinuousLinearMap.opENorm_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opENorm_comp_le (h : F ->SL[σ₂₃] G) (f : E ->SL[σ₁₂] F) : ‖h.comp f‖ₑ <= ‖
h‖ₑ * ‖f‖ₑ
参数：h : F ->SL[σ₂₃] G；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNNNorm_comp_le`：opNNNorm_comp_le (h : F ->SL[σ₂₃] 
G) (f : E ->SL[σ₁₂] F) : ‖h.comp f‖₊ <= ‖h‖₊ * ‖f‖₊
-/
lemma opENorm_comp_le (h : F →SL[σ₂₃] G) (f : E →SL[σ₁₂] F) : ‖h.comp f‖ₑ ≤ ‖h‖ₑ * ‖f‖ₑ := by
  simpa [enorm, ← ENNReal.coe_mul] using opNNNorm_comp_le h f
/-
**ContinuousLinearMap.le_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E) : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
参数：f : E ->SL[σ₁₂] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem le_opNNNorm (f : E →SL[σ₁₂] F) (x : E) : ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ :=
  f.le_opNorm x
/-
**ContinuousLinearMap.le_opENorm** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) : ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
参数：f : E ->SL[σ₁₂] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
-/
lemma le_opENorm (f : E →SL[σ₁₂] F) (x : E) : ‖f x‖ₑ ≤ ‖f‖ₑ * ‖x‖ₑ := by
  dsimp [enorm]; exact mod_cast le_opNNNorm ..

@[deprecated (since := "2026-06-27")] alias le_opNorm_enorm := le_opENorm

/-- If one controls the enorm of every `f x`, then one controls the enorm of `f`. -/
/-
**ContinuousLinearMap.opENorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opENorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ
 <= M * ‖x‖ₑ) : ‖f‖ₑ <= M
参数：f : E ->SL[σ₁₂] F；hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
If one controls the enorm of every `f x`, then one controls the enorm of `f`.
-/
theorem opENorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ≥0∞} (hM : ∀ x, ‖f x‖ₑ ≤ M * ‖x‖ₑ) :
    ‖f‖ₑ ≤ M := by
  rcases eq_top_or_lt_top M with rfl | h'M
  · simp
  lift M to NNReal using h'M.ne
  simp only [← ofReal_norm, ENNReal.ofReal_le_coe]
  apply opNorm_le_bound _ (by positivity) (fun x ↦ ?_)
  specialize hM x
  simp only [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal] at hM
  rwa [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hM
/-
**ContinuousLinearMap.le_of_opENorm_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：le_of_opENorm_le_of_le (f : E ->SL[σ₁₂] F) {x} {a b : Real>=0∞} (hf : ‖f‖ₑ
 <= a) (hx : ‖x‖ₑ <= b) : ‖f x‖ₑ <= a * b
参数：f : E ->SL[σ₁₂] F；hf : ‖f‖ₑ <= a；hx : ‖x‖ₑ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ContinuousLinearMap.le_opENorm`：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) :
 ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
theorem le_of_opENorm_le_of_le (f : E →SL[σ₁₂] F) {x} {a b : ℝ≥0∞} (hf : ‖f‖ₑ ≤ a) (hx : ‖x‖ₑ ≤ b) :
    ‖f x‖ₑ ≤ a * b :=
  (f.le_opENorm x).trans <| by gcongr
/-
**ContinuousLinearMap.le_opENorm_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：le_opENorm_of_le (f : E ->SL[σ₁₂] F) {c : Real>=0∞} {x} (h : ‖x‖ₑ <= c) : 
‖f x‖ₑ <= ‖f‖ₑ * c
参数：f : E ->SL[σ₁₂] F；h : ‖x‖ₑ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opENorm_le_of_le`：le_of_opENorm_le_of_le (f : 
E ->SL[σ₁₂] F) {x} {a b : Real>=0∞} (hf : ‖f‖ₑ <= a) (hx : ‖x‖ₑ <= b) : ‖f x‖ₑ <
= a * b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_opENorm_of_le (f : E →SL[σ₁₂] F) {c : ℝ≥0∞} {x} (h : ‖x‖ₑ ≤ c) : ‖f x‖ₑ ≤ ‖f‖ₑ * c :=
  f.le_of_opENorm_le_of_le le_rfl h
/-
**ContinuousLinearMap.le_of_opENorm_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：le_of_opENorm_le (f : E ->SL[σ₁₂] F) {c : Real>=0∞} (h : ‖f‖ₑ <= c) (x : E
) : ‖f x‖ₑ <= c * ‖x‖ₑ
参数：f : E ->SL[σ₁₂] F；h : ‖f‖ₑ <= c；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opENorm_le_of_le`：le_of_opENorm_le_of_le (f : 
E ->SL[σ₁₂] F) {x} {a b : Real>=0∞} (hf : ‖f‖ₑ <= a) (hx : ‖x‖ₑ <= b) : ‖f x‖ₑ <
= a * b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_of_opENorm_le (f : E →SL[σ₁₂] F) {c : ℝ≥0∞} (h : ‖f‖ₑ ≤ c) (x : E) : ‖f x‖ₑ ≤ c * ‖x‖ₑ :=
  f.le_of_opENorm_le_of_le h le_rfl
/-
**ContinuousLinearMap.opENorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：opENorm_le_iff {f : E ->SL[σ₁₂] F} {M : Real>=0∞} : ‖f‖ₑ <= M ↔ forall x, 
‖f x‖ₑ <= M * ‖x‖ₑ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_of_opENorm_le`：le_of_opENorm_le (f : E ->SL[σ₁₂] 
F) {c : Real>=0∞} (h : ‖f‖ₑ <= c) (x : E) : ‖f x‖ₑ <= c * ‖x‖ₑ
· 使用定理 `ContinuousLinearMap.opENorm_le_bound`：opENorm_le_bound (f : E ->SL[σ₁₂] 
F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ) : ‖f‖ₑ <= M
-/
theorem opENorm_le_iff {f : E →SL[σ₁₂] F} {M : ℝ≥0∞} :
    ‖f‖ₑ ≤ M ↔ ∀ x, ‖f x‖ₑ ≤ M * ‖x‖ₑ :=
  ⟨f.le_of_opENorm_le, opENorm_le_bound f⟩
/-
**ContinuousLinearMap.nndist_le_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：nndist_le_opNNNorm (f : E ->SL[σ₁₂] F) (x y : E) : nndist (f x) (f y) <= ‖
f‖₊ * nndist x y
参数：f : E ->SL[σ₁₂] F；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.dist_le_opNorm`：dist_le_opNorm (x y : E) : dist (f x
) (f y) <= ‖f‖ * dist x y
-/
theorem nndist_le_opNNNorm (f : E →SL[σ₁₂] F) (x y : E) : nndist (f x) (f y) ≤ ‖f‖₊ * nndist x y :=
  dist_le_opNorm f x y

/-- continuous linear maps are Lipschitz continuous. -/
/-
**ContinuousLinearMap.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：lipschitz (f : E ->SL[σ₁₂] F) : LipschitzWith ‖f‖₊ f
参数：f : E ->SL[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.lipschitz_of_bound_nnnorm`：∀ {𝓕 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F
]   [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊

--- 原说明 ---
continuous linear maps are Lipschitz continuous.
-/
theorem lipschitz (f : E →SL[σ₁₂] F) : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm

/-- Evaluation of a continuous linear map `f` at a point is Lipschitz continuous in `f`. -/
/-
**ContinuousLinearMap.lipschitz_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E ->SL[σ₁₂] F => f x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzWith_iff_norm_sub_le`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F}   {C : 
NNReal}, LipschitzW…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Evaluation of a continuous linear map `f` at a point is Lipschitz continuous in 
`f`.
-/
theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E →SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)
/-
**ContinuousLinearMap.exists_mul_lt_apply_of_lt_opNNNorm** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：exists_mul_lt_apply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr :
 r < ‖f‖₊) : exists x, r * ‖x‖₊ < ‖f x‖₊
参数：f : E ->SL[σ₁₂] F；hr : r < ‖f‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `notMem_of_lt_csInf`：notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf
 s) (hs : BddBelow s) : x ∉ s
· 使用定理 `ContinuousLinearMap.nnnorm_def`：nnnorm_def (f : E ->SL[σ₁₂] F) : ‖f‖₊ = 
sInf { c | forall x, ‖f x‖₊ <= c * ‖x‖₊ }
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem exists_mul_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [not_forall, not_le, Set.mem_ofPred] using
    notMem_of_lt_csInf (nnnorm_def f ▸ hr : r < sInf { c : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ })
      (OrderBot.bddBelow _)
/-
**ContinuousLinearMap.exists_mul_lt_of_lt_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：exists_mul_lt_of_lt_opNorm (f : E ->SL[σ₁₂] F) {r : Real} (hr₀ : 0 <= r) (
hr : r < ‖f‖) : exists x, r * ‖x‖ < ‖f x‖
参数：f : E ->SL[σ₁₂] F；hr₀ : 0 <= r；hr : r < ‖f‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ContinuousLinearMap.exists_mul_lt_apply_of_lt_opNNNorm`：exists_mul_lt_ap
ply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x,
 r * ‖x‖₊ < ‖f x‖₊
-/
theorem exists_mul_lt_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < ‖f x‖ := by
  lift r to ℝ≥0 using hr₀
  exact f.exists_mul_lt_apply_of_lt_opNNNorm hr

end ContinuousLinearMap

namespace ContinuousLinearEquiv
variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-
**ContinuousLinearEquiv.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqu
iv`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type u_5} [inst : Non
triviallyNormedField 𝕜]   [inst_1 : NontriviallyNormedField 𝕜₂] [inst_2 : Semino
rmedAddCommGroup E] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 
𝕜 E] [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [inst_6 : RingHomIsometric σ₁₂
]   {σ₂₁ : 𝕜₂ →+* 𝕜} [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair 
σ₂₁ σ₁₂] (e : E ≃SL[σ₁₂] F),   LipschitzWith ‖↑e‖₊ ⇑e
参数：e : E ≃SL[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
-/
protected theorem lipschitz (e : E ≃SL[σ₁₂] F) : LipschitzWith ‖(e : E →SL[σ₁₂] F)‖₊ e :=
  (e : E →SL[σ₁₂] F).lipschitz

end ContinuousLinearEquiv

end NontriviallySemiNormed

section DenselyNormedDomain
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：exists_lt_apply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r <
 ‖f‖₊) : exists x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊
参数：f : E ->SL[σ₁₂] F；hr : r < ‖f‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.exists_mul_lt_apply_of_lt_opNNNorm`：exists_mul_lt_ap
ply_of_lt_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x,
 r * ‖x‖₊ < ‖f x‖₊
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nnnorm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 
‖a‖₊ ≠ 0 ↔ a ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
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
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NormedField.exists_lt_nnnorm_lt`：exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (
h : r₁ < r₂) : exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.lt_inv_iff_mul_lt`：lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0)
 : r < p⁻¹ ↔ r * p < 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 35 条，此处仅展示前 30 条）
-/
theorem exists_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0}
    (hr : r < ‖f‖₊) : ∃ x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_opNNNorm hr
  have hy' : ‖y‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simp [heq, nnnorm_zero, map_zero] at hy
  have hfy : ‖f y‖₊ ≠ 0 := hy.ne_zero
  rw [← inv_inv ‖f y‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm ‖y‖₊, ←
    mul_assoc, ← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, ?_⟩
  rwa [map_smulₛₗ f, nnnorm_smul, ← div_lt_iff₀ hfy.bot_lt, div_eq_mul_inv,
    RingHomIsometric.nnnorm_map]
/-
**ContinuousLinearMap.exists_lt_apply_of_lt_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：exists_lt_apply_of_lt_opNorm (f : E ->SL[σ₁₂] F) {r : Real} (hr : r < ‖f‖)
 : exists x : E, ‖x‖ < 1 ∧ r < ‖f x‖
参数：f : E ->SL[σ₁₂] F；hr : r < ‖f‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm`：exists_lt_apply_of_l
t_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x : E, ‖x‖
₊ < 1 ∧ r < ‖f x‖₊
-/
theorem exists_lt_apply_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ}
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to ℝ≥0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_opNNNorm hr
/-
**ContinuousLinearMap.sSup_unit_ball_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：sSup_unit_ball_eq_nnnorm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' 
ball 0 1) = ‖f‖₊
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm`：exists_lt_apply_of_l
t_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x : E, ‖x‖
₊ < 1 ∧ r < ‖f x‖₊
-/
theorem sSup_unit_ball_eq_nnnorm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) ?_
    fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩
/-
**ContinuousLinearMap.sSup_unit_ball_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：sSup_unit_ball_eq_norm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖) '' bal
l 0 1) = ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_sSup`：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `ContinuousLinearMap.sSup_unit_ball_eq_nnnorm`：sSup_unit_ball_eq_nnnorm (
f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊
-/
theorem sSup_unit_ball_eq_norm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_unit_ball_eq_nnnorm
/-
**ContinuousLinearMap.sSup_unitClosedBall_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：sSup_unitClosedBall_eq_nnnorm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊
) '' closedBall 0 1) = ‖f‖₊
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.unit_le_opNorm`：unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <
= ‖f‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.sSup_unit_ball_eq_nnnorm`：sSup_unit_ball_eq_nnnorm (
f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊
· 使用定理 `csSup_le_csSup'`：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s
 subseteq t) : sSup s <= sSup t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
-/
theorem sSup_unitClosedBall_eq_nnnorm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ := by
  have hbdd : ∀ y ∈ (fun x => ‖f x‖₊) '' closedBall 0 1, y ≤ ‖f‖₊ := by
    rintro - ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  refine le_antisymm (csSup_le ((nonempty_closedBall.mpr zero_le_one).image _) hbdd) ?_
  rw [← sSup_unit_ball_eq_nnnorm]
  gcongr
  exacts [⟨‖f‖₊, hbdd⟩, ball_subset_closedBall]
/-
**ContinuousLinearMap.sSup_unitClosedBall_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：sSup_unitClosedBall_eq_norm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖) '
' closedBall 0 1) = ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_sSup`：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `ContinuousLinearMap.sSup_unitClosedBall_eq_nnnorm`：sSup_unitClosedBall_e
q_nnnorm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊
-/
theorem sSup_unitClosedBall_eq_norm (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using!
    NNReal.coe_inj.2 f.sSup_unitClosedBall_eq_nnnorm
/-
**ContinuousLinearMap.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm [NormedAlgebra Real 𝕜] (f : E
 ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x : E, ‖x‖₊ = 1 ∧ r < ‖f x‖
₊
参数：f : E ->SL[σ₁₂] F；hr : r < ‖f‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm`：exists_lt_apply_of_l
t_opNNNorm (f : E ->SL[σ₁₂] F) {r : Real>=0} (hr : r < ‖f‖₊) : exists x : E, ‖x‖
₊ < 1 ∧ r < ‖f x‖₊
· 使用定理 `eq_zero_or_nnnorm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E
), a = 0 ∨ 0 < ‖a‖₊
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
（共 40 条，此处仅展示前 30 条）
-/
theorem exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm [NormedAlgebra ℝ 𝕜]
    (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x : E, ‖x‖₊ = 1 ∧ r < ‖f x‖₊ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNNNorm f hr
  obtain rfl | hx0 := eq_zero_or_nnnorm_pos x
  · simp at hr
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖₊⁻¹ * ‖f x‖₊ by simpa [nnnorm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖₊ := by simpa
    _ < ‖x‖₊⁻¹ * ‖f x‖₊ := by gcongr; exact hr.pos

/-- When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall_eq_nnnorm` can
be tightened to take the supremum over only the `Metric.sphere`. -/
/-
**ContinuousLinearMap.sSup_sphere_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：sSup_sphere_eq_nnnorm [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F) : sSup ((
fun x => ‖f x‖₊) '' Metric.sphere 0 1) = ‖f‖₊
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_eq_empty_of_subsingleton`：sphere_eq_empty_of_subsingleton 
[Subsingleton α] (hε : ε != 0) : sphere x ε = ∅
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `ContinuousLinearMap.opNNNorm_subsingleton`：opNNNorm_subsingleton [Subsin
gleton E] (f : E ->SL[σ₁₂] F) : ‖f‖₊ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedSpace.sphere_nonempty`：NormedSpace.sphere_nonempty {x : E} {r : Re
al} : (sphere x r).Nonempty ↔ 0 <= r
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用定理 `ContinuousLinearMap.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm`：exists
_nnnorm_eq_one_lt_apply_of_lt_opNNNorm [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F
) {r : Real>=0} (hr : r < ‖f‖₊) : exists x : E, ‖x‖₊ =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall
_eq_nnnorm` can
be tightened to take the supremum over only the `Metric.sphere`.
-/
theorem sSup_sphere_eq_nnnorm [NormedAlgebra ℝ 𝕜] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' Metric.sphere 0 1) = ‖f‖₊ := by
  cases subsingleton_or_nontrivial E
  · simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).image _) ?_ fun ub hub => ?_
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using! f.le_opNorm_of_le (mem_sphere_zero_iff_norm.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hub
    exact ⟨_, ⟨x, by simpa using! congrArg NNReal.toReal hx, rfl⟩, hxf⟩

/-- When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall_eq_norm` can be
tightened to take the supremum over only the `Metric.sphere`. -/
/-
**ContinuousLinearMap.sSup_sphere_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：sSup_sphere_eq_norm [NormedAlgebra Real 𝕜] (f : E ->SL[σ₁₂] F) : sSup ((fu
n x => ‖f x‖) '' Metric.sphere 0 1) = ‖f‖
参数：f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_sSup`：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `ContinuousLinearMap.sSup_sphere_eq_nnnorm`：sSup_sphere_eq_nnnorm [Normed
Algebra Real 𝕜] (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' Metric.sphere 0
 1) = ‖f‖₊

--- 原说明 ---
When the domain is a real normed space, `ContinuousLinearMap.sSup_unitClosedBall
_eq_norm` can be
tightened to take the supremum over only the `Metric.sphere`.
-/
theorem sSup_sphere_eq_norm [NormedAlgebra ℝ 𝕜] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' Metric.sphere 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using! NNReal.coe_inj.2 f.sSup_sphere_eq_nnnorm

end ContinuousLinearMap

end DenselyNormedDomain

