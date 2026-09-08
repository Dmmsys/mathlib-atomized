/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.TransferInstance
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# The weak operator topology in Hilbert spaces

This file gives a few properties of the weak operator topology that are specific to operators on
Hilbert spaces. This mostly involves using the Fréchet-Riesz representation to convert between
applications of elements of the dual and inner products with vectors in the space.

## Main results

+ `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`: a function `f : α → E →WOT[𝕜] F`
  tends to `𝓝 A` if and only if `fun a ↦ ⟪y, (f a) x⟫_𝕜` tends to `𝓝 ⟪y, A x⟫_𝕜` for all
  `x : E`, `y : F`. Also included are the corresponding characterizations of continuity.
+ The adjoint operation is continuous in the weak operator topology, declared as an instance of
  `ContinuousStar (F →WOT[𝕜] F)`.
-/

public section

open scoped Topology InnerProductSpace

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[ext]
/-
**ContinuousLinearMapWOT.ext_inner** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
pWOT`。
形式化陈述：ext_inner {A B : E ->WOT[𝕜] F} (h : forall x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) :
 A = B
参数：h : forall x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMapWOT.ext_iff`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} [inst 
: NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_3}   {F 
: Type u_4} [inst_2 …
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
-/
lemma ext_inner {A B : E →WOT[𝕜] F} (h : ∀ x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) : A = B := by
  rw [ContinuousLinearMapWOT.ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y

variable [CompleteSpace F]

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a) x⟫` tends to `⟪y, A x⟫` along the same filter. -/
/-
**ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：tendsto_iff_forall_inner_apply_tendsto {α : Type*} {l : Filter α} {f : α -
> E ->WOT[𝕜] F} {A : E ->WOT[𝕜] F} : Tendsto f l (𝓝 A) ↔ forall x y, Tendsto (fu
n a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a) x⟫` tends to `⟪y, A x⟫` along 
the same filter.
-/
lemma tendsto_iff_forall_inner_apply_tendsto {α : Type*} {l : Filter α}
    {f : α → E →WOT[𝕜] F} {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜) := by
  simp_rw [tendsto_iff_forall_dual_apply_tendsto]
  exact .symm <| forall_congr' fun _ ↦
    Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ ↦ Iff.rfl
/-
**ContinuousLinearMapWOT.le_nhds_iff_forall_inner_apply_le_nhds** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearMapWOT`。
形式化陈述：le_nhds_iff_forall_inner_apply_le_nhds {l : Filter (E ->WOT[𝕜] F)} {A : E 
->WOT[𝕜] F} : l <= 𝓝 A ↔ forall x y, l.map (fun T => ⟪y, T x⟫_𝕜) <= 𝓝 (⟪y, A x⟫_
𝕜)
参数：E ->WOT[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`：tendsto_i
ff_forall_inner_apply_tendsto {α : Type*} {l : Filter α} {f : α -> E ->WOT[𝕜] F}
 {A : E ->WOT[𝕜] F} : Tendsto f l (𝓝 A) ↔ forall x …
-/
lemma le_nhds_iff_forall_inner_apply_le_nhds {l : Filter (E →WOT[𝕜] F)}
    {A : E →WOT[𝕜] F} : l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫_𝕜) ≤ 𝓝 (⟪y, A x⟫_𝕜) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)
/-
**ContinuousLinearMapWOT.continuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearMapWOT`。
形式化陈述：continuousWithinAt_iff {α : Type*} [TopologicalSpace α] {f : α -> E ->WOT[
𝕜] F} {s : Set α} {a : α} : ContinuousWithinAt f s a ↔ forall x y, ContinuousWit
hinAt (⟪y, f · x⟫_𝕜) s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`：tendsto_i
ff_forall_inner_apply_tendsto {α : Type*} {l : Filter α} {f : α -> E ->WOT[𝕜] F}
 {A : E ->WOT[𝕜] F} : Tendsto f l (𝓝 A) ↔ forall x …
-/
lemma continuousWithinAt_iff {α : Type*} [TopologicalSpace α]
    {f : α → E →WOT[𝕜] F} {s : Set α} {a : α} :
    ContinuousWithinAt f s a ↔ ∀ x y, ContinuousWithinAt (⟪y, f · x⟫_𝕜) s a :=
  tendsto_iff_forall_inner_apply_tendsto
/-
**ContinuousLinearMapWOT.continuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：continuousAt_iff {α : Type*} [TopologicalSpace α] {f : α -> E ->WOT[𝕜] F} 
{a : α} : ContinuousAt f a ↔ forall x y, ContinuousAt (⟪y, f · x⟫_𝕜) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`：tendsto_i
ff_forall_inner_apply_tendsto {α : Type*} {l : Filter α} {f : α -> E ->WOT[𝕜] F}
 {A : E ->WOT[𝕜] F} : Tendsto f l (𝓝 A) ↔ forall x …
-/
lemma continuousAt_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {a : α} :
    ContinuousAt f a ↔ ∀ x y, ContinuousAt (⟪y, f · x⟫_𝕜) a :=
  tendsto_iff_forall_inner_apply_tendsto
/-
**ContinuousLinearMapWOT.continuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMapWOT`。
形式化陈述：continuousOn_iff {α : Type*} [TopologicalSpace α] {f : α -> E ->WOT[𝕜] F} 
{s : Set α} : ContinuousOn f s ↔ forall x y, ContinuousOn (⟪y, f · x⟫_𝕜) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuousOn_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {s : Set α} :
    ContinuousOn f s ↔ ∀ x y, ContinuousOn (⟪y, f · x⟫_𝕜) s := by
  simp_rw [ContinuousOn, forall_comm (α := E), forall_comm (α := F), continuousWithinAt_iff]
/-
**ContinuousLinearMapWOT.continuous_iff** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earMapWOT`。
形式化陈述：continuous_iff {α : Type*} [TopologicalSpace α] {f : α -> E ->WOT[𝕜] F} : 
Continuous f ↔ forall x y, Continuous (⟪y, f · x⟫_𝕜)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} :
    Continuous f ↔ ∀ x y, Continuous (⟪y, f · x⟫_𝕜) := by
  simp_rw [continuous_iff_continuousAt, forall_comm (α := E), forall_comm (α := F),
    continuousAt_iff]

@[fun_prop] alias ⟨continuousWithinAt_inner_apply, continuousWithinAt⟩ := continuousWithinAt_iff
@[fun_prop] alias ⟨continuousOn_inner_apply, continuousOn⟩ := continuousOn_iff
@[fun_prop] alias ⟨continuousAt_inner_apply, continuousAt⟩ := continuousAt_iff
@[fun_prop] alias ⟨continuous_inner_apply, continuous⟩ := continuous_iff
/-
**ContinuousLinearMapWOT.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : StarRing (F →WOT[𝕜] F) := equiv.starRing
/-
**ContinuousLinearMapWOT.star_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearM
apWOT`。
形式化陈述：star_apply (A : F ->WOT[𝕜] F) (x : F) : star A x = star (toCLM A) x
参数：A : F ->WOT[𝕜] F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma star_apply (A : F →WOT[𝕜] F) (x : F) : star A x = star (toCLM A) x := rfl
/-
**ContinuousLinearMapWOT.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule 𝕜 (F →WOT[𝕜] F) := equiv.starModule 𝕜
/-
**ContinuousLinearMapWOT.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMapWOT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousStar (F →WOT[𝕜] F) where
  continuous_star := by
    simp_rw [continuous_iff, star_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, coe_toCLM]
    rw [forall_comm]
    conv in ⟪_, _⟫_𝕜 => rw [← inner_conj_symm, ← RCLike.star_def]
    fun_prop

end ContinuousLinearMapWOT

