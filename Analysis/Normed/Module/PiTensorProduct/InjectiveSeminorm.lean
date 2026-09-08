/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Injective seminorm on the tensor of a finite family of normed spaces.

The purpose of this file is to develop the theory of the injective tensor norm.

A first formalization turned out not to capture the common mathematical definition and is
now deprecated. See

https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/injectiveSeminorm/with/568798633

## Main definitions

* `PiTensorProduct.toDualContinuousMultilinearMap`: The `𝕜`-linear map from
  `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending `x` to the map
  `f ↦ f x`.

## TODO

* Reimplement `injectiveSeminorm`.

-/

@[expose] public section

-- These explicit universe variables are required by `injectiveSeminorm`, which
-- has been marked as deprecated on 2026-06-10. TBD: delete the variables after the
-- deprecated material has been removed or re-implemented.
universe uι u𝕜 uE

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

namespace PiTensorProduct

section seminorm

variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`. -/
@[simps!]
/-
**PiTensorProduct.toDualContinuousMultilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `PiTe
nsorProduct`。
形式化陈述：toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) ->ₗ[𝕜] ContinuousMultilinea
rMap 𝕜 E F ->L[𝕜] F where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sen
ding
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`.
-/
noncomputable def toDualContinuousMultilinearMap :
    (⨂[𝕜] i, E i) →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuous
    (lift.toLinearMap.flip x ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear) ‖x‖
    (fun f ↦ by simpa [mul_comm] using norm_eval_le_projectiveSeminorm f x)
  map_add' x y := by
    ext; simp
  map_smul' a x := by
    ext; simp
/-
**PiTensorProduct.toDualContinuousMultilinearMap_le_projectiveSeminorm** 是 Mathl
ib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) : ‖
toDualContinuousMultilinearMap F x‖ <= ‖x‖
参数：x : ⨂[𝕜] i, E i。
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
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMap F x‖ ≤ ‖x‖ := by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (by positivity)

/-- The injective seminorm on `⨂[𝕜] i, Eᵢ`. Morally, it sends `x` in `⨂[𝕜] i, Eᵢ` to the
`sup` of the operator norms of the `PiTensorProduct.toDualContinuousMultilinearMap F x`, for all
normed vector spaces `F`. In fact, we only take in the same universe as `⨂[𝕜] i, Eᵢ`, and then
prove in `PiTensorProduct.norm_eval_le_injectiveSeminorm` that this gives the same result.
-/
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
noncomputable irreducible_def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}

@[deprecated "no replacement" (since := "2026-06-10")]
/-
**PiTensorProduct.dualSeminorms_bounded** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：dualSeminorms_bounded : BddAbove {p | exists (G : Type (max uι u𝕜 uE)) (_ 
: SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSemino
rm 𝕜 (ContinuousMultilinearMap 𝕜 E G ->L[𝕜] G)) (toDualContinuousMultilinearMap 
G (𝕜
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.toDualContinuousMultilinearMap_le_projectiveSeminorm`：to
DualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) : ‖toDualCo
ntinuousMultilinearMap F x‖ <= ‖x‖
-/
lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))} := by
  use projectiveSeminorm
  simp only [mem_upperBounds, Set.mem_ofPred_eq, forall_exists_index]
  intro p G _ _ hp x
  simpa [hp] using! toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/-
**PiTensorProduct.injectiveSeminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
形式化陈述：injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) : injectiveSeminorm x = ⨆ p : {p
 | exists (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G) (_ : NormedSp
ace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G ->L[
𝕜] G)) (toDualContinuousMultilinearMap G (𝕜
参数：x : ⨂[𝕜] i, E i。
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
· 使用定理 `PiTensorProduct.injectiveSeminorm_def`：∀ {ι : Type u_2} [inst : Fintype 
ι] {𝕜 : Type u_3} [inst_1 : NontriviallyNormedField 𝕜] {E : ι → Type u_4}   [ins
t_2 : (i : ι) → SeminormedA…
· 使用定理 `Seminorm.sSup_apply`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField
 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 
𝕜 E)}, Bd…
· 使用引理 `PiTensorProduct.dualSeminorms_bounded`：dualSeminorms_bounded : BddAbove 
{p | exists (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G) (_ : Normed
Space 𝕜 G), p = Seminorm.co…
-/
theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}, p.1 x := by
  simpa only [injectiveSeminorm, Set.coe_ofPred, Set.mem_ofPred_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] instSeminormedAddCommGroup in
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/-
**PiTensorProduct.norm_eval_le_injectiveSeminorm** 是 Mathlib 中的一个定理，位于命名空间 `PiTe
nsorProduct`。
形式化陈述：norm_eval_le_injectiveSeminorm (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂
[𝕜] i, E i) : ‖lift f.toMultilinearMap x‖ <= ‖f‖ * injectiveSeminorm x
参数：f : ContinuousMultilinearMap 𝕜 E F；x : ⨂[𝕜] i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMultilinearMap.opNorm_le_iff`：opNorm_le_iff {f : ContinuousMul
tilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
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
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.injectiveSeminorm_def`：∀ {ι : Type u_2} [inst : Fintype 
ι] {𝕜 : Type u_3} [inst_1 : NontriviallyNormedField 𝕜] {E : ι → Type u_4}   [ins
t_2 : (i : ι) → SeminormedA…
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用引理 `PiTensorProduct.dualSeminorms_bounded`：dualSeminorms_bounded : BddAbove 
{p | exists (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G) (_ : Normed
Space 𝕜 G), p = Seminorm.co…
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
（共 41 条，此处仅展示前 30 条）
-/
theorem norm_eval_le_injectiveSeminorm (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x := by
    /- If `F` were in `Type (max uι u𝕜 uE)` (which is the type of `⨂[𝕜] i, E i`), then the
    property that we want to prove would hold by definition of `injectiveSeminorm`. This is
    not necessarily true, but we will show that there exists a normed vector space `G` in
    `Type (max uι u𝕜 uE)` and an injective isometry from `G` to `F` such that `f` factors
    through a continuous multilinear map `f'` from `E = Π i, E i` to `G`, to which we can apply
    the definition of `injectiveSeminorm`. The desired inequality for `f` then follows
    immediately.
    The idea is very simple: the multilinear map `f` corresponds by `PiTensorProduct.lift`
    to a linear map from `⨂[𝕜] i, E i` to `F`, say `l`. We want to take `G` to be the image of
    `l`, with the norm induced from that of `F`; to make sure that we are in the correct universe,
    it is actually more convenient to take `G` equal to the coimage of `l` (i.e. the quotient
    of `⨂[𝕜] i, E i` by the kernel of `l`), which is canonically isomorphic to its image by
    `LinearMap.quotKerEquivRange`. -/
  set G := (⨂[𝕜] i, E i) ⧸ LinearMap.ker (lift f.toMultilinearMap)
  set G' := LinearMap.range (lift f.toMultilinearMap)
  set e := LinearMap.quotKerEquivRange (lift f.toMultilinearMap)
  let := SeminormedAddCommGroup.induced G G' e
  let := NormedSpace.induced 𝕜 G G' e
  set f'₀ := lift.symm (e.symm.toLinearMap ∘ₗ LinearMap.rangeRestrict (lift f.toMultilinearMap))
  have hf'₀ : ∀ (x : Π (i : ι), E i), ‖f'₀ x‖ ≤ ‖f‖ * ∏ i, ‖x i‖ := fun x ↦ by
    change ‖e (f'₀ x)‖ ≤ _
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Submodule.coe_norm,
        LinearMap.codRestrict_apply, lift.tprod, ContinuousMultilinearMap.coe_coe, e, f'₀]
    exact f.le_opNorm x
  set f' := MultilinearMap.mkContinuous f'₀ ‖f‖ hf'₀
  have hnorm : ‖f'‖ ≤ ‖f‖ := (f'.opNorm_le_iff (norm_nonneg f)).mpr hf'₀
  have heq : e (lift f'.toMultilinearMap x) = lift f.toMultilinearMap x := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod =>
      simp only [lift_symm, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, SetLike.val_smul,
      LinearMap.codRestrict_apply, f', f'₀]
    | add _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  suffices h : ‖lift f'.toMultilinearMap x‖ ≤ ‖f'‖ * injectiveSeminorm x by
    change ‖(e (lift f'.toMultilinearMap x)).1‖ ≤ _ at h
    rw [heq] at h
    exact h.trans (by gcongr)
  have hle : Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
      (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E)) ≤ injectiveSeminorm := by
    simp only [injectiveSeminorm]
    refine le_csSup dualSeminorms_bounded ?_
    rw [Set.mem_ofPred]
    existsi G, inferInstance, inferInstance
    rfl
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg f'))
  simp only [Seminorm.comp_apply, coe_normSeminorm, ← toDualContinuousMultilinearMap_apply_apply]
  rw [mul_comm]
  exact ContinuousLinearMap.le_opNorm _ _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/-
**PiTensorProduct.injectiveSeminorm_le_projectiveSeminorm** 是 Mathlib 中的一个定理，位于命
名空间 `PiTensorProduct`。
形式化陈述：injectiveSeminorm_le_projectiveSeminorm : injectiveSeminorm (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.injectiveSeminorm_def`：∀ {ι : Type u_2} [inst : Fintype 
ι] {𝕜 : Type u_3} [inst_1 : NontriviallyNormedField 𝕜] {E : ι → Type u_4}   [ins
t_2 : (i : ι) → SeminormedA…
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Seminorm.zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : out
Param (Type u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [
self : Is…
· 使用定理 `Seminorm.instIsZeroApplyReal`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Se
minormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E],   IsZeroApply (Semino
rm 𝕜 E) E ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `PUnit.instSMulCommClass`：∀ {R : Type u_1} {S : Type u_2}, SMulCommClass 
R S PUnit.{u_3 + 1}
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `PiTensorProduct.toDualContinuousMultilinearMap_le_projectiveSeminorm`：to
DualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) : ‖toDualCo
ntinuousMultilinearMap F x‖ <= ‖x‖
-/
theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) ≤ projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_ofPred_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(max (max uE uι) u𝕜) + 1} x) 0,
      norm_zero]
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨G, _, _, h⟩ := hp
    rw [h]; intro x; simp only [Seminorm.comp_apply, coe_normSeminorm]
    exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/-
**PiTensorProduct.injectiveSeminorm_tprod_le** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：injectiveSeminorm_tprod_le (m : Π (i : ι), E i) : injectiveSeminorm (⨂ₜ[𝕜]
 i, m i) <= ∏ i, ‖m i‖
参数：m : Π (i : ι), E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PiTensorProduct.injectiveSeminorm_le_projectiveSeminorm`：injectiveSemino
rm_le_projectiveSeminorm : injectiveSeminorm (𝕜
· 使用定理 `PiTensorProduct.projectiveSeminorm_tprod_le`：projectiveSeminorm_tprod_le
 (m : Π i, E i) : ‖(⨂ₜ[𝕜] i, m i)‖ <= ∏ i, ‖m i‖
-/
theorem injectiveSeminorm_tprod_le (m : Π (i : ι), E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ :=
  le_trans (injectiveSeminorm_le_projectiveSeminorm _) (projectiveSeminorm_tprod_le m)

end seminorm

end PiTensorProduct

