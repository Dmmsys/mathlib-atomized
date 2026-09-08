/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The derivative of bounded bilinear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded bilinear maps.
-/

public section


open Asymptotics Topology

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

section BilinearMap

/-! ### Derivative of a bounded bilinear map -/

variable {b : E × F → G} {u : Set (E × F)}

open NormedField

-- TODO: rewrite/golf using analytic functions?
@[fun_prop]
/-
**IsBoundedBilinearMap.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.hasStrictFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p :
 E × F) : HasStrictFDerivAt b (h.deriv p) p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsBoundedBilinearMap.add_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   
[inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.add_left`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [
inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.map_sub_left`：map_sub_left (h : IsBoundedBilinearMa
p 𝕜 f) {x y : E} {z : F} : f (x - y, z) = f (x, z) - f (y, z)
· 使用定理 `IsBoundedBilinearMap.map_sub_right`：map_sub_right (h : IsBoundedBilinear
Map 𝕜 f) {x : E} {y z : F} : f (x, y - z) = f (x, y) - f (x, z)
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `_private.Mathlib.Analysis.Calculus.FDeriv.Bilinear.0.IsBoundedBilinearMa
p.hasStrictFDerivAt._abel_1_4`：∀ {E : Type u_2} {F : Type u_3} {G : Type u_1} [i
nst : NormedAddCommGroup G] {b : E × F → G} (x₁ : E) (y₁ : F) (x₂ : E)   (y₂ : F
) (x : E) (…
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedBilinearMap.isBigO_comp`：isBigO_comp {α : Type*} (H : IsBounded
BilinearMap 𝕜 f) {g : α -> E} {h : α -> F} {l : Filter α} : (fun x => f (g x, h 
x)) =O[l] fun x => ‖g …
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
（共 44 条，此处仅展示前 30 条）
-/
theorem IsBoundedBilinearMap.hasStrictFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasStrictFDerivAt b (h.deriv p) p := by
  simp only [hasStrictFDerivAt_iff_isLittleO]
  simp only [← map_add_left_nhds_zero (p, p), isLittleO_map]
  set T := (E × F) × E × F
  calc
    _ = fun x ↦ h.deriv (x.1 - x.2) (x.2.1, x.1.2) := by
      ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
      rcases p with ⟨x, y⟩
      simp only [map_sub, deriv_apply, Function.comp_apply, Prod.mk_add_mk, h.add_right, h.add_left,
        Prod.mk_sub_mk, h.map_sub_left, h.map_sub_right, sub_add_sub_cancel]
      abel
    -- _ =O[𝓝 (0 : T)] fun x ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖ :=
    --     h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp
    -- _ = o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1 := _
    _ =o[𝓝 (0 : T)] fun x ↦ x.1 - x.2 := by
      -- TODO : add 2 `calc` steps instead of the next 3 lines
      refine h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp.trans_isLittleO ?_
      suffices (fun x : T ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖) =o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1 by
        simpa only [mul_one, isLittleO_norm_right] using this
      refine (isBigO_refl _ _).mul_isLittleO ((isLittleO_one_iff _).2 ?_)
      -- TODO: `continuity` fails
      exact (continuous_snd.fst.prodMk continuous_fst.snd).norm.tendsto' _ _ (by simp)
    _ = _ := by simp [T, Function.comp_def]

@[fun_prop]
/-
**IsBoundedBilinearMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.hasFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F
) : HasFDerivAt b (h.deriv p) p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
-/
theorem IsBoundedBilinearMap.hasFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFDerivAt b (h.deriv p) p :=
  (h.hasStrictFDerivAt p).hasFDerivAt

@[fun_prop]
/-
**IsBoundedBilinearMap.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.hasFDerivWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p :
 E × F) : HasFDerivWithinAt b (h.deriv p) u p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
-/
theorem IsBoundedBilinearMap.hasFDerivWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFDerivWithinAt b (h.deriv p) u p :=
  (h.hasFDerivAt p).hasFDerivWithinAt

@[fun_prop]
/-
**IsBoundedBilinearMap.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.differentiableAt (h : IsBoundedBilinearMap 𝕜 b) (p : 
E × F) : DifferentiableAt 𝕜 b p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
-/
theorem IsBoundedBilinearMap.differentiableAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableAt 𝕜 b p :=
  (h.hasFDerivAt p).differentiableAt

@[fun_prop]
/-
**IsBoundedBilinearMap.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.differentiableWithinAt (h : IsBoundedBilinearMap 𝕜 b)
 (p : E × F) : DifferentiableWithinAt 𝕜 b u p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsBoundedBilinearMap.differentiableAt`：IsBoundedBilinearMap.differentiab
leAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : DifferentiableAt 𝕜 b p
-/
theorem IsBoundedBilinearMap.differentiableWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableWithinAt 𝕜 b u p :=
  (h.differentiableAt p).differentiableWithinAt
/-
**IsBoundedBilinearMap.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {b : E × F → G} (h : IsBoundedBiline
arMap 𝕜 b) (p : E × F),   fderiv 𝕜 b p = h.deriv p
参数：h : IsBoundedBilinearMap 𝕜 b；p : E × F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
-/
protected theorem IsBoundedBilinearMap.fderiv (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    fderiv 𝕜 b p = h.deriv p :=
  HasFDerivAt.fderiv (h.hasFDerivAt p)
/-
**IsBoundedBilinearMap.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinear
Map`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {b : E × F → G} {u : Set (E × F)}   
(h : IsBoundedBilinearMap 𝕜 b) (p : E × F), UniqueDiffWithinAt 𝕜 u p → fderivWit
hin 𝕜 b u p = h.deriv p
参数：E × F；h : IsBoundedBilinearMap 𝕜 b；p : E × F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.differentiableAt`：IsBoundedBilinearMap.differentiab
leAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : DifferentiableAt 𝕜 b p
· 使用定理 `IsBoundedBilinearMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
-/
protected theorem IsBoundedBilinearMap.fderivWithin (h : IsBoundedBilinearMap 𝕜 b) (p : E × F)
    (hxs : UniqueDiffWithinAt 𝕜 u p) : fderivWithin 𝕜 b u p = h.deriv p := by
  rw [DifferentiableAt.fderivWithin (h.differentiableAt p) hxs]
  exact h.fderiv p

@[fun_prop]
/-
**IsBoundedBilinearMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Diffe
rentiable 𝕜 b
参数：h : IsBoundedBilinearMap 𝕜 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.differentiableAt`：IsBoundedBilinearMap.differentiab
leAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : DifferentiableAt 𝕜 b p
-/
theorem IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b :=
  fun x => h.differentiableAt x

@[fun_prop]
/-
**IsBoundedBilinearMap.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.differentiableOn (h : IsBoundedBilinearMap 𝕜 b) : Dif
ferentiableOn 𝕜 b u
参数：h : IsBoundedBilinearMap 𝕜 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `IsBoundedBilinearMap.differentiable`：IsBoundedBilinearMap.differentiable
 (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b
-/
theorem IsBoundedBilinearMap.differentiableOn (h : IsBoundedBilinearMap 𝕜 b) :
    DifferentiableOn 𝕜 b u :=
  h.differentiable.differentiableOn

variable (B : E →L[𝕜] F →L[𝕜] G)

@[fun_prop]
/-
**ContinuousLinearMap.hasFDerivWithinAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.hasFDerivWithinAt_of_bilinear {f : G' -> E} {g : G' ->
 F} {f' : G' ->L[𝕜] E} {g' : G' ->L[𝕜] F} {x : G'} {s : Set G'} (hf : HasFDerivW
ithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun y =
> B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x。
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
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem ContinuousLinearMap.hasFDerivWithinAt_of_bilinear {f : G' → E} {g : G' → F}
    {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'} {s : Set G'} (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun y => B (f y) (g y))
      (B.precompR G' (f x) g' + B.precompL G' f' (g x)) s x := by
  -- need `by exact` to deal with tricky unification
  exact (B.isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp_hasFDerivWithinAt x (hf.prodMk hg)

@[fun_prop]
/-
**ContinuousLinearMap.hasFDerivAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.hasFDerivAt_of_bilinear {f : G' -> E} {g : G' -> F} {f
' : G' ->L[𝕜] E} {g' : G' ->L[𝕜] F} {x : G'} (hf : HasFDerivAt f f' x) (hg : Has
FDerivAt g g' x) : HasFDerivAt (fun y => B (f y) (g y)) (B.precompR G' (f x) g' 
+ B.precompL G' f' (g x)) x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x。
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
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem ContinuousLinearMap.hasFDerivAt_of_bilinear {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E}
    {g' : G' →L[𝕜] F} {x : G'} (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x := by
  -- need `by exact` to deal with tricky unification
  exact (B.isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp x (hf.prodMk hg)

@[fun_prop]
/-
**ContinuousLinearMap.hasStrictFDerivAt_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.hasStrictFDerivAt_of_bilinear {f : G' -> E} {g : G' ->
 F} {f' : G' ->L[𝕜] E} {g' : G' ->L[𝕜] F} {x : G'} (hf : HasStrictFDerivAt f f' 
x) (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun y => B (f y) (g y)) 
(B.precompR G' (f x) g' + B.precompL G' f' (g x)) x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem ContinuousLinearMap.hasStrictFDerivAt_of_bilinear
    {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E}
    {g' : G' →L[𝕜] F} {x : G'} (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun y => B (f y) (g y))
      (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x :=
  (B.isBoundedBilinearMap.hasStrictFDerivAt (f x, g x)).comp x (hf.prodMk hg)
/-
**ContinuousLinearMap.fderivWithin_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.fderivWithin_of_bilinear {f : G' -> E} {g : G' -> F} {
x : G'} {s : Set G'} (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableW
ithinAt 𝕜 g s x) (hs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun y => B (f
 y) (g y)) s x = B.precompR G' (f x) (fderivWithin 𝕜 g s x) + B.precompL G' (fde
rivWithin 𝕜 f s x) (g x)
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x；hs : 
UniqueDiffWithinAt 𝕜 s x。
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
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearMap.hasFDerivWithinAt_of_bilinear`：ContinuousLinearMap.h
asFDerivWithinAt_of_bilinear {f : G' -> E} {g : G' -> F} {f' : G' ->L[𝕜] E} {g' 
: G' ->L[𝕜] F} {x : G'} {s : Set G'} (h…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem ContinuousLinearMap.fderivWithin_of_bilinear {f : G' → E} {g : G' → F} {x : G'} {s : Set G'}
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => B (f y) (g y)) s x =
      B.precompR G' (f x) (fderivWithin 𝕜 g s x) + B.precompL G' (fderivWithin 𝕜 f s x) (g x) :=
  (B.hasFDerivWithinAt_of_bilinear hf.hasFDerivWithinAt hg.hasFDerivWithinAt).fderivWithin hs
/-
**ContinuousLinearMap.fderiv_of_bilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.fderiv_of_bilinear {f : G' -> E} {g : G' -> F} {x : G'
} (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : fderiv 𝕜 (fun y 
=> B (f y) (g y)) x = B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv
 𝕜 f x) (g x)
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
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
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearMap.hasFDerivAt_of_bilinear`：ContinuousLinearMap.hasFDer
ivAt_of_bilinear {f : G' -> E} {g : G' -> F} {f' : G' ->L[𝕜] E} {g' : G' ->L[𝕜] 
F} {x : G'} (hf : HasFDerivAt f f…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem ContinuousLinearMap.fderiv_of_bilinear {f : G' → E} {g : G' → F} {x : G'}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => B (f y) (g y)) x =
      B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv 𝕜 f x) (g x) :=
  (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv

end BilinearMap

end

