/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sharvil Kesarwani
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Complemented subspaces of Banach spaces

A submodule `p` of a topological module `E` over `R` is called *complemented*
(`Submodule.ClosedComplemented`) if there exists a continuous linear projection `f : E →ₗ[R] p`,
`∀ x : p, f x = x`.

All results in this file rely on the open mapping theorem, hence the Banach space assumption.

## Main results

* `Submodule.isTopCompl_iff_isCompl_isClosed`: in a Banach space, two submodules are topological
  complements (`Submodule.IsTopCompl`) if and only if they are algebraic complements (`IsCompl`)
* `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl`: in a Banach space. a
  submodule is complemented if and only if it is closed and admits a closed algebraic complement.

## TODO

Generalize these results to metrizable complete topological vector spaces, once the open mapping
theorem is available in that setting.

## Tags

complemented subspace, Banach space
-/

@[expose] public section


variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

open LinearMap (ker range)

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace (F × G)]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃L[R] F × G`. -/
nonrec def equivProdOfSurjectiveOfIsCompl (f : E →L[𝕜] F) (g : E →L[𝕜] G) (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) : E ≃L[𝕜] F × G :=
  (f.equivProdOfSurjectiveOfIsCompl (g : E →ₗ[𝕜] G) hf hg hfg).toContinuousLinearEquivOfContinuous
    (f.continuous.prodMk g.continuous)

@[simp]
/-
**ContinuousLinearMap.coe_equivProdOfSurjectiveOfIsCompl** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：coe_equivProdOfSurjectiveOfIsCompl {f : E ->L[𝕜] F} {g : E ->L[𝕜] G} (hf :
 f.range = ⊤) (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) : (equivProdOfSurje
ctiveOfIsCompl f g hf hg hfg : E ->ₗ[𝕜] F × G) = f.prod g
参数：hf : f.range = ⊤；hg : g.range = ⊤；hfg : IsCompl f.ker g.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[𝕜] F × G) = f.prod g := rfl

@[simp]
/-
**ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_toLinearEquiv** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：equivProdOfSurjectiveOfIsCompl_toLinearEquiv {f : E ->L[𝕜] F} {g : E ->L[𝕜
] G} (hf : f.range = ⊤) (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) : (equivP
rodOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv = LinearMap.equivProdOfSur
jectiveOfIsCompl f g hf hg hfg
参数：hf : f.range = ⊤；hg : g.range = ⊤；hfg : IsCompl f.ker g.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivProdOfSurjectiveOfIsCompl_toLinearEquiv {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (hf : f.range = ⊤) (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg).toLinearEquiv =
      LinearMap.equivProdOfSurjectiveOfIsCompl f g hf hg hfg := rfl

@[simp]
/-
**ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：equivProdOfSurjectiveOfIsCompl_apply {f : E ->L[𝕜] F} {g : E ->L[𝕜] G} (hf
 : f.range = ⊤) (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) (x : E) : equivPr
odOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x)
参数：hf : f.range = ⊤；hg : g.range = ⊤；hfg : IsCompl f.ker g.ker；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →L[𝕜] F} {g : E →L[𝕜] G} (hf : f.range = ⊤)
    (hg : g.range = ⊤) (hfg : IsCompl f.ker g.ker) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end ContinuousLinearMap

namespace Submodule

variable [CompleteSpace E] {p q : Subspace 𝕜 E}

/-
**Submodule.IsCompl.isTopCompl_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.
IsCompl`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [CompleteSpace E] {p q : S
ubspace 𝕜 E},   IsCompl p q → IsClosed ↑p → IsClosed ↑q → Submodule.IsTopCompl p
 q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl`：∀ {
R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst
_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LinearEquiv.continuous_symm`：continuous_symm (e : E ≃ₛₗ[σ] F) (h : Conti
nuous e) : Continuous e.symm
· 使用定理 `Submodule.continuous_prodEquivOfIsCompl`：continuous_prodEquivOfIsCompl (
h : IsCompl p q) : Continuous (p.prodEquivOfIsCompl q h)
-/
theorem IsCompl.isTopCompl_of_isClosed (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : IsTopCompl p q := by
  have := hp.completeSpace_coe; have := hq.completeSpace_coe
  rw [isTopCompl_iff_continuous_symm_prodEquivOfIsCompl h]
  exact (p.prodEquivOfIsCompl q h).continuous_symm (continuous_prodEquivOfIsCompl h)

open Submodule in
/-
**Submodule.isTopCompl_iff_isCompl_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：isTopCompl_iff_isCompl_isClosed : IsTopCompl p q ↔ IsCompl p q ∧ IsClosed 
(p : Set E) ∧ IsClosed (q : Set E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `Submodule.IsTopCompl.isClosed`：∀ {R : Type u_1} [inst : Ring R] {M : Typ
e u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] {p q …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Submodule.IsTopCompl.isClosed'`：∀ {R : Type u_1} [inst : Ring R] {M : Ty
pe u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] {p q …
· 使用定理 `Submodule.IsCompl.isTopCompl_of_isClosed`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] [CompleteSpa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isTopCompl_iff_isCompl_isClosed :
    IsTopCompl p q ↔ IsCompl p q ∧ IsClosed (p : Set E) ∧ IsClosed (q : Set E) :=
  ⟨fun h ↦ ⟨h.isCompl, h.isClosed, h.isClosed'⟩, fun h ↦ h.1.isTopCompl_of_isClosed h.2.1 h.2.2⟩

variable (p q)

/-- If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuously
isomorphic to `E`. -/
@[deprecated prodEquivOfIsTopCompl (since := "2026-06-07")]
/-
**Submodule.prodEquivOfClosedCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq :
 IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q` is a closed complement of a closed subspace `p`, then `p × q` is continuo
usly
isomorphic to `E`.
-/
def prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : (p × q) ≃L[𝕜] E := by
  haveI := hp.completeSpace_coe; haveI := hq.completeSpace_coe
  refine (p.prodEquivOfIsCompl q h).toContinuousLinearEquivOfContinuous ?_
  exact (p.subtypeL.coprod q.subtypeL).continuous

/-- Projection to a closed submodule along a closed complement. -/
@[deprecated projectionOntoL (since := "2026-06-07")]
/-
**Submodule.linearProjOfClosedCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (hq 
: IsClosed (q : Set E)) : E ->L[𝕜] p
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to a closed submodule along a closed complement.
-/
def linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : E →L[𝕜] p :=
  ContinuousLinearMap.fst 𝕜 p q ∘L ↑(prodEquivOfClosedCompl p q h hp hq).symm

variable {p q}

@[deprecated "Use `coe_prodEquivOfIsTopCompl` instead" (since := "2026-06-07")]
/-
**Submodule.coe_prodEquivOfClosedCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E)) (
hq : IsClosed (q : Set E)) : ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquiv
OfIsCompl q h
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodEquivOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq) = p.prodEquivOfIsCompl q h := rfl

@[deprecated "Use `coe_symm_prodEquivOfIsTopCompl` instead" (since := "2026-06-07")]
/-
**Submodule.coe_prodEquivOfClosedCompl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：coe_prodEquivOfClosedCompl_symm (h : IsCompl p q) (hp : IsClosed (p : Set 
E)) (hq : IsClosed (q : Set E)) : ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (
p.prodEquivOfIsCompl q h).symm
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodEquivOfClosedCompl_symm (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    ⇑(p.prodEquivOfClosedCompl q h hp hq).symm = (p.prodEquivOfIsCompl q h).symm := rfl

@[deprecated "Use `toLinearMap_projectionOntoL` instead" (since := "2026-06-07")]
/-
**Submodule.coe_continuous_linearProjOfClosedCompl** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule`。
形式化陈述：coe_continuous_linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p
 : Set E)) (hq : IsClosed (q : Set E)) : (p.linearProjOfClosedCompl q h hp hq : 
E ->ₗ[𝕜] p) = p.projectionOnto q h
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_continuous_linearProjOfClosedCompl (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) :
    (p.linearProjOfClosedCompl q h hp hq : E →ₗ[𝕜] p) = p.projectionOnto q h := rfl

@[deprecated "Use `coe_projectionOntoL` instead" (since := "2026-06-07")]
/-
**Submodule.coe_continuous_linearProjOfClosedCompl'** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmodule`。
形式化陈述：coe_continuous_linearProjOfClosedCompl' (h : IsCompl p q) (hp : IsClosed (
p : Set E)) (hq : IsClosed (q : Set E)) : ⇑(p.linearProjOfClosedCompl q h hp hq)
 = p.projectionOnto q h
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；hq : IsClosed (q : Set E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_continuous_linearProjOfClosedCompl' (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : ⇑(p.linearProjOfClosedCompl q h hp hq) = p.projectionOnto q h :=
  rfl
/-
**Submodule.ClosedComplemented.of_isCompl_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule.ClosedComplemented`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [CompleteSpace E] {p q : S
ubspace 𝕜 E},   IsCompl p q → IsClosed ↑p → IsClosed ↑q → Submodule.ClosedComple
mented p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
· 使用定理 `Submodule.IsCompl.isTopCompl_of_isClosed`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] [CompleteSpa…
-/
theorem ClosedComplemented.of_isCompl_isClosed (h : IsCompl p q) (hp : IsClosed (p : Set E))
    (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  (IsCompl.isTopCompl_of_isClosed h hp hq).closedComplemented

alias IsCompl.closedComplemented_of_isClosed := ClosedComplemented.of_isCompl_isClosed
/-
**Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl** 是 Mathlib 
中的一个定理，位于命名空间 `Submodule`。
形式化陈述：closedComplemented_iff_isClosed_exists_isClosed_isCompl : p.ClosedCompleme
nted ↔ IsClosed (p : Set E) ∧ exists q : Submodule 𝕜 E, IsClosed (q : Set E) ∧ I
sCompl p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.isClosed`：∀ {R : Type u_1} [inst : Ring R] 
{M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] [Cont…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Submodule.ClosedComplemented.exists_isClosed_isCompl`：∀ {R : Type u_1} [
inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGro
up M]   [inst_3 : _root_.Module R M] {p : …
· 使用定理 `Submodule.ClosedComplemented.of_isCompl_isClosed`：∀ {𝕜 : Type u_1} {E : 
Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] [CompleteSpa…
-/
theorem closedComplemented_iff_isClosed_exists_isClosed_isCompl :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ q : Submodule 𝕜 E, IsClosed (q : Set E) ∧ IsCompl p q :=
  ⟨fun h => ⟨h.isClosed, h.exists_isClosed_isCompl⟩,
    fun ⟨hp, ⟨_, hq, hpq⟩⟩ => .of_isCompl_isClosed hpq hp hq⟩

end Submodule

