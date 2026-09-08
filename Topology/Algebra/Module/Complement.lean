/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sharvil Kesarwani
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Topological complements of submodules

Let `M` be a topological `R`-module. Two submodules `p, q` of `M` are said to be
*topological complements* (`Submodule.IsTopCompl`) if they are algebraic complements and the
algebraic isomorphism `M ≃ p × q` is a homeomorphism.

Not all submodules of `M` admit such a topological complements (even if they admit algebraic
complements). In the literature, such a submodule is called *topologically complemented*
or *direct*. One may also find the terminology *closed complemented* because,
in a Banach space, a closed algebraic complement is automatically a topological complement.
This is the terminology we use for now (`Submodule.ClosedComplemented`), but we should eventually
change to something less misleading.

## Main definitions

* `Submodule.IsTopCompl`: we say that two submodules are *topological complements* if they are
  algebraic complements and the projection on `p` along `q` is continuous. This is equivalent
  to the definition given above.
* `Submodule.ClosedComplemented`: we say that a submodule is (topologically) *complemented* if
  there exists a continuous projection `M →ₗ[R] p`.
* `Submodule.projectionOntoL`: if `h : IsTopCompl p q`, `p.projectionOntoL q h` is the
  continuous linear projection `M →L[R] p` along `q`. This is the continuous version of
  `Submodule.projectionOnto`.
* `Submodule.projectionL`: if `h : IsTopCompl p q`, `p.projectionL q h` is the continuous
  linear projection `M →L[R] M` onto `p` along `q`. This is the continuous version of
  `Submodule.IsCompl.projection`.
* `Submodule.ClosedComplemented.complement`: an arbitrary topological complement of a topologically
  complemented submodule.
* `Submodule.prodEquivOfIsTopCompl`: the bundled continuous linear equivalence `p × q ≃L[R] M`
  arising from a topological complement pair.
* `Submodule.quotientEquivOfIsTopCompl`: the bundled continuous linear equivalence `M ⧸ p ≃L[R] q`
  arising from a topological complement pair.
* `ContinuousLinearMap.ofIsTopCompl`: the continuous linear map induced by maps on a topological
  complement pair.

## Main statements

* `IsIdempotentElem.isTopCompl`: the range and kernel of a continuous projection are topological
  complements.
* `Submodule.IsTopCompl.isClosed`: if `p` and `q` are topological complements in a Hausdorff space,
  they are closed.

## Implementation details

In the definition of `Submodule.IsTopCompl`, we choose to ask for the continuity of the projection
on the left submdule along the right one, because it is a simpler map to work with than the
map `M ≃ p × q`.

Because the condition is symmetric, a lot of lemmas could have a left and a right variation.
In general we only include the left version, the right one being accessible through
`Submodule.IsTopCompl.symm`.

-/

@[expose] public section

open LinearMap (ker range)
open Topology ContinuousLinearMap Function Submodule

namespace Submodule

variable {R : Type*} [Ring R] {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open ContinuousLinearMap

/-- Two submodules `p` and `q` are *topological complements* if they are algebraic complements and
the projection on `p` along `q` is continuous. -/
@[pp_nodot]
/-
**Submodule.IsTopCompl** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {M : Type u_2} →       [Topologic
alSpace M] →         [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module R M] → 
Submodule R M → Submodule R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two submodules `p` and `q` are *topological complements* if they are algebraic c
omplements and
the projection on `p` along `q` is continuous.
-/
structure IsTopCompl (p q : Submodule R M) : Prop where
  isCompl : IsCompl p q
  continuous_projection : Continuous (p.projection q isCompl)

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
/-
**Submodule.ClosedComplemented** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：ClosedComplemented (p : Submodule R M) : Prop
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule `p` is called *complemented* if there exists a continuous projection
 `M →ₗ[R] p`.
-/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p q : Submodule R M}

section IsTopCompl

/-
**Submodule.IsCompl.isTopCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsCompl`
。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} (h : IsCompl p q),   Submodule.IsTopCompl p q ↔ Continuous ⇑(p.projection q h
)
参数：h : IsCompl p q；p.projection q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.continuous_projection`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [i
nst_3 : _root_.Module R M] {p q …
-/
theorem IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projection q h) :=
  ⟨IsTopCompl.continuous_projection, fun h' ↦ ⟨h, h'⟩⟩
/-
**Submodule.IsCompl.isTopCompl_iff_projectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.IsCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} (h : IsCompl p q),   Submodule.IsTopCompl p q ↔ Continuous ⇑(p.projectionOnto
 q h)
参数：h : IsCompl p q；p.projectionOnto q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsCompl.isTopCompl_iff`：∀ {R : Type u_1} [inst : Ring R] {M : 
Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] {p q …
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsCompl.isTopCompl_iff_projectionOnto (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projectionOnto q h) := by
  rw [h.isTopCompl_iff, IsInducing.subtypeVal.continuous_iff]
  rfl

@[deprecated (since := "2026-05-05")] alias IsCompl.isTopCompl_iff_linearProjOfIsCompl :=
  IsCompl.isTopCompl_iff_projectionOnto
/-
**Submodule.IsTopCompl.continuous_projectionOnto** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule.IsTopCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} (h : Submodule.IsTopCompl p q), Continuous ⇑(p.projectionOnto q ⋯)
参数：h : Submodule.IsTopCompl p q；p.projectionOnto q ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `Submodule.IsCompl.isTopCompl_iff_projectionOnto`：∀ {R : Type u_1} [inst 
: Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]
   [inst_3 : _root_.Module R M] {p q …
-/
theorem IsTopCompl.continuous_projectionOnto (h : IsTopCompl p q) :
    Continuous (p.projectionOnto q h.isCompl) :=
  h.isCompl.isTopCompl_iff_projectionOnto.mp h

@[deprecated (since := "2026-05-05")] alias IsTopCompl.continuous_linearProjOfIsCompl :=
  IsTopCompl.continuous_projectionOnto
/-
**Submodule.IsTopCompl.symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsTopCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [ContinuousSub M],   Submodule.IsTopCompl p q → Submodule.IsTopCompl q p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.projection_eq_id_sub_projection`：projection_eq_id_sub_projecti
on (hpq : IsCompl p q) : q.projection p hpq.symm = .id - p.projection q hpq
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Submodule.IsTopCompl.continuous_projection`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [i
nst_3 : _root_.Module R M] {p q …
-/
protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection
/-
**Submodule.isTopCompl_comm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isTopCompl_comm [ContinuousSub M] : IsTopCompl p q ↔ IsTopCompl q p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
-/
theorem isTopCompl_comm [ContinuousSub M] : IsTopCompl p q ↔ IsTopCompl q p :=
  ⟨IsTopCompl.symm, IsTopCompl.symm⟩

open LinearMap in
/-
**Submodule._root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl** 是 Mathlib 中
的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl {f : M →L[R] M}
    (hf : IsIdempotentElem f) : IsTopCompl f.range f.ker where
  isCompl := hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_projection ▸ f.continuous
/-
**Submodule.isTopCompl_bot_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isTopCompl_bot_top : IsTopCompl (⊥ : Submodule R M) ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.zero`：zero : IsIdempotentElem (0 : M₀)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isTopCompl`：∀ {R : Type u_1} [inst 
: Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]
   [inst_3 : _root_.Module R M] {f : …
-/
theorem isTopCompl_bot_top :
    IsTopCompl (⊥ : Submodule R M) ⊤ := by
  have : IsIdempotentElem (0 : M →L[R] M) := .zero
  simpa using this.isTopCompl
/-
**Submodule.isTopCompl_top_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isTopCompl_top_bot : IsTopCompl (⊤ : Submodule R M) ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isTopCompl`：∀ {R : Type u_1} [inst 
: Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]
   [inst_3 : _root_.Module R M] {f : …
-/
theorem isTopCompl_top_bot :
    IsTopCompl (⊤ : Submodule R M) ⊥ := by
  have : IsIdempotentElem (.id R M : M →L[R] M) := .one
  simpa using this.isTopCompl

open LinearMap in
/-
**Submodule._root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse** 是 M
athlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.IsTopCompl f₂.ker :=
  let p := f₁ ∘L f₂
  have p_idem : IsIdempotentElem p := by ext x; simp [p, h (f₂ x)]
  have range_p : p.range = f₁.range := range_comp_of_range_eq_top _ <|
    range_eq_top_of_surjective _ h.surjective
  have ker_p : p.ker = f₂.ker := ker_comp_of_ker_eq_bot _ <|
    ker_eq_bot_of_injective h.injective
  range_p ▸ ker_p ▸ p_idem.isTopCompl
/-
**Submodule._root_.ContinuousLinearMap.isTopCompl_of_proj** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isTopCompl_of_proj {f : M →L[R] p} (hf : ∀ x : p, f x = x) :
    IsTopCompl p f.ker := by
  simpa using p.subtypeL.isTopCompl_range_ker_of_leftInverse f hf

section projectionOnto

variable (p q) in
/-- If `h : IsTopCompl p q`, `h.projectionOnto` is the continuous linear projection `M →L[R] p`
along `q`. This is the continuous version of `Submodule.linearProjOfIsCompl`.

See also `Submodule.IsTopCompl.projection` for the same projection as an element of `M →L[R] M`. -/
/-
**Submodule.projectionOntoL** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：projectionOntoL (h : IsTopCompl p q) : M ->L[R] p
参数：h : IsTopCompl p q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `Submodule.IsTopCompl.continuous_projectionOnto`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p q …

--- 原说明 ---
If `h : IsTopCompl p q`, `h.projectionOnto` is the continuous linear projection 
`M →L[R] p`
along `q`. This is the continuous version of `Submodule.linearProjOfIsCompl`.

See also `Submodule.IsTopCompl.projection` for the same projection as an element
 of `M →L[R] M`.
-/
noncomputable def projectionOntoL (h : IsTopCompl p q) : M →L[R] p :=
  ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]
/-
**Submodule.toLinearMap_projectionOntoL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_projectionOntoL (h : IsTopCompl p q) : p.projectionOntoL q h =
 p.projectionOnto q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_projectionOntoL (h : IsTopCompl p q) :
    p.projectionOntoL q h = p.projectionOnto q h.isCompl :=
  rfl

@[simp]
/-
**Submodule.projectionOntoL_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOntoL_apply_left (h : IsTopCompl p q) (x : p) : p.projectionOnto
L q h x = x
参数：h : IsTopCompl p q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionOntoL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionOntoL q h x = x :=
  projectionOnto_apply_left h.isCompl x

@[simp]
/-
**Submodule.coe_projectionOntoL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_projectionOntoL (h : IsTopCompl p q) : ⇑(p.projectionOntoL q h) = p.pr
ojectionOnto q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projectionOntoL (h : IsTopCompl p q) :
    ⇑(p.projectionOntoL q h) = p.projectionOnto q h.isCompl :=
  rfl
/-
**Submodule.range_projectionOntoL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).range
 = ⊤
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_projectionOnto`：range_projectionOnto (h : IsCompl p q) :
 range (projectionOnto p q h) = ⊤
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).range = ⊤ := by
  simp
/-
**Submodule.projectionOntoL_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOntoL_surjective (h : IsTopCompl p q) : Surjective (p.projection
OntoL q h)
参数：h : IsTopCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_surjective`：projectionOnto_surjective (h : IsCo
mpl p q) : Function.Surjective (projectionOnto p q h)
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionOntoL_surjective (h : IsTopCompl p q) : Surjective (p.projectionOntoL q h) :=
  projectionOnto_surjective h.isCompl
/-
**Submodule.projectionOntoL_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：projectionOntoL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} : p.project
ionOntoL q h x = 0 ↔ x in q
参数：h : IsTopCompl p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOnto_apply_eq_zero_iff`：projectionOnto_apply_eq_zero
_iff (h : IsCompl p q) {x : E} : projectionOnto p q h x = 0 ↔ x in q
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionOntoL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionOntoL q h x = 0 ↔ x ∈ q :=
  projectionOnto_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff
/-
**Submodule.projectionOntoL_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionOntoL_apply_right (h : IsTopCompl p q) (x : q) : p.projectionOnt
oL q h x = 0
参数：h : IsTopCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOntoL_apply_eq_zero_of_mem_right`：∀ {R : Type u_1} [
inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGro
up M]   [inst_3 : _root_.Module R M] {p q …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem projectionOntoL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionOntoL q h x = 0 :=
  projectionOntoL_apply_eq_zero_of_mem_right h x.2
/-
**Submodule.ker_projectionOntoL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).ker = q
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_projectionOntoL (h : IsTopCompl p q) :
    (p.projectionOntoL q h).ker = q := by
  simp
/-
**Submodule.isQuotientMap_projectionOntoL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isQuotientMap_projectionOntoL (h : IsTopCompl p q) : IsQuotientMap (p.proj
ectionOntoL q h)
参数：h : IsTopCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.of_inverse`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {g : Y → X},   
Continuous f → Continuo…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Submodule.projectionOntoL_apply_left`：projectionOntoL_apply_left (h : Is
TopCompl p q) (x : p) : p.projectionOntoL q h x = x
-/
theorem isQuotientMap_projectionOntoL (h : IsTopCompl p q) :
    IsQuotientMap (p.projectionOntoL q h) :=
  .of_inverse continuous_subtype_val (p.projectionOntoL q h).continuous
    (projectionOntoL_apply_left h)

end projectionOnto

section projection

variable (p q) in
/-- If `h : IsTopCompl p q`, `h.projection` is the continuous linear projection `M →L[R] M` onto
`p` along `q`. This is the continuous version of `Submodule.IsCompl.projection`.

See also `Submodule.IsTopCompl.projectionOnto` for the same projection as an element of
`M →L[R] p`. -/
/-
**Submodule.projectionL** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：projectionL (h : IsTopCompl p q) : M ->L[R] M
参数：h : IsTopCompl p q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : IsTopCompl p q`, `h.projection` is the continuous linear projection `M →
L[R] M` onto
`p` along `q`. This is the continuous version of `Submodule.IsCompl.projection`.

See also `Submodule.IsTopCompl.projectionOnto` for the same projection as an ele
ment of
`M →L[R] p`.
-/
noncomputable def projectionL (h : IsTopCompl p q) : M →L[R] M :=
  p.subtypeL ∘L p.projectionOntoL q h

@[simp]
/-
**Submodule.coe_projectionL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_projectionL (h : IsTopCompl p q) : ⇑(p.projectionL q h) = p.projection
 q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projectionL (h : IsTopCompl p q) :
    ⇑(p.projectionL q h) = p.projection q h.isCompl :=
  rfl

@[simp]
/-
**Submodule.toLinearMap_projectionL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_projectionL (h : IsTopCompl p q) : p.projectionL q h = p.proje
ction q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_projectionL (h : IsTopCompl p q) :
    p.projectionL q h = p.projection q h.isCompl :=
  rfl
/-
**Submodule.projectionL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionL_apply (h : IsTopCompl p q) (x : M) : p.projectionL q h x = p.p
rojectionOntoL q h x
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projectionL_apply (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = p.projectionOntoL q h x :=
  rfl

@[simp]
/-
**Submodule.coe_projectionOntoL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_projectionOntoL_apply (h : IsTopCompl p q) (x : M) : (p.projectionOnto
L q h x : M) = p.projectionL q h x
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projectionOntoL_apply (h : IsTopCompl p q) (x : M) :
    (p.projectionOntoL q h x : M) = p.projectionL q h x :=
  rfl
/-
**Submodule.projectionL_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionL_apply_mem (h : IsTopCompl p q) (x : M) : p.projectionL q h x i
n p
参数：h : IsTopCompl p q；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem projectionL_apply_mem (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x ∈ p :=
  SetLike.coe_mem _
/-
**Submodule.projectionL_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionL_apply_left (h : IsTopCompl p q) (x : p) : p.projectionL q h x 
= x
参数：h : IsTopCompl p q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_apply_left`：projection_apply_left (hpq : IsCompl p 
q) (x : p) : p.projection q hpq x = x
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionL q h x = x :=
  projection_apply_left h.isCompl x
/-
**Submodule.range_projectionL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_projectionL (h : IsTopCompl p q) : (p.projectionL q h).range = p
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_projection`：range_projection (hpq : IsCompl p q) : range
 (p.projection q hpq) = p
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).range = p := by
  simp
/-
**Submodule.projectionL_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} : p.projectionL
 q h x = 0 ↔ x in q
参数：h : IsTopCompl p q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_apply_eq_zero_iff`：projection_apply_eq_zero_iff (hp
q : IsCompl p q) {x : E} : p.projection q hpq x = 0 ↔ x in q
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionL q h x = 0 ↔ x ∈ q :=
  projection_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff
/-
**Submodule.projectionL_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：projectionL_apply_right (h : IsTopCompl p q) (x : q) : p.projectionL q h x
 = 0
参数：h : IsTopCompl p q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionL_apply_eq_zero_of_mem_right`：∀ {R : Type u_1} [inst
 : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M
]   [inst_3 : _root_.Module R M] {p q …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem projectionL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionL q h x = 0 :=
  projectionL_apply_eq_zero_of_mem_right h x.2
/-
**Submodule.ker_projectionL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_projectionL (h : IsTopCompl p q) : (p.projectionL q h).ker = q
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_projection`：ker_projection (hpq : IsCompl p q) : ker (p.pr
ojection q hpq) = q
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).ker = q := by
  simp

@[simp]
/-
**Submodule.isIdempotentElem_projectionL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isIdempotentElem_projectionL (h : IsTopCompl p q) : IsIdempotentElem (p.pr
ojectionL q h)
参数：h : IsTopCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem isIdempotentElem_projectionL (h : IsTopCompl p q) :
    IsIdempotentElem (p.projectionL q h) := by
  simp [← isIdempotentElem_toLinearMap_iff]
/-
**Submodule.projectionL_add_projectionL_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：projectionL_add_projectionL_eq_self [ContinuousSub M] (h : IsTopCompl p q)
 (x : M) : p.projectionL q h x + q.projectionL p h.symm x = x
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_add_projection_eq_self`：projection_add_projection_e
q_self (hpq : IsCompl p q) (x : E) : (p.projection q hpq) x + (q.projection p hp
q.symm) x = x
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem projectionL_add_projectionL_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x + q.projectionL p h.symm x = x :=
  projection_add_projection_eq_self h.isCompl x
/-
**Submodule.projectionL_add_projectionL_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：projectionL_add_projectionL_eq_id [IsTopologicalAddGroup M] (h : IsTopComp
l p q) : p.projectionL q h + q.projectionL p h.symm = .id R M
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Submodule.projectionL_add_projectionL_eq_self`：projectionL_add_projectio
nL_eq_self [ContinuousSub M] (h : IsTopCompl p q) (x : M) : p.projectionL q h x 
+ q.projectionL p h.symm x = x
-/
theorem projectionL_add_projectionL_eq_id [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    p.projectionL q h + q.projectionL p h.symm = .id R M :=
  ContinuousLinearMap.ext <| projectionL_add_projectionL_eq_self h
/-
**Submodule.projectionL_eq_self_sub_projectionL** 是 Mathlib 中的一个引理，位于命名空间 `Submo
dule`。
形式化陈述：projectionL_eq_self_sub_projectionL [ContinuousSub M] (h : IsTopCompl p q)
 (x : M) : q.projectionL p h.symm x = x - p.projectionL q h x
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Submodule.projectionL_add_projectionL_eq_self`：projectionL_add_projectio
nL_eq_self [ContinuousSub M] (h : IsTopCompl p q) (x : M) : p.projectionL q h x 
+ q.projectionL p h.symm x = x
-/
lemma projectionL_eq_self_sub_projectionL [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    q.projectionL p h.symm x = x - p.projectionL q h x := by
  rw [eq_sub_iff_add_eq, projectionL_add_projectionL_eq_self]
/-
**Submodule.projectionL_eq_id_sub_projectionL** 是 Mathlib 中的一个引理，位于命名空间 `Submodu
le`。
形式化陈述：projectionL_eq_id_sub_projectionL [IsTopologicalAddGroup M] (h : IsTopComp
l p q) : q.projectionL p h.symm = .id R M - p.projectionL q h
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用引理 `Submodule.projectionL_eq_self_sub_projectionL`：projectionL_eq_self_sub_p
rojectionL [ContinuousSub M] (h : IsTopCompl p q) (x : M) : q.projectionL p h.sy
mm x = x - p.projectionL q h x
-/
lemma projectionL_eq_id_sub_projectionL [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    q.projectionL p h.symm = .id R M - p.projectionL q h :=
  ContinuousLinearMap.ext <| projectionL_eq_self_sub_projectionL h

/-- The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`. -/
/-
**Submodule.projectionL_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：projectionL_eq_self_iff (h : IsTopCompl p q) (x : M) : p.projectionL q h x
 = x ↔ x in p
参数：h : IsTopCompl p q；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projection_eq_self_iff`：∀ {R : Type u_1} [inst : Ring R] {E : 
Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p q : Submod
ule R E} (hpq : IsComp…
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …

--- 原说明 ---
The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`.
-/
lemma projectionL_eq_self_iff (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = x ↔ x ∈ p :=
  projection_eq_self_iff h.isCompl x
/-
**Submodule._root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL** 是 Mathl
ib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL
    {f : M →L[R] M} (hf : IsIdempotentElem f) : f = f.range.projectionL f.ker hf.isTopCompl :=
  coe_inj.mp <| LinearMap.IsIdempotentElem.eq_projection hf.toLinearMap
/-
**Submodule._root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range
_ker** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker
    {f : M →L[R] M} : IsIdempotentElem f ↔
      ∃ h : IsTopCompl f.range f.ker, f = f.range.projectionL f.ker h :=
  ⟨fun h ↦ ⟨_, h.eq_projectionL⟩, fun ⟨hf, h⟩ ↦ h.symm ▸ isIdempotentElem_projectionL hf⟩

end projection

section closed_hausdorff

/-
**Submodule.IsTopCompl.closedComplemented** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.I
sTopCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M}, Submodule.IsTopCompl p q → p.ClosedComplemented
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projectionOntoL_apply_left`：projectionOntoL_apply_left (h : Is
TopCompl p q) (x : p) : p.projectionOntoL q h x = x
-/
theorem IsTopCompl.closedComplemented (h : IsTopCompl p q) : ClosedComplemented p :=
  ⟨p.projectionOntoL q h, projectionOntoL_apply_left h⟩

/-- A variant of `Submodule.IsTopCompl.isClosed`. This has the very mild advantage over
`h.symm.isClosed` that it doesn't assume `ContinuousSub M`. -/
/-
**Submodule.IsTopCompl.isClosed'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsTopCompl
`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [T1Space ↥p], Submodule.IsTopCompl p q → IsClosed ↑q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_projectionOntoL`：ker_projectionOntoL (h : IsTopCompl p q) 
: (p.projectionOntoL q h).ker = q
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)

--- 原说明 ---
A variant of `Submodule.IsTopCompl.isClosed`. This has the very mild advantage o
ver
`h.symm.isClosed` that it doesn't assume `ContinuousSub M`.
-/
theorem IsTopCompl.isClosed' [T1Space p] (h : IsTopCompl p q) : IsClosed (q : Set M) := by
  rw [← ker_projectionOntoL h]
  exact isClosed_ker _

/-- If `p` and `q` are topological complements and `q` is Hausdorff, then `p` is closed. -/
/-
**Submodule.IsTopCompl.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsTopCompl`
。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [T1Space ↥q] [ContinuousSub M],   Submodule.IsTopCompl p q → IsClosed ↑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isClosed'`：∀ {R : Type u_1} [inst : Ring R] {M : Ty
pe u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] {p q …
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …

--- 原说明 ---
If `p` and `q` are topological complements and `q` is Hausdorff, then `p` is clo
sed.
-/
protected theorem IsTopCompl.isClosed [T1Space q] [ContinuousSub M] (h : IsTopCompl p q) :
    IsClosed (p : Set M) :=
  h.symm.isClosed'
/-
**Submodule.IsTopCompl.t3Space** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsTopCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [IsTopologicalAddGroup M],   Submodule.IsTopCompl p q → IsClosed ↑q → T3Space
 ↥p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Submodule.isQuotientMap_projectionOntoL`：isQuotientMap_projectionOntoL (
h : IsTopCompl p q) : IsQuotientMap (p.projectionOntoL q h)
· 使用定理 `Submodule.ker_projectionOntoL`：ker_projectionOntoL (h : IsTopCompl p q) 
: (p.projectionOntoL q h).ker = q
· 使用定理 `IsTopologicalAddGroup.t1Space`：∀ (G : Type w) [inst : TopologicalSpace G
] [inst_1 : AddGroup G] [ContinuousAdd G], IsClosed {0} → T1Space G
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `RegularSpace.t3Space_iff_t0Space`：RegularSpace.t3Space_iff_t0Space [Regu
larSpace X] : T3Space X ↔ T0Space X
· 使用定理 `instRegularSpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R
egularSpace X] {p : X → Prop}, RegularSpace (Subtype p)
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
-/
protected theorem IsTopCompl.t3Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T3Space p := by
  have : IsClosed ({0} : Set p) := by
    rw [← (isQuotientMap_projectionOntoL h).isClosed_preimage]
    rwa [← ker_projectionOntoL h] at hq
  have : T1Space p := IsTopologicalAddGroup.t1Space _ this
  rw [RegularSpace.t3Space_iff_t0Space]
  infer_instance

/-- If `p` and `q` are topological complements and `q` is closed, then `p` is Hausdorff. -/
/-
**Submodule.IsTopCompl.t2Space** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsTopCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [IsTopologicalAddGroup M],   Submodule.IsTopCompl p q → IsClosed ↑q → T2Space
 ↥p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.t3Space`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X

--- 原说明 ---
If `p` and `q` are topological complements and `q` is closed, then `p` is Hausdo
rff.
-/
protected theorem IsTopCompl.t2Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T2Space p :=
  have := h.t3Space hq
  inferInstance

end closed_hausdorff

end IsTopCompl

section ClosedComplemented

/-
**Submodule.ClosedComplemented.exists_isTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p : Submodule R M}
, p.ClosedComplemented → ∃ q, Submodule.IsTopCompl p q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `ContinuousLinearMap.isTopCompl_of_proj`：∀ {R : Type u_1} [inst : Ring R]
 {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] {p : …
-/
theorem ClosedComplemented.exists_isTopCompl (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsTopCompl p q :=
  Exists.elim h fun f hf => ⟨_, f.isTopCompl_of_proj hf⟩
/-
**Submodule.closedComplemented_iff_exists_isTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule`。
形式化陈述：closedComplemented_iff_exists_isTopCompl : ClosedComplemented p ↔ exists q
, IsTopCompl p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.exists_isTopCompl`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p : …
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
-/
theorem closedComplemented_iff_exists_isTopCompl :
    ClosedComplemented p ↔ ∃ q, IsTopCompl p q :=
  ⟨ClosedComplemented.exists_isTopCompl, fun H ↦ H.elim fun _ hq ↦ hq.closedComplemented⟩
/-
**Submodule.ClosedComplemented.exists_isClosed_isCompl** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p : Submodule R M}
 [T1Space ↥p], p.ClosedComplemented → ∃ q, IsClosed ↑q ∧ IsCompl p q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Submodule.ClosedComplemented.exists_isTopCompl`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p : …
· 使用定理 `Submodule.IsTopCompl.isClosed'`：∀ {R : Type u_1} [inst : Ring R] {M : Ty
pe u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] {p q …
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem ClosedComplemented.exists_isClosed_isCompl [T1Space p] (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

/-- An arbitrary choice of topological complement of a topologically complemented submodule. -/
/-
**Submodule.ClosedComplemented.complement** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.C
losedComplemented`。
形式化陈述：{R : Type u_1} →   [inst : Ring R] →     {M : Type u_2} →       [inst_1 : 
TopologicalSpace M] →         [inst_2 : AddCommGroup M] →           [inst_3 : _r
oot_.Module R M] → {p : Submodule R M} → p.ClosedComplemented → Submodule R M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.exists_isTopCompl`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p : …

--- 原说明 ---
An arbitrary choice of topological complement of a topologically complemented su
bmodule.
-/
noncomputable def ClosedComplemented.complement (h : ClosedComplemented p) : Submodule R M :=
  Classical.choose h.exists_isTopCompl
/-
**Submodule.ClosedComplemented.isTopCompl_complement** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p : Submodule R M}
 (h : p.ClosedComplemented), Submodule.IsTopCompl p h.complement
参数：h : p.ClosedComplemented。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submodule.ClosedComplemented.exists_isTopCompl`：∀ {R : Type u_1} [inst :
 Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] {p : …
-/
theorem ClosedComplemented.isTopCompl_complement (h : ClosedComplemented p) :
    IsTopCompl p h.complement :=
  Classical.choose_spec h.exists_isTopCompl
/-
**Submodule.ClosedComplemented.isCompl_complement** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p : Submodule R M}
 (h : p.ClosedComplemented), IsCompl p h.complement
参数：h : p.ClosedComplemented。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `Submodule.ClosedComplemented.isTopCompl_complement`：∀ {R : Type u_1} [in
st : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module R M] {p : …
-/
theorem ClosedComplemented.isCompl_complement (h : ClosedComplemented p) : IsCompl p h.complement :=
  h.isTopCompl_complement.isCompl
/-
**Submodule.ClosedComplemented.isClosed_complement** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p : Submodule R M}
 [T1Space ↥p] (h : p.ClosedComplemented), IsClosed ↑h.complement
参数：h : p.ClosedComplemented。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isClosed'`：∀ {R : Type u_1} [inst : Ring R] {M : Ty
pe u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] {p q …
· 使用定理 `Submodule.ClosedComplemented.isTopCompl_complement`：∀ {R : Type u_1} [in
st : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module R M] {p : …
-/
theorem ClosedComplemented.isClosed_complement [T1Space p] (h : ClosedComplemented p) :
    IsClosed (h.complement : Set M) :=
  h.isTopCompl_complement.isClosed'
/-
**Submodule.ClosedComplemented.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Clo
sedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [ContinuousSub M] [
T1Space M] {p : Submodule R M}, p.ClosedComplemented → IsClosed ↑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isClosed`：∀ {R : Type u_1} [inst : Ring R] {M : Typ
e u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] {p q …
· 使用定理 `Submodule.ClosedComplemented.isTopCompl_complement`：∀ {R : Type u_1} [in
st : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module R M] {p : …
-/
protected theorem ClosedComplemented.isClosed [ContinuousSub M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) :=
  h.isTopCompl_complement.isClosed

@[simp]
/-
**Submodule.closedComplemented_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
· 使用定理 `Submodule.isTopCompl_bot_top`：isTopCompl_bot_top : IsTopCompl (⊥ : Submo
dule R M) ⊤
-/
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  isTopCompl_bot_top.closedComplemented

@[simp]
/-
**Submodule.closedComplemented_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：closedComplemented_top : ClosedComplemented (⊤ : Submodule R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
· 使用定理 `Submodule.isTopCompl_top_bot`：isTopCompl_top_bot : IsTopCompl (⊤ : Submo
dule R M) ⊥
-/
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  isTopCompl_top_bot.closedComplemented
/-
**Submodule._root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse**
 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.ClosedComplemented :=
  f₁.isTopCompl_range_ker_of_leftInverse f₂ h |>.closedComplemented
/-
**Submodule._root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse** 
是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse [ContinuousSub M]
    (f₁ : M →L[R] N) (f₂ : N →L[R] M) (h : Function.RightInverse f₂ f₁) :
    f₁.ker.ClosedComplemented :=
  f₂.isTopCompl_range_ker_of_leftInverse f₁ h.leftInverse |>.symm.closedComplemented

set_option backward.isDefEq.respectTransparency.types false in
/-- If `p` is a closed complemented submodule,
then there exists a submodule `q` and a continuous linear equivalence `M ≃L[R] (p × q)` such that
`e (x : p) = (x, 0)`, `e (y : q) = (0, y)`, and `e.symm x = x.1 + x.2`.

In fact, the properties of `e` imply the properties of `e.symm` and vice versa,
but we provide both for convenience. -/
/-
**Submodule.ClosedComplemented.exists_submodule_equiv_prod** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule.ClosedComplemented`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [IsTopologicalAddGr
oup M] {p : Submodule R M},   p.ClosedComplemented →     ∃ q e, (∀ (x : ↥p), e ↑
x = (x, 0)) ∧ (∀ (y : ↥q), e ↑y = (0, y)) ∧ ∀ (x : ↥p × ↥q), e.symm x = ↑x.1 + ↑
x.2
参数：∀ (x : ↥p), e ↑x = (x, 0)；∀ (y : ↥q), e ↑y = (0, y)；x : ↥p × ↥q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ContinuousLinearMap.apply_val_ker`：apply_val_ker (f : M₁ ->SL[σ₁₂] M₂) (
x : f.ker) : f x = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
If `p` is a closed complemented submodule,
then there exists a submodule `q` and a continuous linear equivalence `M ≃L[R] (
p × q)` such that
`e (x : p) = (x, 0)`, `e (y : q) = (0, y)`, and `e.symm x = x.1 + x.2`.

In fact, the properties of `e` imply the properties of `e.symm` and vice versa,
but we provide both for convenience.
-/
lemma ClosedComplemented.exists_submodule_equiv_prod [IsTopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    ∃ (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (∀ x : p, e x = (x, 0)) ∧ (∀ y : q, e y = (0, y)) ∧ (∀ x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ ↦ by ext <;> simp [hf], fun _ ↦ by ext <;> simp, fun _ ↦ rfl⟩

end ClosedComplemented

section ContinuousLinearEquiv

variable [IsTopologicalAddGroup M]

/-- Two complementary submodules are topological complements if and only if the linear equivalence
`Submodule.prodEquivOfIsCompl` is continuous in the inverse direction. -/
/-
**Submodule.IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl** 是 Mathli
b 中的一个定理，位于命名空间 `Submodule.IsCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [IsTopologicalAddGroup M] (h : IsCompl p q),   Submodule.IsTopCompl p q ↔ Con
tinuous ⇑(p.prodEquivOfIsCompl q h).symm
参数：h : IsCompl p q；p.prodEquivOfIsCompl q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Two complementary submodules are topological complements if and only if the line
ar equivalence
`Submodule.prodEquivOfIsCompl` is continuous in the inverse direction.
-/
theorem IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.prodEquivOfIsCompl q h).symm :=
  ⟨fun hTop ↦ ((p.projectionOntoL q hTop).prod (q.projectionOntoL p hTop.symm)).continuous.congr
    fun x ↦ (prodEquivOfIsCompl_symm_apply h x).symm,
  fun hCont ↦ ⟨h, continuous_subtype_val.comp <| continuous_fst.comp hCont⟩⟩

/-- The linear equivalence `Submodule.prodEquivOfIsCompl` from a pair of complementary submodules is
always continuous. -/
/-
**Submodule.continuous_prodEquivOfIsCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：continuous_prodEquivOfIsCompl (h : IsCompl p q) : Continuous (p.prodEquivO
fIsCompl q h)
参数：h : IsCompl p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
The linear equivalence `Submodule.prodEquivOfIsCompl` from a pair of complementa
ry submodules is
always continuous.
-/
theorem continuous_prodEquivOfIsCompl (h : IsCompl p q) : Continuous (p.prodEquivOfIsCompl q h) :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/-- Two complementary submodules are topological complements if and only if the linear equivalence
`Submodule.prodEquivOfIsCompl` is a homeomorphism. -/
/-
**Submodule.IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl** 是 Mathlib 中
的一个定理，位于命名空间 `Submodule.IsCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [IsTopologicalAddGroup M] (h : IsCompl p q),   Submodule.IsTopCompl p q ↔ IsH
omeomorph ⇑(p.prodEquivOfIsCompl q h)
参数：h : IsCompl p q；p.prodEquivOfIsCompl q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.isHomeomorph_iff`：∀ {S : Type u_1} [inst : Semiring S] {S₁ :
 Type u_6} {M : Type u_7} {M₁ : Type u_8} [inst_1 : Semiring S₁]   {σ : S →+* S₁
} {σ' : S₁ →+* S} …
· 使用定理 `Submodule.IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl`：∀ {
R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst
_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q …
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Submodule.continuous_prodEquivOfIsCompl`：continuous_prodEquivOfIsCompl (
h : IsCompl p q) : Continuous (p.prodEquivOfIsCompl q h)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two complementary submodules are topological complements if and only if the line
ar equivalence
`Submodule.prodEquivOfIsCompl` is a homeomorphism.
-/
theorem IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ IsHomeomorph (p.prodEquivOfIsCompl q h) := by
  rw [(p.prodEquivOfIsCompl q h).isHomeomorph_iff,
    isTopCompl_iff_continuous_symm_prodEquivOfIsCompl, and_iff_right]
  exact continuous_prodEquivOfIsCompl h

variable (p q) in
/-- If two submodules are topological complements, then the linear equivalence
`Submodule.prodEquivOfIsCompl` is a homeomorphism, bundled as a continuous linear equivalence. -/
/-
**Submodule.prodEquivOfIsTopCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：prodEquivOfIsTopCompl (h : IsTopCompl p q) : (p × q) ≃L[R] M
参数：h : IsTopCompl p q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …

--- 原说明 ---
If two submodules are topological complements, then the linear equivalence
`Submodule.prodEquivOfIsCompl` is a homeomorphism, bundled as a continuous linea
r equivalence.
-/
noncomputable def prodEquivOfIsTopCompl (h : IsTopCompl p q) : (p × q) ≃L[R] M :=
  { p.prodEquivOfIsCompl q h.isCompl with
    continuous_toFun := continuous_prodEquivOfIsCompl h.isCompl
    continuous_invFun := h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp h }

@[simp]
/-
**Submodule.toLinearEquiv_prodEquivOfIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：toLinearEquiv_prodEquivOfIsTopCompl (h : IsTopCompl p q) : (prodEquivOfIsT
opCompl p q h : (p × q) ≃ₗ[R] M) = p.prodEquivOfIsCompl q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    (prodEquivOfIsTopCompl p q h : (p × q) ≃ₗ[R] M) = p.prodEquivOfIsCompl q h.isCompl :=
  rfl

@[simp]
/-
**Submodule.coe_prodEquivOfIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_prodEquivOfIsTopCompl (h : IsTopCompl p q) : ⇑(prodEquivOfIsTopCompl p
 q h) = p.prodEquivOfIsCompl q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    ⇑(prodEquivOfIsTopCompl p q h) = p.prodEquivOfIsCompl q h.isCompl :=
  rfl

@[simp]
/-
**Submodule.coe_symm_prodEquivOfIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：coe_symm_prodEquivOfIsTopCompl (h : IsTopCompl p q) : ⇑(prodEquivOfIsTopCo
mpl p q h).symm = (p.prodEquivOfIsCompl q h.isCompl).symm
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    ⇑(prodEquivOfIsTopCompl p q h).symm = (p.prodEquivOfIsCompl q h.isCompl).symm :=
  rfl
/-
**Submodule.prodEquivOfIsTopCompl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prodEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : p × q) : prodEquivOf
IsTopCompl p q h x = (x.1 : M) + x.2
参数：h : IsTopCompl p q；x : p × q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : p × q) :
    prodEquivOfIsTopCompl p q h x = (x.1 : M) + x.2 :=
  rfl
/-
**Submodule.prodEquivOfIsTopCompl_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：prodEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (x : M) : (prodEquiv
OfIsTopCompl p q h).symm x = ((p.projectionOntoL q h x, q.projectionOntoL p h.sy
mm x) : p × q)
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem prodEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (x : M) :
    (prodEquivOfIsTopCompl p q h).symm x =
      ((p.projectionOntoL q h x, q.projectionOntoL p h.symm x) : p × q) :=
  prodEquivOfIsCompl_symm_apply h.isCompl x

/-- Two complementary submodules are topological complements if and only if the linear equivalence
`Submodule.quotientEquivOfIsCompl` is continuous. -/
/-
**Submodule.IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl** 是 Mathlib
 中的一个定理，位于命名空间 `Submodule.IsCompl`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace
 M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {p q : Submodule R 
M} [IsTopologicalAddGroup M] (h : IsCompl p q),   Submodule.IsTopCompl p q ↔ Con
tinuous ⇑(p.quotientEquivOfIsCompl q h)
参数：h : IsCompl p q；p.quotientEquivOfIsCompl q h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `Submodule.isQuotientMap_mkQL`：isQuotientMap_mkQL : IsQuotientMap S.mkQL
· 使用定理 `Submodule.isTopCompl_comm`：isTopCompl_comm [ContinuousSub M] : IsTopComp
l p q ↔ IsTopCompl q p
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Submodule.IsCompl.isTopCompl_iff_projectionOnto`：∀ {R : Type u_1} [inst 
: Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]
   [inst_3 : _root_.Module R M] {p q …
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x

--- 原说明 ---
Two complementary submodules are topological complements if and only if the line
ar equivalence
`Submodule.quotientEquivOfIsCompl` is continuous.
-/
theorem IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.quotientEquivOfIsCompl q h) := by
  rw [p.isQuotientMap_mkQL.continuous_iff, isTopCompl_comm]
  exact h.symm.isTopCompl_iff_projectionOnto

variable (p q) in
/-- If two submodules are topological complements, then the linear equivalence
`Submodule.quotientEquivOfIsCompl` is a homeomorphism, bundled as a continuous linear
equivalence. -/
/-
**Submodule.quotientEquivOfIsTopCompl** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientEquivOfIsTopCompl (h : IsTopCompl p q) : (M ⧸ p) ≃L[R] q
参数：h : IsTopCompl p q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …

--- 原说明 ---
If two submodules are topological complements, then the linear equivalence
`Submodule.quotientEquivOfIsCompl` is a homeomorphism, bundled as a continuous l
inear
equivalence.
-/
noncomputable def quotientEquivOfIsTopCompl (h : IsTopCompl p q) : (M ⧸ p) ≃L[R] q :=
  { p.quotientEquivOfIsCompl q h.isCompl with
    continuous_toFun := h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp h
    continuous_invFun := (p.mkQL.comp q.subtypeL).continuous }

@[simp]
/-
**Submodule.toLinearEquiv_quotientEquivOfIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmodule`。
形式化陈述：toLinearEquiv_quotientEquivOfIsTopCompl (h : IsTopCompl p q) : (quotientEq
uivOfIsTopCompl p q h : (M ⧸ p) ≃ₗ[R] q) = p.quotientEquivOfIsCompl q h.isCompl
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_quotientEquivOfIsTopCompl (h : IsTopCompl p q) :
    (quotientEquivOfIsTopCompl p q h : (M ⧸ p) ≃ₗ[R] q) = p.quotientEquivOfIsCompl q h.isCompl :=
  rfl
/-
**Submodule.quotientEquivOfIsTopCompl_comp_mkQL** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：quotientEquivOfIsTopCompl_comp_mkQL (h : IsTopCompl p q) : (quotientEquivO
fIsTopCompl p q h) ∘L p.mkQL = q.projectionOntoL p h.symm
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfIsTopCompl_comp_mkQL (h : IsTopCompl p q) :
    (quotientEquivOfIsTopCompl p q h) ∘L p.mkQL = q.projectionOntoL p h.symm :=
  rfl

@[simp]
/-
**Submodule.quotientEquivOfIsTopCompl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：quotientEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : M ⧸ p) : quotien
tEquivOfIsTopCompl p q h x = p.quotientEquivOfIsCompl q h.isCompl x
参数：h : IsTopCompl p q；x : M ⧸ p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : M ⧸ p) :
    quotientEquivOfIsTopCompl p q h x = p.quotientEquivOfIsCompl q h.isCompl x :=
  rfl

@[simp]
/-
**Submodule.quotientEquivOfIsTopCompl_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：quotientEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (y : q) : (quoti
entEquivOfIsTopCompl p q h).symm y = p.mkQ y
参数：h : IsTopCompl p q；y : q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (y : q) :
    (quotientEquivOfIsTopCompl p q h).symm y = p.mkQ y :=
  rfl
/-
**Submodule.quotientEquivOfIsTopCompl_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：quotientEquivOfIsTopCompl_apply_mk (h : IsTopCompl p q) (x : M) : quotient
EquivOfIsTopCompl p q h (Quotient.mk x) = q.projectionOnto p h.isCompl.symm x
参数：h : IsTopCompl p q；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.quotientEquivOfIsCompl_apply_mk`：quotientEquivOfIsCompl_apply_
mk (h : IsCompl p q) (x : E) : quotientEquivOfIsCompl p q h (Quotient.mk x) = q.
projectionOnto p h.symm x
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
-/
theorem quotientEquivOfIsTopCompl_apply_mk (h : IsTopCompl p q) (x : M) :
    quotientEquivOfIsTopCompl p q h (Quotient.mk x) = q.projectionOnto p h.isCompl.symm x :=
  quotientEquivOfIsCompl_apply_mk h.isCompl x

end ContinuousLinearEquiv

end Submodule

namespace ContinuousLinearMap

variable {R : Type*} [Ring R] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module R E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  {p q : Submodule R E}

/-- Given continuous linear maps `φ : p →L[R] F` and `ψ : q →L[R] F` from topological complement
submodules `p` and `q` of `E`, `ContinuousLinearMap.ofIsCompl` is the induced continuous linear map
`E →L[R] F` over the entire module.

This is the continuous version of `LinearMap.ofIsCompl`. -/
/-
**ContinuousLinearMap.ofIsTopCompl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) : E ->
L[R] F
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given continuous linear maps `φ : p →L[R] F` and `ψ : q →L[R] F` from topologica
l complement
submodules `p` and `q` of `E`, `ContinuousLinearMap.ofIsCompl` is the induced co
ntinuous linear map
`E →L[R] F` over the entire module.

This is the continuous version of `LinearMap.ofIsCompl`.
-/
noncomputable def ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) : E →L[R] F :=
  φ.coprod ψ ∘L ↑(prodEquivOfIsTopCompl p q h).symm
/-
**ContinuousLinearMap.ofIsTopCompl_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：ofIsTopCompl_eq_add (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
 : ofIsTopCompl h φ ψ = φ ∘L p.projectionOntoL q h + ψ ∘L q.projectionOntoL p h.
symm
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `ContinuousLinearMap.coprod_apply`：∀ {R : Type u_1} {M : Type u_3} {M₁ : 
Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]   [i
nst_2 : TopologicalSpa…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsTopCompl_eq_add (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    ofIsTopCompl h φ ψ = φ ∘L p.projectionOntoL q h + ψ ∘L q.projectionOntoL p h.symm := by
  ext; simp [ofIsTopCompl]

@[simp]
/-
**ContinuousLinearMap.toLinearMap_ofIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：toLinearMap_ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[
R] F) : (ofIsTopCompl h φ ψ : E ->ₗ[R] F) = LinearMap.ofIsCompl h.isCompl φ ψ
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    (ofIsTopCompl h φ ψ : E →ₗ[R] F) = LinearMap.ofIsCompl h.isCompl φ ψ :=
  rfl

@[simp]
/-
**ContinuousLinearMap.ofIsTopCompl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：ofIsTopCompl_apply (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) 
(x : E) : ofIsTopCompl h φ ψ (x : E) = LinearMap.ofIsCompl h.isCompl φ ψ x
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofIsTopCompl_apply (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) (x : E) :
    ofIsTopCompl h φ ψ (x : E) = LinearMap.ofIsCompl h.isCompl φ ψ x :=
  rfl
/-
**ContinuousLinearMap.ofIsTopCompl_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：ofIsTopCompl_apply_left (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R
] F) (x : p) : ofIsTopCompl h φ ψ (x : E) = φ x
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ofIsCompl_apply_left`：ofIsCompl_apply_left (h : IsCompl p q) {
φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p) : ofIsCompl h φ ψ (u : E) = φ u
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsTopCompl_apply_left (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) (x : p) :
    ofIsTopCompl h φ ψ (x : E) = φ x := by simp
/-
**ContinuousLinearMap.ofIsTopCompl_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：ofIsTopCompl_apply_right (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[
R] F) (x : q) : ofIsTopCompl h φ ψ (x : E) = ψ x
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ofIsCompl_apply_right`：ofIsCompl_apply_right (h : IsCompl p q)
 {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q) : ofIsCompl h φ ψ (v : E) = ψ v
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsTopCompl_apply_right (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) (x : q) :
    ofIsTopCompl h φ ψ (x : E) = ψ x := by simp
/-
**ContinuousLinearMap.ofIsTopCompl_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：ofIsTopCompl_eq (h : IsTopCompl p q) {φ : p ->L[R] F} {ψ : q ->L[R] F} {χ 
: E ->L[R] F} (hφ : forall u : p, φ u = χ u) (hψ : forall u : q, ψ u = χ u) : of
IsTopCompl h φ ψ = χ
参数：h : IsTopCompl p q；hφ : forall u : p, φ u = χ u；hψ : forall u : q, ψ u = χ u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `LinearMap.ofIsCompl_eq`：ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} 
{ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F} (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u
 = χ u) : of…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ofIsTopCompl_eq (h : IsTopCompl p q) {φ : p →L[R] F} {ψ : q →L[R] F} {χ : E →L[R] F}
    (hφ : ∀ u : p, φ u = χ u) (hψ : ∀ u : q, ψ u = χ u) : ofIsTopCompl h φ ψ = χ := by
  ext; simp [LinearMap.ofIsCompl_eq h.isCompl hφ, hψ]

@[simp]
/-
**ContinuousLinearMap.ofIsTopCompl_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：ofIsTopCompl_zero (h : IsTopCompl p q) : (ofIsTopCompl h 0 0 : E ->L[R] F)
 = 0
参数：h : IsTopCompl p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `LinearMap.ofIsCompl_zero`：ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl 
h 0 0 : E ->ₗ[R] F) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsTopCompl_zero (h : IsTopCompl p q) : (ofIsTopCompl h 0 0 : E →L[R] F) = 0 := by
  ext; simp

@[simp]
/-
**ContinuousLinearMap.ofIsTopCompl_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：ofIsTopCompl_add (h : IsTopCompl p q) (φ₁ φ₂ : p ->L[R] F) (ψ₁ ψ₂ : q ->L[
R] F) : ofIsTopCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsTopCompl h φ₁ ψ₁ + ofIsTopCompl
 h φ₂ ψ₂
参数：h : IsTopCompl p q；φ₁ φ₂ : p ->L[R] F；ψ₁ ψ₂ : q ->L[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.ofIsCompl_add`：ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p ->ₗ[
R] F} {ψ₁ ψ₂ : q ->ₗ[R] F} : ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁
 + ofIsCompl …
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsTopCompl_add (h : IsTopCompl p q) (φ₁ φ₂ : p →L[R] F) (ψ₁ ψ₂ : q →L[R] F) :
    ofIsTopCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsTopCompl h φ₁ ψ₁ + ofIsTopCompl h φ₂ ψ₂ := by
  ext; simp
/-
**ContinuousLinearMap.range_ofIsTopCompl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：range_ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) 
: LinearMap.range (ofIsTopCompl h φ ψ : E ->ₗ[R] F) = φ.range ⊔ ψ.range
参数：h : IsTopCompl p q；φ : p ->L[R] F；ψ : q ->L[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_ofIsCompl`：range_ofIsCompl (hpq : IsCompl p q) {φ : p ->
ₗ[R] F} {ψ : q ->ₗ[R] F} : range (ofIsCompl hpq φ ψ) = range φ ⊔ range ψ
· 使用定理 `Submodule.IsTopCompl.isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_
.Module R M] {p q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_ofIsTopCompl (h : IsTopCompl p q) (φ : p →L[R] F) (ψ : q →L[R] F) :
    LinearMap.range (ofIsTopCompl h φ ψ : E →ₗ[R] F) = φ.range ⊔ ψ.range := by simp

end ContinuousLinearMap

