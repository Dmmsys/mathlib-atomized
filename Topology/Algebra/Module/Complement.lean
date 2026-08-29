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
/--
Definition of `IsTopCompl` / `IsTopCompl` 的定义

English:
structure IsTopCompl
  parameters: (p q : Submodule R M)
  axioms and operations (2):
    - isCompl : IsCompl p q
    - continuous_projection : Continuous (p.projection q isCompl)

中文:
结构 是TopCompl
  参数: (p q : 子模 R M)
  公理与运算 (2 个):
    - isCompl : 是补集 p q
    - continuous_projection : 连续 (p.projection q isCompl)
-/
structure IsTopCompl (p q : Submodule R M) : Prop where
  isCompl : IsCompl p q
  continuous_projection : Continuous (p.projection q isCompl)

/--
Definition of `ClosedComplemented` / `ClosedComplemented` 的定义

English:
definition ClosedComplemented
  signature: (p : Submodule R M)
  body: exists f : M ->L[R] p, forall x : p, f x = x

中文:
定义 ClosedComplemented
  签名: (p : 子模 R M)
  定义体: exists f : M ->L[R] p, forall x : p, f x = x
-/
def ClosedComplemented (p : Submodule R M) : Prop :=
  exists f : M ->L[R] p, forall x : p, f x = x

variable {p q : Submodule R M}

section IsTopCompl

/--
theorem `IsCompl.isTopCompl_iff` / 定理 `IsCompl.isTopCompl_iff`

English:
theorem IsCompl.isTopCompl_iff
  given: (h : IsCompl p q)
  proof: ⟨IsTopCompl.continuous_projection, fun h' => ⟨h, h'⟩⟩

中文:
定理 是补集.isTopCompl_iff
  条件: (h : 是补集 p q)
  证明: ⟨IsTopCompl.continuous_projection, fun h' => ⟨h, h'⟩⟩

Depends on / 依赖: IsTopCompl, IsTopCompl.continuous_projection, continuous_projection
-/
theorem IsCompl.isTopCompl_iff (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projection q h) :=
  ⟨IsTopCompl.continuous_projection, fun h' => ⟨h, h'⟩⟩

/--
theorem `IsCompl.isTopCompl_iff_projectionOnto` / 定理 `IsCompl.isTopCompl_iff_projectionOnto`

English:
theorem IsCompl.isTopCompl_iff_projectionOnto
  given: (h : IsCompl p q)
  proof: by
  rw [h.isTopCompl_iff]; rw [IsInducing.subtypeVal.continuous_iff]
  rfl

@[deprecated (since := "2026-05-05")] alias IsCompl.isTopCompl_iff_linearProjOfIsCompl :=
  IsCompl.isTopCompl_iff_projectionOnto

中文:
定理 是补集.isTopCompl_iff_projectionOnto
  条件: (h : 是补集 p q)
  证明: by
  rw [h.isTopCompl_iff]; rw [IsInducing.subtypeVal.continuous_iff]
  rfl

@[deprecated (since := "2026-05-05")] alias IsCompl.isTopCompl_iff_linearProjOfIsCompl :=
  IsCompl.isTopCompl_iff_projectionOnto

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuous_iff, continuous_iff, h.isTopCompl_iff, isTopCompl_iff, subtypeVal
-/
theorem IsCompl.isTopCompl_iff_projectionOnto (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.projectionOnto q h) := by
  rw [h.isTopCompl_iff]; rw [IsInducing.subtypeVal.continuous_iff]
  rfl

@[deprecated (since := "2026-05-05")] alias IsCompl.isTopCompl_iff_linearProjOfIsCompl :=
  IsCompl.isTopCompl_iff_projectionOnto

/--
theorem `IsTopCompl.continuous_projectionOnto` / 定理 `IsTopCompl.continuous_projectionOnto`

English:
theorem IsTopCompl.continuous_projectionOnto
  given: (h : IsTopCompl p q)
  proof: h.isCompl.isTopCompl_iff_projectionOnto.mp h

@[deprecated (since := "2026-05-05")] alias IsTopCompl.continuous_linearProjOfIsCompl :=
  IsTopCompl.continuous_projectionOnto

中文:
定理 是TopCompl.continuous_projectionOnto
  条件: (h : 是TopCompl p q)
  证明: h.isCompl.isTopCompl_iff_projectionOnto.mp h

@[deprecated (since := "2026-05-05")] alias IsTopCompl.continuous_linearProjOfIsCompl :=
  IsTopCompl.continuous_projectionOnto

Depends on / 依赖: h.isCompl.isTopCompl_iff_projectionOnto.mp, isCompl, isTopCompl_iff_projectionOnto
-/
theorem IsTopCompl.continuous_projectionOnto (h : IsTopCompl p q) :
    Continuous (p.projectionOnto q h.isCompl) :=
  h.isCompl.isTopCompl_iff_projectionOnto.mp h

@[deprecated (since := "2026-05-05")] alias IsTopCompl.continuous_linearProjOfIsCompl :=
  IsTopCompl.continuous_projectionOnto

/--
theorem `IsTopCompl.symm` / 定理 `IsTopCompl.symm`

English:
theorem IsTopCompl.symm
  given: [ContinuousSub M] (h : IsTopCompl p q)
  statement: IsTopCompl q p where
  proof: h.isCompl.symm
  continuous_projection := by
    rw [projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection

中文:
定理 是TopCompl.symm
  条件: [余ntinuousSub M] (h : 是TopCompl p q)
  结论: 是TopCompl q p where
  证明: h.isCompl.symm
  continuous_projection := by
    rw [projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection
-/
protected theorem IsTopCompl.symm [ContinuousSub M] (h : IsTopCompl p q) : IsTopCompl q p where
  isCompl := h.isCompl.symm
  continuous_projection := by
    rw [projection_eq_id_sub_projection h.isCompl]
    exact continuous_id.sub h.continuous_projection

/--
theorem `isTopCompl_comm` / 定理 `isTopCompl_comm`

English:
theorem isTopCompl_comm
  given: [ContinuousSub M]
  statement: IsTopCompl p q ↔ IsTopCompl q p
  proof: ⟨IsTopCompl.symm, IsTopCompl.symm⟩

中文:
定理 isTopCompl_comm
  条件: [余ntinuousSub M]
  结论: 是TopCompl p q ↔ 是TopCompl q p
  证明: ⟨IsTopCompl.symm, IsTopCompl.symm⟩

Depends on / 依赖: IsTopCompl, IsTopCompl.symm
-/
theorem isTopCompl_comm [ContinuousSub M] : IsTopCompl p q ↔ IsTopCompl q p :=
  ⟨IsTopCompl.symm, IsTopCompl.symm⟩

open LinearMap in
/--
theorem `_root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl` / 定理 `_root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl`

English:
theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl
  statement: {f : M ->L[R] M}
  proof: hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_projection ▸ f.continuous

中文:
定理 _root_.连续线性映射.IsIdempotentElem.isTopCompl
  结论: {f : M ->L[R] M}
  证明: hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_projection ▸ f.continuous

Depends on / 依赖: hf.toLinearMap.isCompl, isCompl, toLinearMap
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.isTopCompl {f : M ->L[R] M}
    (hf : IsIdempotentElem f) : IsTopCompl f.range f.ker where
  isCompl := hf.toLinearMap.isCompl
  continuous_projection := hf.toLinearMap.eq_projection ▸ f.continuous

/--
theorem `isTopCompl_bot_top` / 定理 `isTopCompl_bot_top`

English:
theorem isTopCompl_bot_top
  proof: by
  have : IsIdempotentElem (0 : M ->L[R] M) := .zero
  simpa using this.isTopCompl

中文:
定理 isTopCompl_bot_top
  证明: by
  have : IsIdempotentElem (0 : M ->L[R] M) := .zero
  simpa using this.isTopCompl

Depends on / 依赖: IsIdempotentElem, isTopCompl, this.isTopCompl
-/
theorem isTopCompl_bot_top :
    IsTopCompl (⊥ : Submodule R M) ⊤ := by
  have : IsIdempotentElem (0 : M ->L[R] M) := .zero
  simpa using this.isTopCompl

/--
theorem `isTopCompl_top_bot` / 定理 `isTopCompl_top_bot`

English:
theorem isTopCompl_top_bot
  proof: by
  have : IsIdempotentElem (.id R M : M ->L[R] M) := .one
  simpa using this.isTopCompl

中文:
定理 isTopCompl_top_bot
  证明: by
  have : IsIdempotentElem (.id R M : M ->L[R] M) := .one
  simpa using this.isTopCompl

Depends on / 依赖: IsIdempotentElem, isTopCompl, this.isTopCompl
-/
theorem isTopCompl_top_bot :
    IsTopCompl (⊤ : Submodule R M) ⊥ := by
  have : IsIdempotentElem (.id R M : M ->L[R] M) := .one
  simpa using this.isTopCompl

open LinearMap in
/--
theorem `_root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse` / 定理 `_root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse`

English:
theorem _root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse
  proof: let p := f₁ ∘L f₂
  have p_idem : IsIdempotentElem p := by ext x; simp [p, h (f₂ x)]
have range_p : p.range = f₁.range := range_comp_of_range_eq_top _
    range_eq_top_of_surjective _ h.surjective
have ker_p : p.ker = f₂.ker := ker_comp_of_ker_eq_bot _
    ker_eq_bot_of_injective h.injective
  range

中文:
定理 _root_.连续线性映射.isTopCompl_range_ker_of_leftInverse
  证明: let p := f₁ ∘L f₂
  have p_idem : IsIdempotentElem p := by ext x; simp [p, h (f₂ x)]
have range_p : p.range = f₁.range := range_comp_of_range_eq_top _
    range_eq_top_of_surjective _ h.surjective
have ker_p : p.ker = f₂.ker := ker_comp_of_ker_eq_bot _
    ker_eq_bot_of_injective h.injective
  range

Depends on / 依赖: IsIdempotentElem, h.injective, h.surjective, injective, isTopCompl, ker_comp_of_ker_eq_bot, ker_eq_bot_of_injective, ker_p, p.ker, p.range, p_idem, p_idem.isTopCompl, range_comp_of_range_eq_top, range_eq_top_of_surjective, range_p, surjective
-/
theorem _root_.ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse
    (f₁ : M ->L[R] N) (f₂ : N ->L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.IsTopCompl f₂.ker :=
  let p := f₁ ∘L f₂
  have p_idem : IsIdempotentElem p := by ext x; simp [p, h (f₂ x)]
have range_p : p.range = f₁.range := range_comp_of_range_eq_top _
    range_eq_top_of_surjective _ h.surjective
have ker_p : p.ker = f₂.ker := ker_comp_of_ker_eq_bot _
    ker_eq_bot_of_injective h.injective
  range_p ▸ ker_p ▸ p_idem.isTopCompl

/--
theorem `_root_.ContinuousLinearMap.isTopCompl_of_proj` / 定理 `_root_.ContinuousLinearMap.isTopCompl_of_proj`

English:
theorem _root_.ContinuousLinearMap.isTopCompl_of_proj
  given: {f : M ->L[R] p} (hf : forall x : p, f x = x)
  proof: by
  simpa using p.subtypeL.isTopCompl_range_ker_of_leftInverse f hf

中文:
定理 _root_.连续线性映射.isTopCompl_of_proj
  条件: {f : M ->L[R] p} (hf : 对任意 x : p, f x = x)
  证明: by
  simpa using p.subtypeL.isTopCompl_range_ker_of_leftInverse f hf

Depends on / 依赖: isTopCompl_range_ker_of_leftInverse, p.subtypeL.isTopCompl_range_ker_of_leftInverse, subtypeL
-/
theorem _root_.ContinuousLinearMap.isTopCompl_of_proj {f : M ->L[R] p} (hf : forall x : p, f x = x) :
    IsTopCompl p f.ker := by
  simpa using p.subtypeL.isTopCompl_range_ker_of_leftInverse f hf

section projectionOnto

variable (p q) in
/--
Definition of `projectionOntoL` / `projectionOntoL` 的定义

English:
definition projectionOntoL
  signature: (h : IsTopCompl p q)
  body: ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]

中文:
定义 projectionOntoL
  签名: (h : 是TopCompl p q)
  定义体: ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]

Depends on / 依赖: continuous_projectionOnto, h.continuous_projectionOnto, h.isCompl, isCompl, p.projectionOnto, projectionOnto
-/
noncomputable def projectionOntoL (h : IsTopCompl p q) : M ->L[R] p :=
  ⟨p.projectionOnto q h.isCompl, h.continuous_projectionOnto⟩

@[simp]
/--
theorem `toLinearMap_projectionOntoL` / 定理 `toLinearMap_projectionOntoL`

English:
theorem toLinearMap_projectionOntoL
  given: (h : IsTopCompl p q)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_projectionOntoL
  条件: (h : 是TopCompl p q)
  证明: rfl

@[simp]
-/
theorem toLinearMap_projectionOntoL (h : IsTopCompl p q) :
    p.projectionOntoL q h = p.projectionOnto q h.isCompl :=
  rfl

@[simp]
/--
theorem `projectionOntoL_apply_left` / 定理 `projectionOntoL_apply_left`

English:
theorem projectionOntoL_apply_left
  given: (h : IsTopCompl p q) (x : p)
  proof: projectionOnto_apply_left h.isCompl x

@[simp]

中文:
定理 projectionOntoL_apply_left
  条件: (h : 是TopCompl p q) (x : p)
  证明: projectionOnto_apply_left h.isCompl x

@[simp]

Depends on / 依赖: h.isCompl, isCompl, projectionOnto_apply_left
-/
theorem projectionOntoL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionOntoL q h x = x :=
  projectionOnto_apply_left h.isCompl x

@[simp]
/--
theorem `coe_projectionOntoL` / 定理 `coe_projectionOntoL`

English:
theorem coe_projectionOntoL
  given: (h : IsTopCompl p q)
  proof: rfl

中文:
定理 coe_projectionOntoL
  条件: (h : 是TopCompl p q)
  证明: rfl
-/
theorem coe_projectionOntoL (h : IsTopCompl p q) :
    ⇑(p.projectionOntoL q h) = p.projectionOnto q h.isCompl :=
  rfl

/--
theorem `range_projectionOntoL` / 定理 `range_projectionOntoL`

English:
theorem range_projectionOntoL
  given: (h : IsTopCompl p q)
  statement: (p.projectionOntoL q h).range = ⊤
  proof: by
  simp

中文:
定理 range_projectionOntoL
  条件: (h : 是TopCompl p q)
  结论: (p.projectionOntoL q h).range = ⊤
  证明: by
  simp
-/
theorem range_projectionOntoL (h : IsTopCompl p q) : (p.projectionOntoL q h).range = ⊤ := by
  simp

/--
theorem `projectionOntoL_surjective` / 定理 `projectionOntoL_surjective`

English:
theorem projectionOntoL_surjective
  given: (h : IsTopCompl p q)
  statement: Surjective (p.projectionOntoL q h)
  proof: projectionOnto_surjective h.isCompl

中文:
定理 projectionOntoL_surjective
  条件: (h : 是TopCompl p q)
  结论: 满射 (p.projectionOntoL q h)
  证明: projectionOnto_surjective h.isCompl

Depends on / 依赖: h.isCompl, isCompl, projectionOnto_surjective
-/
theorem projectionOntoL_surjective (h : IsTopCompl p q) : Surjective (p.projectionOntoL q h) :=
  projectionOnto_surjective h.isCompl

/--
theorem `projectionOntoL_apply_eq_zero_iff` / 定理 `projectionOntoL_apply_eq_zero_iff`

English:
theorem projectionOntoL_apply_eq_zero_iff
  given: (h : IsTopCompl p q) {x : M}
  proof: projectionOnto_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff

中文:
定理 projectionOntoL_apply_eq_zero_iff
  条件: (h : 是TopCompl p q) {x : M}
  证明: projectionOnto_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff

Depends on / 依赖: h.isCompl, isCompl, projectionOnto_apply_eq_zero_iff
-/
theorem projectionOntoL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionOntoL q h x = 0 ↔ x in q :=
  projectionOnto_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionOntoL_apply_eq_zero_of_mem_right⟩ :=
  projectionOntoL_apply_eq_zero_iff

/--
theorem `projectionOntoL_apply_right` / 定理 `projectionOntoL_apply_right`

English:
theorem projectionOntoL_apply_right
  given: (h : IsTopCompl p q) (x : q)
  proof: projectionOntoL_apply_eq_zero_of_mem_right h x.2

中文:
定理 projectionOntoL_apply_right
  条件: (h : 是TopCompl p q) (x : q)
  证明: projectionOntoL_apply_eq_zero_of_mem_right h x.2

Depends on / 依赖: projectionOntoL_apply_eq_zero_of_mem_right
-/
theorem projectionOntoL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionOntoL q h x = 0 :=
  projectionOntoL_apply_eq_zero_of_mem_right h x.2

/--
theorem `ker_projectionOntoL` / 定理 `ker_projectionOntoL`

English:
theorem ker_projectionOntoL
  given: (h : IsTopCompl p q)
  proof: by
  simp

中文:
定理 ker_projectionOntoL
  条件: (h : 是TopCompl p q)
  证明: by
  simp
-/
theorem ker_projectionOntoL (h : IsTopCompl p q) :
    (p.projectionOntoL q h).ker = q := by
  simp

/--
theorem `isQuotientMap_projectionOntoL` / 定理 `isQuotientMap_projectionOntoL`

English:
theorem isQuotientMap_projectionOntoL
  given: (h : IsTopCompl p q)
  proof: .of_inverse continuous_subtype_val (p.projectionOntoL q h).continuous
    (projectionOntoL_apply_left h)

中文:
定理 isQuotientMap_projectionOntoL
  条件: (h : 是TopCompl p q)
  证明: .of_inverse continuous_subtype_val (p.projectionOntoL q h).continuous
    (projectionOntoL_apply_left h)

Depends on / 依赖: continuous, continuous_subtype_val, of_inverse, p.projectionOntoL, projectionOntoL, projectionOntoL_apply_left
-/
theorem isQuotientMap_projectionOntoL (h : IsTopCompl p q) :
    IsQuotientMap (p.projectionOntoL q h) :=
  .of_inverse continuous_subtype_val (p.projectionOntoL q h).continuous
    (projectionOntoL_apply_left h)

end projectionOnto

section projection

variable (p q) in
/--
Definition of `projectionL` / `projectionL` 的定义

English:
definition projectionL
  signature: (h : IsTopCompl p q)
  body: p.subtypeL ∘L p.projectionOntoL q h

@[simp]

中文:
定义 projectionL
  签名: (h : 是TopCompl p q)
  定义体: p.subtypeL ∘L p.projectionOntoL q h

@[simp]

Depends on / 依赖: p.projectionOntoL, p.subtypeL, projectionOntoL, subtypeL
-/
noncomputable def projectionL (h : IsTopCompl p q) : M ->L[R] M :=
  p.subtypeL ∘L p.projectionOntoL q h

@[simp]
/--
theorem `coe_projectionL` / 定理 `coe_projectionL`

English:
theorem coe_projectionL
  given: (h : IsTopCompl p q)
  proof: rfl

@[simp]

中文:
定理 coe_projectionL
  条件: (h : 是TopCompl p q)
  证明: rfl

@[simp]
-/
theorem coe_projectionL (h : IsTopCompl p q) :
    ⇑(p.projectionL q h) = p.projection q h.isCompl :=
  rfl

@[simp]
/--
theorem `toLinearMap_projectionL` / 定理 `toLinearMap_projectionL`

English:
theorem toLinearMap_projectionL
  given: (h : IsTopCompl p q)
  proof: rfl

中文:
定理 toLinearMap_projectionL
  条件: (h : 是TopCompl p q)
  证明: rfl
-/
theorem toLinearMap_projectionL (h : IsTopCompl p q) :
    p.projectionL q h = p.projection q h.isCompl :=
  rfl

/--
theorem `projectionL_apply` / 定理 `projectionL_apply`

English:
theorem projectionL_apply
  given: (h : IsTopCompl p q) (x : M)
  proof: rfl

@[simp]

中文:
定理 projectionL_apply
  条件: (h : 是TopCompl p q) (x : M)
  证明: rfl

@[simp]
-/
theorem projectionL_apply (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = p.projectionOntoL q h x :=
  rfl

@[simp]
/--
theorem `coe_projectionOntoL_apply` / 定理 `coe_projectionOntoL_apply`

English:
theorem coe_projectionOntoL_apply
  given: (h : IsTopCompl p q) (x : M)
  proof: rfl

中文:
定理 coe_projectionOntoL_apply
  条件: (h : 是TopCompl p q) (x : M)
  证明: rfl
-/
theorem coe_projectionOntoL_apply (h : IsTopCompl p q) (x : M) :
    (p.projectionOntoL q h x : M) = p.projectionL q h x :=
  rfl

/--
theorem `projectionL_apply_mem` / 定理 `projectionL_apply_mem`

English:
theorem projectionL_apply_mem
  given: (h : IsTopCompl p q) (x : M)
  proof: SetLike.coe_mem _

中文:
定理 projectionL_apply_mem
  条件: (h : 是TopCompl p q) (x : M)
  证明: SetLike.coe_mem _

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem
-/
theorem projectionL_apply_mem (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x in p :=
  SetLike.coe_mem _

/--
theorem `projectionL_apply_left` / 定理 `projectionL_apply_left`

English:
theorem projectionL_apply_left
  given: (h : IsTopCompl p q) (x : p)
  proof: projection_apply_left h.isCompl x

中文:
定理 projectionL_apply_left
  条件: (h : 是TopCompl p q) (x : p)
  证明: projection_apply_left h.isCompl x

Depends on / 依赖: h.isCompl, isCompl, projection_apply_left
-/
theorem projectionL_apply_left (h : IsTopCompl p q) (x : p) :
    p.projectionL q h x = x :=
  projection_apply_left h.isCompl x

/--
theorem `range_projectionL` / 定理 `range_projectionL`

English:
theorem range_projectionL
  given: (h : IsTopCompl p q)
  proof: by
  simp

中文:
定理 range_projectionL
  条件: (h : 是TopCompl p q)
  证明: by
  simp
-/
theorem range_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).range = p := by
  simp

/--
theorem `projectionL_apply_eq_zero_iff` / 定理 `projectionL_apply_eq_zero_iff`

English:
theorem projectionL_apply_eq_zero_iff
  given: (h : IsTopCompl p q) {x : M}
  proof: projection_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff

中文:
定理 projectionL_apply_eq_zero_iff
  条件: (h : 是TopCompl p q) {x : M}
  证明: projection_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff

Depends on / 依赖: h.isCompl, isCompl, projection_apply_eq_zero_iff
-/
theorem projectionL_apply_eq_zero_iff (h : IsTopCompl p q) {x : M} :
    p.projectionL q h x = 0 ↔ x in q :=
  projection_apply_eq_zero_iff h.isCompl

alias ⟨_, projectionL_apply_eq_zero_of_mem_right⟩ :=
  projectionL_apply_eq_zero_iff

/--
theorem `projectionL_apply_right` / 定理 `projectionL_apply_right`

English:
theorem projectionL_apply_right
  given: (h : IsTopCompl p q) (x : q)
  proof: projectionL_apply_eq_zero_of_mem_right h x.2

中文:
定理 projectionL_apply_right
  条件: (h : 是TopCompl p q) (x : q)
  证明: projectionL_apply_eq_zero_of_mem_right h x.2

Depends on / 依赖: projectionL_apply_eq_zero_of_mem_right
-/
theorem projectionL_apply_right (h : IsTopCompl p q) (x : q) :
    p.projectionL q h x = 0 :=
  projectionL_apply_eq_zero_of_mem_right h x.2

/--
theorem `ker_projectionL` / 定理 `ker_projectionL`

English:
theorem ker_projectionL
  given: (h : IsTopCompl p q)
  proof: by
  simp

@[simp]

中文:
定理 ker_projectionL
  条件: (h : 是TopCompl p q)
  证明: by
  simp

@[simp]
-/
theorem ker_projectionL (h : IsTopCompl p q) :
    (p.projectionL q h).ker = q := by
  simp

@[simp]
/--
theorem `isIdempotentElem_projectionL` / 定理 `isIdempotentElem_projectionL`

English:
theorem isIdempotentElem_projectionL
  given: (h : IsTopCompl p q)
  proof: by
  simp [← isIdempotentElem_toLinearMap_iff]

中文:
定理 isIdempotentElem_projectionL
  条件: (h : 是TopCompl p q)
  证明: by
  simp [← isIdempotentElem_toLinearMap_iff]

Depends on / 依赖: isIdempotentElem_toLinearMap_iff
-/
theorem isIdempotentElem_projectionL (h : IsTopCompl p q) :
    IsIdempotentElem (p.projectionL q h) := by
  simp [← isIdempotentElem_toLinearMap_iff]

/--
theorem `projectionL_add_projectionL_eq_self` / 定理 `projectionL_add_projectionL_eq_self`

English:
theorem projectionL_add_projectionL_eq_self
  statement: [ContinuousSub M]
  proof: projection_add_projection_eq_self h.isCompl x

中文:
定理 projectionL_add_projectionL_eq_self
  结论: [余ntinuousSub M]
  证明: projection_add_projection_eq_self h.isCompl x

Depends on / 依赖: h.isCompl, isCompl, projection_add_projection_eq_self
-/
theorem projectionL_add_projectionL_eq_self [ContinuousSub M]
    (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x + q.projectionL p h.symm x = x :=
  projection_add_projection_eq_self h.isCompl x

/--
theorem `projectionL_add_projectionL_eq_id` / 定理 `projectionL_add_projectionL_eq_id`

English:
theorem projectionL_add_projectionL_eq_id
  given: [IsTopologicalAddGroup M] (h : IsTopCompl p q)
  proof: ContinuousLinearMap.ext projectionL_add_projectionL_eq_self h

中文:
定理 projectionL_add_projectionL_eq_id
  条件: [是拓扑加群 M] (h : 是TopCompl p q)
  证明: ContinuousLinearMap.ext projectionL_add_projectionL_eq_self h

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, projectionL_add_projectionL_eq_self
-/
theorem projectionL_add_projectionL_eq_id [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    p.projectionL q h + q.projectionL p h.symm = .id R M :=
ContinuousLinearMap.ext projectionL_add_projectionL_eq_self h

/--
lemma `projectionL_eq_self_sub_projectionL` / 引理 `projectionL_eq_self_sub_projectionL`

English:
lemma projectionL_eq_self_sub_projectionL
  given: [ContinuousSub M] (h : IsTopCompl p q) (x : M)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [projectionL_add_projectionL_eq_self]

中文:
引理 projectionL_eq_self_sub_projectionL
  条件: [余ntinuousSub M] (h : 是TopCompl p q) (x : M)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [projectionL_add_projectionL_eq_self]

Depends on / 依赖: eq_sub_iff_add_eq, projectionL_add_projectionL_eq_self
-/
lemma projectionL_eq_self_sub_projectionL [ContinuousSub M] (h : IsTopCompl p q) (x : M) :
    q.projectionL p h.symm x = x - p.projectionL q h x := by
  rw [eq_sub_iff_add_eq]; rw [projectionL_add_projectionL_eq_self]

/--
lemma `projectionL_eq_id_sub_projectionL` / 引理 `projectionL_eq_id_sub_projectionL`

English:
lemma projectionL_eq_id_sub_projectionL
  given: [IsTopologicalAddGroup M] (h : IsTopCompl p q)
  proof: ContinuousLinearMap.ext projectionL_eq_self_sub_projectionL h

中文:
引理 projectionL_eq_id_sub_projectionL
  条件: [是拓扑加群 M] (h : 是TopCompl p q)
  证明: ContinuousLinearMap.ext projectionL_eq_self_sub_projectionL h

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, projectionL_eq_self_sub_projectionL
-/
lemma projectionL_eq_id_sub_projectionL [IsTopologicalAddGroup M] (h : IsTopCompl p q) :
    q.projectionL p h.symm = .id R M - p.projectionL q h :=
ContinuousLinearMap.ext projectionL_eq_self_sub_projectionL h

/--
lemma `projectionL_eq_self_iff` / 引理 `projectionL_eq_self_iff`

English:
lemma projectionL_eq_self_iff
  given: (h : IsTopCompl p q) (x : M)
  proof: projection_eq_self_iff h.isCompl x

中文:
引理 projectionL_eq_self_iff
  条件: (h : 是TopCompl p q) (x : M)
  证明: projection_eq_self_iff h.isCompl x

Depends on / 依赖: h.isCompl, isCompl, projection_eq_self_iff
-/
lemma projectionL_eq_self_iff (h : IsTopCompl p q) (x : M) :
    p.projectionL q h x = x ↔ x in p :=
  projection_eq_self_iff h.isCompl x

/--
theorem `_root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL` / 定理 `_root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL`

English:
theorem _root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL
  proof: coe_inj.mp LinearMap.IsIdempotentElem.eq_projection hf.toLinearMap

中文:
定理 _root_.连续线性映射.IsIdempotentElem.eq_projectionL
  证明: coe_inj.mp LinearMap.IsIdempotentElem.eq_projection hf.toLinearMap

Depends on / 依赖: IsIdempotentElem, LinearMap, LinearMap.IsIdempotentElem.eq_projection, coe_inj, coe_inj.mp, eq_projection, hf.toLinearMap, toLinearMap
-/
theorem _root_.ContinuousLinearMap.IsIdempotentElem.eq_projectionL
    {f : M ->L[R] M} (hf : IsIdempotentElem f) : f = f.range.projectionL f.ker hf.isTopCompl :=
coe_inj.mp LinearMap.IsIdempotentElem.eq_projection hf.toLinearMap

/--
theorem `_root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker` / 定理 `_root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker`

English:
theorem _root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker
  proof: ⟨fun h => ⟨_, h.eq_projectionL⟩, fun ⟨hf, h⟩ => h.symm ▸ isIdempotentElem_projectionL hf⟩

中文:
定理 _root_.连续线性映射.isIdempotentElem_iff_eq_projectionL_range_ker
  证明: ⟨fun h => ⟨_, h.eq_projectionL⟩, fun ⟨hf, h⟩ => h.symm ▸ isIdempotentElem_projectionL hf⟩

Depends on / 依赖: eq_projectionL, h.eq_projectionL, h.symm, isIdempotentElem_projectionL
-/
theorem _root_.ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker
    {f : M ->L[R] M} : IsIdempotentElem f ↔
      exists h : IsTopCompl f.range f.ker, f = f.range.projectionL f.ker h :=
  ⟨fun h => ⟨_, h.eq_projectionL⟩, fun ⟨hf, h⟩ => h.symm ▸ isIdempotentElem_projectionL hf⟩

end projection

section closed_hausdorff

/--
theorem `IsTopCompl.closedComplemented` / 定理 `IsTopCompl.closedComplemented`

English:
theorem IsTopCompl.closedComplemented
  given: (h : IsTopCompl p q)
  statement: ClosedComplemented p
  proof: ⟨p.projectionOntoL q h, projectionOntoL_apply_left h⟩

中文:
定理 是TopCompl.closedComplemented
  条件: (h : 是TopCompl p q)
  结论: ClosedComplemented p
  证明: ⟨p.projectionOntoL q h, projectionOntoL_apply_left h⟩

Depends on / 依赖: p.projectionOntoL, projectionOntoL, projectionOntoL_apply_left
-/
theorem IsTopCompl.closedComplemented (h : IsTopCompl p q) : ClosedComplemented p :=
  ⟨p.projectionOntoL q h, projectionOntoL_apply_left h⟩

/--
theorem `IsTopCompl.isClosed'` / 定理 `IsTopCompl.isClosed'`

English:
theorem IsTopCompl.isClosed'
  given: [T1Space p] (h : IsTopCompl p q)
  statement: IsClosed (q : Set M)
  proof: by
  rw [← ker_projectionOntoL h]
  exact isClosed_ker _

中文:
定理 是TopCompl.isClosed'
  条件: [T1空间 p] (h : 是TopCompl p q)
  结论: 是闭集 (q : 集合 M)
  证明: by
  rw [← ker_projectionOntoL h]
  exact isClosed_ker _

Depends on / 依赖: isClosed_ker, ker_projectionOntoL
-/
theorem IsTopCompl.isClosed' [T1Space p] (h : IsTopCompl p q) : IsClosed (q : Set M) := by
  rw [← ker_projectionOntoL h]
  exact isClosed_ker _

/--
theorem `IsTopCompl.isClosed` / 定理 `IsTopCompl.isClosed`

English:
theorem IsTopCompl.isClosed
  given: [T1Space q] [ContinuousSub M] (h : IsTopCompl p q)
  proof: h.symm.isClosed'

中文:
定理 是TopCompl.isClosed
  条件: [T1空间 q] [余ntinuousSub M] (h : 是TopCompl p q)
  证明: h.symm.isClosed'
-/
protected theorem IsTopCompl.isClosed [T1Space q] [ContinuousSub M] (h : IsTopCompl p q) :
    IsClosed (p : Set M) :=
  h.symm.isClosed'

/--
theorem `IsTopCompl.t3Space` / 定理 `IsTopCompl.t3Space`

English:
theorem IsTopCompl.t3Space
  statement: [IsTopologicalAddGroup M] (h : IsTopCompl p q)
  proof: by
  have : IsClosed ({0} : Set p) := by
    rw [← (isQuotientMap_projectionOntoL h).isClosed_preimage]
    rwa [← ker_projectionOntoL h] at hq
  have : T1Space p := IsTopologicalAddGroup.t1Space _ this
  rw [RegularSpace.t3Space_iff_t0Space]
  infer_instance

中文:
定理 是TopCompl.t3Space
  结论: [是拓扑加群 M] (h : 是TopCompl p q)
  证明: by
  have : IsClosed ({0} : Set p) := by
    rw [← (isQuotientMap_projectionOntoL h).isClosed_preimage]
    rwa [← ker_projectionOntoL h] at hq
  have : T1Space p := IsTopologicalAddGroup.t1Space _ this
  rw [RegularSpace.t3Space_iff_t0Space]
  infer_instance
-/
protected theorem IsTopCompl.t3Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T3Space p := by
  have : IsClosed ({0} : Set p) := by
    rw [← (isQuotientMap_projectionOntoL h).isClosed_preimage]
    rwa [← ker_projectionOntoL h] at hq
  have : T1Space p := IsTopologicalAddGroup.t1Space _ this
  rw [RegularSpace.t3Space_iff_t0Space]
  infer_instance

/--
theorem `IsTopCompl.t2Space` / 定理 `IsTopCompl.t2Space`

English:
theorem IsTopCompl.t2Space
  statement: [IsTopologicalAddGroup M] (h : IsTopCompl p q)
  proof: have := h.t3Space hq
  inferInstance

中文:
定理 是TopCompl.t2Space
  结论: [是拓扑加群 M] (h : 是TopCompl p q)
  证明: have := h.t3Space hq
  inferInstance
-/
protected theorem IsTopCompl.t2Space [IsTopologicalAddGroup M] (h : IsTopCompl p q)
    (hq : IsClosed (q : Set M)) : T2Space p :=
  have := h.t3Space hq
  inferInstance

end closed_hausdorff

end IsTopCompl

section ClosedComplemented

/--
theorem `ClosedComplemented.exists_isTopCompl` / 定理 `ClosedComplemented.exists_isTopCompl`

English:
theorem ClosedComplemented.exists_isTopCompl
  given: (h : ClosedComplemented p)
  proof: Exists.elim h fun f hf => ⟨_, f.isTopCompl_of_proj hf⟩

中文:
定理 ClosedComplemented.存在_isTopCompl
  条件: (h : ClosedComplemented p)
  证明: Exists.elim h fun f hf => ⟨_, f.isTopCompl_of_proj hf⟩

Depends on / 依赖: Exists, Exists.elim, f.isTopCompl_of_proj, isTopCompl_of_proj
-/
theorem ClosedComplemented.exists_isTopCompl (h : ClosedComplemented p) :
    exists q : Submodule R M, IsTopCompl p q :=
  Exists.elim h fun f hf => ⟨_, f.isTopCompl_of_proj hf⟩

/--
theorem `closedComplemented_iff_exists_isTopCompl` / 定理 `closedComplemented_iff_exists_isTopCompl`

English:
theorem closedComplemented_iff_exists_isTopCompl
  proof: ⟨ClosedComplemented.exists_isTopCompl, fun H => H.elim fun _ hq => hq.closedComplemented⟩

中文:
定理 closedComplemented_iff_存在_isTopCompl
  证明: ⟨ClosedComplemented.exists_isTopCompl, fun H => H.elim fun _ hq => hq.closedComplemented⟩

Depends on / 依赖: ClosedComplemented, ClosedComplemented.exists_isTopCompl, H.elim, closedComplemented, exists_isTopCompl, hq.closedComplemented
-/
theorem closedComplemented_iff_exists_isTopCompl :
    ClosedComplemented p ↔ exists q, IsTopCompl p q :=
  ⟨ClosedComplemented.exists_isTopCompl, fun H => H.elim fun _ hq => hq.closedComplemented⟩

/--
theorem `ClosedComplemented.exists_isClosed_isCompl` / 定理 `ClosedComplemented.exists_isClosed_isCompl`

English:
theorem ClosedComplemented.exists_isClosed_isCompl
  given: [T1Space p] (h : ClosedComplemented p)
  proof: Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

中文:
定理 ClosedComplemented.存在_isClosed_isCompl
  条件: [T1空间 p] (h : ClosedComplemented p)
  证明: Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

Depends on / 依赖: Exists, Exists.elim, exists_isTopCompl, h.exists_isTopCompl, hq.isClosed, hq.isCompl, isClosed, isCompl
-/
theorem ClosedComplemented.exists_isClosed_isCompl [T1Space p] (h : ClosedComplemented p) :
    exists q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h.exists_isTopCompl fun q hq => ⟨q, hq.isClosed', hq.isCompl⟩

/--
Definition of `ClosedComplemented.complement` / `ClosedComplemented.complement` 的定义

English:
definition ClosedComplemented.complement
  signature: (h : ClosedComplemented p)
  body: Classical.choose h.exists_isTopCompl

中文:
定义 ClosedComplemented.complement
  签名: (h : ClosedComplemented p)
  定义体: Classical.choose h.exists_isTopCompl

Depends on / 依赖: Classical, Classical.choose, exists_isTopCompl, h.exists_isTopCompl
-/
noncomputable def ClosedComplemented.complement (h : ClosedComplemented p) : Submodule R M :=
  Classical.choose h.exists_isTopCompl

/--
theorem `ClosedComplemented.isTopCompl_complement` / 定理 `ClosedComplemented.isTopCompl_complement`

English:
theorem ClosedComplemented.isTopCompl_complement
  given: (h : ClosedComplemented p)
  proof: Classical.choose_spec h.exists_isTopCompl

中文:
定理 ClosedComplemented.isTopCompl_complement
  条件: (h : ClosedComplemented p)
  证明: Classical.choose_spec h.exists_isTopCompl

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_isTopCompl, h.exists_isTopCompl
-/
theorem ClosedComplemented.isTopCompl_complement (h : ClosedComplemented p) :
    IsTopCompl p h.complement :=
  Classical.choose_spec h.exists_isTopCompl

/--
theorem `ClosedComplemented.isCompl_complement` / 定理 `ClosedComplemented.isCompl_complement`

English:
theorem ClosedComplemented.isCompl_complement
  given: (h : ClosedComplemented p)
  statement: IsCompl p h.complement
  proof: h.isTopCompl_complement.isCompl

中文:
定理 ClosedComplemented.isCompl_complement
  条件: (h : ClosedComplemented p)
  结论: 是补集 p h.complement
  证明: h.isTopCompl_complement.isCompl

Depends on / 依赖: h.isTopCompl_complement.isCompl, isCompl, isTopCompl_complement
-/
theorem ClosedComplemented.isCompl_complement (h : ClosedComplemented p) : IsCompl p h.complement :=
  h.isTopCompl_complement.isCompl

/--
theorem `ClosedComplemented.isClosed_complement` / 定理 `ClosedComplemented.isClosed_complement`

English:
theorem ClosedComplemented.isClosed_complement
  given: [T1Space p] (h : ClosedComplemented p)
  proof: h.isTopCompl_complement.isClosed'

中文:
定理 ClosedComplemented.isClosed_complement
  条件: [T1空间 p] (h : ClosedComplemented p)
  证明: h.isTopCompl_complement.isClosed'

Depends on / 依赖: h.isTopCompl_complement.isClosed, isClosed, isTopCompl_complement
-/
theorem ClosedComplemented.isClosed_complement [T1Space p] (h : ClosedComplemented p) :
    IsClosed (h.complement : Set M) :=
  h.isTopCompl_complement.isClosed'

/--
theorem `ClosedComplemented.isClosed` / 定理 `ClosedComplemented.isClosed`

English:
theorem ClosedComplemented.isClosed
  statement: [ContinuousSub M] [T1Space M]
  proof: h.isTopCompl_complement.isClosed

@[simp]

中文:
定理 ClosedComplemented.isClosed
  结论: [余ntinuousSub M] [T1空间 M]
  证明: h.isTopCompl_complement.isClosed

@[simp]
-/
protected theorem ClosedComplemented.isClosed [ContinuousSub M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) :=
  h.isTopCompl_complement.isClosed

@[simp]
/--
theorem `closedComplemented_bot` / 定理 `closedComplemented_bot`

English:
theorem closedComplemented_bot
  statement: ClosedComplemented (⊥ : Submodule R M)
  proof: isTopCompl_bot_top.closedComplemented

@[simp]

中文:
定理 closedComplemented_bot
  结论: ClosedComplemented (⊥ : 子模 R M)
  证明: isTopCompl_bot_top.closedComplemented

@[simp]

Depends on / 依赖: closedComplemented, isTopCompl_bot_top, isTopCompl_bot_top.closedComplemented
-/
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  isTopCompl_bot_top.closedComplemented

@[simp]
/--
theorem `closedComplemented_top` / 定理 `closedComplemented_top`

English:
theorem closedComplemented_top
  statement: ClosedComplemented (⊤ : Submodule R M)
  proof: isTopCompl_top_bot.closedComplemented

中文:
定理 closedComplemented_top
  结论: ClosedComplemented (⊤ : 子模 R M)
  证明: isTopCompl_top_bot.closedComplemented

Depends on / 依赖: closedComplemented, isTopCompl_top_bot, isTopCompl_top_bot.closedComplemented
-/
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  isTopCompl_top_bot.closedComplemented

/--
theorem `_root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse` / 定理 `_root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse`

English:
theorem _root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse
  proof: .closedComplemented f₁.isTopCompl_range_ker_of_leftInverse f₂ h

中文:
定理 _root_.连续线性映射.closedComplemented_range_of_leftInverse
  证明: .closedComplemented f₁.isTopCompl_range_ker_of_leftInverse f₂ h

Depends on / 依赖: closedComplemented, isTopCompl_range_ker_of_leftInverse
-/
theorem _root_.ContinuousLinearMap.closedComplemented_range_of_leftInverse
    (f₁ : M ->L[R] N) (f₂ : N ->L[R] M) (h : Function.LeftInverse f₂ f₁) :
    f₁.range.ClosedComplemented :=
.closedComplemented f₁.isTopCompl_range_ker_of_leftInverse f₂ h

/--
theorem `_root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse` / 定理 `_root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse`

English:
theorem _root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse
  statement: [ContinuousSub M]
  proof: .symm.closedComplemented f₂.isTopCompl_range_ker_of_leftInverse f₁ h.leftInverse

中文:
定理 _root_.连续线性映射.closedComplemented_ker_of_rightInverse
  结论: [余ntinuousSub M]
  证明: .symm.closedComplemented f₂.isTopCompl_range_ker_of_leftInverse f₁ h.leftInverse

Depends on / 依赖: closedComplemented, h.leftInverse, isTopCompl_range_ker_of_leftInverse, leftInverse, symm.closedComplemented
-/
theorem _root_.ContinuousLinearMap.closedComplemented_ker_of_rightInverse [ContinuousSub M]
    (f₁ : M ->L[R] N) (f₂ : N ->L[R] M) (h : Function.RightInverse f₂ f₁) :
    f₁.ker.ClosedComplemented :=
.symm.closedComplemented f₂.isTopCompl_range_ker_of_leftInverse f₁ h.leftInverse

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ClosedComplemented.exists_submodule_equiv_prod` / 引理 `ClosedComplemented.exists_submodule_equiv_prod`

English:
lemma ClosedComplemented.exists_submodule_equiv_prod
  statement: [IsTopologicalAddGroup M]
  proof: let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ => by ext <;> simp [hf], fun _ => by ext <;> simp, fun _ => rfl⟩

中文:
引理 ClosedComplemented.存在_submodule_equiv_prod
  结论: [是拓扑加群 M]
  证明: let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ => by ext <;> simp [hf], fun _ => by ext <;> simp, fun _ => rfl⟩

Depends on / 依赖: equivOfRightInverse, f.ker, p.subtypeL, subtypeL
-/
lemma ClosedComplemented.exists_submodule_equiv_prod [IsTopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    exists (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (forall x : p, e x = (x, 0)) ∧ (forall y : q, e y = (0, y)) ∧ (forall x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ => by ext <;> simp [hf], fun _ => by ext <;> simp, fun _ => rfl⟩

end ClosedComplemented

section ContinuousLinearEquiv

variable [IsTopologicalAddGroup M]

/--
theorem `IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl` / 定理 `IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl`

English:
theorem IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: ⟨fun hTop => ((p.projectionOntoL q hTop).prod (q.projectionOntoL p hTop.symm)).continuous.congr
    fun x => (prodEquivOfIsCompl_symm_apply h x).symm,
fun hCont => ⟨h, continuous_subtype_val.comp continuous_fst.comp hCont⟩⟩

中文:
定理 是补集.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl
  条件: (h : 是补集 p q)
  证明: ⟨fun hTop => ((p.projectionOntoL q hTop).prod (q.projectionOntoL p hTop.symm)).continuous.congr
    fun x => (prodEquivOfIsCompl_symm_apply h x).symm,
fun hCont => ⟨h, continuous_subtype_val.comp continuous_fst.comp hCont⟩⟩

Depends on / 依赖: continuous, continuous.congr, continuous_fst, continuous_fst.comp, continuous_subtype_val, continuous_subtype_val.comp, hTop.symm, p.projectionOntoL, prodEquivOfIsCompl_symm_apply, projectionOntoL, q.projectionOntoL
-/
theorem IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.prodEquivOfIsCompl q h).symm :=
  ⟨fun hTop => ((p.projectionOntoL q hTop).prod (q.projectionOntoL p hTop.symm)).continuous.congr
    fun x => (prodEquivOfIsCompl_symm_apply h x).symm,
fun hCont => ⟨h, continuous_subtype_val.comp continuous_fst.comp hCont⟩⟩

/--
theorem `continuous_prodEquivOfIsCompl` / 定理 `continuous_prodEquivOfIsCompl`

English:
theorem continuous_prodEquivOfIsCompl
  given: (h : IsCompl p q)
  statement: Continuous (p.prodEquivOfIsCompl q h)
  proof: (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

中文:
定理 continuous_prodEquivOfIsCompl
  条件: (h : 是补集 p q)
  结论: 连续 (p.prodEquivOfIsCompl q h)
  证明: (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

Depends on / 依赖: continuous_fst, continuous_snd, continuous_subtype_val, continuous_subtype_val.comp
-/
theorem continuous_prodEquivOfIsCompl (h : IsCompl p q) : Continuous (p.prodEquivOfIsCompl q h) :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/--
theorem `IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl` / 定理 `IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl`

English:
theorem IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: by
  rw [(p.prodEquivOfIsCompl q h).isHomeomorph_iff]; rw [isTopCompl_iff_continuous_symm_prodEquivOfIsCompl]; rw [and_iff_right]
  exact continuous_prodEquivOfIsCompl h

中文:
定理 是补集.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl
  条件: (h : 是补集 p q)
  证明: by
  rw [(p.prodEquivOfIsCompl q h).isHomeomorph_iff]; rw [isTopCompl_iff_continuous_symm_prodEquivOfIsCompl]; rw [and_iff_right]
  exact continuous_prodEquivOfIsCompl h

Depends on / 依赖: and_iff_right, continuous_prodEquivOfIsCompl, isHomeomorph_iff, isTopCompl_iff_continuous_symm_prodEquivOfIsCompl, p.prodEquivOfIsCompl, prodEquivOfIsCompl
-/
theorem IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ IsHomeomorph (p.prodEquivOfIsCompl q h) := by
  rw [(p.prodEquivOfIsCompl q h).isHomeomorph_iff]; rw [isTopCompl_iff_continuous_symm_prodEquivOfIsCompl]; rw [and_iff_right]
  exact continuous_prodEquivOfIsCompl h

variable (p q) in
/--
Definition of `prodEquivOfIsTopCompl` / `prodEquivOfIsTopCompl` 的定义

English:
definition prodEquivOfIsTopCompl
  signature: (h : IsTopCompl p q)
  body: { p.prodEquivOfIsCompl q h.isCompl with
    continuous_toFun := continuous_prodEquivOfIsCompl h.isCompl
    continuous_invFun := h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp h }

@[simp]

中文:
定义 prodEquivOfIsTopCompl
  签名: (h : 是TopCompl p q)
  定义体: { p.prodEquivOfIsCompl q h.isCompl with
    continuous_toFun := continuous_prodEquivOfIsCompl h.isCompl
    continuous_invFun := h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp h }

@[simp]

Depends on / 依赖: continuous_invFun, continuous_prodEquivOfIsCompl, continuous_toFun, h.isCompl, h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp, isCompl, isTopCompl_iff_continuous_symm_prodEquivOfIsCompl, p.prodEquivOfIsCompl, prodEquivOfIsCompl
-/
noncomputable def prodEquivOfIsTopCompl (h : IsTopCompl p q) : (p × q) ≃L[R] M :=
  { p.prodEquivOfIsCompl q h.isCompl with
    continuous_toFun := continuous_prodEquivOfIsCompl h.isCompl
    continuous_invFun := h.isCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl.mp h }

@[simp]
/--
theorem `toLinearEquiv_prodEquivOfIsTopCompl` / 定理 `toLinearEquiv_prodEquivOfIsTopCompl`

English:
theorem toLinearEquiv_prodEquivOfIsTopCompl
  given: (h : IsTopCompl p q)
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_prodEquivOfIsTopCompl
  条件: (h : 是TopCompl p q)
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    (prodEquivOfIsTopCompl p q h : (p × q) ≃ₗ[R] M) = p.prodEquivOfIsCompl q h.isCompl :=
  rfl

@[simp]
/--
theorem `coe_prodEquivOfIsTopCompl` / 定理 `coe_prodEquivOfIsTopCompl`

English:
theorem coe_prodEquivOfIsTopCompl
  given: (h : IsTopCompl p q)
  proof: rfl

@[simp]

中文:
定理 coe_prodEquivOfIsTopCompl
  条件: (h : 是TopCompl p q)
  证明: rfl

@[simp]
-/
theorem coe_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    ⇑(prodEquivOfIsTopCompl p q h) = p.prodEquivOfIsCompl q h.isCompl :=
  rfl

@[simp]
/--
theorem `coe_symm_prodEquivOfIsTopCompl` / 定理 `coe_symm_prodEquivOfIsTopCompl`

English:
theorem coe_symm_prodEquivOfIsTopCompl
  given: (h : IsTopCompl p q)
  proof: rfl

中文:
定理 coe_symm_prodEquivOfIsTopCompl
  条件: (h : 是TopCompl p q)
  证明: rfl
-/
theorem coe_symm_prodEquivOfIsTopCompl (h : IsTopCompl p q) :
    ⇑(prodEquivOfIsTopCompl p q h).symm = (p.prodEquivOfIsCompl q h.isCompl).symm :=
  rfl

/--
theorem `prodEquivOfIsTopCompl_apply` / 定理 `prodEquivOfIsTopCompl_apply`

English:
theorem prodEquivOfIsTopCompl_apply
  given: (h : IsTopCompl p q) (x : p × q)
  proof: rfl

中文:
定理 prodEquivOfIsTopCompl_apply
  条件: (h : 是TopCompl p q) (x : p × q)
  证明: rfl
-/
theorem prodEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : p × q) :
    prodEquivOfIsTopCompl p q h x = (x.1 : M) + x.2 :=
  rfl

/--
theorem `prodEquivOfIsTopCompl_symm_apply` / 定理 `prodEquivOfIsTopCompl_symm_apply`

English:
theorem prodEquivOfIsTopCompl_symm_apply
  given: (h : IsTopCompl p q) (x : M)
  proof: prodEquivOfIsCompl_symm_apply h.isCompl x

中文:
定理 prodEquivOfIsTopCompl_symm_apply
  条件: (h : 是TopCompl p q) (x : M)
  证明: prodEquivOfIsCompl_symm_apply h.isCompl x

Depends on / 依赖: h.isCompl, isCompl, prodEquivOfIsCompl_symm_apply
-/
theorem prodEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (x : M) :
    (prodEquivOfIsTopCompl p q h).symm x =
      ((p.projectionOntoL q h x, q.projectionOntoL p h.symm x) : p × q) :=
  prodEquivOfIsCompl_symm_apply h.isCompl x

/--
theorem `IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl` / 定理 `IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl`

English:
theorem IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: by
  rw [p.isQuotientMap_mkQL.continuous_iff]; rw [isTopCompl_comm]
  exact h.symm.isTopCompl_iff_projectionOnto

中文:
定理 是补集.isTopCompl_iff_continuous_quotientEquivOfIsCompl
  条件: (h : 是补集 p q)
  证明: by
  rw [p.isQuotientMap_mkQL.continuous_iff]; rw [isTopCompl_comm]
  exact h.symm.isTopCompl_iff_projectionOnto

Depends on / 依赖: continuous_iff, h.symm.isTopCompl_iff_projectionOnto, isQuotientMap_mkQL, isTopCompl_comm, isTopCompl_iff_projectionOnto, p.isQuotientMap_mkQL.continuous_iff
-/
theorem IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl (h : IsCompl p q) :
    IsTopCompl p q ↔ Continuous (p.quotientEquivOfIsCompl q h) := by
  rw [p.isQuotientMap_mkQL.continuous_iff]; rw [isTopCompl_comm]
  exact h.symm.isTopCompl_iff_projectionOnto

variable (p q) in
/--
Definition of `quotientEquivOfIsTopCompl` / `quotientEquivOfIsTopCompl` 的定义

English:
definition quotientEquivOfIsTopCompl
  signature: (h : IsTopCompl p q)
  body: { p.quotientEquivOfIsCompl q h.isCompl with
    continuous_toFun := h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp h
    continuous_invFun := (p.mkQL.comp q.subtypeL).continuous }

@[simp]

中文:
定义 quotientEquivOfIsTopCompl
  签名: (h : 是TopCompl p q)
  定义体: { p.quotientEquivOfIsCompl q h.isCompl with
    continuous_toFun := h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp h
    continuous_invFun := (p.mkQL.comp q.subtypeL).continuous }

@[simp]

Depends on / 依赖: continuous, continuous_invFun, continuous_toFun, h.isCompl, h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp, isCompl, isTopCompl_iff_continuous_quotientEquivOfIsCompl, p.mkQL.comp, p.quotientEquivOfIsCompl, q.subtypeL, quotientEquivOfIsCompl, subtypeL
-/
noncomputable def quotientEquivOfIsTopCompl (h : IsTopCompl p q) : (M ⧸ p) ≃L[R] q :=
  { p.quotientEquivOfIsCompl q h.isCompl with
    continuous_toFun := h.isCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl.mp h
    continuous_invFun := (p.mkQL.comp q.subtypeL).continuous }

@[simp]
/--
theorem `toLinearEquiv_quotientEquivOfIsTopCompl` / 定理 `toLinearEquiv_quotientEquivOfIsTopCompl`

English:
theorem toLinearEquiv_quotientEquivOfIsTopCompl
  given: (h : IsTopCompl p q)
  proof: rfl

中文:
定理 toLinearEquiv_quotientEquivOfIsTopCompl
  条件: (h : 是TopCompl p q)
  证明: rfl
-/
theorem toLinearEquiv_quotientEquivOfIsTopCompl (h : IsTopCompl p q) :
    (quotientEquivOfIsTopCompl p q h : (M ⧸ p) ≃ₗ[R] q) = p.quotientEquivOfIsCompl q h.isCompl :=
  rfl

/--
theorem `quotientEquivOfIsTopCompl_comp_mkQL` / 定理 `quotientEquivOfIsTopCompl_comp_mkQL`

English:
theorem quotientEquivOfIsTopCompl_comp_mkQL
  given: (h : IsTopCompl p q)
  proof: rfl

@[simp]

中文:
定理 quotientEquivOfIsTopCompl_comp_mkQL
  条件: (h : 是TopCompl p q)
  证明: rfl

@[simp]
-/
theorem quotientEquivOfIsTopCompl_comp_mkQL (h : IsTopCompl p q) :
    (quotientEquivOfIsTopCompl p q h) ∘L p.mkQL = q.projectionOntoL p h.symm :=
  rfl

@[simp]
/--
theorem `quotientEquivOfIsTopCompl_apply` / 定理 `quotientEquivOfIsTopCompl_apply`

English:
theorem quotientEquivOfIsTopCompl_apply
  given: (h : IsTopCompl p q) (x : M ⧸ p)
  proof: rfl

@[simp]

中文:
定理 quotientEquivOfIsTopCompl_apply
  条件: (h : 是TopCompl p q) (x : M ⧸ p)
  证明: rfl

@[simp]
-/
theorem quotientEquivOfIsTopCompl_apply (h : IsTopCompl p q) (x : M ⧸ p) :
    quotientEquivOfIsTopCompl p q h x = p.quotientEquivOfIsCompl q h.isCompl x :=
  rfl

@[simp]
/--
theorem `quotientEquivOfIsTopCompl_symm_apply` / 定理 `quotientEquivOfIsTopCompl_symm_apply`

English:
theorem quotientEquivOfIsTopCompl_symm_apply
  given: (h : IsTopCompl p q) (y : q)
  proof: rfl

中文:
定理 quotientEquivOfIsTopCompl_symm_apply
  条件: (h : 是TopCompl p q) (y : q)
  证明: rfl
-/
theorem quotientEquivOfIsTopCompl_symm_apply (h : IsTopCompl p q) (y : q) :
    (quotientEquivOfIsTopCompl p q h).symm y = p.mkQ y :=
  rfl

/--
theorem `quotientEquivOfIsTopCompl_apply_mk` / 定理 `quotientEquivOfIsTopCompl_apply_mk`

English:
theorem quotientEquivOfIsTopCompl_apply_mk
  given: (h : IsTopCompl p q) (x : M)
  proof: quotientEquivOfIsCompl_apply_mk h.isCompl x

中文:
定理 quotientEquivOfIsTopCompl_apply_mk
  条件: (h : 是TopCompl p q) (x : M)
  证明: quotientEquivOfIsCompl_apply_mk h.isCompl x

Depends on / 依赖: h.isCompl, isCompl, quotientEquivOfIsCompl_apply_mk
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

/--
Definition of `ofIsTopCompl` / `ofIsTopCompl` 的定义

English:
definition ofIsTopCompl
  signature: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  body: φ.coprod ψ ∘L ↑(prodEquivOfIsTopCompl p q h).symm

中文:
定义 ofIsTopCompl
  签名: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  定义体: φ.coprod ψ ∘L ↑(prodEquivOfIsTopCompl p q h).symm

Depends on / 依赖: coprod, prodEquivOfIsTopCompl
-/
noncomputable def ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) : E ->L[R] F :=
  φ.coprod ψ ∘L ↑(prodEquivOfIsTopCompl p q h).symm

/--
theorem `ofIsTopCompl_eq_add` / 定理 `ofIsTopCompl_eq_add`

English:
theorem ofIsTopCompl_eq_add
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  proof: by
  ext; simp [ofIsTopCompl]

@[simp]

中文:
定理 ofIsTopCompl_eq_add
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  证明: by
  ext; simp [ofIsTopCompl]

@[simp]

Depends on / 依赖: ofIsTopCompl
-/
theorem ofIsTopCompl_eq_add (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) :
    ofIsTopCompl h φ ψ = φ ∘L p.projectionOntoL q h + ψ ∘L q.projectionOntoL p h.symm := by
  ext; simp [ofIsTopCompl]

@[simp]
/--
theorem `toLinearMap_ofIsTopCompl` / 定理 `toLinearMap_ofIsTopCompl`

English:
theorem toLinearMap_ofIsTopCompl
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_ofIsTopCompl
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  证明: rfl

@[simp]
-/
theorem toLinearMap_ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) :
    (ofIsTopCompl h φ ψ : E ->ₗ[R] F) = LinearMap.ofIsCompl h.isCompl φ ψ :=
  rfl

@[simp]
/--
theorem `ofIsTopCompl_apply` / 定理 `ofIsTopCompl_apply`

English:
theorem ofIsTopCompl_apply
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : E)
  proof: rfl

中文:
定理 ofIsTopCompl_apply
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : E)
  证明: rfl
-/
theorem ofIsTopCompl_apply (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : E) :
    ofIsTopCompl h φ ψ (x : E) = LinearMap.ofIsCompl h.isCompl φ ψ x :=
  rfl

/--
theorem `ofIsTopCompl_apply_left` / 定理 `ofIsTopCompl_apply_left`

English:
theorem ofIsTopCompl_apply_left
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : p)
  proof: by simp

中文:
定理 ofIsTopCompl_apply_left
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : p)
  证明: by simp
-/
theorem ofIsTopCompl_apply_left (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : p) :
    ofIsTopCompl h φ ψ (x : E) = φ x := by simp

/--
theorem `ofIsTopCompl_apply_right` / 定理 `ofIsTopCompl_apply_right`

English:
theorem ofIsTopCompl_apply_right
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : q)
  proof: by simp

中文:
定理 ofIsTopCompl_apply_right
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : q)
  证明: by simp
-/
theorem ofIsTopCompl_apply_right (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) (x : q) :
    ofIsTopCompl h φ ψ (x : E) = ψ x := by simp

/--
theorem `ofIsTopCompl_eq` / 定理 `ofIsTopCompl_eq`

English:
theorem ofIsTopCompl_eq
  statement: (h : IsTopCompl p q) {φ : p ->L[R] F} {ψ : q ->L[R] F} {χ : E ->L[R] F}
  proof: by
  ext; simp [LinearMap.ofIsCompl_eq h.isCompl hφ, hψ]

@[simp]

中文:
定理 ofIsTopCompl_eq
  结论: (h : 是TopCompl p q) {φ : p ->L[R] F} {ψ : q ->L[R] F} {χ : E ->L[R] F}
  证明: by
  ext; simp [LinearMap.ofIsCompl_eq h.isCompl hφ, hψ]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ofIsCompl_eq, h.isCompl, isCompl, ofIsCompl_eq
-/
theorem ofIsTopCompl_eq (h : IsTopCompl p q) {φ : p ->L[R] F} {ψ : q ->L[R] F} {χ : E ->L[R] F}
    (hφ : forall u : p, φ u = χ u) (hψ : forall u : q, ψ u = χ u) : ofIsTopCompl h φ ψ = χ := by
  ext; simp [LinearMap.ofIsCompl_eq h.isCompl hφ, hψ]

@[simp]
/--
theorem `ofIsTopCompl_zero` / 定理 `ofIsTopCompl_zero`

English:
theorem ofIsTopCompl_zero
  given: (h : IsTopCompl p q)
  statement: (ofIsTopCompl h 0 0 : E ->L[R] F) = 0
  proof: by
  ext; simp

@[simp]

中文:
定理 ofIsTopCompl_zero
  条件: (h : 是TopCompl p q)
  结论: (ofIsTopCompl h 0 0 : E ->L[R] F) = 0
  证明: by
  ext; simp

@[simp]
-/
theorem ofIsTopCompl_zero (h : IsTopCompl p q) : (ofIsTopCompl h 0 0 : E ->L[R] F) = 0 := by
  ext; simp

@[simp]
/--
theorem `ofIsTopCompl_add` / 定理 `ofIsTopCompl_add`

English:
theorem ofIsTopCompl_add
  given: (h : IsTopCompl p q) (φ₁ φ₂ : p ->L[R] F) (ψ₁ ψ₂ : q ->L[R] F)
  proof: by
  ext; simp

中文:
定理 ofIsTopCompl_add
  条件: (h : 是TopCompl p q) (φ₁ φ₂ : p ->L[R] F) (ψ₁ ψ₂ : q ->L[R] F)
  证明: by
  ext; simp
-/
theorem ofIsTopCompl_add (h : IsTopCompl p q) (φ₁ φ₂ : p ->L[R] F) (ψ₁ ψ₂ : q ->L[R] F) :
    ofIsTopCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsTopCompl h φ₁ ψ₁ + ofIsTopCompl h φ₂ ψ₂ := by
  ext; simp

/--
theorem `range_ofIsTopCompl` / 定理 `range_ofIsTopCompl`

English:
theorem range_ofIsTopCompl
  given: (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  proof: by simp

中文:
定理 range_ofIsTopCompl
  条件: (h : 是TopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F)
  证明: by simp
-/
theorem range_ofIsTopCompl (h : IsTopCompl p q) (φ : p ->L[R] F) (ψ : q ->L[R] F) :
    LinearMap.range (ofIsTopCompl h φ ψ : E ->ₗ[R] F) = φ.range ⊔ ψ.range := by simp

end ContinuousLinearMap
