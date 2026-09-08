/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of charts and local structomorphisms

We show that the model with corners, charts, extended charts and their inverses are `C^n`,
and that local structomorphisms are `C^n` with `C^n` inverses.

## Implementation notes

This file uses the name `writtenInExtend` (in analogy to `writtenInExtChart`) to refer to a
composition `ψ.extend J ∘ f ∘ φ.extend I` of `f : M → N` with charts `ψ` and `φ` extended by the
appropriate models with corners. This is not a definition, so technically deviating from the naming
convention.

`isLocalStructomorphOn` is another made-up name.
-/

assert_not_exists mfderiv

public section

open Set ChartedSpace IsManifold
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a `C^n` manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  -- declare a topological space `M'`.
  {M' : Type*} [TopologicalSpace M']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H} {x : M}

/-! ### Atlas members are `C^n` -/

section Atlas

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-
**ModelWithCorners.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜, E) n I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `ModelWithCorners.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
theorem ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜, E) n I := by
  intro x
  refine contMDiffAt_iff.mpr ⟨I.continuousAt, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy ↦ by simp [hy]) (by simp)
@[deprecated (since := "2026-06-16")] alias contMDiff_model := ModelWithCorners.contMDiff

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-
**ModelWithCorners.contMDiffOn_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelWithCorners.contMDiffOn_symm : ContMDiffOn 𝓘(𝕜, E) I n I.symm (range 
I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ModelWithCorners.contMDiffOn_symm : ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I) := by
  intro x hx
  apply contMDiffWithinAt_iff.mpr ⟨by fun_prop, ?_⟩
  simpa using contDiffWithinAt_id.congr (fun y hy ↦ by simp [hy]) (by simp [hx])
@[deprecated (since := "2026-06-16")]
alias contMDiffOn_model_symm := ModelWithCorners.contMDiffOn_symm

/-- An atlas member is `C^n` for any `n`. -/
/-
**contMDiffOn_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_of_mem_maximalAtlas (h : e in maximalAtlas I n M) : ContMDiffO
n I I n e e.source
参数：h : e in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_maximalAtlas`：lif
tPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e e.…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `contDiffWithinAtProp_id`：contDiffWithinAtProp_id (x : H) : ContDiffWithi
nAtProp I I n id univ x

--- 原说明 ---
An atlas member is `C^n` for any `n`.
-/
theorem contMDiffOn_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) :
    ContMDiffOn I I n e e.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_maximalAtlas
    contDiffWithinAtProp_id h

/-- The inverse of an atlas member is `C^n` for any `n`. -/
/-
**contMDiffOn_symm_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_symm_of_mem_maximalAtlas (h : e in maximalAtlas I n M) : ContM
DiffOn I I n e.symm e.target
参数：h : e in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_symm_of_mem_maximalAtlas
`：liftPropOn_symm_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : fora
ll y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `contDiffWithinAtProp_id`：contDiffWithinAtProp_id (x : H) : ContDiffWithi
nAtProp I I n id univ x

--- 原说明 ---
The inverse of an atlas member is `C^n` for any `n`.
-/
theorem contMDiffOn_symm_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) :
    ContMDiffOn I I n e.symm e.target :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_symm_of_mem_maximalAtlas
      contDiffWithinAtProp_id h
/-
**contMDiffAt_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_of_mem_maximalAtlas (h : e in maximalAtlas I n M) (hx : x in e
.source) : ContMDiffAt I I n e x
参数：h : e in maximalAtlas I n M；hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `contMDiffOn_of_mem_maximalAtlas`：contMDiffOn_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) : ContMDiffOn I I n e e.source
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem contMDiffAt_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffAt I I n e x :=
  (contMDiffOn_of_mem_maximalAtlas h).contMDiffAt <| e.open_source.mem_nhds hx
/-
**contMDiffAt_symm_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_symm_of_mem_maximalAtlas {x : H} (h : e in maximalAtlas I n M)
 (hx : x in e.target) : ContMDiffAt I I n e.symm x
参数：h : e in maximalAtlas I n M；hx : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `contMDiffOn_symm_of_mem_maximalAtlas`：contMDiffOn_symm_of_mem_maximalAtl
as (h : e in maximalAtlas I n M) : ContMDiffOn I I n e.symm e.target
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem contMDiffAt_symm_of_mem_maximalAtlas {x : H} (h : e ∈ maximalAtlas I n M)
    (hx : x ∈ e.target) : ContMDiffAt I I n e.symm x :=
  (contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt <| e.open_target.mem_nhds hx
/-
**contMDiffOn_chart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_chart [IsManifold I n M] : ContMDiffOn I I n (chartAt H x) (ch
artAt H x).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_of_mem_maximalAtlas`：contMDiffOn_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) : ContMDiffOn I I n e e.source
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffOn_chart [IsManifold I n M] :
    ContMDiffOn I I n (chartAt H x) (chartAt H x).source :=
  contMDiffOn_of_mem_maximalAtlas <| chart_mem_maximalAtlas x
/-
**contMDiffOn_chart_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_chart_symm [IsManifold I n M] : ContMDiffOn I I n (chartAt H x
).symm (chartAt H x).target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_symm_of_mem_maximalAtlas`：contMDiffOn_symm_of_mem_maximalAtl
as (h : e in maximalAtlas I n M) : ContMDiffOn I I n e.symm e.target
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffOn_chart_symm [IsManifold I n M] :
    ContMDiffOn I I n (chartAt H x).symm (chartAt H x).target :=
  contMDiffOn_symm_of_mem_maximalAtlas <| chart_mem_maximalAtlas x
/-
**OpenPartialHomeomorph.contMDiffAt_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contMDiffAt_extend {x : M} (he : e in maximalAtlas I
 n M) (hx : x in e.source) : ContMDiffAt I 𝓘(𝕜, E) n (e.extend I) x
参数：he : e in maximalAtlas I n M；hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ModelWithCorners.contMDiff`：ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜
, E) n I
· 使用定理 `contMDiffAt_of_mem_maximalAtlas`：contMDiffAt_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) (hx : x in e.source) : ContMDiffAt I I n e x
-/
theorem OpenPartialHomeomorph.contMDiffAt_extend {x : M}
    (he : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, E) n (e.extend I) x :=
  (I.contMDiff _).comp x <| contMDiffAt_of_mem_maximalAtlas he hx
/-
**OpenPartialHomeomorph.contMDiffOn_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contMDiffOn_extend (he : e in maximalAtlas I n M) : 
ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source
参数：he : e in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.contMDiffAt_extend`：OpenPartialHomeomorph.contMDif
fAt_extend {x : M} (he : e in maximalAtlas I n M) (hx : x in e.source) : ContMDi
ffAt I 𝓘(𝕜, E) n (e.extend I) …
-/
theorem OpenPartialHomeomorph.contMDiffOn_extend (he : e ∈ maximalAtlas I n M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' ↦ (e.contMDiffAt_extend he hx').contMDiffWithinAt
/-
**contMDiffAt_extChartAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_extChartAt' [IsManifold I n M] {x' : M} (h : x' in (chartAt H 
x).source) : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x'
参数：h : x' in (chartAt H x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.contMDiffAt_extend`：OpenPartialHomeomorph.contMDif
fAt_extend {x : M} (he : e in maximalAtlas I n M) (hx : x in e.source) : ContMDi
ffAt I 𝓘(𝕜, E) n (e.extend I) …
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffAt_extChartAt' [IsManifold I n M] {x' : M} (h : x' ∈ (chartAt H x).source) :
    ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' :=
  (chartAt H x).contMDiffAt_extend (chart_mem_maximalAtlas x) h
/-
**contMDiffAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff_source`：contMDiffAt_iff_source : ContMDiffAt I I' n f x 
↔ ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChart
At I x x)
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem`：ContMDiffWithinAt.congr_
of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] 
f) (hx : x in s) : ContMDiffWithinAt…
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x := by
  rw [contMDiffAt_iff_source]
  apply contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
  exact PartialEquiv.right_inv (extChartAt I x) hy
/-
**contMDiffOn_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_extChartAt [IsManifold I n M] : ContMDiffOn I 𝓘(𝕜, E) n (extCh
artAt I x) (chartAt H x).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.contMDiffOn_extend`：OpenPartialHomeomorph.contMDif
fOn_extend (he : e in maximalAtlas I n M) : ContMDiffOn I 𝓘(𝕜, E) n (e.extend I)
 e.source
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffOn_extChartAt [IsManifold I n M] :
    ContMDiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).source :=
  (chartAt H x).contMDiffOn_extend (chart_mem_maximalAtlas x)
/-
**contMDiffOn_extend_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_extend_symm (he : e in maximalAtlas I n M) : ContMDiffOn 𝓘(𝕜, 
E) I n (e.extend I).symm (I '' e.target)
参数：he : e in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `contMDiffOn_symm_of_mem_maximalAtlas`：contMDiffOn_symm_of_mem_maximalAtl
as (h : e in maximalAtlas I n M) : ContMDiffOn I I n e.symm e.target
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `ModelWithCorners.contMDiffOn_symm`：ModelWithCorners.contMDiffOn_symm : C
ontMDiffOn 𝓘(𝕜, E) I n I.symm (range I)
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem contMDiffOn_extend_symm (he : e ∈ maximalAtlas I n M) :
    ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) := by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (I.contMDiffOn_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl
/-
**contMDiffOn_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_extChartAt_symm [IsManifold I n M] (x : M) : ContMDiffOn 𝓘(𝕜, 
E) I n (extChartAt I x).symm (extChartAt I x).target
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_target`：extChartAt_target (x : M) : (extChartAt I x).target =
 I.symm ⁻¹' (chartAt H x).target inter range I
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `contMDiffOn_extend_symm`：contMDiffOn_extend_symm (he : e in maximalAtlas
 I n M) : ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target)
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffOn_extChartAt_symm [IsManifold I n M] (x : M) :
    ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target := by
  convert! contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
  · rw [extChartAt_target, I.image_eq]
  · infer_instance
/-
**contMDiffWithinAt_extChartAt_symm_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_extChartAt_symm_target [IsManifold I n M] (x : M) {y : E
} (hy : y in (extChartAt I x).target) : ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartA
t I x).symm (extChartAt I x).target y
参数：x : M；hy : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_extChartAt_symm`：contMDiffOn_extChartAt_symm [IsManifold I n
 M] (x : M) : ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).tar
get
-/
theorem contMDiffWithinAt_extChartAt_symm_target [IsManifold I n M]
    (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target y :=
  contMDiffOn_extChartAt_symm x y hy
/-
**contMDiffWithinAt_extChartAt_symm_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_extChartAt_symm_range [IsManifold I n M] (x : M) {y : E}
 (hy : y in (extChartAt I x).target) : ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt
 I x).symm (range I) y
参数：x : M；hy : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`：ContMDiffWithinAt.mono_of_mem_
nhdsWithin (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) : ContMDiff
WithinAt I I' n f t x
· 使用定理 `contMDiffWithinAt_extChartAt_symm_target`：contMDiffWithinAt_extChartAt_s
ymm_target [IsManifold I n M] (x : M) {y : E} (hy : y in (extChartAt I x).target
) : ContMDiffWithinAt 𝓘(𝕜, E) …
· 使用定理 `extChartAt_target_mem_nhdsWithin_of_mem`：extChartAt_target_mem_nhdsWithi
n_of_mem {x : M} {y : E} (hy : y in (extChartAt I x).target) : (extChartAt I x).
target in 𝓝[range I] y
-/
theorem contMDiffWithinAt_extChartAt_symm_range [IsManifold I n M]
    (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) y :=
  (contMDiffWithinAt_extChartAt_symm_target x hy).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin_of_mem hy)
/-
**contMDiffWithinAt_extChartAt_symm_target_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_extChartAt_symm_target_self (x : M) : ContMDiffWithinAt 
𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target (extChartAt I x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_target`：contMDiffWithinAt_iff_target : ContMDiffWi
thinAt I I' n f s x ↔ ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n 
(extChartAt I' (f …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ModelWithCorners.continuousAt_symm`：continuousAt_symm {x} : ContinuousAt
 I.symm x
· 使用定理 `ContMDiffWithinAt.congr_of_mem`：ContMDiffWithinAt.congr_of_mem (h : Cont
MDiffWithinAt I I' n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : x in s) : Con
tMDiffWithinAt I I' …
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem contMDiffWithinAt_extChartAt_symm_target_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target
      (extChartAt I x x) := by
  rw [contMDiffWithinAt_iff_target]
  constructor
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp _ I.continuousAt_symm
    exact (chartAt H x).symm.continuousAt (by simp)
  · apply contMDiffWithinAt_id.congr_of_mem (fun y hy ↦ ?_) (by simp)
    convert! PartialEquiv.right_inv (extChartAt I x) hy
    simp
/-
**contMDiffWithinAt_extChartAt_symm_range_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_extChartAt_symm_range_self (x : M) : ContMDiffWithinAt 𝓘
(𝕜, E) I n (extChartAt I x).symm (range I) (extChartAt I x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`：ContMDiffWithinAt.mono_of_mem_
nhdsWithin (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) : ContMDiff
WithinAt I I' n f t x
· 使用定理 `contMDiffWithinAt_extChartAt_symm_target_self`：contMDiffWithinAt_extChar
tAt_symm_target_self (x : M) : ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).sy
mm (extChartAt I x).target (extChar…
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
-/
theorem contMDiffWithinAt_extChartAt_symm_range_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) (extChartAt I x x) :=
  (contMDiffWithinAt_extChartAt_symm_target_self x).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin x)

/-- An element of `contDiffGroupoid n I` is `C^n`. -/
/-
**contMDiffOn_of_mem_contDiffGroupoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_of_mem_contDiffGroupoid {e' : OpenPartialHomeomorph H H} (h : 
e' in contDiffGroupoid n I) : ContMDiffOn I I n e' e'.source
参数：h : e' in contDiffGroupoid n I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_groupoid`：liftPro
pOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y)
 {f : OpenPartialHomeomorph H H} (hf : f in G) : Lift…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `contDiffWithinAtProp_id`：contDiffWithinAtProp_id (x : H) : ContDiffWithi
nAtProp I I n id univ x

--- 原说明 ---
An element of `contDiffGroupoid n I` is `C^n`.
-/
theorem contMDiffOn_of_mem_contDiffGroupoid {e' : OpenPartialHomeomorph H H}
    (h : e' ∈ contDiffGroupoid n I) : ContMDiffOn I I n e' e'.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_groupoid contDiffWithinAtProp_id h
/-
**OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn [IsManifold I n M] (
φ : OpenPartialHomeomorph M H) (hφ : ContMDiffOn I I n φ φ.source) (hφ' : ContMD
iffOn I I n φ.symm φ.target) : φ in maximalAtlas I n M
参数：φ : OpenPartialHomeomorph M H；hφ : ContMDiffOn I I n φ φ.source；hφ' : ContMDi
ffOn I I n φ.symm φ.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pregroupoid.mk.congr_simp`：∀ {H : Type u_2} [inst : TopologicalSpace H] 
(property property_1 : (H → H) → Set H → Prop)   (e_property : property = proper
ty_1)   (comp :…
· 使用定理 `contMDiffOn_of_mem_maximalAtlas`：contMDiffOn_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) : ContMDiffOn I I n e e.source
· 使用定理 `StructureGroupoid.subset_maximalAtlas`：StructureGroupoid.subset_maximalA
tlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `contMDiffOn_symm_of_mem_maximalAtlas`：contMDiffOn_symm_of_mem_maximalAtl
as (h : e in maximalAtlas I n M) : ContMDiffOn I I n e.symm e.target
· 使用定理 `ContMDiff.comp_contMDiffOn`：ContMDiff.comp_contMDiffOn {f : M -> M'} {g 
: M' -> M''} {s : Set M} (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f 
s) : ContMDiffOn…
· 使用定理 `ModelWithCorners.contMDiff`：ModelWithCorners.contMDiff : ContMDiff I 𝓘(𝕜
, E) n I
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `ModelWithCorners.contMDiffOn_symm`：ModelWithCorners.contMDiffOn_symm : C
ontMDiffOn 𝓘(𝕜, E) I n I.symm (range I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn [IsManifold I n M]
    (φ : OpenPartialHomeomorph M H) (hφ : ContMDiffOn I I n φ φ.source)
    (hφ' : ContMDiffOn I I n φ.symm φ.target) :
    φ ∈ maximalAtlas I n M := by
  simp only [mfld_simps, IsManifold.mem_maximalAtlas_iff, StructureGroupoid.maximalAtlas,
    contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    ← contMDiffOn_iff_contDiffOn]
  intro e he
  have he' := contMDiffOn_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.subset_maximalAtlas _ he)
  have he'' := contMDiffOn_symm_of_mem_maximalAtlas (I := I) (n := n)
    (StructureGroupoid.subset_maximalAtlas _ he)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  all_goals apply I.contMDiff.comp_contMDiffOn
  · apply he'.comp (hφ'.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · apply hφ.comp (he''.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · exact hφ.comp (he''.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
  · exact he'.comp (hφ'.comp (I.contMDiffOn_symm.mono (by simp)) (by grind)) (by grind)
/-
**IsManifold.mem_maximalAtlas_iff_contMDiffOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsManifold.mem_maximalAtlas_iff_contMDiffOn [IsManifold I n M] (φ : OpenPa
rtialHomeomorph M H) : φ in maximalAtlas I n M ↔ ContMDiffOn I I n φ φ.source ∧ 
ContMDiffOn I I n φ.symm φ.target
参数：φ : OpenPartialHomeomorph M H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_of_mem_maximalAtlas`：contMDiffOn_of_mem_maximalAtlas (h : e 
in maximalAtlas I n M) : ContMDiffOn I I n e e.source
· 使用定理 `contMDiffOn_symm_of_mem_maximalAtlas`：contMDiffOn_symm_of_mem_maximalAtl
as (h : e in maximalAtlas I n M) : ContMDiffOn I I n e.symm e.target
· 使用引理 `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn`：OpenPartialHomeom
orph.mem_maximalAtlas_of_contMDiffOn [IsManifold I n M] (φ : OpenPartialHomeomor
ph M H) (hφ : ContMDiffOn I I n φ φ.source)…
-/
lemma IsManifold.mem_maximalAtlas_iff_contMDiffOn [IsManifold I n M]
    (φ : OpenPartialHomeomorph M H) :
    φ ∈ maximalAtlas I n M ↔ ContMDiffOn I I n φ φ.source ∧ ContMDiffOn I I n φ.symm φ.target :=
  ⟨fun h ↦ ⟨contMDiffOn_of_mem_maximalAtlas h, contMDiffOn_symm_of_mem_maximalAtlas h⟩,
   fun ⟨hφ, hφ'⟩ ↦ φ.mem_maximalAtlas_of_contMDiffOn hφ hφ'⟩

end Atlas

/-! ### (local) structomorphisms are `C^n` -/

section IsLocalStructomorph

variable [IsManifold I n M] [ChartedSpace H M'] [IsM' : IsManifold I n M']

/-
**isLocalStructomorphOn_contDiffGroupoid_iff_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalStructomorphOn_contDiffGroupoid_iff_aux {f : OpenPartialHomeomorph 
M M'} (hf : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.so
urce) : ContMDiffOn I I n f f.source
参数：hf : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_of_locally_contMDiffOn`：contMDiffOn_of_locally_contMDiffOn (
h : forall x in s, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f (s inter u
)) : ContMDiffOn I I' n …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `contMDiffOn_chart_symm`：contMDiffOn_chart_symm [IsManifold I n M] : Cont
MDiffOn I I n (chartAt H x).symm (chartAt H x).target
· 使用定理 `contMDiffOn_of_mem_contDiffGroupoid`：contMDiffOn_of_mem_contDiffGroupoid
 {e' : OpenPartialHomeomorph H H} (h : e' in contDiffGroupoid n I) : ContMDiffOn
 I I n e' e'.source
· 使用定理 `contMDiffOn_chart`：contMDiffOn_chart [IsManifold I n M] : ContMDiffOn I 
I n (chartAt H x) (chartAt H x).source
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `ContMDiffOn.comp'`：ContMDiffOn.comp' {t : Set M'} {g : M' -> M''} (hg : 
ContMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g
 ∘ f) (…
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
-/
theorem isLocalStructomorphOn_contDiffGroupoid_iff_aux {f : OpenPartialHomeomorph M M'}
    (hf : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source) :
    ContMDiffOn I I n f f.source := by
  -- It suffices to show regularity near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDiffGroupoid`.
  obtain
    ⟨e, he, he' : EqOn (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source ∩ e.source), hex :
      c x ∈ e.source⟩ :=
    hxf (by simp only [hx, mfld_simps])
  -- We choose a convenient set `s` in `M`.
  let s : Set M := (f.trans c').source ∩ ((c.trans e).trans c'.symm).source
  refine ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, ?_, ?_⟩
  · simp only [s, mfld_simps]
    rw [← he'] <;> simp only [c, c', hx, hex, mfld_simps]
  -- We need to show `f` is `ContMDiffOn` the domain `s ∩ f.source`.  We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `ContMDiffOn` it.
  have H₁ : ContMDiffOn I I n (c'.symm ∘ e ∘ c) s := by
    have hc' : ContMDiffOn I I n c'.symm _ := contMDiffOn_chart_symm
    have he'' : ContMDiffOn I I n e _ := contMDiffOn_of_mem_contDiffGroupoid he
    have hc : ContMDiffOn I I n c _ := contMDiffOn_chart
    refine (hc'.comp' (he''.comp' hc)).mono ?_
    dsimp [s, c, c']
    mfld_set_tac
  have H₂ : EqOn f (c'.symm ∘ e ∘ c) s := by
    intro y hy
    simp only [s, mfld_simps] at hy
    have hy₁ : f y ∈ c'.source := by simp only [hy, mfld_simps]
    have hy₂ : y ∈ c.source := by simp only [hy, mfld_simps]
    have hy₃ : c y ∈ c.symm ⁻¹' f.source ∩ e.source := by simp only [hy, mfld_simps]
    calc
      f y = c'.symm (c' (f y)) := by rw [c'.left_inv hy₁]
      _ = c'.symm (c' (f (c.symm (c y)))) := by rw [c.left_inv hy₂]
      _ = c'.symm (e (c y)) := by rw [← he' hy₃]; rfl
  refine (H₁.congr H₂).mono ?_
  mfld_set_tac

/-- Let `M` and `M'` be manifolds with the same model-with-corners, `I`.  Then `f : M → M'`
is a local structomorphism for `I`, if and only if it is manifold-`C^n` on the domain of definition
in both directions. -/
/-
**isLocalStructomorphOn_contDiffGroupoid_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalStructomorphOn_contDiffGroupoid_iff (f : OpenPartialHomeomorph M M'
) : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source ↔ C
ontMDiffOn I I n f f.source ∧ ContMDiffOn I I n f.symm f.target
参数：f : OpenPartialHomeomorph M M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLocalStructomorphOn_contDiffGroupoid_iff_aux`：isLocalStructomorphOn_co
ntDiffGroupoid_iff_aux {f : OpenPartialHomeomorph M M'} (hf : LiftPropOn (contDi
ffGroupoid n I).IsLocalStructomorphW…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'`：∀ {H : Type u_1}
 [inst : TopologicalSpace H] {G : StructureGroupoid H} [ClosedUnderRestriction G
]   (f : OpenPartialHomeomorph H H) {s : Set…
· 使用定理 `instClosedUnderRestrictionContDiffGroupoid`：∀ {n : WithTop ℕ∞} {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `OpenPartialHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn`：symm_eqOn_o
f_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t) (hs : e.
source inter s = e'.source inter s) (Heq : EqOn e…
· 使用定理 `OpenPartialHomeomorph.isImage_source_target`：isImage_source_target : e.I
sImage e.source e.target
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StructureGroupoid.symm`：StructureGroupoid.symm (G : StructureGroupoid H)
 {e : OpenPartialHomeomorph H H} (he : e in G) : e.symm in G
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Let `M` and `M'` be manifolds with the same model-with-corners, `I`.  Then `f : 
M → M'`
is a local structomorphism for `I`, if and only if it is manifold-`C^n` on the d
omain of definition
in both directions.
-/
theorem isLocalStructomorphOn_contDiffGroupoid_iff (f : OpenPartialHomeomorph M M') :
    LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source ↔
      ContMDiffOn I I n f f.source ∧ ContMDiffOn I I n f.symm f.target := by
  constructor
  · intro h
    refine ⟨isLocalStructomorphOn_contDiffGroupoid_iff_aux h,
      isLocalStructomorphOn_contDiffGroupoid_iff_aux ?_⟩
    -- todo: we can generalize this part of the proof to a lemma
    intro X hX
    let x := f.symm X
    have hx : x ∈ f.source := f.symm.mapsTo hX
    let c := chartAt H x
    let c' := chartAt H X
    obtain ⟨-, hxf⟩ := h x hx
    refine ⟨(f.symm.continuousAt hX).continuousWithinAt, fun h2x => ?_⟩
    obtain ⟨e, he, h2e, hef, hex⟩ :
      ∃ e : OpenPartialHomeomorph H H,
        e ∈ contDiffGroupoid n I ∧
          e.source ⊆ (c.symm ≫ₕ f ≫ₕ c').source ∧
            EqOn (c' ∘ f ∘ c.symm) e e.source ∧ c x ∈ e.source := by
      have h1 : c' = chartAt H (f x) := by simp only [x, c', f.right_inv hX]
      have h2 : c' ∘ f ∘ c.symm = ⇑(c.symm ≫ₕ f ≫ₕ c') := rfl
      have hcx : c x ∈ c.symm ⁻¹' f.source := by simp only [c, hx, mfld_simps]
      rw [h2]
      rw [← h1, h2, OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff'] at hxf
      · exact hxf hcx
      · dsimp [x, c]; mfld_set_tac
      · apply Or.inl
        simp only [c, hx, h1, mfld_simps]
    have h2X : c' X = e (c (f.symm X)) := by
      rw [← hef hex]
      dsimp only [Function.comp_def]
      have hfX : f.symm X ∈ c.source := by simp only [c, x, mfld_simps]
      rw [c.left_inv hfX, f.right_inv hX]
    have h3e : EqOn (c ∘ f.symm ∘ c'.symm) e.symm (c'.symm ⁻¹' f.target ∩ e.target) := by
      have h1 : EqOn (c.symm ≫ₕ f ≫ₕ c').symm e.symm (e.target ∩ e.target) := by
        apply EqOn.symm
        refine e.isImage_source_target.symm_eqOn_of_inter_eq_of_eqOn ?_ ?_
        · rw [inter_self, inter_eq_right.mpr h2e]
        · rw [inter_self]; exact hef.symm
      have h2 : e.target ⊆ (c.symm ≫ₕ f ≫ₕ c').target := by
        intro x hx; rw [← e.right_inv hx, ← hef (e.symm.mapsTo hx)]
        exact OpenPartialHomeomorph.mapsTo _ (h2e <| e.symm.mapsTo hx)
      rw [inter_self] at h1
      rwa [inter_eq_right.mpr]
      refine h2.trans ?_
      mfld_set_tac
    refine ⟨e.symm, StructureGroupoid.symm _ he, h3e, ?_⟩
    rw [h2X]; exact e.mapsTo hex
  · -- We now show the converse: an open partial homeomorphism `f : M → M'` which is `C^n` in both
    -- directions is a local structomorphism.  We do this by proposing
    -- `((chart_at H x).symm.trans f).trans (chart_at H (f x))` as a candidate for a structomorphism
    -- of `H`.
    rintro ⟨h₁, h₂⟩ x hx
    refine ⟨(h₁ x hx).continuousWithinAt, ?_⟩
    let c := chartAt H x
    let c' := chartAt H (f x)
    rintro (hx' : c x ∈ c.symm ⁻¹' f.source)
    -- propose `(c.symm.trans f).trans c'` as a candidate for a local structomorphism of `H`
    refine ⟨(c.symm.trans f).trans c', ⟨?_, ?_⟩, (?_ : EqOn (c' ∘ f ∘ c.symm) _ _), ?_⟩
    · -- regularity of the candidate local structomorphism in the forward direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I n f (f ≫ₕ c').source ((extChartAt I x).symm y) := by
        refine (h₁ ((extChartAt I x).symm y) ?_).mono ?_
        · simp only [c, hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I x).symm y ∈ c.source := by simp only [c, hy, mfld_simps]
      have hy'' : f ((extChartAt I x).symm y) ∈ c'.source := by
        simp only [c, hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert! H.2.mono _
      · simp only [c, hy, mfld_simps]
      · dsimp [c, c']; mfld_set_tac
    · -- regularity of the candidate local structomorphism in the reverse direction
      intro y hy
      simp only [mfld_simps] at hy
      have H : ContMDiffWithinAt I I n f.symm (f.symm ≫ₕ c).source
          ((extChartAt I (f x)).symm y) := by
        refine (h₂ ((extChartAt I (f x)).symm y) ?_).mono ?_
        · simp only [c', hy, mfld_simps]
        · mfld_set_tac
      have hy' : (extChartAt I (f x)).symm y ∈ c'.source := by simp only [c', hy, mfld_simps]
      have hy'' : f.symm ((extChartAt I (f x)).symm y) ∈ c.source := by
        simp only [c', hy, mfld_simps]
      rw [contMDiffWithinAt_iff_of_mem_source hy' hy''] at H
      convert! H.2.mono _
      · simp only [c', hy, mfld_simps]
      · dsimp [c, c']; mfld_set_tac
    -- now check the candidate local structomorphism agrees with `f` where it is supposed to
    · simp only [mfld_simps]; apply eqOn_refl
    · simp only [c, c', hx', mfld_simps]

end IsLocalStructomorph

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {s : Set M}
  {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}

/-- This is a smooth analogue of `OpenPartialHomeomorph.continuousWithinAt_writtenInExtend_iff`. -/
/-
**OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff {y : M} (hφ : 
φ in maximalAtlas I n M) (hψ : ψ in maximalAtlas J n N) (hy : y in φ.source) (hg
y : f y in ψ.source) (hmaps : MapsTo f s ψ.source) : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘
(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm) ((φ.extend I).symm ⁻¹' s inter ran
ge I) (φ.extend I y) ↔ ContMDiffWithinAt I J n f s y
参数：hφ : φ in maximalAtlas I n M；hψ : ψ in maximalAtlas J n N；hy : y in φ.source；
hgy : f y in ψ.source；hmaps : MapsTo f s ψ.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas`：contMDiffWithinAt_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (
hx : x in e.source) (hy : f x i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_writtenInExtend_iff`：continuous
WithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'} {y
 : M} (hy : y in f.source) (hgy : g y in f'.source…
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `contMDiffWithinAt_iff_contDiffWithinAt`：contMDiffWithinAt_iff_contDiffWi
thinAt {f : E -> E'} {s : Set E} {x : E} : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n 
f s x ↔ ContDiffWithinAt 𝕜 n…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
This is a smooth analogue of `OpenPartialHomeomorph.continuousWithinAt_writtenIn
Extend_iff`.
-/
theorem OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff {y : M}
    (hφ : φ ∈ maximalAtlas I n M) (hψ : ψ ∈ maximalAtlas J n N)
    (hy : y ∈ φ.source) (hgy : f y ∈ ψ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm)
      ((φ.extend I).symm ⁻¹' s ∩ range I) (φ.extend I y) ↔ ContMDiffWithinAt I J n f s y := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hφ hψ hy hgy]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [← φ.continuousWithinAt_writtenInExtend_iff (I := I) (I' := J) hy hgy hmaps]
    exact h.continuousWithinAt
  · rwa [← contMDiffWithinAt_iff_contDiffWithinAt]
  · rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact h.2
/-
**OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff (hφ : φ in maximalAt
las I n M) (hψ : ψ in maximalAtlas J n N) (hs : s subseteq φ.source) (hmaps : Ma
psTo f s ψ.source) : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I
).symm) (φ.extend I '' s) ↔ ContMDiffOn I J n f s
参数：hφ : φ in maximalAtlas I n M；hψ : ψ in maximalAtlas J n N；hs : s subseteq φ.s
ource；hmaps : MapsTo f s ψ.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `contMDiffWithinAt_congr_set`：contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image_of_subset`：map_exte
nd_nhdsWithin_eq_image_of_subset {y : M} (hy : y in f.source) (hs : s subseteq f
.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I …
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff`：OpenPartial
Homeomorph.contMDiffWithinAt_writtenInExtend_iff {y : M} (hφ : φ in maximalAtlas
 I n M) (hψ : ψ in maximalAtlas J n N) (hy : y in…
-/
theorem OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
    (hφ : φ ∈ maximalAtlas I n M) (hψ : ψ ∈ maximalAtlas J n N)
    (hs : s ⊆ φ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm) (φ.extend I '' s) ↔
      ContMDiffOn I J n f s := by
  refine forall_mem_image.trans <| forall₂_congr fun x hx ↦ ?_
  refine (contMDiffWithinAt_congr_set ?_).trans
    (contMDiffWithinAt_writtenInExtend_iff hφ hψ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← φ.map_extend_nhdsWithin_eq_image_of_subset,
    ← φ.map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]
