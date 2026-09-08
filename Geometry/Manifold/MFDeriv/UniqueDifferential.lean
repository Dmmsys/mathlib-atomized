/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Unique derivative sets in manifolds

In this file, we prove various properties of unique derivative sets in manifolds.
* `image_denseRange`: suppose `f` is differentiable on `s` and its derivative at every point of `s`
  has dense range. If `s` has the unique differential property, then so does `f '' s`.
* `uniqueMDiffOn_preimage`: the unique differential property is preserved by local diffeomorphisms
* `uniqueDiffOn_target_inter`: the unique differential property is preserved by
  pullbacks of extended charts
* `tangentBundle_proj_preimage`: if `s` has the unique differential property,
  its preimage under the tangent bundle projection also has
-/

public section

noncomputable section

open scoped Manifold
open Set

/-! ### Unique derivative sets in manifolds -/

section UniqueMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H' M'']
  {s : Set M} {x : M}

section

/-- If `s` has the unique differential property at `x`, `f` is differentiable within `s` at `x` and
its derivative has dense range, then `f '' s` has the unique differential property at `f x`. -/
/-
**UniqueMDiffWithinAt.image_denseRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffAt[s] x) {f : M -> M
'} {f' : E ->L[𝕜] E'} (hf : HasMFDerivAt[s] f x f') (hd : DenseRange f') : Uniqu
eMDiffAt[f '' s] (f x)
参数：hs : UniqueMDiffAt[s] x；hf : HasMFDerivAt[s] f x f'；hd : DenseRange f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.inter'`：UniqueMDiffWithinAt.inter' (hs : UniqueMDiff
At[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[s inter t] x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `UniqueDiffWithinAt.congr_pt`：UniqueDiffWithinAt.congr_pt (h : UniqueDiff
WithinAt 𝕜 s x) (hy : x = y) : UniqueDiffWithinAt 𝕜 s y
· 使用定理 `UniqueDiffWithinAt.mono`：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt
 𝕜 s x) (st : s subseteq t) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `HasFDerivWithinAt.uniqueDiffWithinAt`：HasFDerivWithinAt.uniqueDiffWithin
At (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseR
ange f') : UniqueDiffWithi…
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` has the unique differential property at `x`, `f` is differentiable within
 `s` at `x` and
its derivative has dense range, then `f '' s` has the unique differential proper
ty at `f x`.
-/
theorem UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffAt[s] x)
    {f : M → M'} {f' : E →L[𝕜] E'} (hf : HasMFDerivAt[s] f x f')
    (hd : DenseRange f') : UniqueMDiffAt[f '' s] (f x) := by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
  have := hs.inter' <| hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

/-- If `s` has the unique differential property, `f` is differentiable on `s` and its derivative
at every point of `s` has dense range, then `f '' s` has the unique differential property.
This version uses the `HasMFDerivWithinAt` predicate. -/
/-
**UniqueMDiffOn.image_denseRange'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.image_denseRange' (hs : UniqueMDiff[s]) {f : M -> M'} {f' : 
M -> E ->L[𝕜] E'} (hf : forall x in s, HasMFDerivAt[s] f x (f' x)) (hd : forall 
x in s, DenseRange (f' x)) : UniqueMDiff[f '' s]
参数：hs : UniqueMDiff[s]；hf : forall x in s, HasMFDerivAt[s] f x (f' x)；hd : foral
l x in s, DenseRange (f' x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `UniqueMDiffWithinAt.image_denseRange`：UniqueMDiffWithinAt.image_denseRan
ge (hs : UniqueMDiffAt[s] x) {f : M -> M'} {f' : E ->L[𝕜] E'} (hf : HasMFDerivAt
[s] f x f') (hd : DenseRan…

--- 原说明 ---
If `s` has the unique differential property, `f` is differentiable on `s` and it
s derivative
at every point of `s` has dense range, then `f '' s` has the unique differential
 property.
This version uses the `HasMFDerivWithinAt` predicate.
-/
theorem UniqueMDiffOn.image_denseRange' (hs : UniqueMDiff[s]) {f : M → M'}
    {f' : M → E →L[𝕜] E'} (hf : ∀ x ∈ s, HasMFDerivAt[s] f x (f' x))
    (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueMDiff[f '' s] :=
  forall_mem_image.2 fun x hx ↦ (hs x hx).image_denseRange (hf x hx) (hd x hx)

/-- If `s` has the unique differential property, `f` is differentiable on `s` and its derivative
at every point of `s` has dense range, then `f '' s` has the unique differential property. -/
/-
**UniqueMDiffOn.image_denseRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.image_denseRange (hs : UniqueMDiff[s]) {f : M -> M'} (hf : M
Diff[s] f) (hd : forall x in s, DenseRange (mfderiv[s] f x)) : UniqueMDiff[f '' 
s]
参数：hs : UniqueMDiff[s]；hf : MDiff[s] f；hd : forall x in s, DenseRange (mfderiv[s
] f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffOn.image_denseRange'`：UniqueMDiffOn.image_denseRange' (hs : U
niqueMDiff[s]) {f : M -> M'} {f' : M -> E ->L[𝕜] E'} (hf : forall x in s, HasMFD
erivAt[s] f x (f' x))…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)

--- 原说明 ---
If `s` has the unique differential property, `f` is differentiable on `s` and it
s derivative
at every point of `s` has dense range, then `f '' s` has the unique differential
 property.
-/
theorem UniqueMDiffOn.image_denseRange (hs : UniqueMDiff[s]) {f : M → M'}
    (hf : MDiff[s] f) (hd : ∀ x ∈ s, DenseRange (mfderiv[s] f x)) :
    UniqueMDiff[f '' s] :=
  hs.image_denseRange' (fun x hx ↦ (hf x hx).hasMFDerivWithinAt) hd
/-
**UniqueMDiffWithinAt.preimage_openPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `
UniqueMDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {s : Set M} {x : M},   UniqueMDiffAt[s]
 x →     ∀ {e : OpenPartialHomeomorph M M'},       OpenPartialHomeomorph.MDiffer
entiable I I' e → x ∈ e.source → UniqueMDiffAt[e.target ∩ ↑e.symm ⁻¹' s] (↑e x)
参数：↑e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `UniqueMDiffWithinAt.image_denseRange`：UniqueMDiffWithinAt.image_denseRan
ge (hs : UniqueMDiffAt[s] x) {f : M -> M'} {f' : E ->L[𝕜] E'} (hf : HasMFDerivAt
[s] f x f') (hd : DenseRan…
· 使用定理 `UniqueMDiffWithinAt.inter`：UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt
[s] x) (ht : t in 𝓝 x) : UniqueMDiffAt[s inter t] x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mdifferentiableAt`：∀ {𝕜 : Type u_1
} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective`：mfderiv_surjec
tive {x : M} (hx : x in e.source) : Function.Surjective (mfderiv% e x)
-/
protected theorem UniqueMDiffWithinAt.preimage_openPartialHomeomorph
    (hs : UniqueMDiffAt[s] x) {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
    (hx : x ∈ e.source) : UniqueMDiffAt[e.target ∩ e.symm ⁻¹' s] (e x) := by
  rw [← e.image_source_inter_eq', inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
/-
**UniqueMDiffOn.uniqueMDiffOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiff[s]) {e : OpenPartia
lHomeomorph M M'} (he : e.MDifferentiable I I') : UniqueMDiff[e.target inter e.s
ymm ⁻¹' s]
参数：hs : UniqueMDiff[s]；he : e.MDifferentiable I I'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.preimage_openPartialHomeomorph`：∀ {𝕜 : Type u_1} [in
st : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x

--- 原说明 ---
If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property.
-/
theorem UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiff[s])
    {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I') :
    UniqueMDiff[e.target ∩ e.symm ⁻¹' s] := fun _x hx ↦
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_openPartialHomeomorph he (e.map_target hx.1)

variable [IsManifold I 1 M] in
/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
/-
**UniqueMDiffOn.uniqueMDiffOn_target_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.uniqueMDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) : U
niqueMDiff[(extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s]
参数：hs : UniqueMDiff[s]；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `UniqueMDiffOn.image_denseRange'`：UniqueMDiffOn.image_denseRange' (hs : U
niqueMDiff[s]) {f : M -> M'} {f' : M -> E ->L[𝕜] E'} (hf : forall x in s, HasMFD
erivAt[s] f x (f' x))…
· 使用定理 `UniqueMDiffOn.inter`：UniqueMDiffOn.inter (hs : UniqueMDiff[s]) (ht : IsO
pen t) : UniqueMDiff[s inter t]
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `hasMFDerivWithinAt_extChartAt`：hasMFDerivWithinAt_extChartAt (h : y in (
chartAt H x).source) : HasMFDerivAt[s] (extChartAt I x) y (mfderiv% (chartAt H x
) y :)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective`：mfderiv_surjec
tive {x : M} (hx : x in e.source) : Function.Surjective (mfderiv% e x)
· 使用定理 `mdifferentiable_chart`：mdifferentiable_chart (x : M) : (chartAt H x).MDi
fferentiable I I

--- 原说明 ---
If a set in a manifold has the unique derivative property, then its pullback by 
any extended
chart, in the vector space, also has the unique derivative property.
-/
theorem UniqueMDiffOn.uniqueMDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) :
    UniqueMDiff[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] := by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  rw [← PartialEquiv.image_source_inter_eq', inter_comm, extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy ↦ hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy ↦ ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange

variable [IsManifold I 1 M] in
/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
/-
**UniqueMDiffOn.uniqueDiffOn_target_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) : Un
iqueDiffOn 𝕜 ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s)
参数：hs : UniqueMDiff[s]；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffOn.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {s : Set E},…
· 使用定理 `UniqueMDiffOn.uniqueMDiffOn_target_inter`：UniqueMDiffOn.uniqueMDiffOn_ta
rget_inter (hs : UniqueMDiff[s]) (x : M) : UniqueMDiff[(extChartAt I x).target i
nter (extChartAt I x).symm ⁻¹'…

--- 原说明 ---
If a set in a manifold has the unique derivative property, then its pullback by 
any extended
chart, in the vector space, also has the unique derivative property.
-/
theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
  (hs.uniqueMDiffOn_target_inter x).uniqueDiffOn

variable [IsManifold I 1 M] in
/-
**UniqueMDiffOn.uniqueDiffWithinAt_range_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.uniqueDiffWithinAt_range_inter (hs : UniqueMDiff[s]) (x : M)
 (y : E) (hy : y in (extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s) :
 UniqueDiffWithinAt 𝕜 (range I inter (extChartAt I x).symm ⁻¹' s) y
参数：hs : UniqueMDiff[s]；x : M；y : E；hy : y in (extChartAt I x).target inter (extC
hartAt I x).symm ⁻¹' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono`：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt
 𝕜 s x) (st : s subseteq t) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `UniqueMDiffOn.uniqueDiffOn_target_inter`：UniqueMDiffOn.uniqueDiffOn_targ
et_inter (hs : UniqueMDiff[s]) (x : M) : UniqueDiffOn 𝕜 ((extChartAt I x).target
 inter (extChartAt I x).symm …
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
-/
theorem UniqueMDiffOn.uniqueDiffWithinAt_range_inter (hs : UniqueMDiff[s]) (x : M) (y : E)
    (hy : y ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :
    UniqueDiffWithinAt 𝕜 (range I ∩ (extChartAt I x).symm ⁻¹' s) y := by
  apply (hs.uniqueDiffOn_target_inter x y hy).mono
  apply inter_subset_inter_left _ (extChartAt_target_subset_range x)

variable [IsManifold I 1 M] in
/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
/-
**UniqueMDiffOn.uniqueDiffOn_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiff[s]) (x : M) (y
 : M'') {f : M -> M''} (hf : ContinuousOn f s) : UniqueDiffOn 𝕜 ((extChartAt I x
).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source
))
参数：hs : UniqueMDiff[s]；x : M；y : M''；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffOn.uniqueDiffOn_target_inter`：UniqueMDiffOn.uniqueDiffOn_targ
et_inter (hs : UniqueMDiff[s]) (x : M) : UniqueDiffOn 𝕜 ((extChartAt I x).target
 inter (extChartAt I x).symm …
· 使用定理 `UniqueMDiffWithinAt.inter'`：UniqueMDiffWithinAt.inter' (hs : UniqueMDiff
At[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[s inter t] x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_extChartAt_source`：isOpen_extChartAt_source (x : M) : IsOpen (ext
ChartAt I x).source
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
When considering functions between manifolds, this statement shows up often. It 
entails
the unique differential of the pullback in extended charts of the set where the 
function can
be read in the charts.
-/
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiff[s]) (x : M) (y : M'')
    {f : M → M''} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiff[s ∩ f ⁻¹' (extChartAt I' y).source] := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

end

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Z : M → Type*}
  [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)] [FiberBundle F Z]

/-
**UniqueMDiffWithinAt.bundle_preimage_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma UniqueMDiffWithinAt.bundle_preimage_aux {p : TotalSpace F Z}
    (hs : UniqueMDiffAt[s] p.proj) (h's : s ⊆ (trivializationAt F Z p.proj).baseSet) :
    UniqueMDiffAt[π F Z ⁻¹' s] p := by
  suffices ((extChartAt I p.proj).symm ⁻¹' s ∩ range I) ×ˢ univ ⊆
      (extChartAt (I.prod 𝓘(𝕜, F)) p).symm ⁻¹' (TotalSpace.proj ⁻¹' s) ∩ range (I.prod 𝓘(𝕜, F)) by
    let w := (extChartAt (I.prod 𝓘(𝕜, F)) p p).2
    have A : extChartAt (I.prod 𝓘(𝕜, F)) p p = (extChartAt I p.1 p.1, w) := by
      ext
      · simp [FiberBundle.chartedSpace_chartAt]
      · rfl
    simp only [UniqueMDiffWithinAt, A] at hs ⊢
    exact (hs.prod (uniqueDiffWithinAt_univ (x := w))).mono this
  rcases p with ⟨x, v⟩
  dsimp
  rintro ⟨z, w⟩ ⟨hz, -⟩
  simp only [mem_inter_iff, mem_preimage, Function.comp_apply,
    mem_range] at hz
  simp only [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.coe_trans_symm, mem_inter_iff,
    mem_preimage, Function.comp_apply, mem_range]
  constructor
  · rw [PartialEquiv.prod_symm, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.refl_coe,
      OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    convert! hz.1
    apply Trivialization.proj_symm_apply'
    exact h's hz.1
  · rcases hz.2 with ⟨u, rfl⟩
    exact ⟨(u, w), rfl⟩

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. -/
/-
**UniqueMDiffWithinAt.bundle_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.bundle_preimage {p : TotalSpace F Z} (hs : UniqueMDiff
At[s] p.proj) : UniqueMDiffAt[π F Z ⁻¹' s] p
参数：hs : UniqueMDiffAt[s] p.proj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential.0.UniqueMD
iffWithinAt.bundle_preimage_aux`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `UniqueMDiffWithinAt.inter`：UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt
[s] x) (ht : t in 𝓝 x) : UniqueMDiffAt[s inter t] x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `UniqueMDiffWithinAt.mono`：UniqueMDiffWithinAt.mono (h : UniqueMDiffAt[s]
 x) (st : s subseteq t) : UniqueMDiffAt[t] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
In a fiber bundle, the preimage under the projection of a set with unique differ
entials
in the base has unique differentials in the bundle.
-/
theorem UniqueMDiffWithinAt.bundle_preimage {p : TotalSpace F Z} (hs : UniqueMDiffAt[s] p.proj) :
    UniqueMDiffAt[π F Z ⁻¹' s] p := by
  suffices UniqueMDiffAt[π F Z ⁻¹' (s ∩ (trivializationAt F Z p.proj).baseSet)] p from
    this.mono (by simp)
  apply UniqueMDiffWithinAt.bundle_preimage_aux (hs.inter _) inter_subset_right
  exact (trivializationAt F Z p.proj).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p.proj)

variable (Z)

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. Version with a point `⟨b, x⟩`. -/
/-
**UniqueMDiffWithinAt.bundle_preimage'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.bundle_preimage' {b : M} (hs : UniqueMDiffAt[s] b) (x 
: Z b) : UniqueMDiffAt[π F Z ⁻¹' s] ⟨b, x⟩
参数：hs : UniqueMDiffAt[s] b；x : Z b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.bundle_preimage`：UniqueMDiffWithinAt.bundle_preimage
 {p : TotalSpace F Z} (hs : UniqueMDiffAt[s] p.proj) : UniqueMDiffAt[π F Z ⁻¹' s
] p

--- 原说明 ---
In a fiber bundle, the preimage under the projection of a set with unique differ
entials
in the base has unique differentials in the bundle. Version with a point `⟨b, x⟩
`.
-/
theorem UniqueMDiffWithinAt.bundle_preimage' {b : M} (hs : UniqueMDiffAt[s] b) (x : Z b) :
    UniqueMDiffAt[π F Z ⁻¹' s] ⟨b, x⟩ :=
  hs.bundle_preimage (p := ⟨b, x⟩)

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. -/
/-
**UniqueMDiffOn.bundle_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.bundle_preimage (hs : UniqueMDiff[s]) : UniqueMDiff[π F Z ⁻¹
' s]
参数：hs : UniqueMDiff[s]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.bundle_preimage`：UniqueMDiffWithinAt.bundle_preimage
 {p : TotalSpace F Z} (hs : UniqueMDiffAt[s] p.proj) : UniqueMDiffAt[π F Z ⁻¹' s
] p

--- 原说明 ---
In a fiber bundle, the preimage under the projection of a set with unique differ
entials
in the base has unique differentials in the bundle.
-/
theorem UniqueMDiffOn.bundle_preimage (hs : UniqueMDiff[s]) : UniqueMDiff[π F Z ⁻¹' s] :=
  fun _p hp ↦ (hs _ hp).bundle_preimage

end UniqueMDiff

