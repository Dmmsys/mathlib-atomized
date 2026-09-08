/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.Notation

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `MDifferentiable`, `ContMDiff`, `mfderiv`, `tangentMap`
and related notions.

## Main statements

* `ContMDiffOn.contMDiffOn_tangentMapWithin` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `ContMDiff.contMDiff_tangentMap` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

@[expose] public section

open Set Function Filter ChartedSpace IsManifold Bundle

open scoped Topology Manifold Bundle

/-! ### Definition of `C^n` functions between manifolds -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : WithTop ℕ∞}
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a `C^n` manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [Js : IsManifold J 1 N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare functions, sets
  {f : M → M'} {s : Set M}

/-! ### The derivative of a `C^(n+1)` function is `C^n` -/

section mfderiv
variable [Is : IsManifold I 1 M] [I's : IsManifold I' 1 M']

/-- The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is `C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
Version within a set.
-/
/-
**ContMDiffWithinAt.mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {m n : WithTop ℕ∞} {E 
: Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Ty
pe u_3} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4
}   [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [i
nst_6 : NormedAddCommGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [in
st_8 : TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [i
nst_9 : TopologicalSpace M'] [inst_10 : ChartedSpace H' M'] {F : Type u_8}   [in
st_11 : NormedAddCommGroup F] [inst_12 : NormedSpace 𝕜 F] {G : Type u_9} [inst_1
3 : TopologicalSpace G]   {J : ModelWithCorners 𝕜 F G} {N : Type u_10} [inst_14 
: TopologicalSpace N] [inst_15 : ChartedSpace G N]   [Js : IsManifold J 1 N] [Is
 : IsManifold I 1 M] [I's : IsManifold I' 1 M'] {x₀ : N} {f : N → M → M'} {g : N
 → M}   {t : Set N} {u : Set M},   ContMDiffWithinAt (J.prod I) I' n (Function.u
ncurry f) (t ×ˢ u) (x₀, g x₀) →     ContMDiffWithinAt J I m g t x₀ →       x₀ ∈ 
t →         Set.MapsTo g t u →           m + 1 ≤ n →             UniqueMDiff[u] 
→               ContMDiffWithinAt J (modelWithCornersSelf 𝕜 (E →L[𝕜] E')) m     
            (inTangentCoordinates I I' g (fun x => f x (g x)) (fun x => mfderiv[
u] (f x) (g x)) x₀) t x₀
参数：J.prod I；Function.uncurry f；t ×ˢ u；x₀, g x₀；modelWithCornersSelf 𝕜 (E →L[𝕜] E
')；inTangentCoordinates I I' g (fun x => f x (g x)) (fun x => mfderiv[u] (f x) (
g x)) x₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin`：contMDiffWithinAt_if
f_contMDiffWithinAt_nhdsWithin [IsManifold I n M] [IsManifold I' n M'] (hn : n !
= ∞) : ContMDiffWithinAt I I' n f s x ↔ …
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C
^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is 
`C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative se
nsible.
Version within a set.
-/
protected theorem ContMDiffWithinAt.mfderivWithin {x₀ : N} {f : N → M → M'} {g : N → M}
    {t : Set N} {u : Set M}
    (hf : CMDiffAt[t ×ˢ u] n (Function.uncurry f) (x₀, g x₀))
    (hg : CMDiffAt[t] m g x₀) (hx₀ : x₀ ∈ t)
    (hu : MapsTo g t u) (hmn : m + 1 ≤ n) (h'u : UniqueMDiff[u]) :
    CMDiffAt[t] m (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) x₀) x₀ := by
  -- first localize the result to a smaller set, to make sure everything happens in chart domains
  let t' := t ∩ g ⁻¹' ((extChartAt I (g x₀)).source)
  have ht't : t' ⊆ t := inter_subset_left
  suffices CMDiffAt[t'] m (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) x₀) x₀ by
    apply ContMDiffWithinAt.mono_of_mem_nhdsWithin this
    apply inter_mem self_mem_nhdsWithin
    exact hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (g x₀))
  -- register a few basic facts that maps send suitable neighborhoods to suitable neighborhoods,
  -- by continuity
  have hx₀gx₀ : (x₀, g x₀) ∈ t ×ˢ u := by simp [hx₀, hu hx₀]
  have h4f : ContinuousWithinAt (fun x ↦ f x (g x)) t x₀ := by
    change ContinuousWithinAt ((Function.uncurry f) ∘ (fun x ↦ (x, g x))) t x₀
    refine ContinuousWithinAt.comp hf.continuousWithinAt ?_ (fun y hy ↦ by simp [hy, hu hy])
    exact (continuousWithinAt_id.prodMk hg.continuousWithinAt)
  have h4f := h4f.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I') (f x₀ (g x₀)))
  have h3f := (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).mp
    (hf.of_le <| (self_le_add_left 1 m).trans hmn)
  simp only [hx₀gx₀, insert_eq_of_mem] at h3f
  have h2f : ∀ᶠ x₂ in 𝓝[t] x₀, CMDiffAt[u] 1 (f x₂) (g x₂) := by
    have : MapsTo (fun x ↦ (x, g x)) t (t ×ˢ u) := fun y hy ↦ by simp [hy, hu hy]
    filter_upwards [((continuousWithinAt_id.prodMk hg.continuousWithinAt)
      |>.tendsto_nhdsWithin this).eventually h3f, self_mem_nhdsWithin] with x hx h'x
    apply hx.comp (g x) (contMDiffWithinAt_const.prodMk contMDiffWithinAt_id)
    exact fun y hy ↦ by simp [h'x, hy]
  have h2g : g ⁻¹' (extChartAt I (g x₀)).source ∈ 𝓝[t] x₀ :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (g x₀))
  -- key point: the derivative of `f` composed with extended charts, at the point `g x` read in the
  -- chart, is `C^n` in the vector space sense. This follows from `ContDiffWithinAt.fderivWithin`,
  -- which is the vector space analogue of the result we are proving.
  have : ContDiffWithinAt 𝕜 m (fun x ↦ fderivWithin 𝕜
        (extChartAt I' (f x₀ (g x₀)) ∘ f ((extChartAt J x₀).symm x) ∘ (extChartAt I (g x₀)).symm)
        ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        (extChartAt I (g x₀) (g ((extChartAt J x₀).symm x))))
      ((extChartAt J x₀).symm ⁻¹' t' ∩ range J) (extChartAt J x₀ x₀) := by
    have hf' := hf.mono (prod_mono_left ht't)
    have hg' := hg.mono (show t' ⊆ t from inter_subset_left)
    rw [contMDiffWithinAt_iff] at hf' hg'
    simp_rw [Function.comp_def, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm,
      ModelWithCorners.range_prod] at hf' ⊢
    apply ContDiffWithinAt.fderivWithin _ _ _ (show (m : WithTop ℕ∞) + 1 ≤ n from mod_cast hmn)
    · simp [hx₀, t']
    · apply inter_subset_left.trans
      rw [preimage_subset_iff]
      intro a ha
      refine ⟨PartialEquiv.map_source _ (inter_subset_right ha :), ?_⟩
      rw [mem_preimage, PartialEquiv.left_inv (extChartAt I (g x₀))]
      · exact hu (inter_subset_left ha)
      · exact (inter_subset_right ha :)
    · have : ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ (extChartAt I (g x₀)).target)
          ⊆ ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ range I) := by
        apply inter_subset_inter_right
        exact Set.prod_mono_right (extChartAt_target_subset_range (g x₀))
      convert! hf'.2.mono this
      · ext y; simp; tauto
      · simp
    · exact hg'.2
    · exact UniqueMDiffOn.uniqueDiffOn_target_inter h'u (g x₀)
  -- reformulate the previous point as `C^n` in the manifold sense (but still for a map between
  -- vector spaces)
  have : CMDiffAt[t'] m
      (fun x ↦ fderivWithin 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ f x ∘ (extChartAt I (g x₀)).symm)
      ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        (extChartAt I (g x₀) (g x))) x₀ := by
    simp_rw [contMDiffWithinAt_iff_source (x := x₀),
      contMDiffWithinAt_iff_contDiffWithinAt, Function.comp_def]
    exact this
  -- finally, argue that the map we control in the previous point coincides locally with the map we
  -- want to prove the regularity of, so regularity of the latter follows from regularity of the
  -- former.
  apply this.congr_of_eventuallyEq_of_mem _ (by simp [t', hx₀])
  apply nhdsWithin_mono _ ht't
  filter_upwards [h2f, h4f, h2g, self_mem_nhdsWithin] with x hx h'x h2 hxt
  have h1 : g x ∈ u := hu hxt
  have h3 : UniqueMDiffAt[(extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u]
      ((extChartAt I (g x₀)) (g x)) := by
    apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    apply UniqueMDiffOn.uniqueDiffOn_target_inter h'u
    refine ⟨PartialEquiv.map_source _ h2, ?_⟩
    rwa [mem_preimage, PartialEquiv.left_inv _ h2]
  have A : mfderiv[range I] ((extChartAt I (g x₀)).symm) ((extChartAt I (g x₀)) (g x))
      = mfderiv[(extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u]
        ((extChartAt I (g x₀)).symm) ((extChartAt I (g x₀)) (g x)) := by
    apply (MDifferentiableWithinAt.mfderivWithin_mono _ h3 _).symm
    · apply mdifferentiableWithinAt_extChartAt_symm
      exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
    · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
  rw [inTangentCoordinates_eq_mfderiv_comp, A,
    ← mfderivWithin_comp_of_eq, ← mfderiv_comp_mfderivWithin_of_eq]
  · exact mfderivWithin_eq_fderivWithin
  · exact mdifferentiableAt_extChartAt (by simpa using h'x)
  · apply MDifferentiableWithinAt.comp (I' := I) (u := u) _ _ _ inter_subset_right
    · convert! hx.mdifferentiableWithinAt one_ne_zero
      exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
    · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
      · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
      · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact h3
  · simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I (g x₀)) h2]
  · exact hx.mdifferentiableWithinAt one_ne_zero
  · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
    · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
    · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact inter_subset_right
  · exact h3
  · exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
  · simpa using h2
  · simpa using h'x

/-- The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `ContMDiffWithinAt.mfderivWithin` where `f` does not contain any
parameters and `g = id`.
-/
/-
**ContMDiffWithinAt.mfderivWithin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mfderivWithin_const {x₀ : M} {f : M -> M'} (hf : CMDiffA
t[s] n f x₀) (hmn : m + 1 <= n) (hx : x₀ in s) (hs : UniqueMDiff[s]) : CMDiffAt[
s] m (inTangentCoordinates I I' id f (mfderiv[s] f) x₀) x₀
参数：hf : CMDiffAt[s] n f x₀；hmn : m + 1 <= n；hx : x₀ in s；hs : UniqueMDiff[s]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `contMDiffWithinAt_snd`：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) J n Prod.snd s p
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
· 使用定理 `ContMDiffWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {m n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpac…
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s

--- 原说明 ---
The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a co
ntinuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative se
nsible.
This is a special case of `ContMDiffWithinAt.mfderivWithin` where `f` does not c
ontain any
parameters and `g = id`.
-/
theorem ContMDiffWithinAt.mfderivWithin_const {x₀ : M} {f : M → M'}
    (hf : CMDiffAt[s] n f x₀) (hmn : m + 1 ≤ n) (hx : x₀ ∈ s) (hs : UniqueMDiff[s]) :
    CMDiffAt[s] m (inTangentCoordinates I I' id f (mfderiv[s] f) x₀) x₀ := by
  have : CMDiffAt[s ×ˢ s] n (fun x : M × M ↦ f x.2) (x₀, x₀) :=
    hf.comp (x₀, x₀) contMDiffWithinAt_snd mapsTo_snd_prod
  exact this.mfderivWithin contMDiffWithinAt_id hx (mapsTo_id _) hmn hs

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is similar to `ContMDiffWithinAt.mfderivWithin`, but where the continuous linear map is
applied to a (variable) vector.
-/
/-
**ContMDiffWithinAt.mfderivWithin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mfderivWithin_apply {x₀ : N'} {f : N -> M -> M'} {g : N 
-> M} {g₁ : N' -> N} {g₂ : N' -> E} {t : Set N} {u : Set M} {v : Set N'} (hf : C
MDiffAt[t ×ˢ u] n (Function.uncurry f) (g₁ x₀, g (g₁ x₀))) (hg : CMDiffAt[t] m g
 (g₁ x₀)) (hg₁ : CMDiffAt[v] m g₁ x₀) (hg₂ : CMDiffAt[v] m g₂ x₀) (hmn : m + 1 <
= n) (h'g₁ : MapsTo g₁ v t) (hg₁x₀ : g₁ x₀ in t) (h'g : MapsTo g t u) (hu : Uniq
ueMDiff[u]) : CMDiffAt[v] m (fun x => (inTangentCoordinates I I' g (fun x => f x
 (g x)) (fun x => mfderiv[
参数：hf : CMDiffAt[t ×ˢ u] n (Function.uncurry f) (g₁ x₀, g (g₁ x₀))；hg : CMDiffAt
[t] m g (g₁ x₀)；hg₁ : CMDiffAt[v] m g₁ x₀；hg₂ : CMDiffAt[v] m g₂ x₀；hmn : m + 1 
<= n；h'g₁ : MapsTo g₁ v t；hg₁x₀ : g₁ x₀ in t；h'g : MapsTo g t u；hu : UniqueMDiff
[u]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.clm_apply`：ContMDiffWithinAt.clm_apply {g : M -> F₁ ->
L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L
[𝕜] F₂) n g s x) …
· 使用定理 `ContMDiffWithinAt.comp_of_eq`：ContMDiffWithinAt.comp_of_eq {t : Set M'} 
{g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffWithinAt I' I'' n g t y) (hf : C
ontMDiffWithinAt I…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {m n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpac…

--- 原说明 ---
The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied 
to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀
`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivativ
e sensible.

This is similar to `ContMDiffWithinAt.mfderivWithin`, but where the continuous l
inear map is
applied to a (variable) vector.
-/
theorem ContMDiffWithinAt.mfderivWithin_apply {x₀ : N'}
    {f : N → M → M'} {g : N → M} {g₁ : N' → N} {g₂ : N' → E} {t : Set N} {u : Set M} {v : Set N'}
    (hf : CMDiffAt[t ×ˢ u] n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : CMDiffAt[t] m g (g₁ x₀)) (hg₁ : CMDiffAt[v] m g₁ x₀)
    (hg₂ : CMDiffAt[v] m g₂ x₀) (hmn : m + 1 ≤ n) (h'g₁ : MapsTo g₁ v t)
    (hg₁x₀ : g₁ x₀ ∈ t) (h'g : MapsTo g t u) (hu : UniqueMDiff[u]) :
    CMDiffAt[v] m (fun x ↦ (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) (g₁ x₀) (g₁ x)) (g₂ x)) x₀ :=
  ((hf.mfderivWithin hg hg₁x₀ h'g hmn hu).comp_of_eq hg₁ h'g₁ rfl).clm_apply hg₂

/-- The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is `C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This result is used to show that maps into the 1-jet bundle and cotangent bundle are `C^n`.
`ContMDiffAt.mfderiv_const` is a special case of this.
-/
/-
**ContMDiffAt.mfderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {m n : WithTop ℕ∞} {E 
: Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Ty
pe u_3} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4
}   [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [i
nst_6 : NormedAddCommGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [in
st_8 : TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [i
nst_9 : TopologicalSpace M'] [inst_10 : ChartedSpace H' M'] {F : Type u_8}   [in
st_11 : NormedAddCommGroup F] [inst_12 : NormedSpace 𝕜 F] {G : Type u_9} [inst_1
3 : TopologicalSpace G]   {J : ModelWithCorners 𝕜 F G} {N : Type u_10} [inst_14 
: TopologicalSpace N] [inst_15 : ChartedSpace G N]   [Js : IsManifold J 1 N] [Is
 : IsManifold I 1 M] [I's : IsManifold I' 1 M'] {x₀ : N} (f : N → M → M') (g : N
 → M),   ContMDiffAt (J.prod I) I' n (Function.uncurry f) (x₀, g x₀) →     ContM
DiffAt J I m g x₀ →       m + 1 ≤ n →         ContMDiffAt J (modelWithCornersSel
f 𝕜 (E →L[𝕜] E')) m           (inTangentCoordinates I I' g (fun x => f x (g x)) 
(fun x => mfderiv% (f x) (g x)) x₀) x₀
参数：f : N → M → M'；g : N → M；J.prod I；Function.uncurry f；x₀, g x₀；modelWithCorner
sSelf 𝕜 (E →L[𝕜] E')；inTangentCoordinates I I' g (fun x => f x (g x)) (fun x => 
mfderiv% (f x) (g x)) x₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContMDiffWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {m n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpac…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]

--- 原说明 ---
The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C
^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is 
`C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative se
nsible.
This result is used to show that maps into the 1-jet bundle and cotangent bundle
 are `C^n`.
`ContMDiffAt.mfderiv_const` is a special case of this.
-/
protected theorem ContMDiffAt.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
    (hf : CMDiffAt n (Function.uncurry f) (x₀, g x₀)) (hg : CMDiffAt m g x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m
      (inTangentCoordinates I I' g (fun x ↦ f x (g x)) (fun x ↦ mfderiv% (f x) (g x)) x₀) x₀ := by
  rw [← contMDiffWithinAt_univ] at hf hg ⊢
  rw [← univ_prod_univ] at hf
  simp_rw [← mfderivWithin_univ]
  exact ContMDiffWithinAt.mfderivWithin hf hg (mem_univ _) (mapsTo_univ _ _) hmn
    uniqueMDiffOn_univ

/-- The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `ContMDiffAt.mfderiv` where `f` does not contain any parameters and
`g = id`.
-/
/-
**ContMDiffAt.mfderiv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.mfderiv_const {x₀ : M} {f : M -> M'} (hf : CMDiffAt n f x₀) (h
mn : m + 1 <= n) : CMDiffAt m (inTangentCoordinates I I' id f (mfderiv% f) x₀) x
₀
参数：hf : CMDiffAt n f x₀；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {m n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpac…
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `contMDiffAt_snd`：contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J 
n Prod.snd p
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x

--- 原说明 ---
The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a co
ntinuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative se
nsible.
This is a special case of `ContMDiffAt.mfderiv` where `f` does not contain any p
arameters and
`g = id`.
-/
theorem ContMDiffAt.mfderiv_const {x₀ : M} {f : M → M'} (hf : CMDiffAt n f x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m (inTangentCoordinates I I' id f (mfderiv% f) x₀) x₀ :=
  haveI : CMDiffAt n (fun x : M × M ↦ f x.2) (x₀, x₀) :=
    ContMDiffAt.comp (x₀, x₀) hf contMDiffAt_snd
  this.mfderiv (fun _ ↦ f) id contMDiffAt_id hmn

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is similar to `ContMDiffAt.mfderiv`, but where the continuous linear map is applied to a
(variable) vector.
-/
/-
**ContMDiffAt.mfderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.mfderiv_apply {x₀ : N'} (f : N -> M -> M') (g : N -> M) (g₁ : 
N' -> N) (g₂ : N' -> E) (hf : CMDiffAt n (Function.uncurry f) (g₁ x₀, g (g₁ x₀))
) (hg : CMDiffAt m g (g₁ x₀)) (hg₁ : CMDiffAt m g₁ x₀) (hg₂ : CMDiffAt m g₂ x₀) 
(hmn : m + 1 <= n) : CMDiffAt m (fun x => inTangentCoordinates I I' g (fun x => 
f x (g x)) (fun x => mfderiv% (f x) (g x)) (g₁ x₀) (g₁ x) (g₂ x)) x₀
参数：f : N -> M -> M'；g : N -> M；g₁ : N' -> N；g₂ : N' -> E；hf : CMDiffAt n (Functi
on.uncurry f) (g₁ x₀, g (g₁ x₀))；hg : CMDiffAt m g (g₁ x₀)；hg₁ : CMDiffAt m g₁ x
₀；hg₂ : CMDiffAt m g₂ x₀；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.clm_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `ContMDiffAt.comp_of_eq`：ContMDiffAt.comp_of_eq {g : M' -> M''} {x : M} {
y : M'} (hg : ContMDiffAt I' I'' n g y) (hf : ContMDiffAt I I' n f x) (hx : f x 
= y) : ContM…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {m n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpac…

--- 原说明 ---
The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied 
to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀
`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivativ
e sensible.

This is similar to `ContMDiffAt.mfderiv`, but where the continuous linear map is
 applied to a
(variable) vector.
-/
theorem ContMDiffAt.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N) (g₂ : N' → E)
    (hf : CMDiffAt n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : CMDiffAt m g (g₁ x₀)) (hg₁ : CMDiffAt m g₁ x₀) (hg₂ : CMDiffAt m g₂ x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m (fun x ↦ inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv% (f x) (g x)) (g₁ x₀) (g₁ x) (g₂ x)) x₀ :=
  ((hf.mfderiv f g hg hmn).comp_of_eq hg₁ rfl).clm_apply hg₂

end mfderiv

/-! ### The tangent map of a `C^(n+1)` function is `C^n` -/

section tangentMap

variable [Is : IsManifold I 1 M] [I's : IsManifold I' 1 M']

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
/-
**ContMDiffOn.contMDiffOn_tangentMapWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.contMDiffOn_tangentMapWithin (hf : CMDiff[s] n f) (hmn : m + 1
 <= n) (hs : UniqueMDiff[s]) : CMDiff[(π E (TangentSpace I) ⁻¹' s)] m (tangentMa
p[s] f)
参数：hf : CMDiff[s] n f；hmn : m + 1 <= n；hs : UniqueMDiff[s]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Bundle.contMDiffWithinAt_proj`：contMDiffWithinAt_proj {s : Set (TotalSpa
ce F E)} {p : TotalSpace F E} : ContMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E)
 s p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffWithinAt.mfderivWithin_const`：ContMDiffWithinAt.mfderivWithin_c
onst {x₀ : M} {f : M -> M'} (hf : CMDiffAt[s] n f x₀) (hmn : m + 1 <= n) (hx : x
₀ in s) (hs : UniqueMDiff[s…
· 使用引理 `ContMDiffWithinAt.clm_apply_of_inCoordinates`：ContMDiffWithinAt.clm_appl
y_of_inCoordinates (hϕ : CMDiffAt[s] n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m
₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀…

--- 原说明 ---
If a function is `C^n` on a domain with unique derivatives, then its bundled der
ivative
is `C^m` when `m+1 ≤ n`.
-/
theorem ContMDiffOn.contMDiffOn_tangentMapWithin
    (hf : CMDiff[s] n f) (hmn : m + 1 ≤ n) (hs : UniqueMDiff[s]) :
    CMDiff[(π E (TangentSpace I) ⁻¹' s)] m (tangentMap[s] f) := by
  intro x₀ hx₀
  let s' : Set (TangentBundle I M) := (π E (TangentSpace I) ⁻¹' s)
  let b₁ : TangentBundle I M → M := fun p ↦ p.1
  let v : Π (y : TangentBundle I M), TangentSpace% (b₁ y) := fun y ↦ y.2
  have hv : CMDiffAt[s'] m (fun y ↦ (v y : TangentBundle I M)) x₀ := contMDiffWithinAt_id
  let b₂ : TangentBundle I M → M' := f ∘ b₁
  have hb₂ : CMDiffAt[s'] m b₂ x₀ :=
    ((hf (b₁ x₀) hx₀).of_le (le_self_add.trans hmn)).comp _
      (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  let ϕ : Π (y : TangentBundle I M), TangentSpace% (b₁ y) →L[𝕜] TangentSpace% (b₂ y) :=
    fun y ↦ mfderiv[s] f (b₁ y)
  have hϕ : CMDiffAt[s'] m (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
      (TangentSpace I' (M := M')) (b₁ x₀) (b₁ y) (b₂ x₀) (b₂ y) (ϕ y)) x₀ := by
    have A : CMDiffAt[s] m (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
        (TangentSpace I' (M := M')) (b₁ x₀) y (b₂ x₀) (f y) (mfderiv[s] f y)) (b₁ x₀) :=
      .mfderivWithin_const (hf _ hx₀) hmn hx₀ hs
    exact A.comp _ (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
/-
**ContMDiffOn.continuousOn_tangentMapWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.continuousOn_tangentMapWithin (hf : CMDiff[s] n f) (hmn : 1 <=
 n) (hs : UniqueMDiff[s]) : ContinuousOn (tangentMap[s] f) (π E (TangentSpace I)
 ⁻¹' s)
参数：hf : CMDiff[s] n f；hmn : 1 <= n；hs : UniqueMDiff[s]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffOn_tangentMapWithin`：ContMDiffOn.contMDiffOn_tangen
tMapWithin (hf : CMDiff[s] n f) (hmn : m + 1 <= n) (hs : UniqueMDiff[s]) : CMDif
f[(π E (TangentSpace I) ⁻¹' s)…
· 使用定理 `ContMDiffOn.continuousOn`：ContMDiffOn.continuousOn (hf : ContMDiffOn I I
' n f s) : ContinuousOn f s

--- 原说明 ---
If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then i
ts bundled
derivative is continuous there.
-/
theorem ContMDiffOn.continuousOn_tangentMapWithin (hf : CMDiff[s] n f) (hmn : 1 ≤ n)
    (hs : UniqueMDiff[s]) :
    ContinuousOn (tangentMap[s] f) (π E (TangentSpace I) ⁻¹' s) := by
  have : CMDiff[π E (TangentSpace I) ⁻¹' s] 0 (tangentMap[s] f) :=
    hf.contMDiffOn_tangentMapWithin hmn hs
  exact this.continuousOn

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
/-
**ContMDiff.contMDiff_tangentMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.contMDiff_tangentMap (hf : CMDiff n f) (hmn : m + 1 <= n) : CMDi
ff m (tangentMap% f)
参数：hf : CMDiff n f；hmn : m + 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `tangentMapWithin_univ`：tangentMapWithin_univ : tangentMap[(univ : Set M)
] f = tangentMap% f
· 使用定理 `ContMDiffOn.contMDiffOn_tangentMapWithin`：ContMDiffOn.contMDiffOn_tangen
tMapWithin (hf : CMDiff[s] n f) (hmn : m + 1 <= n) (hs : UniqueMDiff[s]) : CMDif
f[(π E (TangentSpace I) ⁻¹' s)…
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]

--- 原说明 ---
If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`.
-/
theorem ContMDiff.contMDiff_tangentMap (hf : CMDiff n f) (hmn : m + 1 ≤ n) :
    CMDiff m (tangentMap% f) := by
  rw [← contMDiffOn_univ] at hf ⊢
  convert! hf.contMDiffOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
/-
**ContMDiff.continuous_tangentMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.continuous_tangentMap (hf : CMDiff n f) (hmn : 1 <= n) : Continu
ous (tangentMap% f)
参数：hf : CMDiff n f；hmn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `tangentMapWithin_univ`：tangentMapWithin_univ : tangentMap[(univ : Set M)
] f = tangentMap% f
· 使用定理 `ContMDiffOn.continuousOn_tangentMapWithin`：ContMDiffOn.continuousOn_tang
entMapWithin (hf : CMDiff[s] n f) (hmn : 1 <= n) (hs : UniqueMDiff[s]) : Continu
ousOn (tangentMap[s] f) (π E (T…
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]

--- 原说明 ---
If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous.
-/
theorem ContMDiff.continuous_tangentMap (hf : CMDiff n f) (hmn : 1 ≤ n) :
    Continuous (tangentMap% f) := by
  rw [← contMDiffOn_univ] at hf
  rw [← continuousOn_univ]
  convert! hf.continuousOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

end tangentMap

namespace TangentBundle

open Bundle

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
/-
**TangentBundle.tangentMap_tangentBundle_pure** 是 Mathlib 中的一个定理，位于命名空间 `Tangent
Bundle`。
形式化陈述：tangentMap_tangentBundle_pure [Is : IsManifold I 1 M] (p : TangentBundle I
 M) : tangentMap% (zeroSection (B
参数：p : TangentBundle I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ModelWithCorners.continuous_invFun`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ContMDiff.mdifferentiableAt`：ContMDiff.mdifferentiableAt (hf : CMDiff n 
f) (hn : n != 0) : MDiffAt f x
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `fderivWithin_eq_fderiv`：fderivWithin_eq_fderiv [ContinuousAdd E] [Contin
uousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDif
fWithinAt 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ModelWithCorners.uniqueDiffWithinAt_image`：uniqueDiffWithinAt_image {x :
 H} : UniqueDiffWithinAt 𝕜 (range I) (I x)
· 使用定理 `DifferentiableAt.prodMk`：DifferentiableAt.prodMk (hf₁ : DifferentiableAt
 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x : E => (f₁ 
x, f₂ x)) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `DifferentiableAt.fderiv_prodMk`：DifferentiableAt.fderiv_prodMk (hf₁ : Di
fferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) : fderiv 𝕜 (fun x : E => 
(f₁ x, f₂ x)) x = (f…
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderiv_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : 
Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Top
olo…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderiv_fun_const`：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) =
 0
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 
0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant
 on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the c
oordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical spl
itting at each
point of the zero section (since there is a canonical horizontal space there, th
e tangent space
to the zero section, in addition to the canonical vertical space which is the ke
rnel of the
derivative of the projection), and this canonical splitting is also the one that
 comes from the
coordinates on the tangent bundle in our definitions. So this statement is not a
s crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly.
-/
theorem tangentMap_tangentBundle_pure [Is : IsManifold I 1 M]
    (p : TangentBundle I M) :
    tangentMap% (zeroSection (B := M) E (TangentSpace I)) p = ⟨⟨p.proj, 0⟩, ⟨p.2, 0⟩⟩ := by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chartAt H x).target ∈ 𝓝 (I ((chartAt H x) x)) := by
    apply IsOpen.mem_nhds
    · apply (OpenPartialHomeomorph.open_target _).preimage I.continuous_invFun
    · simp only [mfld_simps]
  have A : MDiffAt (fun x ↦ TotalSpace.mk' E (x : M) (0 : TangentSpace I x)) x :=
    haveI : CMDiff 1 (zeroSection E (TangentSpace I : M → Type _)) :=
      Bundle.contMDiff_zeroSection 𝕜 (TangentSpace I : M → Type _)
    this.mdifferentiableAt one_ne_zero
  have B : fderivWithin 𝕜 (fun x' : E ↦ (x', (0 : E))) (Set.range I) (I ((chartAt H x) x)) v
      = (v, 0) := by
    rw [fderivWithin_eq_fderiv, DifferentiableAt.fderiv_prodMk]
    · simp
    · exact differentiableAt_fun_id
    · exact differentiableAt_const _
    · exact ModelWithCorners.uniqueDiffWithinAt_image I
    · exact differentiableAt_id.prodMk (differentiableAt_const _)
  simp +unfoldPartialApp only [Bundle.zeroSection, tangentMap, mfderiv, A,
    if_pos, chartAt, FiberBundle.chartedSpace_chartAt, TangentBundle.trivializationAt_apply,
    Function.comp_def, map_zero, mfld_simps]
  rw [← fderivWithin_inter N] at B
  rw [← fderivWithin_inter N, ← B]
  congr 1
  refine fderivWithin_congr (fun y hy ↦ ?_) ?_
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]

end TangentBundle

namespace ContMDiffMap

-- These helpers for dot notation have been moved here from
-- `Mathlib/Geometry/Manifold/ContMDiffMap.lean` to avoid needing to import this file there.
-- (However as a consequence we import `Mathlib/Geometry/Manifold/ContMDiffMap.lean` here now.)
-- They could be moved to another file (perhaps a new file) if desired.
open scoped Manifold ContDiff

/-
**ContMDiffMap.mdifferentiable'** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {E : 
Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type
 u_3} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4} 
  [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [ins
t_6 : NormedAddCommGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst
_8 : TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [ins
t_9 : TopologicalSpace M'] [inst_10 : ChartedSpace H' M'] (f : ContMDiffMap I I'
 M M' n),   n ≠ 0 → MDiff ⇑f
参数：f : ContMDiffMap I I' M M' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `ContMDiffMap.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
-/
protected theorem mdifferentiable' (f : C^n⟮I, M; I', M'⟯) (hn : n ≠ 0) : MDiff f :=
  f.contMDiff.mdifferentiable hn
/-
**ContMDiffMap.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] (f : ContMDiffMap I I' M M' ↑⊤),   MDif
f ⇑f
参数：f : ContMDiffMap I I' M M' ↑⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.mdifferentiable'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {n : WithTop ℕ∞} {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : MDiff f :=
  f.mdifferentiable' (by simp)
/-
**ContMDiffMap.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] (f : ContMDiffMap I I' M M' ↑⊤) {x : M}
,   MDiffAt ⇑f x
参数：f : ContMDiffMap I I' M M' ↑⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.mdifferentiable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
-/
protected theorem mdifferentiableAt (f : C^∞⟮I, M; I', M'⟯) {x} : MDiffAt f x :=
  f.mdifferentiable x

end ContMDiffMap

section EquivTangentBundleProd

variable (I I' M M') in
/-- The tangent bundle of a product is canonically isomorphic to the product of the tangent
bundles. -/
/-
**equivTangentBundleProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     (I : ModelWithCorners 𝕜 E H) →                 (M : Type u_4) →            
       [inst_4 : TopologicalSpace M] →                     [inst_5 : ChartedSpac
e H M] →                       {E' : Type u_5} →                         [inst_6
 : NormedAddCommGroup E'] →                           [inst_7 : NormedSpace 𝕜 E'
] →                             {H' : Type u_6} →                               
[inst_8 : TopologicalSpace H'] →                                 (I' : ModelWith
Corners 𝕜 E' H') →                                   (M' : Type u_7) →          
                           [inst_9 : TopologicalSpace M'] →                     
                  [inst_10 : ChartedSpace H' M'] →                              
           TangentBundle (I.prod I') (M × M') ≃ TangentBundle I M × TangentBundl
e I' M'
参数：I : ModelWithCorners 𝕜 E H；M : Type u_4；I' : ModelWithCorners 𝕜 E' H'；M' : Ty
pe u_7；I.prod I'；M × M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent bundle of a product is canonically isomorphic to the product of the 
tangent
bundles.
-/
@[simps] def equivTangentBundleProd :
    TangentBundle (I.prod I') (M × M') ≃ (TangentBundle I M) × (TangentBundle I' M') where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
/-
**equivTangentBundleProd_eq_tangentMap_prod_tangentMap** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：equivTangentBundleProd_eq_tangentMap_prod_tangentMap : equivTangentBundleP
rod I M I' M' = fun (p : TangentBundle (I.prod I') (M × M')) => (tangentMap% (@P
rod.fst M M') p, tangentMap% (@Prod.snd M M') p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tangentMap_prodFst`：tangentMap_prodFst {p : TangentBundle (I.prod I') (M
 × M')} : tangentMap% (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩
· 使用定理 `tangentMap_prodSnd`：tangentMap_prodSnd {p : TangentBundle (I.prod I') (M
 × M')} : tangentMap% (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩
-/
lemma equivTangentBundleProd_eq_tangentMap_prod_tangentMap :
    equivTangentBundleProd I M I' M' = fun (p : TangentBundle (I.prod I') (M × M')) ↦
      (tangentMap% (@Prod.fst M M') p, tangentMap% (@Prod.snd M M') p) := by
  simp only [tangentMap_prodFst, tangentMap_prodSnd]; rfl

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The canonical equivalence between the tangent bundle of a product and the product of
tangent bundles is smooth. -/
/-
**contMDiff_equivTangentBundleProd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_equivTangentBundleProd : CMDiff n (equivTangentBundleProd I M I'
 M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `equivTangentBundleProd_eq_tangentMap_prod_tangentMap`：equivTangentBundle
Prod_eq_tangentMap_prod_tangentMap : equivTangentBundleProd I M I' M' = fun (p :
 TangentBundle (I.prod I') (M × M')) => (t…
· 使用定理 `ContMDiff.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiff.contMDiff_tangentMap`：ContMDiff.contMDiff_tangentMap (hf : CMD
iff n f) (hmn : m + 1 <= n) : CMDiff m (tangentMap% f)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)

--- 原说明 ---
The canonical equivalence between the tangent bundle of a product and the produc
t of
tangent bundles is smooth.
-/
lemma contMDiff_equivTangentBundleProd :
    CMDiff n (equivTangentBundleProd I M I' M') := by
  rw [equivTangentBundleProd_eq_tangentMap_prod_tangentMap]
  exact (contMDiff_fst.contMDiff_tangentMap le_rfl).prodMk
    (contMDiff_snd.contMDiff_tangentMap le_rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical equivalence between the product of tangent bundles and the tangent bundle of a
product is smooth. -/
/-
**contMDiff_equivTangentBundleProd_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_equivTangentBundleProd_symm : CMDiff n (equivTangentBundleProd I
 M I' M').symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `UniqueDiffWithinAt.prod`：UniqueDiffWithinAt.prod (hs : UniqueDiffWithinA
t 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ModelWithCorners.uniqueDiffWithinAt_image`：uniqueDiffWithinAt_image {x :
 H} : UniqueDiffWithinAt 𝕜 (range I) (I x)
· 使用定理 `Bundle.contMDiffAt_totalSpace`：contMDiffAt_totalSpace {f : M -> TotalSpa
ce F E} {x₀ : M} : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n
 (fun x => (f x).pr…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `ContMDiffAt.prodMap`：ContMDiffAt.prodMap (hf : ContMDiffAt I I' n f x) (
hg : ContMDiffAt J J' n g y) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f
 g) (x, y…
· 使用定理 `Bundle.contMDiffAt_proj`：contMDiffAt_proj {p : TotalSpace F E} : ContMDi
ffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffAt_prod_module_iff`：contMDiffAt_prod_module_iff (f : M -> F₁ × 
F₂) : ContMDiffAt I 𝓘(𝕜, F₁ × F₂) n f x ↔ ContMDiffAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f
) x ∧ ContMDiffAt…
· 使用定理 `contMDiffAt_fst`：contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I 
n Prod.fst p
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `contDiffWithinAt_ext_coord_change`：contDiffWithinAt_ext_coord_change [Is
Manifold I n M] (x x' : M) {y : E} (hy : y in ((extChartAt I x').symm ≫ extChart
At I x).source) : ContD…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The canonical equivalence between the product of tangent bundles and the tangent
 bundle of a
product is smooth.
-/
lemma contMDiff_equivTangentBundleProd_symm :
    CMDiff n (equivTangentBundleProd I M I' M').symm := by
  /- Contrary to what one might expect, this proof is nontrivial. It is not a formalization issue:
  even on paper, I don't have a simple proof of the statement. The reason is that there is no nice
  functorial expression for the map from `TM × T'M` to `T (M × M')`, so I need to come back to
  the definition and break things into pieces.
  The argument goes as follows. Since we're looking at a map into a vector bundle whose basis map
  is smooth, it suffices to check the smoothness of the second component, in a chart. It lands in
  a product vector space `E × E'`, so it suffices to check that the composition with each projection
  to `E` and `E'` is smooth.
  We notice that the composition of this map with the first projection coincides with the projection
  `TM × TM' → TM` read in the target chart, which is smooth, so we're done.
  The issue is with checking differentiability everywhere (to justify that the derivative of a
  product is the product of the derivatives), and writing down things.
  -/
  rintro ⟨a, b⟩
  have U w w' : UniqueDiffWithinAt 𝕜 (Set.range (Prod.map I I')) (I w, I' w') := by
    simp only [range_prodMap]
    apply UniqueDiffWithinAt.prod
    · exact ModelWithCorners.uniqueDiffWithinAt_image I
    · exact ModelWithCorners.uniqueDiffWithinAt_image I'
  rw [contMDiffAt_totalSpace]
  simp only [equivTangentBundleProd, TangentBundle.trivializationAt_apply, mfld_simps,
    Equiv.coe_fn_symm_mk]
  refine ⟨?_, (contMDiffAt_prod_module_iff _).2 ⟨?_, ?_⟩⟩
  · exact (contMDiffAt_proj (TangentSpace I)).prodMap (contMDiffAt_proj (TangentSpace I'))
  · /- check that the composition with the first projection in the target chart is smooth.
    For this, we check that it coincides locally with the projection `pM : TM × TM' → TM` read in
    the target chart, which is obviously smooth. -/
    have smooth_pM : CMDiffAt n (Prod.fst : TangentBundle I M × TangentBundle I' M' → _) (a, b) :=
      contMDiffAt_fst
    apply (contMDiffAt_totalSpace.1 smooth_pM).2.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    -- now we have to check that the original map coincides locally with `pM` read in target chart.
    simp only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_toPartialHomeomorph,
      PartialEquiv.prod_source, mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I) (I ((chartAt H p.1.proj) p.1.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt _ one_ne_zero
      apply contDiffWithinAt_ext_coord_change
      simp [hp.1]
    have D (w : TangentBundle I' M') :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.fst : E × E' → E)) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' w.proj) w.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0)
        differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
    simp only [comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prodMk (by exact D _) ?_ (U _ _)]; swap
    · let φ' (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I')
          (I' ((chartAt H' p.2.proj) p.2.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt _ one_ne_zero
        apply contDiffWithinAt_ext_coord_change
        simp [hp.2]
      have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.snd) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0')
          differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
      exact D'
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _ = fderivWithin 𝕜 φ _ _ _
    rw [range_prodMap] at U
    rw [fderivWithin_comp _ (by exact D0) differentiableWithinAt_fst mapsTo_fst_prod (U _ _)]
    simp [fderivWithin_fst, U]
  · /- check that the composition with the second projection in the target chart is smooth.
    For this, we check that it coincides locally with the projection `pM' : TM × TM' → TM'` read in
    the target chart, which is obviously smooth. -/
    have smooth_pM' : CMDiffAt n (Prod.snd : TangentBundle I M × TangentBundle I' M' → _) (a, b) :=
      contMDiffAt_snd
    apply (contMDiffAt_totalSpace.1 smooth_pM').2.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    -- now we have to check that the original map coincides locally with `pM'` read in target chart.
    simp only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_toPartialHomeomorph,
      PartialEquiv.prod_source, mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I') (I' ((chartAt H' p.2.proj) p.2.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt _ one_ne_zero
      apply contDiffWithinAt_ext_coord_change
      simp [hp.2]
    have D (w : TangentBundle I M) :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.snd : E × E' → E')) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H w.proj) w.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0)
        differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
    simp only [comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prodMk ?_ (by exact D _) (U _ _)]; swap
    · let φ' (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I)
          (I ((chartAt H p.1.proj) p.1.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt _ one_ne_zero
        apply contDiffWithinAt_ext_coord_change
        simp [hp.1]
      have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.fst) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0')
          differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
      exact D'
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change fderivWithin 𝕜 (φ ∘ Prod.snd) _ _ _ = fderivWithin 𝕜 φ _ _ _
    rw [range_prodMap] at U
    rw [fderivWithin_comp _ (by exact D0) differentiableWithinAt_snd mapsTo_snd_prod (U _ _)]
    simp [fderivWithin_snd, U]

end EquivTangentBundleProd

