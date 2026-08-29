/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Topology.ClusterPt

/-!
# Continuity in topological spaces

For topological spaces `X` and `Y`, a function `f : X → Y` and a point `x : X`,
`ContinuousAt f x` means `f` is continuous at `x`, and global continuity is
`Continuous f`. There is also a version of continuity `PContinuous` for
partially defined functions.

## Tags

continuity, continuous function
-/

@[expose] public section

open Set Filter Topology

variable {X Y Z : Type*}

open TopologicalSpace

-- The curly braces are intentional, so this definition works well with simp
-- when topologies are not those provided by instances.
/--
theorem `continuous_def` / 定理 `continuous_def`

English:
theorem continuous_def
  given: {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X -> Y}
  proof: ⟨fun hf => hf.1, fun h => ⟨h⟩⟩

中文:
定理 continuous_def
  条件: {_ : 拓扑空间 X} {_ : 拓扑空间 Y} {f : X -> Y}
  证明: ⟨fun hf => hf.1, fun h => ⟨h⟩⟩
-/
theorem continuous_def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X -> Y} :
    Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X -> Y} {s : Set X} {x : X} {y : Y}

/--
theorem `IsOpen.preimage` / 定理 `IsOpen.preimage`

English:
theorem IsOpen.preimage
  given: (hf : Continuous f) {t : Set Y} (h : IsOpen t)
  proof: hf.isOpen_preimage t h

中文:
定理 是开集.原像
  条件: (hf : 连续 f) {t : 集合 Y} (h : 是开集 t)
  证明: hf.isOpen_preimage t h

Depends on / 依赖: hf.isOpen_preimage, isOpen_preimage
-/
theorem IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : IsOpen t) :
    IsOpen (f ⁻¹' t) :=
  hf.isOpen_preimage t h

/--
lemma `Equiv.continuous_symm_iff` / 引理 `Equiv.continuous_symm_iff`

English:
lemma Equiv.continuous_symm_iff
  given: (e : X ≃ Y)
  statement: Continuous e.symm ↔ IsOpenMap e
  proof: by
  simp_rw [continuous_def, ← Equiv.image_eq_preimage_symm, IsOpenMap]

中文:
引理 等价.continuous_symm_iff
  条件: (e : X ≃ Y)
  结论: 连续 e.symm ↔ 是开映射 e
  证明: by
  simp_rw [continuous_def, ← Equiv.image_eq_preimage_symm, IsOpenMap]

Depends on / 依赖: Equiv.image_eq_preimage_symm, IsOpenMap, continuous_def, image_eq_preimage_symm, simp_rw
-/
lemma Equiv.continuous_symm_iff (e : X ≃ Y) : Continuous e.symm ↔ IsOpenMap e := by
  simp_rw [continuous_def, ← Equiv.image_eq_preimage_symm, IsOpenMap]

/--
lemma `Equiv.isOpenMap_symm_iff` / 引理 `Equiv.isOpenMap_symm_iff`

English:
lemma Equiv.isOpenMap_symm_iff
  given: (e : X ≃ Y)
  statement: IsOpenMap e.symm ↔ Continuous e
  proof: by
  simp_rw [← Equiv.continuous_symm_iff, Equiv.symm_symm]

中文:
引理 等价.isOpenMap_symm_iff
  条件: (e : X ≃ Y)
  结论: 是开映射 e.symm ↔ 连续 e
  证明: by
  simp_rw [← Equiv.continuous_symm_iff, Equiv.symm_symm]

Depends on / 依赖: Equiv.continuous_symm_iff, Equiv.symm_symm, continuous_symm_iff, simp_rw, symm_symm
-/
lemma Equiv.isOpenMap_symm_iff (e : X ≃ Y) : IsOpenMap e.symm ↔ Continuous e := by
  simp_rw [← Equiv.continuous_symm_iff, Equiv.symm_symm]

/--
theorem `continuous_congr` / 定理 `continuous_congr`

English:
theorem continuous_congr
  given: {g : X -> Y} (h : forall x, f x = g x)
  proof: .of_eq congrArg _ funext h

中文:
定理 continuous_congr
  条件: {g : X -> Y} (h : 对任意 x, f x = g x)
  证明: .of_eq congrArg _ funext h

Depends on / 依赖: of_eq
-/
theorem continuous_congr {g : X -> Y} (h : forall x, f x = g x) :
    Continuous f ↔ Continuous g :=
.of_eq congrArg _ funext h

/--
theorem `Continuous.congr` / 定理 `Continuous.congr`

English:
theorem Continuous.congr
  given: {g : X -> Y} (h : Continuous f) (h' : forall x, f x = g x)
  statement: Continuous g
  proof: .mp h continuous_congr h'

中文:
定理 连续.congr
  条件: {g : X -> Y} (h : 连续 f) (h' : 对任意 x, f x = g x)
  结论: 连续 g
  证明: .mp h continuous_congr h'

Depends on / 依赖: continuous_congr
-/
theorem Continuous.congr {g : X -> Y} (h : Continuous f) (h' : forall x, f x = g x) : Continuous g :=
.mp h continuous_congr h'

/--
theorem `ContinuousAt.tendsto` / 定理 `ContinuousAt.tendsto`

English:
theorem ContinuousAt.tendsto
  given: (h : ContinuousAt f x)
  proof: h

中文:
定理 ContinuousAt.tendsto
  条件: (h : ContinuousAt f x)
  证明: h
-/
theorem ContinuousAt.tendsto (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h

/--
theorem `continuousAt_def` / 定理 `continuousAt_def`

English:
theorem continuousAt_def
  statement: ContinuousAt f x ↔ forall A in 𝓝 (f x), f ⁻¹' A in 𝓝 x
  proof: Iff.rfl

中文:
定理 continuousAt_def
  结论: ContinuousAt f x ↔ 对任意 A in 𝓝 (f x), f ⁻¹' A in 𝓝 x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f x), f ⁻¹' A in 𝓝 x :=
  Iff.rfl

/--
theorem `continuousAt_congr` / 定理 `continuousAt_congr`

English:
theorem continuousAt_congr
  given: {g : X -> Y} (h : f =ᶠ[𝓝 x] g)
  proof: by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]

中文:
定理 continuousAt_congr
  条件: {g : X -> Y} (h : f =ᶠ[𝓝 x] g)
  证明: by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]

Depends on / 依赖: ContinuousAt, eq_of_nhds, h.eq_of_nhds, tendsto_congr
-/
theorem continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]

/--
theorem `ContinuousAt.congr` / 定理 `ContinuousAt.congr`

English:
theorem ContinuousAt.congr
  given: {g : X -> Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g)
  proof: (continuousAt_congr h).1 hf

中文:
定理 ContinuousAt.congr
  条件: {g : X -> Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g)
  证明: (continuousAt_congr h).1 hf

Depends on / 依赖: continuousAt_congr
-/
theorem ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf

/--
theorem `ContinuousAt.preimage_mem_nhds` / 定理 `ContinuousAt.preimage_mem_nhds`

English:
theorem ContinuousAt.preimage_mem_nhds
  statement: {t : Set Y} (h : ContinuousAt f x)
  proof: h ht

中文:
定理 ContinuousAt.preimage_mem_nhds
  结论: {t : 集合 Y} (h : ContinuousAt f x)
  证明: h ht
-/
theorem ContinuousAt.preimage_mem_nhds {t : Set Y} (h : ContinuousAt f x)
    (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x :=
  h ht

/--
theorem `ContinuousAt.eventually_mem` / 定理 `ContinuousAt.eventually_mem`

English:
theorem ContinuousAt.eventually_mem
  statement: {f : X -> Y} {x : X} (hf : ContinuousAt f x) {s : Set Y}
  proof: hf hs

中文:
定理 ContinuousAt.eventually_mem
  结论: {f : X -> Y} {x : X} (hf : ContinuousAt f x) {s : 集合 Y}
  证明: hf hs
-/
theorem ContinuousAt.eventually_mem {f : X -> Y} {x : X} (hf : ContinuousAt f x) {s : Set Y}
    (hs : s in 𝓝 (f x)) : forallᶠ y in 𝓝 x, f y in s :=
  hf hs

/--
lemma `not_continuousAt_of_tendsto` / 引理 `not_continuousAt_of_tendsto`

English:
lemma not_continuousAt_of_tendsto
  statement: {f : X -> Y} {l₁ : Filter X} {l₂ : Filter Y} {x : X}
  proof: fun cont =>
  (cont.mono_left hl₁).not_tendsto hl₂ hf

中文:
引理 not_continuousAt_of_tendsto
  结论: {f : X -> Y} {l₁ : 滤子 X} {l₂ : 滤子 Y} {x : X}
  证明: fun cont =>
  (cont.mono_left hl₁).not_tendsto hl₂ hf
-/
lemma not_continuousAt_of_tendsto {f : X -> Y} {l₁ : Filter X} {l₂ : Filter Y} {x : X}
    (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l₁ <= 𝓝 x) (hl₂ : Disjoint (𝓝 (f x)) l₂) :
    ¬ ContinuousAt f x := fun cont =>
  (cont.mono_left hl₁).not_tendsto hl₂ hf

/--
theorem `ClusterPt.map` / 定理 `ClusterPt.map`

English:
theorem ClusterPt.map
  statement: {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx)
  proof: (NeBot.map H f).mono hfc.tendsto.inf hf

中文:
定理 ClusterPt.map
  结论: {lx : 滤子 X} {ly : 滤子 Y} (H : ClusterPt x lx)
  证明: (NeBot.map H f).mono hfc.tendsto.inf hf

Depends on / 依赖: NeBot.map, hfc.tendsto.inf, tendsto
-/
theorem ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx)
    (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly :=
(NeBot.map H f).mono hfc.tendsto.inf hf

/--
theorem `preimage_interior_subset_interior_preimage` / 定理 `preimage_interior_subset_interior_preimage`

English:
theorem preimage_interior_subset_interior_preimage
  given: {t : Set Y} (hf : Continuous f)
  proof: interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)

中文:
定理 preimage_interior_subset_interior_preimage
  条件: {t : 集合 Y} (hf : 连续 f)
  证明: interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)

Depends on / 依赖: interior_maximal, interior_subset, isOpen_interior, isOpen_interior.preimage, preimage, preimage_mono
-/
theorem preimage_interior_subset_interior_preimage {t : Set Y} (hf : Continuous f) :
    f ⁻¹' interior t subseteq interior (f ⁻¹' t) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)

/--
theorem `continuous_iff_preimage_interior_subset_interior_preimage` / 定理 `continuous_iff_preimage_interior_subset_interior_preimage`

English:
theorem continuous_iff_preimage_interior_subset_interior_preimage
  proof: preimage_interior_subset_interior_preimage h
mpr h := ⟨fun s hs => subset_interior_iff_isOpen.mp by grw [← h, hs.interior_eq]⟩

@[continuity]

中文:
定理 continuous_iff_preimage_interior_subset_interior_preimage
  证明: preimage_interior_subset_interior_preimage h
mpr h := ⟨fun s hs => subset_interior_iff_isOpen.mp by grw [← h, hs.interior_eq]⟩

@[continuity]

Depends on / 依赖: preimage_interior_subset_interior_preimage
-/
theorem continuous_iff_preimage_interior_subset_interior_preimage :
    Continuous f ↔ forall s, f ⁻¹' (interior s) subseteq interior (f ⁻¹' s) where
  mp h s := preimage_interior_subset_interior_preimage h
mpr h := ⟨fun s hs => subset_interior_iff_isOpen.mp by grw [← h, hs.interior_eq]⟩

@[continuity]
/--
theorem `continuous_id` / 定理 `continuous_id`

English:
theorem continuous_id
  statement: Continuous (id : X -> X)
  proof: continuous_def.2 fun _ => id

中文:
定理 continuous_id
  结论: 连续 (id : X -> X)
  证明: continuous_def.2 fun _ => id
-/
theorem continuous_id : Continuous (id : X -> X) :=
  continuous_def.2 fun _ => id

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
/--
theorem `continuous_id'` / 定理 `continuous_id'`

English:
theorem continuous_id'
  statement: Continuous (fun (x : X) => x)
  proof: continuous_id

中文:
定理 continuous_id'
  结论: 连续 (fun (x : X) => x)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_id' : Continuous (fun (x : X) => x) := continuous_id

/--
theorem `Continuous.comp` / 定理 `Continuous.comp`

English:
theorem Continuous.comp
  given: {g : Y -> Z} (hg : Continuous g) (hf : Continuous f)
  proof: continuous_def.2 fun _ h => (h.preimage hg).preimage hf

中文:
定理 连续.comp
  条件: {g : Y -> Z} (hg : 连续 g) (hf : 连续 f)
  证明: continuous_def.2 fun _ h => (h.preimage hg).preimage hf

Depends on / 依赖: continuous_def, h.preimage, preimage
-/
theorem Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  continuous_def.2 fun _ h => (h.preimage hg).preimage hf

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
/--
theorem `Continuous.comp'` / 定理 `Continuous.comp'`

English:
theorem Continuous.comp'
  given: {g : Y -> Z} (hg : Continuous g) (hf : Continuous f)
  proof: hg.comp hf

@[fun_prop]

中文:
定理 连续.comp'
  条件: {g : Y -> Z} (hg : 连续 g) (hf : 连续 f)
  证明: hg.comp hf

@[fun_prop]

Depends on / 依赖: hg.comp
-/
theorem Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) := hg.comp hf

@[fun_prop]
/--
theorem `Continuous.iterate` / 定理 `Continuous.iterate`

English:
theorem Continuous.iterate
  given: {f : X -> X} (h : Continuous f) (n : Nat)
  statement: Continuous f^[n]
  proof: Nat.recOn n continuous_id fun _ ihn => ihn.comp h

nonrec theorem ContinuousAt.comp {g : Y -> Z} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

@[fun_prop]

中文:
定理 连续.iterate
  条件: {f : X -> X} (h : 连续 f) (n : 自然数)
  结论: 连续 f^[n]
  证明: Nat.recOn n continuous_id fun _ ihn => ihn.comp h

nonrec theorem ContinuousAt.comp {g : Y -> Z} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

@[fun_prop]

Depends on / 依赖: Nat.recOn, continuous_id, ihn.comp
-/
theorem Continuous.iterate {f : X -> X} (h : Continuous f) (n : Nat) : Continuous f^[n] :=
  Nat.recOn n continuous_id fun _ ihn => ihn.comp h

nonrec theorem ContinuousAt.comp {g : Y -> Z} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

@[fun_prop]
/--
theorem `ContinuousAt.comp'` / 定理 `ContinuousAt.comp'`

English:
theorem ContinuousAt.comp'
  statement: {g : Y -> Z} {x : X} (hg : ContinuousAt g (f x))
  proof: ContinuousAt.comp hg hf

中文:
定理 ContinuousAt.comp'
  结论: {g : Y -> Z} {x : X} (hg : ContinuousAt g (f x))
  证明: ContinuousAt.comp hg hf

Depends on / 依赖: ContinuousAt, ContinuousAt.comp
-/
theorem ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x := ContinuousAt.comp hg hf

/--
theorem `ContinuousAt.comp_of_eq` / 定理 `ContinuousAt.comp_of_eq`

English:
theorem ContinuousAt.comp_of_eq
  statement: {g : Y -> Z} (hg : ContinuousAt g y)
  proof: by subst hy; exact hg.comp hf

中文:
定理 ContinuousAt.comp_of_eq
  结论: {g : Y -> Z} (hg : ContinuousAt g y)
  证明: by subst hy; exact hg.comp hf

Depends on / 依赖: hg.comp
-/
theorem ContinuousAt.comp_of_eq {g : Y -> Z} (hg : ContinuousAt g y)
    (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x := by subst hy; exact hg.comp hf

/--
theorem `Continuous.tendsto` / 定理 `Continuous.tendsto`

English:
theorem Continuous.tendsto
  given: (hf : Continuous f) (x)
  statement: Tendsto f (𝓝 x) (𝓝 (f x))
  proof: ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩

中文:
定理 连续.tendsto
  条件: (hf : 连续 f) (x)
  结论: 收敛 f (𝓝 x) (𝓝 (f x))
  证明: ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, ht.preimage, nhds_basis_opens, preimage, tendsto_iff
-/
theorem Continuous.tendsto (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩

/--
theorem `Continuous.tendsto'` / 定理 `Continuous.tendsto'`

English:
theorem Continuous.tendsto'
  given: (hf : Continuous f) (x : X) (y : Y) (h : f x = y)
  proof: h ▸ hf.tendsto x

@[fun_prop]

中文:
定理 连续.tendsto'
  条件: (hf : 连续 f) (x : X) (y : Y) (h : f x = y)
  证明: h ▸ hf.tendsto x

@[fun_prop]

Depends on / 依赖: hf.tendsto, tendsto
-/
theorem Continuous.tendsto' (hf : Continuous f) (x : X) (y : Y) (h : f x = y) :
    Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.tendsto x

@[fun_prop]
/--
theorem `Continuous.continuousAt` / 定理 `Continuous.continuousAt`

English:
theorem Continuous.continuousAt
  given: (h : Continuous f)
  statement: ContinuousAt f x
  proof: h.tendsto x

中文:
定理 连续.continuousAt
  条件: (h : 连续 f)
  结论: ContinuousAt f x
  证明: h.tendsto x

Depends on / 依赖: h.tendsto, tendsto
-/
theorem Continuous.continuousAt (h : Continuous f) : ContinuousAt f x :=
  h.tendsto x

/--
theorem `continuous_iff_continuousAt` / 定理 `continuous_iff_continuousAt`

English:
theorem continuous_iff_continuousAt
  statement: Continuous f ↔ forall x, ContinuousAt f x
  proof: ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
hf x hU.mem_nhds hx⟩

@[fun_prop]

中文:
定理 continuous_iff_continuousAt
  结论: 连续 f ↔ 对任意 x, ContinuousAt f x
  证明: ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
hf x hU.mem_nhds hx⟩

@[fun_prop]

Depends on / 依赖: Continuous, Continuous.tendsto, continuous_def, hU.mem_nhds, isOpen_iff_mem_nhds, mem_nhds, tendsto
-/
theorem continuous_iff_continuousAt : Continuous f ↔ forall x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
hf x hU.mem_nhds hx⟩

@[fun_prop]
/--
theorem `continuousAt_const` / 定理 `continuousAt_const`

English:
theorem continuousAt_const
  statement: ContinuousAt (fun _ : X => y) x
  proof: tendsto_const_nhds

@[continuity, fun_prop]

中文:
定理 continuousAt_const
  结论: ContinuousAt (fun _ : X => y) x
  证明: tendsto_const_nhds

@[continuity, fun_prop]

Depends on / 依赖: tendsto_const_nhds
-/
theorem continuousAt_const : ContinuousAt (fun _ : X => y) x :=
  tendsto_const_nhds

@[continuity, fun_prop]
/--
theorem `continuous_const` / 定理 `continuous_const`

English:
theorem continuous_const
  statement: Continuous fun _ : X => y
  proof: continuous_iff_continuousAt.mpr fun _ => continuousAt_const

中文:
定理 continuous_const
  结论: 连续 fun _ : X => y
  证明: continuous_iff_continuousAt.mpr fun _ => continuousAt_const
-/
theorem continuous_const : Continuous fun _ : X => y :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_const

/--
theorem `Filter.EventuallyEq.continuousAt` / 定理 `Filter.EventuallyEq.continuousAt`

English:
theorem Filter.EventuallyEq.continuousAt
  given: (h : f =ᶠ[𝓝 x] fun _ => y)
  proof: (continuousAt_congr h).2 tendsto_const_nhds

中文:
定理 滤子.EventuallyEq.continuousAt
  条件: (h : f =ᶠ[𝓝 x] fun _ => y)
  证明: (continuousAt_congr h).2 tendsto_const_nhds

Depends on / 依赖: continuousAt_congr, tendsto_const_nhds
-/
theorem Filter.EventuallyEq.continuousAt (h : f =ᶠ[𝓝 x] fun _ => y) :
    ContinuousAt f x :=
  (continuousAt_congr h).2 tendsto_const_nhds

/--
theorem `continuous_of_const` / 定理 `continuous_of_const`

English:
theorem continuous_of_const
  given: (h : forall x y, f x = f y)
  statement: Continuous f
  proof: continuous_iff_continuousAt.mpr fun x =>
Filter.EventuallyEq.continuousAt Eventually.of_forall fun y => h y x

中文:
定理 continuous_of_const
  条件: (h : 对任意 x y, f x = f y)
  结论: 连续 f
  证明: continuous_iff_continuousAt.mpr fun x =>
Filter.EventuallyEq.continuousAt Eventually.of_forall fun y => h y x

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyEq, Filter, Filter.EventuallyEq.continuousAt, continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, of_forall
-/
theorem continuous_of_const (h : forall x y, f x = f y) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
Filter.EventuallyEq.continuousAt Eventually.of_forall fun y => h y x

/--
theorem `continuousAt_id` / 定理 `continuousAt_id`

English:
theorem continuousAt_id
  statement: ContinuousAt id x
  proof: continuous_id.continuousAt

@[fun_prop]

中文:
定理 continuousAt_id
  结论: ContinuousAt id x
  证明: continuous_id.continuousAt

@[fun_prop]

Depends on / 依赖: continuousAt, continuous_id, continuous_id.continuousAt
-/
theorem continuousAt_id : ContinuousAt id x :=
  continuous_id.continuousAt

@[fun_prop]
/--
theorem `continuousAt_id'` / 定理 `continuousAt_id'`

English:
theorem continuousAt_id'
  given: (y)
  statement: ContinuousAt (fun x : X => x) y
  proof: continuousAt_id

中文:
定理 continuousAt_id'
  条件: (y)
  结论: ContinuousAt (fun x : X => x) y
  证明: continuousAt_id

Depends on / 依赖: continuousAt_id
-/
theorem continuousAt_id' (y) : ContinuousAt (fun x : X => x) y := continuousAt_id

/--
theorem `ContinuousAt.iterate` / 定理 `ContinuousAt.iterate`

English:
theorem ContinuousAt.iterate
  given: {f : X -> X} (hf : ContinuousAt f x) (hx : f x = x) (n : Nat)
  proof: Nat.recOn n continuousAt_id fun _n ihn => ihn.comp_of_eq hf hx

中文:
定理 ContinuousAt.iterate
  条件: {f : X -> X} (hf : ContinuousAt f x) (hx : f x = x) (n : 自然数)
  证明: Nat.recOn n continuousAt_id fun _n ihn => ihn.comp_of_eq hf hx

Depends on / 依赖: Nat.recOn, comp_of_eq, continuousAt_id, ihn.comp_of_eq
-/
theorem ContinuousAt.iterate {f : X -> X} (hf : ContinuousAt f x) (hx : f x = x) (n : Nat) :
    ContinuousAt f^[n] x :=
  Nat.recOn n continuousAt_id fun _n ihn => ihn.comp_of_eq hf hx

/--
theorem `continuous_iff_isClosed` / 定理 `continuous_iff_isClosed`

English:
theorem continuous_iff_isClosed
  statement: Continuous f ↔ forall s, IsClosed s -> IsClosed (f ⁻¹' s)
  proof: continuous_def.trans compl_surjective.forall.trans by
    simp only [isOpen_compl_iff, preimage_compl]

中文:
定理 continuous_iff_isClosed
  结论: 连续 f ↔ 对任意 s, 是闭集 s -> 是闭集 (f ⁻¹' s)
  证明: continuous_def.trans compl_surjective.forall.trans by
    simp only [isOpen_compl_iff, preimage_compl]

Depends on / 依赖: compl_surjective, compl_surjective.forall.trans, continuous_def, continuous_def.trans, isOpen_compl_iff, preimage_compl
-/
theorem continuous_iff_isClosed : Continuous f ↔ forall s, IsClosed s -> IsClosed (f ⁻¹' s) :=
continuous_def.trans compl_surjective.forall.trans by
    simp only [isOpen_compl_iff, preimage_compl]

/--
theorem `IsClosed.preimage` / 定理 `IsClosed.preimage`

English:
theorem IsClosed.preimage
  given: (hf : Continuous f) {t : Set Y} (h : IsClosed t)
  proof: continuous_iff_isClosed.mp hf t h

中文:
定理 是闭集.原像
  条件: (hf : 连续 f) {t : 集合 Y} (h : 是闭集 t)
  证明: continuous_iff_isClosed.mp hf t h

Depends on / 依赖: continuous_iff_isClosed, continuous_iff_isClosed.mp
-/
theorem IsClosed.preimage (hf : Continuous f) {t : Set Y} (h : IsClosed t) :
    IsClosed (f ⁻¹' t) :=
  continuous_iff_isClosed.mp hf t h

/--
theorem `mem_closure_image` / 定理 `mem_closure_image`

English:
theorem mem_closure_image
  statement: (hf : ContinuousAt f x)
  proof: mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf

中文:
定理 mem_closure_image
  结论: (hf : ContinuousAt f x)
  证明: mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf

Depends on / 依赖: mem_closure_iff_frequently, mem_closure_of_frequently_of_tendsto, mem_image_of_mem
-/
theorem mem_closure_image (hf : ContinuousAt f x)
    (hx : x in closure s) : f x in closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf

/--
theorem `Continuous.closure_preimage_subset` / 定理 `Continuous.closure_preimage_subset`

English:
theorem Continuous.closure_preimage_subset
  given: (hf : Continuous f) (t : Set Y)
  proof: by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)

中文:
定理 连续.closure_preimage_subset
  条件: (hf : 连续 f) (t : 集合 Y)
  证明: by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)

Depends on / 依赖: closure_eq, closure_mono, isClosed_closure, isClosed_closure.preimage, preimage, preimage_mono, subset_closure
-/
theorem Continuous.closure_preimage_subset (hf : Continuous f) (t : Set Y) :
    closure (f ⁻¹' t) subseteq f ⁻¹' closure t := by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)

/--
theorem `Continuous.frontier_preimage_subset` / 定理 `Continuous.frontier_preimage_subset`

English:
theorem Continuous.frontier_preimage_subset
  given: (hf : Continuous f) (t : Set Y)
  proof: sdiff_subset_sdiff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

中文:
定理 连续.frontier_preimage_subset
  条件: (hf : 连续 f) (t : 集合 Y)
  证明: sdiff_subset_sdiff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

Depends on / 依赖: closure_preimage_subset, hf.closure_preimage_subset, preimage_interior_subset_interior_preimage, sdiff_subset_sdiff
-/
theorem Continuous.frontier_preimage_subset (hf : Continuous f) (t : Set Y) :
    frontier (f ⁻¹' t) subseteq f ⁻¹' frontier t :=
  sdiff_subset_sdiff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

/--
theorem `Set.MapsTo.closure` / 定理 `Set.MapsTo.closure`

English:
theorem Set.MapsTo.closure
  statement: {t : Set Y} (h : MapsTo f s t)
  proof: by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)

中文:
定理 集合.映射到.closure
  结论: {t : 集合 Y} (h : 映射到 f s t)
  证明: by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)
-/
protected theorem Set.MapsTo.closure {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) : MapsTo f (closure s) (closure t) := by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)

/--
theorem `image_closure_subset_closure_image` / 定理 `image_closure_subset_closure_image`

English:
theorem image_closure_subset_closure_image
  given: (h : Continuous f)
  proof: ((mapsTo_image f s).closure h).image_subset

中文:
定理 image_closure_subset_closure_image
  条件: (h : 连续 f)
  证明: ((mapsTo_image f s).closure h).image_subset

Depends on / 依赖: closure, image_subset, mapsTo_image
-/
theorem image_closure_subset_closure_image (h : Continuous f) :
    f '' closure s subseteq closure (f '' s) :=
  ((mapsTo_image f s).closure h).image_subset

/--
theorem `closure_image_closure` / 定理 `closure_image_closure`

English:
theorem closure_image_closure
  given: (h : Continuous f)
  proof: Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_mono subset_closure)

中文:
定理 closure_image_closure
  条件: (h : 连续 f)
  证明: Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_mono subset_closure)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, closure_minimal, closure_mono, image_closure_subset_closure_image, image_mono, isClosed_closure, subset_closure
-/
theorem closure_image_closure (h : Continuous f) :
    closure (f '' closure s) = closure (f '' s) :=
  Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_mono subset_closure)

/--
theorem `closure_subset_preimage_closure_image` / 定理 `closure_subset_preimage_closure_image`

English:
theorem closure_subset_preimage_closure_image
  given: (h : Continuous f)
  proof: (mapsTo_image _ _).closure h

中文:
定理 closure_subset_preimage_closure_image
  条件: (h : 连续 f)
  证明: (mapsTo_image _ _).closure h

Depends on / 依赖: closure, mapsTo_image
-/
theorem closure_subset_preimage_closure_image (h : Continuous f) :
    closure s subseteq f ⁻¹' closure (f '' s) :=
  (mapsTo_image _ _).closure h

/--
lemma `nonempty_preimage_closure_image` / 引理 `nonempty_preimage_closure_image`

English:
lemma nonempty_preimage_closure_image
  given: (h : Continuous f) (t : Set X) (ht : t.Nonempty)
  proof: (Nonempty.mono (closure_subset_preimage_closure_image h (s := t)) (closure_nonempty_iff.mpr ht))

中文:
引理 nonempty_preimage_closure_image
  条件: (h : 连续 f) (t : 集合 X) (ht : t.非空)
  证明: (Nonempty.mono (closure_subset_preimage_closure_image h (s := t)) (closure_nonempty_iff.mpr ht))

Depends on / 依赖: Nonempty, Nonempty.mono, closure_nonempty_iff, closure_nonempty_iff.mpr, closure_subset_preimage_closure_image
-/
lemma nonempty_preimage_closure_image (h : Continuous f) (t : Set X) (ht : t.Nonempty) :
    (f ⁻¹' (closure (f '' t))).Nonempty :=
  (Nonempty.mono (closure_subset_preimage_closure_image h (s := t)) (closure_nonempty_iff.mpr ht))

/--
theorem `continuous_iff_image_closure_subset_closure_image` / 定理 `continuous_iff_image_closure_subset_closure_image`

English:
theorem continuous_iff_image_closure_subset_closure_image
  proof: image_closure_subset_closure_image h
mpr h := continuous_iff_isClosed.mpr fun s hs => isClosed_of_closure_subset by
    grw [image_subset_iff.mp <| h <| f ⁻¹' s, image_preimage_subset, hs.closure_subset]

中文:
定理 continuous_iff_image_closure_subset_closure_image
  证明: image_closure_subset_closure_image h
mpr h := continuous_iff_isClosed.mpr fun s hs => isClosed_of_closure_subset by
    grw [image_subset_iff.mp <| h <| f ⁻¹' s, image_preimage_subset, hs.closure_subset]

Depends on / 依赖: image_closure_subset_closure_image
-/
theorem continuous_iff_image_closure_subset_closure_image :
    Continuous f ↔ forall s, f '' closure s subseteq closure (f '' s) where
  mp h s := image_closure_subset_closure_image h
mpr h := continuous_iff_isClosed.mpr fun s hs => isClosed_of_closure_subset by
    grw [image_subset_iff.mp <| h <| f ⁻¹' s, image_preimage_subset, hs.closure_subset]

/--
theorem `map_mem_closure` / 定理 `map_mem_closure`

English:
theorem map_mem_closure
  statement: {t : Set Y} (hf : Continuous f)
  proof: ht.closure hf hx

中文:
定理 map_mem_closure
  结论: {t : 集合 Y} (hf : 连续 f)
  证明: ht.closure hf hx

Depends on / 依赖: closure, ht.closure
-/
theorem map_mem_closure {t : Set Y} (hf : Continuous f)
    (hx : x in closure s) (ht : MapsTo f s t) : f x in closure t :=
  ht.closure hf hx

/--
theorem `Set.MapsTo.closure_left` / 定理 `Set.MapsTo.closure_left`

English:
theorem Set.MapsTo.closure_left
  statement: {t : Set Y} (h : MapsTo f s t)
  proof: ht.closure_eq ▸ h.closure hc

中文:
定理 集合.映射到.closure_left
  结论: {t : 集合 Y} (h : 映射到 f s t)
  证明: ht.closure_eq ▸ h.closure hc

Depends on / 依赖: closure, closure_eq, h.closure, ht.closure_eq
-/
theorem Set.MapsTo.closure_left {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) (ht : IsClosed t) : MapsTo f (closure s) t :=
  ht.closure_eq ▸ h.closure hc

/--
theorem `Filter.Tendsto.lift'_closure` / 定理 `Filter.Tendsto.lift'_closure`

English:
theorem Filter.Tendsto.lift'_closure
  given: (hf : Continuous f) {l l'} (h : Tendsto f l l')
  proof: tendsto_lift'.2 fun s hs => by
    filter_upwards [mem_lift' (h hs)] using (mapsTo_preimage _ _).closure hf

中文:
定理 滤子.收敛.lift'_closure
  条件: (hf : 连续 f) {l l'} (h : 收敛 f l l')
  证明: tendsto_lift'.2 fun s hs => by
    filter_upwards [mem_lift' (h hs)] using (mapsTo_preimage _ _).closure hf

Depends on / 依赖: closure, filter_upwards, mapsTo_preimage, mem_lift, tendsto_lift
-/
theorem Filter.Tendsto.lift'_closure (hf : Continuous f) {l l'} (h : Tendsto f l l') :
    Tendsto f (l.lift' closure) (l'.lift' closure) :=
  tendsto_lift'.2 fun s hs => by
    filter_upwards [mem_lift' (h hs)] using (mapsTo_preimage _ _).closure hf

/--
theorem `tendsto_lift'_closure_nhds` / 定理 `tendsto_lift'_closure_nhds`

English:
theorem tendsto_lift'_closure_nhds
  given: (hf : Continuous f) (x : X)
  proof: (hf.tendsto x).lift'_closure hf

中文:
定理 tendsto_lift'_closure_nhds
  条件: (hf : 连续 f) (x : X)
  证明: (hf.tendsto x).lift'_closure hf

Depends on / 依赖: _closure, hf.tendsto, tendsto
-/
theorem tendsto_lift'_closure_nhds (hf : Continuous f) (x : X) :
    Tendsto f ((𝓝 x).lift' closure) ((𝓝 (f x)).lift' closure) :=
  (hf.tendsto x).lift'_closure hf

/-!
### Function with dense range
-/

section DenseRange

variable {α ι : Type*} (f : α -> X) (g : X -> Y)
variable {f : α -> X} {s : Set X}

/--
theorem `Function.Surjective.denseRange` / 定理 `Function.Surjective.denseRange`

English:
theorem Function.Surjective.denseRange
  given: (hf : Function.Surjective f)
  statement: DenseRange f
  proof: fun x => by
  simp [hf.range_eq]

中文:
定理 函数.满射.denseRange
  条件: (hf : 函数.满射 f)
  结论: DenseRange f
  证明: fun x => by
  simp [hf.range_eq]

Depends on / 依赖: hf.range_eq, range_eq
-/
theorem Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [hf.range_eq]

/--
theorem `denseRange_id` / 定理 `denseRange_id`

English:
theorem denseRange_id
  statement: DenseRange (id : X -> X)
  proof: Function.Surjective.denseRange Function.surjective_id

中文:
定理 denseRange_id
  结论: DenseRange (id : X -> X)
  证明: Function.Surjective.denseRange Function.surjective_id

Depends on / 依赖: Function, Function.Surjective.denseRange, Function.surjective_id, Surjective, denseRange, surjective_id
-/
theorem denseRange_id : DenseRange (id : X -> X) :=
  Function.Surjective.denseRange Function.surjective_id

/--
theorem `denseRange_iff_closure_range` / 定理 `denseRange_iff_closure_range`

English:
theorem denseRange_iff_closure_range
  statement: DenseRange f ↔ closure (range f) = univ
  proof: dense_iff_closure_eq

中文:
定理 denseRange_iff_closure_range
  结论: DenseRange f ↔ closure (range f) = univ
  证明: dense_iff_closure_eq

Depends on / 依赖: dense_iff_closure_eq
-/
theorem denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ :=
  dense_iff_closure_eq

/--
theorem `DenseRange.closure_range` / 定理 `DenseRange.closure_range`

English:
theorem DenseRange.closure_range
  given: (h : DenseRange f)
  statement: closure (range f) = univ
  proof: h.closure_eq

@[simp]

中文:
定理 DenseRange.closure_range
  条件: (h : DenseRange f)
  结论: closure (range f) = univ
  证明: h.closure_eq

@[simp]

Depends on / 依赖: closure_eq, h.closure_eq
-/
theorem DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ :=
  h.closure_eq

@[simp]
/--
lemma `denseRange_subtype_val` / 引理 `denseRange_subtype_val`

English:
lemma denseRange_subtype_val
  given: {p : X -> Prop}
  statement: DenseRange (@Subtype.val _ p) ↔ Dense {x | p x}
  proof: by
  simp [DenseRange]

中文:
引理 denseRange_subtype_val
  条件: {p : X -> 命题}
  结论: DenseRange (@子类型.val _ p) ↔ 稠密 {x | p x}
  证明: by
  simp [DenseRange]

Depends on / 依赖: DenseRange
-/
lemma denseRange_subtype_val {p : X -> Prop} : DenseRange (@Subtype.val _ p) ↔ Dense {x | p x} := by
  simp [DenseRange]

/--
theorem `Dense.denseRange_val` / 定理 `Dense.denseRange_val`

English:
theorem Dense.denseRange_val
  given: (h : Dense s)
  statement: DenseRange ((↑) : s -> X)
  proof: denseRange_subtype_val.2 h

中文:
定理 稠密.denseRange_val
  条件: (h : 稠密 s)
  结论: DenseRange ((↑) : s -> X)
  证明: denseRange_subtype_val.2 h

Depends on / 依赖: denseRange_subtype_val
-/
theorem Dense.denseRange_val (h : Dense s) : DenseRange ((↑) : s -> X) :=
  denseRange_subtype_val.2 h

/--
theorem `Continuous.range_subset_closure_image_dense` / 定理 `Continuous.range_subset_closure_image_dense`

English:
theorem Continuous.range_subset_closure_image_dense
  statement: {f : X -> Y} (hf : Continuous f)
  proof: by
  rw [← image_univ]; rw [← hs.closure_eq]
  exact image_closure_subset_closure_image hf

中文:
定理 连续.range_subset_closure_image_dense
  结论: {f : X -> Y} (hf : 连续 f)
  证明: by
  rw [← image_univ]; rw [← hs.closure_eq]
  exact image_closure_subset_closure_image hf

Depends on / 依赖: closure_eq, hs.closure_eq, image_closure_subset_closure_image, image_univ
-/
theorem Continuous.range_subset_closure_image_dense {f : X -> Y} (hf : Continuous f)
    (hs : Dense s) : range f subseteq closure (f '' s) := by
  rw [← image_univ]; rw [← hs.closure_eq]
  exact image_closure_subset_closure_image hf

/--
theorem `DenseRange.dense_image` / 定理 `DenseRange.dense_image`

English:
theorem DenseRange.dense_image
  statement: {f : X -> Y} (hf' : DenseRange f) (hf : Continuous f)
  proof: (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

中文:
定理 DenseRange.dense_image
  结论: {f : X -> Y} (hf' : DenseRange f) (hf : 连续 f)
  证明: (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

Depends on / 依赖: hf.range_subset_closure_image_dense, of_closure, range_subset_closure_image_dense
-/
theorem DenseRange.dense_image {f : X -> Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) : Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

/--
theorem `DenseRange.subset_closure_image_preimage_of_isOpen` / 定理 `DenseRange.subset_closure_image_preimage_of_isOpen`

English:
theorem DenseRange.subset_closure_image_preimage_of_isOpen
  given: (hf : DenseRange f) (hs : IsOpen s)
  proof: by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

中文:
定理 DenseRange.subset_closure_image_preimage_of_isOpen
  条件: (hf : DenseRange f) (hs : 是开集 s)
  证明: by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

Depends on / 依赖: hf.open_subset_closure_inter, image_preimage_eq_inter_range, open_subset_closure_inter
-/
theorem DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) (hs : IsOpen s) :
    s subseteq closure (f '' f ⁻¹' s) := by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

/--
theorem `DenseRange.dense_of_mapsTo` / 定理 `DenseRange.dense_of_mapsTo`

English:
theorem DenseRange.dense_of_mapsTo
  statement: {f : X -> Y} (hf' : DenseRange f) (hf : Continuous f)
  proof: (hf'.dense_image hf hs).mono ht.image_subset

中文:
定理 DenseRange.dense_of_mapsTo
  结论: {f : X -> Y} (hf' : DenseRange f) (hf : 连续 f)
  证明: (hf'.dense_image hf hs).mono ht.image_subset

Depends on / 依赖: dense_image, ht.image_subset, image_subset
-/
theorem DenseRange.dense_of_mapsTo {f : X -> Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) {t : Set Y} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset

/--
theorem `DenseRange.comp` / 定理 `DenseRange.comp`

English:
theorem DenseRange.comp
  statement: {g : Y -> Z} {f : α -> Y} (hg : DenseRange g) (hf : DenseRange f)
  proof: by
  rw [DenseRange]; rw [range_comp]
  exact hg.dense_image cg hf

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty α ↔ Nonempty X :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

中文:
定理 DenseRange.comp
  结论: {g : Y -> Z} {f : α -> Y} (hg : DenseRange g) (hf : DenseRange f)
  证明: by
  rw [DenseRange]; rw [range_comp]
  exact hg.dense_image cg hf

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty α ↔ Nonempty X :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

Depends on / 依赖: DenseRange, dense_image, hg.dense_image, range_comp
-/
theorem DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRange g) (hf : DenseRange f)
    (cg : Continuous g) : DenseRange (g ∘ f) := by
  rw [DenseRange]; rw [range_comp]
  exact hg.dense_image cg hf

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty α ↔ Nonempty X :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

/--
theorem `DenseRange.nonempty` / 定理 `DenseRange.nonempty`

English:
theorem DenseRange.nonempty
  given: [h : Nonempty X] (hf : DenseRange f)
  statement: Nonempty α
  proof: hf.nonempty_iff.mpr h

中文:
定理 DenseRange.nonempty
  条件: [h : 非空 X] (hf : DenseRange f)
  结论: 非空 α
  证明: hf.nonempty_iff.mpr h

Depends on / 依赖: hf.nonempty_iff.mpr, nonempty_iff
-/
theorem DenseRange.nonempty [h : Nonempty X] (hf : DenseRange f) : Nonempty α :=
  hf.nonempty_iff.mpr h

/--
Definition of `DenseRange.some` / `DenseRange.some` 的定义

English:
definition DenseRange.some
  signature: (hf : DenseRange f) (x : X)
  body: Classical.choice hf.nonempty_iff.mpr ⟨x⟩

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) (ho : IsOpen s) (hs : s.Nonempty) :
    exists a, f a in s :=
exists_range_iff.1 hf.exists_mem_open ho hs

中文:
定义 DenseRange.some
  签名: (hf : DenseRange f) (x : X)
  定义体: Classical.choice hf.nonempty_iff.mpr ⟨x⟩

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) (ho : IsOpen s) (hs : s.Nonempty) :
    exists a, f a in s :=
exists_range_iff.1 hf.exists_mem_open ho hs

Depends on / 依赖: Classical, Classical.choice, choice, hf.nonempty_iff.mpr, nonempty_iff
-/
noncomputable def DenseRange.some (hf : DenseRange f) (x : X) : α :=
Classical.choice hf.nonempty_iff.mpr ⟨x⟩

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) (ho : IsOpen s) (hs : s.Nonempty) :
    exists a, f a in s :=
exists_range_iff.1 hf.exists_mem_open ho hs

/--
theorem `DenseRange.mem_nhds` / 定理 `DenseRange.mem_nhds`

English:
theorem DenseRange.mem_nhds
  given: (h : DenseRange f) (hs : s in 𝓝 x)
  proof: let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨x, mem_interior_iff_mem_nhds.2 hs⟩
  ⟨a, interior_subset ha⟩

中文:
定理 DenseRange.mem_nhds
  条件: (h : DenseRange f) (hs : s in 𝓝 x)
  证明: let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨x, mem_interior_iff_mem_nhds.2 hs⟩
  ⟨a, interior_subset ha⟩

Depends on / 依赖: exists_mem_open, h.exists_mem_open, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds
-/
theorem DenseRange.mem_nhds (h : DenseRange f) (hs : s in 𝓝 x) :
    exists a, f a in s :=
  let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨x, mem_interior_iff_mem_nhds.2 hs⟩
  ⟨a, interior_subset ha⟩

end DenseRange

library_note «continuity lemma statement» /--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`Measurable`, `Differentiable`, `ContinuousOn`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `Continuous (fun p ↦ p.1 + p.2)`;
* `Continuous (Function.uncurry (+))`;
* `Continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following example fails, because of limitations in the
  elaboration process.
  ```
  variable {M : Type*} [Add M] [TopologicalSpace M] [ContinuousAdd M]
  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp _

  -- This example used to fail, but would be accepted if you wrote is as
  -- `continuous_add.comp (continuous_id.prodMk continuous_id :)`.
  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp (continuous_id.prodMk continuous_id)
  ```

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way

A much more convenient way to write continuity lemmas is like `Continuous.add`:
```
Continuous.add {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
  Continuous (f + g)
```
The conclusion can be `Continuous (fun x ↦ f x + g x)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `Continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.
  (Having a domain `Y × Z` would be less convenient in general.)

As an example for a unary operation, we have `Continuous.neg`.
```
Continuous.neg {f : X → G} (hf : Continuous f) : Continuous (-f)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp <| continuous_neg.comp <| continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
/--
Definition of `strans` / `strans` 的定义

English:
definition strans
  signature: {x : F} (γ γ' : Path x x) (t₀ : I)

中文:
定义 strans
  签名: {x : F} (γ γ' : 道路 x x) (t₀ : I)
-/
def strans {x : F} (γ γ' : Path x x) (t₀ : I) : Path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, Path (f x) (f x)} {t₀ s : X → I}
  (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
  (ht : Continuous t₀) (hs : Continuous s) :
  Continuous (fun x ↦ strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `Path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `Function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `Int.fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
/--
lemma `ContinuousOn.comp_fract` / 引理 `ContinuousOn.comp_fract`

English:
lemma ContinuousOn.comp_fract
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/

中文:
引理 ContinuousOn.comp_fract
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  证明: -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/
-/
lemma ContinuousOn.comp_fract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ → Y} {g : X → ℝ} (hf : Continuous ↿f) (hg : Continuous g) (h : ∀ s, f s 0 = f s 1) :
    Continuous (fun x ↦ f x (fract (g x)))
```
With `ContinuousAt` you can be even more precise about what to prove in case of discontinuities,
see e.g. `ContinuousAt.comp_div_cases`.
-/

library_note «comp_of_eq lemmas» /--
Lean's elaborator has trouble elaborating applications of lemmas that state that the composition of
two functions satisfy some property at a point, like `ContinuousAt.comp` / `ContDiffAt.comp` and
`ContMDiffWithinAt.comp`. The reason is that a lemma like this looks like
`ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f) x`.
Since Lean's elaborator elaborates the arguments from left-to-right, when you write `hg.comp hf`,
the elaborator will try to figure out *both* `f` and `g` from the type of `hg`. It tries to figure
out `f` just from the point where `g` is continuous. For example, if `hg : ContinuousAt g (a, x)`
then the elaborator will assign `f` to the function `Prod.mk a`, since in that case `f x = (a, x)`.
This is undesirable in most cases where `f` is not a variable. There are some ways to work around
this, for example by giving `f` explicitly, or to force Lean to elaborate `hf` before elaborating
`hg`, but this is annoying.
Another better solution is to reformulate composition lemmas to have the following shape
`ContinuousAt g y → ContinuousAt f x → f x = y → ContinuousAt (g ∘ f) x`.
This is even useful if the proof of `f x = y` is `rfl`.
The reason that this works better is because the type of `hg` doesn't mention `f`.
Only after elaborating the two `ContinuousAt` arguments, Lean will try to unify `f x` with `y`,
which is often easy after having chosen the correct functions for `f` and `g`.
Here is an example that shows the difference:
```
example [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X} (f : X → X → Y)
    (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
    ContinuousAt (fun x ↦ f x x) x₀ :=
  -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/
