/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.Bases.Basic

/-!
# Lift filters along filter and set functions
-/

assert_not_exists Set.Finite

public section

open Set Filter Function

namespace Filter

variable {α β γ : Type*} {ι : Sort*}

section lift

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α -> Filter β}

@[simp]
/--
theorem `lift_top` / 定理 `lift_top`

English:
theorem lift_top
  given: (g : Set α -> Filter β)
  statement: (⊤ : Filter α).lift g = g univ
  proof: by simp [Filter.lift]

中文:
定理 lift_top
  条件: (g : 集合 α -> 滤子 β)
  结论: (⊤ : 滤子 α).lift g = g univ
  证明: by simp [Filter.lift]

Depends on / 依赖: Filter, Filter.lift
-/
theorem lift_top (g : Set α -> Filter β) : (⊤ : Filter α).lift g = g univ := by simp [Filter.lift]

/--
theorem `HasBasis.mem_lift_iff` / 定理 `HasBasis.mem_lift_iff`

English:
theorem HasBasis.mem_lift_iff
  statement: {ι} {p : ι -> Prop} {s : ι -> Set α} {f : Filter α}
  proof: by
  refine (mem_biInf_of_directed ?_ ⟨univ, univ_sets _⟩).trans ?_
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ inter t₂, inter_mem ht₁ ht₂, gm inter_subset_left, gm inter_subset_right⟩
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H

中文:
定理 有基.mem_lift_iff
  结论: {ι} {p : ι -> 命题} {s : ι -> 集合 α} {f : 滤子 α}
  证明: by
  refine (mem_biInf_of_directed ?_ ⟨univ, univ_sets _⟩).trans ?_
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ inter t₂, inter_mem ht₁ ht₂, gm inter_subset_left, gm inter_subset_right⟩
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H

Depends on / 依赖: exists_iff, hf.exists_iff, inter_mem, inter_subset_left, inter_subset_right, mem_biInf_of_directed, mem_iff, univ_sets
-/
theorem HasBasis.mem_lift_iff {ι} {p : ι -> Prop} {s : ι -> Set α} {f : Filter α}
    (hf : f.HasBasis p s) {β : ι -> Type*} {pg : forall i, β i -> Prop} {sg : forall i, β i -> Set γ}
    {g : Set α -> Filter γ} (hg : forall i, (g <| s i).HasBasis (pg i) (sg i)) (gm : Monotone g)
    {s : Set γ} : s in f.lift g ↔ exists i, p i ∧ exists x, pg i x ∧ sg i x subseteq s := by
  refine (mem_biInf_of_directed ?_ ⟨univ, univ_sets _⟩).trans ?_
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ inter t₂, inter_mem ht₁ ht₂, gm inter_subset_left, gm inter_subset_right⟩
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H

/--
theorem `HasBasis.lift` / 定理 `HasBasis.lift`

English:
theorem HasBasis.lift
  statement: {ι} {p : ι -> Prop} {s : ι -> Set α} {f : Filter α} (hf : f.HasBasis p s)
  proof: by
  refine ⟨fun t => (hf.mem_lift_iff hg gm).trans ?_⟩
  simp [Sigma.exists, and_assoc, exists_and_left]

中文:
定理 有基.lift
  结论: {ι} {p : ι -> 命题} {s : ι -> 集合 α} {f : 滤子 α} (hf : f.有基 p s)
  证明: by
  refine ⟨fun t => (hf.mem_lift_iff hg gm).trans ?_⟩
  simp [Sigma.exists, and_assoc, exists_and_left]

Depends on / 依赖: Sigma.exists, and_assoc, exists_and_left, hf.mem_lift_iff, mem_lift_iff
-/
theorem HasBasis.lift {ι} {p : ι -> Prop} {s : ι -> Set α} {f : Filter α} (hf : f.HasBasis p s)
    {β : ι -> Type*} {pg : forall i, β i -> Prop} {sg : forall i, β i -> Set γ} {g : Set α -> Filter γ}
    (hg : forall i, (g (s i)).HasBasis (pg i) (sg i)) (gm : Monotone g) :
    (f.lift g).HasBasis
      (fun i : Σ i, β i => p i.1 ∧ pg i.1 i.2)
      fun i : Σ i, β i => sg i.1 i.2 := by
  refine ⟨fun t => (hf.mem_lift_iff hg gm).trans ?_⟩
  simp [Sigma.exists, and_assoc, exists_and_left]

/--
theorem `mem_lift_sets` / 定理 `mem_lift_sets`

English:
theorem mem_lift_sets
  given: (hg : Monotone g) {s : Set β}
  statement: s in f.lift g ↔ exists t in f, s in g t
  proof: (f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans by
    simp only [id, exists_mem_subset_iff]

中文:
定理 mem_lift_sets
  条件: (hg : 递增 g) {s : 集合 β}
  结论: s in f.lift g ↔ 存在 t in f, s in g t
  证明: (f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans by
    simp only [id, exists_mem_subset_iff]

Depends on / 依赖: basis_sets, exists_mem_subset_iff, f.basis_sets.mem_lift_iff, mem_lift_iff
-/
theorem mem_lift_sets (hg : Monotone g) {s : Set β} : s in f.lift g ↔ exists t in f, s in g t :=
(f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans by
    simp only [id, exists_mem_subset_iff]

/--
theorem `sInter_lift_sets` / 定理 `sInter_lift_sets`

English:
theorem sInter_lift_sets
  given: (hg : Monotone g)
  proof: by
  simp only [sInter_eq_biInter, mem_ofPred_eq, mem_lift_sets hg, iInter_exists,
    iInter_and, @iInter_comm _ (Set β)]

中文:
定理 s整数er_lift_sets
  条件: (hg : 递增 g)
  证明: by
  simp only [sInter_eq_biInter, mem_ofPred_eq, mem_lift_sets hg, iInter_exists,
    iInter_and, @iInter_comm _ (Set β)]

Depends on / 依赖: iInter_and, iInter_comm, iInter_exists, mem_lift_sets, mem_ofPred_eq, sInter_eq_biInter
-/
theorem sInter_lift_sets (hg : Monotone g) :
    ⋂₀ { s | s in f.lift g } = ⋂ s in f, ⋂₀ { t | t in g s } := by
  simp only [sInter_eq_biInter, mem_ofPred_eq, mem_lift_sets hg, iInter_exists,
    iInter_and, @iInter_comm _ (Set β)]

/--
theorem `mem_lift` / 定理 `mem_lift`

English:
theorem mem_lift
  given: {s : Set β} {t : Set α} (ht : t in f) (hs : s in g t)
  statement: s in f.lift g
  proof: le_principal_iff.mp
show f.lift g <= 𝓟 s from iInf_le_of_le t iInf_le_of_le ht le_principal_iff.mpr hs

中文:
定理 mem_lift
  条件: {s : 集合 β} {t : 集合 α} (ht : t in f) (hs : s in g t)
  结论: s in f.lift g
  证明: le_principal_iff.mp
show f.lift g <= 𝓟 s from iInf_le_of_le t iInf_le_of_le ht le_principal_iff.mpr hs

Depends on / 依赖: f.lift, iInf_le_of_le, le_principal_iff, le_principal_iff.mp, le_principal_iff.mpr
-/
theorem mem_lift {s : Set β} {t : Set α} (ht : t in f) (hs : s in g t) : s in f.lift g :=
le_principal_iff.mp
show f.lift g <= 𝓟 s from iInf_le_of_le t iInf_le_of_le ht le_principal_iff.mpr hs

/--
theorem `lift_le` / 定理 `lift_le`

English:
theorem lift_le
  statement: {f : Filter α} {g : Set α -> Filter β} {h : Filter β} {s : Set α} (hs : s in f)
  proof: iInf₂_le_of_le s hs hg

中文:
定理 lift_le
  结论: {f : 滤子 α} {g : 集合 α -> 滤子 β} {h : 滤子 β} {s : 集合 α} (hs : s in f)
  证明: iInf₂_le_of_le s hs hg
-/
theorem lift_le {f : Filter α} {g : Set α -> Filter β} {h : Filter β} {s : Set α} (hs : s in f)
    (hg : g s <= h) : f.lift g <= h :=
  iInf₂_le_of_le s hs hg

/--
theorem `le_lift` / 定理 `le_lift`

English:
theorem le_lift
  given: {f : Filter α} {g : Set α -> Filter β} {h : Filter β}
  proof: le_iInf₂_iff

中文:
定理 le_lift
  条件: {f : 滤子 α} {g : 集合 α -> 滤子 β} {h : 滤子 β}
  证明: le_iInf₂_iff
-/
theorem le_lift {f : Filter α} {g : Set α -> Filter β} {h : Filter β} :
    h <= f.lift g ↔ forall s in f, h <= g s :=
  le_iInf₂_iff

/--
theorem `lift_mono` / 定理 `lift_mono`

English:
theorem lift_mono
  given: (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  statement: f₁.lift g₁ <= f₂.lift g₂
  proof: iInf_mono fun s => iInf_mono' fun hs => ⟨hf hs, hg s⟩

中文:
定理 lift_mono
  条件: (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  结论: f₁.lift g₁ <= f₂.lift g₂
  证明: iInf_mono fun s => iInf_mono' fun hs => ⟨hf hs, hg s⟩

Depends on / 依赖: iInf_mono
-/
theorem lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁ <= f₂.lift g₂ :=
  iInf_mono fun s => iInf_mono' fun hs => ⟨hf hs, hg s⟩

/--
theorem `lift_mono'` / 定理 `lift_mono'`

English:
theorem lift_mono'
  given: (hg : forall s in f, g₁ s <= g₂ s)
  statement: f.lift g₁ <= f.lift g₂
  proof: iInf₂_mono hg

中文:
定理 lift_mono'
  条件: (hg : 对任意 s in f, g₁ s <= g₂ s)
  结论: f.lift g₁ <= f.lift g₂
  证明: iInf₂_mono hg
-/
theorem lift_mono' (hg : forall s in f, g₁ s <= g₂ s) : f.lift g₁ <= f.lift g₂ := iInf₂_mono hg

/--
theorem `tendsto_lift` / 定理 `tendsto_lift`

English:
theorem tendsto_lift
  given: {m : γ -> β} {l : Filter γ}
  proof: by
  simp only [Filter.lift, tendsto_iInf]

中文:
定理 tendsto_lift
  条件: {m : γ -> β} {l : 滤子 γ}
  证明: by
  simp only [Filter.lift, tendsto_iInf]

Depends on / 依赖: Filter, Filter.lift, tendsto_iInf
-/
theorem tendsto_lift {m : γ -> β} {l : Filter γ} :
    Tendsto m l (f.lift g) ↔ forall s in f, Tendsto m l (g s) := by
  simp only [Filter.lift, tendsto_iInf]

/--
theorem `map_lift_eq` / 定理 `map_lift_eq`

English:
theorem map_lift_eq
  given: {m : β -> γ} (hg : Monotone g)
  statement: map m (f.lift g) = f.lift (map m ∘ g)
  proof: have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, mem_map, Function.comp_apply]

中文:
定理 map_lift_eq
  条件: {m : β -> γ} (hg : 递增 g)
  结论: map m (f.lift g) = f.lift (map m ∘ g)
  证明: have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, mem_map, Function.comp_apply]

Depends on / 依赖: Filter, Filter.ext, Function, Function.comp_apply, Monotone, comp_apply, map_mono, map_mono.comp, mem_lift_sets, mem_map
-/
theorem map_lift_eq {m : β -> γ} (hg : Monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
  have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, mem_map, Function.comp_apply]

/--
theorem `comap_lift_eq` / 定理 `comap_lift_eq`

English:
theorem comap_lift_eq
  given: {m : γ -> β}
  statement: comap m (f.lift g) = f.lift (comap m ∘ g)
  proof: by
  simp only [Filter.lift, comap_iInf]; rfl

中文:
定理 comap_lift_eq
  条件: {m : γ -> β}
  结论: comap m (f.lift g) = f.lift (comap m ∘ g)
  证明: by
  simp only [Filter.lift, comap_iInf]; rfl

Depends on / 依赖: Filter, Filter.lift, comap_iInf
-/
theorem comap_lift_eq {m : γ -> β} : comap m (f.lift g) = f.lift (comap m ∘ g) := by
  simp only [Filter.lift, comap_iInf]; rfl

/--
theorem `comap_lift_eq2` / 定理 `comap_lift_eq2`

English:
theorem comap_lift_eq2
  given: {m : β -> α} {g : Set β -> Filter γ} (hg : Monotone g)
  proof: le_antisymm (le_iInf₂ fun s hs => iInf₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_iInf₂ fun _s ⟨s', hs', h_sub⟩ => iInf₂_le_of_le s' hs' <| hg h_sub)

中文:
定理 comap_lift_eq2
  条件: {m : β -> α} {g : 集合 β -> 滤子 γ} (hg : 递增 g)
  证明: le_antisymm (le_iInf₂ fun s hs => iInf₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_iInf₂ fun _s ⟨s', hs', h_sub⟩ => iInf₂_le_of_le s' hs' <| hg h_sub)

Depends on / 依赖: Subset, Subset.rfl, h_sub, le_antisymm
-/
theorem comap_lift_eq2 {m : β -> α} {g : Set β -> Filter γ} (hg : Monotone g) :
    (comap m f).lift g = f.lift (g ∘ preimage m) :=
  le_antisymm (le_iInf₂ fun s hs => iInf₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_iInf₂ fun _s ⟨s', hs', h_sub⟩ => iInf₂_le_of_le s' hs' <| hg h_sub)

/--
theorem `lift_map_le` / 定理 `lift_map_le`

English:
theorem lift_map_le
  given: {g : Set β -> Filter γ} {m : α -> β}
  statement: (map m f).lift g <= f.lift (g ∘ image m)
  proof: le_lift.2 fun _s hs => lift_le (image_mem_map hs) le_rfl

中文:
定理 lift_map_le
  条件: {g : 集合 β -> 滤子 γ} {m : α -> β}
  结论: (map m f).lift g <= f.lift (g ∘ 像 m)
  证明: le_lift.2 fun _s hs => lift_le (image_mem_map hs) le_rfl

Depends on / 依赖: image_mem_map, le_lift, le_rfl, lift_le
-/
theorem lift_map_le {g : Set β -> Filter γ} {m : α -> β} : (map m f).lift g <= f.lift (g ∘ image m) :=
  le_lift.2 fun _s hs => lift_le (image_mem_map hs) le_rfl

/--
theorem `map_lift_eq2` / 定理 `map_lift_eq2`

English:
theorem map_lift_eq2
  given: {g : Set β -> Filter γ} {m : α -> β} (hg : Monotone g)
  proof: lift_map_le.antisymm le_lift.2 fun _s hs => lift_le hs hg image_preimage_subset _ _

中文:
定理 map_lift_eq2
  条件: {g : 集合 β -> 滤子 γ} {m : α -> β} (hg : 递增 g)
  证明: lift_map_le.antisymm le_lift.2 fun _s hs => lift_le hs hg image_preimage_subset _ _

Depends on / 依赖: antisymm, image_preimage_subset, le_lift, lift_le, lift_map_le, lift_map_le.antisymm
-/
theorem map_lift_eq2 {g : Set β -> Filter γ} {m : α -> β} (hg : Monotone g) :
    (map m f).lift g = f.lift (g ∘ image m) :=
lift_map_le.antisymm le_lift.2 fun _s hs => lift_le hs hg image_preimage_subset _ _

/--
theorem `lift_comm` / 定理 `lift_comm`

English:
theorem lift_comm
  given: {g : Filter β} {h : Set α -> Set β -> Filter γ}
  proof: le_antisymm
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)

中文:
定理 lift_comm
  条件: {g : 滤子 β} {h : 集合 α -> 集合 β -> 滤子 γ}
  证明: le_antisymm
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)

Depends on / 依赖: iInf_le, iInf_le_of_le, le_antisymm, le_iInf
-/
theorem lift_comm {g : Filter β} {h : Set α -> Set β -> Filter γ} :
    (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t :=
  le_antisymm
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
iInf_le_of_le j iInf_le_of_le hj iInf_le_of_le i iInf_le _ hi)

/--
theorem `lift_assoc` / 定理 `lift_assoc`

English:
theorem lift_assoc
  given: {h : Set β -> Filter γ} (hg : Monotone g)
  proof: le_antisymm
    (le_iInf₂ fun _s hs => le_iInf₂ fun t ht =>
iInf_le_of_le t iInf_le _ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_iInf₂ fun t ht =>
      let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
iInf_le_of_le s iInf_le_of_le hs iInf_le_of_le t iInf_le _ h')

中文:
定理 lift_assoc
  条件: {h : 集合 β -> 滤子 γ} (hg : 递增 g)
  证明: le_antisymm
    (le_iInf₂ fun _s hs => le_iInf₂ fun t ht =>
iInf_le_of_le t iInf_le _ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_iInf₂ fun t ht =>
      let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
iInf_le_of_le s iInf_le_of_le hs iInf_le_of_le t iInf_le _ h')

Depends on / 依赖: iInf_le, iInf_le_of_le, le_antisymm, mem_lift_sets
-/
theorem lift_assoc {h : Set β -> Filter γ} (hg : Monotone g) :
    (f.lift g).lift h = f.lift fun s => (g s).lift h :=
  le_antisymm
    (le_iInf₂ fun _s hs => le_iInf₂ fun t ht =>
iInf_le_of_le t iInf_le _ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_iInf₂ fun t ht =>
      let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
iInf_le_of_le s iInf_le_of_le hs iInf_le_of_le t iInf_le _ h')

/--
theorem `lift_lift_same_le_lift` / 定理 `lift_lift_same_le_lift`

English:
theorem lift_lift_same_le_lift
  given: {g : Set α -> Set α -> Filter β}
  proof: le_lift.2 fun _s hs => lift_le hs lift_le hs le_rfl

中文:
定理 lift_lift_same_le_lift
  条件: {g : 集合 α -> 集合 α -> 滤子 β}
  证明: le_lift.2 fun _s hs => lift_le hs lift_le hs le_rfl

Depends on / 依赖: le_lift, le_rfl, lift_le
-/
theorem lift_lift_same_le_lift {g : Set α -> Set α -> Filter β} :
    (f.lift fun s => f.lift (g s)) <= f.lift fun s => g s s :=
le_lift.2 fun _s hs => lift_le hs lift_le hs le_rfl

/--
theorem `lift_lift_same_eq_lift` / 定理 `lift_lift_same_eq_lift`

English:
theorem lift_lift_same_eq_lift
  statement: {g : Set α -> Set α -> Filter β} (hg₁ : forall s, Monotone fun t => g s t)
  proof: lift_lift_same_le_lift.antisymm
le_lift.2 fun s hs => le_lift.2 fun t ht => lift_le (inter_mem hs ht)
      calc
        g (s inter t) (s inter t) <= g s (s inter t) := hg₂ (s inter t) inter_subset_left
        _ <= g s t := hg₁ s inter_subset_right

中文:
定理 lift_lift_same_eq_lift
  结论: {g : 集合 α -> 集合 α -> 滤子 β} (hg₁ : 对任意 s, 递增 fun t => g s t)
  证明: lift_lift_same_le_lift.antisymm
le_lift.2 fun s hs => le_lift.2 fun t ht => lift_le (inter_mem hs ht)
      calc
        g (s inter t) (s inter t) <= g s (s inter t) := hg₂ (s inter t) inter_subset_left
        _ <= g s t := hg₁ s inter_subset_right

Depends on / 依赖: antisymm, inter_mem, inter_subset_left, inter_subset_right, le_lift, lift_le, lift_lift_same_le_lift, lift_lift_same_le_lift.antisymm
-/
theorem lift_lift_same_eq_lift {g : Set α -> Set α -> Filter β} (hg₁ : forall s, Monotone fun t => g s t)
    (hg₂ : forall t, Monotone fun s => g s t) : (f.lift fun s => f.lift (g s)) = f.lift fun s => g s s :=
lift_lift_same_le_lift.antisymm
le_lift.2 fun s hs => le_lift.2 fun t ht => lift_le (inter_mem hs ht)
      calc
        g (s inter t) (s inter t) <= g s (s inter t) := hg₂ (s inter t) inter_subset_left
        _ <= g s t := hg₁ s inter_subset_right

/--
theorem `lift_principal` / 定理 `lift_principal`

English:
theorem lift_principal
  given: {s : Set α} (hg : Monotone g)
  statement: (𝓟 s).lift g = g s
  proof: (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun _t ht => hg ht)

中文:
定理 lift_principal
  条件: {s : 集合 α} (hg : 递增 g)
  结论: (𝓟 s).lift g = g s
  证明: (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun _t ht => hg ht)

Depends on / 依赖: antisymm, le_lift, le_rfl, lift_le, mem_principal_self
-/
theorem lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s :=
  (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun _t ht => hg ht)

/--
theorem `monotone_lift` / 定理 `monotone_lift`

English:
theorem monotone_lift
  statement: [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Filter β} (hf : Monotone f)
  proof: fun _ _ h => lift_mono (hf h) (hg h)

中文:
定理 monotone_lift
  结论: [预序 γ] {f : γ -> 滤子 α} {g : γ -> 集合 α -> 滤子 β} (hf : 递增 f)
  证明: fun _ _ h => lift_mono (hf h) (hg h)

Depends on / 依赖: lift_mono
-/
theorem monotone_lift [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Filter β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift (g c) := fun _ _ h => lift_mono (hf h) (hg h)

/--
theorem `lift_neBot_iff` / 定理 `lift_neBot_iff`

English:
theorem lift_neBot_iff
  given: (hm : Monotone g)
  statement: (NeBot (f.lift g)) ↔ forall s in f, NeBot (g s)
  proof: by
  simp only [neBot_iff, Ne, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists, not_and]

@[simp]

中文:
定理 lift_neBot_iff
  条件: (hm : 递增 g)
  结论: (NeBot (f.lift g)) ↔ 对任意 s in f, NeBot (g s)
  证明: by
  simp only [neBot_iff, Ne, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists, not_and]

@[simp]

Depends on / 依赖: empty_mem_iff_bot, mem_lift_sets, neBot_iff, not_and, not_exists
-/
theorem lift_neBot_iff (hm : Monotone g) : (NeBot (f.lift g)) ↔ forall s in f, NeBot (g s) := by
  simp only [neBot_iff, Ne, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists, not_and]

@[simp]
/--
theorem `lift_const` / 定理 `lift_const`

English:
theorem lift_const
  given: {f : Filter α} {g : Filter β}
  statement: (f.lift fun _ => g) = g
  proof: iInf_subtype'.trans iInf_const

@[simp]

中文:
定理 lift_const
  条件: {f : 滤子 α} {g : 滤子 β}
  结论: (f.lift fun _ => g) = g
  证明: iInf_subtype'.trans iInf_const

@[simp]

Depends on / 依赖: iInf_const, iInf_subtype
-/
theorem lift_const {f : Filter α} {g : Filter β} : (f.lift fun _ => g) = g :=
  iInf_subtype'.trans iInf_const

@[simp]
/--
theorem `lift_inf` / 定理 `lift_inf`

English:
theorem lift_inf
  given: {f : Filter α} {g h : Set α -> Filter β}
  proof: by simp only [Filter.lift, iInf_inf_eq]

@[simp]

中文:
定理 lift_inf
  条件: {f : 滤子 α} {g h : 集合 α -> 滤子 β}
  证明: by simp only [Filter.lift, iInf_inf_eq]

@[simp]

Depends on / 依赖: Filter, Filter.lift, iInf_inf_eq
-/
theorem lift_inf {f : Filter α} {g h : Set α -> Filter β} :
    (f.lift fun x => g x ⊓ h x) = f.lift g ⊓ f.lift h := by simp only [Filter.lift, iInf_inf_eq]

@[simp]
/--
theorem `lift_principal2` / 定理 `lift_principal2`

English:
theorem lift_principal2
  given: {f : Filter α}
  statement: f.lift 𝓟 = f
  proof: le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_iInf fun s => le_iInf fun hs => by simp only [hs, le_principal_iff])

中文:
定理 lift_principal2
  条件: {f : 滤子 α}
  结论: f.lift 𝓟 = f
  证明: le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_iInf fun s => le_iInf fun hs => by simp only [hs, le_principal_iff])

Depends on / 依赖: le_antisymm, le_iInf, le_principal_iff, mem_lift, mem_principal_self
-/
theorem lift_principal2 {f : Filter α} : f.lift 𝓟 = f :=
  le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_iInf fun s => le_iInf fun hs => by simp only [hs, le_principal_iff])

/--
theorem `lift_iInf_le` / 定理 `lift_iInf_le`

English:
theorem lift_iInf_le
  given: {f : ι -> Filter α} {g : Set α -> Filter β}
  proof: le_iInf fun _ => lift_mono (iInf_le _ _) le_rfl

中文:
定理 lift_iInf_le
  条件: {f : ι -> 滤子 α} {g : 集合 α -> 滤子 β}
  证明: le_iInf fun _ => lift_mono (iInf_le _ _) le_rfl

Depends on / 依赖: iInf_le, le_iInf, le_rfl, lift_mono
-/
theorem lift_iInf_le {f : ι -> Filter α} {g : Set α -> Filter β} :
    (iInf f).lift g <= ⨅ i, (f i).lift g :=
  le_iInf fun _ => lift_mono (iInf_le _ _) le_rfl

/--
theorem `lift_iInf` / 定理 `lift_iInf`

English:
theorem lift_iInf
  statement: [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filter β}
  proof: by
  refine lift_iInf_le.antisymm fun s => ?_
  have H : forall t in iInf f, ⨅ i, (f i).lift g <= g t := by
    intro t ht
    refine iInf_sets_induct ht ?_ fun hs ht => ?_
    · inhabit ι
      exact iInf₂_le_of_le default univ (iInf_le _ univ_mem)
    · rw [hg]
      exact le_inf (iInf₂_le_of_le _ _ <| iInf_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp, and_imp]
  exact fun t ht hs => H t ht hs

中文:
定理 lift_iInf
  结论: [非空 ι] {f : ι -> 滤子 α} {g : 集合 α -> 滤子 β}
  证明: by
  refine lift_iInf_le.antisymm fun s => ?_
  have H : forall t in iInf f, ⨅ i, (f i).lift g <= g t := by
    intro t ht
    refine iInf_sets_induct ht ?_ fun hs ht => ?_
    · inhabit ι
      exact iInf₂_le_of_le default univ (iInf_le _ univ_mem)
    · rw [hg]
      exact le_inf (iInf₂_le_of_le _ _ <| iInf_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp, and_imp]
  exact fun t ht hs => H t ht hs

Depends on / 依赖: Monotone, Monotone.of_map_inf, and_imp, antisymm, exists_imp, iInf_le, iInf_sets_induct, inhabit, le_inf, lift_iInf_le, lift_iInf_le.antisymm, mem_lift_sets, of_map_inf, univ_mem
-/
theorem lift_iInf [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filter β}
    (hg : forall s t, g (s inter t) = g s ⊓ g t) : (iInf f).lift g = ⨅ i, (f i).lift g := by
  refine lift_iInf_le.antisymm fun s => ?_
  have H : forall t in iInf f, ⨅ i, (f i).lift g <= g t := by
    intro t ht
    refine iInf_sets_induct ht ?_ fun hs ht => ?_
    · inhabit ι
      exact iInf₂_le_of_le default univ (iInf_le _ univ_mem)
    · rw [hg]
      exact le_inf (iInf₂_le_of_le _ _ <| iInf_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp, and_imp]
  exact fun t ht hs => H t ht hs

/--
theorem `lift_iInf_of_directed` / 定理 `lift_iInf_of_directed`

English:
theorem lift_iInf_of_directed
  statement: [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filter β}
  proof: lift_iInf_le.antisymm fun s => by
    simp only [mem_lift_sets hg, exists_imp, and_imp, mem_iInf_of_directed hf]
exact fun t i ht hs => mem_iInf_of_mem i mem_lift ht hs

中文:
定理 lift_iInf_of_directed
  结论: [非空 ι] {f : ι -> 滤子 α} {g : 集合 α -> 滤子 β}
  证明: lift_iInf_le.antisymm fun s => by
    simp only [mem_lift_sets hg, exists_imp, and_imp, mem_iInf_of_directed hf]
exact fun t i ht hs => mem_iInf_of_mem i mem_lift ht hs

Depends on / 依赖: and_imp, antisymm, exists_imp, lift_iInf_le, lift_iInf_le.antisymm, mem_iInf_of_directed, mem_iInf_of_mem, mem_lift, mem_lift_sets
-/
theorem lift_iInf_of_directed [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Filter β}
    (hf : Directed (· >= ·) f) (hg : Monotone g) : (iInf f).lift g = ⨅ i, (f i).lift g :=
  lift_iInf_le.antisymm fun s => by
    simp only [mem_lift_sets hg, exists_imp, and_imp, mem_iInf_of_directed hf]
exact fun t i ht hs => mem_iInf_of_mem i mem_lift ht hs

/--
theorem `lift_iInf_of_map_univ` / 定理 `lift_iInf_of_map_univ`

English:
theorem lift_iInf_of_map_univ
  statement: {f : ι -> Filter α} {g : Set α -> Filter β}
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_empty, hg']
  · exact lift_iInf hg

中文:
定理 lift_iInf_of_map_univ
  结论: {f : ι -> 滤子 α} {g : 集合 α -> 滤子 β}
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_empty, hg']
  · exact lift_iInf hg

Depends on / 依赖: iInf_of_empty, isEmpty_or_nonempty, lift_iInf
-/
theorem lift_iInf_of_map_univ {f : ι -> Filter α} {g : Set α -> Filter β}
    (hg : forall s t, g (s inter t) = g s ⊓ g t) (hg' : g univ = ⊤) :
    (iInf f).lift g = ⨅ i, (f i).lift g := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_empty, hg']
  · exact lift_iInf hg

end lift

section Lift'

variable {f f₁ f₂ : Filter α} {h h₁ h₂ : Set α -> Set β}

@[simp]
/--
theorem `lift'_top` / 定理 `lift'_top`

English:
theorem lift'_top
  given: (h : Set α -> Set β)
  statement: (⊤ : Filter α).lift' h = 𝓟 (h univ)
  proof: lift_top _

中文:
定理 lift'_top
  条件: (h : 集合 α -> 集合 β)
  结论: (⊤ : 滤子 α).lift' h = 𝓟 (h univ)
  证明: lift_top _

Depends on / 依赖: lift_top
-/
theorem lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 𝓟 (h univ) :=
  lift_top _

/--
theorem `mem_lift'` / 定理 `mem_lift'`

English:
theorem mem_lift'
  given: {t : Set α} (ht : t in f)
  statement: h t in f.lift' h
  proof: le_principal_iff.mp show f.lift' h <= 𝓟 (h t) from iInf_le_of_le t iInf_le_of_le ht le_rfl

中文:
定理 mem_lift'
  条件: {t : 集合 α} (ht : t in f)
  结论: h t in f.lift' h
  证明: le_principal_iff.mp show f.lift' h <= 𝓟 (h t) from iInf_le_of_le t iInf_le_of_le ht le_rfl

Depends on / 依赖: f.lift, iInf_le_of_le, le_principal_iff, le_principal_iff.mp, le_rfl
-/
theorem mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h :=
le_principal_iff.mp show f.lift' h <= 𝓟 (h t) from iInf_le_of_le t iInf_le_of_le ht le_rfl

/--
theorem `tendsto_lift'` / 定理 `tendsto_lift'`

English:
theorem tendsto_lift'
  given: {m : γ -> β} {l : Filter γ}
  proof: by
  simp only [Filter.lift', tendsto_lift, tendsto_principal, comp]

中文:
定理 tendsto_lift'
  条件: {m : γ -> β} {l : 滤子 γ}
  证明: by
  simp only [Filter.lift', tendsto_lift, tendsto_principal, comp]

Depends on / 依赖: Filter, Filter.lift, tendsto_lift, tendsto_principal
-/
theorem tendsto_lift' {m : γ -> β} {l : Filter γ} :
    Tendsto m l (f.lift' h) ↔ forall s in f, forallᶠ a in l, m a in h s := by
  simp only [Filter.lift', tendsto_lift, tendsto_principal, comp]

/--
theorem `HasBasis.lift'` / 定理 `HasBasis.lift'`

English:
theorem HasBasis.lift'
  given: {ι} {p : ι -> Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h)
  proof: ⟨fun t => (hf.mem_lift_iff (fun i => hasBasis_principal (h (s i)))
    (monotone_principal.comp hh)).trans <| by simp only [exists_const, true_and, comp]⟩

中文:
定理 有基.lift'
  条件: {ι} {p : ι -> 命题} {s} (hf : f.有基 p s) (hh : 递增 h)
  证明: ⟨fun t => (hf.mem_lift_iff (fun i => hasBasis_principal (h (s i)))
    (monotone_principal.comp hh)).trans <| by simp only [exists_const, true_and, comp]⟩

Depends on / 依赖: exists_const, hasBasis_principal, hf.mem_lift_iff, mem_lift_iff, monotone_principal, monotone_principal.comp, true_and
-/
theorem HasBasis.lift' {ι} {p : ι -> Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h) :
    (f.lift' h).HasBasis p (h ∘ s) :=
  ⟨fun t => (hf.mem_lift_iff (fun i => hasBasis_principal (h (s i)))
    (monotone_principal.comp hh)).trans <| by simp only [exists_const, true_and, comp]⟩

/--
theorem `mem_lift'_sets` / 定理 `mem_lift'_sets`

English:
theorem mem_lift'_sets
  given: (hh : Monotone h) {s : Set β}
  statement: s in f.lift' h ↔ exists t in f, h t subseteq s
  proof: mem_lift_sets monotone_principal.comp hh

中文:
定理 mem_lift'_sets
  条件: (hh : 递增 h) {s : 集合 β}
  结论: s in f.lift' h ↔ 存在 t in f, h t subseteq s
  证明: mem_lift_sets monotone_principal.comp hh
-/
theorem mem_lift'_sets (hh : Monotone h) {s : Set β} : s in f.lift' h ↔ exists t in f, h t subseteq s :=
mem_lift_sets monotone_principal.comp hh

/--
theorem `eventually_lift'_iff` / 定理 `eventually_lift'_iff`

English:
theorem eventually_lift'_iff
  given: (hh : Monotone h) {p : β -> Prop}
  proof: mem_lift'_sets hh

中文:
定理 eventually_lift'_iff
  条件: (hh : 递增 h) {p : β -> 命题}
  证明: mem_lift'_sets hh

Depends on / 依赖: _sets, mem_lift
-/
theorem eventually_lift'_iff (hh : Monotone h) {p : β -> Prop} :
    (forallᶠ y in f.lift' h, p y) ↔ exists t in f, forall y in h t, p y :=
  mem_lift'_sets hh

/--
theorem `sInter_lift'_sets` / 定理 `sInter_lift'_sets`

English:
theorem sInter_lift'_sets
  given: (hh : Monotone h)
  statement: ⋂₀ { s | s in f.lift' h } = ⋂ s in f, h s
  proof: (sInter_lift_sets (monotone_principal.comp hh)).trans iInter₂_congr fun _ _ => csInf_Ici

中文:
定理 s整数er_lift'_sets
  条件: (hh : 递增 h)
  结论: ⋂₀ { s | s in f.lift' h } = ⋂ s in f, h s
  证明: (sInter_lift_sets (monotone_principal.comp hh)).trans iInter₂_congr fun _ _ => csInf_Ici

Depends on / 依赖: csInf_Ici, monotone_principal, monotone_principal.comp, sInter_lift_sets
-/
theorem sInter_lift'_sets (hh : Monotone h) : ⋂₀ { s | s in f.lift' h } = ⋂ s in f, h s :=
(sInter_lift_sets (monotone_principal.comp hh)).trans iInter₂_congr fun _ _ => csInf_Ici

/--
theorem `lift'_le` / 定理 `lift'_le`

English:
theorem lift'_le
  statement: {f : Filter α} {g : Set α -> Set β} {h : Filter β} {s : Set α} (hs : s in f)
  proof: lift_le hs hg

中文:
定理 lift'_le
  结论: {f : 滤子 α} {g : 集合 α -> 集合 β} {h : 滤子 β} {s : 集合 α} (hs : s in f)
  证明: lift_le hs hg
-/
theorem lift'_le {f : Filter α} {g : Set α -> Set β} {h : Filter β} {s : Set α} (hs : s in f)
    (hg : 𝓟 (g s) <= h) : f.lift' g <= h :=
  lift_le hs hg

/--
theorem `lift'_mono` / 定理 `lift'_mono`

English:
theorem lift'_mono
  given: (hf : f₁ <= f₂) (hh : h₁ <= h₂)
  statement: f₁.lift' h₁ <= f₂.lift' h₂
  proof: lift_mono hf fun s => principal_mono.mpr hh s

中文:
定理 lift'_mono
  条件: (hf : f₁ <= f₂) (hh : h₁ <= h₂)
  结论: f₁.lift' h₁ <= f₂.lift' h₂
  证明: lift_mono hf fun s => principal_mono.mpr hh s
-/
theorem lift'_mono (hf : f₁ <= f₂) (hh : h₁ <= h₂) : f₁.lift' h₁ <= f₂.lift' h₂ :=
lift_mono hf fun s => principal_mono.mpr hh s

/--
theorem `lift'_mono'` / 定理 `lift'_mono'`

English:
theorem lift'_mono'
  given: (hh : forall s in f, h₁ s subseteq h₂ s)
  statement: f.lift' h₁ <= f.lift' h₂
  proof: iInf₂_mono fun s hs => principal_mono.mpr hh s hs

中文:
定理 lift'_mono'
  条件: (hh : 对任意 s in f, h₁ s subseteq h₂ s)
  结论: f.lift' h₁ <= f.lift' h₂
  证明: iInf₂_mono fun s hs => principal_mono.mpr hh s hs
-/
theorem lift'_mono' (hh : forall s in f, h₁ s subseteq h₂ s) : f.lift' h₁ <= f.lift' h₂ :=
iInf₂_mono fun s hs => principal_mono.mpr hh s hs

/--
theorem `lift'_cong` / 定理 `lift'_cong`

English:
theorem lift'_cong
  given: (hh : forall s in f, h₁ s = h₂ s)
  statement: f.lift' h₁ = f.lift' h₂
  proof: le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)

中文:
定理 lift'_cong
  条件: (hh : 对任意 s in f, h₁ s = h₂ s)
  结论: f.lift' h₁ = f.lift' h₂
  证明: le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)
-/
theorem lift'_cong (hh : forall s in f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
  le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)

/--
theorem `map_lift'_eq` / 定理 `map_lift'_eq`

English:
theorem map_lift'_eq
  given: {m : β -> γ} (hh : Monotone h)
  statement: map m (f.lift' h) = f.lift' (image m ∘ h)
  proof: calc
map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by simp only [comp_def, Filter.lift', map_principal]

中文:
定理 map_lift'_eq
  条件: {m : β -> γ} (hh : 递增 h)
  结论: map m (f.lift' h) = f.lift' (像 m ∘ h)
  证明: calc
map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by simp only [comp_def, Filter.lift', map_principal]

Depends on / 依赖: Filter, Filter.lift, comp_def, f.lift, map_lift_eq, map_principal, monotone_principal, monotone_principal.comp
-/
theorem map_lift'_eq {m : β -> γ} (hh : Monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
  calc
map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by simp only [comp_def, Filter.lift', map_principal]

/--
theorem `lift'_map_le` / 定理 `lift'_map_le`

English:
theorem lift'_map_le
  given: {g : Set β -> Set γ} {m : α -> β}
  statement: (map m f).lift' g <= f.lift' (g ∘ image m)
  proof: lift_map_le

中文:
定理 lift'_map_le
  条件: {g : 集合 β -> 集合 γ} {m : α -> β}
  结论: (map m f).lift' g <= f.lift' (g ∘ 像 m)
  证明: lift_map_le
-/
theorem lift'_map_le {g : Set β -> Set γ} {m : α -> β} : (map m f).lift' g <= f.lift' (g ∘ image m) :=
  lift_map_le

/--
theorem `map_lift'_eq2` / 定理 `map_lift'_eq2`

English:
theorem map_lift'_eq2
  given: {g : Set β -> Set γ} {m : α -> β} (hg : Monotone g)
  proof: map_lift_eq2 monotone_principal.comp hg

中文:
定理 map_lift'_eq2
  条件: {g : 集合 β -> 集合 γ} {m : α -> β} (hg : 递增 g)
  证明: map_lift_eq2 monotone_principal.comp hg
-/
theorem map_lift'_eq2 {g : Set β -> Set γ} {m : α -> β} (hg : Monotone g) :
    (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 monotone_principal.comp hg

/--
theorem `comap_lift'_eq` / 定理 `comap_lift'_eq`

English:
theorem comap_lift'_eq
  given: {m : γ -> β}
  statement: comap m (f.lift' h) = f.lift' (preimage m ∘ h)
  proof: by
  simp only [Filter.lift', comap_lift_eq, comp_def, comap_principal]

中文:
定理 comap_lift'_eq
  条件: {m : γ -> β}
  结论: comap m (f.lift' h) = f.lift' (原像 m ∘ h)
  证明: by
  simp only [Filter.lift', comap_lift_eq, comp_def, comap_principal]

Depends on / 依赖: Filter, Filter.lift, comap_lift_eq, comap_principal, comp_def
-/
theorem comap_lift'_eq {m : γ -> β} : comap m (f.lift' h) = f.lift' (preimage m ∘ h) := by
  simp only [Filter.lift', comap_lift_eq, comp_def, comap_principal]

/--
theorem `comap_lift'_eq2` / 定理 `comap_lift'_eq2`

English:
theorem comap_lift'_eq2
  given: {m : β -> α} {g : Set β -> Set γ} (hg : Monotone g)
  proof: comap_lift_eq2 monotone_principal.comp hg

中文:
定理 comap_lift'_eq2
  条件: {m : β -> α} {g : 集合 β -> 集合 γ} (hg : 递增 g)
  证明: comap_lift_eq2 monotone_principal.comp hg
-/
theorem comap_lift'_eq2 {m : β -> α} {g : Set β -> Set γ} (hg : Monotone g) :
    (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
comap_lift_eq2 monotone_principal.comp hg

/--
theorem `lift'_principal` / 定理 `lift'_principal`

English:
theorem lift'_principal
  given: {s : Set α} (hh : Monotone h)
  statement: (𝓟 s).lift' h = 𝓟 (h s)
  proof: lift_principal monotone_principal.comp hh

中文:
定理 lift'_principal
  条件: {s : 集合 α} (hh : 递增 h)
  结论: (𝓟 s).lift' h = 𝓟 (h s)
  证明: lift_principal monotone_principal.comp hh
-/
theorem lift'_principal {s : Set α} (hh : Monotone h) : (𝓟 s).lift' h = 𝓟 (h s) :=
lift_principal monotone_principal.comp hh

/--
theorem `lift'_pure` / 定理 `lift'_pure`

English:
theorem lift'_pure
  given: {a : α} (hh : Monotone h)
  statement: (pure a : Filter α).lift' h = 𝓟 (h {a})
  proof: by
  rw [← principal_singleton]; rw [lift'_principal hh]

中文:
定理 lift'_pure
  条件: {a : α} (hh : 递增 h)
  结论: (pure a : 滤子 α).lift' h = 𝓟 (h {a})
  证明: by
  rw [← principal_singleton]; rw [lift'_principal hh]
-/
theorem lift'_pure {a : α} (hh : Monotone h) : (pure a : Filter α).lift' h = 𝓟 (h {a}) := by
  rw [← principal_singleton]; rw [lift'_principal hh]

/--
theorem `lift'_bot` / 定理 `lift'_bot`

English:
theorem lift'_bot
  given: (hh : Monotone h)
  statement: (⊥ : Filter α).lift' h = 𝓟 (h ∅)
  proof: by
  rw [← principal_empty]; rw [lift'_principal hh]

中文:
定理 lift'_bot
  条件: (hh : 递增 h)
  结论: (⊥ : 滤子 α).lift' h = 𝓟 (h ∅)
  证明: by
  rw [← principal_empty]; rw [lift'_principal hh]
-/
theorem lift'_bot (hh : Monotone h) : (⊥ : Filter α).lift' h = 𝓟 (h ∅) := by
  rw [← principal_empty]; rw [lift'_principal hh]

/--
theorem `le_lift'` / 定理 `le_lift'`

English:
theorem le_lift'
  given: {f : Filter α} {h : Set α -> Set β} {g : Filter β}
  proof: le_lift.trans forall₂_congr fun _ _ => le_principal_iff

中文:
定理 le_lift'
  条件: {f : 滤子 α} {h : 集合 α -> 集合 β} {g : 滤子 β}
  证明: le_lift.trans forall₂_congr fun _ _ => le_principal_iff

Depends on / 依赖: le_lift, le_lift.trans, le_principal_iff
-/
theorem le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filter β} :
    g <= f.lift' h ↔ forall s in f, h s in g :=
le_lift.trans forall₂_congr fun _ _ => le_principal_iff

/--
theorem `principal_le_lift'` / 定理 `principal_le_lift'`

English:
theorem principal_le_lift'
  given: {t : Set β}
  statement: 𝓟 t <= f.lift' h ↔ forall s in f, t subseteq h s
  proof: le_lift'

中文:
定理 principal_le_lift'
  条件: {t : 集合 β}
  结论: 𝓟 t <= f.lift' h ↔ 对任意 s in f, t subseteq h s
  证明: le_lift'

Depends on / 依赖: le_lift
-/
theorem principal_le_lift' {t : Set β} : 𝓟 t <= f.lift' h ↔ forall s in f, t subseteq h s :=
  le_lift'

/--
theorem `monotone_lift'` / 定理 `monotone_lift'`

English:
theorem monotone_lift'
  statement: [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Set β} (hf : Monotone f)
  proof: fun _ _ h => lift'_mono (hf h) (hg h)

中文:
定理 monotone_lift'
  结论: [预序 γ] {f : γ -> 滤子 α} {g : γ -> 集合 α -> 集合 β} (hf : 递增 f)
  证明: fun _ _ h => lift'_mono (hf h) (hg h)

Depends on / 依赖: _mono
-/
theorem monotone_lift' [Preorder γ] {f : γ -> Filter α} {g : γ -> Set α -> Set β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift' (g c) := fun _ _ h => lift'_mono (hf h) (hg h)

/--
theorem `lift_lift'_assoc` / 定理 `lift_lift'_assoc`

English:
theorem lift_lift'_assoc
  statement: {g : Set α -> Set β} {h : Set β -> Filter γ} (hg : Monotone g)
  proof: calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh]

中文:
定理 lift_lift'_assoc
  结论: {g : 集合 α -> 集合 β} {h : 集合 β -> 滤子 γ} (hg : 递增 g)
  证明: calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh]

Depends on / 依赖: f.lift, lift_assoc, lift_principal, monotone_principal, monotone_principal.comp
-/
theorem lift_lift'_assoc {g : Set α -> Set β} {h : Set β -> Filter γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift h = f.lift fun s => h (g s) :=
  calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh]

/--
theorem `lift'_lift'_assoc` / 定理 `lift'_lift'_assoc`

English:
theorem lift'_lift'_assoc
  statement: {g : Set α -> Set β} {h : Set β -> Set γ} (hg : Monotone g)
  proof: lift_lift'_assoc hg (monotone_principal.comp hh)

中文:
定理 lift'_lift'_assoc
  结论: {g : 集合 α -> 集合 β} {h : 集合 β -> 集合 γ} (hg : 递增 g)
  证明: lift_lift'_assoc hg (monotone_principal.comp hh)
-/
theorem lift'_lift'_assoc {g : Set α -> Set β} {h : Set β -> Set γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift' h = f.lift' fun s => h (g s) :=
  lift_lift'_assoc hg (monotone_principal.comp hh)

/--
theorem `lift'_lift_assoc` / 定理 `lift'_lift_assoc`

English:
theorem lift'_lift_assoc
  given: {g : Set α -> Filter β} {h : Set β -> Set γ} (hg : Monotone g)
  proof: lift_assoc hg

中文:
定理 lift'_lift_assoc
  条件: {g : 集合 α -> 滤子 β} {h : 集合 β -> 集合 γ} (hg : 递增 g)
  证明: lift_assoc hg
-/
theorem lift'_lift_assoc {g : Set α -> Filter β} {h : Set β -> Set γ} (hg : Monotone g) :
    (f.lift g).lift' h = f.lift fun s => (g s).lift' h :=
  lift_assoc hg

/--
theorem `lift_lift'_same_le_lift'` / 定理 `lift_lift'_same_le_lift'`

English:
theorem lift_lift'_same_le_lift'
  given: {g : Set α -> Set α -> Set β}
  proof: lift_lift_same_le_lift

中文:
定理 lift_lift'_same_le_lift'
  条件: {g : 集合 α -> 集合 α -> 集合 β}
  证明: lift_lift_same_le_lift
-/
theorem lift_lift'_same_le_lift' {g : Set α -> Set α -> Set β} :
    (f.lift fun s => f.lift' (g s)) <= f.lift' fun s => g s s :=
  lift_lift_same_le_lift

/--
theorem `lift_lift'_same_eq_lift'` / 定理 `lift_lift'_same_eq_lift'`

English:
theorem lift_lift'_same_eq_lift'
  statement: {g : Set α -> Set α -> Set β} (hg₁ : forall s, Monotone fun t => g s t)
  proof: lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)

中文:
定理 lift_lift'_same_eq_lift'
  结论: {g : 集合 α -> 集合 α -> 集合 β} (hg₁ : 对任意 s, 递增 fun t => g s t)
  证明: lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)
-/
theorem lift_lift'_same_eq_lift' {g : Set α -> Set α -> Set β} (hg₁ : forall s, Monotone fun t => g s t)
    (hg₂ : forall t, Monotone fun s => g s t) :
    (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s :=
  lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)

/--
theorem `lift'_inf_principal_eq` / 定理 `lift'_inf_principal_eq`

English:
theorem lift'_inf_principal_eq
  given: {h : Set α -> Set β} {s : Set β}
  proof: by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, iInf_subtype', ← iInf_inf]

中文:
定理 lift'_inf_principal_eq
  条件: {h : 集合 α -> 集合 β} {s : 集合 β}
  证明: by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, iInf_subtype', ← iInf_inf]
-/
theorem lift'_inf_principal_eq {h : Set α -> Set β} {s : Set β} :
    f.lift' h ⊓ 𝓟 s = f.lift' fun t => h t inter s := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, iInf_subtype', ← iInf_inf]

/--
theorem `lift'_neBot_iff` / 定理 `lift'_neBot_iff`

English:
theorem lift'_neBot_iff
  given: (hh : Monotone h)
  statement: NeBot (f.lift' h) ↔ forall s in f, (h s).Nonempty
  proof: calc
    NeBot (f.lift' h) ↔ forall s in f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ forall s in f, (h s).Nonempty := by simp only [principal_neBot_iff]

@[simp]

中文:
定理 lift'_neBot_iff
  条件: (hh : 递增 h)
  结论: NeBot (f.lift' h) ↔ 对任意 s in f, (h s).非空
  证明: calc
    NeBot (f.lift' h) ↔ forall s in f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ forall s in f, (h s).Nonempty := by simp only [principal_neBot_iff]

@[simp]
-/
theorem lift'_neBot_iff (hh : Monotone h) : NeBot (f.lift' h) ↔ forall s in f, (h s).Nonempty :=
  calc
    NeBot (f.lift' h) ↔ forall s in f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ forall s in f, (h s).Nonempty := by simp only [principal_neBot_iff]

@[simp]
/--
theorem `lift'_id` / 定理 `lift'_id`

English:
theorem lift'_id
  given: {f : Filter α}
  statement: f.lift' id = f
  proof: lift_principal2

中文:
定理 lift'_id
  条件: {f : 滤子 α}
  结论: f.lift' id = f
  证明: lift_principal2
-/
theorem lift'_id {f : Filter α} : f.lift' id = f :=
  lift_principal2

/--
theorem `lift'_iInf` / 定理 `lift'_iInf`

English:
theorem lift'_iInf
  statement: [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Set β}
  proof: lift_iInf fun s t => by simp only [inf_principal, comp, hg]

中文:
定理 lift'_iInf
  结论: [非空 ι] {f : ι -> 滤子 α} {g : 集合 α -> 集合 β}
  证明: lift_iInf fun s t => by simp only [inf_principal, comp, hg]
-/
theorem lift'_iInf [Nonempty ι] {f : ι -> Filter α} {g : Set α -> Set β}
    (hg : forall s t, g (s inter t) = g s inter g t) : (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf fun s t => by simp only [inf_principal, comp, hg]

/--
theorem `lift'_iInf_of_map_univ` / 定理 `lift'_iInf_of_map_univ`

English:
theorem lift'_iInf_of_map_univ
  statement: {f : ι -> Filter α} {g : Set α -> Set β}
  proof: lift_iInf_of_map_univ (fun s t => by simp only [inf_principal, comp, hg])
    (by rw [Function.comp_apply, hg', principal_univ])

中文:
定理 lift'_iInf_of_map_univ
  结论: {f : ι -> 滤子 α} {g : 集合 α -> 集合 β}
  证明: lift_iInf_of_map_univ (fun s t => by simp only [inf_principal, comp, hg])
    (by rw [Function.comp_apply, hg', principal_univ])
-/
theorem lift'_iInf_of_map_univ {f : ι -> Filter α} {g : Set α -> Set β}
    (hg : forall {s t}, g (s inter t) = g s inter g t) (hg' : g univ = univ) :
    (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf_of_map_univ (fun s t => by simp only [inf_principal, comp, hg])
    (by rw [Function.comp_apply, hg', principal_univ])

/--
theorem `lift'_inf` / 定理 `lift'_inf`

English:
theorem lift'_inf
  given: (f g : Filter α) {s : Set α -> Set β} (hs : forall t₁ t₂, s (t₁ inter t₂) = s t₁ inter s t₂)
  proof: by
  rw [inf_eq_iInf]; rw [inf_eq_iInf]; rw [lift'_iInf hs]
  refine iInf_congr ?_
  rintro (_ | _) <;> rfl

中文:
定理 lift'_inf
  条件: (f g : 滤子 α) {s : 集合 α -> 集合 β} (hs : 对任意 t₁ t₂, s (t₁ inter t₂) = s t₁ inter s t₂)
  证明: by
  rw [inf_eq_iInf]; rw [inf_eq_iInf]; rw [lift'_iInf hs]
  refine iInf_congr ?_
  rintro (_ | _) <;> rfl
-/
theorem lift'_inf (f g : Filter α) {s : Set α -> Set β} (hs : forall t₁ t₂, s (t₁ inter t₂) = s t₁ inter s t₂) :
    (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s := by
  rw [inf_eq_iInf]; rw [inf_eq_iInf]; rw [lift'_iInf hs]
  refine iInf_congr ?_
  rintro (_ | _) <;> rfl

/--
theorem `lift'_inf_le` / 定理 `lift'_inf_le`

English:
theorem lift'_inf_le
  given: (f g : Filter α) (s : Set α -> Set β)
  proof: le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)

中文:
定理 lift'_inf_le
  条件: (f g : 滤子 α) (s : 集合 α -> 集合 β)
  证明: le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)
-/
theorem lift'_inf_le (f g : Filter α) (s : Set α -> Set β) :
    (f ⊓ g).lift' s <= f.lift' s ⊓ g.lift' s :=
  le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)

/--
theorem `comap_eq_lift'` / 定理 `comap_eq_lift'`

English:
theorem comap_eq_lift'
  given: {f : Filter β} {m : α -> β}
  statement: comap m f = f.lift' (preimage m)
  proof: Filter.ext fun _ => (mem_lift'_sets monotone_preimage).symm

中文:
定理 comap_eq_lift'
  条件: {f : 滤子 β} {m : α -> β}
  结论: comap m f = f.lift' (原像 m)
  证明: Filter.ext fun _ => (mem_lift'_sets monotone_preimage).symm

Depends on / 依赖: Filter, Filter.ext, _sets, mem_lift, monotone_preimage
-/
theorem comap_eq_lift' {f : Filter β} {m : α -> β} : comap m f = f.lift' (preimage m) :=
  Filter.ext fun _ => (mem_lift'_sets monotone_preimage).symm

end Lift'

section Prod

variable {f : Filter α}

/--
theorem `prod_def` / 定理 `prod_def`

English:
theorem prod_def
  given: {f : Filter α} {g : Filter β}
  proof: by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using! iInf_congr fun i => iInf_comm

alias mem_prod_same_iff := mem_prod_self_iff

中文:
定理 prod_def
  条件: {f : 滤子 α} {g : 滤子 β}
  证明: by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using! iInf_congr fun i => iInf_comm

alias mem_prod_same_iff := mem_prod_self_iff

Depends on / 依赖: Filter, Filter.lift, basis_sets, eq_biInf, f.basis_sets.prod, g.basis_sets, iInf_and, iInf_comm, iInf_congr, iInf_prod
-/
theorem prod_def {f : Filter α} {g : Filter β} :
    f ×ˢ g = f.lift fun s => g.lift' fun t => s ×ˢ t := by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using! iInf_congr fun i => iInf_comm

alias mem_prod_same_iff := mem_prod_self_iff

/--
theorem `prod_same_eq` / 定理 `prod_same_eq`

English:
theorem prod_same_eq
  statement: f ×ˢ f = f.lift' fun t : Set α => t ×ˢ t
  proof: f.basis_sets.prod_self.eq_biInf

中文:
定理 prod_same_eq
  结论: f ×ˢ f = f.lift' fun t : 集合 α => t ×ˢ t
  证明: f.basis_sets.prod_self.eq_biInf

Depends on / 依赖: basis_sets, eq_biInf, f.basis_sets.prod_self.eq_biInf, prod_self
-/
theorem prod_same_eq : f ×ˢ f = f.lift' fun t : Set α => t ×ˢ t :=
  f.basis_sets.prod_self.eq_biInf

/--
theorem `tendsto_prod_self_iff` / 定理 `tendsto_prod_self_iff`

English:
theorem tendsto_prod_self_iff
  given: {f : α × α -> β} {x : Filter α} {y : Filter β}
  proof: by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff]

中文:
定理 tendsto_prod_self_iff
  条件: {f : α × α -> β} {x : 滤子 α} {y : 滤子 β}
  证明: by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff]

Depends on / 依赖: mem_prod_same_iff, prod_sub_preimage_iff, tendsto_def
-/
theorem tendsto_prod_self_iff {f : α × α -> β} {x : Filter α} {y : Filter β} :
    Filter.Tendsto f (x ×ˢ x) y ↔ forall W in y, exists U in x, forall x x' : α, x in U -> x' in U -> f (x, x') in W := by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff]

variable {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}

/--
theorem `prod_lift_lift` / 定理 `prod_lift_lift`

English:
theorem prod_lift_lift
  statement: {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ -> Filter β₁}
  proof: by
  simp only [prod_def, lift_assoc hg₁]
  apply congr_arg; funext x
  rw [lift_comm]
  apply congr_arg; funext y
  apply lift'_lift_assoc hg₂

中文:
定理 prod_lift_lift
  结论: {f₁ : 滤子 α₁} {f₂ : 滤子 α₂} {g₁ : 集合 α₁ -> 滤子 β₁}
  证明: by
  simp only [prod_def, lift_assoc hg₁]
  apply congr_arg; funext x
  rw [lift_comm]
  apply congr_arg; funext y
  apply lift'_lift_assoc hg₂

Depends on / 依赖: _lift_assoc, congr_arg, lift_assoc, lift_comm, prod_def
-/
theorem prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ -> Filter β₁}
    {g₂ : Set α₂ -> Filter β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift g₁ ×ˢ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ˢ g₂ t := by
  simp only [prod_def, lift_assoc hg₁]
  apply congr_arg; funext x
  rw [lift_comm]
  apply congr_arg; funext y
  apply lift'_lift_assoc hg₂

/--
theorem `prod_lift'_lift'` / 定理 `prod_lift'_lift'`

English:
theorem prod_lift'_lift'
  statement: {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ -> Set β₁}
  proof: calc
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ˢ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      { simp only [prod_principal_principal] }

中文:
定理 prod_lift'_lift'
  结论: {f₁ : 滤子 α₁} {f₂ : 滤子 α₂} {g₁ : 集合 α₁ -> 集合 β₁}
  证明: calc
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ˢ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      { simp only [prod_principal_principal] }

Depends on / 依赖: monotone_principal, monotone_principal.comp, prod_lift_lift, prod_principal_principal
-/
theorem prod_lift'_lift' {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ -> Set β₁}
    {g₂ : Set α₂ -> Set β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' fun t => g₁ s ×ˢ g₂ t :=
  calc
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ˢ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      { simp only [prod_principal_principal] }

end Prod

end Filter
