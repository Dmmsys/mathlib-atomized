/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Constructions

/-!
# Neighborhoods relative to a subset

This file develops API on the relative versions `nhdsWithin` and `nhdsSetWithin` of `nhds` and
`nhdsSet`, which are defined in previous definition files.

Their basic properties studied in this file include the relationship between neighborhood filters
relative to a set and neighborhood filters in the corresponding subtype, and are in later files used
to develop relative versions `ContinuousOn` and `ContinuousWithinAt` of `Continuous` and
`ContinuousAt`.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝ˢ[t] s`: the filter `nhdsSetWithin s t` of neighborhoods of a set `s` within a set `t`.

-/

public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α]

/-!
## Properties of the neighborhood-within filter
-/

@[simp]
/--
theorem `nhds_bind_nhdsWithin` / 定理 `nhds_bind_nhdsWithin`

English:
theorem nhds_bind_nhdsWithin
  given: {a : α} {s : Set α}
  statement: ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a
  proof: bind_inf_principal.trans congr_arg₂ _ nhds_bind_nhds rfl

@[simp]

中文:
定理 nhds_bind_nhdsWithin
  条件: {a : α} {s : Set α}
  结论: ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a
  证明: bind_inf_principal.trans congr_arg₂ _ nhds_bind_nhds rfl

@[simp]

Depends on / 依赖: bind_inf_principal, bind_inf_principal.trans, nhds_bind_nhds
-/
theorem nhds_bind_nhdsWithin {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a :=
bind_inf_principal.trans congr_arg₂ _ nhds_bind_nhds rfl

@[simp]
/--
theorem `eventually_nhds_nhdsWithin` / 定理 `eventually_nhds_nhdsWithin`

English:
theorem eventually_nhds_nhdsWithin
  given: {a : α} {s : Set α} {p : α -> Prop}
  proof: Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }

中文:
定理 eventually_nhds_nhdsWithin
  条件: {a : α} {s : Set α} {p : α -> 命题}
  证明: Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }

Depends on / 依赖: Filter, Filter.ext_iff, ext_iff, nhds_bind_nhdsWithin
-/
theorem eventually_nhds_nhdsWithin {a : α} {s : Set α} {p : α -> Prop} :
    (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in 𝓝[s] a, p x :=
  Filter.ext_iff.1 nhds_bind_nhdsWithin { x | p x }

/--
theorem `eventually_nhdsWithin_iff` / 定理 `eventually_nhdsWithin_iff`

English:
theorem eventually_nhdsWithin_iff
  given: {a : α} {s : Set α} {p : α -> Prop}
  proof: eventually_inf_principal

中文:
定理 eventually_nhdsWithin_iff
  条件: {a : α} {s : Set α} {p : α -> 命题}
  证明: eventually_inf_principal

Depends on / 依赖: eventually_inf_principal
-/
theorem eventually_nhdsWithin_iff {a : α} {s : Set α} {p : α -> Prop} :
    (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x :=
  eventually_inf_principal

/--
theorem `frequently_nhdsWithin_iff` / 定理 `frequently_nhdsWithin_iff`

English:
theorem frequently_nhdsWithin_iff
  given: {z : α} {s : Set α} {p : α -> Prop}
  proof: frequently_inf_principal.trans by simp only [and_comm]

中文:
定理 frequently_nhdsWithin_iff
  条件: {z : α} {s : Set α} {p : α -> 命题}
  证明: frequently_inf_principal.trans by simp only [and_comm]

Depends on / 依赖: and_comm, frequently_inf_principal, frequently_inf_principal.trans
-/
theorem frequently_nhdsWithin_iff {z : α} {s : Set α} {p : α -> Prop} :
    (existsᶠ x in 𝓝[s] z, p x) ↔ existsᶠ x in 𝓝 z, p x ∧ x in s :=
frequently_inf_principal.trans by simp only [and_comm]

/--
theorem `mem_closure_ne_iff_frequently_within` / 定理 `mem_closure_ne_iff_frequently_within`

English:
theorem mem_closure_ne_iff_frequently_within
  given: {z : α} {s : Set α}
  proof: by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]

@[simp]

中文:
定理 mem_closure_ne_iff_frequently_within
  条件: {z : α} {s : Set α}
  证明: by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]

@[simp]

Depends on / 依赖: frequently_nhdsWithin_iff, mem_closure_iff_frequently
-/
theorem mem_closure_ne_iff_frequently_within {z : α} {s : Set α} :
    z in closure (s \ {z}) ↔ existsᶠ x in 𝓝[!=] z, x in s := by
  simp [mem_closure_iff_frequently, frequently_nhdsWithin_iff]

@[simp]
/--
theorem `eventually_eventually_nhdsWithin` / 定理 `eventually_eventually_nhdsWithin`

English:
theorem eventually_eventually_nhdsWithin
  given: {a : α} {s : Set α} {p : α -> Prop}
  proof: by
  refine ⟨fun h => ?_, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h ⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

@[simp]

中文:
定理 eventually_eventually_nhdsWithin
  条件: {a : α} {s : Set α} {p : α -> 命题}
  证明: by
  refine ⟨fun h => ?_, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h ⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

@[simp]

Depends on / 依赖: eventually_nhdsWithin_iff, eventually_nhds_nhdsWithin, filter_mono, h.mono, inf_le_left, self_of_nhds
-/
theorem eventually_eventually_nhdsWithin {a : α} {s : Set α} {p : α -> Prop} :
    (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in 𝓝[s] a, p x := by
  refine ⟨fun h => ?_, fun h => (eventually_nhds_nhdsWithin.2 h).filter_mono inf_le_left⟩
  simp only [eventually_nhdsWithin_iff] at h ⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

@[simp]
/--
theorem `eventually_mem_nhdsWithin_iff` / 定理 `eventually_mem_nhdsWithin_iff`

English:
theorem eventually_mem_nhdsWithin_iff
  given: {x : α} {s t : Set α}
  proof: eventually_eventually_nhdsWithin

中文:
定理 eventually_mem_nhdsWithin_iff
  条件: {x : α} {s t : Set α}
  证明: eventually_eventually_nhdsWithin

Depends on / 依赖: eventually_eventually_nhdsWithin
-/
theorem eventually_mem_nhdsWithin_iff {x : α} {s t : Set α} :
    (forallᶠ x' in 𝓝[s] x, t in 𝓝[s] x') ↔ t in 𝓝[s] x :=
  eventually_eventually_nhdsWithin

/--
theorem `nhdsWithin_eq` / 定理 `nhdsWithin_eq`

English:
theorem nhdsWithin_eq
  given: (a : α) (s : Set α)
  proof: ((nhds_basis_opens a).inf_principal s).eq_biInf

中文:
定理 nhdsWithin_eq
  条件: (a : α) (s : Set α)
  证明: ((nhds_basis_opens a).inf_principal s).eq_biInf

Depends on / 依赖: eq_biInf, inf_principal, nhds_basis_opens
-/
theorem nhdsWithin_eq (a : α) (s : Set α) :
    𝓝[s] a = ⨅ t in { t : Set α | a in t ∧ IsOpen t }, 𝓟 (t inter s) :=
  ((nhds_basis_opens a).inf_principal s).eq_biInf

/--
lemma `nhdsWithin_univ` / 引理 `nhdsWithin_univ`

English:
lemma nhdsWithin_univ
  given: (a : α)
  statement: 𝓝[Set.univ] a = 𝓝 a
  proof: by
  rw [nhdsWithin]; rw [principal_univ]; rw [inf_top_eq]

中文:
引理 nhdsWithin_univ
  条件: (a : α)
  结论: 𝓝[Set.univ] a = 𝓝 a
  证明: by
  rw [nhdsWithin]; rw [principal_univ]; rw [inf_top_eq]
-/
@[simp] lemma nhdsWithin_univ (a : α) : 𝓝[Set.univ] a = 𝓝 a := by
  rw [nhdsWithin]; rw [principal_univ]; rw [inf_top_eq]

/--
theorem `nhdsWithin_hasBasis` / 定理 `nhdsWithin_hasBasis`

English:
theorem nhdsWithin_hasBasis
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} {a : α}
  proof: h.inf_principal t

中文:
定理 nhdsWithin_hasBasis
  结论: {ι : Sort*} {p : ι -> 命题} {s : ι -> Set α} {a : α}
  证明: h.inf_principal t

Depends on / 依赖: h.inf_principal, inf_principal
-/
theorem nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α} {a : α}
    (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p fun i => s i inter t :=
  h.inf_principal t

/--
theorem `nhdsWithin_basis_open` / 定理 `nhdsWithin_basis_open`

English:
theorem nhdsWithin_basis_open
  given: (a : α) (t : Set α)
  proof: nhdsWithin_hasBasis (nhds_basis_opens a) t

中文:
定理 nhdsWithin_basis_open
  条件: (a : α) (t : Set α)
  证明: nhdsWithin_hasBasis (nhds_basis_opens a) t

Depends on / 依赖: nhdsWithin_hasBasis, nhds_basis_opens
-/
theorem nhdsWithin_basis_open (a : α) (t : Set α) :
    (𝓝[t] a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t :=
  nhdsWithin_hasBasis (nhds_basis_opens a) t

/--
theorem `mem_nhdsWithin` / 定理 `mem_nhdsWithin`

English:
theorem mem_nhdsWithin
  given: {t : Set α} {a : α} {s : Set α}
  proof: by
  simpa only [and_assoc, and_left_comm] using (nhdsWithin_basis_open a s).mem_iff

中文:
定理 mem_nhdsWithin
  条件: {t : Set α} {a : α} {s : Set α}
  证明: by
  simpa only [and_assoc, and_left_comm] using (nhdsWithin_basis_open a s).mem_iff

Depends on / 依赖: and_assoc, and_left_comm, mem_iff, nhdsWithin_basis_open
-/
theorem mem_nhdsWithin {t : Set α} {a : α} {s : Set α} :
    t in 𝓝[s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t := by
  simpa only [and_assoc, and_left_comm] using (nhdsWithin_basis_open a s).mem_iff

/--
theorem `mem_nhdsWithin_iff_exists_mem_nhds_inter` / 定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`

English:
theorem mem_nhdsWithin_iff_exists_mem_nhds_inter
  given: {t : Set α} {a : α} {s : Set α}
  proof: (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff

中文:
定理 mem_nhdsWithin_iff_exists_mem_nhds_inter
  条件: {t : Set α} {a : α} {s : Set α}
  证明: (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff

Depends on / 依赖: basis_sets, mem_iff, nhdsWithin_hasBasis
-/
theorem mem_nhdsWithin_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} :
    t in 𝓝[s] a ↔ exists u in 𝓝 a, u inter s subseteq t :=
  (nhdsWithin_hasBasis (𝓝 a).basis_sets s).mem_iff

/--
theorem `sdiff_mem_nhdsWithin_compl` / 定理 `sdiff_mem_nhdsWithin_compl`

English:
theorem sdiff_mem_nhdsWithin_compl
  given: {x : α} {s : Set α} (hs : s in 𝓝 x) (t : Set α)
  proof: sdiff_mem_inf_principal_compl hs t

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_compl := sdiff_mem_nhdsWithin_compl

中文:
定理 sdiff_mem_nhdsWithin_compl
  条件: {x : α} {s : Set α} (hs : s in 𝓝 x) (t : Set α)
  证明: sdiff_mem_inf_principal_compl hs t

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_compl := sdiff_mem_nhdsWithin_compl

Depends on / 依赖: sdiff_mem_inf_principal_compl
-/
theorem sdiff_mem_nhdsWithin_compl {x : α} {s : Set α} (hs : s in 𝓝 x) (t : Set α) :
    s \ t in 𝓝[tᶜ] x :=
  sdiff_mem_inf_principal_compl hs t

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_compl := sdiff_mem_nhdsWithin_compl

/--
theorem `sdiff_mem_nhdsWithin_sdiff` / 定理 `sdiff_mem_nhdsWithin_sdiff`

English:
theorem sdiff_mem_nhdsWithin_sdiff
  given: {x : α} {s t : Set α} (hs : s in 𝓝[t] x) (t' : Set α)
  proof: by
  rw [nhdsWithin]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_diff := sdiff_mem_nhdsWithin_sdiff

中文:
定理 sdiff_mem_nhdsWithin_sdiff
  条件: {x : α} {s t : Set α} (hs : s in 𝓝[t] x) (t' : Set α)
  证明: by
  rw [nhdsWithin]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_diff := sdiff_mem_nhdsWithin_sdiff

Depends on / 依赖: inf_assoc, inf_principal, inter_mem_inf, mem_principal_self, nhdsWithin, sdiff_eq
-/
theorem sdiff_mem_nhdsWithin_sdiff {x : α} {s t : Set α} (hs : s in 𝓝[t] x) (t' : Set α) :
    s \ t' in 𝓝[t \ t'] x := by
  rw [nhdsWithin]; rw [sdiff_eq]; rw [sdiff_eq]; rw [← inf_principal]; rw [← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

@[deprecated (since := "2026-06-03")] alias diff_mem_nhdsWithin_diff := sdiff_mem_nhdsWithin_sdiff

/--
theorem `nhds_of_nhdsWithin_of_nhds` / 定理 `nhds_of_nhdsWithin_of_nhds`

English:
theorem nhds_of_nhdsWithin_of_nhds
  given: {s t : Set α} {a : α} (h1 : s in 𝓝 a) (h2 : t in 𝓝[s] a)
  proof: by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (𝓝 a).sets_of_superset ((𝓝 a).inter_sets Hw h1) hw

中文:
定理 nhds_of_nhdsWithin_of_nhds
  条件: {s t : Set α} {a : α} (h1 : s in 𝓝 a) (h2 : t in 𝓝[s] a)
  证明: by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (𝓝 a).sets_of_superset ((𝓝 a).inter_sets Hw h1) hw

Depends on / 依赖: inter_sets, mem_nhdsWithin_iff_exists_mem_nhds_inter, mem_nhdsWithin_iff_exists_mem_nhds_inter.mp, sets_of_superset
-/
theorem nhds_of_nhdsWithin_of_nhds {s t : Set α} {a : α} (h1 : s in 𝓝 a) (h2 : t in 𝓝[s] a) :
    t in 𝓝 a := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (𝓝 a).sets_of_superset ((𝓝 a).inter_sets Hw h1) hw

/--
theorem `mem_nhdsWithin_iff_eventually` / 定理 `mem_nhdsWithin_iff_eventually`

English:
theorem mem_nhdsWithin_iff_eventually
  given: {s t : Set α} {x : α}
  proof: eventually_inf_principal

中文:
定理 mem_nhdsWithin_iff_eventually
  条件: {s t : Set α} {x : α}
  证明: eventually_inf_principal

Depends on / 依赖: eventually_inf_principal
-/
theorem mem_nhdsWithin_iff_eventually {s t : Set α} {x : α} :
    t in 𝓝[s] x ↔ forallᶠ y in 𝓝 x, y in s -> y in t :=
  eventually_inf_principal

/--
theorem `mem_nhdsWithin_iff_eventuallyEq` / 定理 `mem_nhdsWithin_iff_eventuallyEq`

English:
theorem mem_nhdsWithin_iff_eventuallyEq
  given: {s t : Set α} {x : α}
  proof: by
  simp_rw [mem_nhdsWithin_iff_eventually, eventuallyEq_set, mem_inter_iff, iff_self_and]

中文:
定理 mem_nhdsWithin_iff_eventuallyEq
  条件: {s t : Set α} {x : α}
  证明: by
  simp_rw [mem_nhdsWithin_iff_eventually, eventuallyEq_set, mem_inter_iff, iff_self_and]

Depends on / 依赖: eventuallyEq_set, iff_self_and, mem_inter_iff, mem_nhdsWithin_iff_eventually, simp_rw
-/
theorem mem_nhdsWithin_iff_eventuallyEq {s t : Set α} {x : α} :
    t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α) := by
  simp_rw [mem_nhdsWithin_iff_eventually, eventuallyEq_set, mem_inter_iff, iff_self_and]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_nhdsWithin_inter_self` / 引理 `mem_nhdsWithin_inter_self`

English:
lemma mem_nhdsWithin_inter_self
  given: {s t : Set α} {x : α}
  statement: t in 𝓝[s inter t] x
  proof: mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_assoc]

中文:
引理 mem_nhdsWithin_inter_self
  条件: {s t : Set α} {x : α}
  结论: t in 𝓝[s inter t] x
  证明: mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_assoc]

Depends on / 依赖: inter_assoc, mem_nhdsWithin_iff_eventuallyEq, mem_nhdsWithin_iff_eventuallyEq.mpr
-/
lemma mem_nhdsWithin_inter_self {s t : Set α} {x : α} : t in 𝓝[s inter t] x :=
mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_nhdsWithin_self_inter` / 引理 `mem_nhdsWithin_self_inter`

English:
lemma mem_nhdsWithin_self_inter
  given: {s t : Set α} {x : α}
  statement: s in 𝓝[s inter t] x
  proof: mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_comm s t, inter_assoc]

中文:
引理 mem_nhdsWithin_self_inter
  条件: {s t : Set α} {x : α}
  结论: s in 𝓝[s inter t] x
  证明: mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_comm s t, inter_assoc]

Depends on / 依赖: inter_assoc, inter_comm, mem_nhdsWithin_iff_eventuallyEq, mem_nhdsWithin_iff_eventuallyEq.mpr
-/
lemma mem_nhdsWithin_self_inter {s t : Set α} {x : α} : s in 𝓝[s inter t] x :=
mem_nhdsWithin_iff_eventuallyEq.mpr by simp [inter_comm s t, inter_assoc]

/--
theorem `nhdsWithin_eq_iff_eventuallyEq` / 定理 `nhdsWithin_eq_iff_eventuallyEq`

English:
theorem nhdsWithin_eq_iff_eventuallyEq
  given: {s t : Set α} {x : α}
  statement: 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
  proof: set_eventuallyEq_iff_inf_principal.symm

中文:
定理 nhdsWithin_eq_iff_eventuallyEq
  条件: {s t : Set α} {x : α}
  结论: 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
  证明: set_eventuallyEq_iff_inf_principal.symm

Depends on / 依赖: set_eventuallyEq_iff_inf_principal, set_eventuallyEq_iff_inf_principal.symm
-/
theorem nhdsWithin_eq_iff_eventuallyEq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t :=
  set_eventuallyEq_iff_inf_principal.symm

/--
theorem `nhdsWithin_le_iff` / 定理 `nhdsWithin_le_iff`

English:
theorem nhdsWithin_le_iff
  given: {s t : Set α} {x : α}
  statement: 𝓝[s] x <= 𝓝[t] x ↔ t in 𝓝[s] x
  proof: set_eventuallyLE_iff_inf_principal_le.symm.trans set_eventuallyLE_iff_mem_inf_principal

中文:
定理 nhdsWithin_le_iff
  条件: {s t : Set α} {x : α}
  结论: 𝓝[s] x <= 𝓝[t] x ↔ t in 𝓝[s] x
  证明: set_eventuallyLE_iff_inf_principal_le.symm.trans set_eventuallyLE_iff_mem_inf_principal

Depends on / 依赖: set_eventuallyLE_iff_inf_principal_le, set_eventuallyLE_iff_inf_principal_le.symm.trans, set_eventuallyLE_iff_mem_inf_principal
-/
theorem nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝[t] x ↔ t in 𝓝[s] x :=
  set_eventuallyLE_iff_inf_principal_le.symm.trans set_eventuallyLE_iff_mem_inf_principal

/--
theorem `preimage_nhdsWithin_coinduced'` / 定理 `preimage_nhdsWithin_coinduced'`

English:
theorem preimage_nhdsWithin_coinduced'
  statement: {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
  proof: by
  lift a to t using h
  replace hs : (fun x : t => X x) ⁻¹' s in 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]

中文:
定理 preimage_nhdsWithin_coinduced'
  结论: {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
  证明: by
  lift a to t using h
  replace hs : (fun x : t => X x) ⁻¹' s in 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]

Depends on / 依赖: map_nhds_subtype_val, mem_map, preimage_nhds_coinduced, replace
-/
theorem preimage_nhdsWithin_coinduced' {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
    (hs : s in @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s in 𝓝[t] a := by
  lift a to t using h
  replace hs : (fun x : t => X x) ⁻¹' s in 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]

/--
theorem `mem_nhdsWithin_of_mem_nhds` / 定理 `mem_nhdsWithin_of_mem_nhds`

English:
theorem mem_nhdsWithin_of_mem_nhds
  given: {s t : Set α} {a : α} (h : s in 𝓝 a)
  statement: s in 𝓝[t] a
  proof: mem_inf_of_left h

中文:
定理 mem_nhdsWithin_of_mem_nhds
  条件: {s t : Set α} {a : α} (h : s in 𝓝 a)
  结论: s in 𝓝[t] a
  证明: mem_inf_of_left h

Depends on / 依赖: mem_inf_of_left
-/
theorem mem_nhdsWithin_of_mem_nhds {s t : Set α} {a : α} (h : s in 𝓝 a) : s in 𝓝[t] a :=
  mem_inf_of_left h

/--
theorem `self_mem_nhdsWithin` / 定理 `self_mem_nhdsWithin`

English:
theorem self_mem_nhdsWithin
  given: {a : α} {s : Set α}
  statement: s in 𝓝[s] a
  proof: mem_inf_of_right (mem_principal_self s)

中文:
定理 self_mem_nhdsWithin
  条件: {a : α} {s : Set α}
  结论: s in 𝓝[s] a
  证明: mem_inf_of_right (mem_principal_self s)

Depends on / 依赖: mem_inf_of_right, mem_principal_self
-/
theorem self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s] a :=
  mem_inf_of_right (mem_principal_self s)

/--
theorem `eventually_mem_nhdsWithin` / 定理 `eventually_mem_nhdsWithin`

English:
theorem eventually_mem_nhdsWithin
  given: {a : α} {s : Set α}
  statement: forallᶠ x in 𝓝[s] a, x in s
  proof: self_mem_nhdsWithin

中文:
定理 eventually_mem_nhdsWithin
  条件: {a : α} {s : Set α}
  结论: 对任意ᶠ x in 𝓝[s] a, x in s
  证明: self_mem_nhdsWithin

Depends on / 依赖: self_mem_nhdsWithin
-/
theorem eventually_mem_nhdsWithin {a : α} {s : Set α} : forallᶠ x in 𝓝[s] a, x in s :=
  self_mem_nhdsWithin

/--
theorem `inter_mem_nhdsWithin` / 定理 `inter_mem_nhdsWithin`

English:
theorem inter_mem_nhdsWithin
  given: (s : Set α) {t : Set α} {a : α} (h : t in 𝓝 a)
  statement: s inter t in 𝓝[s] a
  proof: inter_mem self_mem_nhdsWithin (mem_inf_of_left h)

中文:
定理 inter_mem_nhdsWithin
  条件: (s : Set α) {t : Set α} {a : α} (h : t in 𝓝 a)
  结论: s inter t in 𝓝[s] a
  证明: inter_mem self_mem_nhdsWithin (mem_inf_of_left h)

Depends on / 依赖: inter_mem, mem_inf_of_left, self_mem_nhdsWithin
-/
theorem inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a :=
  inter_mem self_mem_nhdsWithin (mem_inf_of_left h)

/--
theorem `pure_le_nhdsWithin` / 定理 `pure_le_nhdsWithin`

English:
theorem pure_le_nhdsWithin
  given: {a : α} {s : Set α} (ha : a in s)
  statement: pure a <= 𝓝[s] a
  proof: le_inf (pure_le_nhds a) (le_principal_iff.2 ha)

中文:
定理 pure_le_nhdsWithin
  条件: {a : α} {s : Set α} (ha : a in s)
  结论: pure a <= 𝓝[s] a
  证明: le_inf (pure_le_nhds a) (le_principal_iff.2 ha)

Depends on / 依赖: le_inf, le_principal_iff, pure_le_nhds
-/
theorem pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s) : pure a <= 𝓝[s] a :=
  le_inf (pure_le_nhds a) (le_principal_iff.2 ha)

/--
theorem `mem_of_mem_nhdsWithin` / 定理 `mem_of_mem_nhdsWithin`

English:
theorem mem_of_mem_nhdsWithin
  given: {a : α} {s t : Set α} (ha : a in s) (ht : t in 𝓝[s] a)
  statement: a in t
  proof: pure_le_nhdsWithin ha ht

中文:
定理 mem_of_mem_nhdsWithin
  条件: {a : α} {s t : Set α} (ha : a in s) (ht : t in 𝓝[s] a)
  结论: a in t
  证明: pure_le_nhdsWithin ha ht

Depends on / 依赖: pure_le_nhdsWithin
-/
theorem mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha : a in s) (ht : t in 𝓝[s] a) : a in t :=
  pure_le_nhdsWithin ha ht

/--
theorem `Filter.Eventually.self_of_nhdsWithin` / 定理 `Filter.Eventually.self_of_nhdsWithin`

English:
theorem Filter.Eventually.self_of_nhdsWithin
  statement: {p : α -> Prop} {s : Set α} {x : α}
  proof: mem_of_mem_nhdsWithin hx h

中文:
定理 Filter.Eventually.self_of_nhdsWithin
  结论: {p : α -> 命题} {s : Set α} {x : α}
  证明: mem_of_mem_nhdsWithin hx h

Depends on / 依赖: mem_of_mem_nhdsWithin
-/
theorem Filter.Eventually.self_of_nhdsWithin {p : α -> Prop} {s : Set α} {x : α}
    (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in s) : p x :=
  mem_of_mem_nhdsWithin hx h

/--
theorem `tendsto_const_nhdsWithin` / 定理 `tendsto_const_nhdsWithin`

English:
theorem tendsto_const_nhdsWithin
  given: {l : Filter β} {s : Set α} {a : α} (ha : a in s)
  proof: tendsto_const_pure.mono_right pure_le_nhdsWithin ha

中文:
定理 tendsto_const_nhdsWithin
  条件: {l : Filter β} {s : Set α} {a : α} (ha : a in s)
  证明: tendsto_const_pure.mono_right pure_le_nhdsWithin ha

Depends on / 依赖: mono_right, pure_le_nhdsWithin, tendsto_const_pure, tendsto_const_pure.mono_right
-/
theorem tendsto_const_nhdsWithin {l : Filter β} {s : Set α} {a : α} (ha : a in s) :
    Tendsto (fun _ : β => a) l (𝓝[s] a) :=
tendsto_const_pure.mono_right pure_le_nhdsWithin ha

/--
theorem `nhdsWithin_restrict''` / 定理 `nhdsWithin_restrict''`

English:
theorem nhdsWithin_restrict''
  given: {a : α} (s : Set α) {t : Set α} (h : t in 𝓝[s] a)
  proof: le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr Set.inter_subset_left))

中文:
定理 nhdsWithin_restrict''
  条件: {a : α} (s : Set α) {t : Set α} (h : t in 𝓝[s] a)
  证明: le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr Set.inter_subset_left))

Depends on / 依赖: Set.inter_subset_left, inf_le_inf_left, inf_le_left, inter_mem, inter_subset_left, le_antisymm, le_inf, le_principal_iff, le_principal_iff.mpr, principal_mono, principal_mono.mpr, self_mem_nhdsWithin
-/
theorem nhdsWithin_restrict'' {a : α} (s : Set α) {t : Set α} (h : t in 𝓝[s] a) :
    𝓝[s] a = 𝓝[s inter t] a :=
  le_antisymm (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhdsWithin h)))
    (inf_le_inf_left _ (principal_mono.mpr Set.inter_subset_left))

/--
theorem `nhdsWithin_restrict'` / 定理 `nhdsWithin_restrict'`

English:
theorem nhdsWithin_restrict'
  given: {a : α} (s : Set α) {t : Set α} (h : t in 𝓝 a)
  statement: 𝓝[s] a = 𝓝[s inter t] a
  proof: nhdsWithin_restrict'' s mem_inf_of_left h

中文:
定理 nhdsWithin_restrict'
  条件: {a : α} (s : Set α) {t : Set α} (h : t in 𝓝 a)
  结论: 𝓝[s] a = 𝓝[s inter t] a
  证明: nhdsWithin_restrict'' s mem_inf_of_left h

Depends on / 依赖: mem_inf_of_left, nhdsWithin_restrict
-/
theorem nhdsWithin_restrict' {a : α} (s : Set α) {t : Set α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a :=
nhdsWithin_restrict'' s mem_inf_of_left h

/--
theorem `nhdsWithin_restrict` / 定理 `nhdsWithin_restrict`

English:
theorem nhdsWithin_restrict
  given: {a : α} (s : Set α) {t : Set α} (h₀ : a in t) (h₁ : IsOpen t)
  proof: nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)

中文:
定理 nhdsWithin_restrict
  条件: {a : α} (s : Set α) {t : Set α} (h₀ : a in t) (h₁ : IsOpen t)
  证明: nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, mem_nhds, nhdsWithin_restrict
-/
theorem nhdsWithin_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a in t) (h₁ : IsOpen t) :
    𝓝[s] a = 𝓝[s inter t] a :=
  nhdsWithin_restrict' s (IsOpen.mem_nhds h₁ h₀)

/--
theorem `nhdsWithin_le_of_mem` / 定理 `nhdsWithin_le_of_mem`

English:
theorem nhdsWithin_le_of_mem
  given: {a : α} {s t : Set α} (h : s in 𝓝[t] a)
  statement: 𝓝[t] a <= 𝓝[s] a
  proof: nhdsWithin_le_iff.mpr h

中文:
定理 nhdsWithin_le_of_mem
  条件: {a : α} {s t : Set α} (h : s in 𝓝[t] a)
  结论: 𝓝[t] a <= 𝓝[s] a
  证明: nhdsWithin_le_iff.mpr h

Depends on / 依赖: nhdsWithin_le_iff, nhdsWithin_le_iff.mpr
-/
theorem nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a :=
  nhdsWithin_le_iff.mpr h

/--
theorem `nhdsWithin_le_nhds` / 定理 `nhdsWithin_le_nhds`

English:
theorem nhdsWithin_le_nhds
  given: {a : α} {s : Set α}
  statement: 𝓝[s] a <= 𝓝 a
  proof: by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem

中文:
定理 nhdsWithin_le_nhds
  条件: {a : α} {s : Set α}
  结论: 𝓝[s] a <= 𝓝 a
  证明: by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem

Depends on / 依赖: nhdsWithin_le_of_mem, nhdsWithin_univ, univ_mem
-/
theorem nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝 a := by
  rw [← nhdsWithin_univ]
  apply nhdsWithin_le_of_mem
  exact univ_mem

/--
theorem `nhdsWithin_eq_nhdsWithin'` / 定理 `nhdsWithin_eq_nhdsWithin'`

English:
theorem nhdsWithin_eq_nhdsWithin'
  given: {a : α} {s t u : Set α} (hs : s in 𝓝 a) (h₂ : t inter s = u inter s)
  proof: by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]

中文:
定理 nhdsWithin_eq_nhdsWithin'
  条件: {a : α} {s t u : Set α} (hs : s in 𝓝 a) (h₂ : t inter s = u inter s)
  证明: by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]

Depends on / 依赖: nhdsWithin_restrict
-/
theorem nhdsWithin_eq_nhdsWithin' {a : α} {s t u : Set α} (hs : s in 𝓝 a) (h₂ : t inter s = u inter s) :
    𝓝[t] a = 𝓝[u] a := by rw [nhdsWithin_restrict' t hs, nhdsWithin_restrict' u hs, h₂]

/--
theorem `nhdsWithin_eq_nhdsWithin` / 定理 `nhdsWithin_eq_nhdsWithin`

English:
theorem nhdsWithin_eq_nhdsWithin
  statement: {a : α} {s t u : Set α} (h₀ : a in s) (h₁ : IsOpen s)
  proof: by
  rw [nhdsWithin_restrict t h₀ h₁]; rw [nhdsWithin_restrict u h₀ h₁]; rw [h₂]

中文:
定理 nhdsWithin_eq_nhdsWithin
  结论: {a : α} {s t u : Set α} (h₀ : a in s) (h₁ : IsOpen s)
  证明: by
  rw [nhdsWithin_restrict t h₀ h₁]; rw [nhdsWithin_restrict u h₀ h₁]; rw [h₂]

Depends on / 依赖: nhdsWithin_restrict
-/
theorem nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set α} (h₀ : a in s) (h₁ : IsOpen s)
    (h₂ : t inter s = u inter s) : 𝓝[t] a = 𝓝[u] a := by
  rw [nhdsWithin_restrict t h₀ h₁]; rw [nhdsWithin_restrict u h₀ h₁]; rw [h₂]

/--
theorem `nhdsWithin_eq_nhds` / 定理 `nhdsWithin_eq_nhds`

English:
theorem nhdsWithin_eq_nhds
  given: {a : α} {s : Set α}
  statement: 𝓝[s] a = 𝓝 a ↔ s in 𝓝 a
  proof: inf_eq_left.trans le_principal_iff

中文:
定理 nhdsWithin_eq_nhds
  条件: {a : α} {s : Set α}
  结论: 𝓝[s] a = 𝓝 a ↔ s in 𝓝 a
  证明: inf_eq_left.trans le_principal_iff
-/
@[simp] theorem nhdsWithin_eq_nhds {a : α} {s : Set α} : 𝓝[s] a = 𝓝 a ↔ s in 𝓝 a :=
  inf_eq_left.trans le_principal_iff

/--
theorem `IsOpen.nhdsWithin_eq` / 定理 `IsOpen.nhdsWithin_eq`

English:
theorem IsOpen.nhdsWithin_eq
  given: {a : α} {s : Set α} (h : IsOpen s) (ha : a in s)
  statement: 𝓝[s] a = 𝓝 a
  proof: nhdsWithin_eq_nhds.2 h.mem_nhds ha

中文:
定理 IsOpen.nhdsWithin_eq
  条件: {a : α} {s : Set α} (h : IsOpen s) (ha : a in s)
  结论: 𝓝[s] a = 𝓝 a
  证明: nhdsWithin_eq_nhds.2 h.mem_nhds ha

Depends on / 依赖: h.mem_nhds, mem_nhds, nhdsWithin_eq_nhds
-/
theorem IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a in s) : 𝓝[s] a = 𝓝 a :=
nhdsWithin_eq_nhds.2 h.mem_nhds ha

/--
theorem `preimage_nhds_within_coinduced` / 定理 `preimage_nhds_within_coinduced`

English:
theorem preimage_nhds_within_coinduced
  statement: {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
  proof: by
  rw [← ht.nhdsWithin_eq h]
  exact preimage_nhdsWithin_coinduced' h hs

@[simp]

中文:
定理 preimage_nhds_within_coinduced
  结论: {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
  证明: by
  rw [← ht.nhdsWithin_eq h]
  exact preimage_nhdsWithin_coinduced' h hs

@[simp]

Depends on / 依赖: ht.nhdsWithin_eq, nhdsWithin_eq, preimage_nhdsWithin_coinduced
-/
theorem preimage_nhds_within_coinduced {X : α -> β} {s : Set β} {t : Set α} {a : α} (h : a in t)
    (ht : IsOpen t)
    (hs : s in @nhds β (.coinduced (fun x : t => X x) inferInstance) (X a)) :
    X ⁻¹' s in 𝓝 a := by
  rw [← ht.nhdsWithin_eq h]
  exact preimage_nhdsWithin_coinduced' h hs

@[simp]
/--
theorem `nhdsWithin_empty` / 定理 `nhdsWithin_empty`

English:
theorem nhdsWithin_empty
  given: (a : α)
  statement: 𝓝[∅] a = ⊥
  proof: by rw [nhdsWithin, principal_empty, inf_bot_eq]

中文:
定理 nhdsWithin_empty
  条件: (a : α)
  结论: 𝓝[∅] a = ⊥
  证明: by rw [nhdsWithin, principal_empty, inf_bot_eq]

Depends on / 依赖: inf_bot_eq, nhdsWithin, principal_empty
-/
theorem nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥ := by rw [nhdsWithin, principal_empty, inf_bot_eq]

/--
theorem `nhdsWithin_union` / 定理 `nhdsWithin_union`

English:
theorem nhdsWithin_union
  given: (a : α) (s t : Set α)
  statement: 𝓝[s union t] a = 𝓝[s] a ⊔ 𝓝[t] a
  proof: by
  delta nhdsWithin
  rw [← inf_sup_left]; rw [sup_principal]

中文:
定理 nhdsWithin_union
  条件: (a : α) (s t : Set α)
  结论: 𝓝[s union t] a = 𝓝[s] a ⊔ 𝓝[t] a
  证明: by
  delta nhdsWithin
  rw [← inf_sup_left]; rw [sup_principal]

Depends on / 依赖: inf_sup_left, nhdsWithin, sup_principal
-/
theorem nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] a = 𝓝[s] a ⊔ 𝓝[t] a := by
  delta nhdsWithin
  rw [← inf_sup_left]; rw [sup_principal]

/--
theorem `nhds_eq_nhdsWithin_sup_nhdsWithin` / 定理 `nhds_eq_nhdsWithin_sup_nhdsWithin`

English:
theorem nhds_eq_nhdsWithin_sup_nhdsWithin
  given: (b : α) {I₁ I₂ : Set α} (hI : Set.univ = I₁ union I₂)
  proof: by
  rw [← nhdsWithin_univ b]; rw [hI]; rw [nhdsWithin_union]

中文:
定理 nhds_eq_nhdsWithin_sup_nhdsWithin
  条件: (b : α) {I₁ I₂ : Set α} (hI : Set.univ = I₁ union I₂)
  证明: by
  rw [← nhdsWithin_univ b]; rw [hI]; rw [nhdsWithin_union]

Depends on / 依赖: nhdsWithin_union, nhdsWithin_univ
-/
theorem nhds_eq_nhdsWithin_sup_nhdsWithin (b : α) {I₁ I₂ : Set α} (hI : Set.univ = I₁ union I₂) :
    nhds b = nhdsWithin b I₁ ⊔ nhdsWithin b I₂ := by
  rw [← nhdsWithin_univ b]; rw [hI]; rw [nhdsWithin_union]

/--
lemma `inter_mem_nhdsWithin_inter` / 引理 `inter_mem_nhdsWithin_inter`

English:
lemma inter_mem_nhdsWithin_inter
  given: {a b c d : Set α} {x : α} (h : a in 𝓝[b] x) (h' : c in 𝓝[d] x)
  proof: inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')

中文:
引理 inter_mem_nhdsWithin_inter
  条件: {a b c d : Set α} {x : α} (h : a in 𝓝[b] x) (h' : c in 𝓝[d] x)
  证明: inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')

Depends on / 依赖: inter_mem, inter_subset_left, inter_subset_right, nhdsWithin_mono
-/
lemma inter_mem_nhdsWithin_inter {a b c d : Set α} {x : α} (h : a in 𝓝[b] x) (h' : c in 𝓝[d] x) :
    a inter c in 𝓝[b inter d] x :=
  inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')

/--
theorem `union_mem_nhds_of_mem_nhdsWithin` / 定理 `union_mem_nhds_of_mem_nhdsWithin`

English:
theorem union_mem_nhds_of_mem_nhdsWithin
  statement: {b : α}
  proof: by
  rw [← nhdsWithin_univ b]; rw [h]; rw [nhdsWithin_union]
  exact ⟨mem_of_superset hL (by simp), mem_of_superset hR (by simp)⟩

中文:
定理 union_mem_nhds_of_mem_nhdsWithin
  结论: {b : α}
  证明: by
  rw [← nhdsWithin_univ b]; rw [h]; rw [nhdsWithin_union]
  exact ⟨mem_of_superset hL (by simp), mem_of_superset hR (by simp)⟩

Depends on / 依赖: mem_of_superset, nhdsWithin_union, nhdsWithin_univ
-/
theorem union_mem_nhds_of_mem_nhdsWithin {b : α}
    {I₁ I₂ : Set α} (h : Set.univ = I₁ union I₂)
    {L : Set α} (hL : L in nhdsWithin b I₁)
    {R : Set α} (hR : R in nhdsWithin b I₂) : L union R in nhds b := by
  rw [← nhdsWithin_univ b]; rw [h]; rw [nhdsWithin_union]
  exact ⟨mem_of_superset hL (by simp), mem_of_superset hR (by simp)⟩


/--
lemma `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin` / 引理 `punctured_nhds_eq_nhdsWithin_sup_nhdsWithin`

English:
lemma punctured_nhds_eq_nhdsWithin_sup_nhdsWithin
  given: [LinearOrder α] {x : α}
  proof: by
  rw [← Iio_union_Ioi]; rw [nhdsWithin_union]

中文:
引理 punctured_nhds_eq_nhdsWithin_sup_nhdsWithin
  条件: [LinearOrder α] {x : α}
  证明: by
  rw [← Iio_union_Ioi]; rw [nhdsWithin_union]

Depends on / 依赖: Iio_union_Ioi, nhdsWithin_union
-/
lemma punctured_nhds_eq_nhdsWithin_sup_nhdsWithin [LinearOrder α] {x : α} :
    𝓝[!=] x = 𝓝[<] x ⊔ 𝓝[>] x := by
  rw [← Iio_union_Ioi]; rw [nhdsWithin_union]


/--
theorem `nhds_of_Ici_Iic` / 定理 `nhds_of_Ici_Iic`

English:
theorem nhds_of_Ici_Iic
  statement: [LinearOrder α] {b : α}
  proof: union_mem_nhds_of_mem_nhdsWithin Iic_union_Ici.symm
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)

中文:
定理 nhds_of_Ici_Iic
  结论: [LinearOrder α] {b : α}
  证明: union_mem_nhds_of_mem_nhdsWithin Iic_union_Ici.symm
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)

Depends on / 依赖: Iic_union_Ici, Iic_union_Ici.symm, inter_mem, self_mem_nhdsWithin, union_mem_nhds_of_mem_nhdsWithin
-/
theorem nhds_of_Ici_Iic [LinearOrder α] {b : α}
    {L : Set α} (hL : L in 𝓝[<=] b)
    {R : Set α} (hR : R in 𝓝[>=] b) : L inter Iic b union R inter Ici b in 𝓝 b :=
  union_mem_nhds_of_mem_nhdsWithin Iic_union_Ici.symm
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)

/--
theorem `nhdsWithin_biUnion` / 定理 `nhdsWithin_biUnion`

English:
theorem nhdsWithin_biUnion
  given: {ι} {I : Set ι} (hI : I.Finite) (s : ι -> Set α) (a : α)
  proof: by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hT => simp only [hT, nhdsWithin_union, iSup_insert, biUnion_insert]

中文:
定理 nhdsWithin_biUnion
  条件: {ι} {I : Set ι} (hI : I.Finite) (s : ι -> Set α) (a : α)
  证明: by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hT => simp only [hT, nhdsWithin_union, iSup_insert, biUnion_insert]

Depends on / 依赖: Finite, Set.Finite.induction_on, biUnion_insert, iSup_insert, induction_on, insert, nhdsWithin_union
-/
theorem nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (s : ι -> Set α) (a : α) :
    𝓝[⋃ i in I, s i] a = ⨆ i in I, 𝓝[s i] a := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hT => simp only [hT, nhdsWithin_union, iSup_insert, biUnion_insert]

/--
theorem `nhdsWithin_sUnion` / 定理 `nhdsWithin_sUnion`

English:
theorem nhdsWithin_sUnion
  given: {S : Set (Set α)} (hS : S.Finite) (a : α)
  proof: by
  rw [sUnion_eq_biUnion]; rw [nhdsWithin_biUnion hS]

中文:
定理 nhdsWithin_sUnion
  条件: {S : Set (Set α)} (hS : S.Finite) (a : α)
  证明: by
  rw [sUnion_eq_biUnion]; rw [nhdsWithin_biUnion hS]

Depends on / 依赖: nhdsWithin_biUnion, sUnion_eq_biUnion
-/
theorem nhdsWithin_sUnion {S : Set (Set α)} (hS : S.Finite) (a : α) :
    𝓝[⋃₀ S] a = ⨆ s in S, 𝓝[s] a := by
  rw [sUnion_eq_biUnion]; rw [nhdsWithin_biUnion hS]

/--
theorem `nhdsWithin_iUnion` / 定理 `nhdsWithin_iUnion`

English:
theorem nhdsWithin_iUnion
  given: {ι} [Finite ι] (s : ι -> Set α) (a : α)
  proof: by
  rw [← sUnion_range]; rw [nhdsWithin_sUnion (finite_range s)]; rw [iSup_range]

中文:
定理 nhdsWithin_iUnion
  条件: {ι} [Finite ι] (s : ι -> Set α) (a : α)
  证明: by
  rw [← sUnion_range]; rw [nhdsWithin_sUnion (finite_range s)]; rw [iSup_range]

Depends on / 依赖: finite_range, iSup_range, nhdsWithin_sUnion, sUnion_range
-/
theorem nhdsWithin_iUnion {ι} [Finite ι] (s : ι -> Set α) (a : α) :
    𝓝[⋃ i, s i] a = ⨆ i, 𝓝[s i] a := by
  rw [← sUnion_range]; rw [nhdsWithin_sUnion (finite_range s)]; rw [iSup_range]

/--
theorem `nhdsWithin_inter` / 定理 `nhdsWithin_inter`

English:
theorem nhdsWithin_inter
  given: (a : α) (s t : Set α)
  statement: 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓝[t] a
  proof: by
  delta nhdsWithin
  rw [inf_left_comm]; rw [inf_assoc]; rw [inf_principal]; rw [← inf_assoc]; rw [inf_idem]

中文:
定理 nhdsWithin_inter
  条件: (a : α) (s t : Set α)
  结论: 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓝[t] a
  证明: by
  delta nhdsWithin
  rw [inf_left_comm]; rw [inf_assoc]; rw [inf_principal]; rw [← inf_assoc]; rw [inf_idem]

Depends on / 依赖: inf_assoc, inf_idem, inf_left_comm, inf_principal, nhdsWithin
-/
theorem nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓝[t] a := by
  delta nhdsWithin
  rw [inf_left_comm]; rw [inf_assoc]; rw [inf_principal]; rw [← inf_assoc]; rw [inf_idem]

/--
theorem `nhdsWithin_inter'` / 定理 `nhdsWithin_inter'`

English:
theorem nhdsWithin_inter'
  given: (a : α) (s t : Set α)
  statement: 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓟 t
  proof: by
  delta nhdsWithin
  rw [← inf_principal]; rw [inf_assoc]

中文:
定理 nhdsWithin_inter'
  条件: (a : α) (s t : Set α)
  结论: 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓟 t
  证明: by
  delta nhdsWithin
  rw [← inf_principal]; rw [inf_assoc]

Depends on / 依赖: inf_assoc, inf_principal, nhdsWithin
-/
theorem nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s inter t] a = 𝓝[s] a ⊓ 𝓟 t := by
  delta nhdsWithin
  rw [← inf_principal]; rw [inf_assoc]

/--
theorem `nhdsWithin_inter_of_mem` / 定理 `nhdsWithin_inter_of_mem`

English:
theorem nhdsWithin_inter_of_mem
  given: {a : α} {s t : Set α} (h : s in 𝓝[t] a)
  statement: 𝓝[s inter t] a = 𝓝[t] a
  proof: by
  rw [nhdsWithin_inter]; rw [inf_eq_right]
  exact nhdsWithin_le_of_mem h

中文:
定理 nhdsWithin_inter_of_mem
  条件: {a : α} {s t : Set α} (h : s in 𝓝[t] a)
  结论: 𝓝[s inter t] a = 𝓝[t] a
  证明: by
  rw [nhdsWithin_inter]; rw [inf_eq_right]
  exact nhdsWithin_le_of_mem h

Depends on / 依赖: inf_eq_right, nhdsWithin_inter, nhdsWithin_le_of_mem
-/
theorem nhdsWithin_inter_of_mem {a : α} {s t : Set α} (h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a := by
  rw [nhdsWithin_inter]; rw [inf_eq_right]
  exact nhdsWithin_le_of_mem h

/--
theorem `nhdsWithin_inter_of_mem'` / 定理 `nhdsWithin_inter_of_mem'`

English:
theorem nhdsWithin_inter_of_mem'
  given: {a : α} {s t : Set α} (h : t in 𝓝[s] a)
  statement: 𝓝[s inter t] a = 𝓝[s] a
  proof: by
  rw [inter_comm]; rw [nhdsWithin_inter_of_mem h]

@[simp]

中文:
定理 nhdsWithin_inter_of_mem'
  条件: {a : α} {s t : Set α} (h : t in 𝓝[s] a)
  结论: 𝓝[s inter t] a = 𝓝[s] a
  证明: by
  rw [inter_comm]; rw [nhdsWithin_inter_of_mem h]

@[simp]

Depends on / 依赖: inter_comm, nhdsWithin_inter_of_mem
-/
theorem nhdsWithin_inter_of_mem' {a : α} {s t : Set α} (h : t in 𝓝[s] a) : 𝓝[s inter t] a = 𝓝[s] a := by
  rw [inter_comm]; rw [nhdsWithin_inter_of_mem h]

@[simp]
/--
theorem `nhdsWithin_singleton` / 定理 `nhdsWithin_singleton`

English:
theorem nhdsWithin_singleton
  given: (a : α)
  statement: 𝓝[{a}] a = pure a
  proof: by
  rw [nhdsWithin]; rw [principal_singleton]; rw [inf_eq_right.2 (pure_le_nhds a)]

@[simp]

中文:
定理 nhdsWithin_singleton
  条件: (a : α)
  结论: 𝓝[{a}] a = pure a
  证明: by
  rw [nhdsWithin]; rw [principal_singleton]; rw [inf_eq_right.2 (pure_le_nhds a)]

@[simp]

Depends on / 依赖: inf_eq_right, nhdsWithin, principal_singleton, pure_le_nhds
-/
theorem nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a := by
  rw [nhdsWithin]; rw [principal_singleton]; rw [inf_eq_right.2 (pure_le_nhds a)]

@[simp]
/--
theorem `nhdsWithin_insert` / 定理 `nhdsWithin_insert`

English:
theorem nhdsWithin_insert
  given: (a : α) (s : Set α)
  statement: 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a
  proof: by
  rw [← singleton_union]; rw [nhdsWithin_union]; rw [nhdsWithin_singleton]

中文:
定理 nhdsWithin_insert
  条件: (a : α) (s : Set α)
  结论: 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a
  证明: by
  rw [← singleton_union]; rw [nhdsWithin_union]; rw [nhdsWithin_singleton]

Depends on / 依赖: nhdsWithin_singleton, nhdsWithin_union, singleton_union
-/
theorem nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a ⊔ 𝓝[s] a := by
  rw [← singleton_union]; rw [nhdsWithin_union]; rw [nhdsWithin_singleton]

/--
theorem `mem_nhdsWithin_insert` / 定理 `mem_nhdsWithin_insert`

English:
theorem mem_nhdsWithin_insert
  given: {a : α} {s t : Set α}
  statement: t in 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a
  proof: by
  simp

中文:
定理 mem_nhdsWithin_insert
  条件: {a : α} {s t : Set α}
  结论: t in 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a
  证明: by
  simp
-/
theorem mem_nhdsWithin_insert {a : α} {s t : Set α} : t in 𝓝[insert a s] a ↔ a in t ∧ t in 𝓝[s] a := by
  simp

/--
theorem `insert_mem_nhdsWithin_insert` / 定理 `insert_mem_nhdsWithin_insert`

English:
theorem insert_mem_nhdsWithin_insert
  given: {a : α} {s t : Set α} (h : t in 𝓝[s] a)
  proof: by simp [mem_of_superset h]

中文:
定理 insert_mem_nhdsWithin_insert
  条件: {a : α} {s t : Set α} (h : t in 𝓝[s] a)
  证明: by simp [mem_of_superset h]

Depends on / 依赖: mem_of_superset
-/
theorem insert_mem_nhdsWithin_insert {a : α} {s t : Set α} (h : t in 𝓝[s] a) :
    insert a t in 𝓝[insert a s] a := by simp [mem_of_superset h]

/--
theorem `insert_mem_nhds_iff` / 定理 `insert_mem_nhds_iff`

English:
theorem insert_mem_nhds_iff
  given: {a : α} {s : Set α}
  statement: insert a s in 𝓝 a ↔ s in 𝓝[!=] a
  proof: by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]

@[simp]

中文:
定理 insert_mem_nhds_iff
  条件: {a : α} {s : Set α}
  结论: insert a s in 𝓝 a ↔ s in 𝓝[!=] a
  证明: by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]

@[simp]

Depends on / 依赖: insert_def, mem_compl_iff, mem_inf_principal, mem_singleton_iff, nhdsWithin, or_iff_not_imp_left
-/
theorem insert_mem_nhds_iff {a : α} {s : Set α} : insert a s in 𝓝 a ↔ s in 𝓝[!=] a := by
  simp only [nhdsWithin, mem_inf_principal, mem_compl_iff, mem_singleton_iff, or_iff_not_imp_left,
    insert_def]

@[simp]
/--
theorem `nhdsNE_sup_pure` / 定理 `nhdsNE_sup_pure`

English:
theorem nhdsNE_sup_pure
  given: (a : α)
  statement: 𝓝[!=] a ⊔ pure a = 𝓝 a
  proof: by
  rw [← nhdsWithin_singleton]; rw [← nhdsWithin_union]; rw [compl_union_self]; rw [nhdsWithin_univ]

@[simp]

中文:
定理 nhdsNE_sup_pure
  条件: (a : α)
  结论: 𝓝[!=] a ⊔ pure a = 𝓝 a
  证明: by
  rw [← nhdsWithin_singleton]; rw [← nhdsWithin_union]; rw [compl_union_self]; rw [nhdsWithin_univ]

@[simp]

Depends on / 依赖: compl_union_self, nhdsWithin_singleton, nhdsWithin_union, nhdsWithin_univ
-/
theorem nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a := by
  rw [← nhdsWithin_singleton]; rw [← nhdsWithin_union]; rw [compl_union_self]; rw [nhdsWithin_univ]

@[simp]
/--
theorem `pure_sup_nhdsNE` / 定理 `pure_sup_nhdsNE`

English:
theorem pure_sup_nhdsNE
  given: (a : α)
  statement: pure a ⊔ 𝓝[!=] a = 𝓝 a
  proof: by rw [← sup_comm, nhdsNE_sup_pure]

中文:
定理 pure_sup_nhdsNE
  条件: (a : α)
  结论: pure a ⊔ 𝓝[!=] a = 𝓝 a
  证明: by rw [← sup_comm, nhdsNE_sup_pure]

Depends on / 依赖: nhdsNE_sup_pure, sup_comm
-/
theorem pure_sup_nhdsNE (a : α) : pure a ⊔ 𝓝[!=] a = 𝓝 a := by rw [← sup_comm, nhdsNE_sup_pure]

/--
lemma `continuousAt_iff_punctured_nhds` / 引理 `continuousAt_iff_punctured_nhds`

English:
lemma continuousAt_iff_punctured_nhds
  given: [TopologicalSpace β] {f : α -> β} {a : α}
  proof: by
  simp [ContinuousAt, -pure_sup_nhdsNE, ← pure_sup_nhdsNE a, tendsto_pure_nhds]

中文:
引理 continuousAt_iff_punctured_nhds
  条件: [TopologicalSpace β] {f : α -> β} {a : α}
  证明: by
  simp [ContinuousAt, -pure_sup_nhdsNE, ← pure_sup_nhdsNE a, tendsto_pure_nhds]

Depends on / 依赖: ContinuousAt, pure_sup_nhdsNE, tendsto_pure_nhds
-/
lemma continuousAt_iff_punctured_nhds [TopologicalSpace β] {f : α -> β} {a : α} :
    ContinuousAt f a ↔ Tendsto f (𝓝[!=] a) (𝓝 (f a)) := by
  simp [ContinuousAt, -pure_sup_nhdsNE, ← pure_sup_nhdsNE a, tendsto_pure_nhds]

/--
theorem `nhdsWithin_prod` / 定理 `nhdsWithin_prod`

English:
theorem nhdsWithin_prod
  statement: [TopologicalSpace β]
  proof: by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv

中文:
定理 nhdsWithin_prod
  结论: [TopologicalSpace β]
  证明: by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv

Depends on / 依赖: nhdsWithin_prod_eq, prod_mem_prod
-/
theorem nhdsWithin_prod [TopologicalSpace β]
    {s u : Set α} {t v : Set β} {a : α} {b : β} (hu : u in 𝓝[s] a) (hv : v in 𝓝[t] b) :
    u ×ˢ v in 𝓝[s ×ˢ t] (a, b) := by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv

/--
lemma `Filter.EventuallyEq.mem_interior` / 引理 `Filter.EventuallyEq.mem_interior`

English:
lemma Filter.EventuallyEq.mem_interior
  statement: {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
  proof: by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  simpa [mem_interior_iff_mem_nhds, ← nhdsWithin_eq_nhds, hst] using h

中文:
引理 Filter.EventuallyEq.mem_interior
  结论: {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
  证明: by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  simpa [mem_interior_iff_mem_nhds, ← nhdsWithin_eq_nhds, hst] using h

Depends on / 依赖: mem_interior_iff_mem_nhds, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_eq_nhds
-/
lemma Filter.EventuallyEq.mem_interior {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
    (h : x in interior s) : x in interior t := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  simpa [mem_interior_iff_mem_nhds, ← nhdsWithin_eq_nhds, hst] using h

/--
lemma `Filter.EventuallyEq.mem_interior_iff` / 引理 `Filter.EventuallyEq.mem_interior_iff`

English:
lemma Filter.EventuallyEq.mem_interior_iff
  given: {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
  proof: ⟨fun h => hst.mem_interior h, fun h => hst.symm.mem_interior h⟩

中文:
引理 Filter.EventuallyEq.mem_interior_iff
  条件: {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t)
  证明: ⟨fun h => hst.mem_interior h, fun h => hst.symm.mem_interior h⟩

Depends on / 依赖: hst.mem_interior, hst.symm.mem_interior, mem_interior
-/
lemma Filter.EventuallyEq.mem_interior_iff {x : α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t) :
    x in interior s ↔ x in interior t :=
  ⟨fun h => hst.mem_interior h, fun h => hst.symm.mem_interior h⟩

section Pi

variable {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]

/--
theorem `nhdsWithin_pi_eq'` / 定理 `nhdsWithin_pi_eq'`

English:
theorem nhdsWithin_pi_eq'
  given: {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x : forall i, X i)
  proof: by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]

中文:
定理 nhdsWithin_pi_eq'
  条件: {I : Set ι} (hI : I.Finite) (s : 对任意 i, Set (X i)) (x : 对任意 i, X i)
  证明: by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]

Depends on / 依赖: Filter, Filter.pi, comap_iInf, comap_inf, comap_principal, iInf_inf_eq, iInf_principal_finite, nhdsWithin, nhds_pi, pi_def
-/
theorem nhdsWithin_pi_eq' {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x : forall i, X i) :
    𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ (_ : i in I), 𝓟 (s i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]

/--
theorem `nhdsWithin_pi_eq` / 定理 `nhdsWithin_pi_eq`

English:
theorem nhdsWithin_pi_eq
  given: {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x : forall i, X i)
  proof: by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal]
  rw [iInf_split _ fun i => i in I]; rw [inf_right_comm]
  simp only [iInf_inf_eq]

中文:
定理 nhdsWithin_pi_eq
  条件: {I : Set ι} (hI : I.Finite) (s : 对任意 i, Set (X i)) (x : 对任意 i, X i)
  证明: by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal]
  rw [iInf_split _ fun i => i in I]; rw [inf_right_comm]
  simp only [iInf_inf_eq]

Depends on / 依赖: Filter, Filter.pi, comap_inf, comap_principal, iInf_inf_eq, iInf_principal_finite, iInf_split, inf_right_comm, nhdsWithin, nhds_pi, pi_def
-/
theorem nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : forall i, Set (X i)) (x : forall i, X i) :
    𝓝[pi I s] x =
      (⨅ i in I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
        ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal]
  rw [iInf_split _ fun i => i in I]; rw [inf_right_comm]
  simp only [iInf_inf_eq]

/--
theorem `nhdsWithin_pi_univ_eq` / 定理 `nhdsWithin_pi_univ_eq`

English:
theorem nhdsWithin_pi_univ_eq
  given: [Finite ι] (s : forall i, Set (X i)) (x : forall i, X i)
  proof: by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x

中文:
定理 nhdsWithin_pi_univ_eq
  条件: [Finite ι] (s : 对任意 i, Set (X i)) (x : 对任意 i, X i)
  证明: by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x

Depends on / 依赖: finite_univ, nhdsWithin, nhdsWithin_pi_eq
-/
theorem nhdsWithin_pi_univ_eq [Finite ι] (s : forall i, Set (X i)) (x : forall i, X i) :
    𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) := by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x

/--
theorem `nhdsWithin_pi_eq_bot` / 定理 `nhdsWithin_pi_eq_bot`

English:
theorem nhdsWithin_pi_eq_bot
  given: {I : Set ι} {s : forall i, Set (X i)} {x : forall i, X i}
  proof: by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]

中文:
定理 nhdsWithin_pi_eq_bot
  条件: {I : Set ι} {s : 对任意 i, Set (X i)} {x : 对任意 i, X i}
  证明: by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]

Depends on / 依赖: nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot
-/
theorem nhdsWithin_pi_eq_bot {I : Set ι} {s : forall i, Set (X i)} {x : forall i, X i} :
    𝓝[pi I s] x = ⊥ ↔ exists i in I, 𝓝[s i] x i = ⊥ := by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]

/--
theorem `nhdsWithin_pi_neBot` / 定理 `nhdsWithin_pi_neBot`

English:
theorem nhdsWithin_pi_neBot
  given: {I : Set ι} {s : forall i, Set (X i)} {x : forall i, X i}
  proof: by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]

中文:
定理 nhdsWithin_pi_neBot
  条件: {I : Set ι} {s : 对任意 i, Set (X i)} {x : 对任意 i, X i}
  证明: by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]

Depends on / 依赖: neBot_iff, nhdsWithin_pi_eq_bot
-/
theorem nhdsWithin_pi_neBot {I : Set ι} {s : forall i, Set (X i)} {x : forall i, X i} :
    (𝓝[pi I s] x).NeBot ↔ forall i in I, (𝓝[s i] x i).NeBot := by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]

/--
Instance `instNeBotNhdsWithinUnivPi` / 实例 `instNeBotNhdsWithinUnivPi`

English:
instance instNeBotNhdsWithinUnivPi
  signature: {s : forall i, Set (X i)} {x : forall i, X i}
  body: by
  simpa [nhdsWithin_pi_neBot]

中文:
实例 instNeBotNhdsWithinUnivPi
  签名: {s : 对任意 i, Set (X i)} {x : 对任意 i, X i}
  定义体: by
  simpa [nhdsWithin_pi_neBot]

Depends on / 依赖: nhdsWithin_pi_neBot
-/
instance instNeBotNhdsWithinUnivPi {s : forall i, Set (X i)} {x : forall i, X i}
    [forall i, (𝓝[s i] x i).NeBot] : (𝓝[pi univ s] x).NeBot := by
  simpa [nhdsWithin_pi_neBot]

/--
Instance `Pi.instNeBotNhdsWithinIio` / 实例 `Pi.instNeBotNhdsWithinIio`

English:
instance Pi.instNeBotNhdsWithinIio
  signature: [Nonempty ι] [forall i, Preorder (X i)] {x : forall i, X i}
  body: have : (𝓝[pi univ fun i => Iio (x i)] x).NeBot := inferInstance
this.mono nhdsWithin_mono _ fun _y hy => lt_of_strongLT fun i => hy i trivial

中文:
实例 Pi.instNeBotNhdsWithinIio
  签名: [Nonempty ι] [对任意 i, Preorder (X i)] {x : 对任意 i, X i}
  定义体: have : (𝓝[pi univ fun i => Iio (x i)] x).NeBot := inferInstance
this.mono nhdsWithin_mono _ fun _y hy => lt_of_strongLT fun i => hy i trivial

Depends on / 依赖: lt_of_strongLT, nhdsWithin_mono, this.mono
-/
instance Pi.instNeBotNhdsWithinIio [Nonempty ι] [forall i, Preorder (X i)] {x : forall i, X i}
    [forall i, (𝓝[<] x i).NeBot] : (𝓝[<] x).NeBot :=
  have : (𝓝[pi univ fun i => Iio (x i)] x).NeBot := inferInstance
this.mono nhdsWithin_mono _ fun _y hy => lt_of_strongLT fun i => hy i trivial

/--
Instance `Pi.instNeBotNhdsWithinIoi` / 实例 `Pi.instNeBotNhdsWithinIoi`

English:
instance Pi.instNeBotNhdsWithinIoi
  signature: [Nonempty ι] [forall i, Preorder (X i)] {x : forall i, X i}
  body: Pi.instNeBotNhdsWithinIio (X := fun i => (X i)ᵒᵈ) (x := fun i => OrderDual.toDual (x i))

中文:
实例 Pi.instNeBotNhdsWithinIoi
  签名: [Nonempty ι] [对任意 i, Preorder (X i)] {x : 对任意 i, X i}
  定义体: Pi.instNeBotNhdsWithinIio (X := fun i => (X i)ᵒᵈ) (x := fun i => OrderDual.toDual (x i))

Depends on / 依赖: OrderDual, OrderDual.toDual, Pi.instNeBotNhdsWithinIio, instNeBotNhdsWithinIio, toDual
-/
instance Pi.instNeBotNhdsWithinIoi [Nonempty ι] [forall i, Preorder (X i)] {x : forall i, X i}
    [forall i, (𝓝[>] x i).NeBot] : (𝓝[>] x).NeBot :=
  Pi.instNeBotNhdsWithinIio (X := fun i => (X i)ᵒᵈ) (x := fun i => OrderDual.toDual (x i))

end Pi

/--
theorem `Filter.Tendsto.piecewise_nhdsWithin` / 定理 `Filter.Tendsto.piecewise_nhdsWithin`

English:
theorem Filter.Tendsto.piecewise_nhdsWithin
  statement: {f g : α -> β} {t : Set α} [forall x, Decidable (x in t)]
  proof: by
  apply Tendsto.piecewise <;> rwa [← nhdsWithin_inter']

中文:
定理 Filter.Tendsto.piecewise_nhdsWithin
  结论: {f g : α -> β} {t : Set α} [对任意 x, Decidable (x in t)]
  证明: by
  apply Tendsto.piecewise <;> rwa [← nhdsWithin_inter']

Depends on / 依赖: Tendsto, Tendsto.piecewise, nhdsWithin_inter, piecewise
-/
theorem Filter.Tendsto.piecewise_nhdsWithin {f g : α -> β} {t : Set α} [forall x, Decidable (x in t)]
    {a : α} {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s inter t] a) l)
    (h₁ : Tendsto g (𝓝[s inter tᶜ] a) l) : Tendsto (piecewise t f g) (𝓝[s] a) l := by
  apply Tendsto.piecewise <;> rwa [← nhdsWithin_inter']

/--
theorem `Filter.Tendsto.if_nhdsWithin` / 定理 `Filter.Tendsto.if_nhdsWithin`

English:
theorem Filter.Tendsto.if_nhdsWithin
  statement: {f g : α -> β} {p : α -> Prop} [DecidablePred p] {a : α}
  proof: h₀.piecewise_nhdsWithin h₁

中文:
定理 Filter.Tendsto.if_nhdsWithin
  结论: {f g : α -> β} {p : α -> 命题} [DecidablePred p] {a : α}
  证明: h₀.piecewise_nhdsWithin h₁

Depends on / 依赖: piecewise_nhdsWithin
-/
theorem Filter.Tendsto.if_nhdsWithin {f g : α -> β} {p : α -> Prop} [DecidablePred p] {a : α}
    {s : Set α} {l : Filter β} (h₀ : Tendsto f (𝓝[s inter { x | p x }] a) l)
    (h₁ : Tendsto g (𝓝[s inter { x | ¬p x }] a) l) :
    Tendsto (fun x => if p x then f x else g x) (𝓝[s] a) l :=
  h₀.piecewise_nhdsWithin h₁

/--
theorem `map_nhdsWithin` / 定理 `map_nhdsWithin`

English:
theorem map_nhdsWithin
  given: (f : α -> β) (a : α) (s : Set α)
  proof: ((nhdsWithin_basis_open a s).map f).eq_biInf

中文:
定理 map_nhdsWithin
  条件: (f : α -> β) (a : α) (s : Set α)
  证明: ((nhdsWithin_basis_open a s).map f).eq_biInf

Depends on / 依赖: eq_biInf, nhdsWithin_basis_open
-/
theorem map_nhdsWithin (f : α -> β) (a : α) (s : Set α) :
    map f (𝓝[s] a) = ⨅ t in { t : Set α | a in t ∧ IsOpen t }, 𝓟 (f '' (t inter s)) :=
  ((nhdsWithin_basis_open a s).map f).eq_biInf

/--
theorem `tendsto_nhdsWithin_mono_left` / 定理 `tendsto_nhdsWithin_mono_left`

English:
theorem tendsto_nhdsWithin_mono_left
  statement: {f : α -> β} {a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t)
  proof: h.mono_left nhdsWithin_mono a hst

中文:
定理 tendsto_nhdsWithin_mono_left
  结论: {f : α -> β} {a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t)
  证明: h.mono_left nhdsWithin_mono a hst

Depends on / 依赖: h.mono_left, mono_left, nhdsWithin_mono
-/
theorem tendsto_nhdsWithin_mono_left {f : α -> β} {a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t)
    (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l :=
h.mono_left nhdsWithin_mono a hst

/--
theorem `tendsto_nhdsWithin_mono_right` / 定理 `tendsto_nhdsWithin_mono_right`

English:
theorem tendsto_nhdsWithin_mono_right
  statement: {f : β -> α} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t)
  proof: h.mono_right (nhdsWithin_mono a hst)

中文:
定理 tendsto_nhdsWithin_mono_right
  结论: {f : β -> α} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t)
  证明: h.mono_right (nhdsWithin_mono a hst)

Depends on / 依赖: h.mono_right, mono_right, nhdsWithin_mono
-/
theorem tendsto_nhdsWithin_mono_right {f : β -> α} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t)
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a) :=
  h.mono_right (nhdsWithin_mono a hst)

/--
theorem `tendsto_nhdsWithin_of_tendsto_nhds` / 定理 `tendsto_nhdsWithin_of_tendsto_nhds`

English:
theorem tendsto_nhdsWithin_of_tendsto_nhds
  statement: {f : α -> β} {a : α} {s : Set α} {l : Filter β}
  proof: h.mono_left inf_le_left

中文:
定理 tendsto_nhdsWithin_of_tendsto_nhds
  结论: {f : α -> β} {a : α} {s : Set α} {l : Filter β}
  证明: h.mono_left inf_le_left

Depends on / 依赖: h.mono_left, inf_le_left, mono_left
-/
theorem tendsto_nhdsWithin_of_tendsto_nhds {f : α -> β} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f (𝓝 a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left inf_le_left

/--
theorem `eventually_mem_of_tendsto_nhdsWithin` / 定理 `eventually_mem_of_tendsto_nhdsWithin`

English:
theorem eventually_mem_of_tendsto_nhdsWithin
  statement: {f : β -> α} {a : α} {s : Set α} {l : Filter β}
  proof: by
  simp_rw [nhdsWithin_eq, tendsto_iInf, mem_ofPred_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2

中文:
定理 eventually_mem_of_tendsto_nhdsWithin
  结论: {f : β -> α} {a : α} {s : Set α} {l : Filter β}
  证明: by
  simp_rw [nhdsWithin_eq, tendsto_iInf, mem_ofPred_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2

Depends on / 依赖: eventually_and, isOpen_univ, mem_inter_iff, mem_ofPred_eq, mem_univ, nhdsWithin_eq, simp_rw, tendsto_iInf, tendsto_principal
-/
theorem eventually_mem_of_tendsto_nhdsWithin {f : β -> α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : forallᶠ i in l, f i in s := by
  simp_rw [nhdsWithin_eq, tendsto_iInf, mem_ofPred_eq, tendsto_principal, mem_inter_iff,
    eventually_and] at h
  exact (h univ ⟨mem_univ a, isOpen_univ⟩).2

/--
theorem `tendsto_nhds_of_tendsto_nhdsWithin` / 定理 `tendsto_nhds_of_tendsto_nhdsWithin`

English:
theorem tendsto_nhds_of_tendsto_nhdsWithin
  statement: {f : β -> α} {a : α} {s : Set α} {l : Filter β}
  proof: h.mono_right nhdsWithin_le_nhds

中文:
定理 tendsto_nhds_of_tendsto_nhdsWithin
  结论: {f : β -> α} {a : α} {s : Set α} {l : Filter β}
  证明: h.mono_right nhdsWithin_le_nhds

Depends on / 依赖: h.mono_right, mono_right, nhdsWithin_le_nhds
-/
theorem tendsto_nhds_of_tendsto_nhdsWithin {f : β -> α} {a : α} {s : Set α} {l : Filter β}
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝 a) :=
  h.mono_right nhdsWithin_le_nhds

/--
theorem `nhdsWithin_neBot_of_mem` / 定理 `nhdsWithin_neBot_of_mem`

English:
theorem nhdsWithin_neBot_of_mem
  given: {s : Set α} {x : α} (hx : x in s)
  statement: NeBot (𝓝[s] x)
  proof: mem_closure_iff_nhdsWithin_neBot.1 subset_closure hx

中文:
定理 nhdsWithin_neBot_of_mem
  条件: {s : Set α} {x : α} (hx : x in s)
  结论: NeBot (𝓝[s] x)
  证明: mem_closure_iff_nhdsWithin_neBot.1 subset_closure hx

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, subset_closure
-/
theorem nhdsWithin_neBot_of_mem {s : Set α} {x : α} (hx : x in s) : NeBot (𝓝[s] x) :=
mem_closure_iff_nhdsWithin_neBot.1 subset_closure hx

/--
theorem `IsClosed.mem_of_nhdsWithin_neBot` / 定理 `IsClosed.mem_of_nhdsWithin_neBot`

English:
theorem IsClosed.mem_of_nhdsWithin_neBot
  statement: {s : Set α} (hs : IsClosed s) {x : α}
  proof: hs.closure_eq ▸ mem_closure_iff_nhdsWithin_neBot.2 hx

中文:
定理 IsClosed.mem_of_nhdsWithin_neBot
  结论: {s : Set α} (hs : IsClosed s) {x : α}
  证明: hs.closure_eq ▸ mem_closure_iff_nhdsWithin_neBot.2 hx

Depends on / 依赖: closure_eq, hs.closure_eq, mem_closure_iff_nhdsWithin_neBot
-/
theorem IsClosed.mem_of_nhdsWithin_neBot {s : Set α} (hs : IsClosed s) {x : α}
    (hx : NeBot <| 𝓝[s] x) : x in s :=
  hs.closure_eq ▸ mem_closure_iff_nhdsWithin_neBot.2 hx

/--
theorem `DenseRange.nhdsWithin_neBot` / 定理 `DenseRange.nhdsWithin_neBot`

English:
theorem DenseRange.nhdsWithin_neBot
  given: {ι : Type*} {f : ι -> α} (h : DenseRange f) (x : α)
  proof: mem_closure_iff_clusterPt.1 (h x)

中文:
定理 DenseRange.nhdsWithin_neBot
  条件: {ι : 类型} {f : ι -> α} (h : DenseRange f) (x : α)
  证明: mem_closure_iff_clusterPt.1 (h x)

Depends on / 依赖: mem_closure_iff_clusterPt
-/
theorem DenseRange.nhdsWithin_neBot {ι : Type*} {f : ι -> α} (h : DenseRange f) (x : α) :
    NeBot (𝓝[range f] x) :=
  mem_closure_iff_clusterPt.1 (h x)

/--
theorem `mem_closure_pi` / 定理 `mem_closure_pi`

English:
theorem mem_closure_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] {I : Set ι}
  proof: by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]

中文:
定理 mem_closure_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, TopologicalSpace (α i)] {I : Set ι}
  证明: by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot
-/
theorem mem_closure_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] {I : Set ι}
    {s : forall i, Set (α i)} {x : forall i, α i} : x in closure (pi I s) ↔ forall i in I, x i in closure (s i) := by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]

/--
theorem `closure_pi_set` / 定理 `closure_pi_set`

English:
theorem closure_pi_set
  statement: {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] (I : Set ι)
  proof: Set.ext fun _ => mem_closure_pi

中文:
定理 closure_pi_set
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, TopologicalSpace (α i)] (I : Set ι)
  证明: Set.ext fun _ => mem_closure_pi

Depends on / 依赖: Set.ext, mem_closure_pi
-/
theorem closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] (I : Set ι)
    (s : forall i, Set (α i)) : closure (pi I s) = pi I fun i => closure (s i) :=
  Set.ext fun _ => mem_closure_pi

/--
theorem `dense_pi` / 定理 `dense_pi`

English:
theorem dense_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] {s : forall i, Set (α i)}
  proof: by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]

中文:
定理 dense_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, TopologicalSpace (α i)] {s : 对任意 i, Set (α i)}
  证明: by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]

Depends on / 依赖: closure_eq, closure_pi_set, dense_iff_closure_eq, pi_congr, pi_univ
-/
theorem dense_pi {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α i)] {s : forall i, Set (α i)}
    (I : Set ι) (hs : forall i in I, Dense (s i)) : Dense (pi I s) := by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]

/--
theorem `DenseRange.piMap` / 定理 `DenseRange.piMap`

English:
theorem DenseRange.piMap
  statement: {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (Y i)]
  proof: by
  rw [DenseRange]; rw [Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)

中文:
定理 DenseRange.piMap
  结论: {ι : 类型} {X Y : ι -> 类型} [对任意 i, TopologicalSpace (Y i)]
  证明: by
  rw [DenseRange]; rw [Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)

Depends on / 依赖: DenseRange, Set.range_piMap, Set.univ, dense_pi, range_piMap
-/
theorem DenseRange.piMap {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (Y i)]
    {f : (i : ι) -> (X i) -> (Y i)} (hf : forall i, DenseRange (f i)) :
    DenseRange (Pi.map f) := by
  rw [DenseRange]; rw [Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)

/--
theorem `eventuallyEq_nhdsWithin_iff` / 定理 `eventuallyEq_nhdsWithin_iff`

English:
theorem eventuallyEq_nhdsWithin_iff
  given: {f g : α -> β} {s : Set α} {a : α}
  proof: mem_inf_principal

中文:
定理 eventuallyEq_nhdsWithin_iff
  条件: {f g : α -> β} {s : Set α} {a : α}
  证明: mem_inf_principal

Depends on / 依赖: mem_inf_principal
-/
theorem eventuallyEq_nhdsWithin_iff {f g : α -> β} {s : Set α} {a : α} :
    f =ᶠ[𝓝[s] a] g ↔ forallᶠ x in 𝓝 a, x in s -> f x = g x :=
  mem_inf_principal

/--
theorem `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` / 定理 `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`

English:
theorem eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  statement: {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g)
  proof: by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  grind

中文:
定理 eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  结论: {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g)
  证明: by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  grind

Depends on / 依赖: eventually_nhdsWithin_iff, filter_upwards
-/
theorem eventuallyEq_nhds_of_eventuallyEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g)
    (h₂ : f a = g a) :
    f =ᶠ[𝓝 a] g := by
  filter_upwards [eventually_nhdsWithin_iff.1 h₁]
  grind

/--
theorem `eventuallyEq_nhdsWithin_of_eqOn` / 定理 `eventuallyEq_nhdsWithin_of_eqOn`

English:
theorem eventuallyEq_nhdsWithin_of_eqOn
  given: {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s)
  proof: mem_inf_of_right h

中文:
定理 eventuallyEq_nhdsWithin_of_eqOn
  条件: {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s)
  证明: mem_inf_of_right h

Depends on / 依赖: mem_inf_of_right
-/
theorem eventuallyEq_nhdsWithin_of_eqOn {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  mem_inf_of_right h

/--
theorem `Set.EqOn.eventuallyEq_nhdsWithin` / 定理 `Set.EqOn.eventuallyEq_nhdsWithin`

English:
theorem Set.EqOn.eventuallyEq_nhdsWithin
  given: {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s)
  proof: eventuallyEq_nhdsWithin_of_eqOn h

中文:
定理 Set.EqOn.eventuallyEq_nhdsWithin
  条件: {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s)
  证明: eventuallyEq_nhdsWithin_of_eqOn h

Depends on / 依赖: eventuallyEq_nhdsWithin_of_eqOn
-/
theorem Set.EqOn.eventuallyEq_nhdsWithin {f g : α -> β} {s : Set α} {a : α} (h : EqOn f g s) :
    f =ᶠ[𝓝[s] a] g :=
  eventuallyEq_nhdsWithin_of_eqOn h

/--
theorem `tendsto_nhdsWithin_congr` / 定理 `tendsto_nhdsWithin_congr`

English:
theorem tendsto_nhdsWithin_congr
  statement: {f g : α -> β} {s : Set α} {a : α} {l : Filter β}
  proof: (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf

中文:
定理 tendsto_nhdsWithin_congr
  结论: {f g : α -> β} {s : Set α} {a : α} {l : Filter β}
  证明: (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf

Depends on / 依赖: eventuallyEq_nhdsWithin_of_eqOn, tendsto_congr
-/
theorem tendsto_nhdsWithin_congr {f g : α -> β} {s : Set α} {a : α} {l : Filter β}
    (hfg : forall x in s, f x = g x) (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] a) l :=
  (tendsto_congr' <| eventuallyEq_nhdsWithin_of_eqOn hfg).1 hf

/--
theorem `eventually_nhdsWithin_of_forall` / 定理 `eventually_nhdsWithin_of_forall`

English:
theorem eventually_nhdsWithin_of_forall
  given: {s : Set α} {a : α} {p : α -> Prop} (h : forall x in s, p x)
  proof: mem_inf_of_right h

中文:
定理 eventually_nhdsWithin_of_forall
  条件: {s : Set α} {a : α} {p : α -> 命题} (h : 对任意 x in s, p x)
  证明: mem_inf_of_right h

Depends on / 依赖: mem_inf_of_right
-/
theorem eventually_nhdsWithin_of_forall {s : Set α} {a : α} {p : α -> Prop} (h : forall x in s, p x) :
    forallᶠ x in 𝓝[s] a, p x :=
  mem_inf_of_right h

/--
theorem `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` / 定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`

English:
theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  statement: {a : α} {l : Filter β} {s : Set α}
  proof: tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩

中文:
定理 tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  结论: {a : α} {l : Filter β} {s : Set α}
  证明: tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩

Depends on / 依赖: tendsto_inf, tendsto_principal
-/
theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α}
    (f : β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : forallᶠ x in l, f x in s) : Tendsto f l (𝓝[s] a) :=
  tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩

/--
theorem `tendsto_nhdsWithin_iff` / 定理 `tendsto_nhdsWithin_iff`

English:
theorem tendsto_nhdsWithin_iff
  given: {a : α} {l : Filter β} {s : Set α} {f : β -> α}
  proof: ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

@[simp]

中文:
定理 tendsto_nhdsWithin_iff
  条件: {a : α} {l : Filter β} {s : Set α} {f : β -> α}
  证明: ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

@[simp]

Depends on / 依赖: eventually_mem_of_tendsto_nhdsWithin, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β -> α} :
    Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in l, f n in s :=
  ⟨fun h => ⟨tendsto_nhds_of_tendsto_nhdsWithin h, eventually_mem_of_tendsto_nhdsWithin h⟩, fun h =>
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

@[simp]
/--
theorem `tendsto_nhdsWithin_range` / 定理 `tendsto_nhdsWithin_range`

English:
theorem tendsto_nhdsWithin_range
  given: {a : α} {l : Filter β} {f : β -> α}
  proof: ⟨fun h => h.mono_right inf_le_left, fun h =>
tendsto_inf.2 ⟨h, tendsto_principal.2 Eventually.of_forall mem_range_self⟩⟩

中文:
定理 tendsto_nhdsWithin_range
  条件: {a : α} {l : Filter β} {f : β -> α}
  证明: ⟨fun h => h.mono_right inf_le_left, fun h =>
tendsto_inf.2 ⟨h, tendsto_principal.2 Eventually.of_forall mem_range_self⟩⟩

Depends on / 依赖: Eventually, Eventually.of_forall, h.mono_right, inf_le_left, mem_range_self, mono_right, of_forall, tendsto_inf, tendsto_principal
-/
theorem tendsto_nhdsWithin_range {a : α} {l : Filter β} {f : β -> α} :
    Tendsto f l (𝓝[range f] a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => h.mono_right inf_le_left, fun h =>
tendsto_inf.2 ⟨h, tendsto_principal.2 Eventually.of_forall mem_range_self⟩⟩

/--
theorem `Filter.EventuallyEq.eq_of_nhdsWithin` / 定理 `Filter.EventuallyEq.eq_of_nhdsWithin`

English:
theorem Filter.EventuallyEq.eq_of_nhdsWithin
  statement: {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
  proof: h.self_of_nhdsWithin hmem

中文:
定理 Filter.EventuallyEq.eq_of_nhdsWithin
  结论: {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
  证明: h.self_of_nhdsWithin hmem

Depends on / 依赖: h.self_of_nhdsWithin, self_of_nhdsWithin
-/
theorem Filter.EventuallyEq.eq_of_nhdsWithin {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : f a = g a :=
  h.self_of_nhdsWithin hmem

/--
theorem `eventually_nhdsWithin_of_eventually_nhds` / 定理 `eventually_nhdsWithin_of_eventually_nhds`

English:
theorem eventually_nhdsWithin_of_eventually_nhds
  statement: {s : Set α}
  proof: mem_nhdsWithin_of_mem_nhds h

中文:
定理 eventually_nhdsWithin_of_eventually_nhds
  结论: {s : Set α}
  证明: mem_nhdsWithin_of_mem_nhds h

Depends on / 依赖: mem_nhdsWithin_of_mem_nhds
-/
theorem eventually_nhdsWithin_of_eventually_nhds {s : Set α}
    {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : forallᶠ x in 𝓝[s] a, p x :=
  mem_nhdsWithin_of_mem_nhds h

/--
lemma `Set.MapsTo.preimage_mem_nhdsWithin` / 引理 `Set.MapsTo.preimage_mem_nhdsWithin`

English:
lemma Set.MapsTo.preimage_mem_nhdsWithin
  statement: {f : α -> β} {s : Set α} {t : Set β} {x : α}
  proof: Filter.mem_of_superset self_mem_nhdsWithin hst

中文:
引理 Set.MapsTo.preimage_mem_nhdsWithin
  结论: {f : α -> β} {s : Set α} {t : Set β} {x : α}
  证明: Filter.mem_of_superset self_mem_nhdsWithin hst

Depends on / 依赖: Filter, Filter.mem_of_superset, mem_of_superset, self_mem_nhdsWithin
-/
lemma Set.MapsTo.preimage_mem_nhdsWithin {f : α -> β} {s : Set α} {t : Set β} {x : α}
    (hst : MapsTo f s t) : f ⁻¹' t in 𝓝[s] x :=
  Filter.mem_of_superset self_mem_nhdsWithin hst


/--
theorem `mem_nhdsWithin_subtype` / 定理 `mem_nhdsWithin_subtype`

English:
theorem mem_nhdsWithin_subtype
  given: {s : Set α} {a : { x // x in s }} {t u : Set { x // x in s }}
  proof: by
  rw [nhdsWithin]; rw [nhds_subtype]; rw [principal_subtype]; rw [← comap_inf]; rw [← nhdsWithin]

中文:
定理 mem_nhdsWithin_subtype
  条件: {s : Set α} {a : { x // x in s }} {t u : Set { x // x in s }}
  证明: by
  rw [nhdsWithin]; rw [nhds_subtype]; rw [principal_subtype]; rw [← comap_inf]; rw [← nhdsWithin]

Depends on / 依赖: comap_inf, nhdsWithin, nhds_subtype, principal_subtype
-/
theorem mem_nhdsWithin_subtype {s : Set α} {a : { x // x in s }} {t u : Set { x // x in s }} :
    t in 𝓝[u] a ↔ t in comap ((↑) : s -> α) (𝓝[(↑) '' u] a) := by
  rw [nhdsWithin]; rw [nhds_subtype]; rw [principal_subtype]; rw [← comap_inf]; rw [← nhdsWithin]

/--
theorem `nhdsWithin_subtype` / 定理 `nhdsWithin_subtype`

English:
theorem nhdsWithin_subtype
  given: (s : Set α) (a : { x // x in s }) (t : Set { x // x in s })
  proof: Filter.ext fun _ => mem_nhdsWithin_subtype

中文:
定理 nhdsWithin_subtype
  条件: (s : Set α) (a : { x // x in s }) (t : Set { x // x in s })
  证明: Filter.ext fun _ => mem_nhdsWithin_subtype

Depends on / 依赖: Filter, Filter.ext, mem_nhdsWithin_subtype
-/
theorem nhdsWithin_subtype (s : Set α) (a : { x // x in s }) (t : Set { x // x in s }) :
    𝓝[t] a = comap ((↑) : s -> α) (𝓝[(↑) '' t] a) :=
  Filter.ext fun _ => mem_nhdsWithin_subtype

/--
theorem `nhdsWithin_eq_map_subtype_coe` / 定理 `nhdsWithin_eq_map_subtype_coe`

English:
theorem nhdsWithin_eq_map_subtype_coe
  given: {s : Set α} {a : α} (h : a in s)
  proof: (map_nhds_subtype_val ⟨a, h⟩).symm

中文:
定理 nhdsWithin_eq_map_subtype_coe
  条件: {s : Set α} {a : α} (h : a in s)
  证明: (map_nhds_subtype_val ⟨a, h⟩).symm

Depends on / 依赖: map_nhds_subtype_val
-/
theorem nhdsWithin_eq_map_subtype_coe {s : Set α} {a : α} (h : a in s) :
    𝓝[s] a = map ((↑) : s -> α) (𝓝 ⟨a, h⟩) :=
  (map_nhds_subtype_val ⟨a, h⟩).symm

/--
theorem `mem_nhds_subtype_iff_nhdsWithin` / 定理 `mem_nhds_subtype_iff_nhdsWithin`

English:
theorem mem_nhds_subtype_iff_nhdsWithin
  given: {s : Set α} {a : s} {t : Set s}
  proof: by
  rw [← map_nhds_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]

中文:
定理 mem_nhds_subtype_iff_nhdsWithin
  条件: {s : Set α} {a : s} {t : Set s}
  证明: by
  rw [← map_nhds_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]

Depends on / 依赖: Subtype, Subtype.val_injective, image_mem_map_iff, map_nhds_subtype_val, val_injective
-/
theorem mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} :
    t in 𝓝 a ↔ (↑) '' t in 𝓝[s] (a : α) := by
  rw [← map_nhds_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]

/--
theorem `preimage_coe_mem_nhds_subtype` / 定理 `preimage_coe_mem_nhds_subtype`

English:
theorem preimage_coe_mem_nhds_subtype
  given: {s t : Set α} {a : s}
  statement: (↑) ⁻¹' t in 𝓝 a ↔ t in 𝓝[s] ↑a
  proof: by
  rw [← map_nhds_subtype_val]; rw [mem_map]

中文:
定理 preimage_coe_mem_nhds_subtype
  条件: {s t : Set α} {a : s}
  结论: (↑) ⁻¹' t in 𝓝 a ↔ t in 𝓝[s] ↑a
  证明: by
  rw [← map_nhds_subtype_val]; rw [mem_map]

Depends on / 依赖: map_nhds_subtype_val, mem_map
-/
theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : (↑) ⁻¹' t in 𝓝 a ↔ t in 𝓝[s] ↑a := by
  rw [← map_nhds_subtype_val]; rw [mem_map]

/--
theorem `eventually_nhds_subtype_iff` / 定理 `eventually_nhds_subtype_iff`

English:
theorem eventually_nhds_subtype_iff
  given: (s : Set α) (a : s) (P : α -> Prop)
  proof: preimage_coe_mem_nhds_subtype

中文:
定理 eventually_nhds_subtype_iff
  条件: (s : Set α) (a : s) (P : α -> 命题)
  证明: preimage_coe_mem_nhds_subtype

Depends on / 依赖: preimage_coe_mem_nhds_subtype
-/
theorem eventually_nhds_subtype_iff (s : Set α) (a : s) (P : α -> Prop) :
    (forallᶠ x : s in 𝓝 a, P x) ↔ forallᶠ x in 𝓝[s] a, P x :=
  preimage_coe_mem_nhds_subtype

/--
theorem `frequently_nhds_subtype_iff` / 定理 `frequently_nhds_subtype_iff`

English:
theorem frequently_nhds_subtype_iff
  given: (s : Set α) (a : s) (P : α -> Prop)
  proof: .not eventually_nhds_subtype_iff s a (¬ P ·)

中文:
定理 frequently_nhds_subtype_iff
  条件: (s : Set α) (a : s) (P : α -> 命题)
  证明: .not eventually_nhds_subtype_iff s a (¬ P ·)

Depends on / 依赖: eventually_nhds_subtype_iff
-/
theorem frequently_nhds_subtype_iff (s : Set α) (a : s) (P : α -> Prop) :
    (existsᶠ x : s in 𝓝 a, P x) ↔ existsᶠ x in 𝓝[s] a, P x :=
.not eventually_nhds_subtype_iff s a (¬ P ·)

/--
theorem `tendsto_nhdsWithin_iff_subtype` / 定理 `tendsto_nhdsWithin_iff_subtype`

English:
theorem tendsto_nhdsWithin_iff_subtype
  given: {s : Set α} {a : α} (h : a in s) (f : α -> β) (l : Filter β)
  proof: by
  rw [nhdsWithin_eq_map_subtype_coe h]; rw [tendsto_map'_iff]; rfl

中文:
定理 tendsto_nhdsWithin_iff_subtype
  条件: {s : Set α} {a : α} (h : a in s) (f : α -> β) (l : Filter β)
  证明: by
  rw [nhdsWithin_eq_map_subtype_coe h]; rw [tendsto_map'_iff]; rfl

Depends on / 依赖: _iff, nhdsWithin_eq_map_subtype_coe, tendsto_map
-/
theorem tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a in s) (f : α -> β) (l : Filter β) :
    Tendsto f (𝓝[s] a) l ↔ Tendsto (s.domRestrict f) (𝓝 ⟨a, h⟩) l := by
  rw [nhdsWithin_eq_map_subtype_coe h]; rw [tendsto_map'_iff]; rfl

/--
theorem `clusterPt_principal_subtype_iff_frequently` / 定理 `clusterPt_principal_subtype_iff_frequently`

English:
theorem clusterPt_principal_subtype_iff_frequently
  given: {s t : Set α} (hst : s subseteq t) {J : Set s} {a : s}
  proof: by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop)]; rw [Filter.frequently_map]; rw [clusterPt_principal_iff_frequently]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Subtype.coe

中文:
定理 clusterPt_principal_subtype_iff_frequently
  条件: {s t : Set α} (hst : s subseteq t) {J : Set s} {a : s}
  证明: by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop)]; rw [Filter.frequently_map]; rw [clusterPt_principal_iff_frequently]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Subtype.coe

Depends on / 依赖: Eventually, Eventually.of_forall, Filter, Filter.frequently_comap, Filter.frequently_map, IsInducing, SetCoe, SetCoe.exists, Subtype, Subtype.coe_mk, Topology, Topology.IsInducing.subtypeVal.nhds_eq_comap, a.prop, clusterPt_principal_iff_frequently, coe_mk, exists_and_left, exists_eq_left, frequently_comap, frequently_congr, frequently_map
-/
theorem clusterPt_principal_subtype_iff_frequently {s t : Set α} (hst : s subseteq t) {J : Set s} {a : s} :
    ClusterPt a (Filter.principal J) ↔ existsᶠ x in nhdsWithin a t, exists h : x in s, (⟨x, h⟩ : s) in J := by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop)]; rw [Filter.frequently_map]; rw [clusterPt_principal_iff_frequently]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Topology.IsInducing.subtypeVal.nhds_eq_comap]; rw [Filter.frequently_comap]; rw [Subtype.coe_mk]
  apply frequently_congr
  apply Eventually.of_forall
  intro x
  simp only [SetCoe.exists, exists_and_left, exists_eq_left]
  exact ⟨fun ⟨h, hx⟩ => ⟨hst h, h, hx⟩, fun ⟨_, hx⟩ => hx⟩

/-!
## The `nhdsSetWithin`-filter
-/

variable [TopologicalSpace β]

@[gcongr, mono]
/--
lemma `nhdsSetWithin_mono_left` / 引理 `nhdsSetWithin_mono_left`

English:
lemma nhdsSetWithin_mono_left
  given: {s s' t : Set α} (h : s subseteq s')
  statement: 𝓝ˢ[t] s <= 𝓝ˢ[t] s'
  proof: inf_le_inf_right _ nhdsSet_mono h

@[gcongr, mono]

中文:
引理 nhdsSetWithin_mono_left
  条件: {s s' t : Set α} (h : s subseteq s')
  结论: 𝓝ˢ[t] s <= 𝓝ˢ[t] s'
  证明: inf_le_inf_right _ nhdsSet_mono h

@[gcongr, mono]

Depends on / 依赖: inf_le_inf_right, nhdsSet_mono
-/
lemma nhdsSetWithin_mono_left {s s' t : Set α} (h : s subseteq s') : 𝓝ˢ[t] s <= 𝓝ˢ[t] s' :=
inf_le_inf_right _ nhdsSet_mono h

@[gcongr, mono]
/--
lemma `nhdsSetWithin_mono_right` / 引理 `nhdsSetWithin_mono_right`

English:
lemma nhdsSetWithin_mono_right
  given: {s t t' : Set α} (h : t subseteq t')
  statement: 𝓝ˢ[t] s <= 𝓝ˢ[t'] s
  proof: inf_le_inf_left _ principal_mono.2 h

中文:
引理 nhdsSetWithin_mono_right
  条件: {s t t' : Set α} (h : t subseteq t')
  结论: 𝓝ˢ[t] s <= 𝓝ˢ[t'] s
  证明: inf_le_inf_left _ principal_mono.2 h

Depends on / 依赖: inf_le_inf_left, principal_mono
-/
lemma nhdsSetWithin_mono_right {s t t' : Set α} (h : t subseteq t') : 𝓝ˢ[t] s <= 𝓝ˢ[t'] s :=
inf_le_inf_left _ principal_mono.2 h

/--
lemma `nhdsSetWithin_hasBasis` / 引理 `nhdsSetWithin_hasBasis`

English:
lemma nhdsSetWithin_hasBasis
  statement: {ι : Sort*} {p : ι -> Prop} {s' : ι -> Set α} {s : Set α}
  proof: h.inf_principal t

中文:
引理 nhdsSetWithin_hasBasis
  结论: {ι : Sort*} {p : ι -> 命题} {s' : ι -> Set α} {s : Set α}
  证明: h.inf_principal t

Depends on / 依赖: h.inf_principal, inf_principal
-/
lemma nhdsSetWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s' : ι -> Set α} {s : Set α}
    (h : (𝓝ˢ s).HasBasis p s') (t : Set α) : (𝓝ˢ[t] s).HasBasis p fun i => s' i inter t :=
  h.inf_principal t

/--
lemma `nhdsSetWithin_basis_open` / 引理 `nhdsSetWithin_basis_open`

English:
lemma nhdsSetWithin_basis_open
  given: (s t : Set α)
  proof: nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t

中文:
引理 nhdsSetWithin_basis_open
  条件: (s t : Set α)
  证明: nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t

Depends on / 依赖: hasBasis_nhdsSet, nhdsSetWithin_hasBasis
-/
lemma nhdsSetWithin_basis_open (s t : Set α) :
    (𝓝ˢ[t] s).HasBasis (fun u => IsOpen u ∧ s subseteq u) fun u => u inter t :=
  nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t

/--
lemma `mem_nhdsSetWithin` / 引理 `mem_nhdsSetWithin`

English:
lemma mem_nhdsSetWithin
  given: {s t u : Set α}
  statement: u in 𝓝ˢ[t] s ↔ exists v, IsOpen v ∧ s subseteq v ∧ v inter t subseteq u
  proof: by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]

中文:
引理 mem_nhdsSetWithin
  条件: {s t u : Set α}
  结论: u in 𝓝ˢ[t] s ↔ 存在 v, IsOpen v ∧ s subseteq v ∧ v inter t subseteq u
  证明: by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]

Depends on / 依赖: and_assoc, mem_iff, nhdsSetWithin_basis_open
-/
lemma mem_nhdsSetWithin {s t u : Set α} : u in 𝓝ˢ[t] s ↔ exists v, IsOpen v ∧ s subseteq v ∧ v inter t subseteq u := by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]
/--
lemma `nhdsSetWithin_singleton` / 引理 `nhdsSetWithin_singleton`

English:
lemma nhdsSetWithin_singleton
  given: {x : α} {s : Set α}
  statement: 𝓝ˢ[s] {x} = 𝓝[s] x
  proof: by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]

中文:
引理 nhdsSetWithin_singleton
  条件: {x : α} {s : Set α}
  结论: 𝓝ˢ[s] {x} = 𝓝[s] x
  证明: by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]

Depends on / 依赖: nhdsSetWithin, nhdsWithin
-/
lemma nhdsSetWithin_singleton {x : α} {s : Set α} : 𝓝ˢ[s] {x} = 𝓝[s] x := by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]
/--
lemma `nhdsSetWithin_univ` / 引理 `nhdsSetWithin_univ`

English:
lemma nhdsSetWithin_univ
  given: {s : Set α}
  statement: 𝓝ˢ[univ] s = 𝓝ˢ s
  proof: by
  simp [nhdsSetWithin]

中文:
引理 nhdsSetWithin_univ
  条件: {s : Set α}
  结论: 𝓝ˢ[univ] s = 𝓝ˢ s
  证明: by
  simp [nhdsSetWithin]

Depends on / 依赖: nhdsSetWithin
-/
lemma nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s := by
  simp [nhdsSetWithin]

/--
theorem `mem_nhdsSet` / 定理 `mem_nhdsSet`

English:
theorem mem_nhdsSet
  given: {s t : Set α}
  statement: s in 𝓝ˢ t ↔ exists u subseteq s, IsOpen u ∧ t subseteq u
  proof: by
  simp [← nhdsSetWithin_univ, mem_nhdsSetWithin, and_comm, and_assoc]

@[simp]

中文:
定理 mem_nhdsSet
  条件: {s t : Set α}
  结论: s in 𝓝ˢ t ↔ 存在 u subseteq s, IsOpen u ∧ t subseteq u
  证明: by
  simp [← nhdsSetWithin_univ, mem_nhdsSetWithin, and_comm, and_assoc]

@[simp]

Depends on / 依赖: and_assoc, and_comm, mem_nhdsSetWithin, nhdsSetWithin_univ
-/
theorem mem_nhdsSet {s t : Set α} : s in 𝓝ˢ t ↔ exists u subseteq s, IsOpen u ∧ t subseteq u := by
  simp [← nhdsSetWithin_univ, mem_nhdsSetWithin, and_comm, and_assoc]

@[simp]
/--
lemma `nhdsSetWithin_univ'` / 引理 `nhdsSetWithin_univ'`

English:
lemma nhdsSetWithin_univ'
  given: {s : Set α}
  statement: 𝓝ˢ[s] univ = 𝓟 s
  proof: by
  simp [nhdsSetWithin]

@[simp]

中文:
引理 nhdsSetWithin_univ'
  条件: {s : Set α}
  结论: 𝓝ˢ[s] univ = 𝓟 s
  证明: by
  simp [nhdsSetWithin]

@[simp]

Depends on / 依赖: nhdsSetWithin
-/
lemma nhdsSetWithin_univ' {s : Set α} : 𝓝ˢ[s] univ = 𝓟 s := by
  simp [nhdsSetWithin]

@[simp]
/--
lemma `nhdsSetWithin_self` / 引理 `nhdsSetWithin_self`

English:
lemma nhdsSetWithin_self
  given: {s : Set α}
  statement: 𝓝ˢ[s] s = 𝓟 s
  proof: by
  simp [nhdsSetWithin, principal_le_nhdsSet]

中文:
引理 nhdsSetWithin_self
  条件: {s : Set α}
  结论: 𝓝ˢ[s] s = 𝓟 s
  证明: by
  simp [nhdsSetWithin, principal_le_nhdsSet]

Depends on / 依赖: nhdsSetWithin, principal_le_nhdsSet
-/
lemma nhdsSetWithin_self {s : Set α} : 𝓝ˢ[s] s = 𝓟 s := by
  simp [nhdsSetWithin, principal_le_nhdsSet]

/--
lemma `nhdsSetWithin_eq_principal_of_subset` / 引理 `nhdsSetWithin_eq_principal_of_subset`

English:
lemma nhdsSetWithin_eq_principal_of_subset
  given: {s t : Set α} (h : t subseteq s)
  statement: 𝓝ˢ[t] s = 𝓟 t
  proof: by
  simp [nhdsSetWithin, (principal_mono.2 h).trans principal_le_nhdsSet]

@[simp]

中文:
引理 nhdsSetWithin_eq_principal_of_subset
  条件: {s t : Set α} (h : t subseteq s)
  结论: 𝓝ˢ[t] s = 𝓟 t
  证明: by
  simp [nhdsSetWithin, (principal_mono.2 h).trans principal_le_nhdsSet]

@[simp]

Depends on / 依赖: nhdsSetWithin, principal_le_nhdsSet, principal_mono
-/
lemma nhdsSetWithin_eq_principal_of_subset {s t : Set α} (h : t subseteq s) : 𝓝ˢ[t] s = 𝓟 t := by
  simp [nhdsSetWithin, (principal_mono.2 h).trans principal_le_nhdsSet]

@[simp]
/--
lemma `nhdsSetWithin_empty` / 引理 `nhdsSetWithin_empty`

English:
lemma nhdsSetWithin_empty
  given: {s : Set α}
  statement: 𝓝ˢ[∅] s = ⊥
  proof: by
  simp [nhdsSetWithin]

@[simp]

中文:
引理 nhdsSetWithin_empty
  条件: {s : Set α}
  结论: 𝓝ˢ[∅] s = ⊥
  证明: by
  simp [nhdsSetWithin]

@[simp]

Depends on / 依赖: nhdsSetWithin
-/
lemma nhdsSetWithin_empty {s : Set α} : 𝓝ˢ[∅] s = ⊥ := by
  simp [nhdsSetWithin]

@[simp]
/--
lemma `nhdsSetWithin_empty'` / 引理 `nhdsSetWithin_empty'`

English:
lemma nhdsSetWithin_empty'
  given: {s : Set α}
  statement: 𝓝ˢ[s] ∅ = ⊥
  proof: by
  simp [nhdsSetWithin]

中文:
引理 nhdsSetWithin_empty'
  条件: {s : Set α}
  结论: 𝓝ˢ[s] ∅ = ⊥
  证明: by
  simp [nhdsSetWithin]

Depends on / 依赖: nhdsSetWithin
-/
lemma nhdsSetWithin_empty' {s : Set α} : 𝓝ˢ[s] ∅ = ⊥ := by
  simp [nhdsSetWithin]

/--
lemma `principal_inter_le_nhdsSetWithin` / 引理 `principal_inter_le_nhdsSetWithin`

English:
lemma principal_inter_le_nhdsSetWithin
  given: {s t : Set α}
  statement: 𝓟 (s inter t) <= 𝓝ˢ[t] s
  proof: by
simpa [nhdsSetWithin] using inf_le_of_left_le (b := 𝓟 t) principal_le_nhdsSet

中文:
引理 principal_inter_le_nhdsSetWithin
  条件: {s t : Set α}
  结论: 𝓟 (s inter t) <= 𝓝ˢ[t] s
  证明: by
simpa [nhdsSetWithin] using inf_le_of_left_le (b := 𝓟 t) principal_le_nhdsSet

Depends on / 依赖: inf_le_of_left_le, nhdsSetWithin, principal_le_nhdsSet
-/
lemma principal_inter_le_nhdsSetWithin {s t : Set α} : 𝓟 (s inter t) <= 𝓝ˢ[t] s := by
simpa [nhdsSetWithin] using inf_le_of_left_le (b := 𝓟 t) principal_le_nhdsSet

/--
lemma `nhdsSetWithin_prod_le` / 引理 `nhdsSetWithin_prod_le`

English:
lemma nhdsSetWithin_prod_le
  given: {s s' : Set α} {t t' : Set β}
  proof: by
simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le nhdsSet_prod_le _ _

中文:
引理 nhdsSetWithin_prod_le
  条件: {s s' : Set α} {t t' : Set β}
  证明: by
simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le nhdsSet_prod_le _ _

Depends on / 依赖: inf_le_of_left_le, nhdsSetWithin, nhdsSet_prod_le, prod_inf_prod
-/
lemma nhdsSetWithin_prod_le {s s' : Set α} {t t' : Set β} :
    𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) <= 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le nhdsSet_prod_le _ _

/--
lemma `mem_nhdsSet_induced` / 引理 `mem_nhdsSet_induced`

English:
lemma mem_nhdsSet_induced
  given: {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s u : Set α)
  proof: by
  let := t.induced f
  simp_rw [mem_nhdsSet_iff_exists, isOpen_induced_iff]
  refine ⟨fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_, fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_⟩
  · refine ⟨v', ⟨v', hv'.1, ?_, subset_rfl⟩, hv'.2.trans_subset hv.2⟩
    exact (image_mono hv.1).trans (by simp [hv'])
  · exact ⟨f ⁻¹' v', ⟨v', hv'.1

中文:
引理 mem_nhdsSet_induced
  条件: {α β : 类型} {t : TopologicalSpace β} (f : α -> β) (s u : Set α)
  证明: by
  let := t.induced f
  simp_rw [mem_nhdsSet_iff_exists, isOpen_induced_iff]
  refine ⟨fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_, fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_⟩
  · refine ⟨v', ⟨v', hv'.1, ?_, subset_rfl⟩, hv'.2.trans_subset hv.2⟩
    exact (image_mono hv.1).trans (by simp [hv'])
  · exact ⟨f ⁻¹' v', ⟨v', hv'.1

Depends on / 依赖: image_mono, image_subset_iff, induced, isOpen_induced_iff, mem_nhdsSet_iff_exists, preimage_mono, simp_rw, subset_rfl, t.induced, trans_subset
-/
lemma mem_nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s u : Set α) :
    u in @nhdsSet α (t.induced f) s ↔ exists v in 𝓝ˢ (f '' s), f ⁻¹' v subseteq u := by
  let := t.induced f
  simp_rw [mem_nhdsSet_iff_exists, isOpen_induced_iff]
  refine ⟨fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_, fun ⟨v, ⟨v', hv'⟩, hv⟩ => ?_⟩
  · refine ⟨v', ⟨v', hv'.1, ?_, subset_rfl⟩, hv'.2.trans_subset hv.2⟩
    exact (image_mono hv.1).trans (by simp [hv'])
  · exact ⟨f ⁻¹' v', ⟨v', hv'.1, rfl⟩, image_subset_iff.1 hv'.2.1, (preimage_mono hv'.2.2).trans hv⟩

/--
lemma `nhdsSet_induced` / 引理 `nhdsSet_induced`

English:
lemma nhdsSet_induced
  given: {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s : Set α)
  proof: by
  ext s
  rw [mem_nhdsSet_induced]; rw [mem_comap]

中文:
引理 nhdsSet_induced
  条件: {α β : 类型} {t : TopologicalSpace β} (f : α -> β) (s : Set α)
  证明: by
  ext s
  rw [mem_nhdsSet_induced]; rw [mem_comap]

Depends on / 依赖: mem_comap, mem_nhdsSet_induced
-/
lemma nhdsSet_induced {α β : Type*} {t : TopologicalSpace β} (f : α -> β) (s : Set α) :
    @nhdsSet α (t.induced f) s = comap f (𝓝ˢ (f '' s)) := by
  ext s
  rw [mem_nhdsSet_induced]; rw [mem_comap]

/--
lemma `map_nhdsSet_induced_eq` / 引理 `map_nhdsSet_induced_eq`

English:
lemma map_nhdsSet_induced_eq
  given: {α β : Type*} {t : TopologicalSpace β} {f : α -> β} (s : Set α)
  proof: by
  rw [nhdsSet_induced]; rw [Filter.map_comap]; rw [nhdsSetWithin]

中文:
引理 map_nhdsSet_induced_eq
  条件: {α β : 类型} {t : TopologicalSpace β} {f : α -> β} (s : Set α)
  证明: by
  rw [nhdsSet_induced]; rw [Filter.map_comap]; rw [nhdsSetWithin]

Depends on / 依赖: Filter, Filter.map_comap, map_comap, nhdsSetWithin, nhdsSet_induced
-/
lemma map_nhdsSet_induced_eq {α β : Type*} {t : TopologicalSpace β} {f : α -> β} (s : Set α) :
    map f (@nhdsSet α (t.induced f) s) = 𝓝ˢ[range f] (f '' s) := by
  rw [nhdsSet_induced]; rw [Filter.map_comap]; rw [nhdsSetWithin]

/--
lemma `Topology.IsInducing.map_nhdsSet_eq` / 引理 `Topology.IsInducing.map_nhdsSet_eq`

English:
lemma Topology.IsInducing.map_nhdsSet_eq
  given: {f : α -> β} (hf : IsInducing f) (s : Set α)
  proof: hf.eq_induced ▸ map_nhdsSet_induced_eq s

中文:
引理 Topology.IsInducing.map_nhdsSet_eq
  条件: {f : α -> β} (hf : IsInducing f) (s : Set α)
  证明: hf.eq_induced ▸ map_nhdsSet_induced_eq s

Depends on / 依赖: eq_induced, hf.eq_induced, map_nhdsSet_induced_eq
-/
lemma Topology.IsInducing.map_nhdsSet_eq {f : α -> β} (hf : IsInducing f) (s : Set α) :
    (𝓝ˢ s).map f = 𝓝ˢ[range f] (f '' s) :=
  hf.eq_induced ▸ map_nhdsSet_induced_eq s

/--
lemma `map_nhdsSet_subtype_val` / 引理 `map_nhdsSet_subtype_val`

English:
lemma map_nhdsSet_subtype_val
  given: {s : Set α} (t : Set s)
  proof: by
  rw [IsInducing.subtypeVal.map_nhdsSet_eq]; rw [Subtype.range_val]

中文:
引理 map_nhdsSet_subtype_val
  条件: {s : Set α} (t : Set s)
  证明: by
  rw [IsInducing.subtypeVal.map_nhdsSet_eq]; rw [Subtype.range_val]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.map_nhdsSet_eq, Subtype, Subtype.range_val, map_nhdsSet_eq, range_val, subtypeVal
-/
lemma map_nhdsSet_subtype_val {s : Set α} (t : Set s) :
    map (↑) (𝓝ˢ t) = 𝓝ˢ[s] ((↑) '' t) := by
  rw [IsInducing.subtypeVal.map_nhdsSet_eq]; rw [Subtype.range_val]

/--
lemma `mem_nhdsSet_subtype_iff_nhdsSetWithin` / 引理 `mem_nhdsSet_subtype_iff_nhdsSetWithin`

English:
lemma mem_nhdsSet_subtype_iff_nhdsSetWithin
  given: {s : Set α} {t u : Set s}
  proof: by
  rw [← map_nhdsSet_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]

中文:
引理 mem_nhdsSet_subtype_iff_nhdsSetWithin
  条件: {s : Set α} {t u : Set s}
  证明: by
  rw [← map_nhdsSet_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]

Depends on / 依赖: Subtype, Subtype.val_injective, image_mem_map_iff, map_nhdsSet_subtype_val, val_injective
-/
lemma mem_nhdsSet_subtype_iff_nhdsSetWithin {s : Set α} {t u : Set s} :
    u in 𝓝ˢ t ↔ (↑) '' u in 𝓝ˢ[s] ((↑) '' t) := by
  rw [← map_nhdsSet_subtype_val]; rw [image_mem_map_iff Subtype.val_injective]
