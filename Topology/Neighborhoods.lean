/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Closure

/-!
# Neighborhoods in topological spaces

Each point `x` of `X` gets a neighborhood filter `𝓝 x`.

## Tags

neighborhood
-/

public section

open Set Filter Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {α : Type*} {x : X} {s t : Set X}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `nhds_def'` / 定理 `nhds_def'`

English:
theorem nhds_def'
  given: (x : X)
  statement: 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x in s), 𝓟 s
  proof: by
  simp only [nhds_def, mem_ofPred_eq, @and_comm (x in _), iInf_and]

中文:
定理 nhds_def'
  条件: (x : X)
  结论: 𝓝 x = ⨅ (s : 集合 X) (_ : 是开集 s) (_ : x in s), 𝓟 s
  证明: by
  simp only [nhds_def, mem_ofPred_eq, @and_comm (x in _), iInf_and]

Depends on / 依赖: and_comm, iInf_and, mem_ofPred_eq, nhds_def
-/
theorem nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x in s), 𝓟 s := by
  simp only [nhds_def, mem_ofPred_eq, @and_comm (x in _), iInf_and]

/--
theorem `nhds_basis_opens` / 定理 `nhds_basis_opens`

English:
theorem nhds_basis_opens
  given: (x : X)
  proof: by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s inter t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

中文:
定理 nhds_basis_opens
  条件: (x : X)
  证明: by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s inter t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

Depends on / 依赖: IsOpen, IsOpen.inter, hasBasis_biInf_principal, inter_subset_left, inter_subset_right, isOpen_univ, mem_univ, nhds_def
-/
theorem nhds_basis_opens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s inter t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

/--
theorem `nhds_basis_closeds` / 定理 `nhds_basis_closeds`

English:
theorem nhds_basis_closeds
  given: (x : X)
  statement: (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl
  proof: ⟨fun t => (nhds_basis_opens x).mem_iff.trans
compl_surjective.exists.trans by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]

中文:
定理 nhds_basis_closeds
  条件: (x : X)
  结论: (𝓝 x).有基 (fun s : 集合 X => x ∉ s ∧ 是闭集 s) compl
  证明: ⟨fun t => (nhds_basis_opens x).mem_iff.trans
compl_surjective.exists.trans by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]

Depends on / 依赖: compl_surjective, compl_surjective.exists.trans, isOpen_compl_iff, mem_compl_iff, mem_iff, mem_iff.trans, nhds_basis_opens
-/
theorem nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl :=
⟨fun t => (nhds_basis_opens x).mem_iff.trans
compl_surjective.exists.trans by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]
/--
theorem `lift'_nhds_interior` / 定理 `lift'_nhds_interior`

English:
theorem lift'_nhds_interior
  given: (x : X)
  statement: (𝓝 x).lift' interior = 𝓝 x
  proof: (nhds_basis_opens x).lift'_interior_eq_self fun _ => And.right

中文:
定理 lift'_nhds_interior
  条件: (x : X)
  结论: (𝓝 x).lift' interior = 𝓝 x
  证明: (nhds_basis_opens x).lift'_interior_eq_self fun _ => And.right

Depends on / 依赖: And.right, _interior_eq_self, nhds_basis_opens
-/
theorem lift'_nhds_interior (x : X) : (𝓝 x).lift' interior = 𝓝 x :=
  (nhds_basis_opens x).lift'_interior_eq_self fun _ => And.right

/--
theorem `Filter.HasBasis.nhds_interior` / 定理 `Filter.HasBasis.nhds_interior`

English:
theorem Filter.HasBasis.nhds_interior
  statement: {x : X} {p : ι -> Prop} {s : ι -> Set X}
  proof: lift'_nhds_interior x ▸ h.lift'_interior

中文:
定理 滤子.有基.nhds_interior
  结论: {x : X} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: lift'_nhds_interior x ▸ h.lift'_interior

Depends on / 依赖: _interior, _nhds_interior, h.lift
-/
theorem Filter.HasBasis.nhds_interior {x : X} {p : ι -> Prop} {s : ι -> Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p (interior <| s ·) :=
  lift'_nhds_interior x ▸ h.lift'_interior

/--
theorem `le_nhds_iff` / 定理 `le_nhds_iff`

English:
theorem le_nhds_iff
  given: {f}
  statement: f <= 𝓝 x ↔ forall s : Set X, x in s -> IsOpen s -> s in f
  proof: by simp [nhds_def]

中文:
定理 le_nhds_iff
  条件: {f}
  结论: f <= 𝓝 x ↔ 对任意 s : 集合 X, x in s -> 是开集 s -> s in f
  证明: by simp [nhds_def]

Depends on / 依赖: nhds_def
-/
theorem le_nhds_iff {f} : f <= 𝓝 x ↔ forall s : Set X, x in s -> IsOpen s -> s in f := by simp [nhds_def]

/--
theorem `nhds_le_of_le` / 定理 `nhds_le_of_le`

English:
theorem nhds_le_of_le
  given: {f} (h : x in s) (o : IsOpen s) (sf : 𝓟 s <= f)
  statement: 𝓝 x <= f
  proof: by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf

中文:
定理 nhds_le_of_le
  条件: {f} (h : x in s) (o : 是开集 s) (sf : 𝓟 s <= f)
  结论: 𝓝 x <= f
  证明: by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf

Depends on / 依赖: nhds_def
-/
theorem nhds_le_of_le {f} (h : x in s) (o : IsOpen s) (sf : 𝓟 s <= f) : 𝓝 x <= f := by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf

/--
theorem `mem_nhds_iff` / 定理 `mem_nhds_iff`

English:
theorem mem_nhds_iff
  statement: s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ x in t
  proof: (nhds_basis_opens x).mem_iff.trans exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

中文:
定理 mem_nhds_iff
  结论: s in 𝓝 x ↔ 存在 t subseteq s, 是开集 t ∧ x in t
  证明: (nhds_basis_opens x).mem_iff.trans exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

Depends on / 依赖: exists_congr, mem_iff, mem_iff.trans, nhds_basis_opens
-/
theorem mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ x in t :=
(nhds_basis_opens x).mem_iff.trans exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

/--
theorem `eventually_nhds_iff` / 定理 `eventually_nhds_iff`

English:
theorem eventually_nhds_iff
  given: {p : X -> Prop}
  proof: mem_nhds_iff.trans by simp only [subset_def, mem_ofPred_eq]

中文:
定理 eventually_nhds_iff
  条件: {p : X -> 命题}
  证明: mem_nhds_iff.trans by simp only [subset_def, mem_ofPred_eq]

Depends on / 依赖: mem_nhds_iff, mem_nhds_iff.trans, mem_ofPred_eq, subset_def
-/
theorem eventually_nhds_iff {p : X -> Prop} :
    (forallᶠ y in 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t :=
mem_nhds_iff.trans by simp only [subset_def, mem_ofPred_eq]

/--
theorem `frequently_nhds_iff` / 定理 `frequently_nhds_iff`

English:
theorem frequently_nhds_iff
  given: {p : X -> Prop}
  proof: (nhds_basis_opens x).frequently_iff.trans by simp

中文:
定理 frequently_nhds_iff
  条件: {p : X -> 命题}
  证明: (nhds_basis_opens x).frequently_iff.trans by simp

Depends on / 依赖: frequently_iff, frequently_iff.trans, nhds_basis_opens
-/
theorem frequently_nhds_iff {p : X -> Prop} :
    (existsᶠ y in 𝓝 x, p y) ↔ forall U : Set X, x in U -> IsOpen U -> exists y in U, p y :=
(nhds_basis_opens x).frequently_iff.trans by simp

/--
theorem `mem_interior_iff_mem_nhds` / 定理 `mem_interior_iff_mem_nhds`

English:
theorem mem_interior_iff_mem_nhds
  statement: x in interior s ↔ s in 𝓝 x
  proof: mem_interior.trans mem_nhds_iff.symm

中文:
定理 mem_interior_iff_mem_nhds
  结论: x in interior s ↔ s in 𝓝 x
  证明: mem_interior.trans mem_nhds_iff.symm

Depends on / 依赖: mem_interior, mem_interior.trans, mem_nhds_iff, mem_nhds_iff.symm
-/
theorem mem_interior_iff_mem_nhds : x in interior s ↔ s in 𝓝 x :=
  mem_interior.trans mem_nhds_iff.symm

/--
theorem `map_nhds` / 定理 `map_nhds`

English:
theorem map_nhds
  given: {f : X -> α}
  proof: ((nhds_basis_opens x).map f).eq_biInf

中文:
定理 map_nhds
  条件: {f : X -> α}
  证明: ((nhds_basis_opens x).map f).eq_biInf

Depends on / 依赖: eq_biInf, nhds_basis_opens
-/
theorem map_nhds {f : X -> α} :
    map f (𝓝 x) = ⨅ s in { s : Set X | x in s ∧ IsOpen s }, 𝓟 (f '' s) :=
  ((nhds_basis_opens x).map f).eq_biInf

/--
theorem `mem_of_mem_nhds` / 定理 `mem_of_mem_nhds`

English:
theorem mem_of_mem_nhds
  statement: s in 𝓝 x -> x in s
  proof: fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs

中文:
定理 mem_of_mem_nhds
  结论: s in 𝓝 x -> x in s
  证明: fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs
-/
theorem mem_of_mem_nhds : s in 𝓝 x -> x in s := fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs

/--
theorem `Filter.Eventually.self_of_nhds` / 定理 `Filter.Eventually.self_of_nhds`

English:
theorem Filter.Eventually.self_of_nhds
  given: {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p y)
  statement: p x
  proof: mem_of_mem_nhds h

中文:
定理 滤子.Eventually.self_of_nhds
  条件: {p : X -> 命题} (h : 对任意ᶠ y in 𝓝 x, p y)
  结论: p x
  证明: mem_of_mem_nhds h

Depends on / 依赖: mem_of_mem_nhds
-/
theorem Filter.Eventually.self_of_nhds {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : p x :=
  mem_of_mem_nhds h

/--
theorem `IsOpen.mem_nhds` / 定理 `IsOpen.mem_nhds`

English:
theorem IsOpen.mem_nhds
  given: (hs : IsOpen s) (hx : x in s)
  statement: s in 𝓝 x
  proof: mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩

中文:
定理 是开集.mem_nhds
  条件: (hs : 是开集 s) (hx : x in s)
  结论: s in 𝓝 x
  证明: mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩

Depends on / 依赖: Subset, Subset.refl, mem_nhds_iff
-/
theorem IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 x :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩

/--
theorem `IsOpen.mem_nhds_iff` / 定理 `IsOpen.mem_nhds_iff`

English:
theorem IsOpen.mem_nhds_iff
  given: (hs : IsOpen s)
  statement: s in 𝓝 x ↔ x in s
  proof: ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩

中文:
定理 是开集.mem_nhds_iff
  条件: (hs : 是开集 s)
  结论: s in 𝓝 x ↔ x in s
  证明: ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩
-/
protected theorem IsOpen.mem_nhds_iff (hs : IsOpen s) : s in 𝓝 x ↔ x in s :=
  ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩

/--
theorem `IsClosed.compl_mem_nhds` / 定理 `IsClosed.compl_mem_nhds`

English:
theorem IsClosed.compl_mem_nhds
  given: (hs : IsClosed s) (hx : x ∉ s)
  statement: sᶜ in 𝓝 x
  proof: hs.isOpen_compl.mem_nhds (mem_compl hx)

中文:
定理 是闭集.compl_mem_nhds
  条件: (hs : 是闭集 s) (hx : x ∉ s)
  结论: sᶜ in 𝓝 x
  证明: hs.isOpen_compl.mem_nhds (mem_compl hx)

Depends on / 依赖: hs.isOpen_compl.mem_nhds, isOpen_compl, mem_compl, mem_nhds
-/
theorem IsClosed.compl_mem_nhds (hs : IsClosed s) (hx : x ∉ s) : sᶜ in 𝓝 x :=
  hs.isOpen_compl.mem_nhds (mem_compl hx)

/--
theorem `IsOpen.eventually_mem` / 定理 `IsOpen.eventually_mem`

English:
theorem IsOpen.eventually_mem
  given: (hs : IsOpen s) (hx : x in s)
  proof: IsOpen.mem_nhds hs hx

中文:
定理 是开集.eventually_mem
  条件: (hs : 是开集 s) (hx : x in s)
  证明: IsOpen.mem_nhds hs hx

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, mem_nhds
-/
theorem IsOpen.eventually_mem (hs : IsOpen s) (hx : x in s) :
    forallᶠ x in 𝓝 x, x in s :=
  IsOpen.mem_nhds hs hx

/--
theorem `nhds_basis_opens'` / 定理 `nhds_basis_opens'`

English:
theorem nhds_basis_opens'
  given: (x : X)
  proof: by
  convert! nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

中文:
定理 nhds_basis_opens'
  条件: (x : X)
  证明: by
  convert! nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

Depends on / 依赖: IsOpen, IsOpen.mem_nhds_iff, and_congr_left_iff, convert, mem_nhds_iff, nhds_basis_opens
-/
theorem nhds_basis_opens' (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsOpen s) fun x => x := by
  convert! nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

/--
theorem `exists_open_set_nhds` / 定理 `exists_open_set_nhds`

English:
theorem exists_open_set_nhds
  given: {U : Set X} (h : forall x in s, U in 𝓝 x)
  proof: ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 h x hx, isOpen_interior, interior_subset⟩

中文:
定理 存在_open_set_nhds
  条件: {U : 集合 X} (h : 对任意 x in s, U in 𝓝 x)
  证明: ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 h x hx, isOpen_interior, interior_subset⟩

Depends on / 依赖: interior, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds
-/
theorem exists_open_set_nhds {U : Set X} (h : forall x in s, U in 𝓝 x) :
    exists V : Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U :=
⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 h x hx, isOpen_interior, interior_subset⟩

/--
theorem `exists_open_set_nhds'` / 定理 `exists_open_set_nhds'`

English:
theorem exists_open_set_nhds'
  given: {U : Set X} (h : U in ⨆ x in s, 𝓝 x)
  proof: exists_open_set_nhds (by simpa using h)

中文:
定理 存在_open_set_nhds'
  条件: {U : 集合 X} (h : U in ⨆ x in s, 𝓝 x)
  证明: exists_open_set_nhds (by simpa using h)

Depends on / 依赖: exists_open_set_nhds
-/
theorem exists_open_set_nhds' {U : Set X} (h : U in ⨆ x in s, 𝓝 x) :
    exists V : Set X, s subseteq V ∧ IsOpen V ∧ V subseteq U :=
  exists_open_set_nhds (by simpa using h)

/--
theorem `Filter.Eventually.eventually_nhds` / 定理 `Filter.Eventually.eventually_nhds`

English:
theorem Filter.Eventually.eventually_nhds
  given: {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p y)
  proof: let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]

中文:
定理 滤子.Eventually.eventually_nhds
  条件: {p : X -> 命题} (h : 对任意ᶠ y in 𝓝 x, p y)
  证明: let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]

Depends on / 依赖: eventually_nhds_iff
-/
theorem Filter.Eventually.eventually_nhds {p : X -> Prop} (h : forallᶠ y in 𝓝 x, p y) :
    forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]
/--
theorem `eventually_eventually_nhds` / 定理 `eventually_eventually_nhds`

English:
theorem eventually_eventually_nhds
  given: {p : X -> Prop}
  proof: ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]

中文:
定理 eventually_eventually_nhds
  条件: {p : X -> 命题}
  证明: ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]

Depends on / 依赖: eventually_nhds, h.eventually_nhds, h.self_of_nhds, self_of_nhds
-/
theorem eventually_eventually_nhds {p : X -> Prop} :
    (forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝 x, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]
/--
theorem `frequently_frequently_nhds` / 定理 `frequently_frequently_nhds`

English:
theorem frequently_frequently_nhds
  given: {p : X -> Prop}
  proof: by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]

中文:
定理 frequently_frequently_nhds
  条件: {p : X -> 命题}
  证明: by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]

Depends on / 依赖: eventually_eventually_nhds, not_frequently, not_iff_not
-/
theorem frequently_frequently_nhds {p : X -> Prop} :
    (existsᶠ x' in 𝓝 x, existsᶠ x'' in 𝓝 x', p x'') ↔ existsᶠ x in 𝓝 x, p x := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]
/--
theorem `eventually_mem_nhds_iff` / 定理 `eventually_mem_nhds_iff`

English:
theorem eventually_mem_nhds_iff
  statement: (forallᶠ x' in 𝓝 x, s in 𝓝 x') ↔ s in 𝓝 x
  proof: eventually_eventually_nhds

@[simp]

中文:
定理 eventually_mem_nhds_iff
  结论: (对任意ᶠ x' in 𝓝 x, s in 𝓝 x') ↔ s in 𝓝 x
  证明: eventually_eventually_nhds

@[simp]

Depends on / 依赖: eventually_eventually_nhds
-/
theorem eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s in 𝓝 x') ↔ s in 𝓝 x :=
  eventually_eventually_nhds

@[simp]
/--
theorem `nhds_bind_nhds` / 定理 `nhds_bind_nhds`

English:
theorem nhds_bind_nhds
  statement: (𝓝 x).bind 𝓝 = 𝓝 x
  proof: Filter.ext fun _ => eventually_eventually_nhds

@[simp]

中文:
定理 nhds_bind_nhds
  结论: (𝓝 x).bind 𝓝 = 𝓝 x
  证明: Filter.ext fun _ => eventually_eventually_nhds

@[simp]

Depends on / 依赖: Filter, Filter.ext, eventually_eventually_nhds
-/
theorem nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x :=
  Filter.ext fun _ => eventually_eventually_nhds

@[simp]
/--
theorem `eventually_eventuallyEq_nhds` / 定理 `eventually_eventuallyEq_nhds`

English:
theorem eventually_eventuallyEq_nhds
  given: {f g : X -> α}
  proof: eventually_eventually_nhds

中文:
定理 eventually_eventuallyEq_nhds
  条件: {f g : X -> α}
  证明: eventually_eventually_nhds

Depends on / 依赖: eventually_eventually_nhds
-/
theorem eventually_eventuallyEq_nhds {f g : X -> α} :
    (forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

/--
theorem `Filter.EventuallyEq.eq_of_nhds` / 定理 `Filter.EventuallyEq.eq_of_nhds`

English:
theorem Filter.EventuallyEq.eq_of_nhds
  given: {f g : X -> α} (h : f =ᶠ[𝓝 x] g)
  statement: f x = g x
  proof: h.self_of_nhds

@[simp]

中文:
定理 滤子.EventuallyEq.eq_of_nhds
  条件: {f g : X -> α} (h : f =ᶠ[𝓝 x] g)
  结论: f x = g x
  证明: h.self_of_nhds

@[simp]

Depends on / 依赖: h.self_of_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.eq_of_nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) : f x = g x :=
  h.self_of_nhds

@[simp]
/--
theorem `eventually_eventuallyLE_nhds` / 定理 `eventually_eventuallyLE_nhds`

English:
theorem eventually_eventuallyLE_nhds
  given: [LE α] {f g : X -> α}
  proof: eventually_eventually_nhds

中文:
定理 eventually_eventuallyLE_nhds
  条件: [LE α] {f g : X -> α}
  证明: eventually_eventually_nhds

Depends on / 依赖: eventually_eventually_nhds
-/
theorem eventually_eventuallyLE_nhds [LE α] {f g : X -> α} :
    (forallᶠ y in 𝓝 x, f <=ᶠ[𝓝 y] g) ↔ f <=ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

/--
theorem `Filter.EventuallyEq.eventuallyEq_nhds` / 定理 `Filter.EventuallyEq.eventuallyEq_nhds`

English:
theorem Filter.EventuallyEq.eventuallyEq_nhds
  given: {f g : X -> α} (h : f =ᶠ[𝓝 x] g)
  proof: h.eventually_nhds

中文:
定理 滤子.EventuallyEq.eventuallyEq_nhds
  条件: {f g : X -> α} (h : f =ᶠ[𝓝 x] g)
  证明: h.eventually_nhds

Depends on / 依赖: eventually_nhds, h.eventually_nhds
-/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : X -> α} (h : f =ᶠ[𝓝 x] g) :
    forallᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds

/--
theorem `Filter.EventuallyLE.eventuallyLE_nhds` / 定理 `Filter.EventuallyLE.eventuallyLE_nhds`

English:
theorem Filter.EventuallyLE.eventuallyLE_nhds
  given: [LE α] {f g : X -> α} (h : f <=ᶠ[𝓝 x] g)
  proof: h.eventually_nhds

中文:
定理 滤子.EventuallyLE.eventuallyLE_nhds
  条件: [LE α] {f g : X -> α} (h : f <=ᶠ[𝓝 x] g)
  证明: h.eventually_nhds

Depends on / 依赖: eventually_nhds, h.eventually_nhds
-/
theorem Filter.EventuallyLE.eventuallyLE_nhds [LE α] {f g : X -> α} (h : f <=ᶠ[𝓝 x] g) :
    forallᶠ y in 𝓝 x, f <=ᶠ[𝓝 y] g :=
  h.eventually_nhds

/--
theorem `all_mem_nhds` / 定理 `all_mem_nhds`

English:
theorem all_mem_nhds
  given: (x : X) (P : Set X -> Prop) (hP : forall s t, s subseteq t -> P s -> P t)
  proof: ((nhds_basis_opens x).forall_iff hP).trans by simp only [@and_comm (x in _), and_imp]

中文:
定理 all_mem_nhds
  条件: (x : X) (P : 集合 X -> 命题) (hP : 对任意 s t, s subseteq t -> P s -> P t)
  证明: ((nhds_basis_opens x).forall_iff hP).trans by simp only [@and_comm (x in _), and_imp]

Depends on / 依赖: and_comm, and_imp, forall_iff, nhds_basis_opens
-/
theorem all_mem_nhds (x : X) (P : Set X -> Prop) (hP : forall s t, s subseteq t -> P s -> P t) :
    (forall s in 𝓝 x, P s) ↔ forall s, IsOpen s -> x in s -> P s :=
((nhds_basis_opens x).forall_iff hP).trans by simp only [@and_comm (x in _), and_imp]

/--
theorem `all_mem_nhds_filter` / 定理 `all_mem_nhds_filter`

English:
theorem all_mem_nhds_filter
  statement: (x : X) (f : Set X -> Set α) (hf : forall s t, s subseteq t -> f s subseteq f t)
  proof: all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

中文:
定理 all_mem_nhds_filter
  结论: (x : X) (f : 集合 X -> 集合 α) (hf : 对任意 s t, s subseteq t -> f s subseteq f t)
  证明: all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

Depends on / 依赖: all_mem_nhds, mem_of_superset
-/
theorem all_mem_nhds_filter (x : X) (f : Set X -> Set α) (hf : forall s t, s subseteq t -> f s subseteq f t)
    (l : Filter α) : (forall s in 𝓝 x, f s in l) ↔ forall s, IsOpen s -> x in s -> f s in l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  given: {f : α -> X} {l : Filter α}
  proof: all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _

中文:
定理 tendsto_nhds
  条件: {f : α -> X} {l : 滤子 α}
  证明: all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _

Depends on / 依赖: all_mem_nhds_filter, preimage_mono
-/
theorem tendsto_nhds {f : α -> X} {l : Filter α} :
    Tendsto f l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> f ⁻¹' s in l :=
  all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _

/--
theorem `tendsto_atTop_nhds` / 定理 `tendsto_atTop_nhds`

English:
theorem tendsto_atTop_nhds
  given: [Nonempty α] [SemilatticeSup α] {f : α -> X}
  proof: (atTop_basis.tendsto_iff (nhds_basis_opens x)).trans by
    simp only [and_imp, true_and, mem_Ici]

中文:
定理 tendsto_atTop_nhds
  条件: [非空 α] [SemilatticeSup α] {f : α -> X}
  证明: (atTop_basis.tendsto_iff (nhds_basis_opens x)).trans by
    simp only [and_imp, true_and, mem_Ici]

Depends on / 依赖: and_imp, atTop_basis, atTop_basis.tendsto_iff, mem_Ici, nhds_basis_opens, tendsto_iff, true_and
-/
theorem tendsto_atTop_nhds [Nonempty α] [SemilatticeSup α] {f : α -> X} :
    Tendsto f atTop (𝓝 x) ↔ forall U : Set X, x in U -> IsOpen U -> exists N, forall n, N <= n -> f n in U :=
(atTop_basis.tendsto_iff (nhds_basis_opens x)).trans by
    simp only [and_imp, true_and, mem_Ici]

/--
theorem `tendsto_const_nhds` / 定理 `tendsto_const_nhds`

English:
theorem tendsto_const_nhds
  given: {f : Filter α}
  statement: Tendsto (fun _ : α => x) f (𝓝 x)
  proof: tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha

中文:
定理 tendsto_const_nhds
  条件: {f : 滤子 α}
  结论: 收敛 (fun _ : α => x) f (𝓝 x)
  证明: tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha

Depends on / 依赖: tendsto_nhds, tendsto_nhds.mpr, univ_mem
-/
theorem tendsto_const_nhds {f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha

/--
theorem `tendsto_atTop_of_eventually_const` / 定理 `tendsto_atTop_of_eventually_const`

English:
theorem tendsto_atTop_of_eventually_const
  statement: {ι : Type*} [Preorder ι]
  proof: Tendsto.congr' (EventuallyEq.symm ((eventually_ge_atTop i₀).mono h)) tendsto_const_nhds

中文:
定理 tendsto_atTop_of_eventually_const
  结论: {ι : 类型} [预序 ι]
  证明: Tendsto.congr' (EventuallyEq.symm ((eventually_ge_atTop i₀).mono h)) tendsto_const_nhds

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, Tendsto, Tendsto.congr, eventually_ge_atTop, tendsto_const_nhds
-/
theorem tendsto_atTop_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm ((eventually_ge_atTop i₀).mono h)) tendsto_const_nhds

/--
theorem `tendsto_atBot_of_eventually_const` / 定理 `tendsto_atBot_of_eventually_const`

English:
theorem tendsto_atBot_of_eventually_const
  statement: {ι : Type*} [Preorder ι]
  proof: tendsto_atTop_of_eventually_const (ι := ιᵒᵈ) h

中文:
定理 tendsto_atBot_of_eventually_const
  结论: {ι : 类型} [预序 ι]
  证明: tendsto_atTop_of_eventually_const (ι := ιᵒᵈ) h

Depends on / 依赖: tendsto_atTop_of_eventually_const
-/
theorem tendsto_atBot_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι -> X} {i₀ : ι} (h : forall i <= i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  tendsto_atTop_of_eventually_const (ι := ιᵒᵈ) h

/--
theorem `pure_le_nhds` / 定理 `pure_le_nhds`

English:
theorem pure_le_nhds
  statement: pure <= (𝓝 : X -> Filter X)
  proof: fun _ _ hs => mem_pure.2 mem_of_mem_nhds hs

中文:
定理 pure_le_nhds
  结论: pure <= (𝓝 : X -> 滤子 X)
  证明: fun _ _ hs => mem_pure.2 mem_of_mem_nhds hs

Depends on / 依赖: mem_of_mem_nhds, mem_pure
-/
theorem pure_le_nhds : pure <= (𝓝 : X -> Filter X) := fun _ _ hs => mem_pure.2 mem_of_mem_nhds hs

/--
theorem `tendsto_pure_nhds` / 定理 `tendsto_pure_nhds`

English:
theorem tendsto_pure_nhds
  given: (f : α -> X) (a : α)
  statement: Tendsto f (pure a) (𝓝 (f a))
  proof: (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

中文:
定理 tendsto_pure_nhds
  条件: (f : α -> X) (a : α)
  结论: 收敛 f (pure a) (𝓝 (f a))
  证明: (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

Depends on / 依赖: mono_right, pure_le_nhds, tendsto_pure_pure
-/
theorem tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

/--
theorem `OrderTop.tendsto_atTop_nhds` / 定理 `OrderTop.tendsto_atTop_nhds`

English:
theorem OrderTop.tendsto_atTop_nhds
  given: [PartialOrder α] [OrderTop α] (f : α -> X)
  proof: (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]

中文:
定理 有顶序.tendsto_atTop_nhds
  条件: [偏序 α] [有顶序 α] (f : α -> X)
  证明: (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]

Depends on / 依赖: mono_right, pure_le_nhds, tendsto_atTop_pure
-/
theorem OrderTop.tendsto_atTop_nhds [PartialOrder α] [OrderTop α] (f : α -> X) :
    Tendsto f atTop (𝓝 (f ⊤)) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]
/--
Instance `nhds_neBot` / 实例 `nhds_neBot`

English:
instance nhds_neBot
  signature: : NeBot (𝓝 x)
  body: neBot_of_le (pure_le_nhds x)

中文:
实例 nhds_neBot
  签名: : NeBot (𝓝 x)
  定义体: neBot_of_le (pure_le_nhds x)

Depends on / 依赖: neBot_of_le, pure_le_nhds
-/
instance nhds_neBot : NeBot (𝓝 x) :=
  neBot_of_le (pure_le_nhds x)

/--
theorem `tendsto_nhds_of_eventually_eq` / 定理 `tendsto_nhds_of_eventually_eq`

English:
theorem tendsto_nhds_of_eventually_eq
  given: {l : Filter α} {f : α -> X} (h : forallᶠ x' in l, f x' = x)
  proof: tendsto_const_nhds.congr' (.symm h)

中文:
定理 tendsto_nhds_of_eventually_eq
  条件: {l : 滤子 α} {f : α -> X} (h : 对任意ᶠ x' in l, f x' = x)
  证明: tendsto_const_nhds.congr' (.symm h)

Depends on / 依赖: tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem tendsto_nhds_of_eventually_eq {l : Filter α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) :
    Tendsto f l (𝓝 x) :=
  tendsto_const_nhds.congr' (.symm h)

/--
theorem `Filter.EventuallyEq.tendsto` / 定理 `Filter.EventuallyEq.tendsto`

English:
theorem Filter.EventuallyEq.tendsto
  given: {l : Filter α} {f : α -> X} (hf : f =ᶠ[l] fun _ => x)
  proof: tendsto_nhds_of_eventually_eq hf

中文:
定理 滤子.EventuallyEq.tendsto
  条件: {l : 滤子 α} {f : α -> X} (hf : f =ᶠ[l] fun _ => x)
  证明: tendsto_nhds_of_eventually_eq hf

Depends on / 依赖: tendsto_nhds_of_eventually_eq
-/
theorem Filter.EventuallyEq.tendsto {l : Filter α} {f : α -> X} (hf : f =ᶠ[l] fun _ => x) :
    Tendsto f l (𝓝 x) :=
  tendsto_nhds_of_eventually_eq hf


/--
theorem `interior_eq_nhds'` / 定理 `interior_eq_nhds'`

English:
theorem interior_eq_nhds'
  statement: interior s = { x | s in 𝓝 x }
  proof: Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_ofPred_eq]

中文:
定理 interior_eq_nhds'
  结论: interior s = { x | s in 𝓝 x }
  证明: Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_ofPred_eq]

Depends on / 依赖: Set.ext, mem_interior, mem_nhds_iff, mem_ofPred_eq
-/
theorem interior_eq_nhds' : interior s = { x | s in 𝓝 x } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_ofPred_eq]

/--
theorem `interior_eq_nhds` / 定理 `interior_eq_nhds`

English:
theorem interior_eq_nhds
  statement: interior s = { x | 𝓝 x <= 𝓟 s }
  proof: interior_eq_nhds'.trans by simp only [le_principal_iff]

@[simp]

中文:
定理 interior_eq_nhds
  结论: interior s = { x | 𝓝 x <= 𝓟 s }
  证明: interior_eq_nhds'.trans by simp only [le_principal_iff]

@[simp]

Depends on / 依赖: interior_eq_nhds, le_principal_iff
-/
theorem interior_eq_nhds : interior s = { x | 𝓝 x <= 𝓟 s } :=
interior_eq_nhds'.trans by simp only [le_principal_iff]

@[simp]
/--
theorem `interior_mem_nhds` / 定理 `interior_mem_nhds`

English:
theorem interior_mem_nhds
  statement: interior s in 𝓝 x ↔ s in 𝓝 x
  proof: ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩

中文:
定理 interior_mem_nhds
  结论: interior s in 𝓝 x ↔ s in 𝓝 x
  证明: ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds, mem_nhds, mem_of_superset
-/
theorem interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩

/--
theorem `interior_setOfPred_eq` / 定理 `interior_setOfPred_eq`

English:
theorem interior_setOfPred_eq
  given: {p : X -> Prop}
  statement: interior { x | p x } = { x | forallᶠ y in 𝓝 x, p y }
  proof: interior_eq_nhds'

@[deprecated (since := "2026-07-09")]
alias interior_setOf_eq := interior_setOfPred_eq

中文:
定理 interior_setOfPred_eq
  条件: {p : X -> 命题}
  结论: interior { x | p x } = { x | 对任意ᶠ y in 𝓝 x, p y }
  证明: interior_eq_nhds'

@[deprecated (since := "2026-07-09")]
alias interior_setOf_eq := interior_setOfPred_eq

Depends on / 依赖: interior_eq_nhds
-/
theorem interior_setOfPred_eq {p : X -> Prop} : interior { x | p x } = { x | forallᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'

@[deprecated (since := "2026-07-09")]
alias interior_setOf_eq := interior_setOfPred_eq

/--
theorem `isOpen_setOfPred_eventually_nhds` / 定理 `isOpen_setOfPred_eventually_nhds`

English:
theorem isOpen_setOfPred_eventually_nhds
  given: {p : X -> Prop}
  statement: IsOpen { x | forallᶠ y in 𝓝 x, p y }
  proof: by
  simp only [← interior_setOfPred_eq, isOpen_interior]

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhds := isOpen_setOfPred_eventually_nhds

中文:
定理 isOpen_setOfPred_eventually_nhds
  条件: {p : X -> 命题}
  结论: 是开集 { x | 对任意ᶠ y in 𝓝 x, p y }
  证明: by
  simp only [← interior_setOfPred_eq, isOpen_interior]

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhds := isOpen_setOfPred_eventually_nhds

Depends on / 依赖: interior_setOfPred_eq, isOpen_interior
-/
theorem isOpen_setOfPred_eventually_nhds {p : X -> Prop} : IsOpen { x | forallᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOfPred_eq, isOpen_interior]

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhds := isOpen_setOfPred_eventually_nhds

/--
theorem `subset_interior_iff_nhds` / 定理 `subset_interior_iff_nhds`

English:
theorem subset_interior_iff_nhds
  given: {V : Set X}
  statement: s subseteq interior V ↔ forall x in s, V in 𝓝 x
  proof: by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]

中文:
定理 subset_interior_iff_nhds
  条件: {V : 集合 X}
  结论: s subseteq interior V ↔ 对任意 x in s, V in 𝓝 x
  证明: by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]

Depends on / 依赖: mem_interior_iff_mem_nhds, simp_rw, subset_def
-/
theorem subset_interior_iff_nhds {V : Set X} : s subseteq interior V ↔ forall x in s, V in 𝓝 x := by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]

/--
theorem `isOpen_iff_nhds` / 定理 `isOpen_iff_nhds`

English:
theorem isOpen_iff_nhds
  statement: IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
  proof: calc
    IsOpen s ↔ s subseteq interior s := subset_interior_iff_isOpen.symm
    _ ↔ forall x in s, 𝓝 x <= 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_ofPred]

中文:
定理 isOpen_iff_nhds
  结论: 是开集 s ↔ 对任意 x in s, 𝓝 x <= 𝓟 s
  证明: calc
    IsOpen s ↔ s subseteq interior s := subset_interior_iff_isOpen.symm
    _ ↔ forall x in s, 𝓝 x <= 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_ofPred]

Depends on / 依赖: IsOpen, interior, interior_eq_nhds, mem_ofPred, simp_rw, subset_def, subset_interior_iff_isOpen, subset_interior_iff_isOpen.symm, subseteq
-/
theorem isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s :=
  calc
    IsOpen s ↔ s subseteq interior s := subset_interior_iff_isOpen.symm
    _ ↔ forall x in s, 𝓝 x <= 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_ofPred]

/--
theorem `TopologicalSpace.ext_iff_nhds` / 定理 `TopologicalSpace.ext_iff_nhds`

English:
theorem TopologicalSpace.ext_iff_nhds
  given: {X} {t t' : TopologicalSpace X}
  proof: ⟨fun H _ => congrFun (congrArg _ H) _, fun H => by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds

中文:
定理 拓扑空间.ext_iff_nhds
  条件: {X} {t t' : 拓扑空间 X}
  证明: ⟨fun H _ => congrFun (congrArg _ H) _, fun H => by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds

Depends on / 依赖: isOpen_iff_nhds, simp_rw
-/
theorem TopologicalSpace.ext_iff_nhds {X} {t t' : TopologicalSpace X} :
    t = t' ↔ forall x, @nhds _ t x = @nhds _ t' x :=
  ⟨fun H _ => congrFun (congrArg _ H) _, fun H => by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds

/--
theorem `isOpen_iff_mem_nhds` / 定理 `isOpen_iff_mem_nhds`

English:
theorem isOpen_iff_mem_nhds
  statement: IsOpen s ↔ forall x in s, s in 𝓝 x
  proof: isOpen_iff_nhds.trans forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

中文:
定理 isOpen_iff_mem_nhds
  结论: 是开集 s ↔ 对任意 x in s, s in 𝓝 x
  证明: isOpen_iff_nhds.trans forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

Depends on / 依赖: forall_congr, imp_congr_right, isOpen_iff_nhds, isOpen_iff_nhds.trans, le_principal_iff
-/
theorem isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s in 𝓝 x :=
isOpen_iff_nhds.trans forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

/--
theorem `isOpen_iff_eventually` / 定理 `isOpen_iff_eventually`

English:
theorem isOpen_iff_eventually
  statement: IsOpen s ↔ forall x, x in s -> forallᶠ y in 𝓝 x, y in s
  proof: isOpen_iff_mem_nhds

中文:
定理 isOpen_iff_eventually
  结论: 是开集 s ↔ 对任意 x, x in s -> 对任意ᶠ y in 𝓝 x, y in s
  证明: isOpen_iff_mem_nhds

Depends on / 依赖: isOpen_iff_mem_nhds
-/
theorem isOpen_iff_eventually : IsOpen s ↔ forall x, x in s -> forallᶠ y in 𝓝 x, y in s :=
  isOpen_iff_mem_nhds

/--
theorem `isOpen_singleton_iff_nhds_eq_pure` / 定理 `isOpen_singleton_iff_nhds_eq_pure`

English:
theorem isOpen_singleton_iff_nhds_eq_pure
  given: (x : X)
  statement: IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
  proof: by
  simp [← (pure_le_nhds _).ge_iff_eq', isOpen_iff_mem_nhds]

中文:
定理 isOpen_singleton_iff_nhds_eq_pure
  条件: (x : X)
  结论: 是开集 ({x} : 集合 X) ↔ 𝓝 x = pure x
  证明: by
  simp [← (pure_le_nhds _).ge_iff_eq', isOpen_iff_mem_nhds]

Depends on / 依赖: ge_iff_eq, isOpen_iff_mem_nhds, pure_le_nhds
-/
theorem isOpen_singleton_iff_nhds_eq_pure (x : X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x := by
  simp [← (pure_le_nhds _).ge_iff_eq', isOpen_iff_mem_nhds]

/--
theorem `isOpen_singleton_iff_punctured_nhds` / 定理 `isOpen_singleton_iff_punctured_nhds`

English:
theorem isOpen_singleton_iff_punctured_nhds
  given: (x : X)
  statement: IsOpen ({x} : Set X) ↔ 𝓝[!=] x = ⊥
  proof: by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [nhdsWithin]; rw [← mem_iff_inf_principal_compl]; rw [le_antisymm_iff]
  simp [pure_le_nhds x]

中文:
定理 isOpen_singleton_iff_punctured_nhds
  条件: (x : X)
  结论: 是开集 ({x} : 集合 X) ↔ 𝓝[!=] x = ⊥
  证明: by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [nhdsWithin]; rw [← mem_iff_inf_principal_compl]; rw [le_antisymm_iff]
  simp [pure_le_nhds x]

Depends on / 依赖: isOpen_singleton_iff_nhds_eq_pure, le_antisymm_iff, mem_iff_inf_principal_compl, nhdsWithin, pure_le_nhds
-/
theorem isOpen_singleton_iff_punctured_nhds (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[!=] x = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure]; rw [nhdsWithin]; rw [← mem_iff_inf_principal_compl]; rw [le_antisymm_iff]
  simp [pure_le_nhds x]

/--
theorem `mem_closure_iff_frequently` / 定理 `mem_closure_iff_frequently`

English:
theorem mem_closure_iff_frequently
  statement: x in closure s ↔ existsᶠ x in 𝓝 x, x in s
  proof: by
  rw [Filter.Frequently]; rw [Filter.Eventually]; rw [← mem_interior_iff_mem_nhds]; rw [closure_eq_compl_interior_compl]; rw [mem_compl_iff]; rw [compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

中文:
定理 mem_closure_iff_frequently
  结论: x in closure s ↔ 存在ᶠ x in 𝓝 x, x in s
  证明: by
  rw [Filter.Frequently]; rw [Filter.Eventually]; rw [← mem_interior_iff_mem_nhds]; rw [closure_eq_compl_interior_compl]; rw [mem_compl_iff]; rw [compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Filter.Frequently, Frequently, closure_eq_compl_interior_compl, compl_def, mem_compl_iff, mem_interior_iff_mem_nhds
-/
theorem mem_closure_iff_frequently : x in closure s ↔ existsᶠ x in 𝓝 x, x in s := by
  rw [Filter.Frequently]; rw [Filter.Eventually]; rw [← mem_interior_iff_mem_nhds]; rw [closure_eq_compl_interior_compl]; rw [mem_compl_iff]; rw [compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

/--
theorem `isClosed_iff_frequently` / 定理 `isClosed_iff_frequently`

English:
theorem isClosed_iff_frequently
  statement: IsClosed s ↔ forall x, (existsᶠ y in 𝓝 x, y in s) -> x in s
  proof: by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]

中文:
定理 isClosed_iff_frequently
  结论: 是闭集 s ↔ 对任意 x, (存在ᶠ y in 𝓝 x, y in s) -> x in s
  证明: by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]

Depends on / 依赖: closure_subset_iff_isClosed, forall_congr, mem_closure_iff_frequently
-/
theorem isClosed_iff_frequently : IsClosed s ↔ forall x, (existsᶠ y in 𝓝 x, y in s) -> x in s := by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]

/--
lemma `nhdsWithin_neBot` / 引理 `nhdsWithin_neBot`

English:
lemma nhdsWithin_neBot
  statement: (𝓝[s] x).NeBot ↔ forall ⦃t⦄, t in 𝓝 x -> (t inter s).Nonempty
  proof: by
  rw [nhdsWithin]; rw [inf_neBot_iff]
  exact forall₂_congr fun U _ =>
⟨fun h => h (mem_principal_self _), fun h u hsu => h.mono inter_subset_inter_right _ hsu⟩

@[gcongr]

中文:
引理 nhdsWithin_neBot
  结论: (𝓝[s] x).NeBot ↔ 对任意 ⦃t⦄, t in 𝓝 x -> (t inter s).非空
  证明: by
  rw [nhdsWithin]; rw [inf_neBot_iff]
  exact forall₂_congr fun U _ =>
⟨fun h => h (mem_principal_self _), fun h u hsu => h.mono inter_subset_inter_right _ hsu⟩

@[gcongr]

Depends on / 依赖: h.mono, inf_neBot_iff, inter_subset_inter_right, mem_principal_self, nhdsWithin
-/
lemma nhdsWithin_neBot : (𝓝[s] x).NeBot ↔ forall ⦃t⦄, t in 𝓝 x -> (t inter s).Nonempty := by
  rw [nhdsWithin]; rw [inf_neBot_iff]
  exact forall₂_congr fun U _ =>
⟨fun h => h (mem_principal_self _), fun h u hsu => h.mono inter_subset_inter_right _ hsu⟩

@[gcongr]
/--
theorem `nhdsWithin_mono` / 定理 `nhdsWithin_mono`

English:
theorem nhdsWithin_mono
  given: (x : X) {s t : Set X} (h : s subseteq t)
  statement: 𝓝[s] x <= 𝓝[t] x
  proof: inf_le_inf_left _ (principal_mono.mpr h)

中文:
定理 nhdsWithin_mono
  条件: (x : X) {s t : 集合 X} (h : s subseteq t)
  结论: 𝓝[s] x <= 𝓝[t] x
  证明: inf_le_inf_left _ (principal_mono.mpr h)

Depends on / 依赖: inf_le_inf_left, principal_mono, principal_mono.mpr
-/
theorem nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t) : 𝓝[s] x <= 𝓝[t] x :=
  inf_le_inf_left _ (principal_mono.mpr h)

/--
theorem `IsClosed.interior_union_left` / 定理 `IsClosed.interior_union_left`

English:
theorem IsClosed.interior_union_left
  given: (_ : IsClosed s)
  proof: fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a in s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u inter sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩

中文:
定理 是闭集.interior_union_left
  条件: (_ : 是闭集 s)
  证明: fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a in s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u inter sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩
-/
theorem IsClosed.interior_union_left (_ : IsClosed s) :
    interior (s union t) subseteq s union interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a in s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u inter sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩

/--
theorem `IsClosed.interior_union_right` / 定理 `IsClosed.interior_union_right`

English:
theorem IsClosed.interior_union_right
  given: (h : IsClosed t)
  proof: by
  simpa only [union_comm _ t] using h.interior_union_left

中文:
定理 是闭集.interior_union_right
  条件: (h : 是闭集 t)
  证明: by
  simpa only [union_comm _ t] using h.interior_union_left

Depends on / 依赖: h.interior_union_left, interior_union_left, union_comm
-/
theorem IsClosed.interior_union_right (h : IsClosed t) :
    interior (s union t) subseteq interior s union t := by
  simpa only [union_comm _ t] using h.interior_union_left

/--
theorem `IsOpen.inter_closure` / 定理 `IsOpen.inter_closure`

English:
theorem IsOpen.inter_closure
  given: (h : IsOpen s)
  statement: s inter closure t subseteq closure (s inter t)
  proof: compl_subset_compl.mp by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl

中文:
定理 是开集.inter_closure
  条件: (h : 是开集 s)
  结论: s inter closure t subseteq closure (s inter t)
  证明: compl_subset_compl.mp by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl

Depends on / 依赖: IsClosed, IsClosed.interior_union_left, compl_inter, compl_subset_compl, compl_subset_compl.mp, h.isClosed_compl, interior_compl, interior_union_left, isClosed_compl
-/
theorem IsOpen.inter_closure (h : IsOpen s) : s inter closure t subseteq closure (s inter t) :=
compl_subset_compl.mp by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl

/--
theorem `IsOpen.closure_inter` / 定理 `IsOpen.closure_inter`

English:
theorem IsOpen.closure_inter
  given: (h : IsOpen t)
  statement: closure s inter t subseteq closure (s inter t)
  proof: by
  simpa only [inter_comm t] using h.inter_closure

中文:
定理 是开集.closure_inter
  条件: (h : 是开集 t)
  结论: closure s inter t subseteq closure (s inter t)
  证明: by
  simpa only [inter_comm t] using h.inter_closure

Depends on / 依赖: h.inter_closure, inter_closure, inter_comm
-/
theorem IsOpen.closure_inter (h : IsOpen t) : closure s inter t subseteq closure (s inter t) := by
  simpa only [inter_comm t] using h.inter_closure

/--
theorem `Dense.open_subset_closure_inter` / 定理 `Dense.open_subset_closure_inter`

English:
theorem Dense.open_subset_closure_inter
  given: (hs : Dense s) (ht : IsOpen t)
  proof: calc
    t = t inter closure s := by rw [hs.closure_eq, inter_univ]
    _ subseteq closure (t inter s) := ht.inter_closure

中文:
定理 稠密.open_subset_closure_inter
  条件: (hs : 稠密 s) (ht : 是开集 t)
  证明: calc
    t = t inter closure s := by rw [hs.closure_eq, inter_univ]
    _ subseteq closure (t inter s) := ht.inter_closure

Depends on / 依赖: closure, closure_eq, hs.closure_eq, ht.inter_closure, inter_closure, inter_univ, subseteq
-/
theorem Dense.open_subset_closure_inter (hs : Dense s) (ht : IsOpen t) :
    t subseteq closure (t inter s) :=
  calc
    t = t inter closure s := by rw [hs.closure_eq, inter_univ]
    _ subseteq closure (t inter s) := ht.inter_closure

/--
theorem `Dense.inter_of_isOpen_left` / 定理 `Dense.inter_of_isOpen_left`

English:
theorem Dense.inter_of_isOpen_left
  given: (hs : Dense s) (ht : Dense t) (hso : IsOpen s)
  proof: fun x =>
closure_minimal hso.inter_closure isClosed_closure by simp [hs.closure_eq, ht.closure_eq]

中文:
定理 稠密.inter_of_isOpen_left
  条件: (hs : 稠密 s) (ht : 稠密 t) (hso : 是开集 s)
  证明: fun x =>
closure_minimal hso.inter_closure isClosed_closure by simp [hs.closure_eq, ht.closure_eq]
-/
theorem Dense.inter_of_isOpen_left (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s inter t) := fun x =>
closure_minimal hso.inter_closure isClosed_closure by simp [hs.closure_eq, ht.closure_eq]

/--
theorem `Dense.inter_of_isOpen_right` / 定理 `Dense.inter_of_isOpen_right`

English:
theorem Dense.inter_of_isOpen_right
  given: (hs : Dense s) (ht : Dense t) (hto : IsOpen t)
  proof: inter_comm t s ▸ ht.inter_of_isOpen_left hs hto

中文:
定理 稠密.inter_of_isOpen_right
  条件: (hs : 稠密 s) (ht : 稠密 t) (hto : 是开集 t)
  证明: inter_comm t s ▸ ht.inter_of_isOpen_left hs hto

Depends on / 依赖: ht.inter_of_isOpen_left, inter_comm, inter_of_isOpen_left
-/
theorem Dense.inter_of_isOpen_right (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s inter t) :=
  inter_comm t s ▸ ht.inter_of_isOpen_left hs hto

/--
theorem `Dense.inter_nhds_nonempty` / 定理 `Dense.inter_nhds_nonempty`

English:
theorem Dense.inter_nhds_nonempty
  given: (hs : Dense s) (ht : t in 𝓝 x)
  proof: let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩

中文:
定理 稠密.inter_nhds_nonempty
  条件: (hs : 稠密 s) (ht : t in 𝓝 x)
  证明: let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩

Depends on / 依赖: hs.inter_open_nonempty, inter_open_nonempty, mem_nhds_iff
-/
theorem Dense.inter_nhds_nonempty (hs : Dense s) (ht : t in 𝓝 x) :
    (s inter t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩

/--
theorem `closure_sdiff` / 定理 `closure_sdiff`

English:
theorem closure_sdiff
  statement: closure s \ closure t subseteq closure (s \ t)
  proof: calc
    closure s \ closure t = (closure t)ᶜ inter closure s := by simp only [sdiff_eq, inter_comm]
    _ subseteq closure ((closure t)ᶜ inter s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [sdiff_eq, inter_comm]
_ subseteq closure (s 

中文:
定理 closure_sdiff
  结论: closure s \ closure t subseteq closure (s \ t)
  证明: calc
    closure s \ closure t = (closure t)ᶜ inter closure s := by simp only [sdiff_eq, inter_comm]
    _ subseteq closure ((closure t)ᶜ inter s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [sdiff_eq, inter_comm]
_ subseteq closure (s 

Depends on / 依赖: Subset, Subset.refl, closure, closure_mono, inter_closure, inter_comm, isClosed_closure, isOpen_compl_iff, isOpen_compl_iff.mpr, sdiff_eq, sdiff_subset_sdiff, subset_closure, subseteq
-/
theorem closure_sdiff : closure s \ closure t subseteq closure (s \ t) :=
  calc
    closure s \ closure t = (closure t)ᶜ inter closure s := by simp only [sdiff_eq, inter_comm]
    _ subseteq closure ((closure t)ᶜ inter s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [sdiff_eq, inter_comm]
_ subseteq closure (s \ t) := closure_mono sdiff_subset_sdiff (Subset.refl s) subset_closure

@[deprecated (since := "2026-06-03")] alias closure_diff := closure_sdiff

/--
theorem `Filter.Frequently.mem_of_closed` / 定理 `Filter.Frequently.mem_of_closed`

English:
theorem Filter.Frequently.mem_of_closed
  statement: (h : existsᶠ x in 𝓝 x, x in s)
  proof: hs.closure_subset h.mem_closure

中文:
定理 滤子.Frequently.mem_of_closed
  结论: (h : 存在ᶠ x in 𝓝 x, x in s)
  证明: hs.closure_subset h.mem_closure

Depends on / 依赖: closure_subset, h.mem_closure, hs.closure_subset, mem_closure
-/
theorem Filter.Frequently.mem_of_closed (h : existsᶠ x in 𝓝 x, x in s)
    (hs : IsClosed s) : x in s :=
  hs.closure_subset h.mem_closure

/--
theorem `IsClosed.mem_of_frequently_of_tendsto` / 定理 `IsClosed.mem_of_frequently_of_tendsto`

English:
theorem IsClosed.mem_of_frequently_of_tendsto
  statement: {f : α -> X} {b : Filter α}
  proof: (hf.frequently <| show existsᶠ x in b, (fun y => y in s) (f x) from h).mem_of_closed hs

中文:
定理 是闭集.mem_of_frequently_of_tendsto
  结论: {f : α -> X} {b : 滤子 α}
  证明: (hf.frequently <| show existsᶠ x in b, (fun y => y in s) (f x) from h).mem_of_closed hs

Depends on / 依赖: frequently, hf.frequently, mem_of_closed
-/
theorem IsClosed.mem_of_frequently_of_tendsto {f : α -> X} {b : Filter α}
    (hs : IsClosed s) (h : existsᶠ x in b, f x in s) (hf : Tendsto f b (𝓝 x)) : x in s :=
  (hf.frequently <| show existsᶠ x in b, (fun y => y in s) (f x) from h).mem_of_closed hs

/--
theorem `IsClosed.mem_of_tendsto` / 定理 `IsClosed.mem_of_tendsto`

English:
theorem IsClosed.mem_of_tendsto
  statement: {f : α -> X} {b : Filter α} [NeBot b]
  proof: hs.mem_of_frequently_of_tendsto h.frequently hf

中文:
定理 是闭集.mem_of_tendsto
  结论: {f : α -> X} {b : 滤子 α} [NeBot b]
  证明: hs.mem_of_frequently_of_tendsto h.frequently hf

Depends on / 依赖: frequently, h.frequently, hs.mem_of_frequently_of_tendsto, mem_of_frequently_of_tendsto
-/
theorem IsClosed.mem_of_tendsto {f : α -> X} {b : Filter α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in s :=
  hs.mem_of_frequently_of_tendsto h.frequently hf

/--
theorem `mem_closure_of_frequently_of_tendsto` / 定理 `mem_closure_of_frequently_of_tendsto`

English:
theorem mem_closure_of_frequently_of_tendsto
  statement: {f : α -> X} {b : Filter α}
  proof: (hf.frequently h).mem_closure

中文:
定理 mem_closure_of_frequently_of_tendsto
  结论: {f : α -> X} {b : 滤子 α}
  证明: (hf.frequently h).mem_closure

Depends on / 依赖: frequently, hf.frequently, mem_closure
-/
theorem mem_closure_of_frequently_of_tendsto {f : α -> X} {b : Filter α}
    (h : existsᶠ x in b, f x in s) (hf : Tendsto f b (𝓝 x)) : x in closure s :=
  (hf.frequently h).mem_closure

/--
theorem `mem_closure_of_tendsto` / 定理 `mem_closure_of_tendsto`

English:
theorem mem_closure_of_tendsto
  statement: {f : α -> X} {b : Filter α} [NeBot b]
  proof: mem_closure_of_frequently_of_tendsto h.frequently hf

中文:
定理 mem_closure_of_tendsto
  结论: {f : α -> X} {b : 滤子 α} [NeBot b]
  证明: mem_closure_of_frequently_of_tendsto h.frequently hf

Depends on / 依赖: frequently, h.frequently, mem_closure_of_frequently_of_tendsto
-/
theorem mem_closure_of_tendsto {f : α -> X} {b : Filter α} [NeBot b]
    (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in closure s :=
  mem_closure_of_frequently_of_tendsto h.frequently hf

/--
theorem `tendsto_inf_principal_nhds_iff_of_forall_eq` / 定理 `tendsto_inf_principal_nhds_iff_of_forall_eq`

English:
theorem tendsto_inf_principal_nhds_iff_of_forall_eq
  statement: {f : α -> X} {l : Filter α} {s : Set α}
  proof: by
  rw [tendsto_iff_comap]; rw [tendsto_iff_comap]
  replace h : 𝓟 sᶜ <= comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x in t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right]; rw [sup_

中文:
定理 tendsto_inf_principal_nhds_iff_of_对任意_eq
  结论: {f : α -> X} {l : 滤子 α} {s : 集合 α}
  证明: by
  rw [tendsto_iff_comap]; rw [tendsto_iff_comap]
  replace h : 𝓟 sᶜ <= comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x in t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right]; rw [sup_

Depends on / 依赖: inf_le_left, inf_top_eq, le_trans, mem_of_mem_nhds, principal_univ, replace, sup_inf_right, sup_le, sup_le_iff, sup_principal, tendsto_iff_comap, union_compl_self
-/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : α -> X} {l : Filter α} {s : Set α}
    (h : forall a ∉ s, f a = x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) ↔ Tendsto f l (𝓝 x) := by
  rw [tendsto_iff_comap]; rw [tendsto_iff_comap]
  replace h : 𝓟 sᶜ <= comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x in t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right]; rw [sup_principal]; rw [union_compl_self]; rw [principal_univ]; rw [inf_top_eq]; rw [sup_le_iff]
    at this
  exact this.1
