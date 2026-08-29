/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular, normal, T₃, T₄ and T₅ spaces

This file continues the study of separation properties of topological spaces, focusing
on conditions strictly stronger than T₂.

## Main definitions

* `RegularSpace`: A regular space is one where, given any closed `C` and `x ∉ C`,
  there are disjoint open sets containing `x` and `C` respectively. Such a space is not necessarily
  Hausdorff.
* `T3Space`: A T₃ space is a regular T₀ space. T₃ implies T₂.₅.
* `NormalSpace`: A normal space, is one where given two disjoint closed sets,
  we can find two open sets that separate them. Such a space is not necessarily Hausdorff, even if
  it is T₀.
* `T4Space`: A T₄ space is a normal T₁ space. T₄ implies T₃.
* `CompletelyNormalSpace`: A completely normal space is one in which for any two sets `s`, `t`
  such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
  then there exist disjoint neighbourhoods of `s` and `t`. `Embedding.completelyNormalSpace` allows
  us to conclude that this is equivalent to all subspaces being normal. Such a space is not
  necessarily Hausdorff or regular, even if it is T₀.
* `T5Space`: A T₅ space is a completely normal T₁ space. T₅ implies T₄.

See `Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### Regular spaces

If the space is also Lindelöf:

* `NormalSpace.of_regularSpace_lindelofSpace`: every regular Lindelöf space is normal.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* <https://en.wikipedia.org/wiki/Normal_space>
* [Willard's *General Topology*][zbMATH02107988]

-/

public section

assert_not_exists UniformSpace

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section RegularSpace

/-- A topological space is called a *regular space* if for any closed set `s` and `a ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in terms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`. -/
@[mk_iff]
/--
Definition of `RegularSpace` / `RegularSpace` 的定义

English:
class RegularSpace
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - regular : forall {s : Set X} {a}, IsClosed s -> a ∉ s -> Disjoint (𝓝ˢ s) (𝓝 a)

中文:
类 RegularSpace
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - regular : 对任意 {s : Set X} {a}, IsClosed s -> a ∉ s -> Disjoint (𝓝ˢ s) (𝓝 a)
-/
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods. -/
  regular : forall {s : Set X} {a}, IsClosed s -> a ∉ s -> Disjoint (𝓝ˢ s) (𝓝 a)

/--
theorem `regularSpace_TFAE` / 定理 `regularSpace_TFAE`

English:
theorem regularSpace_TFAE
  given: (X : Type u) [TopologicalSpace X]
  proof: by
  tfae_have 1 ↔ 5 := by
    rw [regularSpace_iff]; rw [(@compl_surjective (Set X) _).forall]; rw [forall_comm]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ in _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_

中文:
定理 regularSpace_TFAE
  条件: (X : 类型u) [TopologicalSpace X]
  证明: by
  tfae_have 1 ↔ 5 := by
    rw [regularSpace_iff]; rw [(@compl_surjective (Set X) _).forall]; rw [forall_comm]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ in _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_

Depends on / 依赖: Classical, Classical.not_not, _closure, _closure.le_basis_iff, and_comm, and_imp, antisymm, compl_subset_compl, compl_surjective, disjoint_iff_right, forall_comm, interior_compl, isClosed_compl_iff, le_basis_iff, le_lift, mem_compl_iff, nhds_basis_opens, not_not, regularSpace_iff, subset_interior_iff_mem_nhdsSet
-/
theorem regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [RegularSpace X,
      forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ s) (𝓝 x),
      forall (x : X) (s : Set X), Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s,
      forall (x : X) (s : Set X), s in 𝓝 x -> exists t in 𝓝 x, IsClosed t ∧ t subseteq s,
      forall x : X, (𝓝 x).lift' closure <= 𝓝 x,
      forall x : X, (𝓝 x).lift' closure = 𝓝 x] := by
  tfae_have 1 ↔ 5 := by
    rw [regularSpace_iff]; rw [(@compl_surjective (Set X) _).forall]; rw [forall_comm]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ in _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_basis_opens _).disjoint_iff_right, ← subset_interior_iff_mem_nhdsSet,
      interior_compl, compl_subset_compl]
  tfae_have 5 -> 6 := fun h a => (h a).antisymm (𝓝 _).le_lift'_closure
  tfae_have 6 -> 4
  | H, a, s, hs => by
    rw [← H] at hs
    rcases (𝓝 a).basis_sets.lift'_closure.mem_iff.mp hs with ⟨U, hU, hUs⟩
    exact ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, hUs⟩
  tfae_have 4 -> 2
  | H, s, a, ha => by
    have ha' : sᶜ in 𝓝 a := by rwa [← mem_interior_iff_mem_nhds, interior_compl]
    rcases H _ _ ha' with ⟨U, hU, hUc, hUs⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ hU
    rwa [← subset_interior_iff_mem_nhdsSet, hUc.isOpen_compl.interior_eq, subset_compl_comm]
  tfae_have 2 -> 3 := by
    refine fun H a s => ⟨fun hd has => mem_closure_iff_nhds_ne_bot.mp has ?_, H s a⟩
    exact (hd.symm.mono_right <| @principal_le_nhdsSet _ _ s).eq_bot
tfae_have 3 -> 1 := fun H => ⟨fun hs ha => (H _ _).mpr hs.closure_eq.symm ▸ ha⟩
  tfae_finish

/--
theorem `RegularSpace.of_lift'_closure_le` / 定理 `RegularSpace.of_lift'_closure_le`

English:
theorem RegularSpace.of_lift'_closure_le
  given: (h : forall x : X, (𝓝 x).lift' closure <= 𝓝 x)
  proof: Iff.mpr ((regularSpace_TFAE X).out 0 4) h

中文:
定理 RegularSpace.of_lift'_closure_le
  条件: (h : 对任意 x : X, (𝓝 x).lift' closure <= 𝓝 x)
  证明: Iff.mpr ((regularSpace_TFAE X).out 0 4) h

Depends on / 依赖: Iff.mpr, regularSpace_TFAE
-/
theorem RegularSpace.of_lift'_closure_le (h : forall x : X, (𝓝 x).lift' closure <= 𝓝 x) :
    RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 4) h

/--
theorem `RegularSpace.of_lift'_closure` / 定理 `RegularSpace.of_lift'_closure`

English:
theorem RegularSpace.of_lift'_closure
  given: (h : forall x : X, (𝓝 x).lift' closure = 𝓝 x)
  statement: RegularSpace X
  proof: Iff.mpr ((regularSpace_TFAE X).out 0 5) h

中文:
定理 RegularSpace.of_lift'_closure
  条件: (h : 对任意 x : X, (𝓝 x).lift' closure = 𝓝 x)
  结论: RegularSpace X
  证明: Iff.mpr ((regularSpace_TFAE X).out 0 5) h
-/
theorem RegularSpace.of_lift'_closure (h : forall x : X, (𝓝 x).lift' closure = 𝓝 x) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 5) h

/--
theorem `RegularSpace.of_hasBasis` / 定理 `RegularSpace.of_hasBasis`

English:
theorem RegularSpace.of_hasBasis
  statement: {ι : X -> Sort*} {p : forall a, ι a -> Prop} {s : forall a, ι a -> Set X}
  proof: .of_lift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)

中文:
定理 RegularSpace.of_hasBasis
  结论: {ι : X -> Sort*} {p : 对任意 a, ι a -> 命题} {s : 对任意 a, ι a -> Set X}
  证明: .of_lift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)

Depends on / 依赖: _closure, _closure_eq_self, of_lift
-/
theorem RegularSpace.of_hasBasis {ι : X -> Sort*} {p : forall a, ι a -> Prop} {s : forall a, ι a -> Set X}
    (h₁ : forall a, (𝓝 a).HasBasis (p a) (s a)) (h₂ : forall a i, p a i -> IsClosed (s a i)) :
    RegularSpace X :=
  .of_lift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)

/--
theorem `RegularSpace.of_exists_mem_nhds_isClosed_subset` / 定理 `RegularSpace.of_exists_mem_nhds_isClosed_subset`

English:
theorem RegularSpace.of_exists_mem_nhds_isClosed_subset
  proof: Iff.mpr ((regularSpace_TFAE X).out 0 3) h

中文:
定理 RegularSpace.of_exists_mem_nhds_isClosed_subset
  证明: Iff.mpr ((regularSpace_TFAE X).out 0 3) h

Depends on / 依赖: Iff.mpr, regularSpace_TFAE
-/
theorem RegularSpace.of_exists_mem_nhds_isClosed_subset
    (h : forall (x : X), forall s in 𝓝 x, exists t in 𝓝 x, IsClosed t ∧ t subseteq s) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 3) h

/-- A weakly locally compact R₁ space is regular. -/
instance (priority := 100) [WeaklyLocallyCompactSpace X] [R1Space X] : RegularSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, _, h⟩ => h

/--
theorem `regularSpace_generateFrom` / 定理 `regularSpace_generateFrom`

English:
theorem regularSpace_generateFrom
  given: {s : Set (Set X)} (h : ‹_› = generateFrom s)
  proof: by
  refine ⟨fun _ t ht a ha => RegularSpace.regular
    (h ▸ isOpen_generateFrom_of_mem ht).isClosed_compl
    (Set.notMem_compl_iff.mpr ha), fun h' => ⟨fun {t a} ht ha => ?_⟩⟩
  obtain ⟨t, rfl⟩ := compl_involutive.surjective t
  rw [isClosed_compl_iff]; rw [h] at ht
  rw [Set.notMem_compl_iff] at 

中文:
定理 regularSpace_generateFrom
  条件: {s : Set (Set X)} (h : ‹_› = generateFrom s)
  证明: by
  refine ⟨fun _ t ht a ha => RegularSpace.regular
    (h ▸ isOpen_generateFrom_of_mem ht).isClosed_compl
    (Set.notMem_compl_iff.mpr ha), fun h' => ⟨fun {t a} ht ha => ?_⟩⟩
  obtain ⟨t, rfl⟩ := compl_involutive.surjective t
  rw [isClosed_compl_iff]; rw [h] at ht
  rw [Set.notMem_compl_iff] at 

Depends on / 依赖: RegularSpace, RegularSpace.regular, Set.notMem_compl_iff, Set.notMem_compl_iff.mpr, compl_inter, compl_involutive, compl_involutive.surjective, compl_sUnion, disjoint_sup_left, isClosed_compl, isClosed_compl_iff, isOpen_generateFrom_of_mem, nhdsSet_union, notMem_compl_iff, regular, sUnion, surjective
-/
theorem regularSpace_generateFrom {s : Set (Set X)} (h : ‹_› = generateFrom s) :
    RegularSpace X ↔ forall t in s, forall a in t, Disjoint (𝓝ˢ tᶜ) (𝓝 a) := by
  refine ⟨fun _ t ht a ha => RegularSpace.regular
    (h ▸ isOpen_generateFrom_of_mem ht).isClosed_compl
    (Set.notMem_compl_iff.mpr ha), fun h' => ⟨fun {t a} ht ha => ?_⟩⟩
  obtain ⟨t, rfl⟩ := compl_involutive.surjective t
  rw [isClosed_compl_iff]; rw [h] at ht
  rw [Set.notMem_compl_iff] at ha
  induction ht with
  | basic t ht => exact h' t ht a ha
  | univ => simp
  | inter t₁ t₂ _ _ ih₁ ih₂ => grind [compl_inter, nhdsSet_union, disjoint_sup_left]
  | sUnion S _ ih =>
    obtain ⟨t, ht, ha⟩ := ha
    grw [compl_sUnion, sInter_image, iInter₂_subset t ht]
    exact ih t ht ha

section
variable [RegularSpace X] {x : X} {s : Set X}

/--
theorem `disjoint_nhdsSet_nhds` / 定理 `disjoint_nhdsSet_nhds`

English:
theorem disjoint_nhdsSet_nhds
  statement: Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s
  proof: by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _

中文:
定理 disjoint_nhdsSet_nhds
  结论: Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s
  证明: by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _

Depends on / 依赖: h.mp, regularSpace_TFAE
-/
theorem disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s := by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _

/--
theorem `disjoint_nhds_nhdsSet` / 定理 `disjoint_nhds_nhdsSet`

English:
theorem disjoint_nhds_nhdsSet
  statement: Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s
  proof: disjoint_comm.trans disjoint_nhdsSet_nhds

中文:
定理 disjoint_nhds_nhdsSet
  结论: Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s
  证明: disjoint_comm.trans disjoint_nhdsSet_nhds

Depends on / 依赖: disjoint_comm, disjoint_comm.trans, disjoint_nhdsSet_nhds
-/
theorem disjoint_nhds_nhdsSet : Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s :=
  disjoint_comm.trans disjoint_nhdsSet_nhds

/-- A regular space is R₁. -/
instance (priority := 100) : R1Space X where
  specializes_or_disjoint_nhds _ _ := or_iff_not_imp_left.2 fun h => by
    rwa [← nhdsSet_singleton, disjoint_nhdsSet_nhds, ← specializes_iff_mem_closure]

/--
theorem `exists_mem_nhds_isClosed_subset` / 定理 `exists_mem_nhds_isClosed_subset`

English:
theorem exists_mem_nhds_isClosed_subset
  given: {x : X} {s : Set X} (h : s in 𝓝 x)
  proof: by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h

中文:
定理 exists_mem_nhds_isClosed_subset
  条件: {x : X} {s : Set X} (h : s in 𝓝 x)
  证明: by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h

Depends on / 依赖: regularSpace_TFAE
-/
theorem exists_mem_nhds_isClosed_subset {x : X} {s : Set X} (h : s in 𝓝 x) :
    exists t in 𝓝 x, IsClosed t ∧ t subseteq s := by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h

/--
theorem `closed_nhds_basis` / 定理 `closed_nhds_basis`

English:
theorem closed_nhds_basis
  given: (x : X)
  statement: (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsClosed s) id
  proof: hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset

中文:
定理 closed_nhds_basis
  条件: (x : X)
  结论: (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsClosed s) id
  证明: hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset

Depends on / 依赖: exists_mem_nhds_isClosed_subset, hasBasis_self
-/
theorem closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ IsClosed s) id :=
  hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset

/--
theorem `lift'_nhds_closure` / 定理 `lift'_nhds_closure`

English:
theorem lift'_nhds_closure
  given: (x : X)
  statement: (𝓝 x).lift' closure = 𝓝 x
  proof: (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right

中文:
定理 lift'_nhds_closure
  条件: (x : X)
  结论: (𝓝 x).lift' closure = 𝓝 x
  证明: (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right
-/
theorem lift'_nhds_closure (x : X) : (𝓝 x).lift' closure = 𝓝 x :=
  (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right

/--
theorem `Filter.HasBasis.nhds_closure` / 定理 `Filter.HasBasis.nhds_closure`

English:
theorem Filter.HasBasis.nhds_closure
  statement: {ι : Sort*} {x : X} {p : ι -> Prop} {s : ι -> Set X}
  proof: lift'_nhds_closure x ▸ h.lift'_closure

中文:
定理 Filter.HasBasis.nhds_closure
  结论: {ι : Sort*} {x : X} {p : ι -> 命题} {s : ι -> Set X}
  证明: lift'_nhds_closure x ▸ h.lift'_closure

Depends on / 依赖: _closure, _nhds_closure, h.lift
-/
theorem Filter.HasBasis.nhds_closure {ι : Sort*} {x : X} {p : ι -> Prop} {s : ι -> Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p fun i => closure (s i) :=
  lift'_nhds_closure x ▸ h.lift'_closure

/--
theorem `hasBasis_nhds_closure` / 定理 `hasBasis_nhds_closure`

English:
theorem hasBasis_nhds_closure
  given: (x : X)
  statement: (𝓝 x).HasBasis (fun s => s in 𝓝 x) closure
  proof: (𝓝 x).basis_sets.nhds_closure

中文:
定理 hasBasis_nhds_closure
  条件: (x : X)
  结论: (𝓝 x).HasBasis (fun s => s in 𝓝 x) closure
  证明: (𝓝 x).basis_sets.nhds_closure

Depends on / 依赖: basis_sets, basis_sets.nhds_closure, nhds_closure
-/
theorem hasBasis_nhds_closure (x : X) : (𝓝 x).HasBasis (fun s => s in 𝓝 x) closure :=
  (𝓝 x).basis_sets.nhds_closure

/--
theorem `hasBasis_opens_closure` / 定理 `hasBasis_opens_closure`

English:
theorem hasBasis_opens_closure
  given: (x : X)
  statement: (𝓝 x).HasBasis (fun s => x in s ∧ IsOpen s) closure
  proof: (nhds_basis_opens x).nhds_closure

中文:
定理 hasBasis_opens_closure
  条件: (x : X)
  结论: (𝓝 x).HasBasis (fun s => x in s ∧ IsOpen s) closure
  证明: (nhds_basis_opens x).nhds_closure

Depends on / 依赖: nhds_basis_opens, nhds_closure
-/
theorem hasBasis_opens_closure (x : X) : (𝓝 x).HasBasis (fun s => x in s ∧ IsOpen s) closure :=
  (nhds_basis_opens x).nhds_closure

/--
theorem `IsCompact.exists_isOpen_closure_subset` / 定理 `IsCompact.exists_isOpen_closure_subset`

English:
theorem IsCompact.exists_isOpen_closure_subset
  given: {K U : Set X} (hK : IsCompact K) (hU : U in 𝓝ˢ K)
  proof: by
  have hd : Disjoint (𝓝ˢ K) (𝓝ˢ Uᶜ) := by
    simpa [hK.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
      ← subset_interior_iff_mem_nhdsSet] using! hU
  rcases ((hasBasis_nhdsSet _).disjoint_iff (hasBasis_nhdsSet _)).1 hd
    with ⟨V, ⟨hVo, hKV⟩, W, ⟨hW, hUW⟩, hVW⟩
  refine ⟨V, hVo, hKV, Subset

中文:
定理 IsCompact.exists_isOpen_closure_subset
  条件: {K U : Set X} (hK : IsCompact K) (hU : U in 𝓝ˢ K)
  证明: by
  have hd : Disjoint (𝓝ˢ K) (𝓝ˢ Uᶜ) := by
    simpa [hK.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
      ← subset_interior_iff_mem_nhdsSet] using! hU
  rcases ((hasBasis_nhdsSet _).disjoint_iff (hasBasis_nhdsSet _)).1 hd
    with ⟨V, ⟨hVo, hKV⟩, W, ⟨hW, hUW⟩, hVW⟩
  refine ⟨V, hVo, hKV, Subset

Depends on / 依赖: Disjoint, Subset, Subset.trans, closure_minimal, compl_subset_comm, disjoint_iff, disjoint_nhdsSet_left, disjoint_nhds_nhdsSet, hK.disjoint_nhdsSet_left, hVW.subset_compl_right, hW.isClosed_compl, hasBasis_nhdsSet, isClosed_compl, subset_compl_right, subset_interior_iff_mem_nhdsSet
-/
theorem IsCompact.exists_isOpen_closure_subset {K U : Set X} (hK : IsCompact K) (hU : U in 𝓝ˢ K) :
    exists V, IsOpen V ∧ K subseteq V ∧ closure V subseteq U := by
  have hd : Disjoint (𝓝ˢ K) (𝓝ˢ Uᶜ) := by
    simpa [hK.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
      ← subset_interior_iff_mem_nhdsSet] using! hU
  rcases ((hasBasis_nhdsSet _).disjoint_iff (hasBasis_nhdsSet _)).1 hd
    with ⟨V, ⟨hVo, hKV⟩, W, ⟨hW, hUW⟩, hVW⟩
  refine ⟨V, hVo, hKV, Subset.trans ?_ (compl_subset_comm.1 hUW)⟩
  exact closure_minimal hVW.subset_compl_right hW.isClosed_compl

/--
theorem `IsCompact.lift'_closure_nhdsSet` / 定理 `IsCompact.lift'_closure_nhdsSet`

English:
theorem IsCompact.lift'_closure_nhdsSet
  given: {K : Set X} (hK : IsCompact K)
  proof: by
  refine le_antisymm (fun U hU => ?_) (le_lift'_closure _)
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  exact mem_of_superset (mem_lift' <| hVo.mem_nhdsSet.2 hKV) hVU

中文:
定理 IsCompact.lift'_closure_nhdsSet
  条件: {K : Set X} (hK : IsCompact K)
  证明: by
  refine le_antisymm (fun U hU => ?_) (le_lift'_closure _)
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  exact mem_of_superset (mem_lift' <| hVo.mem_nhdsSet.2 hKV) hVU

Depends on / 依赖: _closure, exists_isOpen_closure_subset, hK.exists_isOpen_closure_subset, hVo.mem_nhdsSet, le_antisymm, le_lift, mem_lift, mem_nhdsSet, mem_of_superset
-/
theorem IsCompact.lift'_closure_nhdsSet {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).lift' closure = 𝓝ˢ K := by
  refine le_antisymm (fun U hU => ?_) (le_lift'_closure _)
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  exact mem_of_superset (mem_lift' <| hVo.mem_nhdsSet.2 hKV) hVU

/--
theorem `TopologicalSpace.IsTopologicalBasis.nhds_basis_closure` / 定理 `TopologicalSpace.IsTopologicalBasis.nhds_basis_closure`

English:
theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure
  statement: {B : Set (Set X)}
  proof: by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure

中文:
定理 TopologicalSpace.IsTopologicalBasis.nhds_basis_closure
  结论: {B : Set (Set X)}
  证明: by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure

Depends on / 依赖: and_comm, hB.nhds_hasBasis.nhds_closure, nhds_closure, nhds_hasBasis
-/
theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x in s ∧ s in B) closure := by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure

/--
theorem `TopologicalSpace.IsTopologicalBasis.exists_closure_subset` / 定理 `TopologicalSpace.IsTopologicalBasis.exists_closure_subset`

English:
theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset
  statement: {B : Set (Set X)}
  proof: by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h

中文:
定理 TopologicalSpace.IsTopologicalBasis.exists_closure_subset
  结论: {B : Set (Set X)}
  证明: by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h

Depends on / 依赖: and_assoc, exists_prop, hB.nhds_hasBasis.nhds_closure.mem_iff.mp, mem_iff, nhds_closure, nhds_hasBasis
-/
theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {x : X} {s : Set X} (h : s in 𝓝 x) :
    exists t in B, x in t ∧ closure t subseteq s := by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h

/--
theorem `Topology.IsInducing.regularSpace` / 定理 `Topology.IsInducing.regularSpace`

English:
theorem Topology.IsInducing.regularSpace
  statement: [TopologicalSpace Y] {f : Y -> X}
  proof: .of_hasBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous

中文:
定理 Topology.IsInducing.regularSpace
  结论: [TopologicalSpace Y] {f : Y -> X}
  证明: .of_hasBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous
-/
protected theorem Topology.IsInducing.regularSpace [TopologicalSpace Y] {f : Y -> X}
    (hf : IsInducing f) : RegularSpace Y :=
  .of_hasBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous

/--
theorem `regularSpace_induced` / 定理 `regularSpace_induced`

English:
theorem regularSpace_induced
  given: (f : Y -> X)
  statement: @RegularSpace Y (induced f ‹_›)
  proof: letI := induced f ‹_›
  (IsInducing.induced f).regularSpace

中文:
定理 regularSpace_induced
  条件: (f : Y -> X)
  结论: @RegularSpace Y (induced f ‹_›)
  证明: letI := induced f ‹_›
  (IsInducing.induced f).regularSpace

Depends on / 依赖: IsInducing, IsInducing.induced, induced, regularSpace
-/
theorem regularSpace_induced (f : Y -> X) : @RegularSpace Y (induced f ‹_›) :=
  letI := induced f ‹_›
  (IsInducing.induced f).regularSpace

/--
theorem `regularSpace_sInf` / 定理 `regularSpace_sInf`

English:
theorem regularSpace_sInf
  given: {X} {T : Set (TopologicalSpace X)} (h : forall t in T, @RegularSpace X t)
  proof: by
  let _ := sInf T
  have : forall a, (𝓝 a).HasBasis
      (fun If : Σ I : Set T, I -> Set X =>
        If.1.Finite ∧ forall i : If.1, If.2 i in @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := fun a => by
    rw [nhds_sInf]; rw [← iInf_subtype'']
    exact .iInf fun t

中文:
定理 regularSpace_sInf
  条件: {X} {T : Set (TopologicalSpace X)} (h : 对任意 t in T, @RegularSpace X t)
  证明: by
  let _ := sInf T
  have : forall a, (𝓝 a).HasBasis
      (fun If : Σ I : Set T, I -> Set X =>
        If.1.Finite ∧ forall i : If.1, If.2 i in @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := fun a => by
    rw [nhds_sInf]; rw [← iInf_subtype'']
    exact .iInf fun t

Depends on / 依赖: Finite, HasBasis, If.snd, IsClosed, closed_nhds_basis, iInf_subtype, isClosed_iInter, nhds_sInf, of_hasBasis, sInf_le
-/
theorem regularSpace_sInf {X} {T : Set (TopologicalSpace X)} (h : forall t in T, @RegularSpace X t) :
    @RegularSpace X (sInf T) := by
  let _ := sInf T
  have : forall a, (𝓝 a).HasBasis
      (fun If : Σ I : Set T, I -> Set X =>
        If.1.Finite ∧ forall i : If.1, If.2 i in @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := fun a => by
    rw [nhds_sInf]; rw [← iInf_subtype'']
    exact .iInf fun t : T => @closed_nhds_basis X t (h t t.2) a
  refine .of_hasBasis this fun a If hIf => isClosed_iInter fun i => ?_
  exact (hIf.2 i).2.mono (sInf_le (i : T).2)

/--
theorem `regularSpace_iInf` / 定理 `regularSpace_iInf`

English:
theorem regularSpace_iInf
  given: {ι X} {t : ι -> TopologicalSpace X} (h : forall i, @RegularSpace X (t i))
  proof: regularSpace_sInf forall_mem_range.mpr h

中文:
定理 regularSpace_iInf
  条件: {ι X} {t : ι -> TopologicalSpace X} (h : 对任意 i, @RegularSpace X (t i))
  证明: regularSpace_sInf forall_mem_range.mpr h

Depends on / 依赖: forall_mem_range, forall_mem_range.mpr, regularSpace_sInf
-/
theorem regularSpace_iInf {ι X} {t : ι -> TopologicalSpace X} (h : forall i, @RegularSpace X (t i)) :
    @RegularSpace X (iInf t) :=
regularSpace_sInf forall_mem_range.mpr h

/--
theorem `RegularSpace.inf` / 定理 `RegularSpace.inf`

English:
theorem RegularSpace.inf
  statement: {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
  proof: by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)

中文:
定理 RegularSpace.inf
  结论: {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
  证明: by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)

Depends on / 依赖: Bool.forall_bool, forall_bool, inf_eq_iInf, regularSpace_iInf
-/
theorem RegularSpace.inf {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
    (h₂ : @RegularSpace X t₂) : @RegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)

instance {p : X -> Prop} : RegularSpace (Subtype p) :=
  IsEmbedding.subtypeVal.isInducing.regularSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: Y] [RegularSpace Y] : RegularSpace (X × Y)
  body: (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))

中文:
实例 [TopologicalSpace
  签名: Y] [RegularSpace Y] : RegularSpace (X × Y)
  定义体: (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))

Depends on / 依赖: Prod.fst, Prod.snd, regularSpace_induced
-/
instance [TopologicalSpace Y] [RegularSpace Y] : RegularSpace (X × Y) :=
  (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))

instance {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, RegularSpace (X i)] :
    RegularSpace (forall i, X i) :=
  regularSpace_iInf fun _ => regularSpace_induced _

/--
lemma `SeparatedNhds.of_isCompact_isClosed` / 引理 `SeparatedNhds.of_isCompact_isClosed`

English:
lemma SeparatedNhds.of_isCompact_isClosed
  statement: {s t : Set X}
  proof: by
  simpa only [separatedNhds_iff_disjoint, hs.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
    ht.closure_eq, disjoint_left] using hst

中文:
引理 SeparatedNhds.of_isCompact_isClosed
  结论: {s t : Set X}
  证明: by
  simpa only [separatedNhds_iff_disjoint, hs.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
    ht.closure_eq, disjoint_left] using hst

Depends on / 依赖: closure_eq, disjoint_left, disjoint_nhdsSet_left, disjoint_nhds_nhdsSet, hs.disjoint_nhdsSet_left, ht.closure_eq, separatedNhds_iff_disjoint
-/
lemma SeparatedNhds.of_isCompact_isClosed {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simpa only [separatedNhds_iff_disjoint, hs.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
    ht.closure_eq, disjoint_left] using hst

end

/--
lemma `IsClosed.HasSeparatingCover` / 引理 `IsClosed.HasSeparatingCover`

English:
lemma IsClosed.HasSeparatingCover
  statement: {s t : Set X} [LindelofSpace X] [RegularSpace X]
  proof: by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ => trivial) (univ_eq_empty_iff.mpr empty_X)]
.1 exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_lef

中文:
引理 IsClosed.HasSeparatingCover
  结论: {s t : Set X} [LindelofSpace X] [RegularSpace X]
  证明: by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ => trivial) (univ_eq_empty_iff.mpr empty_X)]
.1 exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_lef
-/
lemma IsClosed.HasSeparatingCover {s t : Set X} [LindelofSpace X] [RegularSpace X]
    (s_cl : IsClosed s) (t_cl : IsClosed t) (st_dis : Disjoint s t) : HasSeparatingCover s t := by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ => trivial) (univ_eq_empty_iff.mpr empty_X)]
.1 exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_left t)
  -- This is almost `HasSeparatingCover`, but is not countable. We define for all `a : X` for use
  -- with `IsLindelof.indexed_countable_subcover` momentarily.
  have (a : X) : exists n : Set X, IsOpen n ∧ Disjoint (closure n) t ∧ (a in s -> a in n) := by
    wlog ains : a in s
.disjoint_closure_left, fun a => ains a⟩ · exact ⟨∅, isOpen_empty, SeparatedNhds.empty_left t
obtain ⟨n, nna, ncl, nsubkc⟩ := ((regularSpace_TFAE X).out 0 3 :).mp ‹RegularSpace X› a tᶜ
      t_cl.compl_mem_nhds (disjoint_left.mp st_dis ains)
    exact
      ⟨interior n,
       isOpen_interior,
       disjoint_left.mpr fun ⦃_⦄ ain =>
nsubkc (IsClosed.closure_subset_iff ncl).mpr interior_subset ain,
       fun _ => mem_interior_iff_mem_nhds.mpr nna⟩
  -- By Lindelöf, we may obtain a countable subcover witnessing `HasSeparatingCover`
  choose u u_open u_dis u_nhds using this
  obtain ⟨f, f_cov⟩ := s_cl.isLindelof.indexed_countable_subcover
    u u_open (fun a ainh => mem_iUnion.mpr ⟨a, u_nhds a ainh⟩)
  exact ⟨u ∘ f, f_cov, fun n => ⟨u_open (f n), u_dis (f n)⟩⟩

/--
theorem `disjoint_nested_nhds_of_not_inseparable` / 定理 `disjoint_nested_nhds_of_not_inseparable`

English:
theorem disjoint_nested_nhds_of_not_inseparable
  given: [RegularSpace X] {x y : X} (h : ¬Inseparable x y)
  proof: by
  rcases r1_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, 

中文:
定理 disjoint_nested_nhds_of_not_inseparable
  条件: [RegularSpace X] {x y : X} (h : ¬Inseparable x y)
  证明: by
  rcases r1_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, 

Depends on / 依赖: _op.mem_nhds, exists_mem_nhds_isClosed_subset, mem_nhds, mem_of_superset, r1_separation, x_in, y_in
-/
theorem disjoint_nested_nhds_of_not_inseparable [RegularSpace X] {x y : X} (h : ¬Inseparable x y) :
    exists U₁ in 𝓝 x, exists V₁ in 𝓝 x, exists U₂ in 𝓝 y, exists V₂ in 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ subseteq U₁ ∧ V₂ subseteq U₂ ∧ Disjoint U₁ U₂ := by
  rcases r1_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, V₁, V₁_in, U₂, mem_of_superset V₂_in h₂, V₂, V₂_in,
    V₁_closed, V₂_closed, U₁_op, U₂_op, h₁, h₂, H⟩

end RegularSpace

section LocallyCompactRegularSpace

/--
theorem `exists_compact_closed_between` / 定理 `exists_compact_closed_between`

English:
theorem exists_compact_closed_between
  statement: [LocallyCompactSpace X] [RegularSpace X]
  proof: let ⟨L, L_comp, KL, LU⟩ := exists_compact_between hK hU h_KU
⟨closure L, L_comp.closure, isClosed_closure, KL.trans interior_mono subset_closure,
    L_comp.closure_subset_of_isOpen hU LU⟩

中文:
定理 exists_compact_closed_between
  结论: [LocallyCompactSpace X] [RegularSpace X]
  证明: let ⟨L, L_comp, KL, LU⟩ := exists_compact_between hK hU h_KU
⟨closure L, L_comp.closure, isClosed_closure, KL.trans interior_mono subset_closure,
    L_comp.closure_subset_of_isOpen hU LU⟩

Depends on / 依赖: KL.trans, L_comp, L_comp.closure, L_comp.closure_subset_of_isOpen, closure, closure_subset_of_isOpen, exists_compact_between, h_KU, interior_mono, isClosed_closure, subset_closure
-/
theorem exists_compact_closed_between [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K subseteq U) :
    exists L, IsCompact L ∧ IsClosed L ∧ K subseteq interior L ∧ L subseteq U :=
  let ⟨L, L_comp, KL, LU⟩ := exists_compact_between hK hU h_KU
⟨closure L, L_comp.closure, isClosed_closure, KL.trans interior_mono subset_closure,
    L_comp.closure_subset_of_isOpen hU LU⟩

/--
theorem `IsCompact.nhdsSet_basis_isCompact_isClosed` / 定理 `IsCompact.nhdsSet_basis_isCompact_isClosed`

English:
theorem IsCompact.nhdsSet_basis_isCompact_isClosed
  proof: by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hL', hKL, hLU⟩ := exists_compact_closed_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], ⟨hL, hL'⟩, hLU⟩

中文:
定理 IsCompact.nhdsSet_basis_isCompact_isClosed
  证明: by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hL', hKL, hLU⟩ := exists_compact_closed_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], ⟨hL, hL'⟩, hLU⟩

Depends on / 依赖: exists_compact_closed_between, forall_iff, h_KU, hasBasis_nhdsSet, hasBasis_self, subset_interior_iff_mem_nhdsSet
-/
theorem IsCompact.nhdsSet_basis_isCompact_isClosed
    [LocallyCompactSpace X] [RegularSpace X] {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun L => L in 𝓝ˢ K ∧ IsCompact L ∧ IsClosed L) id := by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hL', hKL, hLU⟩ := exists_compact_closed_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], ⟨hL, hL'⟩, hLU⟩

/--
theorem `exists_open_between_and_isCompact_closure` / 定理 `exists_open_between_and_isCompact_closure`

English:
theorem exists_open_between_and_isCompact_closure
  statement: [LocallyCompactSpace X] [RegularSpace X]
  proof: by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) subseteq L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact L_compact.closur

中文:
定理 exists_open_between_and_isCompact_closure
  结论: [LocallyCompactSpace X] [RegularSpace X]
  证明: by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) subseteq L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact L_compact.closur

Depends on / 依赖: A.trans, L_closed, L_closed.closure_eq, L_compact, L_compact.closure_of_subset, closure, closure_eq, closure_mono, closure_of_subset, exists_compact_closed_between, interior, interior_subset, isOpen_interior, le_of_eq, subseteq
-/
theorem exists_open_between_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) :
    exists V, IsOpen V ∧ K subseteq V ∧ closure V subseteq U ∧ IsCompact (closure V) := by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) subseteq L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact L_compact.closure_of_subset interior_subset

/--
lemma `IsCompact.closure_eq_nhdsKer` / 引理 `IsCompact.closure_eq_nhdsKer`

English:
lemma IsCompact.closure_eq_nhdsKer
  given: [RegularSpace X] {s : Set X} (hs : IsCompact s)
  proof: by
  apply subset_antisymm
  · rw [nhdsKer, ← hs.lift'_closure_nhdsSet]
    simp +contextual [Filter.lift', Filter.lift, closure_mono, subset_of_mem_nhdsSet]
  · intro y hy
    by_contra! hy'
    rw [← _root_.disjoint_nhdsSet_nhds]; rw [Filter.disjoint_iff] at hy'
    obtain ⟨t, hts, t', ht'y, H⟩ :=

中文:
引理 IsCompact.closure_eq_nhdsKer
  条件: [RegularSpace X] {s : Set X} (hs : IsCompact s)
  证明: by
  apply subset_antisymm
  · rw [nhdsKer, ← hs.lift'_closure_nhdsSet]
    simp +contextual [Filter.lift', Filter.lift, closure_mono, subset_of_mem_nhdsSet]
  · intro y hy
    by_contra! hy'
    rw [← _root_.disjoint_nhdsSet_nhds]; rw [Filter.disjoint_iff] at hy'
    obtain ⟨t, hts, t', ht'y, H⟩ :=

Depends on / 依赖: Filter, Filter.disjoint_iff, Filter.lift, Set.disjoint_iff.mp, _closure_nhdsSet, _root_, _root_.disjoint_nhdsSet_nhds, closure_mono, contextual, disjoint_iff, disjoint_nhdsSet_nhds, hs.lift, mem_of_mem_nhds, nhdsKer, subset_antisymm, subset_of_mem_nhdsSet
-/
lemma IsCompact.closure_eq_nhdsKer [RegularSpace X] {s : Set X} (hs : IsCompact s) :
    closure s = nhdsKer s := by
  apply subset_antisymm
  · rw [nhdsKer, ← hs.lift'_closure_nhdsSet]
    simp +contextual [Filter.lift', Filter.lift, closure_mono, subset_of_mem_nhdsSet]
  · intro y hy
    by_contra! hy'
    rw [← _root_.disjoint_nhdsSet_nhds]; rw [Filter.disjoint_iff] at hy'
    obtain ⟨t, hts, t', ht'y, H⟩ := hy'
    exact Set.disjoint_iff.mp H ⟨hy t hts, mem_of_mem_nhds ht'y⟩

end LocallyCompactRegularSpace

section T25

/--
Definition of `T25Space` / `T25Space` 的定义

English:
class T25Space
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - t2_5 : forall ⦃x y : X⦄, x != y -> Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

中文:
类 T25Space
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - t2_5 : 对任意 ⦃x y : X⦄, x != y -> Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)
-/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : forall ⦃x y : X⦄, x != y -> Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

@[simp]
/--
theorem `disjoint_lift'_closure_nhds` / 定理 `disjoint_lift'_closure_nhds`

English:
theorem disjoint_lift'_closure_nhds
  given: [T25Space X] {x y : X}
  proof: ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩

中文:
定理 disjoint_lift'_closure_nhds
  条件: [T25Space X] {x y : X}
  证明: ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩

Depends on / 依赖: T25Space, T25Space.t2_5, nhds_neBot, nhds_neBot.ne, t2_5
-/
theorem disjoint_lift'_closure_nhds [T25Space X] {x y : X} :
    Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure) ↔ x != y :=
  ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩

-- see Note [lower instance priority]
instance (priority := 100) T25Space.t2Space [T25Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _ _ hne =>
    (disjoint_lift'_closure_nhds.2 hne).mono (le_lift'_closure _) (le_lift'_closure _)

/--
theorem `exists_nhds_disjoint_closure` / 定理 `exists_nhds_disjoint_closure`

English:
theorem exists_nhds_disjoint_closure
  given: [T25Space X] {x y : X} (h : x != y)
  proof: ((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1
    disjoint_lift'_closure_nhds.2 h

中文:
定理 exists_nhds_disjoint_closure
  条件: [T25Space X] {x y : X} (h : x != y)
  证明: ((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1
    disjoint_lift'_closure_nhds.2 h

Depends on / 依赖: _closure, _closure.disjoint_iff, _closure_nhds, basis_sets, basis_sets.lift, disjoint_iff, disjoint_lift
-/
theorem exists_nhds_disjoint_closure [T25Space X] {x y : X} (h : x != y) :
    exists s in 𝓝 x, exists t in 𝓝 y, Disjoint (closure s) (closure t) :=
((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1
    disjoint_lift'_closure_nhds.2 h

/--
theorem `exists_open_nhds_disjoint_closure` / 定理 `exists_open_nhds_disjoint_closure`

English:
theorem exists_open_nhds_disjoint_closure
  given: [T25Space X] {x y : X} (h : x != y)
  proof: by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)

中文:
定理 exists_open_nhds_disjoint_closure
  条件: [T25Space X] {x y : X} (h : x != y)
  证明: by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)

Depends on / 依赖: _closure, _closure.disjoint_iff, _closure_nhds, and_assoc, disjoint_iff, disjoint_lift, exists_prop, nhds_basis_opens
-/
theorem exists_open_nhds_disjoint_closure [T25Space X] {x y : X} (h : x != y) :
    exists u : Set X,
      x in u ∧ IsOpen u ∧ exists v : Set X, y in v ∧ IsOpen v ∧ Disjoint (closure u) (closure v) := by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)

/--
theorem `T25Space.of_injective_continuous` / 定理 `T25Space.of_injective_continuous`

English:
theorem T25Space.of_injective_continuous
  statement: [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
  proof: (tendsto_lift'_closure_nhds hcont x).disjoint (t2_5 <| hinj.ne hne)
    (tendsto_lift'_closure_nhds hcont y)

中文:
定理 T25Space.of_injective_continuous
  结论: [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
  证明: (tendsto_lift'_closure_nhds hcont x).disjoint (t2_5 <| hinj.ne hne)
    (tendsto_lift'_closure_nhds hcont y)

Depends on / 依赖: _closure_nhds, disjoint, hinj.ne, t2_5, tendsto_lift
-/
theorem T25Space.of_injective_continuous [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
    (hinj : Injective f) (hcont : Continuous f) : T25Space X where
  t2_5 x y hne := (tendsto_lift'_closure_nhds hcont x).disjoint (t2_5 <| hinj.ne hne)
    (tendsto_lift'_closure_nhds hcont y)

/--
theorem `Topology.IsEmbedding.t25Space` / 定理 `Topology.IsEmbedding.t25Space`

English:
theorem Topology.IsEmbedding.t25Space
  statement: [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
  proof: .of_injective_continuous hf.injective hf.continuous

中文:
定理 Topology.IsEmbedding.t25Space
  结论: [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
  证明: .of_injective_continuous hf.injective hf.continuous

Depends on / 依赖: continuous, hf.continuous, hf.injective, injective, of_injective_continuous
-/
theorem Topology.IsEmbedding.t25Space [TopologicalSpace Y] [T25Space Y] {f : X -> Y}
    (hf : IsEmbedding f) : T25Space X :=
  .of_injective_continuous hf.injective hf.continuous

/--
theorem `Homeomorph.t25Space` / 定理 `Homeomorph.t25Space`

English:
theorem Homeomorph.t25Space
  given: [TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y)
  statement: T25Space Y
  proof: h.symm.isEmbedding.t25Space

中文:
定理 Homeomorph.t25Space
  条件: [TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y)
  结论: T25Space Y
  证明: h.symm.isEmbedding.t25Space
-/
protected theorem Homeomorph.t25Space [TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y) : T25Space Y :=
  h.symm.isEmbedding.t25Space

/--
Instance `Subtype.instT25Space` / 实例 `Subtype.instT25Space`

English:
instance Subtype.instT25Space
  signature: [T25Space X] {p : X -> Prop}
  body: IsEmbedding.subtypeVal.t25Space

中文:
实例 Subtype.instT25Space
  签名: [T25Space X] {p : X -> 命题}
  定义体: IsEmbedding.subtypeVal.t25Space

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t25Space, subtypeVal, t25Space
-/
instance Subtype.instT25Space [T25Space X] {p : X -> Prop} : T25Space {x // p x} :=
  IsEmbedding.subtypeVal.t25Space

end T25

section T3

/--
Definition of `T3Space` / `T3Space` 的定义

English:
class T3Space
  parameters: (X : Type u) [TopologicalSpace X]
  extends: T0Space X, RegularSpace X
  (no additional axioms)

中文:
类 T3Space
  参数: (X : 类型u) [TopologicalSpace X]
  继承: T0Space X, RegularSpace X
  (无附加公理)
-/
class T3Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, RegularSpace X

instance (priority := 90) instT3Space [T0Space X] [RegularSpace X] : T3Space X := ⟨⟩

/--
theorem `RegularSpace.t3Space_iff_t0Space` / 定理 `RegularSpace.t3Space_iff_t0Space`

English:
theorem RegularSpace.t3Space_iff_t0Space
  given: [RegularSpace X]
  statement: T3Space X ↔ T0Space X
  proof: by
  constructor <;> intro <;> infer_instance

中文:
定理 RegularSpace.t3Space_iff_t0Space
  条件: [RegularSpace X]
  结论: T3Space X ↔ T0Space X
  证明: by
  constructor <;> intro <;> infer_instance

Depends on / 依赖: infer_instance
-/
theorem RegularSpace.t3Space_iff_t0Space [RegularSpace X] : T3Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

-- see Note [lower instance priority]
instance (priority := 100) T3Space.t25Space [T3Space X] : T25Space X := by
  refine ⟨fun x y hne => ?_⟩
  rw [lift'_nhds_closure]; rw [lift'_nhds_closure]
  have : x ∉ closure {y} ∨ y ∉ closure {x} :=
    (t0Space_iff_or_notMem_closure X).mp inferInstance hne
  simp only [← disjoint_nhds_nhdsSet, nhdsSet_singleton] at this
  exact this.elim id fun h => h.symm

/--
theorem `Topology.IsEmbedding.t3Space` / 定理 `Topology.IsEmbedding.t3Space`

English:
theorem Topology.IsEmbedding.t3Space
  statement: [TopologicalSpace Y] [T3Space Y] {f : X -> Y}
  proof: { toT0Space := hf.t0Space
    toRegularSpace := hf.isInducing.regularSpace }

中文:
定理 Topology.IsEmbedding.t3Space
  结论: [TopologicalSpace Y] [T3Space Y] {f : X -> Y}
  证明: { toT0Space := hf.t0Space
    toRegularSpace := hf.isInducing.regularSpace }
-/
protected theorem Topology.IsEmbedding.t3Space [TopologicalSpace Y] [T3Space Y] {f : X -> Y}
    (hf : IsEmbedding f) : T3Space X :=
  { toT0Space := hf.t0Space
    toRegularSpace := hf.isInducing.regularSpace }

/--
theorem `Homeomorph.t3Space` / 定理 `Homeomorph.t3Space`

English:
theorem Homeomorph.t3Space
  given: [TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y)
  statement: T3Space Y
  proof: h.symm.isEmbedding.t3Space

中文:
定理 Homeomorph.t3Space
  条件: [TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y)
  结论: T3Space Y
  证明: h.symm.isEmbedding.t3Space
-/
protected theorem Homeomorph.t3Space [TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y) : T3Space Y :=
  h.symm.isEmbedding.t3Space

/--
Instance `Subtype.t3Space` / 实例 `Subtype.t3Space`

English:
instance Subtype.t3Space
  signature: [T3Space X] {p : X -> Prop}
  body: IsEmbedding.subtypeVal.t3Space

中文:
实例 Subtype.t3Space
  签名: [T3Space X] {p : X -> 命题}
  定义体: IsEmbedding.subtypeVal.t3Space

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t3Space, subtypeVal, t3Space
-/
instance Subtype.t3Space [T3Space X] {p : X -> Prop} : T3Space (Subtype p) :=
  IsEmbedding.subtypeVal.t3Space

/--
Instance `ULift.instT3Space` / 实例 `ULift.instT3Space`

English:
instance ULift.instT3Space
  signature: [T3Space X]
  body: IsEmbedding.uliftDown.t3Space

中文:
实例 ULift.instT3Space
  签名: [T3Space X]
  定义体: IsEmbedding.uliftDown.t3Space

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.t3Space, t3Space, uliftDown
-/
instance ULift.instT3Space [T3Space X] : T3Space (ULift X) :=
  IsEmbedding.uliftDown.t3Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: Y] [T3Space X] [T3Space Y] : T3Space (X × Y)
  body: ⟨⟩

中文:
实例 [TopologicalSpace
  签名: Y] [T3Space X] [T3Space Y] : T3Space (X × Y)
  定义体: ⟨⟩
-/
instance [TopologicalSpace Y] [T3Space X] [T3Space Y] : T3Space (X × Y) := ⟨⟩

instance {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, T3Space (X i)] :
    T3Space (forall i, X i) := ⟨⟩

/--
theorem `disjoint_nested_nhds` / 定理 `disjoint_nested_nhds`

English:
theorem disjoint_nested_nhds
  given: [T3Space X] {x y : X} (h : x != y)
  proof: disjoint_nested_nhds_of_not_inseparable (mt Inseparable.eq h)

中文:
定理 disjoint_nested_nhds
  条件: [T3Space X] {x y : X} (h : x != y)
  证明: disjoint_nested_nhds_of_not_inseparable (mt Inseparable.eq h)

Depends on / 依赖: Inseparable, Inseparable.eq, disjoint_nested_nhds_of_not_inseparable
-/
theorem disjoint_nested_nhds [T3Space X] {x y : X} (h : x != y) :
    exists U₁ in 𝓝 x, exists V₁ in 𝓝 x, exists U₂ in 𝓝 y, exists V₂ in 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ subseteq U₁ ∧ V₂ subseteq U₂ ∧ Disjoint U₁ U₂ :=
  disjoint_nested_nhds_of_not_inseparable (mt Inseparable.eq h)

open SeparationQuotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RegularSpace
  signature: X] : T3Space (SeparationQuotient X) where
  body: by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhds_mk]; rw [comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

中文:
实例 [RegularSpace
  签名: X] : T3Space (SeparationQuotient X) where
  定义体: by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhds_mk]; rw [comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

Depends on / 依赖: RegularSpace, RegularSpace.regular, comap_mk_nhdsSet, comap_mk_nhds_mk, continuous_mk, disjoint_comap_iff, hs.preimage, preimage, regular, surjective_mk
-/
instance [RegularSpace X] : T3Space (SeparationQuotient X) where
  regular {s a} hs ha := by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhds_mk]; rw [comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

end T3

section NormalSpace

/--
Definition of `NormalSpace` / `NormalSpace` 的定义

English:
class NormalSpace
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - normal : forall s t : Set X, IsClosed s -> IsClosed t -> Disjoint s t -> SeparatedNhds s t

中文:
类 NormalSpace
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - normal : 对任意 s t : Set X, IsClosed s -> IsClosed t -> Disjoint s t -> SeparatedNhds s t
-/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two disjoint sets in a normal space admit disjoint neighbourhoods. -/
  normal : forall s t : Set X, IsClosed s -> IsClosed t -> Disjoint s t -> SeparatedNhds s t

/--
theorem `normal_separation` / 定理 `normal_separation`

English:
theorem normal_separation
  statement: [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
  proof: NormalSpace.normal s t H1 H2 H3

中文:
定理 normal_separation
  结论: [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
  证明: NormalSpace.normal s t H1 H2 H3

Depends on / 依赖: NormalSpace, NormalSpace.normal, normal
-/
theorem normal_separation [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
    (H3 : Disjoint s t) : SeparatedNhds s t :=
  NormalSpace.normal s t H1 H2 H3

/--
theorem `disjoint_nhdsSet_nhdsSet` / 定理 `disjoint_nhdsSet_nhdsSet`

English:
theorem disjoint_nhdsSet_nhdsSet
  statement: [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
  proof: (normal_separation hs ht hd).disjoint_nhdsSet

中文:
定理 disjoint_nhdsSet_nhdsSet
  结论: [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
  证明: (normal_separation hs ht hd).disjoint_nhdsSet

Depends on / 依赖: disjoint_nhdsSet, normal_separation
-/
theorem disjoint_nhdsSet_nhdsSet [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : Disjoint (𝓝ˢ s) (𝓝ˢ t) :=
  (normal_separation hs ht hd).disjoint_nhdsSet

/--
theorem `normal_exists_closure_subset` / 定理 `normal_exists_closure_subset`

English:
theorem normal_exists_closure_subset
  statement: [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
  proof: by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1

中文:
定理 normal_exists_closure_subset
  结论: [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
  证明: by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1

Depends on / 依赖: Disjoint, Set.disjoint_left.mpr, Subset, Subset.trans, closure_minimal, compl_subset_comm, disjoint_left, isClosed_compl_iff, le_bot, normal_separation
-/
theorem normal_exists_closure_subset [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
    (hst : s subseteq t) : exists u, IsOpen u ∧ s subseteq u ∧ closure u subseteq t := by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1 htt')⟩
  exact fun x hxs hxt => hs't'.le_bot ⟨hxs, hxt⟩

/--
theorem `exists_mem_nhdsSet_isClosed_subset` / 定理 `exists_mem_nhdsSet_isClosed_subset`

English:
theorem exists_mem_nhdsSet_isClosed_subset
  statement: [NormalSpace X] {u s : Set X} (h : s in 𝓝ˢ u)
  proof: by
  obtain ⟨o, ho_open, huo, hos⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨v, hv_open, huv, hcvo⟩ := normal_exists_closure_subset hu ho_open huo
  refine ⟨closure v, ?_, isClosed_closure, hcvo.trans hos⟩
  exact mem_of_superset (mem_nhdsSet_iff_exists.mpr ⟨v, hv_open, huv, subset_rfl⟩) subset_closu

中文:
定理 exists_mem_nhdsSet_isClosed_subset
  结论: [NormalSpace X] {u s : Set X} (h : s in 𝓝ˢ u)
  证明: by
  obtain ⟨o, ho_open, huo, hos⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨v, hv_open, huv, hcvo⟩ := normal_exists_closure_subset hu ho_open huo
  refine ⟨closure v, ?_, isClosed_closure, hcvo.trans hos⟩
  exact mem_of_superset (mem_nhdsSet_iff_exists.mpr ⟨v, hv_open, huv, subset_rfl⟩) subset_closu

Depends on / 依赖: closure, hcvo.trans, ho_open, hv_open, isClosed_closure, mem_nhdsSet_iff_exists, mem_nhdsSet_iff_exists.mp, mem_nhdsSet_iff_exists.mpr, mem_of_superset, normal_exists_closure_subset, subset_closure, subset_rfl
-/
theorem exists_mem_nhdsSet_isClosed_subset [NormalSpace X] {u s : Set X} (h : s in 𝓝ˢ u)
    (hu : IsClosed u) : exists t in 𝓝ˢ u, IsClosed t ∧ t subseteq s := by
  obtain ⟨o, ho_open, huo, hos⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨v, hv_open, huv, hcvo⟩ := normal_exists_closure_subset hu ho_open huo
  refine ⟨closure v, ?_, isClosed_closure, hcvo.trans hos⟩
  exact mem_of_superset (mem_nhdsSet_iff_exists.mpr ⟨v, hv_open, huv, subset_rfl⟩) subset_closure

/--
theorem `closed_nhdsSet_basis` / 定理 `closed_nhdsSet_basis`

English:
theorem closed_nhdsSet_basis
  given: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  statement: (𝓝ˢ u).HasBasis
  proof: by
  refine hasBasis_self.2 fun _ ht => exists_mem_nhdsSet_isClosed_subset ht hu

中文:
定理 closed_nhdsSet_basis
  条件: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  结论: (𝓝ˢ u).HasBasis
  证明: by
  refine hasBasis_self.2 fun _ ht => exists_mem_nhdsSet_isClosed_subset ht hu

Depends on / 依赖: exists_mem_nhdsSet_isClosed_subset, hasBasis_self
-/
theorem closed_nhdsSet_basis [NormalSpace X] (u : Set X) (hu : IsClosed u) : (𝓝ˢ u).HasBasis
    (fun s : Set X => s in 𝓝ˢ u ∧ IsClosed s) id := by
  refine hasBasis_self.2 fun _ ht => exists_mem_nhdsSet_isClosed_subset ht hu

/--
theorem `lift'_nhdsSet_closure` / 定理 `lift'_nhdsSet_closure`

English:
theorem lift'_nhdsSet_closure
  given: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  proof: (closed_nhdsSet_basis u hu).lift'_closure_eq_self fun _ => And.right

中文:
定理 lift'_nhdsSet_closure
  条件: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  证明: (closed_nhdsSet_basis u hu).lift'_closure_eq_self fun _ => And.right
-/
theorem lift'_nhdsSet_closure [NormalSpace X] (u : Set X) (hu : IsClosed u) :
    (𝓝ˢ u).lift' closure = 𝓝ˢ u :=
  (closed_nhdsSet_basis u hu).lift'_closure_eq_self fun _ => And.right

/--
theorem `Filter.HasBasis.nhdsSet_closure` / 定理 `Filter.HasBasis.nhdsSet_closure`

English:
theorem Filter.HasBasis.nhdsSet_closure
  statement: [NormalSpace X] {ι : Sort*} {u : Set X} {p : ι -> Prop}
  proof: lift'_nhdsSet_closure u hu ▸ h.lift'_closure

中文:
定理 Filter.HasBasis.nhdsSet_closure
  结论: [NormalSpace X] {ι : Sort*} {u : Set X} {p : ι -> 命题}
  证明: lift'_nhdsSet_closure u hu ▸ h.lift'_closure

Depends on / 依赖: _closure, _nhdsSet_closure, h.lift
-/
theorem Filter.HasBasis.nhdsSet_closure [NormalSpace X] {ι : Sort*} {u : Set X} {p : ι -> Prop}
    {s : ι -> Set X} (hu : IsClosed u) (h : (𝓝ˢ u).HasBasis p s) :
    (𝓝ˢ u).HasBasis p fun i => closure (s i) :=
  lift'_nhdsSet_closure u hu ▸ h.lift'_closure

/--
theorem `hasBasis_nhdsSet_closure` / 定理 `hasBasis_nhdsSet_closure`

English:
theorem hasBasis_nhdsSet_closure
  given: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  proof: (𝓝ˢ u).basis_sets.nhdsSet_closure hu

中文:
定理 hasBasis_nhdsSet_closure
  条件: [NormalSpace X] (u : Set X) (hu : IsClosed u)
  证明: (𝓝ˢ u).basis_sets.nhdsSet_closure hu

Depends on / 依赖: basis_sets, basis_sets.nhdsSet_closure, nhdsSet_closure
-/
theorem hasBasis_nhdsSet_closure [NormalSpace X] (u : Set X) (hu : IsClosed u) :
    (𝓝ˢ u).HasBasis (fun s => s in 𝓝ˢ u) closure :=
  (𝓝ˢ u).basis_sets.nhdsSet_closure hu

/--
theorem `Topology.IsClosedEmbedding.normalSpace` / 定理 `Topology.IsClosedEmbedding.normalSpace`

English:
theorem Topology.IsClosedEmbedding.normalSpace
  statement: [TopologicalSpace Y] [NormalSpace Y]
  proof: by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.injective hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)

中文:
定理 Topology.IsClosedEmbedding.normalSpace
  结论: [TopologicalSpace Y] [NormalSpace Y]
  证明: by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.injective hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)
-/
protected theorem Topology.IsClosedEmbedding.normalSpace [TopologicalSpace Y] [NormalSpace Y]
    {f : X -> Y} (hf : IsClosedEmbedding f) : NormalSpace X where
  normal s t hs ht hst := by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.injective hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)

/--
theorem `Homeomorph.normalSpace` / 定理 `Homeomorph.normalSpace`

English:
theorem Homeomorph.normalSpace
  given: [TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y)
  proof: h.symm.isClosedEmbedding.normalSpace

中文:
定理 Homeomorph.normalSpace
  条件: [TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y)
  证明: h.symm.isClosedEmbedding.normalSpace
-/
protected theorem Homeomorph.normalSpace [TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y) :
    NormalSpace Y :=
  h.symm.isClosedEmbedding.normalSpace

instance (priority := 100) NormalSpace.of_compactSpace_r1Space [CompactSpace X] [R1Space X] :
    NormalSpace X where
  normal _s _t hs ht := .of_isCompact_isCompact_isClosed hs.isCompact ht.isCompact ht

/-- A regular topological space with a Lindelöf topology is a normal space. A consequence of e.g.
Corollaries 20.8 and 20.10 of [Willard's *General Topology*][zbMATH02107988] (without the
assumption of Hausdorff). -/
instance (priority := 100) NormalSpace.of_regularSpace_lindelofSpace
    [RegularSpace X] [LindelofSpace X] : NormalSpace X where
  normal _ _ hcl kcl hkdis :=
    hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hcl.HasSeparatingCover kcl hkdis, kcl.HasSeparatingCover hcl (Disjoint.symm hkdis)⟩

instance (priority := 100) NormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : NormalSpace X :=
  of_regularSpace_lindelofSpace

end NormalSpace

section Normality

/--
Definition of `T4Space` / `T4Space` 的定义

English:
class T4Space
  parameters: (X : Type u) [TopologicalSpace X]
  extends: T1Space X, NormalSpace X
  (no additional axioms)

中文:
类 T4Space
  参数: (X : 类型u) [TopologicalSpace X]
  继承: T1Space X, NormalSpace X
  (无附加公理)
-/
class T4Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, NormalSpace X

instance (priority := 100) [T1Space X] [NormalSpace X] : T4Space X := ⟨⟩

-- see Note [lower instance priority]
instance (priority := 100) T4Space.t3Space [T4Space X] : T3Space X where
  regular hs hxs := by simpa only [nhdsSet_singleton] using (normal_separation hs isClosed_singleton
    (disjoint_singleton_right.mpr hxs)).disjoint_nhdsSet

/--
theorem `Topology.IsClosedEmbedding.t4Space` / 定理 `Topology.IsClosedEmbedding.t4Space`

English:
theorem Topology.IsClosedEmbedding.t4Space
  statement: [TopologicalSpace Y] [T4Space Y] {f : X -> Y}
  proof: hf.isEmbedding.t1Space
  toNormalSpace := hf.normalSpace

中文:
定理 Topology.IsClosedEmbedding.t4Space
  结论: [TopologicalSpace Y] [T4Space Y] {f : X -> Y}
  证明: hf.isEmbedding.t1Space
  toNormalSpace := hf.normalSpace
-/
protected theorem Topology.IsClosedEmbedding.t4Space [TopologicalSpace Y] [T4Space Y] {f : X -> Y}
    (hf : IsClosedEmbedding f) : T4Space X where
  toT1Space := hf.isEmbedding.t1Space
  toNormalSpace := hf.normalSpace

/--
theorem `Homeomorph.t4Space` / 定理 `Homeomorph.t4Space`

English:
theorem Homeomorph.t4Space
  given: [TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y)
  statement: T4Space Y
  proof: h.symm.isClosedEmbedding.t4Space

中文:
定理 Homeomorph.t4Space
  条件: [TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y)
  结论: T4Space Y
  证明: h.symm.isClosedEmbedding.t4Space
-/
protected theorem Homeomorph.t4Space [TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y) : T4Space Y :=
  h.symm.isClosedEmbedding.t4Space

/--
Instance `ULift.instT4Space` / 实例 `ULift.instT4Space`

English:
instance ULift.instT4Space
  signature: [T4Space X]
  body: IsClosedEmbedding.uliftDown.t4Space

中文:
实例 ULift.instT4Space
  签名: [T4Space X]
  定义体: IsClosedEmbedding.uliftDown.t4Space

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.uliftDown.t4Space, t4Space, uliftDown
-/
instance ULift.instT4Space [T4Space X] : T4Space (ULift X) := IsClosedEmbedding.uliftDown.t4Space

namespace SeparationQuotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormalSpace
  signature: X] : NormalSpace (SeparationQuotient X) where
  body: separatedNhds_iff_disjoint.2 by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

中文:
实例 [NormalSpace
  签名: X] : NormalSpace (SeparationQuotient X) where
  定义体: separatedNhds_iff_disjoint.2 by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

Depends on / 依赖: comap_mk_nhdsSet, continuous_mk, disjoint_comap_iff, disjoint_nhdsSet_nhdsSet, hd.preimage, hs.preimage, ht.preimage, preimage, separatedNhds_iff_disjoint, surjective_mk
-/
instance [NormalSpace X] : NormalSpace (SeparationQuotient X) where
normal s t hs ht hd := separatedNhds_iff_disjoint.2 by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

end SeparationQuotient

end Normality

section CompletelyNormal

/--
Definition of `CompletelyNormalSpace` / `CompletelyNormalSpace` 的定义

English:
class CompletelyNormalSpace
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - completely_normal : forall ⦃s t : Set X⦄, Disjoint (closure s) t -> Disjoint s (closure t) -> Disjoint (𝓝ˢ s) (𝓝ˢ t)

中文:
类 CompletelyNormalSpace
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - completely_normal : 对任意 ⦃s t : Set X⦄, Disjoint (closure s) t -> Disjoint s (closure t) -> Disjoint (𝓝ˢ s) (𝓝ˢ t)
-/
class CompletelyNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`, then `s` and `t`
  admit disjoint neighbourhoods. -/
  completely_normal :
    forall ⦃s t : Set X⦄, Disjoint (closure s) t -> Disjoint s (closure t) -> Disjoint (𝓝ˢ s) (𝓝ˢ t)

export CompletelyNormalSpace (completely_normal)

-- see Note [lower instance priority]
/-- A completely normal space is a normal space. -/
instance (priority := 100) CompletelyNormalSpace.toNormalSpace
    [CompletelyNormalSpace X] : NormalSpace X where
normal s t hs ht hd := separatedNhds_iff_disjoint.2
    completely_normal (by rwa [hs.closure_eq]) (by rwa [ht.closure_eq])

/--
theorem `Topology.IsInducing.completelyNormalSpace` / 定理 `Topology.IsInducing.completelyNormalSpace`

English:
theorem Topology.IsInducing.completelyNormalSpace
  statement: [TopologicalSpace Y] [CompletelyNormalSpace Y]
  proof: by
  refine ⟨fun s t hd₁ hd₂ => ?_⟩
  simp only [he.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_i

中文:
定理 Topology.IsInducing.completelyNormalSpace
  结论: [TopologicalSpace Y] [CompletelyNormalSpace Y]
  证明: by
  refine ⟨fun s t hd₁ hd₂ => ?_⟩
  simp only [he.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_i

Depends on / 依赖: closure_eq_preimage_closure_image, completely_normal, disjoint_comap, he.closure_eq_preimage_closure_image, he.nhdsSet_eq_comap, image_subset_iff, nhdsSet_eq_comap, preimage_compl, subset_compl_iff_disjoint_left, subset_compl_iff_disjoint_right
-/
theorem Topology.IsInducing.completelyNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y]
    {e : X -> Y} (he : IsInducing e) : CompletelyNormalSpace X := by
  refine ⟨fun s t hd₁ hd₂ => ?_⟩
  simp only [he.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_iff_disjoint_right, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_right]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompletelyNormalSpace
  signature: X] {p
  body: IsEmbedding.subtypeVal.completelyNormalSpace

中文:
实例 [CompletelyNormalSpace
  签名: X] {p
  定义体: IsEmbedding.subtypeVal.completelyNormalSpace

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.completelyNormalSpace, completelyNormalSpace, subtypeVal
-/
instance [CompletelyNormalSpace X] {p : X -> Prop} : CompletelyNormalSpace { x // p x } :=
  IsEmbedding.subtypeVal.completelyNormalSpace

/--
Instance `ULift.instCompletelyNormalSpace` / 实例 `ULift.instCompletelyNormalSpace`

English:
instance ULift.instCompletelyNormalSpace
  signature: [CompletelyNormalSpace X]
  body: IsEmbedding.uliftDown.completelyNormalSpace

中文:
实例 ULift.instCompletelyNormalSpace
  签名: [CompletelyNormalSpace X]
  定义体: IsEmbedding.uliftDown.completelyNormalSpace

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.completelyNormalSpace, completelyNormalSpace, uliftDown
-/
instance ULift.instCompletelyNormalSpace [CompletelyNormalSpace X] :
    CompletelyNormalSpace (ULift X) :=
  IsEmbedding.uliftDown.completelyNormalSpace

/--
theorem `completelyNormalSpace_iff_forall_isOpen_normalSpace` / 定理 `completelyNormalSpace_iff_forall_isOpen_normalSpace`

English:
theorem completelyNormalSpace_iff_forall_isOpen_normalSpace
  proof: by
  refine ⟨fun _ _ _ => inferInstance, fun h => ⟨fun s t hSt hsT => ?_⟩⟩
  let e := (closure s inter closure t)ᶜ
  have he : IsOpen e := (isClosed_closure.inter isClosed_closure).isOpen_compl
  specialize h e he
  have hst : Disjoint (((↑) : e -> X) ⁻¹' closure s) (((↑) : e -> X) ⁻¹' closure t) :=

中文:
定理 completelyNormalSpace_iff_forall_isOpen_normalSpace
  证明: by
  refine ⟨fun _ _ _ => inferInstance, fun h => ⟨fun s t hSt hsT => ?_⟩⟩
  let e := (closure s inter closure t)ᶜ
  have he : IsOpen e := (isClosed_closure.inter isClosed_closure).isOpen_compl
  specialize h e he
  have hst : Disjoint (((↑) : e -> X) ⁻¹' closure s) (((↑) : e -> X) ⁻¹' closure t) :=

Depends on / 依赖: Disjoint, IsOpen, closure, continuous_sub, continuous_subtype_val, disjoint_left, isClosed_closure, isClosed_closure.inter, isClosed_closure.preimage, isOpen_compl, normal_separation, preimage, specialize
-/
theorem completelyNormalSpace_iff_forall_isOpen_normalSpace :
    CompletelyNormalSpace X ↔ forall s : Set X, IsOpen s -> NormalSpace s := by
  refine ⟨fun _ _ _ => inferInstance, fun h => ⟨fun s t hSt hsT => ?_⟩⟩
  let e := (closure s inter closure t)ᶜ
  have he : IsOpen e := (isClosed_closure.inter isClosed_closure).isOpen_compl
  specialize h e he
  have hst : Disjoint (((↑) : e -> X) ⁻¹' closure s) (((↑) : e -> X) ⁻¹' closure t) := by
    rw [disjoint_left]
    intro x hxs hxt
    exact x.2 ⟨hxs, hxt⟩
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := normal_separation
    (isClosed_closure.preimage continuous_subtype_val)
    (isClosed_closure.preimage continuous_subtype_val) hst
  rw [Topology.IsInducing.subtypeVal.isOpen_iff] at hU hV
  obtain ⟨U, hU, rfl⟩ := hU
  obtain ⟨V, hV, rfl⟩ := hV
  rw [← separatedNhds_iff_disjoint]
  rw [Subtype.preimage_val_subset_preimage_val_iff]; rw [inter_comm e]; rw [inter_comm e] at hsU htV
  refine ⟨U inter e, V inter e, hU.inter he, hV.inter he, ?_, ?_, ?_⟩
  · intro x hx
    exact hsU ⟨subset_closure hx, fun h => hsT.notMem_of_mem_left hx h.2⟩
  · intro x hx
    exact htV ⟨subset_closure hx, fun h => hSt.notMem_of_mem_left h.1 hx⟩
  · rw [disjoint_left] at hUV ⊢
    intro x hxU hxV
    exact @hUV ⟨x, hxU.2⟩ hxU.1 hxV.1

/--
theorem `completelyNormalSpace_iff_forall_normalSpace` / 定理 `completelyNormalSpace_iff_forall_normalSpace`

English:
theorem completelyNormalSpace_iff_forall_normalSpace
  proof: ⟨fun _ _ => inferInstance, fun h =>
    completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s _ => h s⟩

alias ⟨_, CompletelyNormalSpace.of_forall_isOpen_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_isOpen_normalSpace
alias ⟨_, CompletelyNormalSpace.of_forall_normalSpace⟩ :=
  completely

中文:
定理 completelyNormalSpace_iff_forall_normalSpace
  证明: ⟨fun _ _ => inferInstance, fun h =>
    completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s _ => h s⟩

alias ⟨_, CompletelyNormalSpace.of_forall_isOpen_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_isOpen_normalSpace
alias ⟨_, CompletelyNormalSpace.of_forall_normalSpace⟩ :=
  completely

Depends on / 依赖: completelyNormalSpace_iff_forall_isOpen_normalSpace
-/
theorem completelyNormalSpace_iff_forall_normalSpace :
    CompletelyNormalSpace X ↔ forall s : Set X, NormalSpace s :=
  ⟨fun _ _ => inferInstance, fun h =>
    completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s _ => h s⟩

alias ⟨_, CompletelyNormalSpace.of_forall_isOpen_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_isOpen_normalSpace
alias ⟨_, CompletelyNormalSpace.of_forall_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_normalSpace

instance (priority := 100) CompletelyNormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : CompletelyNormalSpace X :=
  .of_forall_normalSpace fun _ => .of_regularSpace_secondCountableTopology

/--
Definition of `T5Space` / `T5Space` 的定义

English:
class T5Space
  parameters: (X : Type u) [TopologicalSpace X]
  extends: T1Space X, CompletelyNormalSpace X
  (no additional axioms)

中文:
类 T5Space
  参数: (X : 类型u) [TopologicalSpace X]
  继承: T1Space X, CompletelyNormalSpace X
  (无附加公理)
-/
class T5Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, CompletelyNormalSpace X

/--
theorem `Topology.IsEmbedding.t5Space` / 定理 `Topology.IsEmbedding.t5Space`

English:
theorem Topology.IsEmbedding.t5Space
  statement: [TopologicalSpace Y] [T5Space Y] {e : X -> Y}
  proof: he.completelyNormalSpace
  toT1Space := he.t1Space

中文:
定理 Topology.IsEmbedding.t5Space
  结论: [TopologicalSpace Y] [T5Space Y] {e : X -> Y}
  证明: he.completelyNormalSpace
  toT1Space := he.t1Space

Depends on / 依赖: completelyNormalSpace, he.completelyNormalSpace
-/
theorem Topology.IsEmbedding.t5Space [TopologicalSpace Y] [T5Space Y] {e : X -> Y}
    (he : IsEmbedding e) : T5Space X where
  toCompletelyNormalSpace := he.completelyNormalSpace
  toT1Space := he.t1Space

/--
theorem `Homeomorph.t5Space` / 定理 `Homeomorph.t5Space`

English:
theorem Homeomorph.t5Space
  given: [TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y)
  statement: T5Space Y
  proof: h.symm.isClosedEmbedding.t5Space

中文:
定理 Homeomorph.t5Space
  条件: [TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y)
  结论: T5Space Y
  证明: h.symm.isClosedEmbedding.t5Space
-/
protected theorem Homeomorph.t5Space [TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y) : T5Space Y :=
  h.symm.isClosedEmbedding.t5Space

-- see Note [lower instance priority]
/-- A `T₅` space is a `T₄` space. -/
instance (priority := 100) T5Space.toT4Space [T5Space X] : T4Space X where
  -- follows from type-class inference

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T5Space
  signature: X] {p
  body: IsEmbedding.subtypeVal.t5Space

中文:
实例 [T5Space
  签名: X] {p
  定义体: IsEmbedding.subtypeVal.t5Space

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t5Space, subtypeVal, t5Space
-/
instance [T5Space X] {p : X -> Prop} : T5Space { x // p x } :=
  IsEmbedding.subtypeVal.t5Space

/--
Instance `ULift.instT5Space` / 实例 `ULift.instT5Space`

English:
instance ULift.instT5Space
  signature: [T5Space X]
  body: IsEmbedding.uliftDown.t5Space

中文:
实例 ULift.instT5Space
  签名: [T5Space X]
  定义体: IsEmbedding.uliftDown.t5Space

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.t5Space, t5Space, uliftDown
-/
instance ULift.instT5Space [T5Space X] : T5Space (ULift X) :=
  IsEmbedding.uliftDown.t5Space

/--
theorem `t5Space_iff_forall_isOpen_t4Space` / 定理 `t5Space_iff_forall_isOpen_t4Space`

English:
theorem t5Space_iff_forall_isOpen_t4Space
  proof: inferInstance
  mpr h :=
    { toCompletelyNormalSpace :=
        completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s hs => (h s hs).toNormalSpace
      toT1Space :=
        have := h univ isOpen_univ
        t1Space_of_injective_of_continuous
          (fun _ _ => congrArg Subtype.val) (con

中文:
定理 t5Space_iff_forall_isOpen_t4Space
  证明: inferInstance
  mpr h :=
    { toCompletelyNormalSpace :=
        completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s hs => (h s hs).toNormalSpace
      toT1Space :=
        have := h univ isOpen_univ
        t1Space_of_injective_of_continuous
          (fun _ _ => congrArg Subtype.val) (con
-/
theorem t5Space_iff_forall_isOpen_t4Space :
    T5Space X ↔ forall s : Set X, IsOpen s -> T4Space s where
  mp _ _ _ := inferInstance
  mpr h :=
    { toCompletelyNormalSpace :=
        completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s hs => (h s hs).toNormalSpace
      toT1Space :=
        have := h univ isOpen_univ
        t1Space_of_injective_of_continuous
          (fun _ _ => congrArg Subtype.val) (continuous_id.subtype_mk mem_univ) }

/--
theorem `t5Space_iff_forall_t4Space` / 定理 `t5Space_iff_forall_t4Space`

English:
theorem t5Space_iff_forall_t4Space
  proof: ⟨fun _ _ => inferInstance, fun h => t5Space_iff_forall_isOpen_t4Space.2 fun s _ => h s⟩

alias ⟨_, T5Space.of_forall_isOpen_t4Space⟩ := t5Space_iff_forall_isOpen_t4Space
alias ⟨_, T5Space.of_forall_t4Space⟩ := t5Space_iff_forall_t4Space

中文:
定理 t5Space_iff_forall_t4Space
  证明: ⟨fun _ _ => inferInstance, fun h => t5Space_iff_forall_isOpen_t4Space.2 fun s _ => h s⟩

alias ⟨_, T5Space.of_forall_isOpen_t4Space⟩ := t5Space_iff_forall_isOpen_t4Space
alias ⟨_, T5Space.of_forall_t4Space⟩ := t5Space_iff_forall_t4Space

Depends on / 依赖: t5Space_iff_forall_isOpen_t4Space
-/
theorem t5Space_iff_forall_t4Space :
    T5Space X ↔ forall s : Set X, T4Space s :=
  ⟨fun _ _ => inferInstance, fun h => t5Space_iff_forall_isOpen_t4Space.2 fun s _ => h s⟩

alias ⟨_, T5Space.of_forall_isOpen_t4Space⟩ := t5Space_iff_forall_isOpen_t4Space
alias ⟨_, T5Space.of_forall_t4Space⟩ := t5Space_iff_forall_t4Space

open SeparationQuotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompletelyNormalSpace
  signature: X] [R0Space X] : T5Space (SeparationQuotient X) where
  body: by
    rwa [((t1Space_TFAE (SeparationQuotient X)).out 1 0 :), SeparationQuotient.t1Space_iff]
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    apply completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.pr

中文:
实例 [CompletelyNormalSpace
  签名: X] [R0Space X] : T5Space (SeparationQuotient X) where
  定义体: by
    rwa [((t1Space_TFAE (SeparationQuotient X)).out 1 0 :), SeparationQuotient.t1Space_iff]
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    apply completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.pr

Depends on / 依赖: SeparationQuotient, SeparationQuotient.t1Space_iff, comap_mk_nhdsSet, completely_normal, disjoint_comap_iff, exacts, preimage, preimage_mk_closure, surjective_mk, t1Space_TFAE, t1Space_iff
-/
instance [CompletelyNormalSpace X] [R0Space X] : T5Space (SeparationQuotient X) where
  t1 := by
    rwa [((t1Space_TFAE (SeparationQuotient X)).out 1 0 :), SeparationQuotient.t1Space_iff]
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk]; rw [comap_mk_nhdsSet]; rw [comap_mk_nhdsSet]
    apply completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.preimage mk, hd₂.preimage mk]

end CompletelyNormal

/--
theorem `connectedComponent_eq_iInter_isClopen` / 定理 `connectedComponent_eq_iInter_isClopen`

English:
theorem connectedComponent_eq_iInter_isClopen
  given: [T2Space X] [CompactSpace X] (x : X)
  proof: by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  --

中文:
定理 connectedComponent_eq_iInter_isClopen
  条件: [T2Space X] [CompactSpace X] (x : X)
  证明: by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  --

Depends on / 依赖: Subset, Subset.antisymm, antisymm, connectedComponent_subset_iInter_isClopen
-/
theorem connectedComponent_eq_iInter_isClopen [T2Space X] [CompactSpace X] (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x in s }, s := by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `X` we need that `s` is closed
  have hs : @IsClosed X _ (⋂ s : { s : Set X // IsClopen s ∧ x in s }, s) :=
    isClosed_iInter fun s => s.2.1.1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hs]
  intro a b ha hb hab ab_disj
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb ab_disj with ⟨u, v, hu, hv, hau, hbv, huv⟩
  obtain ⟨s, H⟩ : exists s : Set X, IsClopen s ∧ x in s ∧ s subseteq u union v := by
    /- Now we find a clopen set `s` around `x`, contained in `u ∪ v`. We utilize the fact that
    `X \ u ∪ v` will be compact, so there must be some finite intersection of clopen neighbourhoods
    of `X` disjoint to it, but a finite intersection of clopen sets is clopen,
    so we let this be our `s`. -/
    have H1 := (hu.union hv).isClosed_compl.isCompact.inter_iInter_nonempty
      (fun s : { s : Set X // IsClopen s ∧ x in s } => s) fun s => s.2.1.1
    rw [← not_disjoint_iff_nonempty_inter]; rw [imp_not_comm]; rw [not_forall] at H1
    obtain ⟨si, H2⟩ :=
      H1 (disjoint_compl_left_iff_subset.2 <| hab.trans <| union_subset_union hau hbv)
    refine ⟨⋂ U in si, Subtype.val U, ?_, ?_, ?_⟩
    · exact isClopen_biInter_finset fun s _ => s.2.1
    · exact mem_iInter₂.2 fun s _ => s.2.2
    · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
        ← not_nonempty_iff_eq_empty]
  -- So, we get a disjoint decomposition `s = s ∩ u ∪ s ∩ v` of clopen sets. The intersection of all
  -- clopen neighbourhoods will then lie in whichever of u or v x lies in and hence will be a subset
  -- of either a or b.
  · have H1 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv
    rw [union_comm] at H
    have H2 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu huv.symm
    by_cases hxu : x in u <;> [left; right]
    -- The x ∈ u case.
    · suffices ⋂ s : { s : Set X // IsClopen s ∧ x in s }, ↑s subseteq u
        from Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
      · apply Subset.trans _ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x in s } => s.1)
          ⟨s inter u, H1, mem_inter H.2.1 hxu⟩
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    · have h1 : x in v :=
        (hab.trans (union_subset_union hau hbv) (mem_iInter.2 fun i => i.2.2)).resolve_left hxu
      suffices ⋂ s : { s : Set X // IsClopen s ∧ x in s }, ↑s subseteq v
        from (huv.symm.mono this hau).left_le_of_le_sup_left hab
      · refine Subset.trans ?_ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x in s } => s.1)
          ⟨s inter v, H2, mem_inter H.2.1 h1⟩

/-- `ConnectedComponents X` is Hausdorff when `X` is Hausdorff and compact -/
@[stacks 0900 "The Stacks entry proves profiniteness."]
/--
Instance `ConnectedComponents.t2` / 实例 `ConnectedComponents.t2`

English:
instance ConnectedComponents.t2
  signature: [T2Space X] [CompactSpace X]
  body: by
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw 

中文:
实例 ConnectedComponents.t2
  签名: [T2Space X] [CompactSpace X]
  定义体: by
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw 
-/
instance ConnectedComponents.t2 [T2Space X] [CompactSpace X] : T2Space (ConnectedComponents X) := by
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connectedComponent_eq_iInter_isClopen b]; rw [disjoint_iff_inter_eq_empty] at h
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ : exists (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a inter U = ∅ ∧ connectedComponent b subseteq U ∧ (↑) ⁻¹' V = U := by
    have h :=
      (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
        _ (fun s : { s : Set X // IsClopen s ∧ b in s } => s.2.1.1) h
    obtain ⟨fin_a, ha⟩ := h
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : Set X := ⋂ (i : { s // IsClopen s ∧ b in s }) (_ : i in fin_a), i
    have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
    exact ⟨U, (↑) '' U, hU, ha, subset_iInter₂ fun s _ => s.2.1.connectedComponent_subset s.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connectedComponent, h⟩
