/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Filter.Bases.Finite

/-!
# (Co)product of a family of filters

In this file we prove some basic properties of two filters on `Π i, α i`.

* `Filter.pi (f : Π i, Filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, Filter.Tendsto (Function.eval i) (Filter.pi f) (f i)`. It is defined as
  `Π i, Filter.comap (Function.eval i) (f i)`. This is a generalization of binary products to
  indexed products.

* `Filter.coprodᵢ (f : Π i, Filter (α i))`: a generalization of `Filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/

@[expose] public section


open Set Function Filter

namespace Filter

variable {ι : Type*} {α : ι -> Type*} {f f₁ f₂ : (i : ι) -> Filter (α i)} {s : (i : ι) -> Set (α i)}
  {p : forall i, α i -> Prop}

section Pi

/--
theorem `tendsto_eval_pi` / 定理 `tendsto_eval_pi`

English:
theorem tendsto_eval_pi
  given: (f : forall i, Filter (α i)) (i : ι)
  statement: Tendsto (eval i) (pi f) (f i)
  proof: tendsto_iInf' i tendsto_comap

中文:
定理 tendsto_eval_pi
  条件: (f : 对任意 i, Filter (α i)) (i : ι)
  结论: Tendsto (eval i) (pi f) (f i)
  证明: tendsto_iInf' i tendsto_comap

Depends on / 依赖: tendsto_comap, tendsto_iInf
-/
theorem tendsto_eval_pi (f : forall i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap

/--
theorem `tendsto_pi` / 定理 `tendsto_pi`

English:
theorem tendsto_pi
  given: {β : Type*} {m : β -> forall i, α i} {l : Filter β}
  proof: by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

中文:
定理 tendsto_pi
  条件: {β : 类型} {m : β -> 对任意 i, α i} {l : Filter β}
  证明: by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

Depends on / 依赖: tendsto_comap_iff, tendsto_iInf
-/
theorem tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

/-- If a function tends to a product `Filter.pi f` of filters, then its `i`-th component tends to
`f i`. See also `Filter.Tendsto.apply_nhds` for the special case of converging to a point in a
product of topological spaces. -/
alias ⟨Tendsto.apply, _⟩ := tendsto_pi

/--
theorem `le_pi` / 定理 `le_pi`

English:
theorem le_pi
  given: {g : Filter (forall i, α i)}
  statement: g <= pi f ↔ forall i, Tendsto (eval i) g (f i)
  proof: tendsto_pi

@[gcongr, mono]

中文:
定理 le_pi
  条件: {g : Filter (对任意 i, α i)}
  结论: g <= pi f ↔ 对任意 i, Tendsto (eval i) g (f i)
  证明: tendsto_pi

@[gcongr, mono]

Depends on / 依赖: tendsto_pi
-/
theorem le_pi {g : Filter (forall i, α i)} : g <= pi f ↔ forall i, Tendsto (eval i) g (f i) :=
  tendsto_pi

@[gcongr, mono]
/--
theorem `pi_mono` / 定理 `pi_mono`

English:
theorem pi_mono
  given: (h : forall i, f₁ i <= f₂ i)
  statement: pi f₁ <= pi f₂
  proof: iInf_mono fun i => comap_mono h i

中文:
定理 pi_mono
  条件: (h : 对任意 i, f₁ i <= f₂ i)
  结论: pi f₁ <= pi f₂
  证明: iInf_mono fun i => comap_mono h i

Depends on / 依赖: comap_mono, iInf_mono
-/
theorem pi_mono (h : forall i, f₁ i <= f₂ i) : pi f₁ <= pi f₂ :=
iInf_mono fun i => comap_mono h i

/--
theorem `mem_pi_of_mem` / 定理 `mem_pi_of_mem`

English:
theorem mem_pi_of_mem
  given: (i : ι) {s : Set (α i)} (hs : s in f i)
  statement: eval i ⁻¹' s in pi f
  proof: mem_iInf_of_mem i preimage_mem_comap hs

中文:
定理 mem_pi_of_mem
  条件: (i : ι) {s : Set (α i)} (hs : s in f i)
  结论: eval i ⁻¹' s in pi f
  证明: mem_iInf_of_mem i preimage_mem_comap hs

Depends on / 依赖: mem_iInf_of_mem, preimage_mem_comap
-/
theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s in f i) : eval i ⁻¹' s in pi f :=
mem_iInf_of_mem i preimage_mem_comap hs

/--
theorem `pi_mem_pi` / 定理 `pi_mem_pi`

English:
theorem pi_mem_pi
  given: {I : Set ι} (hI : I.Finite) (h : forall i in I, s i in f i)
  statement: I.pi s in pi f
  proof: by
  rw [pi_def]; rw [biInter_eq_iInter]
  refine mem_iInf_of_iInter hI (fun i => ?_) Subset.rfl
  exact preimage_mem_comap (h i i.2)

中文:
定理 pi_mem_pi
  条件: {I : Set ι} (hI : I.Finite) (h : 对任意 i in I, s i in f i)
  结论: I.pi s in pi f
  证明: by
  rw [pi_def]; rw [biInter_eq_iInter]
  refine mem_iInf_of_iInter hI (fun i => ?_) Subset.rfl
  exact preimage_mem_comap (h i i.2)

Depends on / 依赖: AlgHomClass, Subset, Subset.rfl, biInter_eq_iInter, mem_iInf_of_iInter, pi_def, preimage_mem_comap, toAlgHomClass
-/
theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : forall i in I, s i in f i) : I.pi s in pi f := by
  rw [pi_def]; rw [biInter_eq_iInter]
  refine mem_iInf_of_iInter hI (fun i => ?_) Subset.rfl
  exact preimage_mem_comap (h i i.2)

/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: {s : Set (forall i, α i)}
  proof: by
  constructor
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts

中文:
定理 mem_pi
  条件: {s : Set (对任意 i, α i)}
  证明: by
  constructor
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts

Depends on / 依赖: mem_comap, mem_iInf, mem_of_superset, pi_def, pi_mem_pi
-/
theorem mem_pi {s : Set (forall i, α i)} :
    s in pi f ↔ exists I : Set ι, I.Finite ∧ exists t : forall i, Set (α i), (forall i, t i in f i) ∧ I.pi t subseteq s := by
  constructor
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts

/--
theorem `mem_pi'` / 定理 `mem_pi'`

English:
theorem mem_pi'
  given: {s : Set (forall i, α i)}
  proof: mem_pi.trans exists_finite_iff_finset

中文:
定理 mem_pi'
  条件: {s : Set (对任意 i, α i)}
  证明: mem_pi.trans exists_finite_iff_finset

Depends on / 依赖: exists_finite_iff_finset, mem_pi, mem_pi.trans
-/
theorem mem_pi' {s : Set (forall i, α i)} :
    s in pi f ↔ exists I : Finset ι, exists t : forall i, Set (α i), (forall i, t i in f i) ∧ Set.pi (↑I) t subseteq s :=
  mem_pi.trans exists_finite_iff_finset

/--
theorem `mem_of_pi_mem_pi` / 定理 `mem_of_pi_mem_pi`

English:
theorem mem_of_pi_mem_pi
  given: [forall i, NeBot (f i)] {I : Set ι} (h : I.pi s in pi f) {i : ι} (hi : i in I)
  proof: by
  classical
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  refine mem_of_superset (htf i) fun x hx => ?_
  have : forall i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg using this
  have : update g i x in I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> s

中文:
定理 mem_of_pi_mem_pi
  条件: [对任意 i, NeBot (f i)] {I : Set ι} (h : I.pi s in pi f) {i : ι} (hi : i in I)
  证明: by
  classical
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  refine mem_of_superset (htf i) fun x hx => ?_
  have : forall i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg using this
  have : update g i x in I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> s

Depends on / 依赖: Nonempty, classical, eq_or_ne, mem_of_superset, mem_pi, nonempty_of_mem, update
-/
theorem mem_of_pi_mem_pi [forall i, NeBot (f i)] {I : Set ι} (h : I.pi s in pi f) {i : ι} (hi : i in I) :
    s i in f i := by
  classical
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  refine mem_of_superset (htf i) fun x hx => ?_
  have : forall i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg using this
  have : update g i x in I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi

@[simp]
/--
theorem `pi_mem_pi_iff` / 定理 `pi_mem_pi_iff`

English:
theorem pi_mem_pi_iff
  given: [forall i, NeBot (f i)] {I : Set ι} (hI : I.Finite)
  proof: ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

中文:
定理 pi_mem_pi_iff
  条件: [对任意 i, NeBot (f i)] {I : Set ι} (hI : I.Finite)
  证明: ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

Depends on / 依赖: mem_of_pi_mem_pi, pi_mem_pi
-/
theorem pi_mem_pi_iff [forall i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s in pi f ↔ forall i in I, s i in f i :=
  ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

/--
theorem `Eventually.eval_pi` / 定理 `Eventually.eval_pi`

English:
theorem Eventually.eval_pi
  given: {i : ι} (hf : forallᶠ x : α i in f i, p i x)
  proof: (tendsto_eval_pi _ _).eventually hf

中文:
定理 Eventually.eval_pi
  条件: {i : ι} (hf : 对任意ᶠ x : α i in f i, p i x)
  证明: (tendsto_eval_pi _ _).eventually hf

Depends on / 依赖: eventually, tendsto_eval_pi
-/
theorem Eventually.eval_pi {i : ι} (hf : forallᶠ x : α i in f i, p i x) :
    forallᶠ x : forall i : ι, α i in pi f, p i (x i) := (tendsto_eval_pi _ _).eventually hf

/--
theorem `eventually_pi` / 定理 `eventually_pi`

English:
theorem eventually_pi
  given: [Finite ι] (hf : forall i, forallᶠ x in f i, p i x)
  proof: eventually_all.2 fun _i => (hf _).eval_pi

中文:
定理 eventually_pi
  条件: [Finite ι] (hf : 对任意 i, 对任意ᶠ x in f i, p i x)
  证明: eventually_all.2 fun _i => (hf _).eval_pi

Depends on / 依赖: eval_pi, eventually_all
-/
theorem eventually_pi [Finite ι] (hf : forall i, forallᶠ x in f i, p i x) :
    forallᶠ x : forall i, α i in pi f, forall i, p i (x i) := eventually_all.2 fun _i => (hf _).eval_pi

/--
theorem `hasBasis_pi` / 定理 `hasBasis_pi`

English:
theorem hasBasis_pi
  statement: {ι' : ι -> Type*} {s : forall i, ι' i -> Set (α i)} {p : forall i, ι' i -> Prop}
  proof: by
  simpa [Set.pi_def] using! HasBasis.iInf' fun i => (h i).comap (eval i : (forall j, α j) -> α i)

中文:
定理 hasBasis_pi
  结论: {ι' : ι -> 类型} {s : 对任意 i, ι' i -> Set (α i)} {p : 对任意 i, ι' i -> 命题}
  证明: by
  simpa [Set.pi_def] using! HasBasis.iInf' fun i => (h i).comap (eval i : (forall j, α j) -> α i)

Depends on / 依赖: HasBasis, HasBasis.iInf, Set.pi_def, pi_def
-/
theorem hasBasis_pi {ι' : ι -> Type*} {s : forall i, ι' i -> Set (α i)} {p : forall i, ι' i -> Prop}
    (h : forall i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × forall i, ι' i => If.1.Finite ∧ forall i in If.1, p i (If.2 i))
fun If : Set ι × forall i, ι' i => If.1.pi fun i => s i If.2 i := by
  simpa [Set.pi_def] using! HasBasis.iInf' fun i => (h i).comap (eval i : (forall j, α j) -> α i)

/--
theorem `hasBasis_pi_same_index` / 定理 `hasBasis_pi_same_index`

English:
theorem hasBasis_pi_same_index
  statement: {κ : Type*} {p : κ -> Prop} {s : Π i : ι, κ -> Set (α i)}
  proof: by
.to_hasBasis ?_ ?_ refine hasBasis_pi h
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    rcases h_dir I k hI hk with ⟨k₀, hk₀, hk₀'⟩
    exact ⟨⟨I, k₀⟩, ⟨hI, hk₀⟩, Set.pi_mono hk₀'⟩
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    exact ⟨⟨I, fun _ => k⟩, ⟨hI, fun _ _ => hk⟩, subset_rfl⟩

中文:
定理 hasBasis_pi_same_index
  结论: {κ : 类型} {p : κ -> 命题} {s : Π i : ι, κ -> Set (α i)}
  证明: by
.to_hasBasis ?_ ?_ refine hasBasis_pi h
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    rcases h_dir I k hI hk with ⟨k₀, hk₀, hk₀'⟩
    exact ⟨⟨I, k₀⟩, ⟨hI, hk₀⟩, Set.pi_mono hk₀'⟩
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    exact ⟨⟨I, fun _ => k⟩, ⟨hI, fun _ _ => hk⟩, subset_rfl⟩

Depends on / 依赖: Set.pi_mono, h_dir, hasBasis_pi, pi_mono, subset_rfl, to_hasBasis
-/
theorem hasBasis_pi_same_index {κ : Type*} {p : κ -> Prop} {s : Π i : ι, κ -> Set (α i)}
    (h : forall i : ι, (f i).HasBasis p (s i))
    (h_dir : forall I : Set ι, forall k : ι -> κ, I.Finite -> (forall i in I, p (k i)) ->
      exists k₀, p k₀ ∧ forall i in I, s i k₀ subseteq s i (k i)) :
    (pi f).HasBasis (fun Ik : Set ι × κ => Ik.1.Finite ∧ p Ik.2)
      (fun Ik => Ik.1.pi (fun i => s i Ik.2)) := by
.to_hasBasis ?_ ?_ refine hasBasis_pi h
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    rcases h_dir I k hI hk with ⟨k₀, hk₀, hk₀'⟩
    exact ⟨⟨I, k₀⟩, ⟨hI, hk₀⟩, Set.pi_mono hk₀'⟩
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    exact ⟨⟨I, fun _ => k⟩, ⟨hI, fun _ _ => hk⟩, subset_rfl⟩

/--
theorem `HasBasis.pi_self` / 定理 `HasBasis.pi_self`

English:
theorem HasBasis.pi_self
  statement: {α : Type*} {κ : Type*} {f : Filter α} {p : κ -> Prop} {s : κ -> Set α}
  proof: by
  refine hasBasis_pi_same_index (fun _ => h) (fun I k hI hk => ?_)
  rcases h.mem_iff.mp (biInter_mem hI |>.mpr fun i hi => h.mem_of_mem (hk i hi))
    with ⟨k₀, hk₀, hk₀'⟩
  exact ⟨k₀, hk₀, fun i hi => hk₀'.trans (biInter_subset_of_mem hi)⟩

中文:
定理 HasBasis.pi_self
  结论: {α : 类型} {κ : 类型} {f : Filter α} {p : κ -> 命题} {s : κ -> Set α}
  证明: by
  refine hasBasis_pi_same_index (fun _ => h) (fun I k hI hk => ?_)
  rcases h.mem_iff.mp (biInter_mem hI |>.mpr fun i hi => h.mem_of_mem (hk i hi))
    with ⟨k₀, hk₀, hk₀'⟩
  exact ⟨k₀, hk₀, fun i hi => hk₀'.trans (biInter_subset_of_mem hi)⟩

Depends on / 依赖: biInter_mem, biInter_subset_of_mem, h.mem_iff.mp, h.mem_of_mem, hasBasis_pi_same_index, mem_iff, mem_of_mem
-/
theorem HasBasis.pi_self {α : Type*} {κ : Type*} {f : Filter α} {p : κ -> Prop} {s : κ -> Set α}
    (h : f.HasBasis p s) :
    (pi fun _ => f).HasBasis (fun Ik : Set ι × κ => Ik.1.Finite ∧ p Ik.2)
      (fun Ik => Ik.1.pi (fun _ => s Ik.2)) := by
  refine hasBasis_pi_same_index (fun _ => h) (fun I k hI hk => ?_)
  rcases h.mem_iff.mp (biInter_mem hI |>.mpr fun i hi => h.mem_of_mem (hk i hi))
    with ⟨k₀, hk₀, hk₀'⟩
  exact ⟨k₀, hk₀, fun i hi => hk₀'.trans (biInter_subset_of_mem hi)⟩

/--
theorem `le_pi_principal` / 定理 `le_pi_principal`

English:
theorem le_pi_principal
  given: (s : (i : ι) -> Set (α i))
  proof: le_pi.2 fun i => tendsto_principal_principal.2 fun _f hf => hf i trivial

中文:
定理 le_pi_principal
  条件: (s : (i : ι) -> Set (α i))
  证明: le_pi.2 fun i => tendsto_principal_principal.2 fun _f hf => hf i trivial

Depends on / 依赖: le_pi, tendsto_principal_principal
-/
theorem le_pi_principal (s : (i : ι) -> Set (α i)) :
    𝓟 (univ.pi s) <= pi fun i => 𝓟 (s i) :=
  le_pi.2 fun i => tendsto_principal_principal.2 fun _f hf => hf i trivial

/-- The indexed product of finitely many principal filters
is the principal filter corresponding to the cylinder `Set.univ.pi s`.

If the index type is infinite, then `mem_pi_principal` and `hasBasis_pi_principal` may be useful. -/
@[simp]
/--
theorem `pi_principal` / 定理 `pi_principal`

English:
theorem pi_principal
  given: [Finite ι] (s : (i : ι) -> Set (α i))
  proof: by
  simp [Filter.pi, Set.pi_def]

中文:
定理 pi_principal
  条件: [Finite ι] (s : (i : ι) -> Set (α i))
  证明: by
  simp [Filter.pi, Set.pi_def]

Depends on / 依赖: Filter, Filter.pi, Set.pi_def, pi_def
-/
theorem pi_principal [Finite ι] (s : (i : ι) -> Set (α i)) :
    pi (fun i => 𝓟 (s i)) = 𝓟 (univ.pi s) := by
  simp [Filter.pi, Set.pi_def]

/--
theorem `mem_pi_principal` / 定理 `mem_pi_principal`

English:
theorem mem_pi_principal
  given: {t : Set ((i : ι) -> α i)}
  proof: (hasBasis_pi (fun i => hasBasis_principal _)).mem_iff.trans by simp

中文:
定理 mem_pi_principal
  条件: {t : Set ((i : ι) -> α i)}
  证明: (hasBasis_pi (fun i => hasBasis_principal _)).mem_iff.trans by simp

Depends on / 依赖: hasBasis_pi, hasBasis_principal, mem_iff, mem_iff.trans
-/
theorem mem_pi_principal {t : Set ((i : ι) -> α i)} :
    t in pi (fun i => 𝓟 (s i)) ↔ exists I : Set ι, I.Finite ∧ I.pi s subseteq t :=
(hasBasis_pi (fun i => hasBasis_principal _)).mem_iff.trans by simp

/--
theorem `hasBasis_pi_principal` / 定理 `hasBasis_pi_principal`

English:
theorem hasBasis_pi_principal
  given: (s : (i : ι) -> Set (α i))
  proof: ⟨fun _ => mem_pi_principal⟩

中文:
定理 hasBasis_pi_principal
  条件: (s : (i : ι) -> Set (α i))
  证明: ⟨fun _ => mem_pi_principal⟩

Depends on / 依赖: mem_pi_principal
-/
theorem hasBasis_pi_principal (s : (i : ι) -> Set (α i)) :
    HasBasis (pi fun i => 𝓟 (s i)) Set.Finite (Set.pi · s) :=
  ⟨fun _ => mem_pi_principal⟩

/-- The indexed product of finitely many pure filters `pure (f i)` is the pure filter `pure f`.

If the index type is infinite, then `mem_pi_pure` and `hasBasis_pi_pure` below may be useful. -/
@[simp]
/--
theorem `pi_pure` / 定理 `pi_pure`

English:
theorem pi_pure
  given: [Finite ι] (f : (i : ι) -> α i)
  statement: pi (pure <| f ·) = pure f
  proof: by
  simp only [← principal_singleton, pi_principal, univ_pi_singleton]

中文:
定理 pi_pure
  条件: [Finite ι] (f : (i : ι) -> α i)
  结论: pi (pure <| f ·) = pure f
  证明: by
  simp only [← principal_singleton, pi_principal, univ_pi_singleton]

Depends on / 依赖: pi_principal, principal_singleton, univ_pi_singleton
-/
theorem pi_pure [Finite ι] (f : (i : ι) -> α i) : pi (pure <| f ·) = pure f := by
  simp only [← principal_singleton, pi_principal, univ_pi_singleton]

/--
theorem `mem_pi_pure` / 定理 `mem_pi_pure`

English:
theorem mem_pi_pure
  given: {f : (i : ι) -> α i} {s : Set ((i : ι) -> α i)}
  proof: by
  simp only [← principal_singleton, mem_pi_principal]
  simp [subset_def]

中文:
定理 mem_pi_pure
  条件: {f : (i : ι) -> α i} {s : Set ((i : ι) -> α i)}
  证明: by
  simp only [← principal_singleton, mem_pi_principal]
  simp [subset_def]

Depends on / 依赖: mem_pi_principal, principal_singleton, subset_def
-/
theorem mem_pi_pure {f : (i : ι) -> α i} {s : Set ((i : ι) -> α i)} :
    s in pi (fun i => pure (f i)) ↔ exists I : Set ι, I.Finite ∧ forall g, (forall i in I, g i = f i) -> g in s := by
  simp only [← principal_singleton, mem_pi_principal]
  simp [subset_def]

/--
theorem `hasBasis_pi_pure` / 定理 `hasBasis_pi_pure`

English:
theorem hasBasis_pi_pure
  given: (f : (i : ι) -> α i)
  proof: ⟨fun _ => mem_pi_pure⟩

@[simp]

中文:
定理 hasBasis_pi_pure
  条件: (f : (i : ι) -> α i)
  证明: ⟨fun _ => mem_pi_pure⟩

@[simp]

Depends on / 依赖: mem_pi_pure
-/
theorem hasBasis_pi_pure (f : (i : ι) -> α i) :
    HasBasis (pi fun i => pure (f i)) Set.Finite (fun I => {g | forall i in I, g i = f i}) :=
  ⟨fun _ => mem_pi_pure⟩

@[simp]
/--
theorem `pi_inf_principal_univ_pi_eq_bot` / 定理 `pi_inf_principal_univ_pi_eq_bot`

English:
theorem pi_inf_principal_univ_pi_eq_bot
  proof: by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : forall i, existsᶠ x in f i, x in s i) I - t htf hts
    have : forall i, (s i inter t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt using this
    exact hts (fun i _

中文:
定理 pi_inf_principal_univ_pi_eq_bot
  证明: by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : forall i, existsᶠ x in f i, x in s i) I - t htf hts
    have : forall i, (s i inter t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt using this
    exact hts (fun i _

Depends on / 依赖: Nonempty, and_eventually, contrapose, filter_upwards, inf_principal_eq_bot, mem_pi, mem_pi_of_mem, mem_univ_pi
-/
theorem pi_inf_principal_univ_pi_eq_bot :
    pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ exists i, f i ⊓ 𝓟 (s i) = ⊥ := by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : forall i, existsᶠ x in f i, x in s i) I - t htf hts
    have : forall i, (s i inter t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt using this
    exact hts (fun i _ => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi] with x using mt fun h => h i trivial

@[simp]
/--
theorem `pi_inf_principal_pi_eq_bot` / 定理 `pi_inf_principal_pi_eq_bot`

English:
theorem pi_inf_principal_pi_eq_bot
  given: [forall i, NeBot (f i)] {I : Set ι}
  proof: by
  classical
  rw [← univ_pi_piecewise_univ I]; rw [pi_inf_principal_univ_pi_eq_bot]
  refine exists_congr fun i => ?_
  by_cases hi : i in I <;> simp [hi, NeBot.ne']

@[simp]

中文:
定理 pi_inf_principal_pi_eq_bot
  条件: [对任意 i, NeBot (f i)] {I : Set ι}
  证明: by
  classical
  rw [← univ_pi_piecewise_univ I]; rw [pi_inf_principal_univ_pi_eq_bot]
  refine exists_congr fun i => ?_
  by_cases hi : i in I <;> simp [hi, NeBot.ne']

@[simp]

Depends on / 依赖: NeBot.ne, classical, exists_congr, pi_inf_principal_univ_pi_eq_bot, univ_pi_piecewise_univ
-/
theorem pi_inf_principal_pi_eq_bot [forall i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ exists i in I, f i ⊓ 𝓟 (s i) = ⊥ := by
  classical
  rw [← univ_pi_piecewise_univ I]; rw [pi_inf_principal_univ_pi_eq_bot]
  refine exists_congr fun i => ?_
  by_cases hi : i in I <;> simp [hi, NeBot.ne']

@[simp]
/--
theorem `pi_inf_principal_univ_pi_neBot` / 定理 `pi_inf_principal_univ_pi_neBot`

English:
theorem pi_inf_principal_univ_pi_neBot
  proof: by simp [neBot_iff]

@[simp]

中文:
定理 pi_inf_principal_univ_pi_neBot
  证明: by simp [neBot_iff]

@[simp]

Depends on / 依赖: neBot_iff
-/
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ forall i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]

@[simp]
/--
theorem `pi_inf_principal_pi_neBot` / 定理 `pi_inf_principal_pi_neBot`

English:
theorem pi_inf_principal_pi_neBot
  given: [forall i, NeBot (f i)] {I : Set ι}
  proof: by simp [neBot_iff]

中文:
定理 pi_inf_principal_pi_neBot
  条件: [对任意 i, NeBot (f i)] {I : Set ι}
  证明: by simp [neBot_iff]

Depends on / 依赖: neBot_iff
-/
theorem pi_inf_principal_pi_neBot [forall i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ forall i in I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]

/--
Instance `PiInfPrincipalPi.neBot` / 实例 `PiInfPrincipalPi.neBot`

English:
instance PiInfPrincipalPi.neBot
  signature: [h : forall i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι}
  body: (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono
inf_le_inf_left _ principal_mono.2 fun _ hx i _ => hx i trivial

@[simp]

中文:
实例 PiInfPrincipalPi.neBot
  签名: [h : 对任意 i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι}
  定义体: (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono
inf_le_inf_left _ principal_mono.2 fun _ hx i _ => hx i trivial

@[simp]

Depends on / 依赖: inf_le_inf_left, pi_inf_principal_univ_pi_neBot, principal_mono
-/
instance PiInfPrincipalPi.neBot [h : forall i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
(pi_inf_principal_univ_pi_neBot.2 ‹_›).mono
inf_le_inf_left _ principal_mono.2 fun _ hx i _ => hx i trivial

@[simp]
/--
theorem `pi_eq_bot` / 定理 `pi_eq_bot`

English:
theorem pi_eq_bot
  statement: pi f = ⊥ ↔ exists i, f i = ⊥
  proof: by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]

中文:
定理 pi_eq_bot
  结论: pi f = ⊥ ↔ 存在 i, f i = ⊥
  证明: by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]

Depends on / 依赖: pi_inf_principal_univ_pi_eq_bot
-/
theorem pi_eq_bot : pi f = ⊥ ↔ exists i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]
/--
theorem `pi_neBot` / 定理 `pi_neBot`

English:
theorem pi_neBot
  statement: NeBot (pi f) ↔ forall i, NeBot (f i)
  proof: by simp [neBot_iff]

中文:
定理 pi_neBot
  结论: NeBot (pi f) ↔ 对任意 i, NeBot (f i)
  证明: by simp [neBot_iff]

Depends on / 依赖: neBot_iff
-/
theorem pi_neBot : NeBot (pi f) ↔ forall i, NeBot (f i) := by simp [neBot_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NeBot (f i)] : NeBot (pi f)
  body: pi_neBot.2 ‹_›

@[simp]

中文:
实例 [forall
  签名: i, NeBot (f i)] : NeBot (pi f)
  定义体: pi_neBot.2 ‹_›

@[simp]

Depends on / 依赖: pi_neBot
-/
instance [forall i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

@[simp]
/--
theorem `map_eval_pi` / 定理 `map_eval_pi`

English:
theorem map_eval_pi
  given: (f : forall i, Filter (α i)) [forall i, NeBot (f i)] (i : ι)
  proof: by
  refine le_antisymm (tendsto_eval_pi f i) fun s hs => ?_
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine mem_of_superset (htf i) ((subset_eval_image_pi ?_ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)

@[simp]

中文:
定理 map_eval_pi
  条件: (f : 对任意 i, Filter (α i)) [对任意 i, NeBot (f i)] (i : ι)
  证明: by
  refine le_antisymm (tendsto_eval_pi f i) fun s hs => ?_
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine mem_of_superset (htf i) ((subset_eval_image_pi ?_ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)

@[simp]

Depends on / 依赖: image_subset_iff, le_antisymm, mem_map, mem_of_superset, mem_pi, nonempty_of_mem, pi_mem_pi, subset_eval_image_pi, tendsto_eval_pi
-/
theorem map_eval_pi (f : forall i, Filter (α i)) [forall i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i := by
  refine le_antisymm (tendsto_eval_pi f i) fun s hs => ?_
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine mem_of_superset (htf i) ((subset_eval_image_pi ?_ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)

@[simp]
/--
theorem `pi_le_pi` / 定理 `pi_le_pi`

English:
theorem pi_le_pi
  given: [forall i, NeBot (f₁ i)]
  statement: pi f₁ <= pi f₂ ↔ forall i, f₁ i <= f₂ i
  proof: ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩

@[simp]

中文:
定理 pi_le_pi
  条件: [对任意 i, NeBot (f₁ i)]
  结论: pi f₁ <= pi f₂ ↔ 对任意 i, f₁ i <= f₂ i
  证明: ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩

@[simp]

Depends on / 依赖: map_eval_pi, mono_left, pi_mono, tendsto_eval_pi
-/
theorem pi_le_pi [forall i, NeBot (f₁ i)] : pi f₁ <= pi f₂ ↔ forall i, f₁ i <= f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩

@[simp]
/--
theorem `pi_inj` / 定理 `pi_inj`

English:
theorem pi_inj
  given: [forall i, NeBot (f₁ i)]
  statement: pi f₁ = pi f₂ ↔ f₁ = f₂
  proof: by
  refine ⟨fun h => ?_, congr_arg pi⟩
  have hle : f₁ <= f₂ := pi_le_pi.1 h.le
  have : forall i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)

中文:
定理 pi_inj
  条件: [对任意 i, NeBot (f₁ i)]
  结论: pi f₁ = pi f₂ ↔ f₁ = f₂
  证明: by
  refine ⟨fun h => ?_, congr_arg pi⟩
  have hle : f₁ <= f₂ := pi_le_pi.1 h.le
  have : forall i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)

Depends on / 依赖: antisymm, congr_arg, h.ge, h.le, hle.antisymm, neBot_of_le, pi_le_pi
-/
theorem pi_inj [forall i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ := by
  refine ⟨fun h => ?_, congr_arg pi⟩
  have hle : f₁ <= f₂ := pi_le_pi.1 h.le
  have : forall i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)

/--
theorem `tendsto_piMap_pi` / 定理 `tendsto_piMap_pi`

English:
theorem tendsto_piMap_pi
  statement: {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i, Filter (α i)}
  proof: tendsto_pi.2 fun i => (h i).comp (tendsto_eval_pi _ _)

中文:
定理 tendsto_piMap_pi
  结论: {β : ι -> 类型} {f : 对任意 i, α i -> β i} {l : 对任意 i, Filter (α i)}
  证明: tendsto_pi.2 fun i => (h i).comp (tendsto_eval_pi _ _)

Depends on / 依赖: tendsto_eval_pi, tendsto_pi
-/
theorem tendsto_piMap_pi {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i, Filter (α i)}
    {l' : forall i, Filter (β i)} (h : forall i, Tendsto (f i) (l i) (l' i)) :
    Tendsto (Pi.map f) (pi l) (pi l') :=
  tendsto_pi.2 fun i => (h i).comp (tendsto_eval_pi _ _)

/--
theorem `pi_comap` / 定理 `pi_comap`

English:
theorem pi_comap
  given: {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i, Filter (β i)}
  proof: by
  simp [Filter.pi, Filter.comap_comap, Function.comp_def]

中文:
定理 pi_comap
  条件: {β : ι -> 类型} {f : 对任意 i, α i -> β i} {l : 对任意 i, Filter (β i)}
  证明: by
  simp [Filter.pi, Filter.comap_comap, Function.comp_def]

Depends on / 依赖: Filter, Filter.comap_comap, Filter.pi, Function, Function.comp_def, comap_comap, comp_def
-/
theorem pi_comap {β : ι -> Type*} {f : forall i, α i -> β i} {l : forall i, Filter (β i)} :
    pi (fun i => comap (f i) (l i)) = comap (Pi.map f) (pi l) := by
  simp [Filter.pi, Filter.comap_comap, Function.comp_def]

end Pi

/-! ### `n`-ary coproducts of filters -/

section CoprodCat

-- for "Coprod"

/--
Definition of `coprodᵢ` / `coprodᵢ` 的定义

English:
definition coprodᵢ
  signature: (f : forall i, Filter (α i))
  body: ⨆ i : ι, comap (eval i) (f i)

中文:
定义 coprodᵢ
  签名: (f : 对任意 i, Filter (α i))
  定义体: ⨆ i : ι, comap (eval i) (f i)
-/
protected def coprodᵢ (f : forall i, Filter (α i)) : Filter (forall i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)

/--
theorem `mem_coprodᵢ_iff` / 定理 `mem_coprodᵢ_iff`

English:
theorem mem_coprodᵢ_iff
  given: {s : Set (forall i, α i)}
  proof: by simp [Filter.coprodᵢ]

中文:
定理 mem_coprodᵢ_iff
  条件: {s : Set (对任意 i, α i)}
  证明: by simp [Filter.coprodᵢ]

Depends on / 依赖: Filter, Filter.coprod
-/
theorem mem_coprodᵢ_iff {s : Set (forall i, α i)} :
    s in Filter.coprodᵢ f ↔ forall i : ι, exists t₁ in f i, eval i ⁻¹' t₁ subseteq s := by simp [Filter.coprodᵢ]

/--
theorem `compl_mem_coprodᵢ` / 定理 `compl_mem_coprodᵢ`

English:
theorem compl_mem_coprodᵢ
  given: {s : Set (forall i, α i)}
  proof: by
  simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]

中文:
定理 compl_mem_coprodᵢ
  条件: {s : Set (对任意 i, α i)}
  证明: by
  simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]

Depends on / 依赖: Filter, Filter.coprod, compl_mem_comap, mem_iSup
-/
theorem compl_mem_coprodᵢ {s : Set (forall i, α i)} :
    sᶜ in Filter.coprodᵢ f ↔ forall i, (eval i '' s)ᶜ in f i := by
  simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]

/--
theorem `coprodᵢ_neBot_iff'` / 定理 `coprodᵢ_neBot_iff'`

English:
theorem coprodᵢ_neBot_iff'
  proof: by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']

@[simp]

中文:
定理 coprodᵢ_neBot_iff'
  证明: by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']

@[simp]

Depends on / 依赖: Filter, Filter.coprod, comap_eval_neBot_iff, exists_and_left, iSup_neBot
-/
theorem coprodᵢ_neBot_iff' :
    NeBot (Filter.coprodᵢ f) ↔ (forall i, Nonempty (α i)) ∧ exists d, NeBot (f d) := by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']

@[simp]
/--
theorem `coprodᵢ_neBot_iff` / 定理 `coprodᵢ_neBot_iff`

English:
theorem coprodᵢ_neBot_iff
  given: [forall i, Nonempty (α i)]
  statement: NeBot (Filter.coprodᵢ f) ↔ exists d, NeBot (f d)
  proof: by
  simp [coprodᵢ_neBot_iff', *]

中文:
定理 coprodᵢ_neBot_iff
  条件: [对任意 i, Nonempty (α i)]
  结论: NeBot (Filter.coprodᵢ f) ↔ 存在 d, NeBot (f d)
  证明: by
  simp [coprodᵢ_neBot_iff', *]
-/
theorem coprodᵢ_neBot_iff [forall i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ exists d, NeBot (f d) := by
  simp [coprodᵢ_neBot_iff', *]

/--
theorem `coprodᵢ_eq_bot_iff'` / 定理 `coprodᵢ_eq_bot_iff'`

English:
theorem coprodᵢ_eq_bot_iff'
  statement: Filter.coprodᵢ f = ⊥ ↔ (exists i, IsEmpty (α i)) ∨ f = ⊥
  proof: by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using! coprodᵢ_neBot_iff'.not

@[simp]

中文:
定理 coprodᵢ_eq_bot_iff'
  结论: Filter.coprodᵢ f = ⊥ ↔ (存在 i, IsEmpty (α i)) ∨ f = ⊥
  证明: by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using! coprodᵢ_neBot_iff'.not

@[simp]

Depends on / 依赖: funext_iff, not_and_or, not_exists, not_forall, not_neBot, not_nonempty_iff
-/
theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (exists i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using! coprodᵢ_neBot_iff'.not

@[simp]
/--
theorem `coprodᵢ_eq_bot_iff` / 定理 `coprodᵢ_eq_bot_iff`

English:
theorem coprodᵢ_eq_bot_iff
  given: [forall i, Nonempty (α i)]
  statement: Filter.coprodᵢ f = ⊥ ↔ f = ⊥
  proof: by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not

中文:
定理 coprodᵢ_eq_bot_iff
  条件: [对任意 i, Nonempty (α i)]
  结论: Filter.coprodᵢ f = ⊥ ↔ f = ⊥
  证明: by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not

Depends on / 依赖: _neBot_iff.not, funext_iff
-/
theorem coprodᵢ_eq_bot_iff [forall i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not

/--
theorem `coprodᵢ_bot'` / 定理 `coprodᵢ_bot'`

English:
theorem coprodᵢ_bot'
  statement: Filter.coprodᵢ (⊥ : forall i, Filter (α i)) = ⊥
  proof: coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)

@[simp]

中文:
定理 coprodᵢ_bot'
  结论: Filter.coprodᵢ (⊥ : 对任意 i, Filter (α i)) = ⊥
  证明: coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)

@[simp]
-/
@[simp] theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : forall i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)

@[simp]
/--
theorem `coprodᵢ_bot` / 定理 `coprodᵢ_bot`

English:
theorem coprodᵢ_bot
  statement: Filter.coprodᵢ (fun _ => ⊥ : forall i, Filter (α i)) = ⊥
  proof: coprodᵢ_bot'

中文:
定理 coprodᵢ_bot
  结论: Filter.coprodᵢ (fun _ => ⊥ : 对任意 i, Filter (α i)) = ⊥
  证明: coprodᵢ_bot'
-/
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : forall i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'

/--
theorem `NeBot.coprodᵢ` / 定理 `NeBot.coprodᵢ`

English:
theorem NeBot.coprodᵢ
  given: [forall i, Nonempty (α i)] {i : ι} (h : NeBot (f i))
  statement: NeBot (Filter.coprodᵢ f)
  proof: coprodᵢ_neBot_iff.2 ⟨i, h⟩

@[instance]

中文:
定理 NeBot.coprodᵢ
  条件: [对任意 i, Nonempty (α i)] {i : ι} (h : NeBot (f i))
  结论: NeBot (Filter.coprodᵢ f)
  证明: coprodᵢ_neBot_iff.2 ⟨i, h⟩

@[instance]
-/
theorem NeBot.coprodᵢ [forall i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩

@[instance]
/--
theorem `coprodᵢ_neBot` / 定理 `coprodᵢ_neBot`

English:
theorem coprodᵢ_neBot
  statement: [forall i, Nonempty (α i)] [Nonempty ι] (f : forall i, Filter (α i))
  proof: (H (Classical.arbitrary ι)).coprodᵢ

@[gcongr, mono]

中文:
定理 coprodᵢ_neBot
  结论: [对任意 i, Nonempty (α i)] [Nonempty ι] (f : 对任意 i, Filter (α i))
  证明: (H (Classical.arbitrary ι)).coprodᵢ

@[gcongr, mono]

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
theorem coprodᵢ_neBot [forall i, Nonempty (α i)] [Nonempty ι] (f : forall i, Filter (α i))
    [H : forall i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ

@[gcongr, mono]
/--
theorem `coprodᵢ_mono` / 定理 `coprodᵢ_mono`

English:
theorem coprodᵢ_mono
  given: (hf : forall i, f₁ i <= f₂ i)
  statement: Filter.coprodᵢ f₁ <= Filter.coprodᵢ f₂
  proof: iSup_mono fun i => comap_mono (hf i)

中文:
定理 coprodᵢ_mono
  条件: (hf : 对任意 i, f₁ i <= f₂ i)
  结论: Filter.coprodᵢ f₁ <= Filter.coprodᵢ f₂
  证明: iSup_mono fun i => comap_mono (hf i)

Depends on / 依赖: comap_mono, iSup_mono
-/
theorem coprodᵢ_mono (hf : forall i, f₁ i <= f₂ i) : Filter.coprodᵢ f₁ <= Filter.coprodᵢ f₂ :=
  iSup_mono fun i => comap_mono (hf i)

variable {β : ι -> Type*} {m : forall i, α i -> β i}

/--
theorem `map_pi_map_coprodᵢ_le` / 定理 `map_pi_map_coprodᵢ_le`

English:
theorem map_pi_map_coprodᵢ_le
  proof: by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x in t }, H, fun x hx => hH hx⟩

中文:
定理 map_pi_map_coprodᵢ_le
  证明: by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x in t }, H, fun x hx => hH hx⟩

Depends on / 依赖: le_def, mem_map
-/
theorem map_pi_map_coprodᵢ_le :
    map (fun k : forall i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) <=
      Filter.coprodᵢ fun i => map (m i) (f i) := by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x in t }, H, fun x hx => hH hx⟩

/--
theorem `Tendsto.pi_map_coprodᵢ` / 定理 `Tendsto.pi_map_coprodᵢ`

English:
theorem Tendsto.pi_map_coprodᵢ
  given: {g : forall i, Filter (β i)} (h : forall i, Tendsto (m i) (f i) (g i))
  proof: map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)

中文:
定理 Tendsto.pi_map_coprodᵢ
  条件: {g : 对任意 i, Filter (β i)} (h : 对任意 i, Tendsto (m i) (f i) (g i))
  证明: map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)

Depends on / 依赖: _le.trans
-/
theorem Tendsto.pi_map_coprodᵢ {g : forall i, Filter (β i)} (h : forall i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : forall i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)

end CoprodCat

end Filter
