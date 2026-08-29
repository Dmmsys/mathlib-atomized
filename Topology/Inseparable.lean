/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury Kudryashov
-/
module

public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.Fibration
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Inseparable points in a topological space

In this file we prove basic properties of the following notions defined elsewhere.

* `Specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `Inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `InseparableSetoid X`: same relation, as a `Setoid`;

* `SeparationQuotient X`: the quotient of `X` by its `InseparableSetoid`.

We also prove various basic properties of the relation `Inseparable`.

## Notation

- `x ⤳ y`: notation for `Specializes x y`;
- `x ~ᵢ y` is used as a local notation for `Inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/

@[expose] public section


open Set Filter Function Topology

variable {X Y Z α ι : Type*} {A : ι -> Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [forall i, TopologicalSpace (A i)] {x y z : X} {s : Set X} {f g : X -> Y}

/-!
### `Specializes` relation
-/

/--
theorem `specializes_TFAE` / 定理 `specializes_TFAE`

English:
theorem specializes_TFAE
  given: (x y : X)
  proof: by
  tfae_have 1 -> 2 := (pure_le_nhds _).trans
  tfae_have 2 -> 3 := fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 -> 4 := fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 -> 5 := fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔

中文:
定理 specializes_TFAE
  条件: (x y : X)
  证明: by
  tfae_have 1 -> 2 := (pure_le_nhds _).trans
  tfae_have 2 -> 3 := fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 -> 4 := fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 -> 5 := fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔

Depends on / 依赖: closure_subset_iff, hsc.isOpen_compl, hso.mem_nhds, isClosed_closure, isClosed_closure.closure_subset_iff.trans, isOpen_compl, mem_closure_iff_clusterPt, mem_nhds, mem_singleton, nhds_basis_opens, of_not_not, principal_singleton, pure_le_nhds, singleton_subset_iff, subset_closure, tfae_have
-/
theorem specializes_TFAE (x y : X) :
    List.TFAE [x ⤳ y,
      pure x <= 𝓝 y,
      forall s : Set X, IsOpen s -> y in s -> x in s,
      forall s : Set X, IsClosed s -> x in s -> y in s,
      y in closure ({ x } : Set X),
      closure ({ y } : Set X) subseteq closure { x },
      ClusterPt y (pure x)] := by
  tfae_have 1 -> 2 := (pure_le_nhds _).trans
  tfae_have 2 -> 3 := fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 -> 4 := fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 -> 5 := fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5 := isClosed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7 := by
    rw [mem_closure_iff_clusterPt]; rw [principal_singleton]
  tfae_have 5 -> 1 := by
    refine fun h => (nhds_basis_opens _).ge_iff.2 ?_
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish

/--
theorem `specializes_iff_nhds` / 定理 `specializes_iff_nhds`

English:
theorem specializes_iff_nhds
  statement: x ⤳ y ↔ 𝓝 x <= 𝓝 y
  proof: Iff.rfl

中文:
定理 specializes_iff_nhds
  结论: x ⤳ y ↔ 𝓝 x <= 𝓝 y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x <= 𝓝 y :=
  Iff.rfl

/--
theorem `Specializes.not_disjoint` / 定理 `Specializes.not_disjoint`

English:
theorem Specializes.not_disjoint
  given: (h : x ⤳ y)
  statement: ¬Disjoint (𝓝 x) (𝓝 y)
  proof: fun hd =>
absurd (hd.mono_right h) by simp [NeBot.ne']

中文:
定理 Specializes.not_disjoint
  条件: (h : x ⤳ y)
  结论: ¬Disjoint (𝓝 x) (𝓝 y)
  证明: fun hd =>
absurd (hd.mono_right h) by simp [NeBot.ne']
-/
theorem Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoint (𝓝 x) (𝓝 y) := fun hd =>
absurd (hd.mono_right h) by simp [NeBot.ne']

/--
theorem `specializes_iff_pure` / 定理 `specializes_iff_pure`

English:
theorem specializes_iff_pure
  statement: x ⤳ y ↔ pure x <= 𝓝 y
  proof: (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure

中文:
定理 specializes_iff_pure
  结论: x ⤳ y ↔ pure x <= 𝓝 y
  证明: (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y :=
  (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure

/--
theorem `ker_nhds_eq_specializes` / 定理 `ker_nhds_eq_specializes`

English:
theorem ker_nhds_eq_specializes
  statement: (𝓝 x).ker = {y | y ⤳ x}
  proof: by
  ext; simp [specializes_iff_pure, le_def]

中文:
定理 ker_nhds_eq_specializes
  结论: (𝓝 x).ker = {y | y ⤳ x}
  证明: by
  ext; simp [specializes_iff_pure, le_def]

Depends on / 依赖: le_def, specializes_iff_pure
-/
theorem ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ x} := by
  ext; simp [specializes_iff_pure, le_def]

/--
theorem `specializes_iff_forall_open` / 定理 `specializes_iff_forall_open`

English:
theorem specializes_iff_forall_open
  statement: x ⤳ y ↔ forall s : Set X, IsOpen s -> y in s -> x in s
  proof: (specializes_TFAE x y).out 0 2

omit [TopologicalSpace X] in

中文:
定理 specializes_iff_forall_open
  结论: x ⤳ y ↔ 对任意 s : Set X, IsOpen s -> y in s -> x in s
  证明: (specializes_TFAE x y).out 0 2

omit [TopologicalSpace X] in

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_forall_open : x ⤳ y ↔ forall s : Set X, IsOpen s -> y in s -> x in s :=
  (specializes_TFAE x y).out 0 2

omit [TopologicalSpace X] in
/--
theorem `Tendsto.specializes` / 定理 `Tendsto.specializes`

English:
theorem Tendsto.specializes
  given: {l : Filter X} {y : Y} (h : Tendsto g l (𝓝 y)) (hl : forall x, f x ⤳ g x)
  proof: by
  simp_all only [specializes_iff_forall_open, tendsto_nhds]
  refine fun s ho hy => mem_of_superset (h s ho hy) fun x hx => ?_
  exact mem_preimage.2 (hl x s ho (mem_preimage.1 hx))

中文:
定理 Tendsto.specializes
  条件: {l : Filter X} {y : Y} (h : Tendsto g l (𝓝 y)) (hl : 对任意 x, f x ⤳ g x)
  证明: by
  simp_all only [specializes_iff_forall_open, tendsto_nhds]
  refine fun s ho hy => mem_of_superset (h s ho hy) fun x hx => ?_
  exact mem_preimage.2 (hl x s ho (mem_preimage.1 hx))

Depends on / 依赖: mem_of_superset, mem_preimage, specializes_iff_forall_open, tendsto_nhds
-/
theorem Tendsto.specializes {l : Filter X} {y : Y} (h : Tendsto g l (𝓝 y)) (hl : forall x, f x ⤳ g x) :
    Tendsto f l (𝓝 y) := by
  simp_all only [specializes_iff_forall_open, tendsto_nhds]
  refine fun s ho hy => mem_of_superset (h s ho hy) fun x hx => ?_
  exact mem_preimage.2 (hl x s ho (mem_preimage.1 hx))

/--
theorem `Specializes.mem_open` / 定理 `Specializes.mem_open`

English:
theorem Specializes.mem_open
  given: (h : x ⤳ y) (hs : IsOpen s) (hy : y in s)
  statement: x in s
  proof: specializes_iff_forall_open.1 h s hs hy

中文:
定理 Specializes.mem_open
  条件: (h : x ⤳ y) (hs : IsOpen s) (hy : y in s)
  结论: x in s
  证明: specializes_iff_forall_open.1 h s hs hy

Depends on / 依赖: specializes_iff_forall_open
-/
theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y in s) : x in s :=
  specializes_iff_forall_open.1 h s hs hy

/--
theorem `IsOpen.not_specializes` / 定理 `IsOpen.not_specializes`

English:
theorem IsOpen.not_specializes
  given: (hs : IsOpen s) (hx : x ∉ s) (hy : y in s)
  statement: ¬x ⤳ y
  proof: fun h =>
hx h.mem_open hs hy

中文:
定理 IsOpen.not_specializes
  条件: (hs : IsOpen s) (hx : x ∉ s) (hy : y in s)
  结论: ¬x ⤳ y
  证明: fun h =>
hx h.mem_open hs hy
-/
theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y in s) : ¬x ⤳ y := fun h =>
hx h.mem_open hs hy

/--
theorem `specializes_iff_forall_closed` / 定理 `specializes_iff_forall_closed`

English:
theorem specializes_iff_forall_closed
  statement: x ⤳ y ↔ forall s : Set X, IsClosed s -> x in s -> y in s
  proof: (specializes_TFAE x y).out 0 3

中文:
定理 specializes_iff_forall_closed
  结论: x ⤳ y ↔ 对任意 s : Set X, IsClosed s -> x in s -> y in s
  证明: (specializes_TFAE x y).out 0 3

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_forall_closed : x ⤳ y ↔ forall s : Set X, IsClosed s -> x in s -> y in s :=
  (specializes_TFAE x y).out 0 3

/--
theorem `Specializes.mem_closed` / 定理 `Specializes.mem_closed`

English:
theorem Specializes.mem_closed
  given: (h : x ⤳ y) (hs : IsClosed s) (hx : x in s)
  statement: y in s
  proof: specializes_iff_forall_closed.1 h s hs hx

中文:
定理 Specializes.mem_closed
  条件: (h : x ⤳ y) (hs : IsClosed s) (hx : x in s)
  结论: y in s
  证明: specializes_iff_forall_closed.1 h s hs hx

Depends on / 依赖: specializes_iff_forall_closed
-/
theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x in s) : y in s :=
  specializes_iff_forall_closed.1 h s hs hx

/--
theorem `IsClosed.not_specializes` / 定理 `IsClosed.not_specializes`

English:
theorem IsClosed.not_specializes
  given: (hs : IsClosed s) (hx : x in s) (hy : y ∉ s)
  statement: ¬x ⤳ y
  proof: fun h =>
hy h.mem_closed hs hx

中文:
定理 IsClosed.not_specializes
  条件: (hs : IsClosed s) (hx : x in s) (hy : y ∉ s)
  结论: ¬x ⤳ y
  证明: fun h =>
hy h.mem_closed hs hx
-/
theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x in s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
hy h.mem_closed hs hx

/--
theorem `specializes_iff_mem_closure` / 定理 `specializes_iff_mem_closure`

English:
theorem specializes_iff_mem_closure
  statement: x ⤳ y ↔ y in closure ({x} : Set X)
  proof: (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure

中文:
定理 specializes_iff_mem_closure
  结论: x ⤳ y ↔ y in closure ({x} : Set X)
  证明: (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_mem_closure : x ⤳ y ↔ y in closure ({x} : Set X) :=
  (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure

/--
theorem `specializes_iff_closure_subset` / 定理 `specializes_iff_closure_subset`

English:
theorem specializes_iff_closure_subset
  statement: x ⤳ y ↔ closure ({y} : Set X) subseteq closure {x}
  proof: (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset

中文:
定理 specializes_iff_closure_subset
  结论: x ⤳ y ↔ closure ({y} : Set X) subseteq closure {x}
  证明: (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) subseteq closure {x} :=
  (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset

/--
theorem `specializes_iff_clusterPt` / 定理 `specializes_iff_clusterPt`

English:
theorem specializes_iff_clusterPt
  statement: x ⤳ y ↔ ClusterPt y (pure x)
  proof: (specializes_TFAE x y).out 0 6

中文:
定理 specializes_iff_clusterPt
  结论: x ⤳ y ↔ ClusterPt y (pure x)
  证明: (specializes_TFAE x y).out 0 6

Depends on / 依赖: specializes_TFAE
-/
theorem specializes_iff_clusterPt : x ⤳ y ↔ ClusterPt y (pure x) :=
  (specializes_TFAE x y).out 0 6

/--
theorem `Filter.HasBasis.specializes_iff` / 定理 `Filter.HasBasis.specializes_iff`

English:
theorem Filter.HasBasis.specializes_iff
  statement: {ι} {p : ι -> Prop} {s : ι -> Set X}
  proof: specializes_iff_pure.trans h.ge_iff

中文:
定理 Filter.HasBasis.specializes_iff
  结论: {ι} {p : ι -> 命题} {s : ι -> Set X}
  证明: specializes_iff_pure.trans h.ge_iff

Depends on / 依赖: ge_iff, h.ge_iff, specializes_iff_pure, specializes_iff_pure.trans
-/
theorem Filter.HasBasis.specializes_iff {ι} {p : ι -> Prop} {s : ι -> Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ forall i, p i -> x in s i :=
  specializes_iff_pure.trans h.ge_iff

/--
theorem `specializes_rfl` / 定理 `specializes_rfl`

English:
theorem specializes_rfl
  statement: x ⤳ x
  proof: le_rfl

@[refl]

中文:
定理 specializes_rfl
  结论: x ⤳ x
  证明: le_rfl

@[refl]

Depends on / 依赖: le_rfl
-/
theorem specializes_rfl : x ⤳ x := le_rfl

@[refl]
/--
theorem `specializes_refl` / 定理 `specializes_refl`

English:
theorem specializes_refl
  given: (x : X)
  statement: x ⤳ x
  proof: specializes_rfl

@[trans]

中文:
定理 specializes_refl
  条件: (x : X)
  结论: x ⤳ x
  证明: specializes_rfl

@[trans]

Depends on / 依赖: specializes_rfl
-/
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl

@[trans]
/--
theorem `Specializes.trans` / 定理 `Specializes.trans`

English:
theorem Specializes.trans
  statement: x ⤳ y -> y ⤳ z -> x ⤳ z
  proof: le_trans

中文:
定理 Specializes.trans
  结论: x ⤳ y -> y ⤳ z -> x ⤳ z
  证明: le_trans

Depends on / 依赖: le_trans
-/
theorem Specializes.trans : x ⤳ y -> y ⤳ z -> x ⤳ z :=
  le_trans

/--
theorem `specializes_of_eq` / 定理 `specializes_of_eq`

English:
theorem specializes_of_eq
  given: (e : x = y)
  statement: x ⤳ y
  proof: e ▸ specializes_refl x

alias Specializes.of_eq := specializes_of_eq

中文:
定理 specializes_of_eq
  条件: (e : x = y)
  结论: x ⤳ y
  证明: e ▸ specializes_refl x

alias Specializes.of_eq := specializes_of_eq

Depends on / 依赖: specializes_refl
-/
theorem specializes_of_eq (e : x = y) : x ⤳ y :=
  e ▸ specializes_refl x

alias Specializes.of_eq := specializes_of_eq

/--
theorem `specializes_of_nhdsWithin` / 定理 `specializes_of_nhdsWithin`

English:
theorem specializes_of_nhdsWithin
  given: (h₁ : 𝓝[s] x <= 𝓝[s] y) (h₂ : x in s)
  statement: x ⤳ y
  proof: specializes_iff_pure.2
    calc
      pure x <= 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ <= 𝓝[s] y := h₁
      _ <= 𝓝 y := inf_le_left

中文:
定理 specializes_of_nhdsWithin
  条件: (h₁ : 𝓝[s] x <= 𝓝[s] y) (h₂ : x in s)
  结论: x ⤳ y
  证明: specializes_iff_pure.2
    calc
      pure x <= 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ <= 𝓝[s] y := h₁
      _ <= 𝓝 y := inf_le_left

Depends on / 依赖: inf_le_left, le_inf, le_principal_iff, pure_le_nhds, specializes_iff_pure
-/
theorem specializes_of_nhdsWithin (h₁ : 𝓝[s] x <= 𝓝[s] y) (h₂ : x in s) : x ⤳ y :=
specializes_iff_pure.2
    calc
      pure x <= 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ <= 𝓝[s] y := h₁
      _ <= 𝓝 y := inf_le_left

/--
theorem `Specializes.map_of_continuousWithinAt` / 定理 `Specializes.map_of_continuousWithinAt`

English:
theorem Specializes.map_of_continuousWithinAt
  statement: {s : Set X} (h : x ⤳ y)
  proof: by
  rw [specializes_iff_pure] at h ⊢
  calc pure (f x)
    _ = map f (pure x) := (map_pure f x).symm
    _ <= map f (𝓝 y ⊓ 𝓟 s) := map_mono (le_inf h ((pure_le_principal x).mpr hx))
    _ = map f (𝓝[s] y) := rfl
    _ <= _ := hf.tendsto

中文:
定理 Specializes.map_of_continuousWithinAt
  结论: {s : Set X} (h : x ⤳ y)
  证明: by
  rw [specializes_iff_pure] at h ⊢
  calc pure (f x)
    _ = map f (pure x) := (map_pure f x).symm
    _ <= map f (𝓝 y ⊓ 𝓟 s) := map_mono (le_inf h ((pure_le_principal x).mpr hx))
    _ = map f (𝓝[s] y) := rfl
    _ <= _ := hf.tendsto

Depends on / 依赖: hf.tendsto, le_inf, map_mono, map_pure, pure_le_principal, specializes_iff_pure, tendsto
-/
theorem Specializes.map_of_continuousWithinAt {s : Set X} (h : x ⤳ y)
    (hf : ContinuousWithinAt f s y) (hx : x in s) : f x ⤳ f y := by
  rw [specializes_iff_pure] at h ⊢
  calc pure (f x)
    _ = map f (pure x) := (map_pure f x).symm
    _ <= map f (𝓝 y ⊓ 𝓟 s) := map_mono (le_inf h ((pure_le_principal x).mpr hx))
    _ = map f (𝓝[s] y) := rfl
    _ <= _ := hf.tendsto

/--
theorem `Specializes.map_of_continuousOn` / 定理 `Specializes.map_of_continuousOn`

English:
theorem Specializes.map_of_continuousOn
  statement: {s : Set X} (h : x ⤳ y)
  proof: h.map_of_continuousWithinAt (hf.continuousWithinAt hy) hx

中文:
定理 Specializes.map_of_continuousOn
  结论: {s : Set X} (h : x ⤳ y)
  证明: h.map_of_continuousWithinAt (hf.continuousWithinAt hy) hx

Depends on / 依赖: continuousWithinAt, h.map_of_continuousWithinAt, hf.continuousWithinAt, map_of_continuousWithinAt
-/
theorem Specializes.map_of_continuousOn {s : Set X} (h : x ⤳ y)
    (hf : ContinuousOn f s) (hx : x in s) (hy : y in s) : f x ⤳ f y :=
  h.map_of_continuousWithinAt (hf.continuousWithinAt hy) hx

/--
theorem `Specializes.map_of_continuousAt` / 定理 `Specializes.map_of_continuousAt`

English:
theorem Specializes.map_of_continuousAt
  given: (h : x ⤳ y) (hf : ContinuousAt f y)
  statement: f x ⤳ f y
  proof: h.map_of_continuousWithinAt hf.continuousWithinAt (mem_univ x)

中文:
定理 Specializes.map_of_continuousAt
  条件: (h : x ⤳ y) (hf : ContinuousAt f y)
  结论: f x ⤳ f y
  证明: h.map_of_continuousWithinAt hf.continuousWithinAt (mem_univ x)

Depends on / 依赖: continuousWithinAt, h.map_of_continuousWithinAt, hf.continuousWithinAt, map_of_continuousWithinAt, mem_univ
-/
theorem Specializes.map_of_continuousAt (h : x ⤳ y) (hf : ContinuousAt f y) : f x ⤳ f y :=
  h.map_of_continuousWithinAt hf.continuousWithinAt (mem_univ x)

/--
theorem `Specializes.map` / 定理 `Specializes.map`

English:
theorem Specializes.map
  given: (h : x ⤳ y) (hf : Continuous f)
  statement: f x ⤳ f y
  proof: h.map_of_continuousAt hf.continuousAt

中文:
定理 Specializes.map
  条件: (h : x ⤳ y) (hf : Continuous f)
  结论: f x ⤳ f y
  证明: h.map_of_continuousAt hf.continuousAt

Depends on / 依赖: continuousAt, h.map_of_continuousAt, hf.continuousAt, map_of_continuousAt
-/
theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuousAt hf.continuousAt

/--
theorem `Topology.IsInducing.specializes_iff` / 定理 `Topology.IsInducing.specializes_iff`

English:
theorem Topology.IsInducing.specializes_iff
  given: (hf : IsInducing f)
  statement: f x ⤳ f y ↔ x ⤳ y
  proof: by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]

中文:
定理 Topology.IsInducing.specializes_iff
  条件: (hf : IsInducing f)
  结论: f x ⤳ f y ↔ x ⤳ y
  证明: by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]

Depends on / 依赖: closure_eq_preimage_closure_image, hf.closure_eq_preimage_closure_image, image_singleton, mem_preimage, specializes_iff_mem_closure
-/
theorem Topology.IsInducing.specializes_iff (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]

/--
theorem `subtype_specializes_iff` / 定理 `subtype_specializes_iff`

English:
theorem subtype_specializes_iff
  given: {p : X -> Prop} (x y : Subtype p)
  statement: x ⤳ y ↔ (x : X) ⤳ y
  proof: IsInducing.subtypeVal.specializes_iff.symm

@[simp]

中文:
定理 subtype_specializes_iff
  条件: {p : X -> 命题} (x y : Subtype p)
  结论: x ⤳ y ↔ (x : X) ⤳ y
  证明: IsInducing.subtypeVal.specializes_iff.symm

@[simp]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.specializes_iff.symm, specializes_iff, subtypeVal
-/
theorem subtype_specializes_iff {p : X -> Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  IsInducing.subtypeVal.specializes_iff.symm

@[simp]
/--
theorem `specializes_prod` / 定理 `specializes_prod`

English:
theorem specializes_prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y}
  statement: (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂
  proof: by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]

中文:
定理 specializes_prod
  条件: {x₁ x₂ : X} {y₁ y₂ : Y}
  结论: (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂
  证明: by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]

Depends on / 依赖: Specializes, nhds_prod_eq, prod_le_prod
-/
theorem specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ := by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]

/--
theorem `Specializes.prod` / 定理 `Specializes.prod`

English:
theorem Specializes.prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂)
  proof: specializes_prod.2 ⟨hx, hy⟩

中文:
定理 Specializes.prod
  条件: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂)
  证明: specializes_prod.2 ⟨hx, hy⟩

Depends on / 依赖: specializes_prod
-/
theorem Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
    (x₁, y₁) ⤳ (x₂, y₂) :=
  specializes_prod.2 ⟨hx, hy⟩

/--
theorem `Specializes.fst` / 定理 `Specializes.fst`

English:
theorem Specializes.fst
  given: {a b : X × Y} (h : a ⤳ b)
  statement: a.1 ⤳ b.1
  proof: (specializes_prod.1 h).1

中文:
定理 Specializes.fst
  条件: {a b : X × Y} (h : a ⤳ b)
  结论: a.1 ⤳ b.1
  证明: (specializes_prod.1 h).1

Depends on / 依赖: specializes_prod
-/
theorem Specializes.fst {a b : X × Y} (h : a ⤳ b) : a.1 ⤳ b.1 := (specializes_prod.1 h).1
/--
theorem `Specializes.snd` / 定理 `Specializes.snd`

English:
theorem Specializes.snd
  given: {a b : X × Y} (h : a ⤳ b)
  statement: a.2 ⤳ b.2
  proof: (specializes_prod.1 h).2

@[simp]

中文:
定理 Specializes.snd
  条件: {a b : X × Y} (h : a ⤳ b)
  结论: a.2 ⤳ b.2
  证明: (specializes_prod.1 h).2

@[simp]

Depends on / 依赖: specializes_prod
-/
theorem Specializes.snd {a b : X × Y} (h : a ⤳ b) : a.2 ⤳ b.2 := (specializes_prod.1 h).2

@[simp]
/--
theorem `specializes_pi` / 定理 `specializes_pi`

English:
theorem specializes_pi
  given: {f g : forall i, A i}
  statement: f ⤳ g ↔ forall i, f i ⤳ g i
  proof: by
  simp only [Specializes, nhds_pi, pi_le_pi]

中文:
定理 specializes_pi
  条件: {f g : 对任意 i, A i}
  结论: f ⤳ g ↔ 对任意 i, f i ⤳ g i
  证明: by
  simp only [Specializes, nhds_pi, pi_le_pi]

Depends on / 依赖: Specializes, nhds_pi, pi_le_pi
-/
theorem specializes_pi {f g : forall i, A i} : f ⤳ g ↔ forall i, f i ⤳ g i := by
  simp only [Specializes, nhds_pi, pi_le_pi]

/--
theorem `not_specializes_iff_exists_open` / 定理 `not_specializes_iff_exists_open`

English:
theorem not_specializes_iff_exists_open
  statement: ¬x ⤳ y ↔ exists S : Set X, IsOpen S ∧ y in S ∧ x ∉ S
  proof: by
  rw [specializes_iff_forall_open]
  push Not
  rfl

中文:
定理 not_specializes_iff_exists_open
  结论: ¬x ⤳ y ↔ 存在 S : Set X, IsOpen S ∧ y in S ∧ x ∉ S
  证明: by
  rw [specializes_iff_forall_open]
  push Not
  rfl

Depends on / 依赖: specializes_iff_forall_open
-/
theorem not_specializes_iff_exists_open : ¬x ⤳ y ↔ exists S : Set X, IsOpen S ∧ y in S ∧ x ∉ S := by
  rw [specializes_iff_forall_open]
  push Not
  rfl

/--
theorem `not_specializes_iff_exists_closed` / 定理 `not_specializes_iff_exists_closed`

English:
theorem not_specializes_iff_exists_closed
  statement: ¬x ⤳ y ↔ exists S : Set X, IsClosed S ∧ x in S ∧ y ∉ S
  proof: by
  rw [specializes_iff_forall_closed]
  push Not
  rfl

中文:
定理 not_specializes_iff_exists_closed
  结论: ¬x ⤳ y ↔ 存在 S : Set X, IsClosed S ∧ x in S ∧ y ∉ S
  证明: by
  rw [specializes_iff_forall_closed]
  push Not
  rfl

Depends on / 依赖: specializes_iff_forall_closed
-/
theorem not_specializes_iff_exists_closed : ¬x ⤳ y ↔ exists S : Set X, IsClosed S ∧ x in S ∧ y ∉ S := by
  rw [specializes_iff_forall_closed]
  push Not
  rfl

/--
theorem `IsOpen.continuous_piecewise_of_specializes` / 定理 `IsOpen.continuous_piecewise_of_specializes`

English:
theorem IsOpen.continuous_piecewise_of_specializes
  statement: [DecidablePred (· in s)] (hs : IsOpen s)
  proof: by
  have : forall U, IsOpen U -> g ⁻¹' U subseteq f ⁻¹' U := fun U hU x hx => (hspec x).mem_open hU hx
  rw [continuous_def]
  intro U hU
  rw [piecewise_preimage]; rw [ite_eq_of_subset_right _ (this U hU)]
.union (hU.preimage hg) .inter hs exact hU.preimage hf

中文:
定理 IsOpen.continuous_piecewise_of_specializes
  结论: [DecidablePred (· in s)] (hs : IsOpen s)
  证明: by
  have : forall U, IsOpen U -> g ⁻¹' U subseteq f ⁻¹' U := fun U hU x hx => (hspec x).mem_open hU hx
  rw [continuous_def]
  intro U hU
  rw [piecewise_preimage]; rw [ite_eq_of_subset_right _ (this U hU)]
.union (hU.preimage hg) .inter hs exact hU.preimage hf

Depends on / 依赖: IsOpen, continuous_def, hU.preimage, ite_eq_of_subset_right, mem_open, piecewise_preimage, preimage, subseteq
-/
theorem IsOpen.continuous_piecewise_of_specializes [DecidablePred (· in s)] (hs : IsOpen s)
    (hf : Continuous f) (hg : Continuous g) (hspec : forall x, f x ⤳ g x) :
    Continuous (s.piecewise f g) := by
  have : forall U, IsOpen U -> g ⁻¹' U subseteq f ⁻¹' U := fun U hU x hx => (hspec x).mem_open hU hx
  rw [continuous_def]
  intro U hU
  rw [piecewise_preimage]; rw [ite_eq_of_subset_right _ (this U hU)]
.union (hU.preimage hg) .inter hs exact hU.preimage hf

/--
theorem `IsClosed.continuous_piecewise_of_specializes` / 定理 `IsClosed.continuous_piecewise_of_specializes`

English:
theorem IsClosed.continuous_piecewise_of_specializes
  statement: [DecidablePred (· in s)] (hs : IsClosed s)
  proof: by
  simpa only [piecewise_compl] using hs.isOpen_compl.continuous_piecewise_of_specializes hg hf hspec

中文:
定理 IsClosed.continuous_piecewise_of_specializes
  结论: [DecidablePred (· in s)] (hs : IsClosed s)
  证明: by
  simpa only [piecewise_compl] using hs.isOpen_compl.continuous_piecewise_of_specializes hg hf hspec

Depends on / 依赖: continuous_piecewise_of_specializes, hs.isOpen_compl.continuous_piecewise_of_specializes, isOpen_compl, piecewise_compl
-/
theorem IsClosed.continuous_piecewise_of_specializes [DecidablePred (· in s)] (hs : IsClosed s)
    (hf : Continuous f) (hg : Continuous g) (hspec : forall x, g x ⤳ f x) :
    Continuous (s.piecewise f g) := by
  simpa only [piecewise_compl] using hs.isOpen_compl.continuous_piecewise_of_specializes hg hf hspec

/--
theorem `Specializes.clusterPt` / 定理 `Specializes.clusterPt`

English:
theorem Specializes.clusterPt
  given: {f : Filter X} (h : x ⤳ y) (hx : ClusterPt x f)
  proof: Filter.NeBot.mono hx inf_le_inf_right _ h

中文:
定理 Specializes.clusterPt
  条件: {f : Filter X} (h : x ⤳ y) (hx : ClusterPt x f)
  证明: Filter.NeBot.mono hx inf_le_inf_right _ h

Depends on / 依赖: Filter, Filter.NeBot.mono, inf_le_inf_right
-/
theorem Specializes.clusterPt {f : Filter X} (h : x ⤳ y) (hx : ClusterPt x f) :
    ClusterPt y f :=
Filter.NeBot.mono hx inf_le_inf_right _ h

/--
theorem `IsCompact.of_subset_of_specializes` / 定理 `IsCompact.of_subset_of_specializes`

English:
theorem IsCompact.of_subset_of_specializes
  statement: {s t : Set X} (hs : IsCompact s) (hts : t subseteq s)
  proof: by
  intro f _ hf
obtain ⟨x, hxs, hxf⟩ := hs hf.trans Filter.monotone_principal hts
  obtain ⟨y, hyt, hxy⟩ := h x hxs
  exact ⟨y, hyt, hxy.clusterPt hxf⟩

中文:
定理 IsCompact.of_subset_of_specializes
  结论: {s t : Set X} (hs : IsCompact s) (hts : t subseteq s)
  证明: by
  intro f _ hf
obtain ⟨x, hxs, hxf⟩ := hs hf.trans Filter.monotone_principal hts
  obtain ⟨y, hyt, hxy⟩ := h x hxs
  exact ⟨y, hyt, hxy.clusterPt hxf⟩

Depends on / 依赖: Filter, Filter.monotone_principal, clusterPt, hf.trans, hxy.clusterPt, monotone_principal
-/
theorem IsCompact.of_subset_of_specializes {s t : Set X} (hs : IsCompact s) (hts : t subseteq s)
    (h : forall x in s, exists y in t, x ⤳ y) : IsCompact t := by
  intro f _ hf
obtain ⟨x, hxs, hxf⟩ := hs hf.trans Filter.monotone_principal hts
  obtain ⟨y, hyt, hxy⟩ := h x hxs
  exact ⟨y, hyt, hxy.clusterPt hxf⟩

attribute [local instance] specializationPreorder

/--
theorem `Continuous.specialization_monotone` / 定理 `Continuous.specialization_monotone`

English:
theorem Continuous.specialization_monotone
  given: (hf : Continuous f)
  statement: Monotone f
  proof: fun _ _ h => h.map hf

中文:
定理 Continuous.specialization_monotone
  条件: (hf : Continuous f)
  结论: Monotone f
  证明: fun _ _ h => h.map hf

Depends on / 依赖: h.map
-/
theorem Continuous.specialization_monotone (hf : Continuous f) : Monotone f :=
  fun _ _ h => h.map hf

/--
lemma `closure_singleton_eq_Iic` / 引理 `closure_singleton_eq_Iic`

English:
lemma closure_singleton_eq_Iic
  given: (x : X)
  statement: closure {x} = Iic x
  proof: Set.ext fun _ => specializes_iff_mem_closure.symm

中文:
引理 closure_singleton_eq_Iic
  条件: (x : X)
  结论: closure {x} = Iic x
  证明: Set.ext fun _ => specializes_iff_mem_closure.symm

Depends on / 依赖: Set.ext, specializes_iff_mem_closure, specializes_iff_mem_closure.symm
-/
lemma closure_singleton_eq_Iic (x : X) : closure {x} = Iic x :=
  Set.ext fun _ => specializes_iff_mem_closure.symm

/--
Definition of `StableUnderSpecialization` / `StableUnderSpecialization` 的定义

English:
definition StableUnderSpecialization
  signature: (s : Set X)
  body: forall ⦃x y⦄, x ⤳ y -> x in s -> y in s

中文:
定义 StableUnderSpecialization
  签名: (s : Set X)
  定义体: forall ⦃x y⦄, x ⤳ y -> x in s -> y in s
-/
def StableUnderSpecialization (s : Set X) : Prop :=
  forall ⦃x y⦄, x ⤳ y -> x in s -> y in s

/--
Definition of `StableUnderGeneralization` / `StableUnderGeneralization` 的定义

English:
definition StableUnderGeneralization
  signature: (s : Set X)
  body: forall ⦃x y⦄, y ⤳ x -> x in s -> y in s

example {s : Set X} : StableUnderSpecialization s ↔ IsLowerSet s := Iff.rfl
example {s : Set X} : StableUnderGeneralization s ↔ IsUpperSet s := Iff.rfl

中文:
定义 StableUnderGeneralization
  签名: (s : Set X)
  定义体: forall ⦃x y⦄, y ⤳ x -> x in s -> y in s

example {s : Set X} : StableUnderSpecialization s ↔ IsLowerSet s := Iff.rfl
example {s : Set X} : StableUnderGeneralization s ↔ IsUpperSet s := Iff.rfl
-/
def StableUnderGeneralization (s : Set X) : Prop :=
  forall ⦃x y⦄, y ⤳ x -> x in s -> y in s

example {s : Set X} : StableUnderSpecialization s ↔ IsLowerSet s := Iff.rfl
example {s : Set X} : StableUnderGeneralization s ↔ IsUpperSet s := Iff.rfl

/--
lemma `IsClosed.stableUnderSpecialization` / 引理 `IsClosed.stableUnderSpecialization`

English:
lemma IsClosed.stableUnderSpecialization
  given: {s : Set X} (hs : IsClosed s)
  proof: fun _ _ e => e.mem_closed hs

中文:
引理 IsClosed.stableUnderSpecialization
  条件: {s : Set X} (hs : IsClosed s)
  证明: fun _ _ e => e.mem_closed hs

Depends on / 依赖: e.mem_closed, mem_closed
-/
lemma IsClosed.stableUnderSpecialization {s : Set X} (hs : IsClosed s) :
    StableUnderSpecialization s :=
  fun _ _ e => e.mem_closed hs

/--
lemma `IsOpen.stableUnderGeneralization` / 引理 `IsOpen.stableUnderGeneralization`

English:
lemma IsOpen.stableUnderGeneralization
  given: {s : Set X} (hs : IsOpen s)
  proof: fun _ _ e => e.mem_open hs

@[simp]

中文:
引理 IsOpen.stableUnderGeneralization
  条件: {s : Set X} (hs : IsOpen s)
  证明: fun _ _ e => e.mem_open hs

@[simp]

Depends on / 依赖: e.mem_open, mem_open
-/
lemma IsOpen.stableUnderGeneralization {s : Set X} (hs : IsOpen s) :
    StableUnderGeneralization s :=
  fun _ _ e => e.mem_open hs

@[simp]
/--
lemma `stableUnderSpecialization_compl_iff` / 引理 `stableUnderSpecialization_compl_iff`

English:
lemma stableUnderSpecialization_compl_iff
  given: {s : Set X}
  proof: isLowerSet_compl

@[simp]

中文:
引理 stableUnderSpecialization_compl_iff
  条件: {s : Set X}
  证明: isLowerSet_compl

@[simp]

Depends on / 依赖: isLowerSet_compl
-/
lemma stableUnderSpecialization_compl_iff {s : Set X} :
    StableUnderSpecialization sᶜ ↔ StableUnderGeneralization s :=
  isLowerSet_compl

@[simp]
/--
lemma `stableUnderGeneralization_compl_iff` / 引理 `stableUnderGeneralization_compl_iff`

English:
lemma stableUnderGeneralization_compl_iff
  given: {s : Set X}
  proof: isUpperSet_compl

alias ⟨_, StableUnderGeneralization.compl⟩ := stableUnderSpecialization_compl_iff
alias ⟨_, StableUnderSpecialization.compl⟩ := stableUnderGeneralization_compl_iff

中文:
引理 stableUnderGeneralization_compl_iff
  条件: {s : Set X}
  证明: isUpperSet_compl

alias ⟨_, StableUnderGeneralization.compl⟩ := stableUnderSpecialization_compl_iff
alias ⟨_, StableUnderSpecialization.compl⟩ := stableUnderGeneralization_compl_iff

Depends on / 依赖: isUpperSet_compl
-/
lemma stableUnderGeneralization_compl_iff {s : Set X} :
    StableUnderGeneralization sᶜ ↔ StableUnderSpecialization s :=
  isUpperSet_compl

alias ⟨_, StableUnderGeneralization.compl⟩ := stableUnderSpecialization_compl_iff
alias ⟨_, StableUnderSpecialization.compl⟩ := stableUnderGeneralization_compl_iff

/--
lemma `stableUnderSpecialization_univ` / 引理 `stableUnderSpecialization_univ`

English:
lemma stableUnderSpecialization_univ
  statement: StableUnderSpecialization (univ : Set X)
  proof: isLowerSet_univ

中文:
引理 stableUnderSpecialization_univ
  结论: StableUnderSpecialization (univ : Set X)
  证明: isLowerSet_univ

Depends on / 依赖: isLowerSet_univ
-/
lemma stableUnderSpecialization_univ : StableUnderSpecialization (univ : Set X) := isLowerSet_univ
/--
lemma `stableUnderSpecialization_empty` / 引理 `stableUnderSpecialization_empty`

English:
lemma stableUnderSpecialization_empty
  statement: StableUnderSpecialization (∅ : Set X)
  proof: isLowerSet_empty

中文:
引理 stableUnderSpecialization_empty
  结论: StableUnderSpecialization (∅ : Set X)
  证明: isLowerSet_empty

Depends on / 依赖: isLowerSet_empty
-/
lemma stableUnderSpecialization_empty : StableUnderSpecialization (∅ : Set X) := isLowerSet_empty
/--
lemma `stableUnderGeneralization_univ` / 引理 `stableUnderGeneralization_univ`

English:
lemma stableUnderGeneralization_univ
  statement: StableUnderGeneralization (univ : Set X)
  proof: isUpperSet_univ

中文:
引理 stableUnderGeneralization_univ
  结论: StableUnderGeneralization (univ : Set X)
  证明: isUpperSet_univ

Depends on / 依赖: isUpperSet_univ
-/
lemma stableUnderGeneralization_univ : StableUnderGeneralization (univ : Set X) := isUpperSet_univ
/--
lemma `stableUnderGeneralization_empty` / 引理 `stableUnderGeneralization_empty`

English:
lemma stableUnderGeneralization_empty
  statement: StableUnderGeneralization (∅ : Set X)
  proof: isUpperSet_empty

中文:
引理 stableUnderGeneralization_empty
  结论: StableUnderGeneralization (∅ : Set X)
  证明: isUpperSet_empty

Depends on / 依赖: isUpperSet_empty
-/
lemma stableUnderGeneralization_empty : StableUnderGeneralization (∅ : Set X) := isUpperSet_empty

/--
lemma `stableUnderSpecialization_sUnion` / 引理 `stableUnderSpecialization_sUnion`

English:
lemma stableUnderSpecialization_sUnion
  statement: (S : Set (Set X))
  proof: isLowerSet_sUnion H

中文:
引理 stableUnderSpecialization_sUnion
  结论: (S : Set (Set X))
  证明: isLowerSet_sUnion H

Depends on / 依赖: isLowerSet_sUnion
-/
lemma stableUnderSpecialization_sUnion (S : Set (Set X))
    (H : forall s in S, StableUnderSpecialization s) : StableUnderSpecialization (⋃₀ S) :=
  isLowerSet_sUnion H

/--
lemma `stableUnderSpecialization_sInter` / 引理 `stableUnderSpecialization_sInter`

English:
lemma stableUnderSpecialization_sInter
  statement: (S : Set (Set X))
  proof: isLowerSet_sInter H

中文:
引理 stableUnderSpecialization_sInter
  结论: (S : Set (Set X))
  证明: isLowerSet_sInter H

Depends on / 依赖: isLowerSet_sInter
-/
lemma stableUnderSpecialization_sInter (S : Set (Set X))
    (H : forall s in S, StableUnderSpecialization s) : StableUnderSpecialization (⋂₀ S) :=
  isLowerSet_sInter H

/--
lemma `stableUnderGeneralization_sUnion` / 引理 `stableUnderGeneralization_sUnion`

English:
lemma stableUnderGeneralization_sUnion
  statement: (S : Set (Set X))
  proof: isUpperSet_sUnion H

中文:
引理 stableUnderGeneralization_sUnion
  结论: (S : Set (Set X))
  证明: isUpperSet_sUnion H

Depends on / 依赖: isUpperSet_sUnion
-/
lemma stableUnderGeneralization_sUnion (S : Set (Set X))
    (H : forall s in S, StableUnderGeneralization s) : StableUnderGeneralization (⋃₀ S) :=
  isUpperSet_sUnion H

/--
lemma `stableUnderGeneralization_sInter` / 引理 `stableUnderGeneralization_sInter`

English:
lemma stableUnderGeneralization_sInter
  statement: (S : Set (Set X))
  proof: isUpperSet_sInter H

中文:
引理 stableUnderGeneralization_sInter
  结论: (S : Set (Set X))
  证明: isUpperSet_sInter H

Depends on / 依赖: isUpperSet_sInter
-/
lemma stableUnderGeneralization_sInter (S : Set (Set X))
    (H : forall s in S, StableUnderGeneralization s) : StableUnderGeneralization (⋂₀ S) :=
  isUpperSet_sInter H

/--
lemma `stableUnderSpecialization_iUnion` / 引理 `stableUnderSpecialization_iUnion`

English:
lemma stableUnderSpecialization_iUnion
  statement: {ι : Sort*} (S : ι -> Set X)
  proof: isLowerSet_iUnion H

中文:
引理 stableUnderSpecialization_iUnion
  结论: {ι : Sort*} (S : ι -> Set X)
  证明: isLowerSet_iUnion H

Depends on / 依赖: isLowerSet_iUnion
-/
lemma stableUnderSpecialization_iUnion {ι : Sort*} (S : ι -> Set X)
    (H : forall i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋃ i, S i) :=
  isLowerSet_iUnion H

/--
lemma `stableUnderSpecialization_iInter` / 引理 `stableUnderSpecialization_iInter`

English:
lemma stableUnderSpecialization_iInter
  statement: {ι : Sort*} (S : ι -> Set X)
  proof: isLowerSet_iInter H

中文:
引理 stableUnderSpecialization_iInter
  结论: {ι : Sort*} (S : ι -> Set X)
  证明: isLowerSet_iInter H

Depends on / 依赖: isLowerSet_iInter
-/
lemma stableUnderSpecialization_iInter {ι : Sort*} (S : ι -> Set X)
    (H : forall i, StableUnderSpecialization (S i)) : StableUnderSpecialization (⋂ i, S i) :=
  isLowerSet_iInter H

/--
lemma `stableUnderGeneralization_iUnion` / 引理 `stableUnderGeneralization_iUnion`

English:
lemma stableUnderGeneralization_iUnion
  statement: {ι : Sort*} (S : ι -> Set X)
  proof: isUpperSet_iUnion H

中文:
引理 stableUnderGeneralization_iUnion
  结论: {ι : Sort*} (S : ι -> Set X)
  证明: isUpperSet_iUnion H

Depends on / 依赖: isUpperSet_iUnion
-/
lemma stableUnderGeneralization_iUnion {ι : Sort*} (S : ι -> Set X)
    (H : forall i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋃ i, S i) :=
  isUpperSet_iUnion H

/--
lemma `stableUnderGeneralization_iInter` / 引理 `stableUnderGeneralization_iInter`

English:
lemma stableUnderGeneralization_iInter
  statement: {ι : Sort*} (S : ι -> Set X)
  proof: isUpperSet_iInter H

中文:
引理 stableUnderGeneralization_iInter
  结论: {ι : Sort*} (S : ι -> Set X)
  证明: isUpperSet_iInter H

Depends on / 依赖: isUpperSet_iInter
-/
lemma stableUnderGeneralization_iInter {ι : Sort*} (S : ι -> Set X)
    (H : forall i, StableUnderGeneralization (S i)) : StableUnderGeneralization (⋂ i, S i) :=
  isUpperSet_iInter H

/--
lemma `Union_closure_singleton_eq_iff` / 引理 `Union_closure_singleton_eq_iff`

English:
lemma Union_closure_singleton_eq_iff
  given: {s : Set X}
  proof: show _ ↔ IsLowerSet s by simp only [closure_singleton_eq_Iic, ← lowerClosure_eq, coe_lowerClosure]

中文:
引理 Union_closure_singleton_eq_iff
  条件: {s : Set X}
  证明: show _ ↔ IsLowerSet s by simp only [closure_singleton_eq_Iic, ← lowerClosure_eq, coe_lowerClosure]

Depends on / 依赖: IsLowerSet, closure_singleton_eq_Iic, coe_lowerClosure, lowerClosure_eq
-/
lemma Union_closure_singleton_eq_iff {s : Set X} :
    (⋃ x in s, closure {x}) = s ↔ StableUnderSpecialization s :=
  show _ ↔ IsLowerSet s by simp only [closure_singleton_eq_Iic, ← lowerClosure_eq, coe_lowerClosure]

/--
lemma `stableUnderSpecialization_iff_Union_eq` / 引理 `stableUnderSpecialization_iff_Union_eq`

English:
lemma stableUnderSpecialization_iff_Union_eq
  given: {s : Set X}
  proof: Union_closure_singleton_eq_iff.symm

alias ⟨StableUnderSpecialization.Union_eq, _⟩ := stableUnderSpecialization_iff_Union_eq

中文:
引理 stableUnderSpecialization_iff_Union_eq
  条件: {s : Set X}
  证明: Union_closure_singleton_eq_iff.symm

alias ⟨StableUnderSpecialization.Union_eq, _⟩ := stableUnderSpecialization_iff_Union_eq

Depends on / 依赖: Union_closure_singleton_eq_iff, Union_closure_singleton_eq_iff.symm
-/
lemma stableUnderSpecialization_iff_Union_eq {s : Set X} :
    StableUnderSpecialization s ↔ (⋃ x in s, closure {x}) = s :=
  Union_closure_singleton_eq_iff.symm

alias ⟨StableUnderSpecialization.Union_eq, _⟩ := stableUnderSpecialization_iff_Union_eq

/--
lemma `stableUnderSpecialization_iff_exists_sUnion_eq` / 引理 `stableUnderSpecialization_iff_exists_sUnion_eq`

English:
lemma stableUnderSpecialization_iff_exists_sUnion_eq
  given: {s : Set X}
  proof: by
  refine ⟨fun H => ⟨(fun x : X => closure {x}) '' s, ?_, ?_⟩, fun ⟨S, hS, e⟩ => e ▸
    stableUnderSpecialization_sUnion S (fun x hx => (hS x hx).stableUnderSpecialization)⟩
  · rintro _ ⟨_, _, rfl⟩; exact isClosed_closure
  · conv_rhs => rw [← H.Union_eq]
    simp

中文:
引理 stableUnderSpecialization_iff_exists_sUnion_eq
  条件: {s : Set X}
  证明: by
  refine ⟨fun H => ⟨(fun x : X => closure {x}) '' s, ?_, ?_⟩, fun ⟨S, hS, e⟩ => e ▸
    stableUnderSpecialization_sUnion S (fun x hx => (hS x hx).stableUnderSpecialization)⟩
  · rintro _ ⟨_, _, rfl⟩; exact isClosed_closure
  · conv_rhs => rw [← H.Union_eq]
    simp

Depends on / 依赖: H.Union_eq, Union_eq, closure, conv_rhs, isClosed_closure, stableUnderSpecialization, stableUnderSpecialization_sUnion
-/
lemma stableUnderSpecialization_iff_exists_sUnion_eq {s : Set X} :
    StableUnderSpecialization s ↔ exists (S : Set (Set X)), (forall s in S, IsClosed s) ∧ ⋃₀ S = s := by
  refine ⟨fun H => ⟨(fun x : X => closure {x}) '' s, ?_, ?_⟩, fun ⟨S, hS, e⟩ => e ▸
    stableUnderSpecialization_sUnion S (fun x hx => (hS x hx).stableUnderSpecialization)⟩
  · rintro _ ⟨_, _, rfl⟩; exact isClosed_closure
  · conv_rhs => rw [← H.Union_eq]
    simp

/--
lemma `stableUnderGeneralization_iff_exists_sInter_eq` / 引理 `stableUnderGeneralization_iff_exists_sInter_eq`

English:
lemma stableUnderGeneralization_iff_exists_sInter_eq
  given: {s : Set X}
  proof: by
  refine ⟨?_, fun ⟨S, hS, e⟩ => e ▸
    stableUnderGeneralization_sInter S (fun x hx => (hS x hx).stableUnderGeneralization)⟩
  rw [← stableUnderSpecialization_compl_iff]; rw [stableUnderSpecialization_iff_exists_sUnion_eq]
  exact fun ⟨S, h₁, h₂⟩ => ⟨(·ᶜ) '' S, fun s ⟨t, ht, e⟩ => e ▸ (h₁ t ht).

中文:
引理 stableUnderGeneralization_iff_exists_sInter_eq
  条件: {s : Set X}
  证明: by
  refine ⟨?_, fun ⟨S, hS, e⟩ => e ▸
    stableUnderGeneralization_sInter S (fun x hx => (hS x hx).stableUnderGeneralization)⟩
  rw [← stableUnderSpecialization_compl_iff]; rw [stableUnderSpecialization_iff_exists_sUnion_eq]
  exact fun ⟨S, h₁, h₂⟩ => ⟨(·ᶜ) '' S, fun s ⟨t, ht, e⟩ => e ▸ (h₁ t ht).

Depends on / 依赖: compl_injective, isOpen_compl, sUnion_eq_compl_sInter_compl, stableUnderGeneralization, stableUnderGeneralization_sInter, stableUnderSpecialization_compl_iff, stableUnderSpecialization_iff_exists_sUnion_eq, symm.trans
-/
lemma stableUnderGeneralization_iff_exists_sInter_eq {s : Set X} :
    StableUnderGeneralization s ↔ exists (S : Set (Set X)), (forall s in S, IsOpen s) ∧ ⋂₀ S = s := by
  refine ⟨?_, fun ⟨S, hS, e⟩ => e ▸
    stableUnderGeneralization_sInter S (fun x hx => (hS x hx).stableUnderGeneralization)⟩
  rw [← stableUnderSpecialization_compl_iff]; rw [stableUnderSpecialization_iff_exists_sUnion_eq]
  exact fun ⟨S, h₁, h₂⟩ => ⟨(·ᶜ) '' S, fun s ⟨t, ht, e⟩ => e ▸ (h₁ t ht).isOpen_compl,
    compl_injective ((sUnion_eq_compl_sInter_compl S).symm.trans h₂)⟩

/--
lemma `StableUnderSpecialization.preimage` / 引理 `StableUnderSpecialization.preimage`

English:
lemma StableUnderSpecialization.preimage
  statement: {s : Set Y}
  proof: IsLowerSet.preimage hs hf.specialization_monotone

中文:
引理 StableUnderSpecialization.preimage
  结论: {s : Set Y}
  证明: IsLowerSet.preimage hs hf.specialization_monotone

Depends on / 依赖: IsLowerSet, IsLowerSet.preimage, hf.specialization_monotone, preimage, specialization_monotone
-/
lemma StableUnderSpecialization.preimage {s : Set Y}
    (hs : StableUnderSpecialization s) (hf : Continuous f) :
    StableUnderSpecialization (f ⁻¹' s) :=
  IsLowerSet.preimage hs hf.specialization_monotone

/--
lemma `StableUnderGeneralization.preimage` / 引理 `StableUnderGeneralization.preimage`

English:
lemma StableUnderGeneralization.preimage
  statement: {s : Set Y}
  proof: IsUpperSet.preimage hs hf.specialization_monotone

中文:
引理 StableUnderGeneralization.preimage
  结论: {s : Set Y}
  证明: IsUpperSet.preimage hs hf.specialization_monotone

Depends on / 依赖: IsUpperSet, IsUpperSet.preimage, hf.specialization_monotone, preimage, specialization_monotone
-/
lemma StableUnderGeneralization.preimage {s : Set Y}
    (hs : StableUnderGeneralization s) (hf : Continuous f) :
    StableUnderGeneralization (f ⁻¹' s) :=
  IsUpperSet.preimage hs hf.specialization_monotone

/--
Definition of `SpecializingMap` / `SpecializingMap` 的定义

English:
definition SpecializingMap
  signature: (f : X -> Y)
  body: Relation.Fibration (flip (· ⤳ ·)) (flip (· ⤳ ·)) f

中文:
定义 SpecializingMap
  签名: (f : X -> Y)
  定义体: Relation.Fibration (flip (· ⤳ ·)) (flip (· ⤳ ·)) f

Depends on / 依赖: Fibration, Relation, Relation.Fibration
-/
def SpecializingMap (f : X -> Y) : Prop :=
  Relation.Fibration (flip (· ⤳ ·)) (flip (· ⤳ ·)) f

/--
Definition of `GeneralizingMap` / `GeneralizingMap` 的定义

English:
definition GeneralizingMap
  signature: (f : X -> Y)
  body: Relation.Fibration (· ⤳ ·) (· ⤳ ·) f

中文:
定义 GeneralizingMap
  签名: (f : X -> Y)
  定义体: Relation.Fibration (· ⤳ ·) (· ⤳ ·) f

Depends on / 依赖: Fibration, Relation, Relation.Fibration
-/
def GeneralizingMap (f : X -> Y) : Prop :=
  Relation.Fibration (· ⤳ ·) (· ⤳ ·) f

/--
lemma `specializingMap_iff_closure_singleton_subset` / 引理 `specializingMap_iff_closure_singleton_subset`

English:
lemma specializingMap_iff_closure_singleton_subset
  proof: by
  simp only [SpecializingMap, Relation.Fibration, flip, specializes_iff_mem_closure]; rfl

alias ⟨SpecializingMap.closure_singleton_subset, _⟩ := specializingMap_iff_closure_singleton_subset

中文:
引理 specializingMap_iff_closure_singleton_subset
  证明: by
  simp only [SpecializingMap, Relation.Fibration, flip, specializes_iff_mem_closure]; rfl

alias ⟨SpecializingMap.closure_singleton_subset, _⟩ := specializingMap_iff_closure_singleton_subset

Depends on / 依赖: Fibration, Relation, Relation.Fibration, SpecializingMap, specializes_iff_mem_closure
-/
lemma specializingMap_iff_closure_singleton_subset :
    SpecializingMap f ↔ forall x, closure {f x} subseteq f '' closure {x} := by
  simp only [SpecializingMap, Relation.Fibration, flip, specializes_iff_mem_closure]; rfl

alias ⟨SpecializingMap.closure_singleton_subset, _⟩ := specializingMap_iff_closure_singleton_subset

/--
lemma `SpecializingMap.stableUnderSpecialization_image` / 引理 `SpecializingMap.stableUnderSpecialization_image`

English:
lemma SpecializingMap.stableUnderSpecialization_image
  statement: (hf : SpecializingMap f)
  proof: IsLowerSet.image_fibration hf hs

alias StableUnderSpecialization.image := SpecializingMap.stableUnderSpecialization_image

中文:
引理 SpecializingMap.stableUnderSpecialization_image
  结论: (hf : SpecializingMap f)
  证明: IsLowerSet.image_fibration hf hs

alias StableUnderSpecialization.image := SpecializingMap.stableUnderSpecialization_image

Depends on / 依赖: IsLowerSet, IsLowerSet.image_fibration, image_fibration
-/
lemma SpecializingMap.stableUnderSpecialization_image (hf : SpecializingMap f)
    {s : Set X} (hs : StableUnderSpecialization s) : StableUnderSpecialization (f '' s) :=
  IsLowerSet.image_fibration hf hs

alias StableUnderSpecialization.image := SpecializingMap.stableUnderSpecialization_image

/--
lemma `specializingMap_iff_stableUnderSpecialization_image_singleton` / 引理 `specializingMap_iff_stableUnderSpecialization_image_singleton`

English:
lemma specializingMap_iff_stableUnderSpecialization_image_singleton
  proof: by
  simpa only [closure_singleton_eq_Iic] using! Relation.fibration_iff_isLowerSet_image_Iic

中文:
引理 specializingMap_iff_stableUnderSpecialization_image_singleton
  证明: by
  simpa only [closure_singleton_eq_Iic] using! Relation.fibration_iff_isLowerSet_image_Iic

Depends on / 依赖: Relation, Relation.fibration_iff_isLowerSet_image_Iic, closure_singleton_eq_Iic, fibration_iff_isLowerSet_image_Iic
-/
lemma specializingMap_iff_stableUnderSpecialization_image_singleton :
    SpecializingMap f ↔ forall x, StableUnderSpecialization (f '' closure {x}) := by
  simpa only [closure_singleton_eq_Iic] using! Relation.fibration_iff_isLowerSet_image_Iic

/--
lemma `specializingMap_iff_stableUnderSpecialization_image` / 引理 `specializingMap_iff_stableUnderSpecialization_image`

English:
lemma specializingMap_iff_stableUnderSpecialization_image
  proof: Relation.fibration_iff_isLowerSet_image

中文:
引理 specializingMap_iff_stableUnderSpecialization_image
  证明: Relation.fibration_iff_isLowerSet_image

Depends on / 依赖: Relation, Relation.fibration_iff_isLowerSet_image, fibration_iff_isLowerSet_image
-/
lemma specializingMap_iff_stableUnderSpecialization_image :
    SpecializingMap f ↔ forall s, StableUnderSpecialization s -> StableUnderSpecialization (f '' s) :=
  Relation.fibration_iff_isLowerSet_image

/--
lemma `specializingMap_iff_closure_singleton` / 引理 `specializingMap_iff_closure_singleton`

English:
lemma specializingMap_iff_closure_singleton
  given: (hf : Continuous f)
  proof: by
  simpa only [closure_singleton_eq_Iic] using!
    Relation.fibration_iff_image_Iic hf.specialization_monotone

中文:
引理 specializingMap_iff_closure_singleton
  条件: (hf : Continuous f)
  证明: by
  simpa only [closure_singleton_eq_Iic] using!
    Relation.fibration_iff_image_Iic hf.specialization_monotone

Depends on / 依赖: Relation, Relation.fibration_iff_image_Iic, closure_singleton_eq_Iic, fibration_iff_image_Iic, hf.specialization_monotone, specialization_monotone
-/
lemma specializingMap_iff_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ forall x, f '' closure {x} = closure {f x} := by
  simpa only [closure_singleton_eq_Iic] using!
    Relation.fibration_iff_image_Iic hf.specialization_monotone

/--
lemma `specializingMap_iff_isClosed_image_closure_singleton` / 引理 `specializingMap_iff_isClosed_image_closure_singleton`

English:
lemma specializingMap_iff_isClosed_image_closure_singleton
  given: (hf : Continuous f)
  proof: by
  refine ⟨fun h x => ?_, fun h => specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    (fun x => (h x).stableUnderSpecialization)⟩
  rw [(specializingMap_iff_closure_singleton hf).mp h x]
  exact isClosed_closure

中文:
引理 specializingMap_iff_isClosed_image_closure_singleton
  条件: (hf : Continuous f)
  证明: by
  refine ⟨fun h x => ?_, fun h => specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    (fun x => (h x).stableUnderSpecialization)⟩
  rw [(specializingMap_iff_closure_singleton hf).mp h x]
  exact isClosed_closure

Depends on / 依赖: isClosed_closure, specializingMap_iff_closure_singleton, specializingMap_iff_stableUnderSpecialization_image_singleton, specializingMap_iff_stableUnderSpecialization_image_singleton.mpr, stableUnderSpecialization
-/
lemma specializingMap_iff_isClosed_image_closure_singleton (hf : Continuous f) :
    SpecializingMap f ↔ forall x, IsClosed (f '' closure {x}) := by
  refine ⟨fun h x => ?_, fun h => specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    (fun x => (h x).stableUnderSpecialization)⟩
  rw [(specializingMap_iff_closure_singleton hf).mp h x]
  exact isClosed_closure

/--
lemma `SpecializingMap.comp` / 引理 `SpecializingMap.comp`

English:
lemma SpecializingMap.comp
  statement: {f : X -> Y} {g : Y -> Z}
  proof: by
  simp only [specializingMap_iff_stableUnderSpecialization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

中文:
引理 SpecializingMap.comp
  结论: {f : X -> Y} {g : Y -> Z}
  证明: by
  simp only [specializingMap_iff_stableUnderSpecialization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

Depends on / 依赖: Set.image_comp, image_comp, specializingMap_iff_stableUnderSpecialization_image
-/
lemma SpecializingMap.comp {f : X -> Y} {g : Y -> Z}
    (hf : SpecializingMap f) (hg : SpecializingMap g) :
    SpecializingMap (g ∘ f) := by
  simp only [specializingMap_iff_stableUnderSpecialization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

/--
lemma `IsClosedMap.specializingMap` / 引理 `IsClosedMap.specializingMap`

English:
lemma IsClosedMap.specializingMap
  given: (hf : IsClosedMap f)
  statement: SpecializingMap f
  proof: specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    fun _ => (hf _ isClosed_closure).stableUnderSpecialization

中文:
引理 IsClosedMap.specializingMap
  条件: (hf : IsClosedMap f)
  结论: SpecializingMap f
  证明: specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    fun _ => (hf _ isClosed_closure).stableUnderSpecialization

Depends on / 依赖: isClosed_closure, specializingMap_iff_stableUnderSpecialization_image_singleton, specializingMap_iff_stableUnderSpecialization_image_singleton.mpr, stableUnderSpecialization
-/
lemma IsClosedMap.specializingMap (hf : IsClosedMap f) : SpecializingMap f :=
specializingMap_iff_stableUnderSpecialization_image_singleton.mpr
    fun _ => (hf _ isClosed_closure).stableUnderSpecialization

/--
lemma `Topology.IsInducing.specializingMap` / 引理 `Topology.IsInducing.specializingMap`

English:
lemma Topology.IsInducing.specializingMap
  statement: (hf : IsInducing f)
  proof: by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

中文:
引理 Topology.IsInducing.specializingMap
  结论: (hf : IsInducing f)
  证明: by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

Depends on / 依赖: hf.specializes_iff.mp, specializes_iff
-/
lemma Topology.IsInducing.specializingMap (hf : IsInducing f)
    (h : StableUnderSpecialization (range f)) : SpecializingMap f := by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

/--
lemma `Topology.IsInducing.generalizingMap` / 引理 `Topology.IsInducing.generalizingMap`

English:
lemma Topology.IsInducing.generalizingMap
  statement: (hf : IsInducing f)
  proof: by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

中文:
引理 Topology.IsInducing.generalizingMap
  结论: (hf : IsInducing f)
  证明: by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

Depends on / 依赖: hf.specializes_iff.mp, specializes_iff
-/
lemma Topology.IsInducing.generalizingMap (hf : IsInducing f)
    (h : StableUnderGeneralization (range f)) : GeneralizingMap f := by
  intro x y e
  obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩
  exact ⟨_, hf.specializes_iff.mp e, rfl⟩

/--
lemma `Topology.IsOpenEmbedding.generalizingMap` / 引理 `Topology.IsOpenEmbedding.generalizingMap`

English:
lemma Topology.IsOpenEmbedding.generalizingMap
  given: (hf : IsOpenEmbedding f)
  statement: GeneralizingMap f
  proof: hf.isInducing.generalizingMap hf.isOpen_range.stableUnderGeneralization

中文:
引理 Topology.IsOpenEmbedding.generalizingMap
  条件: (hf : IsOpenEmbedding f)
  结论: GeneralizingMap f
  证明: hf.isInducing.generalizingMap hf.isOpen_range.stableUnderGeneralization

Depends on / 依赖: generalizingMap, hf.isInducing.generalizingMap, hf.isOpen_range.stableUnderGeneralization, isInducing, isOpen_range, stableUnderGeneralization
-/
lemma Topology.IsOpenEmbedding.generalizingMap (hf : IsOpenEmbedding f) : GeneralizingMap f :=
  hf.isInducing.generalizingMap hf.isOpen_range.stableUnderGeneralization

/--
lemma `SpecializingMap.stableUnderSpecialization_range` / 引理 `SpecializingMap.stableUnderSpecialization_range`

English:
lemma SpecializingMap.stableUnderSpecialization_range
  given: (h : SpecializingMap f)
  proof: @image_univ _ _ f ▸ stableUnderSpecialization_univ.image h

中文:
引理 SpecializingMap.stableUnderSpecialization_range
  条件: (h : SpecializingMap f)
  证明: @image_univ _ _ f ▸ stableUnderSpecialization_univ.image h

Depends on / 依赖: image_univ, stableUnderSpecialization_univ, stableUnderSpecialization_univ.image
-/
lemma SpecializingMap.stableUnderSpecialization_range (h : SpecializingMap f) :
    StableUnderSpecialization (range f) :=
  @image_univ _ _ f ▸ stableUnderSpecialization_univ.image h

/--
lemma `GeneralizingMap.stableUnderGeneralization_image` / 引理 `GeneralizingMap.stableUnderGeneralization_image`

English:
lemma GeneralizingMap.stableUnderGeneralization_image
  statement: (hf : GeneralizingMap f) {s : Set X}
  proof: IsUpperSet.image_fibration hf hs

中文:
引理 GeneralizingMap.stableUnderGeneralization_image
  结论: (hf : GeneralizingMap f) {s : Set X}
  证明: IsUpperSet.image_fibration hf hs

Depends on / 依赖: IsUpperSet, IsUpperSet.image_fibration, image_fibration
-/
lemma GeneralizingMap.stableUnderGeneralization_image (hf : GeneralizingMap f) {s : Set X}
    (hs : StableUnderGeneralization s) : StableUnderGeneralization (f '' s) :=
  IsUpperSet.image_fibration hf hs

/--
lemma `GeneralizingMap_iff_stableUnderGeneralization_image` / 引理 `GeneralizingMap_iff_stableUnderGeneralization_image`

English:
lemma GeneralizingMap_iff_stableUnderGeneralization_image
  proof: Relation.fibration_iff_isUpperSet_image

alias StableUnderGeneralization.image := GeneralizingMap.stableUnderGeneralization_image

中文:
引理 GeneralizingMap_iff_stableUnderGeneralization_image
  证明: Relation.fibration_iff_isUpperSet_image

alias StableUnderGeneralization.image := GeneralizingMap.stableUnderGeneralization_image

Depends on / 依赖: Relation, Relation.fibration_iff_isUpperSet_image, fibration_iff_isUpperSet_image
-/
lemma GeneralizingMap_iff_stableUnderGeneralization_image :
    GeneralizingMap f ↔ forall s, StableUnderGeneralization s -> StableUnderGeneralization (f '' s) :=
  Relation.fibration_iff_isUpperSet_image

alias StableUnderGeneralization.image := GeneralizingMap.stableUnderGeneralization_image

/--
lemma `GeneralizingMap.stableUnderGeneralization_range` / 引理 `GeneralizingMap.stableUnderGeneralization_range`

English:
lemma GeneralizingMap.stableUnderGeneralization_range
  given: (h : GeneralizingMap f)
  proof: @image_univ _ _ f ▸ stableUnderGeneralization_univ.image h

中文:
引理 GeneralizingMap.stableUnderGeneralization_range
  条件: (h : GeneralizingMap f)
  证明: @image_univ _ _ f ▸ stableUnderGeneralization_univ.image h

Depends on / 依赖: image_univ, stableUnderGeneralization_univ, stableUnderGeneralization_univ.image
-/
lemma GeneralizingMap.stableUnderGeneralization_range (h : GeneralizingMap f) :
    StableUnderGeneralization (range f) :=
  @image_univ _ _ f ▸ stableUnderGeneralization_univ.image h

/--
lemma `GeneralizingMap.comp` / 引理 `GeneralizingMap.comp`

English:
lemma GeneralizingMap.comp
  statement: {f : X -> Y} {g : Y -> Z}
  proof: by
  simp only [GeneralizingMap_iff_stableUnderGeneralization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

中文:
引理 GeneralizingMap.comp
  结论: {f : X -> Y} {g : Y -> Z}
  证明: by
  simp only [GeneralizingMap_iff_stableUnderGeneralization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

Depends on / 依赖: GeneralizingMap_iff_stableUnderGeneralization_image, Set.image_comp, image_comp
-/
lemma GeneralizingMap.comp {f : X -> Y} {g : Y -> Z}
    (hf : GeneralizingMap f) (hg : GeneralizingMap g) :
    GeneralizingMap (g ∘ f) := by
  simp only [GeneralizingMap_iff_stableUnderGeneralization_image, Set.image_comp] at *
  exact fun s h => hg _ (hf _ h)

/-!
### `Inseparable` relation
-/

local infixl:0 " ~ᵢ " => Inseparable

/--
theorem `inseparable_def` / 定理 `inseparable_def`

English:
theorem inseparable_def
  statement: (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y
  proof: Iff.rfl

中文:
定理 inseparable_def
  结论: (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inseparable_def : (x ~ᵢ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl

/--
theorem `inseparable_iff_specializes_and` / 定理 `inseparable_iff_specializes_and`

English:
theorem inseparable_iff_specializes_and
  statement: (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x
  proof: le_antisymm_iff

中文:
定理 inseparable_iff_specializes_and
  结论: (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x
  证明: le_antisymm_iff

Depends on / 依赖: le_antisymm_iff
-/
theorem inseparable_iff_specializes_and : (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iff

/--
theorem `Inseparable.specializes` / 定理 `Inseparable.specializes`

English:
theorem Inseparable.specializes
  given: (h : x ~ᵢ y)
  statement: x ⤳ y
  proof: h.le

中文:
定理 Inseparable.specializes
  条件: (h : x ~ᵢ y)
  结论: x ⤳ y
  证明: h.le

Depends on / 依赖: h.le
-/
theorem Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y := h.le

/--
theorem `Inseparable.specializes'` / 定理 `Inseparable.specializes'`

English:
theorem Inseparable.specializes'
  given: (h : x ~ᵢ y)
  statement: y ⤳ x
  proof: h.ge

中文:
定理 Inseparable.specializes'
  条件: (h : x ~ᵢ y)
  结论: y ⤳ x
  证明: h.ge

Depends on / 依赖: h.ge
-/
theorem Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x := h.ge

/--
theorem `Specializes.antisymm` / 定理 `Specializes.antisymm`

English:
theorem Specializes.antisymm
  given: (h₁ : x ⤳ y) (h₂ : y ⤳ x)
  statement: x ~ᵢ y
  proof: le_antisymm h₁ h₂

中文:
定理 Specializes.antisymm
  条件: (h₁ : x ⤳ y) (h₂ : y ⤳ x)
  结论: x ~ᵢ y
  证明: le_antisymm h₁ h₂

Depends on / 依赖: le_antisymm
-/
theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ᵢ y :=
  le_antisymm h₁ h₂

/--
theorem `inseparable_iff_forall_isOpen` / 定理 `inseparable_iff_forall_isOpen`

English:
theorem inseparable_iff_forall_isOpen
  statement: (x ~ᵢ y) ↔ forall s : Set X, IsOpen s -> (x in s ↔ y in s)
  proof: by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]

中文:
定理 inseparable_iff_forall_isOpen
  结论: (x ~ᵢ y) ↔ 对任意 s : Set X, IsOpen s -> (x in s ↔ y in s)
  证明: by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]

Depends on / 依赖: Iff.comm, forall_and, iff_def, inseparable_iff_specializes_and, specializes_iff_forall_open
-/
theorem inseparable_iff_forall_isOpen : (x ~ᵢ y) ↔ forall s : Set X, IsOpen s -> (x in s ↔ y in s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]

/--
theorem `not_inseparable_iff_exists_open` / 定理 `not_inseparable_iff_exists_open`

English:
theorem not_inseparable_iff_exists_open
  proof: by
  simp [inseparable_iff_forall_isOpen, ← xor_iff_not_iff]

中文:
定理 not_inseparable_iff_exists_open
  证明: by
  simp [inseparable_iff_forall_isOpen, ← xor_iff_not_iff]

Depends on / 依赖: inseparable_iff_forall_isOpen, xor_iff_not_iff
-/
theorem not_inseparable_iff_exists_open :
    ¬(x ~ᵢ y) ↔ exists s : Set X, IsOpen s ∧ Xor (x in s) (y in s) := by
  simp [inseparable_iff_forall_isOpen, ← xor_iff_not_iff]

/--
theorem `inseparable_iff_forall_isClosed` / 定理 `inseparable_iff_forall_isClosed`

English:
theorem inseparable_iff_forall_isClosed
  statement: (x ~ᵢ y) ↔ forall s : Set X, IsClosed s -> (x in s ↔ y in s)
  proof: by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]

中文:
定理 inseparable_iff_forall_isClosed
  结论: (x ~ᵢ y) ↔ 对任意 s : Set X, IsClosed s -> (x in s ↔ y in s)
  证明: by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]

Depends on / 依赖: forall_and, iff_def, inseparable_iff_specializes_and, specializes_iff_forall_closed
-/
theorem inseparable_iff_forall_isClosed : (x ~ᵢ y) ↔ forall s : Set X, IsClosed s -> (x in s ↔ y in s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]

/--
theorem `inseparable_iff_mem_closure` / 定理 `inseparable_iff_mem_closure`

English:
theorem inseparable_iff_mem_closure
  proof: inseparable_iff_specializes_and.trans by simp only [specializes_iff_mem_closure, and_comm]

中文:
定理 inseparable_iff_mem_closure
  证明: inseparable_iff_specializes_and.trans by simp only [specializes_iff_mem_closure, and_comm]

Depends on / 依赖: and_comm, inseparable_iff_specializes_and, inseparable_iff_specializes_and.trans, specializes_iff_mem_closure
-/
theorem inseparable_iff_mem_closure :
    (x ~ᵢ y) ↔ x in closure ({y} : Set X) ∧ y in closure ({x} : Set X) :=
inseparable_iff_specializes_and.trans by simp only [specializes_iff_mem_closure, and_comm]

/--
theorem `inseparable_iff_closure_eq` / 定理 `inseparable_iff_closure_eq`

English:
theorem inseparable_iff_closure_eq
  statement: (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y}
  proof: by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]

中文:
定理 inseparable_iff_closure_eq
  结论: (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y}
  证明: by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]

Depends on / 依赖: eq_comm, inseparable_iff_specializes_and, specializes_iff_closure_subset, subset_antisymm_iff
-/
theorem inseparable_iff_closure_eq : (x ~ᵢ y) ↔ closure ({x} : Set X) = closure {y} := by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]

/--
theorem `inseparable_of_nhdsWithin_eq` / 定理 `inseparable_of_nhdsWithin_eq`

English:
theorem inseparable_of_nhdsWithin_eq
  given: (hx : x in s) (hy : y in s) (h : 𝓝[s] x = 𝓝[s] y)
  statement: x ~ᵢ y
  proof: (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)

中文:
定理 inseparable_of_nhdsWithin_eq
  条件: (hx : x in s) (hy : y in s) (h : 𝓝[s] x = 𝓝[s] y)
  结论: x ~ᵢ y
  证明: (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)

Depends on / 依赖: antisymm, h.ge, h.le, specializes_of_nhdsWithin
-/
theorem inseparable_of_nhdsWithin_eq (hx : x in s) (hy : y in s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ᵢ y :=
  (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)

/--
theorem `Topology.IsInducing.inseparable_iff` / 定理 `Topology.IsInducing.inseparable_iff`

English:
theorem Topology.IsInducing.inseparable_iff
  given: (hf : IsInducing f)
  statement: (f x ~ᵢ f y) ↔ (x ~ᵢ y)
  proof: by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]

中文:
定理 Topology.IsInducing.inseparable_iff
  条件: (hf : IsInducing f)
  结论: (f x ~ᵢ f y) ↔ (x ~ᵢ y)
  证明: by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]

Depends on / 依赖: hf.specializes_iff, inseparable_iff_specializes_and, specializes_iff
-/
theorem Topology.IsInducing.inseparable_iff (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y) := by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]

/--
theorem `subtype_inseparable_iff` / 定理 `subtype_inseparable_iff`

English:
theorem subtype_inseparable_iff
  given: {p : X -> Prop} (x y : Subtype p)
  statement: (x ~ᵢ y) ↔ ((x : X) ~ᵢ y)
  proof: IsInducing.subtypeVal.inseparable_iff.symm

中文:
定理 subtype_inseparable_iff
  条件: {p : X -> 命题} (x y : Subtype p)
  结论: (x ~ᵢ y) ↔ ((x : X) ~ᵢ y)
  证明: IsInducing.subtypeVal.inseparable_iff.symm

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.inseparable_iff.symm, inseparable_iff, subtypeVal
-/
theorem subtype_inseparable_iff {p : X -> Prop} (x y : Subtype p) : (x ~ᵢ y) ↔ ((x : X) ~ᵢ y) :=
  IsInducing.subtypeVal.inseparable_iff.symm

/--
theorem `inseparable_prod` / 定理 `inseparable_prod`

English:
theorem inseparable_prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y}
  proof: by
  simp only [Inseparable, nhds_prod_eq, Filter.prod_inj]

中文:
定理 inseparable_prod
  条件: {x₁ x₂ : X} {y₁ y₂ : Y}
  证明: by
  simp only [Inseparable, nhds_prod_eq, Filter.prod_inj]
-/
@[simp] theorem inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} :
    ((x₁, y₁) ~ᵢ (x₂, y₂)) ↔ (x₁ ~ᵢ x₂) ∧ (y₁ ~ᵢ y₂) := by
  simp only [Inseparable, nhds_prod_eq, Filter.prod_inj]

/--
theorem `Inseparable.prod` / 定理 `Inseparable.prod`

English:
theorem Inseparable.prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂)
  proof: inseparable_prod.2 ⟨hx, hy⟩

@[simp]

中文:
定理 Inseparable.prod
  条件: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂)
  证明: inseparable_prod.2 ⟨hx, hy⟩

@[simp]

Depends on / 依赖: inseparable_prod
-/
theorem Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x₂) (hy : y₁ ~ᵢ y₂) :
    (x₁, y₁) ~ᵢ (x₂, y₂) :=
  inseparable_prod.2 ⟨hx, hy⟩

@[simp]
/--
theorem `inseparable_pi` / 定理 `inseparable_pi`

English:
theorem inseparable_pi
  given: {f g : forall i, A i}
  statement: (f ~ᵢ g) ↔ forall i, f i ~ᵢ g i
  proof: by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]

中文:
定理 inseparable_pi
  条件: {f g : 对任意 i, A i}
  结论: (f ~ᵢ g) ↔ 对任意 i, f i ~ᵢ g i
  证明: by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]

Depends on / 依赖: Inseparable, funext_iff, nhds_pi, pi_inj
-/
theorem inseparable_pi {f g : forall i, A i} : (f ~ᵢ g) ↔ forall i, f i ~ᵢ g i := by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]

namespace Inseparable

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (x : X)
  statement: x ~ᵢ x
  proof: Eq.refl (𝓝 x)

中文:
定理 refl
  条件: (x : X)
  结论: x ~ᵢ x
  证明: Eq.refl (𝓝 x)

Depends on / 依赖: Eq.refl
-/
theorem refl (x : X) : x ~ᵢ x :=
  Eq.refl (𝓝 x)

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: x ~ᵢ x
  proof: refl x

中文:
定理 rfl
  结论: x ~ᵢ x
  证明: refl x
-/
theorem rfl : x ~ᵢ x :=
  refl x

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: (e : x = y)
  statement: Inseparable x y
  proof: e ▸ refl x

@[symm]
nonrec theorem symm (h : x ~ᵢ y) : y ~ᵢ x := h.symm

@[trans]
nonrec theorem trans (h₁ : x ~ᵢ y) (h₂ : y ~ᵢ z) : x ~ᵢ z := h₁.trans h₂

中文:
定理 of_eq
  条件: (e : x = y)
  结论: Inseparable x y
  证明: e ▸ refl x

@[symm]
nonrec theorem symm (h : x ~ᵢ y) : y ~ᵢ x := h.symm

@[trans]
nonrec theorem trans (h₁ : x ~ᵢ y) (h₂ : y ~ᵢ z) : x ~ᵢ z := h₁.trans h₂
-/
theorem of_eq (e : x = y) : Inseparable x y :=
  e ▸ refl x

@[symm]
nonrec theorem symm (h : x ~ᵢ y) : y ~ᵢ x := h.symm

@[trans]
nonrec theorem trans (h₁ : x ~ᵢ y) (h₂ : y ~ᵢ z) : x ~ᵢ z := h₁.trans h₂

/--
theorem `nhds_eq` / 定理 `nhds_eq`

English:
theorem nhds_eq
  given: (h : x ~ᵢ y)
  statement: 𝓝 x = 𝓝 y
  proof: h

中文:
定理 nhds_eq
  条件: (h : x ~ᵢ y)
  结论: 𝓝 x = 𝓝 y
  证明: h
-/
theorem nhds_eq (h : x ~ᵢ y) : 𝓝 x = 𝓝 y := h

/--
theorem `mem_open_iff` / 定理 `mem_open_iff`

English:
theorem mem_open_iff
  given: (h : x ~ᵢ y) (hs : IsOpen s)
  statement: x in s ↔ y in s
  proof: inseparable_iff_forall_isOpen.1 h s hs

中文:
定理 mem_open_iff
  条件: (h : x ~ᵢ y) (hs : IsOpen s)
  结论: x in s ↔ y in s
  证明: inseparable_iff_forall_isOpen.1 h s hs

Depends on / 依赖: inseparable_iff_forall_isOpen
-/
theorem mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x in s ↔ y in s :=
  inseparable_iff_forall_isOpen.1 h s hs

/--
theorem `mem_closed_iff` / 定理 `mem_closed_iff`

English:
theorem mem_closed_iff
  given: (h : x ~ᵢ y) (hs : IsClosed s)
  statement: x in s ↔ y in s
  proof: inseparable_iff_forall_isClosed.1 h s hs

中文:
定理 mem_closed_iff
  条件: (h : x ~ᵢ y) (hs : IsClosed s)
  结论: x in s ↔ y in s
  证明: inseparable_iff_forall_isClosed.1 h s hs

Depends on / 依赖: inseparable_iff_forall_isClosed
-/
theorem mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s) : x in s ↔ y in s :=
  inseparable_iff_forall_isClosed.1 h s hs

/--
theorem `map_of_continuousWithinAt` / 定理 `map_of_continuousWithinAt`

English:
theorem map_of_continuousWithinAt
  statement: {s t : Set X} (h : x ~ᵢ y)
  proof: (h.specializes.map_of_continuousWithinAt hfy hx).antisymm
    (h.specializes'.map_of_continuousWithinAt hfx hy)

中文:
定理 map_of_continuousWithinAt
  结论: {s t : Set X} (h : x ~ᵢ y)
  证明: (h.specializes.map_of_continuousWithinAt hfy hx).antisymm
    (h.specializes'.map_of_continuousWithinAt hfx hy)

Depends on / 依赖: antisymm, h.specializes, h.specializes.map_of_continuousWithinAt, map_of_continuousWithinAt, specializes
-/
theorem map_of_continuousWithinAt {s t : Set X} (h : x ~ᵢ y)
    (hfx : ContinuousWithinAt f s x) (hfy : ContinuousWithinAt f t y)
    (hx : x in t) (hy : y in s) : f x ~ᵢ f y :=
  (h.specializes.map_of_continuousWithinAt hfy hx).antisymm
    (h.specializes'.map_of_continuousWithinAt hfx hy)

/--
theorem `map_of_continuousOn` / 定理 `map_of_continuousOn`

English:
theorem map_of_continuousOn
  statement: {s : Set X} (h : x ~ᵢ y)
  proof: h.map_of_continuousWithinAt (hf.continuousWithinAt hx) (hf.continuousWithinAt hy) hx hy

中文:
定理 map_of_continuousOn
  结论: {s : Set X} (h : x ~ᵢ y)
  证明: h.map_of_continuousWithinAt (hf.continuousWithinAt hx) (hf.continuousWithinAt hy) hx hy

Depends on / 依赖: continuousWithinAt, h.map_of_continuousWithinAt, hf.continuousWithinAt, map_of_continuousWithinAt
-/
theorem map_of_continuousOn {s : Set X} (h : x ~ᵢ y)
    (hf : ContinuousOn f s) (hx : x in s) (hy : y in s) : f x ~ᵢ f y :=
  h.map_of_continuousWithinAt (hf.continuousWithinAt hx) (hf.continuousWithinAt hy) hx hy

/--
theorem `map_of_continuousAt` / 定理 `map_of_continuousAt`

English:
theorem map_of_continuousAt
  given: (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y)
  proof: h.map_of_continuousWithinAt hx.continuousWithinAt hy.continuousWithinAt (mem_univ x) (mem_univ y)

中文:
定理 map_of_continuousAt
  条件: (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y)
  证明: h.map_of_continuousWithinAt hx.continuousWithinAt hy.continuousWithinAt (mem_univ x) (mem_univ y)

Depends on / 依赖: continuousWithinAt, h.map_of_continuousWithinAt, hx.continuousWithinAt, hy.continuousWithinAt, map_of_continuousWithinAt, mem_univ
-/
theorem map_of_continuousAt (h : x ~ᵢ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) :
    f x ~ᵢ f y :=
  h.map_of_continuousWithinAt hx.continuousWithinAt hy.continuousWithinAt (mem_univ x) (mem_univ y)

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (h : x ~ᵢ y) (hf : Continuous f)
  statement: f x ~ᵢ f y
  proof: h.map_of_continuousAt hf.continuousAt hf.continuousAt

中文:
定理 map
  条件: (h : x ~ᵢ y) (hf : Continuous f)
  结论: f x ~ᵢ f y
  证明: h.map_of_continuousAt hf.continuousAt hf.continuousAt

Depends on / 依赖: continuousAt, h.map_of_continuousAt, hf.continuousAt, map_of_continuousAt
-/
theorem map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y :=
  h.map_of_continuousAt hf.continuousAt hf.continuousAt

end Inseparable

/--
theorem `IsClosed.not_inseparable` / 定理 `IsClosed.not_inseparable`

English:
theorem IsClosed.not_inseparable
  given: (hs : IsClosed s) (hx : x in s) (hy : y ∉ s)
  statement: ¬(x ~ᵢ y)
  proof: fun h =>
hy (h.mem_closed_iff hs).1 hx

中文:
定理 IsClosed.not_inseparable
  条件: (hs : IsClosed s) (hx : x in s) (hy : y ∉ s)
  结论: ¬(x ~ᵢ y)
  证明: fun h =>
hy (h.mem_closed_iff hs).1 hx
-/
theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x in s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
hy (h.mem_closed_iff hs).1 hx

/--
theorem `IsOpen.not_inseparable` / 定理 `IsOpen.not_inseparable`

English:
theorem IsOpen.not_inseparable
  given: (hs : IsOpen s) (hx : x in s) (hy : y ∉ s)
  statement: ¬(x ~ᵢ y)
  proof: fun h =>
hy (h.mem_open_iff hs).1 hx

中文:
定理 IsOpen.not_inseparable
  条件: (hs : IsOpen s) (hx : x in s) (hy : y ∉ s)
  结论: ¬(x ~ᵢ y)
  证明: fun h =>
hy (h.mem_open_iff hs).1 hx
-/
theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x in s) (hy : y ∉ s) : ¬(x ~ᵢ y) := fun h =>
hy (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `Inseparable` relation.
-/

variable (X) in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (SeparationQuotient X)
  body: inferInstanceAs TopologicalSpace (Quotient _)

中文:
实例 :
  签名: TopologicalSpace (SeparationQuotient X)
  定义体: inferInstanceAs TopologicalSpace (Quotient _)

Depends on / 依赖: Quotient, TopologicalSpace
-/
instance : TopologicalSpace (SeparationQuotient X) :=
inferInstanceAs TopologicalSpace (Quotient _)

variable {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : X -> SeparationQuotient X
  body: Quotient.mk''

中文:
定义 mk
  签名: : X -> SeparationQuotient X
  定义体: Quotient.mk''

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk : X -> SeparationQuotient X := Quotient.mk''

/--
theorem `isQuotientMap_mk` / 定理 `isQuotientMap_mk`

English:
theorem isQuotientMap_mk
  statement: IsQuotientMap (mk : X -> SeparationQuotient X)
  proof: isQuotientMap_quot_mk

@[fun_prop, continuity]

中文:
定理 isQuotientMap_mk
  结论: IsQuotientMap (mk : X -> SeparationQuotient X)
  证明: isQuotientMap_quot_mk

@[fun_prop, continuity]

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_mk : IsQuotientMap (mk : X -> SeparationQuotient X) :=
  isQuotientMap_quot_mk

@[fun_prop, continuity]
/--
theorem `continuous_mk` / 定理 `continuous_mk`

English:
theorem continuous_mk
  statement: Continuous (mk : X -> SeparationQuotient X)
  proof: continuous_quot_mk

@[simp]

中文:
定理 continuous_mk
  结论: Continuous (mk : X -> SeparationQuotient X)
  证明: continuous_quot_mk

@[simp]

Depends on / 依赖: continuous_quot_mk
-/
theorem continuous_mk : Continuous (mk : X -> SeparationQuotient X) :=
  continuous_quot_mk

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  statement: mk x = mk y ↔ (x ~ᵢ y)
  proof: Quotient.eq''

中文:
定理 mk_eq_mk
  结论: mk x = mk y ↔ (x ~ᵢ y)
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y) :=
  Quotient.eq''

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {P : SeparationQuotient X -> Prop}
  statement: (forall x, P x) ↔ forall x, P (.mk x)
  proof: Quotient.forall

中文:
定理 «forall»
  条件: {P : SeparationQuotient X -> 命题}
  结论: (对任意 x, P x) ↔ 对任意 x, P (.mk x)
  证明: Quotient.forall
-/
protected theorem «forall» {P : SeparationQuotient X -> Prop} : (forall x, P x) ↔ forall x, P (.mk x) :=
  Quotient.forall

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {P : SeparationQuotient X -> Prop}
  statement: (exists x, P x) ↔ exists x, P (.mk x)
  proof: Quotient.exists

中文:
定理 «exists»
  条件: {P : SeparationQuotient X -> 命题}
  结论: (存在 x, P x) ↔ 存在 x, P (.mk x)
  证明: Quotient.exists
-/
protected theorem «exists» {P : SeparationQuotient X -> Prop} : (exists x, P x) ↔ exists x, P (.mk x) :=
  Quotient.exists

/--
theorem `surjective_mk` / 定理 `surjective_mk`

English:
theorem surjective_mk
  statement: Surjective (mk : X -> SeparationQuotient X)
  proof: Quot.mk_surjective

@[simp]

中文:
定理 surjective_mk
  结论: Surjective (mk : X -> SeparationQuotient X)
  证明: Quot.mk_surjective

@[simp]

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem surjective_mk : Surjective (mk : X -> SeparationQuotient X) :=
  Quot.mk_surjective

@[simp]
/--
theorem `range_mk` / 定理 `range_mk`

English:
theorem range_mk
  statement: range (mk : X -> SeparationQuotient X) = univ
  proof: surjective_mk.range_eq

中文:
定理 range_mk
  结论: range (mk : X -> SeparationQuotient X) = univ
  证明: surjective_mk.range_eq

Depends on / 依赖: range_eq, surjective_mk, surjective_mk.range_eq
-/
theorem range_mk : range (mk : X -> SeparationQuotient X) = univ :=
  surjective_mk.range_eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty (SeparationQuotient X)
  body: Nonempty.map mk ‹_›

中文:
实例 [Nonempty
  签名: X] : Nonempty (SeparationQuotient X)
  定义体: Nonempty.map mk ‹_›

Depends on / 依赖: Nonempty, Nonempty.map
-/
instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: X] : Inhabited (SeparationQuotient X)
  body: ⟨mk default⟩

中文:
实例 [Inhabited
  签名: X] : Inhabited (SeparationQuotient X)
  定义体: ⟨mk default⟩
-/
instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: X] : Subsingleton (SeparationQuotient X)
  body: surjective_mk.subsingleton

@[simp]

中文:
实例 [Subsingleton
  签名: X] : Subsingleton (SeparationQuotient X)
  定义体: surjective_mk.subsingleton

@[simp]

Depends on / 依赖: subsingleton, surjective_mk, surjective_mk.subsingleton
-/
instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.subsingleton

@[simp]
/--
theorem `inseparableSetoid_eq_top_iff` / 定理 `inseparableSetoid_eq_top_iff`

English:
theorem inseparableSetoid_eq_top_iff
  given: [TopologicalSpace α]
  proof: Setoid.eq_top_iff.trans TopologicalSpace.indiscrete_iff_forall_inseparable.symm

中文:
定理 inseparableSetoid_eq_top_iff
  条件: [TopologicalSpace α]
  证明: Setoid.eq_top_iff.trans TopologicalSpace.indiscrete_iff_forall_inseparable.symm

Depends on / 依赖: Setoid, Setoid.eq_top_iff.trans, TopologicalSpace, TopologicalSpace.indiscrete_iff_forall_inseparable.symm, eq_top_iff, indiscrete_iff_forall_inseparable
-/
theorem inseparableSetoid_eq_top_iff [TopologicalSpace α] :
    inseparableSetoid α = ⊤ ↔ IndiscreteTopology α :=
  Setoid.eq_top_iff.trans TopologicalSpace.indiscrete_iff_forall_inseparable.symm

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  given: [TopologicalSpace α]
  proof: Quotient.subsingleton_iff.trans inseparableSetoid_eq_top_iff

中文:
定理 subsingleton_iff
  条件: [TopologicalSpace α]
  证明: Quotient.subsingleton_iff.trans inseparableSetoid_eq_top_iff

Depends on / 依赖: Quotient, Quotient.subsingleton_iff.trans, inseparableSetoid_eq_top_iff, subsingleton_iff
-/
theorem subsingleton_iff [TopologicalSpace α] :
    Subsingleton (SeparationQuotient α) ↔ IndiscreteTopology α :=
  Quotient.subsingleton_iff.trans inseparableSetoid_eq_top_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [IndiscreteTopology α] : Subsingleton (SeparationQuotient α)
  body: subsingleton_iff.2 ‹_›

中文:
实例 [TopologicalSpace
  签名: α] [IndiscreteTopology α] : Subsingleton (SeparationQuotient α)
  定义体: subsingleton_iff.2 ‹_›

Depends on / 依赖: subsingleton_iff
-/
instance [TopologicalSpace α] [IndiscreteTopology α] : Subsingleton (SeparationQuotient α) :=
  subsingleton_iff.2 ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [IndiscreteTopology α] {p
  body: by
  simp [TopologicalSpace.indiscrete_iff_forall_inseparable, subtype_inseparable_iff]

中文:
实例 [TopologicalSpace
  签名: α] [IndiscreteTopology α] {p
  定义体: by
  simp [TopologicalSpace.indiscrete_iff_forall_inseparable, subtype_inseparable_iff]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.indiscrete_iff_forall_inseparable, indiscrete_iff_forall_inseparable, subtype_inseparable_iff
-/
instance [TopologicalSpace α] [IndiscreteTopology α] {p : α -> Prop} :
    IndiscreteTopology (Subtype p) := by
  simp [TopologicalSpace.indiscrete_iff_forall_inseparable, subtype_inseparable_iff]

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  given: [TopologicalSpace α]
  proof: by
  simpa [not_subsingleton_iff_nontrivial] using subsingleton_iff.not

中文:
定理 nontrivial_iff
  条件: [TopologicalSpace α]
  证明: by
  simpa [not_subsingleton_iff_nontrivial] using subsingleton_iff.not

Depends on / 依赖: not_subsingleton_iff_nontrivial, subsingleton_iff, subsingleton_iff.not
-/
theorem nontrivial_iff [TopologicalSpace α] :
    Nontrivial (SeparationQuotient α) ↔ NontrivialTopology α := by
  simpa [not_subsingleton_iff_nontrivial] using subsingleton_iff.not

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [NontrivialTopology α] : Nontrivial (SeparationQuotient α)
  body: nontrivial_iff.2 ‹_›

中文:
实例 [TopologicalSpace
  签名: α] [NontrivialTopology α] : Nontrivial (SeparationQuotient α)
  定义体: nontrivial_iff.2 ‹_›

Depends on / 依赖: nontrivial_iff
-/
instance [TopologicalSpace α] [NontrivialTopology α] : Nontrivial (SeparationQuotient α) :=
  nontrivial_iff.2 ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: X] : One (SeparationQuotient X)
  body: ⟨mk 1⟩

中文:
实例 [One
  签名: X] : One (SeparationQuotient X)
  定义体: ⟨mk 1⟩
-/
@[to_additive] instance [One X] : One (SeparationQuotient X) := ⟨mk 1⟩

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: [One X]
  statement: mk (1 : X) = 1
  proof: rfl

中文:
定理 mk_one
  条件: [One X]
  结论: mk (1 : X) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] theorem mk_one [One X] : mk (1 : X) = 1 := rfl

/--
theorem `preimage_image_mk_open` / 定理 `preimage_image_mk_open`

English:
theorem preimage_image_mk_open
  given: (hs : IsOpen s)
  statement: mk ⁻¹' mk '' s = s
  proof: by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

中文:
定理 preimage_image_mk_open
  条件: (hs : IsOpen s)
  结论: mk ⁻¹' mk '' s = s
  证明: by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

Depends on / 依赖: Subset, Subset.antisymm, antisymm, mem_open_iff, mk_eq_mk, subset_preimage_image
-/
theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' mk '' s = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

/--
theorem `isOpenMap_mk` / 定理 `isOpenMap_mk`

English:
theorem isOpenMap_mk
  statement: IsOpenMap (mk : X -> SeparationQuotient X)
  proof: fun s hs =>
isQuotientMap_mk.isOpen_preimage.1 by rwa [preimage_image_mk_open hs]

中文:
定理 isOpenMap_mk
  结论: IsOpenMap (mk : X -> SeparationQuotient X)
  证明: fun s hs =>
isQuotientMap_mk.isOpen_preimage.1 by rwa [preimage_image_mk_open hs]
-/
theorem isOpenMap_mk : IsOpenMap (mk : X -> SeparationQuotient X) := fun s hs =>
isQuotientMap_mk.isOpen_preimage.1 by rwa [preimage_image_mk_open hs]

/--
theorem `isOpenQuotientMap_mk` / 定理 `isOpenQuotientMap_mk`

English:
theorem isOpenQuotientMap_mk
  statement: IsOpenQuotientMap (mk : X -> SeparationQuotient X)
  proof: ⟨surjective_mk, continuous_mk, isOpenMap_mk⟩

中文:
定理 isOpenQuotientMap_mk
  结论: IsOpenQuotientMap (mk : X -> SeparationQuotient X)
  证明: ⟨surjective_mk, continuous_mk, isOpenMap_mk⟩

Depends on / 依赖: continuous_mk, isOpenMap_mk, surjective_mk
-/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : X -> SeparationQuotient X) :=
  ⟨surjective_mk, continuous_mk, isOpenMap_mk⟩

/--
theorem `preimage_image_mk_closed` / 定理 `preimage_image_mk_closed`

English:
theorem preimage_image_mk_closed
  given: (hs : IsClosed s)
  statement: mk ⁻¹' mk '' s = s
  proof: by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

中文:
定理 preimage_image_mk_closed
  条件: (hs : IsClosed s)
  结论: mk ⁻¹' mk '' s = s
  证明: by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

Depends on / 依赖: Subset, Subset.antisymm, antisymm, mem_closed_iff, mk_eq_mk, subset_preimage_image
-/
theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' mk '' s = s := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

/--
theorem `isInducing_mk` / 定理 `isInducing_mk`

English:
theorem isInducing_mk
  statement: IsInducing (mk : X -> SeparationQuotient X)
  proof: ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩

中文:
定理 isInducing_mk
  结论: IsInducing (mk : X -> SeparationQuotient X)
  证明: ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩

Depends on / 依赖: continuous_iff_le_induced, continuous_mk, isOpenMap_mk, le_antisymm, preimage_image_mk_open
-/
theorem isInducing_mk : IsInducing (mk : X -> SeparationQuotient X) :=
  ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩

/--
theorem `isClosedMap_mk` / 定理 `isClosedMap_mk`

English:
theorem isClosedMap_mk
  statement: IsClosedMap (mk : X -> SeparationQuotient X)
  proof: isInducing_mk.isClosedMap by rw [range_mk]; exact isClosed_univ

@[simp]

中文:
定理 isClosedMap_mk
  结论: IsClosedMap (mk : X -> SeparationQuotient X)
  证明: isInducing_mk.isClosedMap by rw [range_mk]; exact isClosed_univ

@[simp]

Depends on / 依赖: isClosedMap, isClosed_univ, isInducing_mk, isInducing_mk.isClosedMap, range_mk
-/
theorem isClosedMap_mk : IsClosedMap (mk : X -> SeparationQuotient X) :=
isInducing_mk.isClosedMap by rw [range_mk]; exact isClosed_univ

@[simp]
/--
theorem `comap_mk_nhds_mk` / 定理 `comap_mk_nhds_mk`

English:
theorem comap_mk_nhds_mk
  statement: comap mk (𝓝 (mk x)) = 𝓝 x
  proof: (isInducing_mk.nhds_eq_comap _).symm

@[simp]

中文:
定理 comap_mk_nhds_mk
  结论: comap mk (𝓝 (mk x)) = 𝓝 x
  证明: (isInducing_mk.nhds_eq_comap _).symm

@[simp]

Depends on / 依赖: isInducing_mk, isInducing_mk.nhds_eq_comap, nhds_eq_comap
-/
theorem comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
  (isInducing_mk.nhds_eq_comap _).symm

@[simp]
/--
theorem `comap_mk_nhdsSet_image` / 定理 `comap_mk_nhdsSet_image`

English:
theorem comap_mk_nhdsSet_image
  statement: comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s
  proof: (isInducing_mk.nhdsSet_eq_comap _).symm

中文:
定理 comap_mk_nhdsSet_image
  结论: comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s
  证明: (isInducing_mk.nhdsSet_eq_comap _).symm

Depends on / 依赖: isInducing_mk, isInducing_mk.nhdsSet_eq_comap, nhdsSet_eq_comap
-/
theorem comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
  (isInducing_mk.nhdsSet_eq_comap _).symm

/--
theorem `map_mk_nhds` / 定理 `map_mk_nhds`

English:
theorem map_mk_nhds
  statement: map mk (𝓝 x) = 𝓝 (mk x)
  proof: by
  rw [← comap_mk_nhds_mk]; rw [map_comap_of_surjective surjective_mk]

中文:
定理 map_mk_nhds
  结论: map mk (𝓝 x) = 𝓝 (mk x)
  证明: by
  rw [← comap_mk_nhds_mk]; rw [map_comap_of_surjective surjective_mk]

Depends on / 依赖: comap_mk_nhds_mk, map_comap_of_surjective, surjective_mk
-/
theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [← comap_mk_nhds_mk]; rw [map_comap_of_surjective surjective_mk]

/--
theorem `map_mk_nhdsSet` / 定理 `map_mk_nhdsSet`

English:
theorem map_mk_nhdsSet
  statement: map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s)
  proof: by
  rw [← comap_mk_nhdsSet_image]; rw [map_comap_of_surjective surjective_mk]

中文:
定理 map_mk_nhdsSet
  结论: map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s)
  证明: by
  rw [← comap_mk_nhdsSet_image]; rw [map_comap_of_surjective surjective_mk]

Depends on / 依赖: comap_mk_nhdsSet_image, map_comap_of_surjective, surjective_mk
-/
theorem map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) := by
  rw [← comap_mk_nhdsSet_image]; rw [map_comap_of_surjective surjective_mk]

/--
theorem `comap_mk_nhdsSet` / 定理 `comap_mk_nhdsSet`

English:
theorem comap_mk_nhdsSet
  statement: comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t)
  proof: by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhdsSet_image]

中文:
定理 comap_mk_nhdsSet
  结论: comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t)
  证明: by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhdsSet_image]

Depends on / 依赖: comap_mk_nhdsSet_image, conv_lhs, image_preimage_eq, surjective_mk
-/
theorem comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) := by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhdsSet_image]

/--
theorem `preimage_mk_closure` / 定理 `preimage_mk_closure`

English:
theorem preimage_mk_closure
  statement: mk ⁻¹' closure t = closure (mk ⁻¹' t)
  proof: isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t

中文:
定理 preimage_mk_closure
  结论: mk ⁻¹' closure t = closure (mk ⁻¹' t)
  证明: isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t

Depends on / 依赖: continuous_mk, isOpenMap_mk, isOpenMap_mk.preimage_closure_eq_closure_preimage, preimage_closure_eq_closure_preimage
-/
theorem preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t

/--
theorem `preimage_mk_interior` / 定理 `preimage_mk_interior`

English:
theorem preimage_mk_interior
  statement: mk ⁻¹' interior t = interior (mk ⁻¹' t)
  proof: isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t

中文:
定理 preimage_mk_interior
  结论: mk ⁻¹' interior t = interior (mk ⁻¹' t)
  证明: isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t

Depends on / 依赖: continuous_mk, isOpenMap_mk, isOpenMap_mk.preimage_interior_eq_interior_preimage, preimage_interior_eq_interior_preimage
-/
theorem preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t

/--
theorem `preimage_mk_frontier` / 定理 `preimage_mk_frontier`

English:
theorem preimage_mk_frontier
  statement: mk ⁻¹' frontier t = frontier (mk ⁻¹' t)
  proof: isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t

中文:
定理 preimage_mk_frontier
  结论: mk ⁻¹' frontier t = frontier (mk ⁻¹' t)
  证明: isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t

Depends on / 依赖: continuous_mk, isOpenMap_mk, isOpenMap_mk.preimage_frontier_eq_frontier_preimage, preimage_frontier_eq_frontier_preimage
-/
theorem preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t

/--
theorem `image_mk_closure` / 定理 `image_mk_closure`

English:
theorem image_mk_closure
  statement: mk '' closure s = closure (mk '' s)
  proof: (image_closure_subset_closure_image continuous_mk).antisymm
    isClosedMap_mk.closure_image_subset _

中文:
定理 image_mk_closure
  结论: mk '' closure s = closure (mk '' s)
  证明: (image_closure_subset_closure_image continuous_mk).antisymm
    isClosedMap_mk.closure_image_subset _

Depends on / 依赖: antisymm, closure_image_subset, continuous_mk, image_closure_subset_closure_image, isClosedMap_mk, isClosedMap_mk.closure_image_subset
-/
theorem image_mk_closure : mk '' closure s = closure (mk '' s) :=
(image_closure_subset_closure_image continuous_mk).antisymm
    isClosedMap_mk.closure_image_subset _

/--
theorem `map_prod_map_mk_nhds` / 定理 `map_prod_map_mk_nhds`

English:
theorem map_prod_map_mk_nhds
  given: (x : X) (y : Y)
  proof: by
  rw [nhds_prod_eq]; rw [← prod_map_map_eq']; rw [map_mk_nhds]; rw [map_mk_nhds]; rw [nhds_prod_eq]

中文:
定理 map_prod_map_mk_nhds
  条件: (x : X) (y : Y)
  证明: by
  rw [nhds_prod_eq]; rw [← prod_map_map_eq']; rw [map_mk_nhds]; rw [map_mk_nhds]; rw [nhds_prod_eq]

Depends on / 依赖: map_mk_nhds, nhds_prod_eq, prod_map_map_eq
-/
theorem map_prod_map_mk_nhds (x : X) (y : Y) :
    map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) := by
  rw [nhds_prod_eq]; rw [← prod_map_map_eq']; rw [map_mk_nhds]; rw [map_mk_nhds]; rw [nhds_prod_eq]

/--
theorem `map_mk_nhdsWithin_preimage` / 定理 `map_mk_nhdsWithin_preimage`

English:
theorem map_mk_nhdsWithin_preimage
  given: (s : Set (SeparationQuotient X)) (x : X)
  proof: by
  rw [nhdsWithin]; rw [← comap_principal]; rw [Filter.push_pull]; rw [nhdsWithin]; rw [map_mk_nhds]

中文:
定理 map_mk_nhdsWithin_preimage
  条件: (s : Set (SeparationQuotient X)) (x : X)
  证明: by
  rw [nhdsWithin]; rw [← comap_principal]; rw [Filter.push_pull]; rw [nhdsWithin]; rw [map_mk_nhds]

Depends on / 依赖: Filter, Filter.push_pull, comap_principal, map_mk_nhds, nhdsWithin, push_pull
-/
theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin]; rw [← comap_principal]; rw [Filter.push_pull]; rw [nhdsWithin]; rw [map_mk_nhds]

/--
theorem `isQuotientMap_prodMap_mk` / 定理 `isQuotientMap_prodMap_mk`

English:
theorem isQuotientMap_prodMap_mk
  statement: IsQuotientMap (Prod.map mk mk : X × Y -> _)
  proof: (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).isQuotientMap

中文:
定理 isQuotientMap_prodMap_mk
  结论: IsQuotientMap (Prod.map mk mk : X × Y -> _)
  证明: (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).isQuotientMap

Depends on / 依赖: isOpenQuotientMap_mk, isOpenQuotientMap_mk.prodMap, isQuotientMap, prodMap
-/
theorem isQuotientMap_prodMap_mk : IsQuotientMap (Prod.map mk mk : X × Y -> _) :=
  (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).isQuotientMap

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : X -> α) (hf : forall x y, (x ~ᵢ y) -> f x = f y)
  body: fun x =>
  Quotient.liftOn' x f hf

@[simp]

中文:
定义 lift
  签名: (f : X -> α) (hf : 对任意 x y, (x ~ᵢ y) -> f x = f y)
  定义体: fun x =>
  Quotient.liftOn' x f hf

@[simp]
-/
def lift (f : X -> α) (hf : forall x y, (x ~ᵢ y) -> f x = f y) : SeparationQuotient X -> α := fun x =>
  Quotient.liftOn' x f hf

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y) (x : X)
  statement: lift f hf (mk x) = f x
  proof: rfl

@[simp]

中文:
定理 lift_mk
  条件: {f : X -> α} (hf : 对任意 x y, (x ~ᵢ y) -> f x = f y) (x : X)
  结论: lift f hf (mk x) = f x
  证明: rfl

@[simp]
-/
theorem lift_mk {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y) (x : X) : lift f hf (mk x) = f x :=
  rfl

@[simp]
/--
theorem `lift_comp_mk` / 定理 `lift_comp_mk`

English:
theorem lift_comp_mk
  given: {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y)
  statement: lift f hf ∘ mk = f
  proof: rfl

@[simp]

中文:
定理 lift_comp_mk
  条件: {f : X -> α} (hf : 对任意 x y, (x ~ᵢ y) -> f x = f y)
  结论: lift f hf ∘ mk = f
  证明: rfl

@[simp]
-/
theorem lift_comp_mk {f : X -> α} (hf : forall x y, (x ~ᵢ y) -> f x = f y) : lift f hf ∘ mk = f :=
  rfl

@[simp]
/--
theorem `tendsto_lift_nhds_mk` / 定理 `tendsto_lift_nhds_mk`

English:
theorem tendsto_lift_nhds_mk
  given: {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {l : Filter α}
  proof: by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]

中文:
定理 tendsto_lift_nhds_mk
  条件: {f : X -> α} {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y} {l : Filter α}
  证明: by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]

Depends on / 依赖: _iff, lift_comp_mk, map_mk_nhds, tendsto_map
-/
theorem tendsto_lift_nhds_mk {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]

@[simp]
/--
theorem `tendsto_lift_nhdsWithin_mk` / 定理 `tendsto_lift_nhdsWithin_mk`

English:
theorem tendsto_lift_nhdsWithin_mk
  statement: {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y}
  proof: by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]

中文:
定理 tendsto_lift_nhdsWithin_mk
  结论: {f : X -> α} {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y}
  证明: by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]

Depends on / 依赖: _iff, lift_comp_mk, map_mk_nhdsWithin_preimage, tendsto_map
-/
theorem tendsto_lift_nhdsWithin_mk {f : X -> α} {hf : forall x y, (x ~ᵢ y) -> f x = f y}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhdsWithin_preimage, tendsto_map'_iff, lift_comp_mk]

@[simp]
/--
theorem `continuousAt_lift` / 定理 `continuousAt_lift`

English:
theorem continuousAt_lift
  given: {hf : forall x y, (x ~ᵢ y) -> f x = f y}
  proof: tendsto_lift_nhds_mk

@[simp]

中文:
定理 continuousAt_lift
  条件: {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y}
  证明: tendsto_lift_nhds_mk

@[simp]

Depends on / 依赖: tendsto_lift_nhds_mk
-/
theorem continuousAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk

@[simp]
/--
theorem `continuousWithinAt_lift` / 定理 `continuousWithinAt_lift`

English:
theorem continuousWithinAt_lift
  statement: {hf : forall x y, (x ~ᵢ y) -> f x = f y}
  proof: tendsto_lift_nhdsWithin_mk

@[simp]

中文:
定理 continuousWithinAt_lift
  结论: {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y}
  证明: tendsto_lift_nhdsWithin_mk

@[simp]

Depends on / 依赖: tendsto_lift_nhdsWithin_mk
-/
theorem continuousWithinAt_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y}
    {s : Set (SeparationQuotient X)} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhdsWithin_mk

@[simp]
/--
theorem `continuousOn_lift` / 定理 `continuousOn_lift`

English:
theorem continuousOn_lift
  given: {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (SeparationQuotient X)}
  proof: by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]

中文:
定理 continuousOn_lift
  条件: {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y} {s : Set (SeparationQuotient X)}
  证明: by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]

Depends on / 依赖: ContinuousOn, continuousWithinAt_lift, mem_preimage, surjective_mk, surjective_mk.forall
-/
theorem continuousOn_lift {hf : forall x y, (x ~ᵢ y) -> f x = f y} {s : Set (SeparationQuotient X)} :
    ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuousWithinAt_lift, mem_preimage]

@[simp]
/--
theorem `continuous_lift_iff` / 定理 `continuous_lift_iff`

English:
theorem continuous_lift_iff
  given: {hf : forall x y, (x ~ᵢ y) -> f x = f y}
  proof: by
  simp only [← continuousOn_univ, continuousOn_lift, preimage_univ]

alias ⟨_, continuous_lift⟩ := continuous_lift_iff

中文:
定理 continuous_lift_iff
  条件: {hf : 对任意 x y, (x ~ᵢ y) -> f x = f y}
  证明: by
  simp only [← continuousOn_univ, continuousOn_lift, preimage_univ]

alias ⟨_, continuous_lift⟩ := continuous_lift_iff

Depends on / 依赖: continuousOn_lift, continuousOn_univ, preimage_univ
-/
theorem continuous_lift_iff {hf : forall x y, (x ~ᵢ y) -> f x = f y} :
    Continuous (lift f hf) ↔ Continuous f := by
  simp only [← continuousOn_univ, continuousOn_lift, preimage_univ]

alias ⟨_, continuous_lift⟩ := continuous_lift_iff
attribute [fun_prop] continuous_lift

/--
Definition of `lift₂` / `lift₂` 的定义

English:
definition lift₂
  signature: (f : X -> Y -> α) (hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d)
  body: fun x y => Quotient.liftOn₂' x y f hf

@[simp]

中文:
定义 lift₂
  签名: (f : X -> Y -> α) (hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d)
  定义体: fun x y => Quotient.liftOn₂' x y f hf

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn
-/
def lift₂ (f : X -> Y -> α) (hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d) :
    SeparationQuotient X -> SeparationQuotient Y -> α := fun x y => Quotient.liftOn₂' x y f hf

@[simp]
/--
theorem `lift₂_mk` / 定理 `lift₂_mk`

English:
theorem lift₂_mk
  statement: {f : X -> Y -> α} (hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d) (x : X)
  proof: rfl

@[simp]

中文:
定理 lift₂_mk
  结论: {f : X -> Y -> α} (hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d) (x : X)
  证明: rfl

@[simp]
-/
theorem lift₂_mk {f : X -> Y -> α} (hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d) (x : X)
    (y : Y) : lift₂ f hf (mk x) (mk y) = f x y :=
  rfl

@[simp]
/--
theorem `tendsto_lift₂_nhds` / 定理 `tendsto_lift₂_nhds`

English:
theorem tendsto_lift₂_nhds
  statement: {f : X -> Y -> α} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  proof: by
  rw [← map_prod_map_mk_nhds]; rw [tendsto_map'_iff]
  rfl

中文:
定理 tendsto_lift₂_nhds
  结论: {f : X -> Y -> α} {hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  证明: by
  rw [← map_prod_map_mk_nhds]; rw [tendsto_map'_iff]
  rfl

Depends on / 依赖: _iff, map_prod_map_mk_nhds, tendsto_map
-/
theorem tendsto_lift₂_nhds {f : X -> Y -> α} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
    {x : X} {y : Y} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝 (mk x, mk y)) l ↔ Tendsto (uncurry f) (𝓝 (x, y)) l := by
  rw [← map_prod_map_mk_nhds]; rw [tendsto_map'_iff]
  rfl

/--
theorem `tendsto_lift₂_nhdsWithin` / 定理 `tendsto_lift₂_nhdsWithin`

English:
theorem tendsto_lift₂_nhdsWithin
  statement: {f : X -> Y -> α}
  proof: by
  rw [nhdsWithin]; rw [← map_prod_map_mk_nhds]; rw [← Filter.push_pull]; rw [comap_principal]
  rfl

@[simp]

中文:
定理 tendsto_lift₂_nhdsWithin
  结论: {f : X -> Y -> α}
  证明: by
  rw [nhdsWithin]; rw [← map_prod_map_mk_nhds]; rw [← Filter.push_pull]; rw [comap_principal]
  rfl

@[simp]
-/
@[simp] theorem tendsto_lift₂_nhdsWithin {f : X -> Y -> α}
    {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d} {x : X} {y : Y}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝[s] (mk x, mk y)) l ↔
      Tendsto (uncurry f) (𝓝[Prod.map mk mk ⁻¹' s] (x, y)) l := by
  rw [nhdsWithin]; rw [← map_prod_map_mk_nhds]; rw [← Filter.push_pull]; rw [comap_principal]
  rfl

@[simp]
/--
theorem `continuousAt_lift₂` / 定理 `continuousAt_lift₂`

English:
theorem continuousAt_lift₂
  statement: {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  proof: tendsto_lift₂_nhds

中文:
定理 continuousAt_lift₂
  结论: {f : X -> Y -> Z} {hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  证明: tendsto_lift₂_nhds
-/
theorem continuousAt_lift₂ {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
    {x : X} {y : Y} :
    ContinuousAt (uncurry <| lift₂ f hf) (mk x, mk y) ↔ ContinuousAt (uncurry f) (x, y) :=
  tendsto_lift₂_nhds

/--
theorem `continuousWithinAt_lift₂` / 定理 `continuousWithinAt_lift₂`

English:
theorem continuousWithinAt_lift₂
  statement: {f : X -> Y -> Z}
  proof: tendsto_lift₂_nhdsWithin

@[simp]

中文:
定理 continuousWithinAt_lift₂
  结论: {f : X -> Y -> Z}
  证明: tendsto_lift₂_nhdsWithin

@[simp]
-/
@[simp] theorem continuousWithinAt_lift₂ {f : X -> Y -> Z}
    {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {x : X} {y : Y} :
    ContinuousWithinAt (uncurry <| lift₂ f hf) s (mk x, mk y) ↔
      ContinuousWithinAt (uncurry f) (Prod.map mk mk ⁻¹' s) (x, y) :=
  tendsto_lift₂_nhdsWithin

@[simp]
/--
theorem `continuousOn_lift₂` / 定理 `continuousOn_lift₂`

English:
theorem continuousOn_lift₂
  statement: {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  proof: by
  simp_rw [ContinuousOn, (surjective_mk.prodMap surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]

中文:
定理 continuousOn_lift₂
  结论: {f : X -> Y -> Z} {hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  证明: by
  simp_rw [ContinuousOn, (surjective_mk.prodMap surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]

Depends on / 依赖: ContinuousOn, Prod.forall, Prod.map, prodMap, simp_rw, surjective_mk, surjective_mk.prodMap
-/
theorem continuousOn_lift₂ {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} :
    ContinuousOn (uncurry <| lift₂ f hf) s ↔ ContinuousOn (uncurry f) (Prod.map mk mk ⁻¹' s) := by
  simp_rw [ContinuousOn, (surjective_mk.prodMap surjective_mk).forall, Prod.forall, Prod.map,
    continuousWithinAt_lift₂]
  rfl

@[simp]
/--
theorem `continuous_lift₂` / 定理 `continuous_lift₂`

English:
theorem continuous_lift₂
  given: {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  proof: by
  simp only [← continuousOn_univ, continuousOn_lift₂, preimage_univ]

中文:
定理 continuous_lift₂
  条件: {f : X -> Y -> Z} {hf : 对任意 a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d}
  证明: by
  simp only [← continuousOn_univ, continuousOn_lift₂, preimage_univ]

Depends on / 依赖: continuousOn_univ, preimage_univ
-/
theorem continuous_lift₂ {f : X -> Y -> Z} {hf : forall a b c d, (a ~ᵢ c) -> (b ~ᵢ d) -> f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [← continuousOn_univ, continuousOn_lift₂, preimage_univ]

end SeparationQuotient

/--
theorem `continuous_congr_of_inseparable` / 定理 `continuous_congr_of_inseparable`

English:
theorem continuous_congr_of_inseparable
  given: (h : forall x, f x ~ᵢ g x)
  proof: by
  simp_rw [SeparationQuotient.isInducing_mk.continuous_iff (Y := Y)]
  exact continuous_congr fun x => SeparationQuotient.mk_eq_mk.mpr (h x)

中文:
定理 continuous_congr_of_inseparable
  条件: (h : 对任意 x, f x ~ᵢ g x)
  证明: by
  simp_rw [SeparationQuotient.isInducing_mk.continuous_iff (Y := Y)]
  exact continuous_congr fun x => SeparationQuotient.mk_eq_mk.mpr (h x)

Depends on / 依赖: SeparationQuotient, SeparationQuotient.isInducing_mk.continuous_iff, SeparationQuotient.mk_eq_mk.mpr, continuous_congr, continuous_iff, isInducing_mk, mk_eq_mk, simp_rw
-/
theorem continuous_congr_of_inseparable (h : forall x, f x ~ᵢ g x) :
    Continuous f ↔ Continuous g := by
  simp_rw [SeparationQuotient.isInducing_mk.continuous_iff (Y := Y)]
  exact continuous_congr fun x => SeparationQuotient.mk_eq_mk.mpr (h x)
