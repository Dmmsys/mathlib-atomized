/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Extending a function from a subset

The main definition of this file is `extendFrom A f` where `f : X → Y`
and `A : Set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analogous to the way `IsDenseInducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuousOn_extendFrom`
which states that, for `extendFrom A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a T₃ space.

-/

@[expose] public section


noncomputable section

open Topology

open Filter Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
Definition of `extendFrom` / `extendFrom` 的定义

English:
definition extendFrom
  signature: (A : Set X) (f : X -> Y)
  body: fun x => @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

中文:
定义 extendFrom
  签名: (A : Set X) (f : X -> Y)
  定义体: fun x => @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

Depends on / 依赖: limUnder
-/
def extendFrom (A : Set X) (f : X -> Y) : X -> Y :=
  fun x => @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

/--
theorem `tendsto_extendFrom` / 定理 `tendsto_extendFrom`

English:
theorem tendsto_extendFrom
  given: {A : Set X} {f : X -> Y} {x : X} (h : exists y, Tendsto f (𝓝[A] x) (𝓝 y))
  proof: tendsto_nhds_limUnder h

中文:
定理 tendsto_extendFrom
  条件: {A : Set X} {f : X -> Y} {x : X} (h : 存在 y, Tendsto f (𝓝[A] x) (𝓝 y))
  证明: tendsto_nhds_limUnder h

Depends on / 依赖: tendsto_nhds_limUnder
-/
theorem tendsto_extendFrom {A : Set X} {f : X -> Y} {x : X} (h : exists y, Tendsto f (𝓝[A] x) (𝓝 y)) :
    Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A f x) :=
  tendsto_nhds_limUnder h

/--
theorem `extendFrom_eq` / 定理 `extendFrom_eq`

English:
theorem extendFrom_eq
  statement: [T2Space Y] {A : Set X} {f : X -> Y} {x : X} {y : Y} (hx : x in closure A)
  proof: haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf

中文:
定理 extendFrom_eq
  结论: [T2Space Y] {A : Set X} {f : X -> Y} {x : X} {y : Y} (hx : x in closure A)
  证明: haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhdsWithin_neBot.mp, tendsto_nhds_limUnder, tendsto_nhds_unique
-/
theorem extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X} {y : Y} (hx : x in closure A)
    (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f x = y :=
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf

/--
theorem `extendFrom_extends` / 定理 `extendFrom_extends`

English:
theorem extendFrom_extends
  given: [T2Space Y] {f : X -> Y} {A : Set X} (hf : ContinuousOn f A)
  proof: fun x x_in => extendFrom_eq (subset_closure x_in) (hf x x_in)

中文:
定理 extendFrom_extends
  条件: [T2Space Y] {f : X -> Y} {A : Set X} (hf : ContinuousOn f A)
  证明: fun x x_in => extendFrom_eq (subset_closure x_in) (hf x x_in)

Depends on / 依赖: extendFrom_eq, subset_closure, x_in
-/
theorem extendFrom_extends [T2Space Y] {f : X -> Y} {A : Set X} (hf : ContinuousOn f A) :
    forall x in A, extendFrom A f x = f x :=
  fun x x_in => extendFrom_eq (subset_closure x_in) (hf x x_in)

/--
theorem `continuousOn_extendFrom` / 定理 `continuousOn_extendFrom`

English:
theorem continuousOn_extendFrom
  statement: [RegularSpace Y] {f : X -> Y} {A B : Set X} (hB : B subseteq closure A)
  proof: by
  set φ := extendFrom A f
  intro x x_in
  suffices forall V' in 𝓝 (φ x), IsClosed V' -> φ ⁻¹' V' in 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : exists V in 𝓝 x, IsOpen V ∧ V inter A subseteq f ⁻¹'

中文:
定理 continuousOn_extendFrom
  结论: [RegularSpace Y] {f : X -> Y} {A B : Set X} (hB : B subseteq closure A)
  证明: by
  set φ := extendFrom A f
  intro x x_in
  suffices forall V' in 𝓝 (φ x), IsClosed V' -> φ ⁻¹' V' in 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : exists V in 𝓝 x, IsOpen V ∧ V inter A subseteq f ⁻¹'

Depends on / 依赖: ContinuousWithinAt, IsClosed, IsOpen, IsOpen.mem_nhds, V_in, V_op, _closed, closed_nhds_basis, extendFrom, mem_nhds, nhdsWithin_basis_open, subseteq, tendsto_extendFrom, tendsto_left_iff, tendsto_left_iff.mp, tendsto_right_iff, x_in
-/
theorem continuousOn_extendFrom [RegularSpace Y] {f : X -> Y} {A B : Set X} (hB : B subseteq closure A)
    (hf : forall x in B, exists y, Tendsto f (𝓝[A] x) (𝓝 y)) : ContinuousOn (extendFrom A f) B := by
  set φ := extendFrom A f
  intro x x_in
  suffices forall V' in 𝓝 (φ x), IsClosed V' -> φ ⁻¹' V' in 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : exists V in 𝓝 x, IsOpen V ∧ V inter A subseteq f ⁻¹' V' := by
    have := tendsto_extendFrom (hf x x_in)
    rcases (nhdsWithin_basis_open x A).tendsto_left_iff.mp this V' V'_in with ⟨V, ⟨hxV, V_op⟩, hV⟩
    exact ⟨V, IsOpen.mem_nhds V_op hxV, V_op, hV⟩
  suffices forall y in V inter B, φ y in V' from
    mem_of_superset (inter_mem_inf V_in <| mem_principal_self B) this
  rintro y ⟨hyV, hyB⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp (hB hyB)
  have limy : Tendsto f (𝓝[A] y) (𝓝 <| φ y) := tendsto_extendFrom (hf y hyB)
  have hVy : V in 𝓝 y := IsOpen.mem_nhds V_op hyV
  have : V inter A in 𝓝[A] y := by simpa only [inter_comm] using inter_mem_nhdsWithin A hVy
  exact V'_closed.mem_of_tendsto limy (mem_of_superset this hV)

/--
theorem `continuous_extendFrom` / 定理 `continuous_extendFrom`

English:
theorem continuous_extendFrom
  statement: [RegularSpace Y] {f : X -> Y} {A : Set X} (hA : Dense A)
  proof: by
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ => hA x) (by simpa using hf)

中文:
定理 continuous_extendFrom
  结论: [RegularSpace Y] {f : X -> Y} {A : Set X} (hA : Dense A)
  证明: by
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ => hA x) (by simpa using hf)

Depends on / 依赖: continuousOn_extendFrom, continuousOn_univ
-/
theorem continuous_extendFrom [RegularSpace Y] {f : X -> Y} {A : Set X} (hA : Dense A)
    (hf : forall x, exists y, Tendsto f (𝓝[A] x) (𝓝 y)) : Continuous (extendFrom A f) := by
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ => hA x) (by simpa using hf)
