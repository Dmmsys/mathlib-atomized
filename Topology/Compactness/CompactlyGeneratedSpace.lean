/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Etienne Marion
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Compactly generated topological spaces

This file defines compactly generated topological spaces. A compactly generated space is a space `X`
whose topology is coinduced by continuous maps from compact Hausdorff spaces to `X`. In such a
space, a set `s` is closed (resp. open) if and only if for all compact Hausdorff space `K` and
`f : K → X` continuous, `f ⁻¹' s` is closed (resp. open) in `K`.

We provide two definitions. `UCompactlyGeneratedSpace.{u} X` corresponds to the type class where the
compact Hausdorff spaces are taken in an arbitrary universe `u`, and should therefore always be used
with an explicit universe parameter. It is intended for categorical purposes.

`CompactlyGeneratedSpace X` corresponds to the case where compact Hausdorff spaces are taken in
the same universe as `X`, and is intended for topological purposes.

We prove basic properties and instances, and prove that a `SequentialSpace` is compactly generated,
as well as a Hausdorff `WeaklyLocallyCompactSpace`.

## Main definitions

* `UCompactlyGeneratedSpace.{u} X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in universe `u`.
* `CompactlyGeneratedSpace X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in the same universe as `X`.

## References

* <https://en.wikipedia.org/wiki/Compactly_generated_space>
* <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>

## Tags

compactly generated space
-/

@[expose] public section

universe u v w x

open TopologicalSpace Filter Topology Set

section UCompactlyGeneratedSpace

variable {X : Type w} {Y : Type x}

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
@[instance_reducible]
/--
Definition of `TopologicalSpace.compactlyGenerated` / `TopologicalSpace.compactlyGenerated` 的定义

English:
definition TopologicalSpace.compactlyGenerated
  signature: (X : Type w) [TopologicalSpace X]
  body: let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
  coinduced f inferInstance

中文:
定义 拓扑空间.compactlyGenerated
  签名: (X : 类型 w) [拓扑空间 X]
  定义体: let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
  coinduced f inferInstance

Depends on / 依赖: CompHaus, coinduced, i.fst
-/
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
  coinduced f inferInstance

/--
lemma `continuous_from_compactlyGenerated` / 引理 `continuous_from_compactlyGenerated`

English:
lemma continuous_from_compactlyGenerated
  statement: [TopologicalSpace X] [t : TopologicalSpace Y] (f : X -> Y)
  proof: by
  rw [continuous_coinduced_dom]
  continuity

中文:
引理 continuous_from_compactlyGenerated
  结论: [拓扑空间 X] [t : 拓扑空间 Y] (f : X -> Y)
  证明: by
  rw [continuous_coinduced_dom]
  continuity

Depends on / 依赖: continuity, continuous_coinduced_dom
-/
lemma continuous_from_compactlyGenerated [TopologicalSpace X] [t : TopologicalSpace Y] (f : X -> Y)
    (h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.

This version includes an explicit universe parameter `u` which should always be specified. It is
intended for categorical purposes. See `CompactlyGeneratedSpace` for the version without this
parameter, intended for topological purposes.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the compact space universe `u` would default
-- to a universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
/--
Definition of `UCompactlyGeneratedSpace` / `UCompactlyGeneratedSpace` 的定义

English:
class UCompactlyGeneratedSpace
  parameters: (X : Type v) [t : TopologicalSpace X]
  axioms and operations (1):
    - le_compactlyGenerated : t <= compactlyGenerated.{u} X

中文:
类 UCompactlyGenerated空间
  参数: (X : 类型v) [t : 拓扑空间 X]
  公理与运算 (1 个):
    - le_compactlyGenerated : t <= compactlyGenerated.{u} X
-/
class UCompactlyGeneratedSpace (X : Type v) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t <= compactlyGenerated.{u} X

/--
lemma `eq_compactlyGenerated` / 引理 `eq_compactlyGenerated`

English:
lemma eq_compactlyGenerated
  given: [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
  proof: by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f => f.2

中文:
引理 eq_compactlyGenerated
  条件: [t : 拓扑空间 X] [UCompactlyGenerated空间.{u} X]
  证明: by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f => f.2

Depends on / 依赖: Sigma.forall, UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.le_compactlyGenerated, compactlyGenerated, continuous_iff_coinduced_le, continuous_sigma_iff, le_antisymm, le_compactlyGenerated
-/
lemma eq_compactlyGenerated [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f => f.2

instance (X : Type v) [t : TopologicalSpace X] [DiscreteTopology X] :
    UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

/- The unused variable linter flags `[tY : TopologicalSpace Y]`,
but we want to use this as a named argument, so we need to disable the linter. -/
set_option linter.unusedVariables false in
/--
lemma `uCompactlyGeneratedSpace_of_continuous_maps` / 引理 `uCompactlyGeneratedSpace_of_continuous_maps`

English:
lemma uCompactlyGeneratedSpace_of_continuous_maps
  statement: [t : TopologicalSpace X]
  proof: by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X -> X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
    suffices forall (i : (T : CompHaus.{u}) 

中文:
引理 uCompactlyGeneratedSpace_of_continuous_maps
  结论: [t : 拓扑空间 X]
  证明: by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X -> X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
    suffices forall (i : (T : CompHaus.{u}) 

Depends on / 依赖: CompHaus, Continuous, compactlyGenerated, continuous_coinduced_rng, continuous_id_iff_le, continuous_sigma_iff, i.fst
-/
lemma uCompactlyGeneratedSpace_of_continuous_maps [t : TopologicalSpace X]
    (h : forall {Y : Type w} [tY : TopologicalSpace Y] (f : X -> Y),
      (forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) -> Continuous f) :
        UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X -> X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) -> X := fun ⟨⟨_, i⟩, s⟩ => i s
    suffices forall (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) => f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/--
lemma `continuous_from_uCompactlyGeneratedSpace` / 引理 `continuous_from_uCompactlyGeneratedSpace`

English:
lemma continuous_from_uCompactlyGeneratedSpace
  statement: [UCompactlyGeneratedSpace.{u} X] (f : X -> Y)
  proof: by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

中文:
引理 continuous_from_uCompactlyGeneratedSpace
  结论: [UCompactlyGenerated空间.{u} X] (f : X -> Y)
  证明: by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

Depends on / 依赖: UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.le_compactlyGenerated, continuous_from_compactlyGenerated, continuous_le_dom, le_compactlyGenerated
-/
lemma continuous_from_uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{u} X] (f : X -> Y)
    (h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

/--
theorem `uCompactlyGeneratedSpace_of_isClosed` / 定理 `uCompactlyGeneratedSpace_of_isClosed`

English:
theorem uCompactlyGeneratedSpace_of_isClosed
  proof: uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_iff_isClosed.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

中文:
定理 uCompactlyGeneratedSpace_of_isClosed
  证明: uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_iff_isClosed.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

Depends on / 依赖: continuous_iff_isClosed, hs.preimage, preimage, uCompactlyGeneratedSpace_of_continuous_maps
-/
theorem uCompactlyGeneratedSpace_of_isClosed
    (h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) -> IsClosed s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_iff_isClosed.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

/--
theorem `uCompactlyGeneratedSpace_of_isOpen` / 定理 `uCompactlyGeneratedSpace_of_isOpen`

English:
theorem uCompactlyGeneratedSpace_of_isOpen
  proof: uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_def.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

中文:
定理 uCompactlyGeneratedSpace_of_isOpen
  证明: uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_def.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

Depends on / 依赖: continuous_def, hs.preimage, preimage, uCompactlyGeneratedSpace_of_continuous_maps
-/
theorem uCompactlyGeneratedSpace_of_isOpen
    (h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) -> IsOpen s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' =>
    continuous_def.2 fun _ hs => h _ fun S g => hs.preimage (h' S g)

/--
theorem `UCompactlyGeneratedSpace.isClosed` / 定理 `UCompactlyGeneratedSpace.isClosed`

English:
theorem UCompactlyGeneratedSpace.isClosed
  statement: [UCompactlyGeneratedSpace.{u} X] {s : Set X}
  proof: by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isClosed_coinduced]; rw [isClosed_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

中文:
定理 UCompactlyGenerated空间.isClosed
  结论: [UCompactlyGenerated空间.{u} X] {s : 集合 X}
  证明: by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isClosed_coinduced]; rw [isClosed_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

Depends on / 依赖: TopologicalSpace, TopologicalSpace.compactlyGenerated, compactlyGenerated, eq_compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff
-/
theorem UCompactlyGeneratedSpace.isClosed [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isClosed_coinduced]; rw [isClosed_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

/--
theorem `UCompactlyGeneratedSpace.isOpen` / 定理 `UCompactlyGeneratedSpace.isOpen`

English:
theorem UCompactlyGeneratedSpace.isOpen
  statement: [UCompactlyGeneratedSpace.{u} X] {s : Set X}
  proof: by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isOpen_coinduced]; rw [isOpen_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

中文:
定理 UCompactlyGenerated空间.isOpen
  结论: [UCompactlyGenerated空间.{u} X] {s : 集合 X}
  证明: by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isOpen_coinduced]; rw [isOpen_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

Depends on / 依赖: TopologicalSpace, TopologicalSpace.compactlyGenerated, compactlyGenerated, eq_compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff
-/
theorem UCompactlyGeneratedSpace.isOpen [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X)]; rw [TopologicalSpace.compactlyGenerated]; rw [isOpen_coinduced]; rw [isOpen_sigma_iff]
  exact fun ⟨S, f⟩ => hs S f

/--
theorem `uCompactlyGeneratedSpace_of_coinduced` / 定理 `uCompactlyGeneratedSpace_of_coinduced`

English:
theorem uCompactlyGeneratedSpace_of_coinduced
  proof: by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => ?_
  rw [ht]; rw [isClosed_coinduced]
  exact UCompactlyGeneratedSpace.isClosed fun _ ⟨g, hg⟩ => h _ ⟨_, hf.comp hg⟩

中文:
定理 uCompactlyGeneratedSpace_of_coinduced
  证明: by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => ?_
  rw [ht]; rw [isClosed_coinduced]
  exact UCompactlyGeneratedSpace.isClosed fun _ ⟨g, hg⟩ => h _ ⟨_, hf.comp hg⟩

Depends on / 依赖: UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.isClosed, hf.comp, isClosed, isClosed_coinduced, uCompactlyGeneratedSpace_of_isClosed
-/
theorem uCompactlyGeneratedSpace_of_coinduced
    [UCompactlyGeneratedSpace.{u} X] {f : X -> Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    UCompactlyGeneratedSpace.{u} Y := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => ?_
  rw [ht]; rw [isClosed_coinduced]
  exact UCompactlyGeneratedSpace.isClosed fun _ ⟨g, hg⟩ => h _ ⟨_, hf.comp hg⟩

/-- The quotient of a compactly generated space is compactly generated. -/
instance {S : Setoid X} [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (Quotient S) :=
  uCompactlyGeneratedSpace_of_coinduced continuous_quotient_mk' rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UCompactlyGeneratedSpace.{u}
  signature: X] [UCompactlyGeneratedSpace.{v} Y] :
  body: by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => ?_
  · let g : ULift.{v} S -> X oplus Y := Sum.inl ∘ f ∘ ULift.down
have hg : Continuous g := continuous_inl.comp hf.comp continuous_ulift

中文:
实例 [UCompactlyGenerated空间.{u}
  签名: X] [UCompactlyGenerated空间.{v} Y] :
  定义体: by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => ?_
  · let g : ULift.{v} S -> X oplus Y := Sum.inl ∘ f ∘ ULift.down
have hg : Continuous g := continuous_inl.comp hf.comp continuous_ulift

Depends on / 依赖: CompHaus, CompHaus.of, Continuous, Sum.inl, Sum.inr, UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.isClosed, ULift.down, all_goals, continuous_inl, continuous_inl.comp, continuous_inr, continuous_inr.comp, continuous_uli, continuous_uliftDown, continuous_uliftUp, hf.comp, isClosed, isClosed_sum_iff, preimage
-/
instance [UCompactlyGeneratedSpace.{u} X] [UCompactlyGeneratedSpace.{v} Y] :
    UCompactlyGeneratedSpace.{max u v} (X oplus Y) := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h => isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => ?_
  · let g : ULift.{v} S -> X oplus Y := Sum.inl ∘ f ∘ ULift.down
have hg : Continuous g := continuous_inl.comp hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp
  · let g : ULift.{u} S -> X oplus Y := Sum.inr ∘ f ∘ ULift.down
have hg : Continuous g := continuous_inr.comp hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{u} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
instance {ι : Type v} {X : ι -> Type w} [forall i, TopologicalSpace (X i)]
    [forall i, UCompactlyGeneratedSpace.{u} (X i)] : UCompactlyGeneratedSpace.{u} (Σ i, X i) :=
  uCompactlyGeneratedSpace_of_isClosed fun _ h => isClosed_sigma_iff.2 fun i =>
    UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ =>
      h S ⟨Sigma.mk i ∘ f, continuous_sigmaMk.comp hf⟩

open OnePoint in
/-- A sequential space is compactly generated.

The proof is taken from <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>,
Proposition 1.6. -/
instance (priority := 100) [SequentialSpace X] : UCompactlyGeneratedSpace.{u} X := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h =>
    SequentialSpace.isClosed_of_seq _ fun u p hu hup => ?_
  let g : ULift.{u} (OnePoint Nat) -> X := (continuousMapMkNat u p hup) ∘ ULift.down
  change ULift.up ∞ in g ⁻¹' s
  have : Filter.Tendsto (@OnePoint.some Nat) Filter.atTop (𝓝 ∞) := by
    rw [← Nat.cofinite_eq_atTop]; rw [← cocompact_eq_cofinite]; rw [← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty
  apply IsClosed.mem_of_tendsto _ ((continuous_uliftUp.tendsto ∞).comp this)
  · simp only [Function.comp_apply, mem_preimage, eventually_atTop]
    exact ⟨0, fun b _ => hu b⟩
  · exact h (CompHaus.of (ULift.{u} (OnePoint Nat))) ⟨g, by fun_prop⟩

end UCompactlyGeneratedSpace

section CompactlyGeneratedSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/--
Definition of `CompactlyGeneratedSpace` / `CompactlyGeneratedSpace` 的定义

English:
abbreviation CompactlyGeneratedSpace
  signature: (X : Type u) [TopologicalSpace X]
  body: UCompactlyGeneratedSpace.{u} X

中文:
缩写 CompactlyGeneratedSpace
  签名: (X : 类型u) [拓扑空间 X]
  定义体: UCompactlyGeneratedSpace.{u} X

Depends on / 依赖: UCompactlyGeneratedSpace
-/
abbrev CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UCompactlyGeneratedSpace.{u} X

/--
lemma `continuous_from_compactlyGeneratedSpace` / 引理 `continuous_from_compactlyGeneratedSpace`

English:
lemma continuous_from_compactlyGeneratedSpace
  statement: [CompactlyGeneratedSpace X] (f : X -> Y)
  proof: continuous_from_uCompactlyGeneratedSpace f fun K ⟨g, hg⟩ => h K g hg

中文:
引理 continuous_from_compactlyGeneratedSpace
  结论: [CompactlyGeneratedSpace X] (f : X -> Y)
  证明: continuous_from_uCompactlyGeneratedSpace f fun K ⟨g, hg⟩ => h K g hg

Depends on / 依赖: continuous_from_uCompactlyGeneratedSpace
-/
lemma continuous_from_compactlyGeneratedSpace [CompactlyGeneratedSpace X] (f : X -> Y)
    (h : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
      (forall g : K -> X, Continuous g -> Continuous (f ∘ g))) : Continuous f :=
  continuous_from_uCompactlyGeneratedSpace f fun K ⟨g, hg⟩ => h K g hg

/--
lemma `compactlyGeneratedSpace_of_continuous_maps` / 引理 `compactlyGeneratedSpace_of_continuous_maps`

English:
lemma compactlyGeneratedSpace_of_continuous_maps
  proof: uCompactlyGeneratedSpace_of_continuous_maps fun f h' => h f fun K _ _ _ g hg =>
    h' (CompHaus.of K) ⟨g, hg⟩

中文:
引理 compactlyGeneratedSpace_of_continuous_maps
  证明: uCompactlyGeneratedSpace_of_continuous_maps fun f h' => h f fun K _ _ _ g hg =>
    h' (CompHaus.of K) ⟨g, hg⟩

Depends on / 依赖: CompHaus, CompHaus.of, uCompactlyGeneratedSpace_of_continuous_maps
-/
lemma compactlyGeneratedSpace_of_continuous_maps
    (h : forall {Y : Type u} [TopologicalSpace Y] (f : X -> Y),
      (forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
        (forall g : K -> X, Continuous g -> Continuous (f ∘ g))) -> Continuous f) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun f h' => h f fun K _ _ _ g hg =>
    h' (CompHaus.of K) ⟨g, hg⟩

/--
theorem `compactlyGeneratedSpace_of_isClosed` / 定理 `compactlyGeneratedSpace_of_isClosed`

English:
theorem compactlyGeneratedSpace_of_isClosed
  proof: uCompactlyGeneratedSpace_of_isClosed fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

中文:
定理 compactlyGeneratedSpace_of_isClosed
  证明: uCompactlyGeneratedSpace_of_isClosed fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

Depends on / 依赖: CompHaus, CompHaus.of, uCompactlyGeneratedSpace_of_isClosed
-/
theorem compactlyGeneratedSpace_of_isClosed
    (h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
      forall (f : K -> X), Continuous f -> IsClosed (f ⁻¹' s)) -> IsClosed s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isClosed fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

/--
theorem `CompactlyGeneratedSpace.isClosed'` / 定理 `CompactlyGeneratedSpace.isClosed'`

English:
theorem CompactlyGeneratedSpace.isClosed'
  statement: [CompactlyGeneratedSpace X] {s : Set X}
  proof: UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => hs S f hf

中文:
定理 CompactlyGeneratedSpace.isClosed'
  结论: [CompactlyGeneratedSpace X] {s : 集合 X}
  证明: UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => hs S f hf

Depends on / 依赖: UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.isClosed, isClosed
-/
theorem CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
      forall (f : K -> X), Continuous f -> IsClosed (f ⁻¹' s)) : IsClosed s :=
  UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ => hs S f hf

/--
theorem `CompactlyGeneratedSpace.isClosed` / 定理 `CompactlyGeneratedSpace.isClosed`

English:
theorem CompactlyGeneratedSpace.isClosed
  statement: [CompactlyGeneratedSpace X] {s : Set X}
  proof: by
  refine isClosed' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

中文:
定理 CompactlyGeneratedSpace.isClosed
  结论: [CompactlyGeneratedSpace X] {s : 集合 X}
  证明: by
  refine isClosed' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

Depends on / 依赖: Set.preimage_inter_range, isClosed, isCompact_range, preimage, preimage_inter_range
-/
theorem CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X}
    (hs : forall ⦃K⦄, IsCompact K -> IsClosed (s inter K)) : IsClosed s := by
  refine isClosed' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/--
theorem `compactlyGeneratedSpace_of_isOpen` / 定理 `compactlyGeneratedSpace_of_isOpen`

English:
theorem compactlyGeneratedSpace_of_isOpen
  proof: uCompactlyGeneratedSpace_of_isOpen fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

中文:
定理 compactlyGeneratedSpace_of_isOpen
  证明: uCompactlyGeneratedSpace_of_isOpen fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

Depends on / 依赖: CompHaus, CompHaus.of, uCompactlyGeneratedSpace_of_isOpen
-/
theorem compactlyGeneratedSpace_of_isOpen
    (h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
      forall (f : K -> X), Continuous f -> IsOpen (f ⁻¹' s)) -> IsOpen s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isOpen fun s h' => h s fun K _ _ _ f hf => h' (CompHaus.of K) ⟨f, hf⟩

/--
theorem `CompactlyGeneratedSpace.isOpen'` / 定理 `CompactlyGeneratedSpace.isOpen'`

English:
theorem CompactlyGeneratedSpace.isOpen'
  statement: [CompactlyGeneratedSpace X] {s : Set X}
  proof: UCompactlyGeneratedSpace.isOpen fun S ⟨f, hf⟩ => hs S f hf

中文:
定理 CompactlyGeneratedSpace.isOpen'
  结论: [CompactlyGeneratedSpace X] {s : 集合 X}
  证明: UCompactlyGeneratedSpace.isOpen fun S ⟨f, hf⟩ => hs S f hf

Depends on / 依赖: UCompactlyGeneratedSpace, UCompactlyGeneratedSpace.isOpen, isOpen
-/
theorem CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
      forall (f : K -> X), Continuous f -> IsOpen (f ⁻¹' s)) : IsOpen s :=
  UCompactlyGeneratedSpace.isOpen fun S ⟨f, hf⟩ => hs S f hf

/--
theorem `CompactlyGeneratedSpace.isOpen` / 定理 `CompactlyGeneratedSpace.isOpen`

English:
theorem CompactlyGeneratedSpace.isOpen
  statement: [CompactlyGeneratedSpace X] {s : Set X}
  proof: by
  refine isOpen' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

中文:
定理 CompactlyGeneratedSpace.isOpen
  结论: [CompactlyGeneratedSpace X] {s : 集合 X}
  证明: by
  refine isOpen' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

Depends on / 依赖: Set.preimage_inter_range, isCompact_range, isOpen, preimage, preimage_inter_range
-/
theorem CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X}
    (hs : forall ⦃K⦄, IsCompact K -> IsOpen (s inter K)) : IsOpen s := by
  refine isOpen' fun K _ _ _ f hf => ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/--
theorem `compactlyGeneratedSpace_of_coinduced` / 定理 `compactlyGeneratedSpace_of_coinduced`

English:
theorem compactlyGeneratedSpace_of_coinduced
  proof: uCompactlyGeneratedSpace_of_coinduced hf ht

中文:
定理 compactlyGeneratedSpace_of_coinduced
  证明: uCompactlyGeneratedSpace_of_coinduced hf ht

Depends on / 依赖: uCompactlyGeneratedSpace_of_coinduced
-/
theorem compactlyGeneratedSpace_of_coinduced
    {X : Type u} [tX : TopologicalSpace X] {Y : Type u} [tY : TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X -> Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    CompactlyGeneratedSpace Y := uCompactlyGeneratedSpace_of_coinduced hf ht

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
instance {ι : Type u} {X : ι -> Type v}
    [forall i, TopologicalSpace (X i)] [forall i, CompactlyGeneratedSpace (X i)] :
    CompactlyGeneratedSpace (Σ i, X i) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h => isClosed_sigma_iff.2 fun i =>
    CompactlyGeneratedSpace.isClosed' fun K _ _ _ f hf => ?_
  let g : ULift.{u} K -> (Σ i, X i) := Sigma.mk i ∘ f ∘ ULift.down
have hg : Continuous g := continuous_sigmaMk.comp hf.comp continuous_uliftDown
  exact (h _ g hg).preimage continuous_uliftUp

variable [T2Space X]

/--
theorem `CompactlyGeneratedSpace.isClosed_iff_of_t2` / 定理 `CompactlyGeneratedSpace.isClosed_iff_of_t2`

English:
theorem CompactlyGeneratedSpace.isClosed_iff_of_t2
  given: [CompactlyGeneratedSpace X] (s : Set X)
  proof: hs.inter hK.isClosed
  mpr := CompactlyGeneratedSpace.isClosed

中文:
定理 CompactlyGeneratedSpace.isClosed_iff_of_t2
  条件: [CompactlyGeneratedSpace X] (s : 集合 X)
  证明: hs.inter hK.isClosed
  mpr := CompactlyGeneratedSpace.isClosed

Depends on / 依赖: hK.isClosed, hs.inter, isClosed
-/
theorem CompactlyGeneratedSpace.isClosed_iff_of_t2 [CompactlyGeneratedSpace X] (s : Set X) :
    IsClosed s ↔ forall ⦃K⦄, IsCompact K -> IsClosed (s inter K) where
  mp hs _ hK := hs.inter hK.isClosed
  mpr := CompactlyGeneratedSpace.isClosed

/--
theorem `compactlyGeneratedSpace_of_isClosed_of_t2` / 定理 `compactlyGeneratedSpace_of_isClosed_of_t2`

English:
theorem compactlyGeneratedSpace_of_isClosed_of_t2
  proof: by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => h s fun K hK => ?_
  rw [Set.inter_comm]; rw [← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

中文:
定理 compactlyGeneratedSpace_of_isClosed_of_t2
  证明: by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => h s fun K hK => ?_
  rw [Set.inter_comm]; rw [← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

Depends on / 依赖: CompactSpace, Set.inter_comm, Subtype, Subtype.image_preimage_coe, Subtype.val, compactlyGeneratedSpace_of_isClosed, continuous_subtype_val, hK.isClosed.isClosedMap_subtype_val, image_preimage_coe, inter_comm, isClosed, isClosedMap_subtype_val, isCompact_iff_compactSpace
-/
theorem compactlyGeneratedSpace_of_isClosed_of_t2
    (h : forall s, (forall (K : Set X), IsCompact K -> IsClosed (s inter K)) -> IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => h s fun K hK => ?_
  rw [Set.inter_comm]; rw [← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

open scoped Set.Notation in
/--
theorem `compactlyGeneratedSpace_of_isOpen_of_t2` / 定理 `compactlyGeneratedSpace_of_isOpen_of_t2`

English:
theorem compactlyGeneratedSpace_of_isOpen_of_t2
  proof: by
  refine compactlyGeneratedSpace_of_isOpen fun s hs => h s fun K hK => ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

中文:
定理 compactlyGeneratedSpace_of_isOpen_of_t2
  证明: by
  refine compactlyGeneratedSpace_of_isOpen fun s hs => h s fun K hK => ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

Depends on / 依赖: CompactSpace, Subtype, Subtype.val, compactlyGeneratedSpace_of_isOpen, continuous_subtype_val, isCompact_iff_compactSpace
-/
theorem compactlyGeneratedSpace_of_isOpen_of_t2
    (h : forall s, (forall (K : Set X), IsCompact K -> IsOpen (K ↓inter s)) -> IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs => h s fun K hK => ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

/-- A Hausdorff and weakly locally compact space is compactly generated. -/
instance (priority := 100) [WeaklyLocallyCompactSpace X] :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h => ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
exact Set.mem_of_mem_inter_left isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

/--
Instance `to_compactlyCoherentSpace` / 实例 `to_compactlyCoherentSpace`

English:
instance to_compactlyCoherentSpace
  signature: [CompactlyGeneratedSpace X]
  body: CompactlyCoherentSpace.of_isOpen_forall_compactSpace fun _ h => CompactlyGeneratedSpace.isOpen'
    fun K _ _ _ f hf => h K f hf

中文:
实例 to_compactlyCoherentSpace
  签名: [CompactlyGeneratedSpace X]
  定义体: CompactlyCoherentSpace.of_isOpen_forall_compactSpace fun _ h => CompactlyGeneratedSpace.isOpen'
    fun K _ _ _ f hf => h K f hf

Depends on / 依赖: CompactlyCoherentSpace, CompactlyCoherentSpace.of_isOpen_forall_compactSpace, CompactlyGeneratedSpace, CompactlyGeneratedSpace.isOpen, isOpen, of_isOpen_forall_compactSpace
-/
instance to_compactlyCoherentSpace [CompactlyGeneratedSpace X] : CompactlyCoherentSpace X :=
  CompactlyCoherentSpace.of_isOpen_forall_compactSpace fun _ h => CompactlyGeneratedSpace.isOpen'
    fun K _ _ _ f hf => h K f hf

/--
Instance `of_compactlyCoherentSpace_of_t2` / 实例 `of_compactlyCoherentSpace_of_t2`

English:
instance of_compactlyCoherentSpace_of_t2
  signature: [CompactlyCoherentSpace X]
  body: by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  rw [CompactlyCoherentSpace.isClosed_iff]
  intro K hK
  rw [← Subtype.preimage_coe_inter_self]
  exact (hs K hK).preimage_val

中文:
实例 of_compactlyCoherentSpace_of_t2
  签名: [余mpactlyCoherent空间 X]
  定义体: by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  rw [CompactlyCoherentSpace.isClosed_iff]
  intro K hK
  rw [← Subtype.preimage_coe_inter_self]
  exact (hs K hK).preimage_val

Depends on / 依赖: CompactlyCoherentSpace, CompactlyCoherentSpace.isClosed_iff, Subtype, Subtype.preimage_coe_inter_self, compactlyGeneratedSpace_of_isClosed_of_t2, isClosed_iff, preimage_coe_inter_self, preimage_val
-/
instance of_compactlyCoherentSpace_of_t2 [CompactlyCoherentSpace X] :
    CompactlyGeneratedSpace X := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  rw [CompactlyCoherentSpace.isClosed_iff]
  intro K hK
  rw [← Subtype.preimage_coe_inter_self]
  exact (hs K hK).preimage_val

end CompactlyGeneratedSpace
