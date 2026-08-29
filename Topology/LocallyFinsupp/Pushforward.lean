/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Spectral.Basic

/-!
# Pushforward of functions with locally finite support

In this file we define the notion of the pushforward of a function with locally finite support
between prespectral spaces along a spectral map. This is used for defining the (proper) pushforward
of algebraic cycles in algebraic geometry.

## Main declarations

- `Function.locallyFinsupp.map`: If `f : X → Y` is a spectral map between spectral spaces and
  `c : X → R` is locally of finite support, the pushforward of `c` along `f` at `y : Y` is
  `∑ᶠ x ∈ f ⁻¹' {y}, c x * w x`, where `w : X → R` is a weight function.

## Notes

In the case of algebraic cycles, the weight function used in `Function.locallyFinsupp.map` will be
specialized to the degree of the residue field extension
(see https://stacks.math.columbia.edu/tag/02R4).
-/

@[expose] public section

open Set Order Topology TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X -> Y} (hf : IsSpectralMap f) (w : X -> R)

namespace Function.locallyFinsupp

variable [Semiring R] {W : Set Y} (hW : IsOpen W) (c : Function.locallyFinsupp X R)
  [PrespectralSpace Y]

variable (f) in
/--
The pushforward of a function `c` of locally finite support by a spectral map with respect to a
weight function `w`.
-/
noncomputable
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (hf : IsSpectralMap f) (c : locallyFinsupp X R)
  body: ∑ᶠ x in f ⁻¹' {z}, c x * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
      (by simp : y in ⊤) (by simp)
    refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
    suffices h : (U inter {z | (f ⁻¹' {z} inter support ⇑c).Nonempty}).Finite by
      refine h.subset (inter_subset_inter_right U fun y hy => ?_)
      obtain ⟨x, (hx : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
      use x
      grind [mem_support]
    suffices (f ⁻¹' (U inter {z | (f ⁻¹' {z} inter c.support).Nonempty}) inter c.support).Finite from
      (this.image f).subset (fun a ha => by grind [Set.Nonempty])
    exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf.2 hU.1.1 hU.1.2).subset
      (by simp; grind)

@[simp]

中文:
定义 map
  签名: (hf : 是谱映射 f) (c : locallyFinsupp X R)
  定义体: ∑ᶠ x in f ⁻¹' {z}, c x * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
      (by simp : y in ⊤) (by simp)
    refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
    suffices h : (U inter {z | (f ⁻¹' {z} inter support ⇑c).Nonempty}).Finite by
      refine h.subset (inter_subset_inter_right U fun y hy => ?_)
      obtain ⟨x, (hx : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
      use x
      grind [mem_support]
    suffices (f ⁻¹' (U inter {z | (f ⁻¹' {z} inter c.support).Nonempty}) inter c.support).Finite from
      (this.image f).subset (fun a ha => by grind [Set.Nonempty])
    exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf.2 hU.1.1 hU.1.2).subset
      (by simp; grind)

@[simp]
-/
def map (hf : IsSpectralMap f) (c : locallyFinsupp X R) : Function.locallyFinsupp Y R where
  toFun z := ∑ᶠ x in f ⁻¹' {z}, c x * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
      (by simp : y in ⊤) (by simp)
    refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
    suffices h : (U inter {z | (f ⁻¹' {z} inter support ⇑c).Nonempty}).Finite by
      refine h.subset (inter_subset_inter_right U fun y hy => ?_)
      obtain ⟨x, (hx : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
      use x
      grind [mem_support]
    suffices (f ⁻¹' (U inter {z | (f ⁻¹' {z} inter c.support).Nonempty}) inter c.support).Finite from
      (this.image f).subset (fun a ha => by grind [Set.Nonempty])
    exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf.2 hU.1.1 hU.1.2).subset
      (by simp; grind)

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y)
  proof: rfl

中文:
引理 map_apply
  条件: (hf : 是谱映射 f) (c : locallyFinsupp X R) (y : Y)
  证明: rfl
-/
lemma map_apply (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y) :
    map f w hf c y = ∑ᶠ x in f ⁻¹' {y}, c x * w x := rfl

/--
lemma `support_map_subset_of_forall_mem` / 引理 `support_map_subset_of_forall_mem`

English:
lemma support_map_subset_of_forall_mem
  statement: (s : Set X) (t : Set Y) (hc : c.support subseteq s)
  proof: by
  intro y hy
  obtain ⟨x, (rfl : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  grind [mem_support]

@[simp]

中文:
引理 support_map_subset_of_对任意_mem
  结论: (s : 集合 X) (t : 集合 Y) (hc : c.support subseteq s)
  证明: by
  intro y hy
  obtain ⟨x, (rfl : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  grind [mem_support]

@[simp]

Depends on / 依赖: exists_ne_zero_of_finsum_mem_ne_zero, mem_support
-/
lemma support_map_subset_of_forall_mem (s : Set X) (t : Set Y) (hc : c.support subseteq s)
    (h : forall x : X, x in s -> w x != 0 -> f x in t) : (map f w hf c).support subseteq t := by
  intro y hy
  obtain ⟨x, (rfl : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  grind [mem_support]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: [PrespectralSpace X] (hw : forall z : X, w z = 1)
  proof: by
  ext
  simp [map, hw]

中文:
引理 map_id
  条件: [Prespectral空间 X] (hw : 对任意 z : X, w z = 1)
  证明: by
  ext
  simp [map, hw]
-/
lemma map_id [PrespectralSpace X] (hw : forall z : X, w z = 1) :
    map id w isSpectralMap_id c = c := by
  ext
  simp [map, hw]

end Function.locallyFinsupp
