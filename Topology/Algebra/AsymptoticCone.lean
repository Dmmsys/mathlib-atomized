/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Asymptotic cone of a set

This file defines the asymptotic cone of a set in a topological affine space.

## Implementation details

The asymptotic cone of a set $A$ is usually defined as the set of points $v$ for which there exist
sequences $t_n > 0$ and $x_n \in A$ such that $t_n \to 0$ and $t_n x_n \to v$. We take a different
approach here using filters: we define the asymptotic cone of `s` as the set of vectors `v` such
that `∃ᶠ p in Filter.atTop • 𝓝 v, p ∈ s` holds.

## Main definitions

* `AffineSpace.asymptoticNhds`: the filter of neighborhoods at infinity in some direction.
* `asymptoticCone`: the asymptotic cone of a subset of a topological affine space.

## Main statements

* `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  closed convex set `s`, then every ray of direction `v` starting from `s` is contained in `s`.
* `Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  convex set `s`, then every ray of direction `v` starting from the interior of `s` is contained in
  `s`.
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

section General

variable
  {k V P : Type*}
  [Field k] [LinearOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace V]

namespace AffineSpace

variable (k P) in
/-- In a topological affine space `P` over `k`, `AffineSpace.asymptoticNhds k P v` is the filter of
neighborhoods at infinity in directions near `v`. In a topological vector space, this is the filter
`Filter.atTop • 𝓝 v`. To support affine spaces, the actual definition is different and should be
considered an implementation detail. Use `AffineSpace.asymptoticNhds_eq_smul` or
`AffineSpace.asymptoticNhds_eq_smul_vadd` for unfolding. -/
@[irreducible]
/--
Definition of `asymptoticNhds` / `asymptoticNhds` 的定义

English:
definition asymptoticNhds
  signature: (v : V)
  body: ⨆ p, atTop (α := k) • 𝓝 v +ᵥ pure p

中文:
定义 asymptoticNhds
  签名: (v : V)
  定义体: ⨆ p, atTop (α := k) • 𝓝 v +ᵥ pure p
-/
def asymptoticNhds (v : V) : Filter P := ⨆ p, atTop (α := k) • 𝓝 v +ᵥ pure p

/--
theorem `asymptoticNhds_vadd_pure` / 定理 `asymptoticNhds_vadd_pure`

English:
theorem asymptoticNhds_vadd_pure
  given: (v : V) (p : P)
  proof: by
  simp_rw [asymptoticNhds, vadd_pure, map_iSup, map_map, Function.comp_def]
  refine (Equiv.vaddConst p).iSup_congr fun _ => ?_
  simp [add_vadd]

中文:
定理 asymptoticNhds_vadd_pure
  条件: (v : V) (p : P)
  证明: by
  simp_rw [asymptoticNhds, vadd_pure, map_iSup, map_map, Function.comp_def]
  refine (Equiv.vaddConst p).iSup_congr fun _ => ?_
  simp [add_vadd]

Depends on / 依赖: Equiv.vaddConst, Function, Function.comp_def, add_vadd, asymptoticNhds, comp_def, iSup_congr, map_iSup, map_map, simp_rw, vaddConst, vadd_pure
-/
theorem asymptoticNhds_vadd_pure (v : V) (p : P) :
    asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v := by
  simp_rw [asymptoticNhds, vadd_pure, map_iSup, map_map, Function.comp_def]
  refine (Equiv.vaddConst p).iSup_congr fun _ => ?_
  simp [add_vadd]

/--
theorem `vadd_asymptoticNhds` / 定理 `vadd_asymptoticNhds`

English:
theorem vadd_asymptoticNhds
  given: (u v : V)
  statement: u +ᵥ asymptoticNhds k P v = asymptoticNhds k P v
  proof: by
  have ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← asymptoticNhds_vadd_pure v p]
  simp_rw [← asymptoticNhds_vadd_pure v (u +ᵥ p), vadd_pure, ← Filter.map_vadd, map_map]
  congr with v
  exact vadd_comm u v p

中文:
定理 vadd_asymptoticNhds
  条件: (u v : V)
  结论: u +ᵥ asymptoticNhds k P v = asymptoticNhds k P v
  证明: by
  have ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← asymptoticNhds_vadd_pure v p]
  simp_rw [← asymptoticNhds_vadd_pure v (u +ᵥ p), vadd_pure, ← Filter.map_vadd, map_map]
  congr with v
  exact vadd_comm u v p

Depends on / 依赖: Filter, Filter.map_vadd, Nonempty, asymptoticNhds_vadd_pure, map_map, map_vadd, nth_rw, simp_rw, vadd_comm, vadd_pure
-/
theorem vadd_asymptoticNhds (u v : V) : u +ᵥ asymptoticNhds k P v = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← asymptoticNhds_vadd_pure v p]
  simp_rw [← asymptoticNhds_vadd_pure v (u +ᵥ p), vadd_pure, ← Filter.map_vadd, map_map]
  congr with v
  exact vadd_comm u v p

variable {α : Type*} {l : Filter α}

/--
theorem `_root_.Filter.Tendsto.asymptoticNhds_vadd_const` / 定理 `_root_.Filter.Tendsto.asymptoticNhds_vadd_const`

English:
theorem _root_.Filter.Tendsto.asymptoticNhds_vadd_const
  statement: {f : α -> V} {v : V} (p : P)
  proof: by
  rw [← asymptoticNhds_vadd_pure]; rw [vadd_pure]
  exact tendsto_map.comp hf

中文:
定理 _root_.滤子.收敛.asymptoticNhds_vadd_const
  结论: {f : α -> V} {v : V} (p : P)
  证明: by
  rw [← asymptoticNhds_vadd_pure]; rw [vadd_pure]
  exact tendsto_map.comp hf

Depends on / 依赖: asymptoticNhds_vadd_pure, tendsto_map, tendsto_map.comp, vadd_pure
-/
theorem _root_.Filter.Tendsto.asymptoticNhds_vadd_const {f : α -> V} {v : V} (p : P)
    (hf : Tendsto f l (asymptoticNhds k V v)) :
    Tendsto (fun x => f x +ᵥ p) l (asymptoticNhds k P v) := by
  rw [← asymptoticNhds_vadd_pure]; rw [vadd_pure]
  exact tendsto_map.comp hf

/--
theorem `_root_.Filter.Tendsto.const_vadd_asymptoticNhds` / 定理 `_root_.Filter.Tendsto.const_vadd_asymptoticNhds`

English:
theorem _root_.Filter.Tendsto.const_vadd_asymptoticNhds
  statement: {f : α -> P} {v : V} (u : V)
  proof: by
  rw [← vadd_asymptoticNhds u]; rw [← Filter.map_vadd]
  exact tendsto_map.comp hf

中文:
定理 _root_.滤子.收敛.const_vadd_asymptoticNhds
  结论: {f : α -> P} {v : V} (u : V)
  证明: by
  rw [← vadd_asymptoticNhds u]; rw [← Filter.map_vadd]
  exact tendsto_map.comp hf

Depends on / 依赖: Filter, Filter.map_vadd, map_vadd, tendsto_map, tendsto_map.comp, vadd_asymptoticNhds
-/
theorem _root_.Filter.Tendsto.const_vadd_asymptoticNhds {f : α -> P} {v : V} (u : V)
    (hf : Tendsto f l (asymptoticNhds k P v)) :
    Tendsto (fun x => u +ᵥ f x) l (asymptoticNhds k P v) := by
  rw [← vadd_asymptoticNhds u]; rw [← Filter.map_vadd]
  exact tendsto_map.comp hf

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]

/--
theorem `asymptoticNhds_eq_smul` / 定理 `asymptoticNhds_eq_smul`

English:
theorem asymptoticNhds_eq_smul
  given: (v : V)
  statement: asymptoticNhds k V v = atTop (α := k) • 𝓝 v
  proof: by
  unfold asymptoticNhds
  apply le_antisymm
  · refine iSup_le fun u => ?_
    simp_rw [vadd_eq_add, add_pure, ← map₂_smul, map_map₂, ← map_prod_eq_map₂]
    have : (fun x : k × V => x.1 • x.2 + u) =ᶠ[atTop ×ˢ 𝓝 v]
        (Function.uncurry (· • ·)) ∘ (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) := by
      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
      simp [h]
    rw [map_congr this]; rw [← map_map]
    apply map_mono
    have : Tendsto (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) (atTop ×ˢ 𝓝 v) _ :=
tendsto_fst.prodMk tendsto_snd.add tendsto_fst.inv_tendsto_atTop.smul_const u
    simpa
  · apply (le_iSup _ 0).trans'
    simp

中文:
定理 asymptoticNhds_eq_smul
  条件: (v : V)
  结论: asymptoticNhds k V v = atTop (α := k) • 𝓝 v
  证明: by
  unfold asymptoticNhds
  apply le_antisymm
  · refine iSup_le fun u => ?_
    simp_rw [vadd_eq_add, add_pure, ← map₂_smul, map_map₂, ← map_prod_eq_map₂]
    have : (fun x : k × V => x.1 • x.2 + u) =ᶠ[atTop ×ˢ 𝓝 v]
        (Function.uncurry (· • ·)) ∘ (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) := by
      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
      simp [h]
    rw [map_congr this]; rw [← map_map]
    apply map_mono
    have : Tendsto (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) (atTop ×ˢ 𝓝 v) _ :=
tendsto_fst.prodMk tendsto_snd.add tendsto_fst.inv_tendsto_atTop.smul_const u
    simpa
  · apply (le_iSup _ 0).trans'
    simp

Depends on / 依赖: Function, Function.uncurry, Tendsto, add_pure, asymptoticNhds, eventually, eventually_ne_atTop, filter_upwards, iSup_le, le_antisymm, map_congr, map_map, map_mono, simp_rw, tendsto_fst, tendsto_fst.eventually, uncurry, vadd_eq_add
-/
theorem asymptoticNhds_eq_smul (v : V) : asymptoticNhds k V v = atTop (α := k) • 𝓝 v := by
  unfold asymptoticNhds
  apply le_antisymm
  · refine iSup_le fun u => ?_
    simp_rw [vadd_eq_add, add_pure, ← map₂_smul, map_map₂, ← map_prod_eq_map₂]
    have : (fun x : k × V => x.1 • x.2 + u) =ᶠ[atTop ×ˢ 𝓝 v]
        (Function.uncurry (· • ·)) ∘ (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) := by
      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
      simp [h]
    rw [map_congr this]; rw [← map_map]
    apply map_mono
    have : Tendsto (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) (atTop ×ˢ 𝓝 v) _ :=
tendsto_fst.prodMk tendsto_snd.add tendsto_fst.inv_tendsto_atTop.smul_const u
    simpa
  · apply (le_iSup _ 0).trans'
    simp

/--
theorem `asymptoticNhds_eq_smul_vadd` / 定理 `asymptoticNhds_eq_smul_vadd`

English:
theorem asymptoticNhds_eq_smul_vadd
  given: (v : V) (p : P)
  proof: by
  rw [← asymptoticNhds_eq_smul]; rw [asymptoticNhds_vadd_pure]

中文:
定理 asymptoticNhds_eq_smul_vadd
  条件: (v : V) (p : P)
  证明: by
  rw [← asymptoticNhds_eq_smul]; rw [asymptoticNhds_vadd_pure]

Depends on / 依赖: asymptoticNhds_eq_smul, asymptoticNhds_vadd_pure
-/
theorem asymptoticNhds_eq_smul_vadd (v : V) (p : P) :
    asymptoticNhds k P v = atTop (α := k) • 𝓝 v +ᵥ pure p := by
  rw [← asymptoticNhds_eq_smul]; rw [asymptoticNhds_vadd_pure]

instance {v : V} : (asymptoticNhds k P v).NeBot := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd v p]
  infer_instance

/--
theorem `asymptoticNhds_zero'` / 定理 `asymptoticNhds_zero'`

English:
theorem asymptoticNhds_zero'
  statement: asymptoticNhds k V (0 : V) = ⊤
  proof: by
  rw [← top_le_iff]; rw [← iSup_pure_eq_top]; rw [iSup_le_iff]
  intro v
  rw [← map_const (f := atTop (α := k))]
  have : (fun _ => v) =ᶠ[atTop (α := k)]
      (Function.uncurry (· • ·)) ∘ (fun c => (c, c⁻¹ • v)) := by
    filter_upwards [eventually_ne_atTop 0] with _ h
    simp [h]
  rw [map_congr this]; rw [← map_map]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  apply map_mono
  have : Tendsto (fun c => (c, c⁻¹ • v)) (atTop (α := k)) _ :=
tendsto_id.prodMk tendsto_inv_atTop_zero.smul_const v
  simpa

@[simp]

中文:
定理 asymptoticNhds_zero'
  结论: asymptoticNhds k V (0 : V) = ⊤
  证明: by
  rw [← top_le_iff]; rw [← iSup_pure_eq_top]; rw [iSup_le_iff]
  intro v
  rw [← map_const (f := atTop (α := k))]
  have : (fun _ => v) =ᶠ[atTop (α := k)]
      (Function.uncurry (· • ·)) ∘ (fun c => (c, c⁻¹ • v)) := by
    filter_upwards [eventually_ne_atTop 0] with _ h
    simp [h]
  rw [map_congr this]; rw [← map_map]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  apply map_mono
  have : Tendsto (fun c => (c, c⁻¹ • v)) (atTop (α := k)) _ :=
tendsto_id.prodMk tendsto_inv_atTop_zero.smul_const v
  simpa

@[simp]
-/
private theorem asymptoticNhds_zero' : asymptoticNhds k V (0 : V) = ⊤ := by
  rw [← top_le_iff]; rw [← iSup_pure_eq_top]; rw [iSup_le_iff]
  intro v
  rw [← map_const (f := atTop (α := k))]
  have : (fun _ => v) =ᶠ[atTop (α := k)]
      (Function.uncurry (· • ·)) ∘ (fun c => (c, c⁻¹ • v)) := by
    filter_upwards [eventually_ne_atTop 0] with _ h
    simp [h]
  rw [map_congr this]; rw [← map_map]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  apply map_mono
  have : Tendsto (fun c => (c, c⁻¹ • v)) (atTop (α := k)) _ :=
tendsto_id.prodMk tendsto_inv_atTop_zero.smul_const v
  simpa

@[simp]
/--
theorem `asymptoticNhds_zero` / 定理 `asymptoticNhds_zero`

English:
theorem asymptoticNhds_zero
  statement: asymptoticNhds k P (0 : V) = ⊤
  proof: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← asymptoticNhds_vadd_pure 0 p]; rw [asymptoticNhds_zero']; rw [vadd_pure]
  exact (Equiv.vaddConst p).surjective.filter_map_top

中文:
定理 asymptoticNhds_zero
  结论: asymptoticNhds k P (0 : V) = ⊤
  证明: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← asymptoticNhds_vadd_pure 0 p]; rw [asymptoticNhds_zero']; rw [vadd_pure]
  exact (Equiv.vaddConst p).surjective.filter_map_top

Depends on / 依赖: Equiv.vaddConst, Nonempty, asymptoticNhds_vadd_pure, asymptoticNhds_zero, filter_map_top, surjective, surjective.filter_map_top, vaddConst, vadd_pure
-/
theorem asymptoticNhds_zero : asymptoticNhds k P (0 : V) = ⊤ := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← asymptoticNhds_vadd_pure 0 p]; rw [asymptoticNhds_zero']; rw [vadd_pure]
  exact (Equiv.vaddConst p).surjective.filter_map_top

/--
theorem `_root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds` / 定理 `_root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds`

English:
theorem _root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds
  statement: {f : α -> k} {g : α -> V} {v : V}
  proof: by
  rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  exact tendsto_map.comp (hf.prodMk hg)

中文:
定理 _root_.滤子.收敛.atTop_smul_nhds_tendsto_asymptoticNhds
  结论: {f : α -> k} {g : α -> V} {v : V}
  证明: by
  rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  exact tendsto_map.comp (hf.prodMk hg)

Depends on / 依赖: asymptoticNhds_eq_smul, hf.prodMk, prodMk, tendsto_map, tendsto_map.comp
-/
theorem _root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds {f : α -> k} {g : α -> V} {v : V}
    (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 v)) :
    Tendsto (fun x => f x • g x) l (asymptoticNhds k V v) := by
  rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]
  exact tendsto_map.comp (hf.prodMk hg)

/--
theorem `_root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds` / 定理 `_root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds`

English:
theorem _root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds
  statement: {f : α -> k} (v : V)
  proof: hf.atTop_smul_nhds_tendsto_asymptoticNhds tendsto_const_nhds

中文:
定理 _root_.滤子.收敛.atTop_smul_const_tendsto_asymptoticNhds
  结论: {f : α -> k} (v : V)
  证明: hf.atTop_smul_nhds_tendsto_asymptoticNhds tendsto_const_nhds

Depends on / 依赖: CompactSpace, UniformSpace, atTop_smul_nhds_tendsto_asymptoticNhds, complete_of_compact, hf.atTop_smul_nhds_tendsto_asymptoticNhds, tendsto_const_nhds
-/
theorem _root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds {f : α -> k} (v : V)
    (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • v) l (asymptoticNhds k V v) :=
  hf.atTop_smul_nhds_tendsto_asymptoticNhds tendsto_const_nhds

/--
theorem `asymptoticNhds_smul` / 定理 `asymptoticNhds_smul`

English:
theorem asymptoticNhds_smul
  given: (v : V) {c : k} (hc : 0 < c)
  proof: by
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [asymptoticNhds_eq_smul_vadd _ p,
    ← show map (c • ·) (𝓝 v) = 𝓝 (c • v) from
      (Homeomorph.smulOfNeZero c hc.ne').map_nhds_eq v,
    ← map₂_smul, map₂_map_right, smul_smul, ← map₂_map_left,
    show map (· * c) atTop = atTop from (OrderIso.mulRight₀ _ hc).map_atTop]

@[simp]

中文:
定理 asymptoticNhds_smul
  条件: (v : V) {c : k} (hc : 0 < c)
  证明: by
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [asymptoticNhds_eq_smul_vadd _ p,
    ← show map (c • ·) (𝓝 v) = 𝓝 (c • v) from
      (Homeomorph.smulOfNeZero c hc.ne').map_nhds_eq v,
    ← map₂_smul, map₂_map_right, smul_smul, ← map₂_map_left,
    show map (· * c) atTop = atTop from (OrderIso.mulRight₀ _ hc).map_atTop]

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, Nonempty, OrderIso, OrderIso.mulRight, asymptoticNhds_eq_smul_vadd, hc.ne, map_atTop, map_nhds_eq, simp_rw, smulOfNeZero, smul_smul
-/
theorem asymptoticNhds_smul (v : V) {c : k} (hc : 0 < c) :
    asymptoticNhds k P (c • v) = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [asymptoticNhds_eq_smul_vadd _ p,
    ← show map (c • ·) (𝓝 v) = 𝓝 (c • v) from
      (Homeomorph.smulOfNeZero c hc.ne').map_nhds_eq v,
    ← map₂_smul, map₂_map_right, smul_smul, ← map₂_map_left,
    show map (· * c) atTop = atTop from (OrderIso.mulRight₀ _ hc).map_atTop]

@[simp]
/--
theorem `nhds_bind_asymptoticNhds` / 定理 `nhds_bind_asymptoticNhds`

English:
theorem nhds_bind_asymptoticNhds
  given: (v : V)
  proof: by
  apply le_antisymm
  · have ⟨p⟩ : Nonempty P := inferInstance
    eta_expand
    simp_rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure]
    nth_rw 2 [← nhds_bind_nhds]
    simp only [le_def, mem_map, ← map₂_smul, mem_map₂_iff, mem_bind]
    grind
  · rw [← pure_bind v (asymptoticNhds k P)]
    exact bind_mono (pure_le_nhds v) .rfl

@[simp]

中文:
定理 nhds_bind_asymptoticNhds
  条件: (v : V)
  证明: by
  apply le_antisymm
  · have ⟨p⟩ : Nonempty P := inferInstance
    eta_expand
    simp_rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure]
    nth_rw 2 [← nhds_bind_nhds]
    simp only [le_def, mem_map, ← map₂_smul, mem_map₂_iff, mem_bind]
    grind
  · rw [← pure_bind v (asymptoticNhds k P)]
    exact bind_mono (pure_le_nhds v) .rfl

@[simp]

Depends on / 依赖: Nonempty, asymptoticNhds, asymptoticNhds_eq_smul_vadd, bind_mono, eta_expand, le_antisymm, le_def, mem_bind, mem_map, nhds_bind_nhds, nth_rw, pure_bind, pure_le_nhds, simp_rw, vadd_pure
-/
theorem nhds_bind_asymptoticNhds (v : V) :
    (𝓝 v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  apply le_antisymm
  · have ⟨p⟩ : Nonempty P := inferInstance
    eta_expand
    simp_rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure]
    nth_rw 2 [← nhds_bind_nhds]
    simp only [le_def, mem_map, ← map₂_smul, mem_map₂_iff, mem_bind]
    grind
  · rw [← pure_bind v (asymptoticNhds k P)]
    exact bind_mono (pure_le_nhds v) .rfl

@[simp]
/--
theorem `asymptoticNhds_bind_nhds` / 定理 `asymptoticNhds_bind_nhds`

English:
theorem asymptoticNhds_bind_nhds
  given: [TopologicalSpace P] [IsTopologicalAddTorsor P] (v : V)
  proof: by
  refine le_antisymm (fun s h => ?_) (bind_mono le_rfl (.of_forall pure_le_nhds))
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd _ p]; rw [vadd_pure] at h ⊢
  rw [← nhds_bind_nhds] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hs⟩ := h
  rw [mem_bind] at ht₂
  obtain ⟨t₃, ht₃, ht₂⟩ := ht₂
  rw [bind_map]; rw [mem_bind]
  refine ⟨(t₁ inter Set.Ioi 0) • t₃, smul_mem_smul (inter_mem ht₁ (Ioi_mem_atTop _)) ht₃,
    Set.forall_mem_image2.mpr fun c ⟨hc₁, hc₂⟩ u hu => ?_⟩
  rw [show s = (· -ᵥ p) ⁻¹' ((· +ᵥ p) ⁻¹' s) by simp [Set.preimage_preimage]]
  apply tendsto_id.vsub tendsto_const_nhds
  rw [vadd_vsub]
  filter_upwards [smul_mem_nhds_smul₀ hc₂.ne' (ht₂ u hu)]
  rw [← Set.image_smul]; rw [Set.forall_mem_image]
  exact fun w hw => hs (Set.smul_mem_smul hc₁ hw)

@[simp]

中文:
定理 asymptoticNhds_bind_nhds
  条件: [拓扑空间 P] [是TopologicalAddTorsor P] (v : V)
  证明: by
  refine le_antisymm (fun s h => ?_) (bind_mono le_rfl (.of_forall pure_le_nhds))
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd _ p]; rw [vadd_pure] at h ⊢
  rw [← nhds_bind_nhds] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hs⟩ := h
  rw [mem_bind] at ht₂
  obtain ⟨t₃, ht₃, ht₂⟩ := ht₂
  rw [bind_map]; rw [mem_bind]
  refine ⟨(t₁ inter Set.Ioi 0) • t₃, smul_mem_smul (inter_mem ht₁ (Ioi_mem_atTop _)) ht₃,
    Set.forall_mem_image2.mpr fun c ⟨hc₁, hc₂⟩ u hu => ?_⟩
  rw [show s = (· -ᵥ p) ⁻¹' ((· +ᵥ p) ⁻¹' s) by simp [Set.preimage_preimage]]
  apply tendsto_id.vsub tendsto_const_nhds
  rw [vadd_vsub]
  filter_upwards [smul_mem_nhds_smul₀ hc₂.ne' (ht₂ u hu)]
  rw [← Set.image_smul]; rw [Set.forall_mem_image]
  exact fun w hw => hs (Set.smul_mem_smul hc₁ hw)

@[simp]

Depends on / 依赖: Ioi_mem_atTop, Nonempty, Set.Ioi, Set.forall_mem_image2.mpr, asymptoticNhds_eq_smul_vadd, bind_map, bind_mono, forall_mem_image2, inter_mem, le_antisymm, le_rfl, mem_bind, nhds_bind_nhds, of_forall, pure_le_nhds, smul_mem_smul, vadd_pure
-/
theorem asymptoticNhds_bind_nhds [TopologicalSpace P] [IsTopologicalAddTorsor P] (v : V) :
    (asymptoticNhds k P v).bind 𝓝 = asymptoticNhds k P v := by
  refine le_antisymm (fun s h => ?_) (bind_mono le_rfl (.of_forall pure_le_nhds))
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd _ p]; rw [vadd_pure] at h ⊢
  rw [← nhds_bind_nhds] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hs⟩ := h
  rw [mem_bind] at ht₂
  obtain ⟨t₃, ht₃, ht₂⟩ := ht₂
  rw [bind_map]; rw [mem_bind]
  refine ⟨(t₁ inter Set.Ioi 0) • t₃, smul_mem_smul (inter_mem ht₁ (Ioi_mem_atTop _)) ht₃,
    Set.forall_mem_image2.mpr fun c ⟨hc₁, hc₂⟩ u hu => ?_⟩
  rw [show s = (· -ᵥ p) ⁻¹' ((· +ᵥ p) ⁻¹' s) by simp [Set.preimage_preimage]]
  apply tendsto_id.vsub tendsto_const_nhds
  rw [vadd_vsub]
  filter_upwards [smul_mem_nhds_smul₀ hc₂.ne' (ht₂ u hu)]
  rw [← Set.image_smul]; rw [Set.forall_mem_image]
  exact fun w hw => hs (Set.smul_mem_smul hc₁ hw)

@[simp]
/--
theorem `asymptoticNhds_bind_asymptoticNhds` / 定理 `asymptoticNhds_bind_asymptoticNhds`

English:
theorem asymptoticNhds_bind_asymptoticNhds
  given: (v : V)
  proof: by
  refine Filter.ext' fun p => ?_
  rw [asymptoticNhds_eq_smul]; rw [eventually_bind]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [eventually_map]; rw [← nhds_bind_asymptoticNhds]; rw [eventually_bind]
  nth_rw 2 [← map_snd_prod (atTop (α := k)) (𝓝 v)]
  rw [eventually_map]
  apply eventually_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ (hc : 0 < c)
  simp only [asymptoticNhds_smul _ hc]

中文:
定理 asymptoticNhds_bind_asymptoticNhds
  条件: (v : V)
  证明: by
  refine Filter.ext' fun p => ?_
  rw [asymptoticNhds_eq_smul]; rw [eventually_bind]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [eventually_map]; rw [← nhds_bind_asymptoticNhds]; rw [eventually_bind]
  nth_rw 2 [← map_snd_prod (atTop (α := k)) (𝓝 v)]
  rw [eventually_map]
  apply eventually_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ (hc : 0 < c)
  simp only [asymptoticNhds_smul _ hc]

Depends on / 依赖: Filter, Filter.ext, asymptoticNhds_eq_smul, asymptoticNhds_smul, eventually, eventually_bind, eventually_congr, eventually_gt_atTop, eventually_map, filter_upwards, map_snd_prod, nhds_bind_asymptoticNhds, nth_rw, tendsto_fst, tendsto_fst.eventually
-/
theorem asymptoticNhds_bind_asymptoticNhds (v : V) :
    (asymptoticNhds k V v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  refine Filter.ext' fun p => ?_
  rw [asymptoticNhds_eq_smul]; rw [eventually_bind]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [eventually_map]; rw [← nhds_bind_asymptoticNhds]; rw [eventually_bind]
  nth_rw 2 [← map_snd_prod (atTop (α := k)) (𝓝 v)]
  rw [eventually_map]
  apply eventually_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ (hc : 0 < c)
  simp only [asymptoticNhds_smul _ hc]

end AffineSpace

open AffineSpace

variable (k) in
/--
Definition of `asymptoticCone` / `asymptoticCone` 的定义

English:
definition asymptoticCone
  signature: (s : Set P)
  body: {v | existsᶠ p in asymptoticNhds k P v, p in s}

中文:
定义 asymptoticCone
  签名: (s : 集合 P)
  定义体: {v | existsᶠ p in asymptoticNhds k P v, p in s}

Depends on / 依赖: asymptoticNhds
-/
def asymptoticCone (s : Set P) : Set V := {v | existsᶠ p in asymptoticNhds k P v, p in s}

/--
theorem `mem_asymptoticCone_iff` / 定理 `mem_asymptoticCone_iff`

English:
theorem mem_asymptoticCone_iff
  given: {v : V} {s : Set P}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_asymptoticCone_iff
  条件: {v : V} {s : 集合 P}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_asymptoticCone_iff {v : V} {s : Set P} :
    v in asymptoticCone k s ↔ existsᶠ p in asymptoticNhds k P v, p in s :=
  Iff.rfl

@[simp]
/--
theorem `asymptoticCone_empty` / 定理 `asymptoticCone_empty`

English:
theorem asymptoticCone_empty
  statement: asymptoticCone k (∅ : Set P) = ∅
  proof: Set.eq_empty_iff_forall_notMem.mpr fun _ => frequently_false _

@[gcongr]

中文:
定理 asymptoticCone_empty
  结论: asymptoticCone k (∅ : 集合 P) = ∅
  证明: Set.eq_empty_iff_forall_notMem.mpr fun _ => frequently_false _

@[gcongr]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem.mpr, eq_empty_iff_forall_notMem, frequently_false
-/
theorem asymptoticCone_empty : asymptoticCone k (∅ : Set P) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ => frequently_false _

@[gcongr]
/--
theorem `asymptoticCone_mono` / 定理 `asymptoticCone_mono`

English:
theorem asymptoticCone_mono
  given: {s t : Set P} (h : s subseteq t)
  statement: asymptoticCone k s subseteq asymptoticCone k t
  proof: fun _ h' => h'.mono h

中文:
定理 asymptoticCone_mono
  条件: {s t : 集合 P} (h : s subseteq t)
  结论: asymptoticCone k s subseteq asymptoticCone k t
  证明: fun _ h' => h'.mono h
-/
theorem asymptoticCone_mono {s t : Set P} (h : s subseteq t) : asymptoticCone k s subseteq asymptoticCone k t :=
  fun _ h' => h'.mono h

/--
theorem `asymptoticCone_union` / 定理 `asymptoticCone_union`

English:
theorem asymptoticCone_union
  given: {s t : Set P}
  proof: by
  ext
  simp only [Set.mem_union, mem_asymptoticCone_iff, Filter.frequently_or_distrib]

中文:
定理 asymptoticCone_union
  条件: {s t : 集合 P}
  证明: by
  ext
  simp only [Set.mem_union, mem_asymptoticCone_iff, Filter.frequently_or_distrib]

Depends on / 依赖: Filter, Filter.frequently_or_distrib, Set.mem_union, frequently_or_distrib, mem_asymptoticCone_iff, mem_union
-/
theorem asymptoticCone_union {s t : Set P} :
    asymptoticCone k (s union t) = asymptoticCone k s union asymptoticCone k t := by
  ext
  simp only [Set.mem_union, mem_asymptoticCone_iff, Filter.frequently_or_distrib]

/--
theorem `asymptoticCone_biUnion` / 定理 `asymptoticCone_biUnion`

English:
theorem asymptoticCone_biUnion
  given: {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set P)
  proof: by
  induction s, hs using Set.Finite.induction_on <;>
    simp [asymptoticCone_union, *]

中文:
定理 asymptoticCone_biUnion
  条件: {ι : 类型} {s : 集合 ι} (hs : s.有限) (f : ι -> 集合 P)
  证明: by
  induction s, hs using Set.Finite.induction_on <;>
    simp [asymptoticCone_union, *]

Depends on / 依赖: Finite, Set.Finite.induction_on, asymptoticCone_union, induction_on
-/
theorem asymptoticCone_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set P) :
    asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, asymptoticCone k (f i) := by
  induction s, hs using Set.Finite.induction_on <;>
    simp [asymptoticCone_union, *]

/--
theorem `asymptoticCone_sUnion` / 定理 `asymptoticCone_sUnion`

English:
theorem asymptoticCone_sUnion
  given: {S : Set (Set P)} (hS : S.Finite)
  proof: by
  rw [Set.sUnion_eq_biUnion]; rw [asymptoticCone_biUnion hS]

nonrec theorem Finset.asymptoticCone_biUnion {ι : Type*} (s : Finset ι) (f : ι -> Set P) :
    asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, asymptoticCone k (f i) :=
  asymptoticCone_biUnion s.finite_toSet f

中文:
定理 asymptoticCone_sUnion
  条件: {S : 集合 (集合 P)} (hS : S.有限)
  证明: by
  rw [Set.sUnion_eq_biUnion]; rw [asymptoticCone_biUnion hS]

nonrec theorem Finset.asymptoticCone_biUnion {ι : Type*} (s : Finset ι) (f : ι -> Set P) :
    asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, asymptoticCone k (f i) :=
  asymptoticCone_biUnion s.finite_toSet f

Depends on / 依赖: Set.sUnion_eq_biUnion, asymptoticCone_biUnion, sUnion_eq_biUnion
-/
theorem asymptoticCone_sUnion {S : Set (Set P)} (hS : S.Finite) :
    asymptoticCone k (⋃₀ S) = ⋃ s in S, asymptoticCone k s := by
  rw [Set.sUnion_eq_biUnion]; rw [asymptoticCone_biUnion hS]

nonrec theorem Finset.asymptoticCone_biUnion {ι : Type*} (s : Finset ι) (f : ι -> Set P) :
    asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, asymptoticCone k (f i) :=
  asymptoticCone_biUnion s.finite_toSet f

/--
theorem `asymptoticCone_iUnion_of_finite` / 定理 `asymptoticCone_iUnion_of_finite`

English:
theorem asymptoticCone_iUnion_of_finite
  given: {ι : Type*} [Finite ι] (f : ι -> Set P)
  proof: by
  rw [← Set.sUnion_range]; rw [asymptoticCone_sUnion (Set.finite_range f)]; rw [Set.biUnion_range]

中文:
定理 asymptoticCone_iUnion_of_finite
  条件: {ι : 类型} [有限 ι] (f : ι -> 集合 P)
  证明: by
  rw [← Set.sUnion_range]; rw [asymptoticCone_sUnion (Set.finite_range f)]; rw [Set.biUnion_range]

Depends on / 依赖: Set.biUnion_range, Set.finite_range, Set.sUnion_range, asymptoticCone_sUnion, biUnion_range, finite_range, sUnion_range
-/
theorem asymptoticCone_iUnion_of_finite {ι : Type*} [Finite ι] (f : ι -> Set P) :
    asymptoticCone k (⋃ i, f i) = ⋃ i, asymptoticCone k (f i) := by
  rw [← Set.sUnion_range]; rw [asymptoticCone_sUnion (Set.finite_range f)]; rw [Set.biUnion_range]

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]

/--
theorem `zero_mem_asymptoticCone` / 定理 `zero_mem_asymptoticCone`

English:
theorem zero_mem_asymptoticCone
  given: {s : Set P}
  statement: 0 in asymptoticCone k s ↔ s.Nonempty
  proof: by
  refine ⟨Function.mtr ?_, fun _ => ?_⟩
  · simp +contextual [Set.not_nonempty_iff_eq_empty]
  · simpa [mem_asymptoticCone_iff]

中文:
定理 zero_mem_asymptoticCone
  条件: {s : 集合 P}
  结论: 0 in asymptoticCone k s ↔ s.非空
  证明: by
  refine ⟨Function.mtr ?_, fun _ => ?_⟩
  · simp +contextual [Set.not_nonempty_iff_eq_empty]
  · simpa [mem_asymptoticCone_iff]

Depends on / 依赖: Function, Function.mtr, Set.not_nonempty_iff_eq_empty, contextual, mem_asymptoticCone_iff, not_nonempty_iff_eq_empty
-/
theorem zero_mem_asymptoticCone {s : Set P} : 0 in asymptoticCone k s ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun _ => ?_⟩
  · simp +contextual [Set.not_nonempty_iff_eq_empty]
  · simpa [mem_asymptoticCone_iff]

/--
theorem `asymptoticCone_nonempty` / 定理 `asymptoticCone_nonempty`

English:
theorem asymptoticCone_nonempty
  given: {s : Set P}
  statement: (asymptoticCone k s).Nonempty ↔ s.Nonempty
  proof: by
  refine ⟨Function.mtr ?_, fun h => ⟨0, zero_mem_asymptoticCone.mpr h⟩⟩
  simp +contextual [Set.not_nonempty_iff_eq_empty]

@[simp]

中文:
定理 asymptoticCone_nonempty
  条件: {s : 集合 P}
  结论: (asymptoticCone k s).非空 ↔ s.非空
  证明: by
  refine ⟨Function.mtr ?_, fun h => ⟨0, zero_mem_asymptoticCone.mpr h⟩⟩
  simp +contextual [Set.not_nonempty_iff_eq_empty]

@[simp]

Depends on / 依赖: Function, Function.mtr, Set.not_nonempty_iff_eq_empty, contextual, not_nonempty_iff_eq_empty, zero_mem_asymptoticCone, zero_mem_asymptoticCone.mpr
-/
theorem asymptoticCone_nonempty {s : Set P} : (asymptoticCone k s).Nonempty ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun h => ⟨0, zero_mem_asymptoticCone.mpr h⟩⟩
  simp +contextual [Set.not_nonempty_iff_eq_empty]

@[simp]
/--
theorem `smul_mem_asymptoticCone_iff` / 定理 `smul_mem_asymptoticCone_iff`

English:
theorem smul_mem_asymptoticCone_iff
  given: {s : Set P} {c : k} {v : V} (hc : 0 < c)
  proof: by
  simp_rw [mem_asymptoticCone_iff, asymptoticNhds_smul v hc]

中文:
定理 smul_mem_asymptoticCone_iff
  条件: {s : 集合 P} {c : k} {v : V} (hc : 0 < c)
  证明: by
  simp_rw [mem_asymptoticCone_iff, asymptoticNhds_smul v hc]

Depends on / 依赖: asymptoticNhds_smul, mem_asymptoticCone_iff, simp_rw
-/
theorem smul_mem_asymptoticCone_iff {s : Set P} {c : k} {v : V} (hc : 0 < c) :
    c • v in asymptoticCone k s ↔ v in asymptoticCone k s := by
  simp_rw [mem_asymptoticCone_iff, asymptoticNhds_smul v hc]

/--
theorem `smul_mem_asymptoticCone` / 定理 `smul_mem_asymptoticCone`

English:
theorem smul_mem_asymptoticCone
  statement: {s : Set P} {c : k} {v : V} (hc : 0 <= c)
  proof: by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mem_asymptoticCone, ← asymptoticCone_nonempty (k := k)]; exact ⟨v, h⟩
  · rwa [smul_mem_asymptoticCone_iff hc]

中文:
定理 smul_mem_asymptoticCone
  结论: {s : 集合 P} {c : k} {v : V} (hc : 0 <= c)
  证明: by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mem_asymptoticCone, ← asymptoticCone_nonempty (k := k)]; exact ⟨v, h⟩
  · rwa [smul_mem_asymptoticCone_iff hc]

Depends on / 依赖: asymptoticCone_nonempty, eq_or_lt, hc.eq_or_lt, smul_mem_asymptoticCone_iff, zero_mem_asymptoticCone, zero_smul
-/
theorem smul_mem_asymptoticCone {s : Set P} {c : k} {v : V} (hc : 0 <= c)
    (h : v in asymptoticCone k s) : c • v in asymptoticCone k s := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mem_asymptoticCone, ← asymptoticCone_nonempty (k := k)]; exact ⟨v, h⟩
  · rwa [smul_mem_asymptoticCone_iff hc]

/--
theorem `asymptoticCone_eq_closure_of_forall_smul_mem` / 定理 `asymptoticCone_eq_closure_of_forall_smul_mem`

English:
theorem asymptoticCone_eq_closure_of_forall_smul_mem
  statement: {s : Set V}
  proof: by
  ext v
  rw [mem_closure_iff_frequently]; rw [← map_snd_prod (atTop (α := k)) (𝓝 v)]; rw [frequently_map]; rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map]
  apply frequently_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ hc
  refine ⟨fun hu => ?_, hs c hc u⟩
  specialize hs c⁻¹ (inv_pos_of_pos hc) (c • u) hu
  rwa [inv_smul_smul₀ hc.ne'] at hs

中文:
定理 asymptoticCone_eq_closure_of_对任意_smul_mem
  结论: {s : 集合 V}
  证明: by
  ext v
  rw [mem_closure_iff_frequently]; rw [← map_snd_prod (atTop (α := k)) (𝓝 v)]; rw [frequently_map]; rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map]
  apply frequently_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ hc
  refine ⟨fun hu => ?_, hs c hc u⟩
  specialize hs c⁻¹ (inv_pos_of_pos hc) (c • u) hu
  rwa [inv_smul_smul₀ hc.ne'] at hs

Depends on / 依赖: asymptoticNhds_eq_smul, eventually, eventually_gt_atTop, filter_upwards, frequently_congr, frequently_map, hc.ne, inv_pos_of_pos, map_snd_prod, mem_asymptoticCone_iff, mem_closure_iff_frequently, specialize, tendsto_fst, tendsto_fst.eventually
-/
theorem asymptoticCone_eq_closure_of_forall_smul_mem {s : Set V}
    (hs : forall c : k, 0 < c -> forall x in s, c • x in s) : asymptoticCone k s = closure s := by
  ext v
  rw [mem_closure_iff_frequently]; rw [← map_snd_prod (atTop (α := k)) (𝓝 v)]; rw [frequently_map]; rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map]
  apply frequently_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ hc
  refine ⟨fun hu => ?_, hs c hc u⟩
  specialize hs c⁻¹ (inv_pos_of_pos hc) (c • u) hu
  rwa [inv_smul_smul₀ hc.ne'] at hs

/--
theorem `asymptoticCone_submodule` / 定理 `asymptoticCone_submodule`

English:
theorem asymptoticCone_submodule
  given: {s : Submodule k V}
  statement: asymptoticCone k (s : Set V) = closure s
  proof: asymptoticCone_eq_closure_of_forall_smul_mem fun _ _ _ h => s.smul_mem _ h

中文:
定理 asymptoticCone_submodule
  条件: {s : 子模 k V}
  结论: asymptoticCone k (s : 集合 V) = closure s
  证明: asymptoticCone_eq_closure_of_forall_smul_mem fun _ _ _ h => s.smul_mem _ h

Depends on / 依赖: asymptoticCone_eq_closure_of_forall_smul_mem, s.smul_mem, smul_mem
-/
theorem asymptoticCone_submodule {s : Submodule k V} : asymptoticCone k (s : Set V) = closure s :=
  asymptoticCone_eq_closure_of_forall_smul_mem fun _ _ _ h => s.smul_mem _ h

/--
theorem `asymptoticCone_affineSubspace` / 定理 `asymptoticCone_affineSubspace`

English:
theorem asymptoticCone_affineSubspace
  given: {s : AffineSubspace k P} (hs : (s : Set P).Nonempty)
  proof: by
  have ⟨p, hp⟩ := hs
  ext v
  simp_rw [← asymptoticCone_submodule, mem_asymptoticCone_iff, ← asymptoticNhds_vadd_pure v p,
    vadd_pure, frequently_map, SetLike.mem_coe, s.vadd_mem_iff_mem_direction _ hp]

@[simp]

中文:
定理 asymptoticCone_affineSubspace
  条件: {s : 仿射子空间 k P} (hs : (s : 集合 P).非空)
  证明: by
  have ⟨p, hp⟩ := hs
  ext v
  simp_rw [← asymptoticCone_submodule, mem_asymptoticCone_iff, ← asymptoticNhds_vadd_pure v p,
    vadd_pure, frequently_map, SetLike.mem_coe, s.vadd_mem_iff_mem_direction _ hp]

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe, asymptoticCone_submodule, asymptoticNhds_vadd_pure, frequently_map, mem_asymptoticCone_iff, mem_coe, s.vadd_mem_iff_mem_direction, simp_rw, vadd_mem_iff_mem_direction, vadd_pure
-/
theorem asymptoticCone_affineSubspace {s : AffineSubspace k P} (hs : (s : Set P).Nonempty) :
    asymptoticCone k (s : Set P) = closure s.direction := by
  have ⟨p, hp⟩ := hs
  ext v
  simp_rw [← asymptoticCone_submodule, mem_asymptoticCone_iff, ← asymptoticNhds_vadd_pure v p,
    vadd_pure, frequently_map, SetLike.mem_coe, s.vadd_mem_iff_mem_direction _ hp]

@[simp]
/--
theorem `asymptoticCone_univ` / 定理 `asymptoticCone_univ`

English:
theorem asymptoticCone_univ
  statement: asymptoticCone k (Set.univ : Set P) = Set.univ
  proof: by
  rw [← AffineSubspace.top_coe k]; rw [asymptoticCone_affineSubspace Set.univ_nonempty]; rw [AffineSubspace.direction_top]; rw [Submodule.top_coe]; rw [closure_univ]

中文:
定理 asymptoticCone_univ
  结论: asymptoticCone k (集合.univ : 集合 P) = 集合.univ
  证明: by
  rw [← AffineSubspace.top_coe k]; rw [asymptoticCone_affineSubspace Set.univ_nonempty]; rw [AffineSubspace.direction_top]; rw [Submodule.top_coe]; rw [closure_univ]

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_top, AffineSubspace.top_coe, Set.univ_nonempty, Submodule, Submodule.top_coe, asymptoticCone_affineSubspace, closure_univ, direction_top, top_coe, univ_nonempty
-/
theorem asymptoticCone_univ : asymptoticCone k (Set.univ : Set P) = Set.univ := by
  rw [← AffineSubspace.top_coe k]; rw [asymptoticCone_affineSubspace Set.univ_nonempty]; rw [AffineSubspace.direction_top]; rw [Submodule.top_coe]; rw [closure_univ]

/--
theorem `asymptoticCone_closure` / 定理 `asymptoticCone_closure`

English:
theorem asymptoticCone_closure
  given: [TopologicalSpace P] [IsTopologicalAddTorsor P] (s : Set P)
  proof: by
  ext
  simp_rw [mem_asymptoticCone_iff, mem_closure_iff_frequently, ← frequently_bind,
    asymptoticNhds_bind_nhds]

中文:
定理 asymptoticCone_closure
  条件: [拓扑空间 P] [是TopologicalAddTorsor P] (s : 集合 P)
  证明: by
  ext
  simp_rw [mem_asymptoticCone_iff, mem_closure_iff_frequently, ← frequently_bind,
    asymptoticNhds_bind_nhds]

Depends on / 依赖: asymptoticNhds_bind_nhds, frequently_bind, mem_asymptoticCone_iff, mem_closure_iff_frequently, simp_rw
-/
theorem asymptoticCone_closure [TopologicalSpace P] [IsTopologicalAddTorsor P] (s : Set P) :
    asymptoticCone k (closure s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, mem_closure_iff_frequently, ← frequently_bind,
    asymptoticNhds_bind_nhds]

/--
theorem `isClosed_asymptoticCone` / 定理 `isClosed_asymptoticCone`

English:
theorem isClosed_asymptoticCone
  given: {s : Set P}
  statement: IsClosed (asymptoticCone k s)
  proof: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [isClosed_iff_frequently]
  intro v h
  simp_rw [mem_asymptoticCone_iff, ← frequently_bind, nhds_bind_asymptoticNhds] at h
  exact h

@[simp]

中文:
定理 isClosed_asymptoticCone
  条件: {s : 集合 P}
  结论: 是闭集 (asymptoticCone k s)
  证明: by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [isClosed_iff_frequently]
  intro v h
  simp_rw [mem_asymptoticCone_iff, ← frequently_bind, nhds_bind_asymptoticNhds] at h
  exact h

@[simp]

Depends on / 依赖: FirstCountableTopology, Nonempty, firstCountableTopology, frequently_bind, isClosed_iff_frequently, mem_asymptoticCone_iff, nhds_bind_asymptoticNhds, simp_rw
-/
theorem isClosed_asymptoticCone {s : Set P} : IsClosed (asymptoticCone k s) := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [isClosed_iff_frequently]
  intro v h
  simp_rw [mem_asymptoticCone_iff, ← frequently_bind, nhds_bind_asymptoticNhds] at h
  exact h

@[simp]
/--
theorem `asymptoticCone_asymptoticCone` / 定理 `asymptoticCone_asymptoticCone`

English:
theorem asymptoticCone_asymptoticCone
  given: (s : Set P)
  proof: by
  ext
  simp_rw [mem_asymptoticCone_iff, ← Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds]

中文:
定理 asymptoticCone_asymptoticCone
  条件: (s : 集合 P)
  证明: by
  ext
  simp_rw [mem_asymptoticCone_iff, ← Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds]

Depends on / 依赖: Filter, Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds, frequently_bind, mem_asymptoticCone_iff, simp_rw
-/
theorem asymptoticCone_asymptoticCone (s : Set P) :
    asymptoticCone k (asymptoticCone k s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, ← Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds]

end General

section Convex

open AffineSpace

variable
  {k V : Type*}
  [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V]
  {s : Set V}

/--
theorem `StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone` / 定理 `StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`

English:
theorem StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
  statement: {c : k} {v p : V}
  proof: by
refine isClosed_iff_frequently.mp hs₂ _
.frequently ?_ .vadd_const _ .const_smul _ tendsto_snd (f := atTop (α := k))
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  apply hv.mp
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop c)]
    with ⟨t, u⟩ (ht : c <= t) (h : t • u +ᵥ p in s)
  change c • u +ᵥ p in s
  apply hs₁.segment_subset h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub, vadd_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).nonneg_smul_right (sub_nonneg.mpr ht)

中文:
定理 StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
  结论: {c : k} {v p : V}
  证明: by
refine isClosed_iff_frequently.mp hs₂ _
.frequently ?_ .vadd_const _ .const_smul _ tendsto_snd (f := atTop (α := k))
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  apply hv.mp
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop c)]
    with ⟨t, u⟩ (ht : c <= t) (h : t • u +ᵥ p in s)
  change c • u +ᵥ p in s
  apply hs₁.segment_subset h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub, vadd_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).nonneg_smul_right (sub_nonneg.mpr ht)

Depends on / 依赖: asymptoticNhds_eq_smul_vadd, const_smul, eventually, eventually_ge_atTop, filter_upwards, frequently, frequently_map, hv.mp, isClosed_iff_frequently, isClosed_iff_frequently.mp, mem_asymptoticCone_iff, mem_segment_iff_sameRay, segment_subset, simp_rw, tendsto_fst, tendsto_fst.eventually, tendsto_snd, vadd_const, vadd_pure
-/
theorem StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : StarConvex k p s) (hs₂ : IsClosed s) (hc : 0 <= c) (hv : v in asymptoticCone k s) :
    c • v +ᵥ p in s := by
refine isClosed_iff_frequently.mp hs₂ _
.frequently ?_ .vadd_const _ .const_smul _ tendsto_snd (f := atTop (α := k))
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v p]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  apply hv.mp
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop c)]
    with ⟨t, u⟩ (ht : c <= t) (h : t • u +ᵥ p in s)
  change c • u +ᵥ p in s
  apply hs₁.segment_subset h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub, vadd_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).nonneg_smul_right (sub_nonneg.mpr ht)

/--
theorem `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone` / 定理 `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`

English:
theorem Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
  statement: {c : k} {v p : V}
  proof: (hs₁ hp).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs₂ hc hv

中文:
定理 凸.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
  结论: {c : k} {v p : V}
  证明: (hs₁ hp).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs₂ hc hv

Depends on / 依赖: smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
-/
theorem Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : Convex k s) (hs₂ : IsClosed s) (hc : 0 <= c) (hv : v in asymptoticCone k s) (hp : p in s) :
    c • v +ᵥ p in s :=
  (hs₁ hp).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs₂ hc hv

/--
theorem `Convex.asymptoticCone` / 定理 `Convex.asymptoticCone`

English:
theorem Convex.asymptoticCone
  given: (hs : Convex k s)
  statement: Convex k (asymptoticCone k s)
  proof: by
  wlog hs' : IsClosed s generalizing s
  · rw [← asymptoticCone_closure]; exact this hs.closure isClosed_closure
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [asymptoticCone_empty]; exact convex_empty
  intro v hv u hu a b ha hb hab
  rw [mem_asymptoticCone_iff]
.asymptoticNhds_vadd_const p refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds _
.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 0] with c hc
  simp_rw [id, smul_add, smul_smul]
  have h₁ : c • v +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hv hp
  have h₂ : c • u +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hu hp
  apply hs.segment_subset h₁ h₂
  rw [← affineSegment_eq_segment]; rw [mem_vadd_const_affineSegment]; rw [affineSegment_eq_segment]
  exists a, b, ha, hb, hab
  module

中文:
定理 凸.asymptoticCone
  条件: (hs : 凸 k s)
  结论: 凸 k (asymptoticCone k s)
  证明: by
  wlog hs' : IsClosed s generalizing s
  · rw [← asymptoticCone_closure]; exact this hs.closure isClosed_closure
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [asymptoticCone_empty]; exact convex_empty
  intro v hv u hu a b ha hb hab
  rw [mem_asymptoticCone_iff]
.asymptoticNhds_vadd_const p refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds _
.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 0] with c hc
  simp_rw [id, smul_add, smul_smul]
  have h₁ : c • v +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hv hp
  have h₂ : c • u +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hu hp
  apply hs.segment_subset h₁ h₂
  rw [← affineSegment_eq_segment]; rw [mem_vadd_const_affineSegment]; rw [affineSegment_eq_segment]
  exists a, b, ha, hb, hab
  module
-/
protected theorem Convex.asymptoticCone (hs : Convex k s) : Convex k (asymptoticCone k s) := by
  wlog hs' : IsClosed s generalizing s
  · rw [← asymptoticCone_closure]; exact this hs.closure isClosed_closure
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [asymptoticCone_empty]; exact convex_empty
  intro v hv u hu a b ha hb hab
  rw [mem_asymptoticCone_iff]
.asymptoticNhds_vadd_const p refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds _
.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 0] with c hc
  simp_rw [id, smul_add, smul_smul]
  have h₁ : c • v +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hv hp
  have h₂ : c • u +ᵥ p in s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hu hp
  apply hs.segment_subset h₁ h₂
  rw [← affineSegment_eq_segment]; rw [mem_vadd_const_affineSegment]; rw [affineSegment_eq_segment]
  exists a, b, ha, hb, hab
  module

/--
theorem `Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone` / 定理 `Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone`

English:
theorem Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone
  statement: {c : k} {v p : V}
  proof: by
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v (c • v +ᵥ p)]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  refine frequently_const.mp (hv.mp ?_)
  have : Tendsto (fun u => -(c • u : V) +ᵥ c • v +ᵥ p) (𝓝 v) (𝓝 p) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [tendsto_fst.eventually <| eventually_gt_atTop 0, this.comp tendsto_snd hp]
    with ⟨t, u⟩ (ht : 0 < t) (hu : -(c • u) +ᵥ c • v +ᵥ p in s) (h : t • u +ᵥ c • v +ᵥ p in s)
  apply hs.segment_subset hu h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub]
  rw [vsub_vadd_eq_vsub_sub]; rw [vsub_self]; rw [zero_sub]; rw [neg_neg]; rw [vadd_vsub]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).pos_smul_right ht

中文:
定理 凸.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone
  结论: {c : k} {v p : V}
  证明: by
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v (c • v +ᵥ p)]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  refine frequently_const.mp (hv.mp ?_)
  have : Tendsto (fun u => -(c • u : V) +ᵥ c • v +ᵥ p) (𝓝 v) (𝓝 p) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [tendsto_fst.eventually <| eventually_gt_atTop 0, this.comp tendsto_snd hp]
    with ⟨t, u⟩ (ht : 0 < t) (hu : -(c • u) +ᵥ c • v +ᵥ p in s) (h : t • u +ᵥ c • v +ᵥ p in s)
  apply hs.segment_subset hu h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub]
  rw [vsub_vadd_eq_vsub_sub]; rw [vsub_self]; rw [zero_sub]; rw [neg_neg]; rw [vadd_vsub]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).pos_smul_right ht

Depends on / 依赖: Continuous, Continuous.tendsto, Tendsto, asymptoticNhds_eq_smul_vadd, eventually, eventually_gt_atTop, filter_upwards, frequently_const, frequently_const.mp, frequently_map, fun_prop, hv.mp, mem_asymptoticCone_iff, tendsto, tendsto_fst, tendsto_fst.eventually, tendsto_snd, this.comp, vadd_pure
-/
theorem Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone {c : k} {v p : V}
    (hs : Convex k s) (hc : 0 <= c) (hp : s in 𝓝 p) (hv : v in asymptoticCone k s) :
    c • v +ᵥ p in s := by
  rw [mem_asymptoticCone_iff]; rw [asymptoticNhds_eq_smul_vadd v (c • v +ᵥ p)]; rw [vadd_pure]; rw [frequently_map]; rw [← map₂_smul]; rw [← map_prod_eq_map₂]; rw [frequently_map] at hv
  refine frequently_const.mp (hv.mp ?_)
  have : Tendsto (fun u => -(c • u : V) +ᵥ c • v +ᵥ p) (𝓝 v) (𝓝 p) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [tendsto_fst.eventually <| eventually_gt_atTop 0, this.comp tendsto_snd hp]
    with ⟨t, u⟩ (ht : 0 < t) (hu : -(c • u) +ᵥ c • v +ᵥ p in s) (h : t • u +ᵥ c • v +ᵥ p in s)
  apply hs.segment_subset hu h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub]
  rw [vsub_vadd_eq_vsub_sub]; rw [vsub_self]; rw [zero_sub]; rw [neg_neg]; rw [vadd_vsub]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).pos_smul_right ht

end Convex
