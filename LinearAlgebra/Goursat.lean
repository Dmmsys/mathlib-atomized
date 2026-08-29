/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.Goursat
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Goursat's lemma for submodules

Let `M, N` be modules over a ring `R`. If `L` is a submodule of `M × N` which projects fully onto
both factors, then there exist submodules `M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the
image of `L` in `(M ⧸ M') × (N ⧸ N')` is the graph of an isomorphism `M ⧸ M' ≃ₗ[R] N ⧸ N'`.
Equivalently, `L` is equal to the preimage in `M × N` of the graph of this isomorphism
`M ⧸ M' ≃ₗ[R] N ⧸ N'`.

`M'` and `N'` can be explicitly constructed as `Submodule.goursatFst L` and `Submodule.goursatSnd L`
respectively.
-/

@[expose] public section

open Function Set LinearMap

namespace Submodule
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {L : Submodule R (M × N)}
  (hL₁ : Surjective (Prod.fst ∘ L.subtype)) (hL₂ : Surjective (Prod.snd ∘ L.subtype))

variable (L) in
/--
Definition of `goursatFst` / `goursatFst` 的定义

English:
definition goursatFst
  signature: : Submodule R M
  body: (LinearMap.ker <| (LinearMap.snd R M N).comp L.subtype).map ((LinearMap.fst R M N).comp L.subtype)

中文:
定义 goursatFst
  签名: : 子模 R M
  定义体: (LinearMap.ker <| (LinearMap.snd R M N).comp L.subtype).map ((LinearMap.fst R M N).comp L.subtype)

Depends on / 依赖: L.subtype, LinearMap, LinearMap.fst, LinearMap.ker, LinearMap.snd, subtype
-/
def goursatFst : Submodule R M :=
  (LinearMap.ker <| (LinearMap.snd R M N).comp L.subtype).map ((LinearMap.fst R M N).comp L.subtype)


variable (L) in
/--
Definition of `goursatSnd` / `goursatSnd` 的定义

English:
definition goursatSnd
  signature: : Submodule R N
  body: (LinearMap.ker <| (LinearMap.fst R M N).comp L.subtype).map ((LinearMap.snd R M N).comp L.subtype)

中文:
定义 goursatSnd
  签名: : 子模 R N
  定义体: (LinearMap.ker <| (LinearMap.fst R M N).comp L.subtype).map ((LinearMap.snd R M N).comp L.subtype)

Depends on / 依赖: L.subtype, LinearMap, LinearMap.fst, LinearMap.ker, LinearMap.snd, subtype
-/
def goursatSnd : Submodule R N :=
  (LinearMap.ker <| (LinearMap.fst R M N).comp L.subtype).map ((LinearMap.snd R M N).comp L.subtype)

/--
lemma `goursatFst_toAddSubgroup` / 引理 `goursatFst_toAddSubgroup`

English:
lemma goursatFst_toAddSubgroup
  proof: by
  ext x
  simp [goursatFst, AddSubgroup.mem_goursatFst]

中文:
引理 goursatFst_toAddSubgroup
  证明: by
  ext x
  simp [goursatFst, AddSubgroup.mem_goursatFst]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_goursatFst, goursatFst, mem_goursatFst
-/
lemma goursatFst_toAddSubgroup :
    (goursatFst L).toAddSubgroup = L.toAddSubgroup.goursatFst := by
  ext x
  simp [goursatFst, AddSubgroup.mem_goursatFst]

/--
lemma `goursatSnd_toAddSubgroup` / 引理 `goursatSnd_toAddSubgroup`

English:
lemma goursatSnd_toAddSubgroup
  proof: by
  ext x
  simp [goursatSnd, AddSubgroup.mem_goursatSnd]

中文:
引理 goursatSnd_toAddSubgroup
  证明: by
  ext x
  simp [goursatSnd, AddSubgroup.mem_goursatSnd]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_goursatSnd, goursatSnd, mem_goursatSnd
-/
lemma goursatSnd_toAddSubgroup :
    (goursatSnd L).toAddSubgroup = L.toAddSubgroup.goursatSnd := by
  ext x
  simp [goursatSnd, AddSubgroup.mem_goursatSnd]

variable (L) in
/--
lemma `goursatFst_prod_goursatSnd_le` / 引理 `goursatFst_prod_goursatSnd_le`

English:
lemma goursatFst_prod_goursatSnd_le
  statement: L.goursatFst.prod L.goursatSnd <= L
  proof: by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using! L.toAddSubgroup.goursatFst_prod_goursatSnd_le

中文:
引理 goursatFst_prod_goursatSnd_le
  结论: L.goursatFst.乘积 L.goursatSnd <= L
  证明: by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using! L.toAddSubgroup.goursatFst_prod_goursatSnd_le

Depends on / 依赖: L.toAddSubgroup.goursatFst_prod_goursatSnd_le, goursatFst_prod_goursatSnd_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup, toAddSubgroup, toAddSubgroup_le
-/
lemma goursatFst_prod_goursatSnd_le : L.goursatFst.prod L.goursatSnd <= L := by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using! L.toAddSubgroup.goursatFst_prod_goursatSnd_le

set_option backward.isDefEq.respectTransparency false in
include hL₁ hL₂ in
/--
lemma `goursat_surjective` / 引理 `goursat_surjective`

English:
lemma goursat_surjective
  statement: exists e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
  proof: by
  -- apply add-group result
  obtain ⟨(e : M ⧸ L.goursatFst ≃+ N ⧸ L.goursatSnd), he⟩ :=
    L.toAddSubgroup.goursat_surjective hL₁ hL₂
  -- check R-linearity of the map
  have (r : R) (x : M ⧸ L.goursatFst) : e (r • x) = r • e x := by
    change (r • x, r • e x) in e.toAddMonoidHom.graph
    rw [← he]; rw [← Prod.smul_mk]
    have : (x, e x) in e.toAddMonoidHom.graph := rfl
    rw [← he]; rw [AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨l, hl⟩, hl'⟩
    use ⟨r • l, L.smul_mem r hl⟩
    rw [← hl']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert! he using 1
  ext v
  rw [mem_toAddSubgroup]; rw [mem_graph_iff]; rw [Eq.comm]
  rfl

中文:
引理 goursat_surjective
  结论: 存在 e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
  证明: by
  -- apply add-group result
  obtain ⟨(e : M ⧸ L.goursatFst ≃+ N ⧸ L.goursatSnd), he⟩ :=
    L.toAddSubgroup.goursat_surjective hL₁ hL₂
  -- check R-linearity of the map
  have (r : R) (x : M ⧸ L.goursatFst) : e (r • x) = r • e x := by
    change (r • x, r • e x) in e.toAddMonoidHom.graph
    rw [← he]; rw [← Prod.smul_mk]
    have : (x, e x) in e.toAddMonoidHom.graph := rfl
    rw [← he]; rw [AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨l, hl⟩, hl'⟩
    use ⟨r • l, L.smul_mem r hl⟩
    rw [← hl']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert! he using 1
  ext v
  rw [mem_toAddSubgroup]; rw [mem_graph_iff]; rw [Eq.comm]
  rfl
-/
lemma goursat_surjective : exists e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
    LinearMap.range ((L.goursatFst.mkQ.prodMap L.goursatSnd.mkQ).comp L.subtype) = e.graph := by
  -- apply add-group result
  obtain ⟨(e : M ⧸ L.goursatFst ≃+ N ⧸ L.goursatSnd), he⟩ :=
    L.toAddSubgroup.goursat_surjective hL₁ hL₂
  -- check R-linearity of the map
  have (r : R) (x : M ⧸ L.goursatFst) : e (r • x) = r • e x := by
    change (r • x, r • e x) in e.toAddMonoidHom.graph
    rw [← he]; rw [← Prod.smul_mk]
    have : (x, e x) in e.toAddMonoidHom.graph := rfl
    rw [← he]; rw [AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨l, hl⟩, hl'⟩
    use ⟨r • l, L.smul_mem r hl⟩
    rw [← hl']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert! he using 1
  ext v
  rw [mem_toAddSubgroup]; rw [mem_graph_iff]; rw [Eq.comm]
  rfl

/--
lemma `goursat` / 引理 `goursat`

English:
lemma goursat
  statement: exists (M' : Submodule R M) (N' : Submodule R N) (M'' : Submodule R M')
  proof: by
  let M' := L.map (LinearMap.fst ..)
  let N' := L.map (LinearMap.snd ..)
  let P : L ->ₗ[R] M' := (LinearMap.fst ..).submoduleMap L
  let Q : L ->ₗ[R] N' := (LinearMap.snd ..).submoduleMap L
  let L' : Submodule R (M' × N') := LinearMap.range (P.prod Q)
  have hL₁' : Surjective (Prod.fst ∘ L'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective L
  have hL₂' : Surjective (Prod.snd ∘ L'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective L
  obtain ⟨e, he⟩ := goursat_surjective hL₁' hL₂'
  use M', N', L'.goursatFst, L'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, L', M', N', P, Q]
  rw [comap_map_eq_self]
  · ext ⟨m, n⟩
    constructor
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      Subtype.ext_iff, submoduleMap_coe_apply, fst_apply, snd_apply]
      grind
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      snd_apply, fst_apply, Subtype.ext_iff, submoduleMap_coe_apply]
      grind
  · convert! goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    simp only [ker_prodMap, ker_mkQ, Submodule.ext_iff]
    grind

中文:
引理 goursat
  结论: 存在 (M' : 子模 R M) (N' : 子模 R N) (M'' : 子模 R M')
  证明: by
  let M' := L.map (LinearMap.fst ..)
  let N' := L.map (LinearMap.snd ..)
  let P : L ->ₗ[R] M' := (LinearMap.fst ..).submoduleMap L
  let Q : L ->ₗ[R] N' := (LinearMap.snd ..).submoduleMap L
  let L' : Submodule R (M' × N') := LinearMap.range (P.prod Q)
  have hL₁' : Surjective (Prod.fst ∘ L'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective L
  have hL₂' : Surjective (Prod.snd ∘ L'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective L
  obtain ⟨e, he⟩ := goursat_surjective hL₁' hL₂'
  use M', N', L'.goursatFst, L'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, L', M', N', P, Q]
  rw [comap_map_eq_self]
  · ext ⟨m, n⟩
    constructor
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      Subtype.ext_iff, submoduleMap_coe_apply, fst_apply, snd_apply]
      grind
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      snd_apply, fst_apply, Subtype.ext_iff, submoduleMap_coe_apply]
      grind
  · convert! goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    simp only [ker_prodMap, ker_mkQ, Submodule.ext_iff]
    grind

Depends on / 依赖: L.map, LinearMap, LinearMap.fst, LinearMap.range, LinearMap.range_comp, LinearMap.snd, P.prod, Prod.fst, Submodule, Surjective, coe_comp, coe_fst, fst_prod, range_comp, range_eq_top, range_subtype, submoduleMap, submoduleMap_s, subtype
-/
lemma goursat : exists (M' : Submodule R M) (N' : Submodule R N) (M'' : Submodule R M')
    (N'' : Submodule R N') (e : (M' ⧸ M'') ≃ₗ[R] N' ⧸ N''),
    L = (e.graph.comap <| M''.mkQ.prodMap N''.mkQ).map (M'.subtype.prodMap N'.subtype) := by
  let M' := L.map (LinearMap.fst ..)
  let N' := L.map (LinearMap.snd ..)
  let P : L ->ₗ[R] M' := (LinearMap.fst ..).submoduleMap L
  let Q : L ->ₗ[R] N' := (LinearMap.snd ..).submoduleMap L
  let L' : Submodule R (M' × N') := LinearMap.range (P.prod Q)
  have hL₁' : Surjective (Prod.fst ∘ L'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective L
  have hL₂' : Surjective (Prod.snd ∘ L'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective L
  obtain ⟨e, he⟩ := goursat_surjective hL₁' hL₂'
  use M', N', L'.goursatFst, L'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, L', M', N', P, Q]
  rw [comap_map_eq_self]
  · ext ⟨m, n⟩
    constructor
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      Subtype.ext_iff, submoduleMap_coe_apply, fst_apply, snd_apply]
      grind
    · simp only [mem_map, LinearMap.mem_range, LinearMap.prod_apply, Function.prod_apply,
      Subtype.exists, Prod.exists, LinearMap.prodMap_apply, subtype_apply, Prod.mk.injEq,
      snd_apply, fst_apply, Subtype.ext_iff, submoduleMap_coe_apply]
      grind
  · convert! goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    simp only [ker_prodMap, ker_mkQ, Submodule.ext_iff]
    grind

end Submodule
