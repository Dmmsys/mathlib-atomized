/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Graph
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Goursat's lemma for subgroups

This file proves Goursat's lemma for subgroups.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `G' ≤ G` and `H' ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ G' × H ⧸ H'` is
the graph of an isomorphism `G ⧸ G' ≃ H ⧸ H'`.

`G'` and `H'` can be explicitly constructed as `Subgroup.goursatFst I` and `Subgroup.goursatSnd I`
respectively.
-/

@[expose] public section

open Function Set

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] {I : Subgroup (G × H)}
  (hI₁ : Surjective (Prod.fst ∘ I.subtype)) (hI₂ : Surjective (Prod.snd ∘ I.subtype))

variable (I) in
/-- For `I` a subgroup of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a subgroup of `G`.

This is the first subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
@[to_additive
/-- For `I` a subgroup of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a subgroup of `G`.

This is the first subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`. -/]
/--
Definition of `goursatFst` / `goursatFst` 的定义

English:
definition goursatFst
  signature: : Subgroup G
  body: ((MonoidHom.snd G H).comp I.subtype).ker.map ((MonoidHom.fst G H).comp I.subtype)

中文:
定义 goursatFst
  签名: : 子群 G
  定义体: ((MonoidHom.snd G H).comp I.subtype).ker.map ((MonoidHom.fst G H).comp I.subtype)

Depends on / 依赖: I.subtype, MonoidHom, MonoidHom.fst, MonoidHom.snd, ker.map, subtype
-/
def goursatFst : Subgroup G :=
  ((MonoidHom.snd G H).comp I.subtype).ker.map ((MonoidHom.fst G H).comp I.subtype)

variable (I) in
/-- For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
@[to_additive
/-- For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.

This is the second subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`. -/]
/--
Definition of `goursatSnd` / `goursatSnd` 的定义

English:
definition goursatSnd
  signature: : Subgroup H
  body: ((MonoidHom.fst G H).comp I.subtype).ker.map ((MonoidHom.snd G H).comp I.subtype)

@[to_additive (attr := simp)]

中文:
定义 goursatSnd
  签名: : 子群 H
  定义体: ((MonoidHom.fst G H).comp I.subtype).ker.map ((MonoidHom.snd G H).comp I.subtype)

@[to_additive (attr := simp)]

Depends on / 依赖: I.subtype, MonoidHom, MonoidHom.fst, MonoidHom.snd, ker.map, subtype
-/
def goursatSnd : Subgroup H :=
  ((MonoidHom.fst G H).comp I.subtype).ker.map ((MonoidHom.snd G H).comp I.subtype)

@[to_additive (attr := simp)]
/--
lemma `mem_goursatFst` / 引理 `mem_goursatFst`

English:
lemma mem_goursatFst
  given: {g : G}
  statement: g in I.goursatFst ↔ (g, 1) in I
  proof: by simp [goursatFst]

@[to_additive (attr := simp)]

中文:
引理 mem_goursatFst
  条件: {g : G}
  结论: g in I.goursatFst ↔ (g, 1) in I
  证明: by simp [goursatFst]

@[to_additive (attr := simp)]

Depends on / 依赖: goursatFst
-/
lemma mem_goursatFst {g : G} : g in I.goursatFst ↔ (g, 1) in I := by simp [goursatFst]

@[to_additive (attr := simp)]
/--
lemma `mem_goursatSnd` / 引理 `mem_goursatSnd`

English:
lemma mem_goursatSnd
  given: {h : H}
  statement: h in I.goursatSnd ↔ (1, h) in I
  proof: by simp [goursatSnd]

include hI₁ in

中文:
引理 mem_goursatSnd
  条件: {h : H}
  结论: h in I.goursatSnd ↔ (1, h) in I
  证明: by simp [goursatSnd]

include hI₁ in

Depends on / 依赖: goursatSnd
-/
lemma mem_goursatSnd {h : H} : h in I.goursatSnd ↔ (1, h) in I := by simp [goursatSnd]

include hI₁ in
/--
lemma `normal_goursatFst` / 引理 `normal_goursatFst`

English:
lemma normal_goursatFst
  statement: I.goursatFst.Normal
  proof: .map inferInstance _ hI₁

include hI₂ in

中文:
引理 normal_goursatFst
  结论: I.goursatFst.正规
  证明: .map inferInstance _ hI₁

include hI₂ in
-/
@[to_additive] lemma normal_goursatFst : I.goursatFst.Normal := .map inferInstance _ hI₁

include hI₂ in
/--
lemma `normal_goursatSnd` / 引理 `normal_goursatSnd`

English:
lemma normal_goursatSnd
  statement: I.goursatSnd.Normal
  proof: .map inferInstance _ hI₂

include hI₁ hI₂ in
@[to_additive]

中文:
引理 normal_goursatSnd
  结论: I.goursatSnd.正规
  证明: .map inferInstance _ hI₂

include hI₁ hI₂ in
@[to_additive]
-/
@[to_additive] lemma normal_goursatSnd : I.goursatSnd.Normal := .map inferInstance _ hI₂

include hI₁ hI₂ in
@[to_additive]
/--
lemma `mk_goursatFst_eq_iff_mk_goursatSnd_eq` / 引理 `mk_goursatFst_eq_iff_mk_goursatSnd_eq`

English:
lemma mk_goursatFst_eq_iff_mk_goursatSnd_eq
  given: {x y : G × H} (hx : x in I) (hy : y in I)
  proof: by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  rw [eq_comm]
  simp only [QuotientGroup.eq_iff_div_mem, mem_goursatFst, mem_goursatSnd]
  constructor <;> intro h
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hx) hy
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hy) hx

中文:
引理 mk_goursatFst_eq_iff_mk_goursatSnd_eq
  条件: {x y : G × H} (hx : x in I) (hy : y in I)
  证明: by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  rw [eq_comm]
  simp only [QuotientGroup.eq_iff_div_mem, mem_goursatFst, mem_goursatSnd]
  constructor <;> intro h
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hx) hy
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hy) hx

Depends on / 依赖: Prod.div_def, Prod.mul_def, QuotientGroup, QuotientGroup.eq_iff_div_mem, div_def, div_mem, eq_comm, eq_iff_div_mem, mem_goursatFst, mem_goursatSnd, mul_def, mul_mem, normal_goursatFst, normal_goursatSnd
-/
lemma mk_goursatFst_eq_iff_mk_goursatSnd_eq {x y : G × H} (hx : x in I) (hy : y in I) :
    (x.1 : G ⧸ I.goursatFst) = y.1 ↔ (x.2 : H ⧸ I.goursatSnd) = y.2 := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  rw [eq_comm]
  simp only [QuotientGroup.eq_iff_div_mem, mem_goursatFst, mem_goursatSnd]
  constructor <;> intro h
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hx) hy
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hy) hx

variable (I) in
@[to_additive AddSubgroup.goursatFst_prod_goursatSnd_le]
/--
lemma `goursatFst_prod_goursatSnd_le` / 引理 `goursatFst_prod_goursatSnd_le`

English:
lemma goursatFst_prod_goursatSnd_le
  statement: I.goursatFst.prod I.goursatSnd <= I
  proof: by
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  simpa using mul_mem (mem_goursatFst.1 hg) (mem_goursatSnd.1 hh)

中文:
引理 goursatFst_prod_goursatSnd_le
  结论: I.goursatFst.乘积 I.goursatSnd <= I
  证明: by
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  simpa using mul_mem (mem_goursatFst.1 hg) (mem_goursatSnd.1 hh)

Depends on / 依赖: mem_goursatFst, mem_goursatSnd, mul_mem
-/
lemma goursatFst_prod_goursatSnd_le : I.goursatFst.prod I.goursatSnd <= I := by
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  simpa using mul_mem (mem_goursatFst.1 hg) (mem_goursatSnd.1 hh)

/-- **Goursat's lemma** for a subgroup of a product with surjective projections.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `M ≤ G` and `N ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism `G ⧸ M ≃ H ⧸ N'`.

`G'` and `H'` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively. -/
@[to_additive
/-- **Goursat's lemma** for a subgroup of a product with surjective projections.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `M ≤ G` and `N ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism `G ⧸ M ≃ H ⧸ N'`.

`G'` and `H'` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively. -/]
/--
lemma `goursat_surjective` / 引理 `goursat_surjective`

English:
lemma goursat_surjective
  proof: normal_goursatFst hI₁
    have := normal_goursatSnd hI₂
    exists e : G ⧸ I.goursatFst ≃* H ⧸ I.goursatSnd,
      (((QuotientGroup.mk' _).prodMap (QuotientGroup.mk' _)).comp I.subtype).range =
        e.toMonoidHom.graph := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  exact (((QuotientGroup.mk' I.goursatFst).prodMap
    (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective _).comp hI₁) ((QuotientGroup.mk'_surjective _).comp hI₂)
    fun ⟨x, hx⟩ ⟨y, hy⟩ => mk_goursatFst_eq_iff_mk_goursatSnd_eq hI₁ hI₂ hx hy

中文:
引理 goursat_surjective
  证明: normal_goursatFst hI₁
    have := normal_goursatSnd hI₂
    exists e : G ⧸ I.goursatFst ≃* H ⧸ I.goursatSnd,
      (((QuotientGroup.mk' _).prodMap (QuotientGroup.mk' _)).comp I.subtype).range =
        e.toMonoidHom.graph := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  exact (((QuotientGroup.mk' I.goursatFst).prodMap
    (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective _).comp hI₁) ((QuotientGroup.mk'_surjective _).comp hI₂)
    fun ⟨x, hx⟩ ⟨y, hy⟩ => mk_goursatFst_eq_iff_mk_goursatSnd_eq hI₁ hI₂ hx hy

Depends on / 依赖: normal_goursatFst
-/
lemma goursat_surjective :
    have := normal_goursatFst hI₁
    have := normal_goursatSnd hI₂
    exists e : G ⧸ I.goursatFst ≃* H ⧸ I.goursatSnd,
      (((QuotientGroup.mk' _).prodMap (QuotientGroup.mk' _)).comp I.subtype).range =
        e.toMonoidHom.graph := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  exact (((QuotientGroup.mk' I.goursatFst).prodMap
    (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective _).comp hI₁) ((QuotientGroup.mk'_surjective _).comp hI₂)
    fun ⟨x, hx⟩ ⟨y, hy⟩ => mk_goursatFst_eq_iff_mk_goursatSnd_eq hI₁ hI₂ hx hy

/-- **Goursat's lemma** for an arbitrary subgroup.

If `I` is a subgroup of `G × H`, then there exist subgroups `G' ≤ G`, `H' ≤ H` and normal subgroups
`M ⊴ G'` and `N ⊴ H'` such that `M × N ≤ I` and the image of `I` in `G' ⧸ M × H' ⧸ N` is the graph
of an isomorphism `G' ⧸ M ≃ H' ⧸ N`. -/
@[to_additive
/-- **Goursat's lemma** for an arbitrary subgroup.

If `I` is a subgroup of `G × H`, then there exist subgroups `G' ≤ G`, `H' ≤ H` and normal subgroups
`M ≤ G'` and `N ≤ H'` such that `M × N ≤ I` and the image of `I` in `G' ⧸ M × H' ⧸ N` is the graph
of an isomorphism `G ⧸ G' ≃ H ⧸ H'`. -/]
/--
lemma `goursat` / 引理 `goursat`

English:
lemma goursat
  proof: by
  let G' := I.map (MonoidHom.fst ..)
  let H' := I.map (MonoidHom.snd ..)
  let P : I ->* G' := (MonoidHom.fst ..).subgroupMap I
  let Q : I ->* H' := (MonoidHom.snd ..).subgroupMap I
  let I' : Subgroup (G' × H') := (P.prod Q).range
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_fst, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.fst ..).subgroupMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_snd, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.range_eq_top]
    exact (MonoidHom.snd ..).subgroupMap_surjective I
  have := normal_goursatFst hI₁'
  have := normal_goursatSnd hI₂'
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  refine ⟨I.map (MonoidHom.fst ..), I.map (MonoidHom.snd ..),
    I'.goursatFst, I'.goursatSnd, inferInstance, inferInstance, e, ?_⟩
  rw [← he]
  simp only [MonoidHom.range_comp, Subgroup.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simpa only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst]
        using ⟨⟨h, hgh⟩, ⟨g, hgh⟩, g, h, hgh, ⟨rfl, rfl⟩⟩
    · simp only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst, forall_exists_index, and_imp]
      rintro h₁ hgh₁ g₁ hg₁h g₂ h₂ hg₂h₂ hP hQ
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert! goursatFst_prod_goursatSnd_le (P.prod Q).range
    ext ⟨g, h⟩
    simp_rw [G', H', MonoidHom.mem_ker, MonoidHom.coe_prodMap, Prod.map_apply, Subgroup.mem_prod,
      Prod.one_eq_mk, Prod.ext_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

中文:
引理 goursat
  证明: by
  let G' := I.map (MonoidHom.fst ..)
  let H' := I.map (MonoidHom.snd ..)
  let P : I ->* G' := (MonoidHom.fst ..).subgroupMap I
  let Q : I ->* H' := (MonoidHom.snd ..).subgroupMap I
  let I' : Subgroup (G' × H') := (P.prod Q).range
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_fst, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.fst ..).subgroupMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_snd, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.range_eq_top]
    exact (MonoidHom.snd ..).subgroupMap_surjective I
  have := normal_goursatFst hI₁'
  have := normal_goursatSnd hI₂'
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  refine ⟨I.map (MonoidHom.fst ..), I.map (MonoidHom.snd ..),
    I'.goursatFst, I'.goursatSnd, inferInstance, inferInstance, e, ?_⟩
  rw [← he]
  simp only [MonoidHom.range_comp, Subgroup.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simpa only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst]
        using ⟨⟨h, hgh⟩, ⟨g, hgh⟩, g, h, hgh, ⟨rfl, rfl⟩⟩
    · simp only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst, forall_exists_index, and_imp]
      rintro h₁ hgh₁ g₁ hg₁h g₂ h₂ hg₂h₂ hP hQ
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert! goursatFst_prod_goursatSnd_le (P.prod Q).range
    ext ⟨g, h⟩
    simp_rw [G', H', MonoidHom.mem_ker, MonoidHom.coe_prodMap, Prod.map_apply, Subgroup.mem_prod,
      Prod.one_eq_mk, Prod.ext_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

Depends on / 依赖: I.map, MonoidHom, MonoidHom.coe_comp, MonoidHom.coe_fst, MonoidHom.fst, MonoidHom.fst_comp_prod, MonoidHom.range_comp, MonoidHom.range_eq_top, MonoidHom.snd, P.prod, Prod.fst, Subgroup, Subgroup.range_subtype, Surjective, coe_comp, coe_fst, fst_comp_prod, range_comp, range_eq_top, range_subtype
-/
lemma goursat :
    exists (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N : Subgroup H') (_ : M.Normal)
      (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N),
      I = (e.toMonoidHom.graph.comap <| (QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N)).map
        (G'.subtype.prodMap H'.subtype) := by
  let G' := I.map (MonoidHom.fst ..)
  let H' := I.map (MonoidHom.snd ..)
  let P : I ->* G' := (MonoidHom.fst ..).subgroupMap I
  let Q : I ->* H' := (MonoidHom.snd ..).subgroupMap I
  let I' : Subgroup (G' × H') := (P.prod Q).range
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_fst, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.fst ..).subgroupMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_snd, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.range_eq_top]
    exact (MonoidHom.snd ..).subgroupMap_surjective I
  have := normal_goursatFst hI₁'
  have := normal_goursatSnd hI₂'
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  refine ⟨I.map (MonoidHom.fst ..), I.map (MonoidHom.snd ..),
    I'.goursatFst, I'.goursatSnd, inferInstance, inferInstance, e, ?_⟩
  rw [← he]
  simp only [MonoidHom.range_comp, Subgroup.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simpa only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst]
        using ⟨⟨h, hgh⟩, ⟨g, hgh⟩, g, h, hgh, ⟨rfl, rfl⟩⟩
    · simp only [G', H', mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists,
        Prod.exists, MonoidHom.coe_prodMap, coe_subtype, Prod.mk.injEq, Prod.map_apply,
        MonoidHom.coe_snd, exists_eq_right, exists_and_right, exists_eq_right_right,
        MonoidHom.coe_fst, forall_exists_index, and_imp]
      rintro h₁ hgh₁ g₁ hg₁h g₂ h₂ hg₂h₂ hP hQ
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert! goursatFst_prod_goursatSnd_le (P.prod Q).range
    ext ⟨g, h⟩
    simp_rw [G', H', MonoidHom.mem_ker, MonoidHom.coe_prodMap, Prod.map_apply, Subgroup.mem_prod,
      Prod.one_eq_mk, Prod.ext_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

end Subgroup
