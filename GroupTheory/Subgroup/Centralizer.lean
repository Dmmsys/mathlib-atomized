/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Submonoid.Centralizer

/-!
# Centralizers of subgroups
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G G' : Type*} [Group G] [Group G']

namespace Subgroup

variable {H K : Subgroup G}

/-- The `centralizer` of `s` is the subgroup of `g : G` commuting with every `h : s`. -/
@[to_additive
/-- The `centralizer` of `s` is the additive subgroup of `g : G` commuting with every `h : s`. -/]
/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set G)
  body: Submonoid.centralizer s
  inv_mem' := Set.inv_mem_centralizer

@[to_additive]

中文:
定义 centralizer
  签名: (s : 集合 G)
  定义体: Submonoid.centralizer s
  inv_mem' := Set.inv_mem_centralizer

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.centralizer, centralizer
-/
def centralizer (s : Set G) : Subgroup G where
  __ := Submonoid.centralizer s
  inv_mem' := Set.inv_mem_centralizer

@[to_additive]
/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {g : G} {s : Set G}
  statement: g in centralizer s ↔ forall h in s, h * g = g * h
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {g : G} {s : 集合 G}
  结论: g in centralizer s ↔ 对任意 h in s, h * g = g * h
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {g : G} {s : Set G} : g in centralizer s ↔ forall h in s, h * g = g * h :=
  Iff.rfl

open scoped commutatorElement in
@[to_additive]
/--
theorem `mem_centralizer_iff_commutator_eq_one` / 定理 `mem_centralizer_iff_commutator_eq_one`

English:
theorem mem_centralizer_iff_commutator_eq_one
  given: {g : G} {s : Set G}
  proof: by
  simp only [commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

中文:
定理 mem_centralizer_iff_commutator_eq_one
  条件: {g : G} {s : 集合 G}
  证明: by
  simp only [commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

Depends on / 依赖: commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul
-/
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g in centralizer s ↔ forall h in s, ⁅h, g⁆ = 1 := by
  simp only [commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

open scoped commutatorElement in
@[to_additive]
/--
theorem `mem_centralizer_iff_commutator_eq_one'` / 定理 `mem_centralizer_iff_commutator_eq_one'`

English:
theorem mem_centralizer_iff_commutator_eq_one'
  given: {g : G} {s : Set G}
  proof: by
  refine forall₂_congr fun _ _ => ?_
  rw [commutatorElement_def]; rw [mul_inv_eq_iff_eq_mul]; rw [mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [eq_comm]

@[to_additive]

中文:
定理 mem_centralizer_iff_commutator_eq_one'
  条件: {g : G} {s : 集合 G}
  证明: by
  refine forall₂_congr fun _ _ => ?_
  rw [commutatorElement_def]; rw [mul_inv_eq_iff_eq_mul]; rw [mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: commutatorElement_def, eq_comm, mul_inv_eq_iff_eq_mul, one_mul
-/
theorem mem_centralizer_iff_commutator_eq_one' {g : G} {s : Set G} :
    g in centralizer s ↔ forall h in s, ⁅g, h⁆ = 1 := by
  refine forall₂_congr fun _ _ => ?_
  rw [commutatorElement_def]; rw [mul_inv_eq_iff_eq_mul]; rw [mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [eq_comm]

@[to_additive]
/--
lemma `mem_centralizer_singleton_iff` / 引理 `mem_centralizer_singleton_iff`

English:
lemma mem_centralizer_singleton_iff
  given: {g k : G}
  proof: by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

@[to_additive]

中文:
引理 mem_centralizer_singleton_iff
  条件: {g k : G}
  证明: by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

@[to_additive]

Depends on / 依赖: Set.mem_singleton_iff, eq_comm, forall_eq, mem_centralizer_iff, mem_singleton_iff
-/
lemma mem_centralizer_singleton_iff {g k : G} :
    k in Subgroup.centralizer {g} ↔ k * g = g * k := by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

@[to_additive]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer Set.univ = center G
  proof: SetLike.ext' (Set.centralizer_univ G)

@[to_additive]

中文:
定理 centralizer_univ
  结论: centralizer 集合.univ = center G
  证明: SetLike.ext' (Set.centralizer_univ G)

@[to_additive]

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ : centralizer Set.univ = center G :=
  SetLike.ext' (Set.centralizer_univ G)

@[to_additive]
/--
theorem `le_centralizer_iff` / 定理 `le_centralizer_iff`

English:
theorem le_centralizer_iff
  statement: H <= centralizer K ↔ K <= centralizer H
  proof: ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]

中文:
定理 le_centralizer_iff
  结论: H <= centralizer K ↔ K <= centralizer H
  证明: ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]
-/
theorem le_centralizer_iff : H <= centralizer K ↔ K <= centralizer H :=
  ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]
/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: (s)
  statement: center G <= centralizer s
  proof: Set.center_subset_centralizer s

@[to_additive]

中文:
定理 center_le_centralizer
  条件: (s)
  结论: center G <= centralizer s
  证明: Set.center_subset_centralizer s

@[to_additive]

Depends on / 依赖: Set.center_subset_centralizer, center_subset_centralizer
-/
theorem center_le_centralizer (s) : center G <= centralizer s :=
  Set.center_subset_centralizer s

@[to_additive]
/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: {s t : Set G} (h : s subseteq t)
  statement: centralizer t <= centralizer s
  proof: Submonoid.centralizer_le h

@[to_additive (attr := simp)]

中文:
定理 centralizer_le
  条件: {s t : 集合 G} (h : s subseteq t)
  结论: centralizer t <= centralizer s
  证明: Submonoid.centralizer_le h

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.centralizer_le, centralizer_le
-/
theorem centralizer_le {s t : Set G} (h : s subseteq t) : centralizer t <= centralizer s :=
  Submonoid.centralizer_le h

@[to_additive (attr := simp)]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {s : Set G}
  statement: centralizer s = ⊤ ↔ s subseteq center G
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive (attr := simp)]

中文:
定理 centralizer_eq_top_iff_subset
  条件: {s : 集合 G}
  结论: centralizer s = ⊤ ↔ s subseteq center G
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive (attr := simp)]

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s subseteq center G :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive (attr := simp)]
/--
theorem `centralizer_center` / 定理 `centralizer_center`

English:
theorem centralizer_center
  statement: centralizer (center G : Set G) = ⊤
  proof: centralizer_eq_top_iff_subset.mpr le_rfl

@[to_additive]

中文:
定理 centralizer_center
  结论: centralizer (center G : 集合 G) = ⊤
  证明: centralizer_eq_top_iff_subset.mpr le_rfl

@[to_additive]

Depends on / 依赖: centralizer_eq_top_iff_subset, centralizer_eq_top_iff_subset.mpr, le_rfl
-/
theorem centralizer_center : centralizer (center G : Set G) = ⊤ :=
  centralizer_eq_top_iff_subset.mpr le_rfl

@[to_additive]
/--
theorem `map_centralizer_le_centralizer_image` / 定理 `map_centralizer_le_centralizer_image`

English:
theorem map_centralizer_le_centralizer_image
  given: (s : Set G) (f : G ->* G')
  proof: by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul]; rw [← map_mul]; rw [hg h hh]

@[to_additive]

中文:
定理 map_centralizer_le_centralizer_image
  条件: (s : 集合 G) (f : G ->* G')
  证明: by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul]; rw [← map_mul]; rw [hg h hh]

@[to_additive]

Depends on / 依赖: map_mul
-/
theorem map_centralizer_le_centralizer_image (s : Set G) (f : G ->* G') :
    (Subgroup.centralizer s).map f <= Subgroup.centralizer (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul]; rw [← map_mul]; rw [hg h hh]

@[to_additive]
/--
Instance `normal_centralizer` / 实例 `normal_centralizer`

English:
instance normal_centralizer
  signature: [H.Normal]
  body: by
    simpa [-mul_left_inj, -mul_right_inj, mul_assoc]
      using congr(i * $(hg _ <| ‹H.Normal›.conj_mem _ hh i⁻¹) * i⁻¹)

@[to_additive]

中文:
实例 normal_centralizer
  签名: [H.正规]
  定义体: by
    simpa [-mul_left_inj, -mul_right_inj, mul_assoc]
      using congr(i * $(hg _ <| ‹H.Normal›.conj_mem _ hh i⁻¹) * i⁻¹)

@[to_additive]

Depends on / 依赖: H.Normal, Normal, conj_mem, mul_assoc, mul_left_inj, mul_right_inj
-/
instance normal_centralizer [H.Normal] : (centralizer H : Subgroup G).Normal where
  conj_mem g hg i h hh := by
    simpa [-mul_left_inj, -mul_right_inj, mul_assoc]
      using congr(i * $(hg _ <| ‹H.Normal›.conj_mem _ hh i⁻¹) * i⁻¹)

@[to_additive]
/--
Instance `characteristic_centralizer` / 实例 `characteristic_centralizer`

English:
instance characteristic_centralizer
  signature: [hH : H.Characteristic]
  body: by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul]; rw [map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]

中文:
实例 characteristic_centralizer
  签名: [hH : H.特征]
  定义体: by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul]; rw [map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.characteristic_iff_comap_le.mpr, Subgroup.characteristic_iff_le_comap.mp, characteristic_iff_comap_le, characteristic_iff_le_comap, injective, map_mul
-/
instance characteristic_centralizer [hH : H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul]; rw [map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]
/--
theorem `le_centralizer_iff_isMulCommutative` / 定理 `le_centralizer_iff_isMulCommutative`

English:
theorem le_centralizer_iff_isMulCommutative
  statement: K <= centralizer K ↔ IsMulCommutative K
  proof: ⟨fun h => ⟨⟨fun x y => Subtype.ext h y.2 x x.2⟩⟩,
fun _ x hx y hy => congrArg Subtype.val mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

中文:
定理 le_centralizer_iff_isMulCommutative
  结论: K <= centralizer K ↔ 是MulCommutative K
  证明: ⟨fun h => ⟨⟨fun x y => Subtype.ext h y.2 x x.2⟩⟩,
fun _ x hx y hy => congrArg Subtype.val mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, mul_comm
-/
theorem le_centralizer_iff_isMulCommutative : K <= centralizer K ↔ IsMulCommutative K :=
⟨fun h => ⟨⟨fun x y => Subtype.ext h y.2 x x.2⟩⟩,
fun _ x hx y hy => congrArg Subtype.val mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

variable (H)

@[to_additive]
/--
theorem `le_centralizer` / 定理 `le_centralizer`

English:
theorem le_centralizer
  given: [h : IsMulCommutative H]
  statement: H <= centralizer H
  proof: le_centralizer_iff_isMulCommutative.mpr h

中文:
定理 le_centralizer
  条件: [h : 是MulCommutative H]
  结论: H <= centralizer H
  证明: le_centralizer_iff_isMulCommutative.mpr h

Depends on / 依赖: le_centralizer_iff_isMulCommutative, le_centralizer_iff_isMulCommutative.mpr
-/
theorem le_centralizer [h : IsMulCommutative H] : H <= centralizer H :=
  le_centralizer_iff_isMulCommutative.mpr h

variable {H} in
@[to_additive]
/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: (s : Set G)
  proof: .mpr Set.subset_centralizer_centralizer closure_le _

@[to_additive]

中文:
引理 closure_le_centralizer_centralizer
  条件: (s : 集合 G)
  证明: .mpr Set.subset_centralizer_centralizer closure_le _

@[to_additive]

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set G) :
    closure s <= centralizer (centralizer s) :=
.mpr Set.subset_centralizer_centralizer closure_le _

@[to_additive]
/--
theorem `centralizer_closure` / 定理 `centralizer_closure`

English:
theorem centralizer_closure
  given: (s : Set G)
  statement: centralizer (closure s) = centralizer s
  proof: le_antisymm (centralizer_le subset_closure)
    (le_centralizer_iff.mp (closure_le_centralizer_centralizer s))

@[to_additive]

中文:
定理 centralizer_closure
  条件: (s : 集合 G)
  结论: centralizer (closure s) = centralizer s
  证明: le_antisymm (centralizer_le subset_closure)
    (le_centralizer_iff.mp (closure_le_centralizer_centralizer s))

@[to_additive]

Depends on / 依赖: centralizer_le, closure_le_centralizer_centralizer, le_antisymm, le_centralizer_iff, le_centralizer_iff.mp, subset_closure
-/
theorem centralizer_closure (s : Set G) : centralizer (closure s) = centralizer s :=
  le_antisymm (centralizer_le subset_closure)
    (le_centralizer_iff.mp (closure_le_centralizer_centralizer s))

@[to_additive]
/--
theorem `centralizer_eq_iInf` / 定理 `centralizer_eq_iInf`

English:
theorem centralizer_eq_iInf
  given: (s : Set G)
  statement: centralizer s = ⨅ g in s, centralizer {g}
  proof: le_antisymm (le_iInf₂ fun g hg => centralizer_le (Set.singleton_subset_iff.mpr hg)) fun x hx => by
    simpa only [mem_iInf, mem_centralizer_singleton_iff, eq_comm (a := x * _)] using! hx

@[to_additive]

中文:
定理 centralizer_eq_iInf
  条件: (s : 集合 G)
  结论: centralizer s = ⨅ g in s, centralizer {g}
  证明: le_antisymm (le_iInf₂ fun g hg => centralizer_le (Set.singleton_subset_iff.mpr hg)) fun x hx => by
    simpa only [mem_iInf, mem_centralizer_singleton_iff, eq_comm (a := x * _)] using! hx

@[to_additive]

Depends on / 依赖: Set.singleton_subset_iff.mpr, centralizer_le, eq_comm, le_antisymm, mem_centralizer_singleton_iff, mem_iInf, singleton_subset_iff
-/
theorem centralizer_eq_iInf (s : Set G) : centralizer s = ⨅ g in s, centralizer {g} :=
  le_antisymm (le_iInf₂ fun g hg => centralizer_le (Set.singleton_subset_iff.mpr hg)) fun x hx => by
    simpa only [mem_iInf, mem_centralizer_singleton_iff, eq_comm (a := x * _)] using! hx

@[to_additive]
/--
theorem `center_eq_iInf` / 定理 `center_eq_iInf`

English:
theorem center_eq_iInf
  given: {s : Set G} (hs : closure s = ⊤)
  proof: by
  rw [← centralizer_univ]; rw [← coe_top]; rw [← hs]; rw [centralizer_closure]; rw [centralizer_eq_iInf]

@[to_additive]

中文:
定理 center_eq_iInf
  条件: {s : 集合 G} (hs : closure s = ⊤)
  证明: by
  rw [← centralizer_univ]; rw [← coe_top]; rw [← hs]; rw [centralizer_closure]; rw [centralizer_eq_iInf]

@[to_additive]

Depends on / 依赖: centralizer_closure, centralizer_eq_iInf, centralizer_univ, coe_top
-/
theorem center_eq_iInf {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g in s, centralizer {g} := by
  rw [← centralizer_univ]; rw [← coe_top]; rw [← hs]; rw [centralizer_closure]; rw [centralizer_eq_iInf]

@[to_additive]
/--
theorem `center_eq_infi'` / 定理 `center_eq_infi'`

English:
theorem center_eq_infi'
  given: {s : Set G} (hs : closure s = ⊤)
  proof: by
  rw [center_eq_iInf hs]; rw [← iInf_subtype'']

中文:
定理 center_eq_infi'
  条件: {s : 集合 G} (hs : closure s = ⊤)
  证明: by
  rw [center_eq_iInf hs]; rw [← iInf_subtype'']

Depends on / 依赖: center_eq_iInf, iInf_subtype
-/
theorem center_eq_infi' {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g : s, centralizer {(g : G)} := by
  rw [center_eq_iInf hs]; rw [← iInf_subtype'']

/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  given: {k : Set G} (hcomm : forall x in k, forall y in k, x * y = y * x)
  proof: have := closure_le_centralizer_centralizer k
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  条件: {k : 集合 G} (hcomm : 对任意 x in k, 对任意 y in k, x * y = y * x)
  证明: have := closure_le_centralizer_centralizer k
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {k : Set G} (hcomm : forall x in k, forall y in k, x * y = y * x) :
    IsMulCommutative (closure k) :=
  have := closure_le_centralizer_centralizer k
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-10"))
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
/--
Definition of `closureCommGroupOfComm` / `closureCommGroupOfComm` 的定义

English:
abbreviation closureCommGroupOfComm
  signature: {k : Set G} (hcomm : forall x in k, forall y in k, x * y = y * x)
  body: have := isMulCommutative_closure hcomm
  inferInstance

@[to_additive]

中文:
缩写 closureCommGroupOfComm
  签名: {k : 集合 G} (hcomm : 对任意 x in k, 对任意 y in k, x * y = y * x)
  定义体: have := isMulCommutative_closure hcomm
  inferInstance

@[to_additive]

Depends on / 依赖: isMulCommutative_closure
-/
abbrev closureCommGroupOfComm {k : Set G} (hcomm : forall x in k, forall y in k, x * y = y * x) :
    CommGroup (closure k) :=
  have := isMulCommutative_closure hcomm
  inferInstance

@[to_additive]
/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S : Type*} [SetLike S G] [MulMemClass S G] (s : S)
  body: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

@[to_additive]

中文:
实例 instIsMulCommutative_closure
  签名: {S : 类型} [集合状 S G] [MulMem类 S G] (s : S)
  定义体: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

@[to_additive]

Depends on / 依赖: isMulCommutative_closure, setLike_mul_comm
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S G] [MulMemClass S G] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set G)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

@[to_additive]
/--
theorem `centralizer_le_normalizer` / 定理 `centralizer_le_normalizer`

English:
theorem centralizer_le_normalizer
  given: (s : Set G)
  statement: centralizer s <= normalizer s
  proof: by
  refine fun g hg h => ⟨fun hh => ?_, fun hh => ?_⟩
  · simpa [← hg h hh]
  · convert! hh
    simpa using hg _ hh

@[to_additive]

中文:
定理 centralizer_le_normalizer
  条件: (s : 集合 G)
  结论: centralizer s <= normalizer s
  证明: by
  refine fun g hg h => ⟨fun hh => ?_, fun hh => ?_⟩
  · simpa [← hg h hh]
  · convert! hh
    simpa using hg _ hh

@[to_additive]

Depends on / 依赖: convert
-/
theorem centralizer_le_normalizer (s : Set G) : centralizer s <= normalizer s := by
  refine fun g hg h => ⟨fun hh => ?_, fun hh => ?_⟩
  · simpa [← hg h hh]
  · convert! hh
    simpa using hg _ hh

@[to_additive]
/--
Instance `normal_subgroupOf_centralizer_normalizer` / 实例 `normal_subgroupOf_centralizer_normalizer`

English:
instance normal_subgroupOf_centralizer_normalizer
  signature: (s : Set G)
  body: by
  refine (Subgroup.normal_subgroupOf_iff <| centralizer_le_normalizer s).mpr fun c n hc hn => ?_
  refine mem_centralizer_iff_commutator_eq_one'.mpr fun g hg => ?_
  suffices n * (c * (n⁻¹ * g * n) * c⁻¹ * n⁻¹ * g⁻¹) = 1 by simpa [commutatorElement_def, mul_assoc]
  simp [← hc _ <| mem_set_normalizer_iff''.mp hn g |>.mp hg]

@[to_additive]

中文:
实例 normal_subgroupOf_centralizer_normalizer
  签名: (s : 集合 G)
  定义体: by
  refine (Subgroup.normal_subgroupOf_iff <| centralizer_le_normalizer s).mpr fun c n hc hn => ?_
  refine mem_centralizer_iff_commutator_eq_one'.mpr fun g hg => ?_
  suffices n * (c * (n⁻¹ * g * n) * c⁻¹ * n⁻¹ * g⁻¹) = 1 by simpa [commutatorElement_def, mul_assoc]
  simp [← hc _ <| mem_set_normalizer_iff''.mp hn g |>.mp hg]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.normal_subgroupOf_iff, centralizer_le_normalizer, commutatorElement_def, mem_centralizer_iff_commutator_eq_one, mem_set_normalizer_iff, mul_assoc, normal_subgroupOf_iff
-/
instance normal_subgroupOf_centralizer_normalizer (s : Set G) :
    (centralizer s |>.subgroupOf <| normalizer s).Normal := by
  refine (Subgroup.normal_subgroupOf_iff <| centralizer_le_normalizer s).mpr fun c n hc hn => ?_
  refine mem_centralizer_iff_commutator_eq_one'.mpr fun g hg => ?_
  suffices n * (c * (n⁻¹ * g * n) * c⁻¹ * n⁻¹ * g⁻¹) = 1 by simpa [commutatorElement_def, mul_assoc]
  simp [← hc _ <| mem_set_normalizer_iff''.mp hn g |>.mp hg]

@[to_additive]
/--
theorem `normalizer_singleton` / 定理 `normalizer_singleton`

English:
theorem normalizer_singleton
  given: (g : G)
  statement: normalizer {g} = centralizer {g}
  proof: by
  refine ext fun h => ⟨?_, ?_⟩
  · rintro hh g rfl
    exact mul_eq_of_eq_mul_inv (hh g |>.mp rfl).symm
  · refine fun hh g => ⟨?_, ?_⟩ <;> rintro rfl
    · exact (eq_mul_inv_of_mul_eq <| hh g rfl).symm
    · simpa using hh _ rfl

中文:
定理 normalizer_singleton
  条件: (g : G)
  结论: normalizer {g} = centralizer {g}
  证明: by
  refine ext fun h => ⟨?_, ?_⟩
  · rintro hh g rfl
    exact mul_eq_of_eq_mul_inv (hh g |>.mp rfl).symm
  · refine fun hh g => ⟨?_, ?_⟩ <;> rintro rfl
    · exact (eq_mul_inv_of_mul_eq <| hh g rfl).symm
    · simpa using hh _ rfl

Depends on / 依赖: eq_mul_inv_of_mul_eq, mul_eq_of_eq_mul_inv
-/
theorem normalizer_singleton (g : G) : normalizer {g} = centralizer {g} := by
  refine ext fun h => ⟨?_, ?_⟩
  · rintro hh g rfl
    exact mul_eq_of_eq_mul_inv (hh g |>.mp rfl).symm
  · refine fun hh g => ⟨?_, ?_⟩ <;> rintro rfl
    · exact (eq_mul_inv_of_mul_eq <| hh g rfl).symm
    · simpa using hh _ rfl

/-- The conjugation action of `N(H)` on `H`. -/
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (normalizer H : Subgroup G) H
  body: ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]

中文:
实例 :
  签名: MulDistribMul作用 (normalizer H : 子群 G) H
  定义体: ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]
-/
instance : MulDistribMulAction (normalizer H : Subgroup G) H where
  smul g h := ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]

/-- The homomorphism `N(H) → Aut(H)` with kernel `C(H)`. -/
@[simps!]
/--
Definition of `normalizerMonoidHom` / `normalizerMonoidHom` 的定义

English:
definition normalizerMonoidHom
  signature: : normalizer (H : Set G) ->* MulAut H
  body: MulDistribMulAction.toMulAut (normalizer H : Subgroup G) H

中文:
定义 normalizerMonoidHom
  签名: : normalizer (H : 集合 G) ->* MulAut H
  定义体: MulDistribMulAction.toMulAut (normalizer H : Subgroup G) H

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMulAut, Subgroup, normalizer, toMulAut
-/
def normalizerMonoidHom : normalizer (H : Set G) ->* MulAut H :=
  MulDistribMulAction.toMulAut (normalizer H : Subgroup G) H

/--
theorem `normalizerMonoidHom_ker` / 定理 `normalizerMonoidHom_ker`

English:
theorem normalizerMonoidHom_ker
  proof: by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

中文:
定理 normalizerMonoidHom_ker
  证明: by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Subgroup, Subgroup.ext_iff, Subtype, Subtype.ext_iff, eq_comm, eq_mul_inv_iff_mul_eq, ext_iff, mem_centralizer_iff, mem_subgroupOf
-/
theorem normalizerMonoidHom_ker :
    H.normalizerMonoidHom.ker = (centralizer H).subgroupOf (normalizer H : Subgroup G) := by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

end Subgroup
