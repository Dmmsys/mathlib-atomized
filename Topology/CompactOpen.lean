/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `ContinuousMap.compactOpen` is the compact-open topology on `C(X, Y)`.
  It is declared as an instance.
* `ContinuousMap.coev` is the coevaluation map `Y → C(X, Y × X)`. It is always continuous.
* `ContinuousMap.curry` is the currying map `C(X × Y, Z) → C(X, C(Y, Z))`. This map always exists
  and it is continuous as long as `X × Y` is locally compact.
* `ContinuousMap.uncurry` is the uncurrying map `C(X, C(Y, Z)) → C(X × Y, Z)`. For this map to
  exist, we need `Y` to be locally compact. If `X` is also locally compact, then this map is
  continuous.
* `Homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`. This homeomorphism exists if `X` and `Y` are locally compact.


## Tags

compact-open, curry, function space
-/

@[expose] public section


open Set Filter TopologicalSpace Topology

namespace ContinuousMap

section CompactOpen

variable {α X Y Z T : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
variable {K : Set X} {U : Set Y}

/--
Instance `compactOpen` / 实例 `compactOpen`

English:
instance compactOpen
  signature: : TopologicalSpace C(X, Y)
  body: .generateFrom image2 (fun K U => {f | MapsTo f K U}) {K | IsCompact K} {U | IsOpen U}

中文:
实例 compactOpen
  签名: : 拓扑空间 C(X, Y)
  定义体: .generateFrom image2 (fun K U => {f | MapsTo f K U}) {K | IsCompact K} {U | IsOpen U}

Depends on / 依赖: IsCompact, IsOpen, MapsTo, generateFrom, image2
-/
instance compactOpen : TopologicalSpace C(X, Y) :=
.generateFrom image2 (fun K U => {f | MapsTo f K U}) {K | IsCompact K} {U | IsOpen U}

/--
theorem `compactOpen_eq` / 定理 `compactOpen_eq`

English:
theorem compactOpen_eq
  statement: @compactOpen X Y _ _ =
  proof: rfl

中文:
定理 compactOpen_eq
  结论: @compactOpen X Y _ _ =
  证明: rfl
-/
theorem compactOpen_eq : @compactOpen X Y _ _ =
    .generateFrom (image2 (fun K U => {f | MapsTo f K U}) {K | IsCompact K} {t | IsOpen t}) :=
  rfl

/--
theorem `isOpen_setOfPred_mapsTo` / 定理 `isOpen_setOfPred_mapsTo`

English:
theorem isOpen_setOfPred_mapsTo
  given: (hK : IsCompact K) (hU : IsOpen U)
  proof: isOpen_generateFrom_of_mem mem_image2_of_mem hK hU

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_mapsTo := isOpen_setOfPred_mapsTo

中文:
定理 isOpen_setOfPred_mapsTo
  条件: (hK : 是紧集 K) (hU : 是开集 U)
  证明: isOpen_generateFrom_of_mem mem_image2_of_mem hK hU

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_mapsTo := isOpen_setOfPred_mapsTo

Depends on / 依赖: isOpen_generateFrom_of_mem, mem_image2_of_mem
-/
theorem isOpen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | MapsTo f K U} :=
isOpen_generateFrom_of_mem mem_image2_of_mem hK hU

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_mapsTo := isOpen_setOfPred_mapsTo

/--
lemma `eventually_mapsTo` / 引理 `eventually_mapsTo`

English:
lemma eventually_mapsTo
  given: {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U)
  proof: (isOpen_setOfPred_mapsTo hK hU).mem_nhds h

中文:
引理 eventually_mapsTo
  条件: {f : C(X, Y)} (hK : 是紧集 K) (hU : 是开集 U) (h : 映射到 f K U)
  证明: (isOpen_setOfPred_mapsTo hK hU).mem_nhds h

Depends on / 依赖: isOpen_setOfPred_mapsTo, mem_nhds
-/
lemma eventually_mapsTo {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U) :
    forallᶠ g : C(X, Y) in 𝓝 f, MapsTo g K U :=
  (isOpen_setOfPred_mapsTo hK hU).mem_nhds h

/--
lemma `isOpen_setOfPred_range_subset` / 引理 `isOpen_setOfPred_range_subset`

English:
lemma isOpen_setOfPred_range_subset
  given: [CompactSpace X] (hU : IsOpen U)
  proof: by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact isOpen_setOfPred_mapsTo isCompact_univ hU

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_range_subset := isOpen_setOfPred_range_subset

中文:
引理 isOpen_setOfPred_range_subset
  条件: [紧空间 X] (hU : 是开集 U)
  证明: by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact isOpen_setOfPred_mapsTo isCompact_univ hU

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_range_subset := isOpen_setOfPred_range_subset

Depends on / 依赖: isCompact_univ, isOpen_setOfPred_mapsTo, mapsTo_univ_iff_range_subset, simp_rw
-/
lemma isOpen_setOfPred_range_subset [CompactSpace X] (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | range f subseteq U} := by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact isOpen_setOfPred_mapsTo isCompact_univ hU

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_range_subset := isOpen_setOfPred_range_subset

/--
lemma `eventually_range_subset` / 引理 `eventually_range_subset`

English:
lemma eventually_range_subset
  given: [CompactSpace X] {f : C(X, Y)} (hU : IsOpen U) (h : range f subseteq U)
  proof: (isOpen_setOfPred_range_subset hU).mem_nhds h

中文:
引理 eventually_range_subset
  条件: [紧空间 X] {f : C(X, Y)} (hU : 是开集 U) (h : range f subseteq U)
  证明: (isOpen_setOfPred_range_subset hU).mem_nhds h

Depends on / 依赖: isOpen_setOfPred_range_subset, mem_nhds
-/
lemma eventually_range_subset [CompactSpace X] {f : C(X, Y)} (hU : IsOpen U) (h : range f subseteq U) :
    forallᶠ g : C(X, Y) in 𝓝 f, range g subseteq U :=
  (isOpen_setOfPred_range_subset hU).mem_nhds h

/--
lemma `nhds_compactOpen` / 引理 `nhds_compactOpen`

English:
lemma nhds_compactOpen
  given: (f : C(X, Y))
  proof: by
  simp_rw +instances [compactOpen_eq, nhds_generateFrom, mem_ofPred_eq, @and_comm (f in _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_ofPred_eq]

中文:
引理 nhds_compactOpen
  条件: (f : C(X, Y))
  证明: by
  simp_rw +instances [compactOpen_eq, nhds_generateFrom, mem_ofPred_eq, @and_comm (f in _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_ofPred_eq]

Depends on / 依赖: and_comm, biInf_prod, compactOpen_eq, iInf_and, iInf_image, image_prod, instances, mem_ofPred_eq, nhds_generateFrom, simp_rw
-/
lemma nhds_compactOpen (f : C(X, Y)) :
    𝓝 f = ⨅ (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U),
      𝓟 {g : C(X, Y) | MapsTo g K U} := by
  simp_rw +instances [compactOpen_eq, nhds_generateFrom, mem_ofPred_eq, @and_comm (f in _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_ofPred_eq]

/--
lemma `tendsto_nhds_compactOpen` / 引理 `tendsto_nhds_compactOpen`

English:
lemma tendsto_nhds_compactOpen
  given: {l : Filter α} {f : α -> C(Y, Z)} {g : C(Y, Z)}
  proof: by
  simp [nhds_compactOpen]

中文:
引理 tendsto_nhds_compactOpen
  条件: {l : 滤子 α} {f : α -> C(Y, Z)} {g : C(Y, Z)}
  证明: by
  simp [nhds_compactOpen]

Depends on / 依赖: nhds_compactOpen
-/
lemma tendsto_nhds_compactOpen {l : Filter α} {f : α -> C(Y, Z)} {g : C(Y, Z)} :
    Tendsto f l (𝓝 g) ↔
      forall K, IsCompact K -> forall U, IsOpen U -> MapsTo g K U -> forallᶠ a in l, MapsTo (f a) K U := by
  simp [nhds_compactOpen]

/--
lemma `continuous_compactOpen` / 引理 `continuous_compactOpen`

English:
lemma continuous_compactOpen
  given: {f : X -> C(Y, Z)}
  proof: continuous_generateFrom_iff.trans forall_mem_image2

中文:
引理 continuous_compactOpen
  条件: {f : X -> C(Y, Z)}
  证明: continuous_generateFrom_iff.trans forall_mem_image2

Depends on / 依赖: continuous_generateFrom_iff, continuous_generateFrom_iff.trans, forall_mem_image2
-/
lemma continuous_compactOpen {f : X -> C(Y, Z)} :
    Continuous f ↔ forall K, IsCompact K -> forall U, IsOpen U -> IsOpen {x | MapsTo (f x) K U} :=
  continuous_generateFrom_iff.trans forall_mem_image2

/--
lemma `hasBasis_nhds` / 引理 `hasBasis_nhds`

English:
lemma hasBasis_nhds
  given: (f : C(X, Y))
  proof: by
  refine ⟨fun s => ?_⟩
  simp_rw [nhds_compactOpen, iInf_comm.{_, 0, _ + 1}, iInf_prod', iInf_and']
  simp [mem_biInf_principal, and_assoc]

中文:
引理 hasBasis_nhds
  条件: (f : C(X, Y))
  证明: by
  refine ⟨fun s => ?_⟩
  simp_rw [nhds_compactOpen, iInf_comm.{_, 0, _ + 1}, iInf_prod', iInf_and']
  simp [mem_biInf_principal, and_assoc]
-/
protected lemma hasBasis_nhds (f : C(X, Y)) :
    (𝓝 f).HasBasis
      (fun S : Set (Set X × Set Y) =>
        S.Finite ∧ forall K U, (K, U) in S -> IsCompact K ∧ IsOpen U ∧ MapsTo f K U)
      (⋂ KU in ·, {g : C(X, Y) | MapsTo g KU.1 KU.2}) := by
  refine ⟨fun s => ?_⟩
  simp_rw [nhds_compactOpen, iInf_comm.{_, 0, _ + 1}, iInf_prod', iInf_and']
  simp [mem_biInf_principal, and_assoc]

/--
lemma `mem_nhds_iff` / 引理 `mem_nhds_iff`

English:
lemma mem_nhds_iff
  given: {f : C(X, Y)} {s : Set C(X, Y)}
  proof: by
  simp [f.hasBasis_nhds.mem_iff, ← ofPred_forall, and_assoc]

中文:
引理 mem_nhds_iff
  条件: {f : C(X, Y)} {s : 集合 C(X, Y)}
  证明: by
  simp [f.hasBasis_nhds.mem_iff, ← ofPred_forall, and_assoc]
-/
protected lemma mem_nhds_iff {f : C(X, Y)} {s : Set C(X, Y)} :
    s in 𝓝 f ↔ exists S : Set (Set X × Set Y), S.Finite ∧
      (forall K U, (K, U) in S -> IsCompact K ∧ IsOpen U ∧ MapsTo f K U) ∧
      {g : C(X, Y) | forall K U, (K, U) in S -> MapsTo g K U} subseteq s := by
  simp [f.hasBasis_nhds.mem_iff, ← ofPred_forall, and_assoc]

/--
lemma `_root_.Filter.HasBasis.nhds_continuousMapConst` / 引理 `_root_.Filter.HasBasis.nhds_continuousMapConst`

English:
lemma _root_.Filter.HasBasis.nhds_continuousMapConst
  statement: {ι : Type*} {c : Y} {p : ι -> Prop}
  proof: by
  refine ⟨fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rcases ContinuousMap.mem_nhds_iff.mp hs with ⟨S, hSf, hS, hSsub⟩
    choose hScompact hSopen hSmaps using hS
    have : ⋂ KU in S, ⋂ (_ : KU.1.Nonempty), KU.2 in 𝓝 c := by
      simp only [biInter_mem hSf, Prod.forall, iInter_mem]
      rintro K U hKU ⟨x, hx⟩
exact (hSopen K U hKU).mem_nhds hSmaps K U hKU hx
    rcases h.mem_iff.mp this with ⟨i, hpi, hi⟩
refine ⟨(⋃ KU in S, KU.1, i), ⟨hSf.isCompact_biUnion Prod.forall.2 hScompact, hpi⟩,
      Subset.trans ?_ hSsub⟩
    intro f hf K V hKV
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact mapsTo_empty _ _
    · refine hf.out.mono (subset_biUnion_of_mem (u := Prod.fst) hKV) (hi.trans ?_)
exact (biInter_subset_of_mem hKV).trans iInter_subset _ hKne
  · rcases hs with ⟨⟨K, i⟩, ⟨hK, hpi⟩, hi⟩
    filter_upwards [eventually_mapsTo hK isOpen_interior fun x _ =>
mem_interior_iff_mem_nhds.mpr h.mem_of_mem hpi] with f hf
exact hi hf.mono_right interior_subset

中文:
引理 _root_.滤子.有基.nhds_continuousMapConst
  结论: {ι : 类型} {c : Y} {p : ι -> 命题}
  证明: by
  refine ⟨fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rcases ContinuousMap.mem_nhds_iff.mp hs with ⟨S, hSf, hS, hSsub⟩
    choose hScompact hSopen hSmaps using hS
    have : ⋂ KU in S, ⋂ (_ : KU.1.Nonempty), KU.2 in 𝓝 c := by
      simp only [biInter_mem hSf, Prod.forall, iInter_mem]
      rintro K U hKU ⟨x, hx⟩
exact (hSopen K U hKU).mem_nhds hSmaps K U hKU hx
    rcases h.mem_iff.mp this with ⟨i, hpi, hi⟩
refine ⟨(⋃ KU in S, KU.1, i), ⟨hSf.isCompact_biUnion Prod.forall.2 hScompact, hpi⟩,
      Subset.trans ?_ hSsub⟩
    intro f hf K V hKV
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact mapsTo_empty _ _
    · refine hf.out.mono (subset_biUnion_of_mem (u := Prod.fst) hKV) (hi.trans ?_)
exact (biInter_subset_of_mem hKV).trans iInter_subset _ hKne
  · rcases hs with ⟨⟨K, i⟩, ⟨hK, hpi⟩, hi⟩
    filter_upwards [eventually_mapsTo hK isOpen_interior fun x _ =>
mem_interior_iff_mem_nhds.mpr h.mem_of_mem hpi] with f hf
exact hi hf.mono_right interior_subset

Depends on / 依赖: ContinuousMap, ContinuousMap.mem_nhds_iff.mp, Nonempty, Prod.forall, Subset, Subset.trans, biInter_mem, h.mem_iff.mp, hScompact, hSf.isCompact_biUnion, hSmaps, hSopen, iInter_mem, isCompact_biUnion, mem_iff, mem_nhds, mem_nhds_iff
-/
lemma _root_.Filter.HasBasis.nhds_continuousMapConst {ι : Type*} {c : Y} {p : ι -> Prop}
    {U : ι -> Set Y} (h : (𝓝 c).HasBasis p U) :
    (𝓝 (const X c)).HasBasis (fun Ki : Set X × ι => IsCompact Ki.1 ∧ p Ki.2)
      fun Ki => {f : C(X, Y) | MapsTo f Ki.1 (U Ki.2)} := by
  refine ⟨fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rcases ContinuousMap.mem_nhds_iff.mp hs with ⟨S, hSf, hS, hSsub⟩
    choose hScompact hSopen hSmaps using hS
    have : ⋂ KU in S, ⋂ (_ : KU.1.Nonempty), KU.2 in 𝓝 c := by
      simp only [biInter_mem hSf, Prod.forall, iInter_mem]
      rintro K U hKU ⟨x, hx⟩
exact (hSopen K U hKU).mem_nhds hSmaps K U hKU hx
    rcases h.mem_iff.mp this with ⟨i, hpi, hi⟩
refine ⟨(⋃ KU in S, KU.1, i), ⟨hSf.isCompact_biUnion Prod.forall.2 hScompact, hpi⟩,
      Subset.trans ?_ hSsub⟩
    intro f hf K V hKV
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact mapsTo_empty _ _
    · refine hf.out.mono (subset_biUnion_of_mem (u := Prod.fst) hKV) (hi.trans ?_)
exact (biInter_subset_of_mem hKV).trans iInter_subset _ hKne
  · rcases hs with ⟨⟨K, i⟩, ⟨hK, hpi⟩, hi⟩
    filter_upwards [eventually_mapsTo hK isOpen_interior fun x _ =>
mem_interior_iff_mem_nhds.mpr h.mem_of_mem hpi] with f hf
exact hi hf.mono_right interior_subset

section Functorial

/-- `C(X, ·)` is a functor. -/
@[fun_prop]
/--
theorem `continuous_postcomp` / 定理 `continuous_postcomp`

English:
theorem continuous_postcomp
  given: (g : C(Y, Z))
  statement: Continuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
  proof: continuous_compactOpen.2 fun _K hK _U hU => isOpen_setOfPred_mapsTo hK (hU.preimage g.2)

中文:
定理 continuous_postcomp
  条件: (g : C(Y, Z))
  结论: 连续 (连续映射.comp g : C(X, Y) -> C(X, Z))
  证明: continuous_compactOpen.2 fun _K hK _U hU => isOpen_setOfPred_mapsTo hK (hU.preimage g.2)

Depends on / 依赖: continuous_compactOpen, hU.preimage, isOpen_setOfPred_mapsTo, preimage
-/
theorem continuous_postcomp (g : C(Y, Z)) : Continuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z)) :=
  continuous_compactOpen.2 fun _K hK _U hU => isOpen_setOfPred_mapsTo hK (hU.preimage g.2)

/--
theorem `postcomp_injective` / 定理 `postcomp_injective`

English:
theorem postcomp_injective
  given: (g : C(Y, Z)) (hg : Function.Injective g)
  proof: fun _ _ => (cancel_left hg).1

中文:
定理 postcomp_injective
  条件: (g : C(Y, Z)) (hg : 函数.单射 g)
  证明: fun _ _ => (cancel_left hg).1

Depends on / 依赖: cancel_left
-/
theorem postcomp_injective (g : C(Y, Z)) (hg : Function.Injective g) :
    Function.Injective (ContinuousMap.comp g : C(X, Y) -> C(X, Z)) :=
  fun _ _ => (cancel_left hg).1

/--
theorem `isInducing_postcomp` / 定理 `isInducing_postcomp`

English:
theorem isInducing_postcomp
  given: (g : C(Y, Z)) (hg : IsInducing g)
  proof: by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOfPred_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_ofPred_eq, comp_apply]

中文:
定理 isInducing_postcomp
  条件: (g : C(Y, Z)) (hg : 是Inducing g)
  证明: by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOfPred_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_ofPred_eq, comp_apply]

Depends on / 依赖: MapsTo, comp_apply, compactOpen_eq, hg.setOfPred_isOpen, image2_image_right, image_image2, induced_generateFrom_eq, mem_preimage, preimage_ofPred_eq, setOfPred_isOpen
-/
theorem isInducing_postcomp (g : C(Y, Z)) (hg : IsInducing g) :
    IsInducing (g.comp : C(X, Y) -> C(X, Z)) where
  eq_induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOfPred_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_ofPred_eq, comp_apply]

/--
theorem `isEmbedding_postcomp` / 定理 `isEmbedding_postcomp`

English:
theorem isEmbedding_postcomp
  given: (g : C(Y, Z)) (hg : IsEmbedding g)
  proof: ⟨isInducing_postcomp g hg.1, postcomp_injective g hg.2⟩

中文:
定理 isEmbedding_postcomp
  条件: (g : C(Y, Z)) (hg : 是嵌入 g)
  证明: ⟨isInducing_postcomp g hg.1, postcomp_injective g hg.2⟩

Depends on / 依赖: isInducing_postcomp, postcomp_injective
-/
theorem isEmbedding_postcomp (g : C(Y, Z)) (hg : IsEmbedding g) :
    IsEmbedding (g.comp : C(X, Y) -> C(X, Z)) :=
  ⟨isInducing_postcomp g hg.1, postcomp_injective g hg.2⟩

/-- `C(·, Z)` is a functor. -/
@[continuity, fun_prop]
/--
theorem `continuous_precomp` / 定理 `continuous_precomp`

English:
theorem continuous_precomp
  given: (f : C(X, Y))
  statement: Continuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
  proof: continuous_compactOpen.2 fun K hK U hU => by
    simpa only [mapsTo_image_iff] using! isOpen_setOfPred_mapsTo (hK.image f.2) hU

中文:
定理 continuous_precomp
  条件: (f : C(X, Y))
  结论: 连续 (fun g => g.comp f : C(Y, Z) -> C(X, Z))
  证明: continuous_compactOpen.2 fun K hK U hU => by
    simpa only [mapsTo_image_iff] using! isOpen_setOfPred_mapsTo (hK.image f.2) hU

Depends on / 依赖: continuous_compactOpen, hK.image, isOpen_setOfPred_mapsTo, mapsTo_image_iff
-/
theorem continuous_precomp (f : C(X, Y)) : Continuous (fun g => g.comp f : C(Y, Z) -> C(X, Z)) :=
  continuous_compactOpen.2 fun K hK U hU => by
    simpa only [mapsTo_image_iff] using! isOpen_setOfPred_mapsTo (hK.image f.2) hU

variable (Z) in
/-- Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
@[simps apply]
/--
Definition of `compRightContinuousMap` / `compRightContinuousMap` 的定义

English:
definition compRightContinuousMap
  signature: (f : C(X, Y))
  body: g.comp f

中文:
定义 compRightContinuousMap
  签名: (f : C(X, Y))
  定义体: g.comp f

Depends on / 依赖: g.comp
-/
def compRightContinuousMap (f : C(X, Y)) :
    C(C(Y, Z), C(X, Z)) where
  toFun g := g.comp f

/--
Definition of `_root_.Homeomorph.arrowCongr` / `_root_.Homeomorph.arrowCongr` 的定义

English:
definition _root_.Homeomorph.arrowCongr
  signature: (φ : X ≃ₜ Z) (ψ : Y ≃ₜ T)
  body: .comp ψ f.comp φ.symm
invFun f := .comp ψ.symm f.comp φ
.trans congrArg f φ.left_inv _ left_inv f := ext fun _ => ψ.left_inv (f _)
.trans congrArg f φ.right_inv _ right_inv f := ext fun _ => ψ.right_inv (f _)
.comp continuous_precomp _ continuous_toFun := continuous_postcomp _
.comp continuous_precomp _ continuous_invFun := continuous_postcomp _

中文:
定义 _root_.同胚.arrowCongr
  签名: (φ : X ≃ₜ Z) (ψ : Y ≃ₜ T)
  定义体: .comp ψ f.comp φ.symm
invFun f := .comp ψ.symm f.comp φ
.trans congrArg f φ.left_inv _ left_inv f := ext fun _ => ψ.left_inv (f _)
.trans congrArg f φ.right_inv _ right_inv f := ext fun _ => ψ.right_inv (f _)
.comp continuous_precomp _ continuous_toFun := continuous_postcomp _
.comp continuous_precomp _ continuous_invFun := continuous_postcomp _
-/
protected def _root_.Homeomorph.arrowCongr (φ : X ≃ₜ Z) (ψ : Y ≃ₜ T) :
    C(X, Y) ≃ₜ C(Z, T) where
toFun f := .comp ψ f.comp φ.symm
invFun f := .comp ψ.symm f.comp φ
.trans congrArg f φ.left_inv _ left_inv f := ext fun _ => ψ.left_inv (f _)
.trans congrArg f φ.right_inv _ right_inv f := ext fun _ => ψ.right_inv (f _)
.comp continuous_precomp _ continuous_toFun := continuous_postcomp _
.comp continuous_precomp _ continuous_invFun := continuous_postcomp _

/--
lemma `continuous_prodMk_const` / 引理 `continuous_prodMk_const`

English:
lemma continuous_prodMk_const
  statement: Continuous fun p : X × C(Y, Z) => prodMk (const Y p.1) p.2
  proof: by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
  rintro ⟨r, f⟩ K hK U hU H
  obtain ⟨V, W, hV, hW, hrV, hKW, hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := r))
    (hK.image f.continuous) hU (by simpa [Set.subset_def, forall_comm (α := X)])
  refine Filter.eventually_of_mem (prod_mem_nhds (hV.mem_nhds (by simpa using hrV))
    (ContinuousMap.eventually_mapsTo hK hW (Set.mapsTo_iff_image_subset.mpr hKW))) ?_
  rintro ⟨r', f'⟩ ⟨hr'V, hf'⟩ x hxK
  exact hVW (Set.mk_mem_prod hr'V (hf' hxK))

中文:
引理 continuous_prodMk_const
  结论: 连续 fun p : X × C(Y, Z) => prodMk (const Y p.1) p.2
  证明: by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
  rintro ⟨r, f⟩ K hK U hU H
  obtain ⟨V, W, hV, hW, hrV, hKW, hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := r))
    (hK.image f.continuous) hU (by simpa [Set.subset_def, forall_comm (α := X)])
  refine Filter.eventually_of_mem (prod_mem_nhds (hV.mem_nhds (by simpa using hrV))
    (ContinuousMap.eventually_mapsTo hK hW (Set.mapsTo_iff_image_subset.mpr hKW))) ?_
  rintro ⟨r', f'⟩ ⟨hr'V, hf'⟩ x hxK
  exact hVW (Set.mk_mem_prod hr'V (hf' hxK))

Depends on / 依赖: ContinuousAt, ContinuousMap, ContinuousMap.eventually_mapsTo, ContinuousMap.tendsto_nhds_compactOpen, Filter, Filter.eventually_of_mem, Set.mapsTo_iff_image_subset.mpr, Set.subset_def, continuous, continuous_iff_continuousAt, eventually_mapsTo, eventually_of_mem, f.continuous, forall_comm, generalized_tube_lemma, hK.image, hV.mem_nhds, isCompact_singleton, mapsTo_iff_image_subset, mem_nhds
-/
lemma continuous_prodMk_const : Continuous fun p : X × C(Y, Z) => prodMk (const Y p.1) p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
  rintro ⟨r, f⟩ K hK U hU H
  obtain ⟨V, W, hV, hW, hrV, hKW, hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := r))
    (hK.image f.continuous) hU (by simpa [Set.subset_def, forall_comm (α := X)])
  refine Filter.eventually_of_mem (prod_mem_nhds (hV.mem_nhds (by simpa using hrV))
    (ContinuousMap.eventually_mapsTo hK hW (Set.mapsTo_iff_image_subset.mpr hKW))) ?_
  rintro ⟨r', f'⟩ ⟨hr'V, hf'⟩ x hxK
  exact hVW (Set.mk_mem_prod hr'V (hf' hxK))

variable [LocallyCompactPair Y Z]

/--
theorem `continuous_comp'` / 定理 `continuous_comp'`

English:
theorem continuous_comp'
  statement: Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1
  proof: by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : exists L in 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet]; rw [← mapsTo_iff_image_subset] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ =>
hg'.comp hf'.mono_right interior_subset

中文:
定理 continuous_comp'
  结论: 连续 fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1
  证明: by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : exists L in 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet]; rw [← mapsTo_iff_image_subset] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ =>
hg'.comp hf'.mono_right interior_subset

Depends on / 依赖: ContinuousAt, IsCompact, MapsTo, continuous, continuous_iff_continuousAt, eventually_mapsTo, exists_mem_nhdsSet_isCompact_mapsTo, f.continuous, g.continuous, hK.image, isOpen_interior, mapsTo_iff_image_subset, mapsTo_image_iff, prod_nhds, simp_rw, subset_interior_iff_mem_nhdsSet, tendsto_nhds_compactOpen
-/
theorem continuous_comp' : Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : exists L in 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet]; rw [← mapsTo_iff_image_subset] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ =>
hg'.comp hf'.mono_right interior_subset

/--
lemma `_root_.Filter.Tendsto.compCM` / 引理 `_root_.Filter.Tendsto.compCM`

English:
lemma _root_.Filter.Tendsto.compCM
  statement: {α : Type*} {l : Filter α} {g : α -> C(Y, Z)} {g₀ : C(Y, Z)}
  proof: (continuous_comp'.tendsto (f₀, g₀)).comp (hf.prodMk_nhds hg)

中文:
引理 _root_.滤子.收敛.compCM
  结论: {α : 类型} {l : 滤子 α} {g : α -> C(Y, Z)} {g₀ : C(Y, Z)}
  证明: (continuous_comp'.tendsto (f₀, g₀)).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_comp, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
lemma _root_.Filter.Tendsto.compCM {α : Type*} {l : Filter α} {g : α -> C(Y, Z)} {g₀ : C(Y, Z)}
    {f : α -> C(X, Y)} {f₀ : C(X, Y)} (hg : Tendsto g l (𝓝 g₀)) (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun a => (g a).comp (f a)) l (𝓝 (g₀.comp f₀)) :=
  (continuous_comp'.tendsto (f₀, g₀)).comp (hf.prodMk_nhds hg)

variable {X' : Type*} [TopologicalSpace X'] {a : X'} {g : X' -> C(Y, Z)} {f : X' -> C(X, Y)}
  {s : Set X'}

nonrec lemma _root_.ContinuousAt.compCM (hg : ContinuousAt g a) (hf : ContinuousAt f a) :
    ContinuousAt (fun x => (g x).comp (f x)) a :=
  hg.compCM hf

nonrec lemma _root_.ContinuousWithinAt.compCM (hg : ContinuousWithinAt g s a)
    (hf : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => (g x).comp (f x)) s a :=
  hg.compCM hf

/--
lemma `_root_.ContinuousOn.compCM` / 引理 `_root_.ContinuousOn.compCM`

English:
lemma _root_.ContinuousOn.compCM
  given: (hg : ContinuousOn g s) (hf : ContinuousOn f s)
  proof: fun a ha =>
  (hg a ha).compCM (hf a ha)

中文:
引理 _root_.ContinuousOn.compCM
  条件: (hg : ContinuousOn g s) (hf : ContinuousOn f s)
  证明: fun a ha =>
  (hg a ha).compCM (hf a ha)
-/
lemma _root_.ContinuousOn.compCM (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s := fun a ha =>
  (hg a ha).compCM (hf a ha)

/--
lemma `_root_.Continuous.compCM` / 引理 `_root_.Continuous.compCM`

English:
lemma _root_.Continuous.compCM
  given: (hg : Continuous g) (hf : Continuous f)
  proof: continuous_comp'.comp (hf.prodMk hg)

中文:
引理 _root_.连续.compCM
  条件: (hg : 连续 g) (hf : 连续 f)
  证明: continuous_comp'.comp (hf.prodMk hg)

Depends on / 依赖: continuous_comp, hf.prodMk, prodMk
-/
lemma _root_.Continuous.compCM (hg : Continuous g) (hf : Continuous f) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prodMk hg)

end Functorial

section Ev

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyCompactPair
  signature: X Y] : ContinuousEval C(X, Y) X Y where
  body: by
    simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro ⟨f, x⟩ U ⟨hx : f x in U, hU : IsOpen U⟩
    rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
    filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h => h.1 h.2

中文:
实例 [LocallyCompactPair
  签名: X Y] : 余ntinuousEval C(X, Y) X Y where
  定义体: by
    simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro ⟨f, x⟩ U ⟨hx : f x in U, hU : IsOpen U⟩
    rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
    filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h => h.1 h.2

Depends on / 依赖: ContinuousAt, IsOpen, continuous, continuous_iff_continuousAt, eventually_mapsTo, exists_mem_nhds_isCompact_mapsTo, f.continuous, filter_upwards, hU.mem_nhds, mem_nhds, nhds_basis_opens, prod_mem_nhds, simp_rw, tendsto_right_iff
-/
instance [LocallyCompactPair X Y] : ContinuousEval C(X, Y) X Y where
  continuous_eval := by
    simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro ⟨f, x⟩ U ⟨hx : f x in U, hU : IsOpen U⟩
    rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
    filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h => h.1 h.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEvalConst C(X, Y) X Y
  body: continuous_def.2 fun U hU => by simpa using! isOpen_setOfPred_mapsTo isCompact_singleton hU

中文:
实例 :
  签名: 余ntinuousEvalConst C(X, Y) X Y
  定义体: continuous_def.2 fun U hU => by simpa using! isOpen_setOfPred_mapsTo isCompact_singleton hU

Depends on / 依赖: continuous_def, isCompact_singleton, isOpen_setOfPred_mapsTo
-/
instance : ContinuousEvalConst C(X, Y) X Y where
  continuous_eval_const x :=
    continuous_def.2 fun U hU => by simpa using! isOpen_setOfPred_mapsTo isCompact_singleton hU

/--
lemma `isClosed_setOfPred_mapsTo` / 引理 `isClosed_setOfPred_mapsTo`

English:
lemma isClosed_setOfPred_mapsTo
  given: {t : Set Y} (ht : IsClosed t) (s : Set X)
  proof: ht.setOfPred_mapsTo fun _ _ => continuous_eval_const _

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_mapsTo := isClosed_setOfPred_mapsTo

中文:
引理 isClosed_setOfPred_mapsTo
  条件: {t : 集合 Y} (ht : 是闭集 t) (s : 集合 X)
  证明: ht.setOfPred_mapsTo fun _ _ => continuous_eval_const _

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_mapsTo := isClosed_setOfPred_mapsTo

Depends on / 依赖: continuous_eval_const, ht.setOfPred_mapsTo, setOfPred_mapsTo
-/
lemma isClosed_setOfPred_mapsTo {t : Set Y} (ht : IsClosed t) (s : Set X) :
    IsClosed {f : C(X, Y) | MapsTo f s t} :=
  ht.setOfPred_mapsTo fun _ _ => continuous_eval_const _

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_mapsTo := isClosed_setOfPred_mapsTo

/--
lemma `isClopen_setOfPred_mapsTo` / 引理 `isClopen_setOfPred_mapsTo`

English:
lemma isClopen_setOfPred_mapsTo
  given: (hK : IsCompact K) (hU : IsClopen U)
  proof: ⟨isClosed_setOfPred_mapsTo hU.isClosed K, isOpen_setOfPred_mapsTo hK hU.isOpen⟩

@[deprecated (since := "2026-07-09")] alias isClopen_setOf_mapsTo := isClopen_setOfPred_mapsTo

@[norm_cast]

中文:
引理 isClopen_setOfPred_mapsTo
  条件: (hK : 是紧集 K) (hU : IsClopen U)
  证明: ⟨isClosed_setOfPred_mapsTo hU.isClosed K, isOpen_setOfPred_mapsTo hK hU.isOpen⟩

@[deprecated (since := "2026-07-09")] alias isClopen_setOf_mapsTo := isClopen_setOfPred_mapsTo

@[norm_cast]

Depends on / 依赖: hU.isClosed, hU.isOpen, isClosed, isClosed_setOfPred_mapsTo, isOpen, isOpen_setOfPred_mapsTo
-/
lemma isClopen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsClopen U) :
    IsClopen {f : C(X, Y) | MapsTo f K U} :=
  ⟨isClosed_setOfPred_mapsTo hU.isClosed K, isOpen_setOfPred_mapsTo hK hU.isOpen⟩

@[deprecated (since := "2026-07-09")] alias isClopen_setOf_mapsTo := isClopen_setOfPred_mapsTo

@[norm_cast]
/--
lemma `specializes_coe` / 引理 `specializes_coe`

English:
lemma specializes_coe
  given: {f g : C(X, Y)}
  statement: ⇑f ⤳ ⇑g ↔ f ⤳ g
  proof: by
  refine ⟨fun h => ?_, fun h => h.map continuous_coeFun⟩
  suffices forall K, IsCompact K -> forall U, IsOpen U -> MapsTo g K U -> MapsTo f K U by
    simpa [specializes_iff_pure, nhds_compactOpen]
  exact fun K _ U hU hg x hx => (h.map (continuous_apply x)).mem_open hU (hg hx)

@[norm_cast]

中文:
引理 specializes_coe
  条件: {f g : C(X, Y)}
  结论: ⇑f ⤳ ⇑g ↔ f ⤳ g
  证明: by
  refine ⟨fun h => ?_, fun h => h.map continuous_coeFun⟩
  suffices forall K, IsCompact K -> forall U, IsOpen U -> MapsTo g K U -> MapsTo f K U by
    simpa [specializes_iff_pure, nhds_compactOpen]
  exact fun K _ U hU hg x hx => (h.map (continuous_apply x)).mem_open hU (hg hx)

@[norm_cast]

Depends on / 依赖: IsCompact, IsOpen, MapsTo, continuous_apply, continuous_coeFun, h.map, mem_open, nhds_compactOpen, specializes_iff_pure
-/
lemma specializes_coe {f g : C(X, Y)} : ⇑f ⤳ ⇑g ↔ f ⤳ g := by
  refine ⟨fun h => ?_, fun h => h.map continuous_coeFun⟩
  suffices forall K, IsCompact K -> forall U, IsOpen U -> MapsTo g K U -> MapsTo f K U by
    simpa [specializes_iff_pure, nhds_compactOpen]
  exact fun K _ U hU hg x hx => (h.map (continuous_apply x)).mem_open hU (hg hx)

@[norm_cast]
/--
lemma `inseparable_coe` / 引理 `inseparable_coe`

English:
lemma inseparable_coe
  given: {f g : C(X, Y)}
  statement: Inseparable (f : X -> Y) g ↔ Inseparable f g
  proof: by
  simp only [inseparable_iff_specializes_and, specializes_coe]

中文:
引理 inseparable_coe
  条件: {f g : C(X, Y)}
  结论: 不可分 (f : X -> Y) g ↔ 不可分 f g
  证明: by
  simp only [inseparable_iff_specializes_and, specializes_coe]

Depends on / 依赖: inseparable_iff_specializes_and, specializes_coe
-/
lemma inseparable_coe {f g : C(X, Y)} : Inseparable (f : X -> Y) g ↔ Inseparable f g := by
  simp only [inseparable_iff_specializes_and, specializes_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T0Space
  signature: Y] : T0Space C(X, Y)
  body: t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

中文:
实例 [T0空间
  签名: Y] : T0空间 C(X, Y)
  定义体: t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coeFun, t0Space_of_injective_of_continuous
-/
instance [T0Space Y] : T0Space C(X, Y) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R0Space
  signature: Y] : R0Space C(X, Y) where
  body: by
    rw [← specializes_coe] at h ⊢
    exact h.symm

中文:
实例 [R0空间
  签名: Y] : R0空间 C(X, Y) where
  定义体: by
    rw [← specializes_coe] at h ⊢
    exact h.symm

Depends on / 依赖: h.symm, specializes_coe
-/
instance [R0Space Y] : R0Space C(X, Y) where
  specializes_symm.symm f g h := by
    rw [← specializes_coe] at h ⊢
    exact h.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: Y] : T1Space C(X, Y)
  body: t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

中文:
实例 [T1空间
  签名: Y] : T1空间 C(X, Y)
  定义体: t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, continuous_coeFun, t1Space_of_injective_of_continuous
-/
instance [T1Space Y] : T1Space C(X, Y) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R1Space
  signature: Y] : R1Space C(X, Y)
  body: .of_continuous_specializes_imp continuous_coeFun fun _ _ => specializes_coe.1

中文:
实例 [R1空间
  签名: Y] : R1空间 C(X, Y)
  定义体: .of_continuous_specializes_imp continuous_coeFun fun _ _ => specializes_coe.1

Depends on / 依赖: continuous_coeFun, of_continuous_specializes_imp, specializes_coe
-/
instance [R1Space Y] : R1Space C(X, Y) :=
  .of_continuous_specializes_imp continuous_coeFun fun _ _ => specializes_coe.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: Y] : T2Space C(X, Y)
  body: inferInstance

中文:
实例 [T2空间
  签名: Y] : T2空间 C(X, Y)
  定义体: inferInstance
-/
instance [T2Space Y] : T2Space C(X, Y) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RegularSpace
  signature: Y] : RegularSpace C(X, Y)
  body: .of_lift'_closure_le fun f => by
    rw [← tendsto_id']; rw [tendsto_nhds_compactOpen]
    intro K hK U hU hf
    rcases (hK.image f.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 hf.image_subset)
      with ⟨V, hVo, hKV, hVU⟩
    filter_upwards [mem_lift' (eventually_mapsTo hK hVo (mapsTo_iff_image_subset.2 hKV))] with g hg
    refine ((isClosed_setOfPred_mapsTo isClosed_closure K).closure_subset ?_).mono_right hVU
    exact closure_mono (fun _ h => h.mono_right subset_closure) hg

中文:
实例 [正则空间
  签名: Y] : 正则空间 C(X, Y)
  定义体: .of_lift'_closure_le fun f => by
    rw [← tendsto_id']; rw [tendsto_nhds_compactOpen]
    intro K hK U hU hf
    rcases (hK.image f.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 hf.image_subset)
      with ⟨V, hVo, hKV, hVU⟩
    filter_upwards [mem_lift' (eventually_mapsTo hK hVo (mapsTo_iff_image_subset.2 hKV))] with g hg
    refine ((isClosed_setOfPred_mapsTo isClosed_closure K).closure_subset ?_).mono_right hVU
    exact closure_mono (fun _ h => h.mono_right subset_closure) hg

Depends on / 依赖: _closure_le, closure_mono, closure_subset, continuous, eventually_mapsTo, exists_isOpen_closure_subset, f.continuous, filter_upwards, h.mono_right, hK.image, hU.mem_nhdsSet, hf.image_subset, image_subset, isClosed_closure, isClosed_setOfPred_mapsTo, mapsTo_iff_image_subset, mem_lift, mem_nhdsSet, mono_right, of_lift
-/
instance [RegularSpace Y] : RegularSpace C(X, Y) :=
  .of_lift'_closure_le fun f => by
    rw [← tendsto_id']; rw [tendsto_nhds_compactOpen]
    intro K hK U hU hf
    rcases (hK.image f.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 hf.image_subset)
      with ⟨V, hVo, hKV, hVU⟩
    filter_upwards [mem_lift' (eventually_mapsTo hK hVo (mapsTo_iff_image_subset.2 hKV))] with g hg
    refine ((isClosed_setOfPred_mapsTo isClosed_closure K).closure_subset ?_).mono_right hVU
    exact closure_mono (fun _ h => h.mono_right subset_closure) hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T3Space
  signature: Y] : T3Space C(X, Y)
  body: inferInstance

中文:
实例 [T3空间
  签名: Y] : T3空间 C(X, Y)
  定义体: inferInstance
-/
instance [T3Space Y] : T3Space C(X, Y) := inferInstance

end Ev

section DiscreteTopology
variable [DiscreteTopology X]

/-- The continuous functions from `X` to `Y` are the same as the plain functions when `X` is
discrete. -/
@[simps toEquiv]
/--
Definition of `homeoFnOfDiscrete` / `homeoFnOfDiscrete` 的定义

English:
definition homeoFnOfDiscrete
  signature: : C(X, Y) ≃ₜ (X -> Y) where
  body: equivFnOfDiscrete
  continuous_invFun :=
    continuous_compactOpen.2 fun K hK U hU => isOpen_set_pi hK.finite_of_discrete fun _ _ => hU

中文:
定义 homeoFnOfDiscrete
  签名: : C(X, Y) ≃ₜ (X -> Y) where
  定义体: equivFnOfDiscrete
  continuous_invFun :=
    continuous_compactOpen.2 fun K hK U hU => isOpen_set_pi hK.finite_of_discrete fun _ _ => hU

Depends on / 依赖: equivFnOfDiscrete
-/
def homeoFnOfDiscrete : C(X, Y) ≃ₜ (X -> Y) where
  __ := equivFnOfDiscrete
  continuous_invFun :=
    continuous_compactOpen.2 fun K hK U hU => isOpen_set_pi hK.finite_of_discrete fun _ _ => hU

attribute [simps! -isSimp] homeoFnOfDiscrete

/--
lemma `coe_homeoFnOfDiscrete` / 引理 `coe_homeoFnOfDiscrete`

English:
lemma coe_homeoFnOfDiscrete
  statement: ⇑homeoFnOfDiscrete = (DFunLike.coe : C(X, Y) -> X -> Y)
  proof: rfl

中文:
引理 coe_homeoFnOfDiscrete
  结论: ⇑homeoFnOfDiscrete = (依赖函数状.coe : C(X, Y) -> X -> Y)
  证明: rfl
-/
@[simp] lemma coe_homeoFnOfDiscrete : ⇑homeoFnOfDiscrete = (DFunLike.coe : C(X, Y) -> X -> Y) := rfl

/--
lemma `homeoFnOfDiscrete_symm_apply` / 引理 `homeoFnOfDiscrete_symm_apply`

English:
lemma homeoFnOfDiscrete_symm_apply
  given: (f : X -> Y)
  statement: homeoFnOfDiscrete.symm f = f
  proof: rfl

中文:
引理 homeoFnOfDiscrete_symm_apply
  条件: (f : X -> Y)
  结论: homeoFnOfDiscrete.symm f = f
  证明: rfl
-/
@[simp] lemma homeoFnOfDiscrete_symm_apply (f : X -> Y) : homeoFnOfDiscrete.symm f = f := rfl

/--
lemma `isHomeomorph_coe` / 引理 `isHomeomorph_coe`

English:
lemma isHomeomorph_coe
  statement: IsHomeomorph ((⇑) : C(X, Y) -> X -> Y)
  proof: homeoFnOfDiscrete.isHomeomorph

中文:
引理 isHomeomorph_coe
  结论: 是同胚 ((⇑) : C(X, Y) -> X -> Y)
  证明: homeoFnOfDiscrete.isHomeomorph

Depends on / 依赖: homeoFnOfDiscrete, homeoFnOfDiscrete.isHomeomorph, isHomeomorph
-/
lemma isHomeomorph_coe : IsHomeomorph ((⇑) : C(X, Y) -> X -> Y) := homeoFnOfDiscrete.isHomeomorph

end DiscreteTopology

section InfInduced

/--
theorem `continuous_restrict` / 定理 `continuous_restrict`

English:
theorem continuous_restrict
  given: (s : Set X)
  statement: Continuous fun F : C(X, Y) => F.restrict s
  proof: continuous_precomp restrict s .id X

中文:
定理 continuous_restrict
  条件: (s : 集合 X)
  结论: 连续 fun F : C(X, Y) => F.restrict s
  证明: continuous_precomp restrict s .id X

Depends on / 依赖: continuous_precomp, restrict
-/
theorem continuous_restrict (s : Set X) : Continuous fun F : C(X, Y) => F.restrict s :=
continuous_precomp restrict s .id X

/--
theorem `compactOpen_le_induced` / 定理 `compactOpen_le_induced`

English:
theorem compactOpen_le_induced
  given: (s : Set X)
  proof: (continuous_restrict s).le_induced

中文:
定理 compactOpen_le_induced
  条件: (s : 集合 X)
  证明: (continuous_restrict s).le_induced

Depends on / 依赖: continuous_restrict, le_induced
-/
theorem compactOpen_le_induced (s : Set X) :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) <=
      .induced (restrict s) ContinuousMap.compactOpen :=
  (continuous_restrict s).le_induced

/--
theorem `compactOpen_eq_iInf_induced` / 定理 `compactOpen_eq_iInf_induced`

English:
theorem compactOpen_eq_iInf_induced
  proof: by
  refine le_antisymm (le_iInf₂ fun s _ => compactOpen_le_induced s) ?_
refine le_generateFrom forall_mem_image2.2 fun K (hK : IsCompact K) U hU => ?_
  refine TopologicalSpace.le_def.1 (iInf₂_le K hK) _ ?_
  convert! isOpen_induced (isOpen_setOfPred_mapsTo (isCompact_iff_isCompact_univ.1 hK) hU)
  simp [Subtype.forall, MapsTo]

中文:
定理 compactOpen_eq_iInf_induced
  证明: by
  refine le_antisymm (le_iInf₂ fun s _ => compactOpen_le_induced s) ?_
refine le_generateFrom forall_mem_image2.2 fun K (hK : IsCompact K) U hU => ?_
  refine TopologicalSpace.le_def.1 (iInf₂_le K hK) _ ?_
  convert! isOpen_induced (isOpen_setOfPred_mapsTo (isCompact_iff_isCompact_univ.1 hK) hU)
  simp [Subtype.forall, MapsTo]

Depends on / 依赖: IsCompact, MapsTo, Subtype, Subtype.forall, TopologicalSpace, TopologicalSpace.le_def, compactOpen_le_induced, convert, forall_mem_image2, isCompact_iff_isCompact_univ, isOpen_induced, isOpen_setOfPred_mapsTo, le_antisymm, le_def, le_generateFrom
-/
theorem compactOpen_eq_iInf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) =
      ⨅ (K : Set X) (_ : IsCompact K), .induced (.restrict K) ContinuousMap.compactOpen := by
  refine le_antisymm (le_iInf₂ fun s _ => compactOpen_le_induced s) ?_
refine le_generateFrom forall_mem_image2.2 fun K (hK : IsCompact K) U hU => ?_
  refine TopologicalSpace.le_def.1 (iInf₂_le K hK) _ ?_
  convert! isOpen_induced (isOpen_setOfPred_mapsTo (isCompact_iff_isCompact_univ.1 hK) hU)
  simp [Subtype.forall, MapsTo]

/--
theorem `nhds_compactOpen_eq_iInf_nhds_induced` / 定理 `nhds_compactOpen_eq_iInf_nhds_induced`

English:
theorem nhds_compactOpen_eq_iInf_nhds_induced
  given: (f : C(X, Y))
  proof: by
  rw [compactOpen_eq_iInf_induced]
  simp only [nhds_iInf, nhds_induced]

中文:
定理 nhds_compactOpen_eq_iInf_nhds_induced
  条件: (f : C(X, Y))
  证明: by
  rw [compactOpen_eq_iInf_induced]
  simp only [nhds_iInf, nhds_induced]

Depends on / 依赖: compactOpen_eq_iInf_induced, nhds_iInf, nhds_induced
-/
theorem nhds_compactOpen_eq_iInf_nhds_induced (f : C(X, Y)) :
    𝓝 f = ⨅ (s) (_ : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compactOpen_eq_iInf_induced]
  simp only [nhds_iInf, nhds_induced]

/--
theorem `tendsto_compactOpen_restrict` / 定理 `tendsto_compactOpen_restrict`

English:
theorem tendsto_compactOpen_restrict
  statement: {ι : Type*} {l : Filter ι} {F : ι -> C(X, Y)} {f : C(X, Y)}
  proof: (continuous_restrict s).continuousAt.tendsto.comp hFf

中文:
定理 tendsto_compactOpen_restrict
  结论: {ι : 类型} {l : 滤子 ι} {F : ι -> C(X, Y)} {f : C(X, Y)}
  证明: (continuous_restrict s).continuousAt.tendsto.comp hFf

Depends on / 依赖: continuousAt, continuousAt.tendsto.comp, continuous_restrict, tendsto
-/
theorem tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι -> C(X, Y)} {f : C(X, Y)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set X) :
    Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).continuousAt.tendsto.comp hFf

/--
theorem `tendsto_compactOpen_iff_forall` / 定理 `tendsto_compactOpen_iff_forall`

English:
theorem tendsto_compactOpen_iff_forall
  given: {ι : Type*} {l : Filter ι} (F : ι -> C(X, Y)) (f : C(X, Y))
  proof: by
  rw [compactOpen_eq_iInf_induced]
  simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp_def]

中文:
定理 tendsto_compactOpen_iff_对任意
  条件: {ι : 类型} {l : 滤子 ι} (F : ι -> C(X, Y)) (f : C(X, Y))
  证明: by
  rw [compactOpen_eq_iInf_induced]
  simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp_def]

Depends on / 依赖: Filter, Filter.tendsto_comap_iff, Function, Function.comp_def, comp_def, compactOpen_eq_iInf_induced, nhds_iInf, nhds_induced, tendsto_comap_iff
-/
theorem tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι -> C(X, Y)) (f : C(X, Y)) :
    Tendsto F l (𝓝 f) ↔
      forall K, IsCompact K -> Tendsto (fun i => (F i).restrict K) l (𝓝 (f.restrict K)) := by
  rw [compactOpen_eq_iInf_induced]
  simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_tendsto_compactOpen_iff_forall` / 定理 `exists_tendsto_compactOpen_iff_forall`

English:
theorem exists_tendsto_compactOpen_iff_forall
  statement: [WeaklyLocallyCompactSpace X] [T2Space Y]
  proof: by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      forall (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x in s₁) (hxs₂ : x in s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      have := isCompact_iff_compactSpace.mp hs₁
      have := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs

中文:
定理 存在_tendsto_compactOpen_iff_对任意
  结论: [WeaklyLocallyCompact空间 X] [T2空间 Y]
  证明: by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      forall (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x in s₁) (hxs₂ : x in s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      have := isCompact_iff_compactSpace.mp hs₁
      have := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs

Depends on / 依赖: f.restrict, restrict, tendsto_compactOpen_restrict
-/
theorem exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Space Y]
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι -> C(X, Y)) :
    (exists f, Filter.Tendsto F l (𝓝 f)) ↔
      forall s : Set X, IsCompact s -> exists f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) := by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      forall (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x in s₁) (hxs₂ : x in s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      have := isCompact_iff_compactSpace.mp hs₁
      have := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs

end InfInduced

section Coev

variable (X Y)

/-- The coevaluation map `Y → C(X, Y × X)` sending a point `x : Y` to the continuous function
on `X` sending `y` to `(x, y)`. -/
@[simps -fullyApplied]
/--
Definition of `coev` / `coev` 的定义

English:
definition coev
  signature: (b : Y)
  body: { toFun := Prod.mk b }

中文:
定义 coev
  签名: (b : Y)
  定义体: { toFun := Prod.mk b }

Depends on / 依赖: Prod.mk
-/
def coev (b : Y) : C(X, Y × X) :=
  { toFun := Prod.mk b }

variable {X Y}

/--
theorem `image_coev` / 定理 `image_coev`

English:
theorem image_coev
  given: {y : Y} (s : Set X)
  statement: coev X Y y '' s = {y} ×ˢ s
  proof: by simp [singleton_prod]

中文:
定理 image_coev
  条件: {y : Y} (s : 集合 X)
  结论: coev X Y y '' s = {y} ×ˢ s
  证明: by simp [singleton_prod]

Depends on / 依赖: singleton_prod
-/
theorem image_coev {y : Y} (s : Set X) : coev X Y y '' s = {y} ×ˢ s := by simp [singleton_prod]

/--
theorem `continuous_coev` / 定理 `continuous_coev`

English:
theorem continuous_coev
  statement: Continuous (coev X Y)
  proof: ((continuous_prodMk_const (X := Y) (Y := X) (Z := X)).comp
    (.prodMk continuous_id (continuous_const (y := ContinuousMap.id _))) :)

中文:
定理 continuous_coev
  结论: 连续 (coev X Y)
  证明: ((continuous_prodMk_const (X := Y) (Y := X) (Z := X)).comp
    (.prodMk continuous_id (continuous_const (y := ContinuousMap.id _))) :)

Depends on / 依赖: ContinuousMap, ContinuousMap.id, continuous_const, continuous_id, continuous_prodMk_const, prodMk
-/
theorem continuous_coev : Continuous (coev X Y) :=
  ((continuous_prodMk_const (X := Y) (Y := X) (Z := X)).comp
    (.prodMk continuous_id (continuous_const (y := ContinuousMap.id _))) :)

end Coev

section Curry

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: (f : C(X × Y, Z))
  body: ⟨Function.curry f a, f.continuous.comp by fun_prop⟩
  continuous_toFun := (continuous_postcomp f).comp continuous_coev

@[simp]

中文:
定义 curry
  签名: (f : C(X × Y, Z))
  定义体: ⟨Function.curry f a, f.continuous.comp by fun_prop⟩
  continuous_toFun := (continuous_postcomp f).comp continuous_coev

@[simp]

Depends on / 依赖: Function, Function.curry, continuous, f.continuous.comp, fun_prop
-/
def curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) where
toFun a := ⟨Function.curry f a, f.continuous.comp by fun_prop⟩
  continuous_toFun := (continuous_postcomp f).comp continuous_coev

@[simp]
/--
theorem `curry_apply` / 定理 `curry_apply`

English:
theorem curry_apply
  given: (f : C(X × Y, Z)) (a : X) (b : Y)
  statement: f.curry a b = f (a, b)
  proof: rfl

中文:
定理 curry_apply
  条件: (f : C(X × Y, Z)) (a : X) (b : Y)
  结论: f.curry a b = f (a, b)
  证明: rfl
-/
theorem curry_apply (f : C(X × Y, Z)) (a : X) (b : Y) : f.curry a b = f (a, b) :=
  rfl

/--
theorem `continuous_of_continuous_uncurry` / 定理 `continuous_of_continuous_uncurry`

English:
theorem continuous_of_continuous_uncurry
  statement: (f : X -> C(Y, Z))
  proof: (curry ⟨_, h⟩).2

中文:
定理 continuous_of_continuous_uncurry
  结论: (f : X -> C(Y, Z))
  证明: (curry ⟨_, h⟩).2
-/
theorem continuous_of_continuous_uncurry (f : X -> C(Y, Z))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  (curry ⟨_, h⟩).2

/--
theorem `continuousOn_of_continuousOn_uncurry` / 定理 `continuousOn_of_continuousOn_uncurry`

English:
theorem continuousOn_of_continuousOn_uncurry
  statement: {s : Set X} (f : X -> C(Y, Z))
  proof: continuousOn_iff_continuous_domRestrict.mpr continuous_of_continuous_uncurry _
    h.comp_continuous (continuous_subtype_val.prodMap continuous_id) (fun x => ⟨x.1.2, trivial⟩)

中文:
定理 continuousOn_of_continuousOn_uncurry
  结论: {s : 集合 X} (f : X -> C(Y, Z))
  证明: continuousOn_iff_continuous_domRestrict.mpr continuous_of_continuous_uncurry _
    h.comp_continuous (continuous_subtype_val.prodMap continuous_id) (fun x => ⟨x.1.2, trivial⟩)

Depends on / 依赖: comp_continuous, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mpr, continuous_id, continuous_of_continuous_uncurry, continuous_subtype_val, continuous_subtype_val.prodMap, h.comp_continuous, prodMap
-/
theorem continuousOn_of_continuousOn_uncurry {s : Set X} (f : X -> C(Y, Z))
    (h : ContinuousOn (Function.uncurry fun x y => f x y) (s ×ˢ univ)) : ContinuousOn f s :=
continuousOn_iff_continuous_domRestrict.mpr continuous_of_continuous_uncurry _
    h.comp_continuous (continuous_subtype_val.prodMap continuous_id) (fun x => ⟨x.1.2, trivial⟩)

/--
theorem `continuous_curry` / 定理 `continuous_curry`

English:
theorem continuous_curry
  given: [LocallyCompactSpace (X × Y)]
  proof: by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval

中文:
定理 continuous_curry
  条件: [局部紧空间 (X × Y)]
  证明: by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval

Depends on / 依赖: Homeomorph, Homeomorph.prodAssoc, comp_continuous_iff, continuous_eval, continuous_of_continuous_uncurry, prodAssoc, symm.comp_continuous_iff
-/
theorem continuous_curry [LocallyCompactSpace (X × Y)] :
    Continuous (curry : C(X × Y, Z) -> C(X, C(Y, Z))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval

/--
theorem `continuous_uncurry_of_continuous` / 定理 `continuous_uncurry_of_continuous`

English:
theorem continuous_uncurry_of_continuous
  given: [LocallyCompactSpace Y] (f : C(X, C(Y, Z)))
  proof: continuous_eval.comp f.continuous.prodMap continuous_id

中文:
定理 continuous_uncurry_of_continuous
  条件: [局部紧空间 Y] (f : C(X, C(Y, Z)))
  证明: continuous_eval.comp f.continuous.prodMap continuous_id

Depends on / 依赖: continuous, continuous_eval, continuous_eval.comp, continuous_id, f.continuous.prodMap, prodMap
-/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    Continuous (Function.uncurry fun x y => f x y) :=
continuous_eval.comp f.continuous.prodMap continuous_id

/-- The uncurried form of a continuous map `X → C(Y, Z)` as a continuous map `X × Y → Z` (if `Y` is
locally compact). If `X` is also locally compact, then this is a homeomorphism between the two
function spaces, see `Homeomorph.curry`. -/
@[simps]
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: [LocallyCompactSpace Y] (f : C(X, C(Y, Z)))
  body: ⟨_, continuous_uncurry_of_continuous f⟩

中文:
定义 uncurry
  签名: [局部紧空间 Y] (f : C(X, C(Y, Z)))
  定义体: ⟨_, continuous_uncurry_of_continuous f⟩

Depends on / 依赖: continuous_uncurry_of_continuous
-/
def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `continuous_uncurry` / 定理 `continuous_uncurry`

English:
theorem continuous_uncurry
  given: [LocallyCompactSpace X] [LocallyCompactSpace Y]
  proof: by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  dsimp [Function.comp_def]
  exact (continuous_fst.fst.eval continuous_fst.snd).eval continuous_snd

中文:
定理 continuous_uncurry
  条件: [局部紧空间 X] [局部紧空间 Y]
  证明: by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  dsimp [Function.comp_def]
  exact (continuous_fst.fst.eval continuous_fst.snd).eval continuous_snd

Depends on / 依赖: Function, Function.comp_def, Homeomorph, Homeomorph.prodAssoc, comp_continuous_iff, comp_def, continuous_fst, continuous_fst.fst.eval, continuous_fst.snd, continuous_of_continuous_uncurry, continuous_snd, prodAssoc
-/
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) -> C(X × Y, Z)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  dsimp [Function.comp_def]
  exact (continuous_fst.fst.eval continuous_fst.snd).eval continuous_snd

/--
Definition of `const'` / `const'` 的定义

English:
definition const'
  signature: : C(Y, C(X, Y))
  body: curry ContinuousMap.fst

@[simp]

中文:
定义 const'
  签名: : C(Y, C(X, Y))
  定义体: curry ContinuousMap.fst

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.fst
-/
def const' : C(Y, C(X, Y)) :=
  curry ContinuousMap.fst

@[simp]
/--
theorem `coe_const'` / 定理 `coe_const'`

English:
theorem coe_const'
  statement: (const' : Y -> C(X, Y)) = const X
  proof: rfl

@[fun_prop]

中文:
定理 coe_const'
  结论: (const' : Y -> C(X, Y)) = const X
  证明: rfl

@[fun_prop]
-/
theorem coe_const' : (const' : Y -> C(X, Y)) = const X :=
  rfl

@[fun_prop]
/--
theorem `continuous_const'` / 定理 `continuous_const'`

English:
theorem continuous_const'
  statement: Continuous (const X : Y -> C(X, Y))
  proof: const'.continuous

中文:
定理 continuous_const'
  结论: 连续 (const X : Y -> C(X, Y))
  证明: const'.continuous

Depends on / 依赖: continuous
-/
theorem continuous_const' : Continuous (const X : Y -> C(X, Y)) :=
  const'.continuous

section mkD

/--
lemma `continuous_mkD_of_uncurry` / 引理 `continuous_mkD_of_uncurry`

English:
lemma continuous_mkD_of_uncurry
  proof: by
  have (x : _) : Continuous (f x) := f_cont.comp (Continuous.prodMk_right x)
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x)]
  exact f_cont

中文:
引理 continuous_mkD_of_uncurry
  证明: by
  have (x : _) : Continuous (f x) := f_cont.comp (Continuous.prodMk_right x)
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x)]
  exact f_cont

Depends on / 依赖: Continuous, Continuous.prodMk_right, continuous_of_continuous_uncurry, f_cont, f_cont.comp, mkD_of_continuous, prodMk_right
-/
lemma continuous_mkD_of_uncurry
    (f : T -> X -> Y) (g : C(X, Y)) (f_cont : Continuous (Function.uncurry f)) :
    Continuous (fun x => mkD (f x) g) := by
  have (x : _) : Continuous (f x) := f_cont.comp (Continuous.prodMk_right x)
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x)]
  exact f_cont

open Set in
/--
lemma `continuousOn_mkD_of_uncurry` / 引理 `continuousOn_mkD_of_uncurry`

English:
lemma continuousOn_mkD_of_uncurry
  statement: {s : Set T}
  proof: by
  have (x) (hx : x in s) : Continuous (f x) := f_cont.comp_continuous
    (Continuous.prodMk_right x) fun _ => ⟨hx, trivial⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_id)
    fun xz => ⟨xz.1.2, trivial⟩

中文:
引理 continuousOn_mkD_of_uncurry
  结论: {s : 集合 T}
  证明: by
  have (x) (hx : x in s) : Continuous (f x) := f_cont.comp_continuous
    (Continuous.prodMk_right x) fun _ => ⟨hx, trivial⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_id)
    fun xz => ⟨xz.1.2, trivial⟩

Depends on / 依赖: Continuous, Continuous.prodMk_right, comp_continuous, continuousOn_iff_continuous_domRestrict, continuous_id, continuous_of_continuous_uncurry, continuous_subtype_val, domRestrict_def, f_cont, f_cont.comp_continuous, mkD_of_continuous, prodMap, prodMk_right, s.domRestrict_def, simp_rw
-/
lemma continuousOn_mkD_of_uncurry {s : Set T}
    (f : T -> X -> Y) (g : C(X, Y)) (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    ContinuousOn (fun x => mkD (f x) g) s := by
  have (x) (hx : x in s) : Continuous (f x) := f_cont.comp_continuous
    (Continuous.prodMk_right x) fun _ => ⟨hx, trivial⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_id)
    fun xz => ⟨xz.1.2, trivial⟩

open Set in
/--
lemma `continuous_mkD_restrict_of_uncurry` / 引理 `continuous_mkD_restrict_of_uncurry`

English:
lemma continuous_mkD_restrict_of_uncurry
  statement: {t : Set X}
  proof: by
  have (x : _) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨trivial, hz⟩
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x)]
  exact f_cont.comp_continuous (.prodMap continuous_id continuous_subtype_val)
    fun xz => ⟨trivial, xz.2.2⟩

中文:
引理 continuous_mkD_restrict_of_uncurry
  结论: {t : 集合 X}
  证明: by
  have (x : _) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨trivial, hz⟩
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x)]
  exact f_cont.comp_continuous (.prodMap continuous_id continuous_subtype_val)
    fun xz => ⟨trivial, xz.2.2⟩

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, comp_continuous, continuousOn, continuous_id, continuous_of_continuous_uncurry, continuous_subtype_val, f_cont, f_cont.comp, f_cont.comp_continuous, mkD_of_continuousOn, prodMap, prodMk_right
-/
lemma continuous_mkD_restrict_of_uncurry {t : Set X}
    (f : T -> X -> Y) (g : C(t, Y)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    Continuous (fun x => mkD (t.domRestrict (f x)) g) := by
  have (x : _) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨trivial, hz⟩
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x)]
  exact f_cont.comp_continuous (.prodMap continuous_id continuous_subtype_val)
    fun xz => ⟨trivial, xz.2.2⟩

open Set in
/--
lemma `continuousOn_mkD_restrict_of_uncurry` / 引理 `continuousOn_mkD_restrict_of_uncurry`

English:
lemma continuousOn_mkD_restrict_of_uncurry
  statement: {s : Set T} {t : Set X}
  proof: by
  have (x) (hx : x in s) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_subtype_val)
    fun xz => ⟨xz.1.2, xz.2.2⟩

中文:
引理 continuousOn_mkD_restrict_of_uncurry
  结论: {s : 集合 T} {t : 集合 X}
  证明: by
  have (x) (hx : x in s) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_subtype_val)
    fun xz => ⟨xz.1.2, xz.2.2⟩

Depends on / 依赖: Continuous, Continuous.prodMk_right, ContinuousOn, comp_continuous, continuousOn, continuousOn_iff_continuous_domRestrict, continuous_of_continuous_uncurry, continuous_subtype_val, domRestrict_def, f_cont, f_cont.comp, f_cont.comp_continuous, mkD_of_continuousOn, prodMap, prodMk_right, s.domRestrict_def, simp_rw
-/
lemma continuousOn_mkD_restrict_of_uncurry {s : Set T} {t : Set X}
    (f : T -> X -> Y) (g : C(t, Y))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    ContinuousOn (fun x => mkD (t.domRestrict (f x)) g) s := by
  have (x) (hx : x in s) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz => ⟨hx, hz⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_subtype_val)
    fun xz => ⟨xz.1.2, xz.2.2⟩

end mkD

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {X : Type*} {Y : Type*} {Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: [LocallyCompactSpace X] [LocallyCompactSpace Y]
  body: ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩

中文:
定义 curry
  签名: [局部紧空间 X] [局部紧空间 Y]
  定义体: ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.curry, continuous_curry, continuous_uncurry, uncurry
-/
def curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩

/--
Definition of `continuousMapOfUnique` / `continuousMapOfUnique` 的定义

English:
definition continuousMapOfUnique
  signature: [Unique X]
  body: const X
  invFun f := f default
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _

@[simp]

中文:
定义 continuousMapOfUnique
  签名: [唯一 X]
  定义体: const X
  invFun f := f default
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _

@[simp]
-/
def continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where
  toFun := const X
  invFun f := f default
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _

@[simp]
/--
theorem `continuousMapOfUnique_apply` / 定理 `continuousMapOfUnique_apply`

English:
theorem continuousMapOfUnique_apply
  given: [Unique X] (y : Y) (x : X)
  statement: continuousMapOfUnique y x = y
  proof: rfl

@[simp]

中文:
定理 continuousMapOfUnique_apply
  条件: [唯一 X] (y : Y) (x : X)
  结论: continuousMapOfUnique y x = y
  证明: rfl

@[simp]
-/
theorem continuousMapOfUnique_apply [Unique X] (y : Y) (x : X) : continuousMapOfUnique y x = y :=
  rfl

@[simp]
/--
theorem `continuousMapOfUnique_symm_apply` / 定理 `continuousMapOfUnique_symm_apply`

English:
theorem continuousMapOfUnique_symm_apply
  given: [Unique X] (f : C(X, Y))
  proof: rfl

中文:
定理 continuousMapOfUnique_symm_apply
  条件: [唯一 X] (f : C(X, Y))
  证明: rfl
-/
theorem continuousMapOfUnique_symm_apply [Unique X] (f : C(X, Y)) :
    continuousMapOfUnique.symm f = f default :=
  rfl

end Homeomorph

section IsQuotientMap

variable {X₀ X Y Z : Type*} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ -> X}

/--
theorem `Topology.IsQuotientMap.continuous_lift_prod_left` / 定理 `Topology.IsQuotientMap.continuous_lift_prod_left`

English:
theorem Topology.IsQuotientMap.continuous_lift_prod_left
  statement: (hf : IsQuotientMap f) {g : X × Y -> Z}
  proof: by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : forall x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X -> C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩

中文:
定理 拓扑.是商映射.continuous_lift_prod_left
  结论: (hf : 是商映射 f) {g : X × Y -> Z}
  证明: by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : forall x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X -> C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩

Depends on / 依赖: Continuous, ContinuousMap, ContinuousMap.continuous_uncurry_of_continuous, ContinuousMap.curry, Gf.continuous, continuous, continuous_iff, continuous_uncurry_of_continuous, hf.continuous_iff, hf.surjective, surjective
-/
theorem Topology.IsQuotientMap.continuous_lift_prod_left (hf : IsQuotientMap f) {g : X × Y -> Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : forall x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X -> C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩

/--
theorem `Topology.IsQuotientMap.continuous_lift_prod_right` / 定理 `Topology.IsQuotientMap.continuous_lift_prod_right`

English:
theorem Topology.IsQuotientMap.continuous_lift_prod_right
  statement: (hf : IsQuotientMap f) {g : Y × X -> Z}
  proof: by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap

中文:
定理 拓扑.是商映射.continuous_lift_prod_right
  结论: (hf : 是商映射 f) {g : Y × X -> Z}
  证明: by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap

Depends on / 依赖: Continuous, Prod.swap, continuous_lift_prod_left, continuous_swap, hf.continuous_lift_prod_left, hg.comp
-/
theorem Topology.IsQuotientMap.continuous_lift_prod_right (hf : IsQuotientMap f) {g : Y × X -> Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap

end IsQuotientMap
