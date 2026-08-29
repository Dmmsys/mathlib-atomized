/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

@[expose] public section

universe w' w u v

open CategoryTheory Limits MorphismProperty TopologicalSpace.Opens AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/--
A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.
-/
@[stacks 022B, mk_iff]
/--
Definition of `QuasiCompactCover` / `QuasiCompactCover` 的定义

English:
class QuasiCompactCover
  parameters: (𝒰 : PreZeroHypercover.{v} S)
  axioms and operations (1):
    - isCompactOpenCovered_of_isAffineOpen({U : S.Opens} (hU : IsAffineOpen U)) : IsCompactOpenCovered (𝒰.f ·) (U : Set S)

中文:
类 QuasiCompactCover
  参数: (𝒰 : PreZeroHypercover.{v} S)
  公理与运算 (1 个):
    - isCompactOpenCovered_of_isAffineOpen({U : S.Opens} (hU : 是仿射开集 U)) : IsCompactOpenCovered (𝒰.f ·) (U : 集合 S)
-/
class QuasiCompactCover (𝒰 : PreZeroHypercover.{v} S) : Prop where
  isCompactOpenCovered_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S)

variable (𝒰 : PreZeroHypercover.{v} S)

/--
lemma `IsAffineOpen.isCompactOpenCovered` / 引理 `IsAffineOpen.isCompactOpenCovered`

English:
lemma IsAffineOpen.isCompactOpenCovered
  given: [QuasiCompactCover 𝒰] {U : S.Opens} (hU : IsAffineOpen U)
  proof: QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen hU

中文:
引理 是仿射开集.isCompactOpenCovered
  条件: [QuasiCompactCover 𝒰] {U : S.Opens} (hU : 是仿射开集 U)
  证明: QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen hU

Depends on / 依赖: QuasiCompactCover, QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen, isCompactOpenCovered_of_isAffineOpen
-/
lemma IsAffineOpen.isCompactOpenCovered [QuasiCompactCover 𝒰] {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S) :=
  QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen hU

namespace QuasiCompactCover

/--
lemma `isCompactOpenCovered_of_isCompact` / 引理 `isCompactOpenCovered_of_isCompact`

English:
lemma isCompactOpenCovered_of_isCompact
  statement: [QuasiCompactCover 𝒰]
  proof: by
  obtain ⟨Us, hUs, hUf, hUc⟩ := S.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine .of_biUnion_eq_of_finite (SetLike.coe '' Us) (by simp_all) (hUf.image _) ?_
  simpa using fun t ht => IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

中文:
引理 isCompactOpenCovered_of_isCompact
  结论: [QuasiCompactCover 𝒰]
  证明: by
  obtain ⟨Us, hUs, hUf, hUc⟩ := S.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine .of_biUnion_eq_of_finite (SetLike.coe '' Us) (by simp_all) (hUf.image _) ?_
  simpa using fun t ht => IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

Depends on / 依赖: IsAffineOpen, IsAffineOpen.isCompactOpenCovered, S.isBasis_affineOpens.exists_finite_of_isCompact, SetLike, SetLike.coe, exists_finite_of_isCompact, hUf.image, isBasis_affineOpens, isCompactOpenCovered, of_biUnion_eq_of_finite
-/
lemma isCompactOpenCovered_of_isCompact [QuasiCompactCover 𝒰]
    {U : S.Opens} (hU : IsCompact (U : Set S)) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S) := by
  obtain ⟨Us, hUs, hUf, hUc⟩ := S.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine .of_biUnion_eq_of_finite (SetLike.coe '' Us) (by simp_all) (hUf.image _) ?_
  simpa using fun t ht => IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

variable {𝒰 : PreZeroHypercover.{v} S} {K : Precoverage Scheme.{u}}

variable (𝒰) in
/--
lemma `exists_isAffineOpen_of_isCompact` / 引理 `exists_isAffineOpen_of_isCompact`

English:
lemma exists_isAffineOpen_of_isCompact
  statement: [QuasiCompactCover 𝒰] {U : S.Opens}
  proof: by
  obtain ⟨n, a, V, ha, heq⟩ := (isCompactOpenCovered_of_isCompact 𝒰 hU).exists_mem_of_isBasis
    (fun i => (𝒰.X i).isBasis_affineOpens) (fun _ _ h => h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

中文:
引理 存在_isAffineOpen_of_isCompact
  结论: [QuasiCompactCover 𝒰] {U : S.Opens}
  证明: by
  obtain ⟨n, a, V, ha, heq⟩ := (isCompactOpenCovered_of_isCompact 𝒰 hU).exists_mem_of_isBasis
    (fun i => (𝒰.X i).isBasis_affineOpens) (fun _ _ h => h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

Depends on / 依赖: exists_mem_of_isBasis, h.isCompact, isBasis_affineOpens, isCompact, isCompactOpenCovered_of_isCompact
-/
lemma exists_isAffineOpen_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens}
    (hU : IsCompact (U : Set S)) :
    exists (n : Nat) (f : Fin n -> 𝒰.I₀) (V : forall i, (𝒰.X (f i)).Opens),
      (forall i, IsAffineOpen (V i)) ∧
      ⋃ i, 𝒰.f (f i) '' (V i) = U := by
  obtain ⟨n, a, V, ha, heq⟩ := (isCompactOpenCovered_of_isCompact 𝒰 hU).exists_mem_of_isBasis
    (fun i => (𝒰.X i).isBasis_affineOpens) (fun _ _ h => h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

/-- If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `K` is the fppf topology (i.e., flat and of finite presentation) and hence in
particular for étale and Zariski covers. -/
@[stacks 022C]
/--
lemma `of_isOpenMap` / 引理 `of_isOpenMap`

English:
lemma of_isOpenMap
  given: {𝒰 : S.Cover K} [Scheme.JointlySurjective K] (h : forall i, IsOpenMap (𝒰.f i))
  proof: .of_isOpenMap
    (fun i => (𝒰.f i).continuous) h (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

中文:
引理 of_isOpenMap
  条件: {𝒰 : S.Cover K} [概形.JointlySurjective K] (h : 对任意 i, 是开映射 (𝒰.f i))
  证明: .of_isOpenMap
    (fun i => (𝒰.f i).continuous) h (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

Depends on / 依赖: of_isOpenMap
-/
lemma of_isOpenMap {𝒰 : S.Cover K} [Scheme.JointlySurjective K] (h : forall i, IsOpenMap (𝒰.f i)) :
    QuasiCompactCover 𝒰.toPreZeroHypercover where
  isCompactOpenCovered_of_isAffineOpen {U} hU := .of_isOpenMap
    (fun i => (𝒰.f i).continuous) h (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

/-- Any open cover is quasi-compact. -/
instance (𝒰 : S.OpenCover) : QuasiCompactCover 𝒰.toPreZeroHypercover :=
  of_isOpenMap fun i => (𝒰.f i).isOpenEmbedding.isOpenMap

/-- If `𝒱` is a refinement of `𝒰` such that `𝒱` is quasicompact, also `𝒰` is quasicompact. -/
@[stacks 03L8]
/--
lemma `of_hom` / 引理 `of_hom`

English:
lemma of_hom
  given: {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱]
  proof: by
  refine ⟨fun {U} hU => ?_⟩
  exact .of_comp (a := f.s₀) (𝒱.f ·) (f.h₀ ·)
    (fun _ => Scheme.Hom.continuous _) (fun i => funext <| by simp [← Scheme.Hom.comp_apply])
    (fun _ => Scheme.Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

中文:
引理 of_hom
  条件: {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.态射 𝒰) [QuasiCompactCover 𝒱]
  证明: by
  refine ⟨fun {U} hU => ?_⟩
  exact .of_comp (a := f.s₀) (𝒱.f ·) (f.h₀ ·)
    (fun _ => Scheme.Hom.continuous _) (fun i => funext <| by simp [← Scheme.Hom.comp_apply])
    (fun _ => Scheme.Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, Scheme.Hom.continuous, comp_apply, continuous, hU.isCompactOpenCovered, isCompactOpenCovered, of_comp
-/
lemma of_hom {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱] :
    QuasiCompactCover 𝒰 := by
  refine ⟨fun {U} hU => ?_⟩
  exact .of_comp (a := f.s₀) (𝒱.f ·) (f.h₀ ·)
    (fun _ => Scheme.Hom.continuous _) (fun i => funext <| by simp [← Scheme.Hom.comp_apply])
    (fun _ => Scheme.Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (𝒰) in
@[stacks 022D "(3)"]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiCompactCover
  signature: 𝒰] {T
  body: by
  refine ⟨fun {U'} hU' => ?_⟩
  wlog h : exists (U : S.Opens), IsAffineOpen U ∧ f '' U' subseteq U generalizing U'
  · refine .of_isCompact_of_forall_exists_isCompactOpenCovered hU'.isCompact fun x hxU => ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens (mem_top (f x))
  

中文:
实例 [QuasiCompactCover
  签名: 𝒰] {T
  定义体: by
  refine ⟨fun {U'} hU' => ?_⟩
  wlog h : exists (U : S.Opens), IsAffineOpen U ∧ f '' U' subseteq U generalizing U'
  · refine .of_isCompact_of_forall_exists_isCompactOpenCovered hU'.isCompact fun x hxU => ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens (mem_top (f x))
  

Depends on / 依赖: IsAffineOpen, S.Opens, S.isBasis_affineOpens, T.isBasis_affineOpens, generalizing, inf_le_right, isBasis_affineOpens, isBasis_iff_nbhd, isBasis_iff_nbhd.mp, isCompact, le_trans, mem_top, of_isCompact_of_forall_exists_isCompactOpenCovered, subseteq
-/
instance [QuasiCompactCover 𝒰] {T : Scheme.{u}} (f : T ⟶ S) :
    QuasiCompactCover (𝒰.pullback₁ f) := by
  refine ⟨fun {U'} hU' => ?_⟩
  wlog h : exists (U : S.Opens), IsAffineOpen U ∧ f '' U' subseteq U generalizing U'
  · refine .of_isCompact_of_forall_exists_isCompactOpenCovered hU'.isCompact fun x hxU => ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens (mem_top (f x))
    obtain ⟨W', hW', hx', hle⟩ := isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x in f ⁻¹ᵁ W ⊓ U' from ⟨hx, hxU⟩)
    exact ⟨W', le_trans hle inf_le_right, by simpa [hx], W'.2,
      this hW' ⟨W, hW, by simpa using! le_trans hle inf_le_left⟩⟩
  obtain ⟨U, hU, hsub⟩ := h
  obtain ⟨s, hf, V, hc, (heq : _ = (U : Set S))⟩ := hU.isCompactOpenCovered 𝒰
  refine ⟨s, hf, fun i hi => pullback.fst f (𝒰.f i) ⁻¹ᵁ U' ⊓ pullback.snd f (𝒰.f i) ⁻¹ᵁ (V i hi),
      fun i hi => ?_, ?_⟩
· exact hU'.isCompact_pullback_inf (hc _ _) hU (by simpa using! hsub) by
      simpa [← SetLike.coe_subset_coe, ← heq, Set.range_comp] using! Set.subset_iUnion_of_subset i
        (Set.subset_iUnion_of_subset hi (Set.subset_preimage_image _ _))
  · refine subset_antisymm (by simp) (fun x hx => ?_)
    have : f x in (U : Set S) := hsub ⟨x, hx, rfl⟩
    simp_rw [← heq, Set.mem_iUnion] at this
    obtain ⟨i, hi, y, hy, heq⟩ := this
    simp_rw [Set.mem_iUnion]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback x y heq.symm
    exact ⟨i, hi, z, ⟨by simpa [hzl], by simpa [hzr]⟩, hzl⟩

variable (𝒰) in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [QuasiCompactCover
  signature: 𝒰] {T
  body: .of_hom (PreZeroHypercover.pullbackIso f 𝒰).hom

@[stacks 022D "(2)"]

中文:
实例 [QuasiCompactCover
  签名: 𝒰] {T
  定义体: .of_hom (PreZeroHypercover.pullbackIso f 𝒰).hom

@[stacks 022D "(2)"]

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.pullbackIso, of_hom, pullbackIso
-/
instance [QuasiCompactCover 𝒰] {T : Scheme.{u}} (f : T ⟶ S) :
    QuasiCompactCover (𝒰.pullback₂ f) :=
  .of_hom (PreZeroHypercover.pullbackIso f 𝒰).hom

@[stacks 022D "(2)"]
instance {X : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} X) [QuasiCompactCover 𝒰]
    (f : forall (x : 𝒰.I₀), PreZeroHypercover.{w} (𝒰.X x)) [forall x, QuasiCompactCover (f x)] :
    QuasiCompactCover (𝒰.bind f) where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    obtain ⟨s, hs, V, hcV, hU⟩ := hU.isCompactOpenCovered 𝒰
    have (i) (hi) : IsCompactOpenCovered ((f i).f ·) (V i hi) :=
      isCompactOpenCovered_of_isCompact (f i) (hcV i hi)
    choose t ht W hcW hV using this
    have : Finite s := hs
    have (i) (hi) : Finite (t i hi) := ht i hi
    refine .of_finite (κ := Σ (i : s), t i.1 i.2) (fun p => ⟨p.1, p.2⟩) (fun p => W _ p.1.2 _ p.2.2)
      (fun p => hcW ..) ?_
    simpa [← hV, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion, Set.image_image] using! hU

/--
Instance `of_finite` / 实例 `of_finite`

English:
instance of_finite
  signature: {𝒰 : S.Cover K} [Scheme.JointlySurjective K]
  body: by
    refine .of_finite_of_isSpectralMap (fun i => (𝒰.f i).isSpectralMap) ?_ U.2 hU.isCompact
    exact (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩)

中文:
实例 of_finite
  签名: {𝒰 : S.Cover K} [概形.JointlySurjective K]
  定义体: by
    refine .of_finite_of_isSpectralMap (fun i => (𝒰.f i).isSpectralMap) ?_ U.2 hU.isCompact
    exact (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩)

Depends on / 依赖: covers, hU.isCompact, isCompact, isSpectralMap, of_finite_of_isSpectralMap
-/
instance of_finite {𝒰 : S.Cover K} [Scheme.JointlySurjective K]
    [forall i, AlgebraicGeometry.QuasiCompact (𝒰.f i)] [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.toPreZeroHypercover where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    refine .of_finite_of_isSpectralMap (fun i => (𝒰.f i).isSpectralMap) ?_ U.2 hU.isCompact
    exact (fun x _ => ⟨𝒰.idx x, 𝒰.covers x⟩)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffine
  signature: S] {P
  body: haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

中文:
实例 [是仿射
  签名: S] {P
  定义体: haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

Depends on / 依赖: Finite, cover.I, of_finite
-/
instance [IsAffine S] {P : MorphismProperty Scheme.{u}} (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: S] : QuasiCompactCover 𝒰 where
  body: by
    convert! IsCompactOpenCovered.empty
    simp [eq_bot_iff]

中文:
实例 [是空
  签名: S] : QuasiCompactCover 𝒰 where
  定义体: by
    convert! IsCompactOpenCovered.empty
    simp [eq_bot_iff]

Depends on / 依赖: IsCompactOpenCovered, IsCompactOpenCovered.empty, convert, eq_bot_iff
-/
instance [IsEmpty S] : QuasiCompactCover 𝒰 where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    convert! IsCompactOpenCovered.empty
    simp [eq_bot_iff]

variable {P : MorphismProperty Scheme.{u}}

/--
Instance `homCover` / 实例 `homCover`

English:
instance homCover
  signature: {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f]
  body: have _ (i) : AlgebraicGeometry.QuasiCompact ((f.cover hf).f i) := ‹_›
  .of_finite

中文:
实例 homCover
  签名: {X S : 概形.{u}} (f : X ⟶ S) (hf : P f) [满射 f]
  定义体: have _ (i) : AlgebraicGeometry.QuasiCompact ((f.cover hf).f i) := ‹_›
  .of_finite

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.QuasiCompact, QuasiCompact, f.cover, of_finite
-/
instance homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] : QuasiCompactCover (f.cover hf).toPreZeroHypercover :=
  have _ (i) : AlgebraicGeometry.QuasiCompact ((f.cover hf).f i) := ‹_›
  .of_finite

/--
Instance `singleton` / 实例 `singleton`

English:
instance singleton
  signature: {X : Scheme.{u}} (f : X ⟶ S) [Surjective f]
  body: homCover (P := ⊤) f trivial

@[stacks 022D "(1)"]

中文:
实例 singleton
  签名: {X : 概形.{u}} (f : X ⟶ S) [满射 f]
  定义体: homCover (P := ⊤) f trivial

@[stacks 022D "(1)"]

Depends on / 依赖: homCover
-/
instance singleton {X : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] :
    QuasiCompactCover (.singleton f) :=
  homCover (P := ⊤) f trivial

@[stacks 022D "(1)"]
instance {P : MorphismProperty Scheme.{u}} [P.ContainsIdentities] [P.RespectsIso]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] :
    QuasiCompactCover (Scheme.coverOfIsIso (P := P) f).toPreZeroHypercover :=
  of_isOpenMap (fun _ => f.homeomorph.isOpenMap)

instance {𝒱 : PreZeroHypercover S} [QuasiCompactCover 𝒰] : QuasiCompactCover (𝒰.sum 𝒱) :=
  .of_hom (PreZeroHypercover.sumInl _ _)

instance {𝒱 : PreZeroHypercover S} [QuasiCompactCover 𝒱] : QuasiCompactCover (𝒰.sum 𝒱) :=
  .of_hom (PreZeroHypercover.sumInr _ _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_hom` / 引理 `exists_hom`

English:
lemma exists_hom
  statement: {S : Scheme.{u}} (𝒰 : S.Cover (Scheme.precoverage P))
  proof: by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : TopologicalSpace.Opens S).carrier from isCompact_univ)
  simp only [coe_top, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_iUnion,
    Set.mem_image, SetLike.mem_coe, forall

中文:
引理 存在_hom
  结论: {S : 概形.{u}} (𝒰 : S.Cover (概形.precoverage P))
  证明: by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : TopologicalSpace.Opens S).carrier from isCompact_univ)
  simp only [coe_top, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_iUnion,
    Set.mem_image, SetLike.mem_coe, forall

Depends on / 依赖: IsCompact, QuasiCompactCover, QuasiCompactCover.exists_isAffineOpen_of_isCompact, Set.mem_iUnion, Set.mem_image, Set.mem_univ, Set.subset_def, Set.univ_subset_iff, SetLike, SetLike.mem_coe, TopologicalSpace, TopologicalSpace.Opens, carrier, coe_top, covers, exists_isAffineOpen_of_isCompact, forall_const, fromSpec, i.down, isCompact_univ
-/
lemma exists_hom {S : Scheme.{u}} (𝒰 : S.Cover (Scheme.precoverage P))
    [P.RespectsLeft @IsOpenImmersion] [CompactSpace S] [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    exists (𝒱 : Scheme.AffineCover.{w} P S) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ forall j, IsOpenImmersion (f.h₀ j) := by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : TopologicalSpace.Opens S).carrier from isCompact_univ)
  simp only [coe_top, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_iUnion,
    Set.mem_image, SetLike.mem_coe, forall_const] at h
  choose idx x hmem hx using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { I₀ := ULift (Fin n)
        X i := Γ(_, V i.down)
        f i := (hV _).fromSpec ≫ 𝒰.f (f _)
        idx s := ⟨idx s⟩
        covers s := by
          use (hV _).isoSpec.hom.base ⟨x s, hmem s⟩
          rw [← Scheme.Hom.comp_apply]; rw [← IsAffineOpen.isoSpec_inv_ι]; rw [Category.assoc]; rw [Iso.hom_inv_id_assoc]
          simp [hx]
        map_prop i :=
          RespectsLeft.precomp (Q := IsOpenImmersion) _ inferInstance _ (𝒰.map_prop _) }
  · exact
      { s₀ i := f i.down
        h₀ i := (hV i.down).fromSpec }
  · infer_instance
  · infer_instance

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} S) [QuasiCompactCover 𝒰]
  body: 𝒰.restrictIndex
      fun i : (Σ U : S.affineOpens, Fin (exists_isAffineOpen_of_isCompact 𝒰 U.2.isCompact).choose) =>
    (exists_isAffineOpen_of_isCompact 𝒰 i.1.2.isCompact).choose_spec.choose i.2

中文:
定义 ulift
  签名: {S : 概形.{u}} (𝒰 : PreZeroHypercover.{w} S) [QuasiCompactCover 𝒰]
  定义体: 𝒰.restrictIndex
      fun i : (Σ U : S.affineOpens, Fin (exists_isAffineOpen_of_isCompact 𝒰 U.2.isCompact).choose) =>
    (exists_isAffineOpen_of_isCompact 𝒰 i.1.2.isCompact).choose_spec.choose i.2

Depends on / 依赖: S.affineOpens, affineOpens, choose_spec, choose_spec.choose, exists_isAffineOpen_of_isCompact, isCompact, restrictIndex
-/
noncomputable def ulift {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} S) [QuasiCompactCover 𝒰] :
    PreZeroHypercover.{u} S :=
  𝒰.restrictIndex
      fun i : (Σ U : S.affineOpens, Fin (exists_isAffineOpen_of_isCompact 𝒰 U.2.isCompact).choose) =>
    (exists_isAffineOpen_of_isCompact 𝒰 i.1.2.isCompact).choose_spec.choose i.2

/--
Definition of `uliftHom` / `uliftHom` 的定义

English:
definition uliftHom
  signature: {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰]
  body: 𝒰.restrictIndexHom _

中文:
定义 uliftHom
  签名: {S : 概形.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰]
  定义体: 𝒰.restrictIndexHom _

Depends on / 依赖: restrictIndexHom
-/
noncomputable def uliftHom {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    (ulift 𝒰).Hom 𝒰 :=
  𝒰.restrictIndexHom _

instance {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    QuasiCompactCover (ulift 𝒰) where
  isCompactOpenCovered_of_isAffineOpen {U} hU :=
    let H := exists_isAffineOpen_of_isCompact 𝒰 hU.isCompact
    .of_finite (fun i : Fin H.choose => ⟨⟨U, hU⟩, i⟩)
      (fun _ => H.choose_spec.choose_spec.choose _)
      (fun _ => H.choose_spec.choose_spec.choose_spec.left _ |>.isCompact)
      H.choose_spec.choose_spec.choose_spec.right

end QuasiCompactCover

namespace Scheme

/--
Definition of `quasiCompactCover` / `quasiCompactCover` 的定义

English:
definition quasiCompactCover
  signature: (S : Scheme.{u})
  body: QuasiCompactCover

@[simp]

中文:
定义 quasiCompactCover
  签名: (S : 概形.{u})
  定义体: QuasiCompactCover

@[simp]

Depends on / 依赖: AddCommGroup, AddCommGrpCat, AddCommGrpCat.uliftFunctor, QuasiCompactCover, X.ellAdicSheaf, ellAdicSheaf, sheafCompose, uliftFunctor
-/
def quasiCompactCover (S : Scheme.{u}) : ObjectProperty (PreZeroHypercover.{v} S) :=
  QuasiCompactCover

@[simp]
/--
lemma `quasiCompactCover_iff` / 引理 `quasiCompactCover_iff`

English:
lemma quasiCompactCover_iff
  given: (S : Scheme.{u}) (𝒰 : PreZeroHypercover.{v} S)
  proof: .rfl

中文:
引理 quasiCompactCover_iff
  条件: (S : 概形.{u}) (𝒰 : PreZeroHypercover.{v} S)
  证明: .rfl
-/
lemma quasiCompactCover_iff (S : Scheme.{u}) (𝒰 : PreZeroHypercover.{v} S) :
    S.quasiCompactCover 𝒰 ↔ QuasiCompactCover 𝒰 := .rfl

/--
Instance `isClosedUnderIsomorphisms_quasiCompactCover` / 实例 `isClosedUnderIsomorphisms_quasiCompactCover`

English:
instance isClosedUnderIsomorphisms_quasiCompactCover
  signature: (S : Scheme.{u})
  body: .of_hom e.hom

中文:
实例 isClosedUnderIsomorphisms_quasiCompactCover
  签名: (S : 概形.{u})
  定义体: .of_hom e.hom

Depends on / 依赖: e.hom, of_hom
-/
instance isClosedUnderIsomorphisms_quasiCompactCover (S : Scheme.{u}) :
    S.quasiCompactCover.IsClosedUnderIsomorphisms where
  of_iso {𝒰 _} e (_ : QuasiCompactCover 𝒰) := .of_hom e.hom

end Scheme

end AlgebraicGeometry
