/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The compact-open topology on continuous monoid morphisms.
-/

@[expose] public section

open Function Topology
open scoped Pointwise

variable (F A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [IsTopologicalGroup E]

namespace ContinuousMonoidHom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (ContinuousMonoidHom A B)
  body: TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

@[to_additive]

中文:
实例 :
  签名: 拓扑空间 (余ntinuous幺半群态射 A B)
  定义体: TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

@[to_additive]

Depends on / 依赖: ContinuousMap, ContinuousMap.compactOpen, TopologicalSpace, TopologicalSpace.induced, compactOpen, induced, toContinuousMap
-/
instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

@[to_additive]
/--
theorem `isInducing_toContinuousMap` / 定理 `isInducing_toContinuousMap`

English:
theorem isInducing_toContinuousMap
  proof: ⟨rfl⟩

@[to_additive]

中文:
定理 isInducing_toContinuousMap
  证明: ⟨rfl⟩

@[to_additive]
-/
theorem isInducing_toContinuousMap :
    IsInducing (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) := ⟨rfl⟩

@[to_additive]
/--
theorem `isEmbedding_toContinuousMap` / 定理 `isEmbedding_toContinuousMap`

English:
theorem isEmbedding_toContinuousMap
  proof: ⟨isInducing_toContinuousMap A B, toContinuousMap_injective⟩

@[to_additive]

中文:
定理 isEmbedding_toContinuousMap
  证明: ⟨isInducing_toContinuousMap A B, toContinuousMap_injective⟩

@[to_additive]

Depends on / 依赖: isInducing_toContinuousMap, toContinuousMap_injective
-/
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) :=
  ⟨isInducing_toContinuousMap A B, toContinuousMap_injective⟩

@[to_additive]
/--
Instance `instContinuousEvalConst` / 实例 `instContinuousEvalConst`

English:
instance instContinuousEvalConst
  signature: : ContinuousEvalConst (ContinuousMonoidHom A B) A B
  body: .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]

中文:
实例 instContinuousEvalConst
  签名: : 余ntinuousEvalConst (余ntinuous幺半群态射 A B) A B
  定义体: .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]

Depends on / 依赖: continuous, isInducing_toContinuousMap, of_continuous_forget
-/
instance instContinuousEvalConst : ContinuousEvalConst (ContinuousMonoidHom A B) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
/--
Instance `instContinuousEval` / 实例 `instContinuousEval`

English:
instance instContinuousEval
  signature: [LocallyCompactPair A B]
  body: .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]

中文:
实例 instContinuousEval
  签名: [LocallyCompactPair A B]
  定义体: .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]

Depends on / 依赖: continuous, isInducing_toContinuousMap, of_continuous_forget
-/
instance instContinuousEval [LocallyCompactPair A B] :
    ContinuousEval (ContinuousMonoidHom A B) A B :=
  .of_continuous_forget (isInducing_toContinuousMap A B).continuous

@[to_additive]
/--
lemma `range_toContinuousMap` / 引理 `range_toContinuousMap`

English:
lemma range_toContinuousMap
  proof: by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f => ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]

中文:
引理 range_toContinuousMap
  证明: by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f => ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]

Depends on / 依赖: Set.Subset.antisymm, Set.range_subset_iff, Subset, antisymm, map_mul, map_one, range_subset_iff
-/
lemma range_toContinuousMap :
    Set.range (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) =
      {f : C(A, B) | f 1 = 1 ∧ forall x y, f (x * y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f => ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]
/--
theorem `isClosedEmbedding_toContinuousMap` / 定理 `isClosedEmbedding_toContinuousMap`

English:
theorem isClosedEmbedding_toContinuousMap
  given: [ContinuousMul B] [T2Space B]
  proof: isEmbedding_toContinuousMap A B
  isClosed_range := by
    simp only [range_toContinuousMap, Set.ofPred_and, Set.ofPred_forall]
refine .inter (isClosed_singleton.preimage (continuous_eval_const 1))
      isClosed_iInter fun x => isClosed_iInter fun y => ?_
exact isClosed_eq (continuous_eval_const (x * y))
      .mul (continuous_eval_const x) (continuous_eval_const y)

中文:
定理 isClosedEmbedding_toContinuousMap
  条件: [连续乘法 B] [T2空间 B]
  证明: isEmbedding_toContinuousMap A B
  isClosed_range := by
    simp only [range_toContinuousMap, Set.ofPred_and, Set.ofPred_forall]
refine .inter (isClosed_singleton.preimage (continuous_eval_const 1))
      isClosed_iInter fun x => isClosed_iInter fun y => ?_
exact isClosed_eq (continuous_eval_const (x * y))
      .mul (continuous_eval_const x) (continuous_eval_const y)

Depends on / 依赖: isEmbedding_toContinuousMap
-/
theorem isClosedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    IsClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B -> C(A, B)) where
  toIsEmbedding := isEmbedding_toContinuousMap A B
  isClosed_range := by
    simp only [range_toContinuousMap, Set.ofPred_and, Set.ofPred_forall]
refine .inter (isClosed_singleton.preimage (continuous_eval_const 1))
      isClosed_iInter fun x => isClosed_iInter fun y => ?_
exact isClosed_eq (continuous_eval_const (x * y))
      .mul (continuous_eval_const x) (continuous_eval_const y)

variable {A B C D E}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: B] : T2Space (ContinuousMonoidHom A B)
  body: (isEmbedding_toContinuousMap A B).t2Space

@[to_additive]

中文:
实例 [T2空间
  签名: B] : T2空间 (余ntinuous幺半群态射 A B)
  定义体: (isEmbedding_toContinuousMap A B).t2Space

@[to_additive]

Depends on / 依赖: isEmbedding_toContinuousMap, t2Space
-/
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (isEmbedding_toContinuousMap A B).t2Space

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalGroup (ContinuousMonoidHom A E)
  body: let hi := isInducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prodMap hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]

中文:
实例 :
  签名: 是拓扑群 (余ntinuous幺半群态射 A E)
  定义体: let hi := isInducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prodMap hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]

Depends on / 依赖: Continuous, Continuous.prodMap, continuous, continuous_iff, continuous_inv, continuous_inv.comp, continuous_mul, continuous_mul.comp, hi.continuous, hi.continuous_iff.mpr, isInducing_toContinuousMap, prodMap
-/
instance : IsTopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := isInducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prodMap hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
/--
theorem `continuous_of_continuous_uncurry` / 定理 `continuous_of_continuous_uncurry`

English:
theorem continuous_of_continuous_uncurry
  statement: {A : Type*} [TopologicalSpace A]
  proof: (isInducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]

中文:
定理 continuous_of_continuous_uncurry
  结论: {A : 类型} [拓扑空间 A]
  证明: (isInducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_of_continuous_uncurry, continuous_iff, continuous_iff.mpr, continuous_of_continuous_uncurry, isInducing_toContinuousMap
-/
theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A -> ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (isInducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)

@[to_additive]
/--
theorem `continuous_comp` / 定理 `continuous_comp`

English:
theorem continuous_comp
  given: [LocallyCompactSpace B]
  proof: (isInducing_toContinuousMap A C).continuous_iff.2
    ContinuousMap.continuous_comp'.comp
      ((isInducing_toContinuousMap A B).prodMap (isInducing_toContinuousMap B C)).continuous

@[to_additive]

中文:
定理 continuous_comp
  条件: [局部紧空间 B]
  证明: (isInducing_toContinuousMap A C).continuous_iff.2
    ContinuousMap.continuous_comp'.comp
      ((isInducing_toContinuousMap A B).prodMap (isInducing_toContinuousMap B C)).continuous

@[to_additive]

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_comp, continuous, continuous_comp, continuous_iff, isInducing_toContinuousMap, prodMap
-/
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
(isInducing_toContinuousMap A C).continuous_iff.2
    ContinuousMap.continuous_comp'.comp
      ((isInducing_toContinuousMap A B).prodMap (isInducing_toContinuousMap B C)).continuous

@[to_additive]
/--
theorem `continuous_comp_left` / 定理 `continuous_comp_left`

English:
theorem continuous_comp_left
  given: (f : ContinuousMonoidHom A B)
  proof: (isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_precomp.comp (isInducing_toContinuousMap B C).continuous

@[to_additive]

中文:
定理 continuous_comp_left
  条件: (f : 余ntinuous幺半群态射 A B)
  证明: (isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_precomp.comp (isInducing_toContinuousMap B C).continuous

@[to_additive]

Depends on / 依赖: continuous, continuous_iff, continuous_precomp, f.toContinuousMap.continuous_precomp.comp, isInducing_toContinuousMap, toContinuousMap
-/
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
(isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_precomp.comp (isInducing_toContinuousMap B C).continuous

@[to_additive]
/--
theorem `continuous_comp_right` / 定理 `continuous_comp_right`

English:
theorem continuous_comp_right
  given: (f : ContinuousMonoidHom B C)
  proof: (isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_postcomp.comp (isInducing_toContinuousMap A B).continuous

中文:
定理 continuous_comp_right
  条件: (f : 余ntinuous幺半群态射 B C)
  证明: (isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_postcomp.comp (isInducing_toContinuousMap A B).continuous

Depends on / 依赖: continuous, continuous_iff, continuous_postcomp, f.toContinuousMap.continuous_postcomp.comp, isInducing_toContinuousMap, toContinuousMap
-/
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
(isInducing_toContinuousMap A C).continuous_iff.2
    f.toContinuousMap.continuous_postcomp.comp (isInducing_toContinuousMap A B).continuous

variable (E) in
/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive /-- `ContinuousAddMonoidHom _ f` is a functor. -/]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (f : ContinuousMonoidHom A B)
  body: g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

中文:
定义 compLeft
  签名: (f : 余ntinuous幺半群态射 A B)
  定义体: g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

Depends on / 依赖: g.comp
-/
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left

variable (A) in
/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive /-- `ContinuousAddMonoidHom f _` is a functor. -/]
/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
  body: f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

中文:
定义 compRight
  签名: {B : 类型} [交换群 B] [拓扑空间 B] [是拓扑群 B]
  定义体: f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

Depends on / 依赖: f.comp
-/
def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right

section DiscreteTopology
variable [DiscreteTopology A] [ContinuousMul B] [T2Space B]

@[to_additive]
/--
lemma `isClosedEmbedding_coe` / 引理 `isClosedEmbedding_coe`

English:
lemma isClosedEmbedding_coe
  statement: IsClosedEmbedding ((⇑) : (A ->ₜ* B) -> A -> B)
  proof: ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp isClosedEmbedding_toContinuousMap ..

@[to_additive]

中文:
引理 isClosedEmbedding_coe
  结论: 是闭嵌入 ((⇑) : (A ->ₜ* B) -> A -> B)
  证明: ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp isClosedEmbedding_toContinuousMap ..

@[to_additive]

Depends on / 依赖: ContinuousMap, ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp, isClosedEmbedding, isClosedEmbedding_toContinuousMap, isHomeomorph_coe
-/
lemma isClosedEmbedding_coe : IsClosedEmbedding ((⇑) : (A ->ₜ* B) -> A -> B) :=
ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp isClosedEmbedding_toContinuousMap ..

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: B] : CompactSpace (A ->ₜ* B)
  body: ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

中文:
实例 [紧空间
  签名: B] : 紧空间 (A ->ₜ* B)
  定义体: ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace, compactSpace, isClosedEmbedding_coe
-/
instance [CompactSpace B] : CompactSpace (A ->ₜ* B) :=
  ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

end DiscreteTopology

section LocallyCompact

variable {X Y : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
  [UniformSpace Y] [CommGroup Y] [IsUniformGroup Y] [T0Space Y] [CompactSpace Y]

@[to_additive]
/--
theorem `locallyCompactSpace_of_equicontinuousAt` / 定理 `locallyCompactSpace_of_equicontinuousAt`

English:
theorem locallyCompactSpace_of_equicontinuousAt
  statement: (U : Set X) (V : Set Y)
  proof: by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  obtain ⟨W, hWo, hWV, hWc⟩ := local_compact_nhds hV
  let S1 : Set (X ->* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X -> Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 -> X -> Y) :=
    h.comp (Subtype.map _root_.id fun f hf => hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 -> X -> Y) := by
    rw [equicontinuous_iff_range]; rw [← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ => W) inter Set.range ((↑) : (X ->* Y) -> (X -> Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f => ⟨fun ⟨g, hg, hf⟩ => hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ => ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ => hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  have hS2 : (interior S2).Nonempty := by
    let T : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U (interior W)}
    have h1 : T.Nonempty := ⟨1, fun _ _ => mem_interior_iff_mem_nhds.mpr hWo⟩
    have h2 : T subseteq S2 := fun f hf => hf.mono_right interior_subset
    have h3 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hU isOpen_interior)
    exact h1.mono (interior_maximal h2 h3)
  exact TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    ⟨⟨S2, (isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)⟩, hS2⟩

中文:
定理 locallyCompactSpace_of_equicontinuousAt
  结论: (U : 集合 X) (V : 集合 Y)
  证明: by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  obtain ⟨W, hWo, hWV, hWc⟩ := local_compact_nhds hV
  let S1 : Set (X ->* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X -> Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 -> X -> Y) :=
    h.comp (Subtype.map _root_.id fun f hf => hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 -> X -> Y) := by
    rw [equicontinuous_iff_range]; rw [← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ => W) inter Set.range ((↑) : (X ->* Y) -> (X -> Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f => ⟨fun ⟨g, hg, hf⟩ => hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ => ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ => hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  have hS2 : (interior S2).Nonempty := by
    let T : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U (interior W)}
    have h1 : T.Nonempty := ⟨1, fun _ _ => mem_interior_iff_mem_nhds.mpr hWo⟩
    have h2 : T subseteq S2 := fun f hf => hf.mono_right interior_subset
    have h3 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hU isOpen_interior)
    exact h1.mono (interior_maximal h2 h3)
  exact TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    ⟨⟨S2, (isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)⟩, hS2⟩

Depends on / 依赖: ContinuousMonoidHom, Equicontinuous, MapsTo, Set.MapsTo, Subtype, Subtype.map, _root_, _root_.id, equicontinuous_of_equicontinuousAt_one, h.comp, hf.mono_right, local_compact_nhds, mono_right, replace
-/
theorem locallyCompactSpace_of_equicontinuousAt (U : Set X) (V : Set Y)
    (hU : IsCompact U) (hV : V in nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X ->* Y | Set.MapsTo f U V} => (f : X -> Y)) 1) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  obtain ⟨W, hWo, hWV, hWc⟩ := local_compact_nhds hV
  let S1 : Set (X ->* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X -> Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 -> X -> Y) :=
    h.comp (Subtype.map _root_.id fun f hf => hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 -> X -> Y) := by
    rw [equicontinuous_iff_range]; rw [← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ => W) inter Set.range ((↑) : (X ->* Y) -> (X -> Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f => ⟨fun ⟨g, hg, hf⟩ => hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ => ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ => hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  have hS2 : (interior S2).Nonempty := by
    let T : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U (interior W)}
    have h1 : T.Nonempty := ⟨1, fun _ _ => mem_interior_iff_mem_nhds.mpr hWo⟩
    have h2 : T subseteq S2 := fun f hf => hf.mono_right interior_subset
    have h3 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hU isOpen_interior)
    exact h1.mono (interior_maximal h2 h3)
  exact TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
    ⟨⟨S2, (isInducing_toContinuousMap X Y).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)⟩, hS2⟩

variable [LocallyCompactSpace X]

@[to_additive]
/--
theorem `locallyCompactSpace_of_hasBasis` / 定理 `locallyCompactSpace_of_hasBasis`

English:
theorem locallyCompactSpace_of_hasBasis
  statement: (V : Nat -> Set Y)
  proof: by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : Nat -> {S : Set X | S in nhds 1} :=
Nat.rec ⟨U0, hU0o⟩ fun _ S => let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : Nat -> Set X := fun n => (U_aux n).1
  have hU1 : forall n, U n in nhds 1 := fun n => (U_aux n).2
  have hU2 : forall n, U (n + 1) * U (n + 1) subseteq U n :=
    fun n => (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : forall n, U (n + 1) subseteq U n :=
    fun n x hx => hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : forall f : X ->* Y, Set.MapsTo f (U 0) (V 0) -> forall n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx => hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  apply locallyCompactSpace_of_equicontinuousAt (U 0) (V 0) hU0c (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ => Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ => ?_⟩
  rw [Set.mem_ofPred_eq]; rw [map_one]; rw [div_one]
  exact hU4 f hf n hx

中文:
定理 locallyCompactSpace_of_hasBasis
  结论: (V : 自然数 -> 集合 Y)
  证明: by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : Nat -> {S : Set X | S in nhds 1} :=
Nat.rec ⟨U0, hU0o⟩ fun _ S => let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : Nat -> Set X := fun n => (U_aux n).1
  have hU1 : forall n, U n in nhds 1 := fun n => (U_aux n).2
  have hU2 : forall n, U (n + 1) * U (n + 1) subseteq U n :=
    fun n => (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : forall n, U (n + 1) subseteq U n :=
    fun n x hx => hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : forall f : X ->* Y, Set.MapsTo f (U 0) (V 0) -> forall n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx => hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  apply locallyCompactSpace_of_equicontinuousAt (U 0) (V 0) hU0c (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ => Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ => ?_⟩
  rw [Set.mem_ofPred_eq]; rw [map_one]; rw [div_one]
  exact hU4 f hf n hx

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Nat.rec, U_aux, choose_spec, exists_closed_nhds_one_inv_eq_mul_subset, exists_compact_mem_nhds, subseteq
-/
theorem locallyCompactSpace_of_hasBasis (V : Nat -> Set Y)
    (hV : forall {n x}, x in V n -> x * x in V n -> x in V (n + 1))
    (hVo : Filter.HasBasis (nhds 1) (fun _ => True) V) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : Nat -> {S : Set X | S in nhds 1} :=
Nat.rec ⟨U0, hU0o⟩ fun _ S => let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : Nat -> Set X := fun n => (U_aux n).1
  have hU1 : forall n, U n in nhds 1 := fun n => (U_aux n).2
  have hU2 : forall n, U (n + 1) * U (n + 1) subseteq U n :=
    fun n => (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : forall n, U (n + 1) subseteq U n :=
    fun n x hx => hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : forall f : X ->* Y, Set.MapsTo f (U 0) (V 0) -> forall n, Set.MapsTo f (U n) (V n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx => hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  apply locallyCompactSpace_of_equicontinuousAt (U 0) (V 0) hU0c (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine fun n _ => Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ => ?_⟩
  rw [Set.mem_ofPred_eq]; rw [map_one]; rw [div_one]
  exact hU4 f hf n hx

end LocallyCompact

end ContinuousMonoidHom
