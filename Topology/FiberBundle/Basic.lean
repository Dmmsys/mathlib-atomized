/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Fiber bundles

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type `Bundle.TotalSpace F E` where
`E : B → Type*` is a function associating to `x : B` the fiber over `x`. This type
`Bundle.TotalSpace F E` is a type of pairs `⟨proj : B, snd : E proj⟩`.

To have a fiber bundle structure on `Bundle.TotalSpace F E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `Bundle.TotalSpace F E`, for which the projection to `B` is
  a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
  from `E x` to `Bundle.TotalSpace F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `FiberBundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`FiberBundleCore` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `FiberPrebundle` which allows to define a topological
fiber bundle from trivializations given as partial equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `FiberBundle F E` : Structure saying that `E : B → Type*` is a fiber bundle with fiber `F`.

### Construction of a bundle from trivializations

* `Bundle.TotalSpace F E` is the type of pairs `(proj : B, snd : E proj)`. We can use the extra
  argument `F` to construct topology on the total space.
* `FiberBundleCore ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : FiberBundleCore ι B F`. Then we define

* `Z.Fiber x` : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.TotalSpace` : the total space of `Z`, defined as `Bundle.TotalSpace F Z.Fiber` with a custom
                    topology.
* `Z.proj` : projection from `Z.TotalSpace` to `B`. It is continuous.
* `Z.localTriv i` : for `i : ι`, bundle trivialization above the set `Z.baseSet i`, which is an
                    open set in `B`.

* `FiberPrebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are open partial homeomorphisms.
* `FiberPrebundle.totalSpaceTopology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

### Data vs mixins

For both fiber and vector bundles, one faces a choice: should the definition state the *existence*
of local trivializations (a propositional typeclass), or specify a fixed atlas of trivializations (a
typeclass containing data)?

In their initial mathlib implementations, both fiber and vector bundles were defined
propositionally. For vector bundles, this turns out to be mathematically wrong: in infinite
dimension, the transition function between two trivializations is not automatically continuous as a
map from the base `B` to the endomorphisms `F →L[R] F` of the fiber (considered with the
operator-norm topology), and so the definition needs to be modified by restricting consideration to
a family of trivializations (constituting the data) which are all mutually-compatible in this sense.
The PRs https://github.com/leanprover-community/mathlib/pull/13052 and
https://github.com/leanprover-community/mathlib/pull/13175 implemented this change.

There is still the choice about whether to hold this data at the level of fiber bundles or of vector
bundles. As of PR https://github.com/leanprover-community/mathlib/pull/17505, the data is all held
in `FiberBundle`, with `VectorBundle` a (propositional) mixin stating fiberwise-linearity.

This allows bundles to carry instances of typeclasses in which the scalar field, `R`, does not
appear as a parameter. Notably, we would like a vector bundle over `R` with fiber `F` over base `B`
to be a `ChartedSpace (B × F)`, with the trivializations providing the charts. This would be a
dangerous instance for typeclass inference, because `R` does not appear as a parameter in
`ChartedSpace (B × F)`. But if the data of the trivializations is held in `FiberBundle`, then a
fiber bundle with fiber `F` over base `B` can be a `ChartedSpace (B × F)`, and this is safe for
typeclass inference.

We expect that this choice of definition will also streamline constructions of fiber bundles with
similar underlying structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

A fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`FiberBundleCore`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
  structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
  (from `F` to `F`) and the manifold derivative (from `TangentSpace I x` to `TangentSpace I' (f x)`)
  are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean cannot check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`TangentSpace I x`. One could fear issues as this composition goes from `TangentSpace I x` to
`TangentSpace I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `FiberBundleCore`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `FiberBundleCore`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is
`Bundle.TotalSpace F (fun b : B ↦ F)`, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `FiberBundleCore`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, structure group
-/

@[expose] public section


variable {ι B F X : Type*} [TopologicalSpace X]

open TopologicalSpace Filter Set Bundle Topology

/-! ### General definition of fiber bundles -/

section FiberBundle

variable (F)
variable [TopologicalSpace B] [TopologicalSpace F] (E : B -> Type*)
  [TopologicalSpace (TotalSpace F E)] [forall b, TopologicalSpace (E b)]

/--
Definition of `FiberBundle` / `FiberBundle` 的定义

English:
class FiberBundle
  parameters: where
  axioms and operations (5):
    - totalSpaceMk_isInducing' : forall b : B, IsInducing (@TotalSpace.mk B F E b)
    - trivializationAtlas' : Set (Trivialization F (π F E))
    - trivializationAt' : B -> Trivialization F (π F E)
    - mem_baseSet_trivializationAt' : forall b : B, b in (trivializationAt' b).baseSet
    - trivialization_mem_atlas' : forall b : B, trivializationAt' b in trivializationAtlas'

中文:
类 纤维丛
  参数: where
  公理与运算 (5 个):
    - totalSpaceMk_isInducing' : 对任意 b : B, 是Inducing (@全空间.mk B F E b)
    - trivializationAtlas' : 集合 (Trivialization F (π F E))
    - trivializationAt' : B -> Trivialization F (π F E)
    - mem_baseSet_trivializationAt' : 对任意 b : B, b in (trivializationAt' b).baseSet
    - trivialization_mem_atlas' : 对任意 b : B, trivializationAt' b in trivializationAtlas'
-/
class FiberBundle where
  totalSpaceMk_isInducing' : forall b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B -> Trivialization F (π F E)
  mem_baseSet_trivializationAt' : forall b : B, b in (trivializationAt' b).baseSet
  trivialization_mem_atlas' : forall b : B, trivializationAt' b in trivializationAtlas'

namespace FiberBundle

variable [FiberBundle F E] (b : B)

/--
theorem `totalSpaceMk_isInducing` / 定理 `totalSpaceMk_isInducing`

English:
theorem totalSpaceMk_isInducing
  statement: IsInducing (@TotalSpace.mk B F E b)
  proof: totalSpaceMk_isInducing' b

中文:
定理 totalSpaceMk_isInducing
  结论: 是Inducing (@全空间.mk B F E b)
  证明: totalSpaceMk_isInducing' b

Depends on / 依赖: totalSpaceMk_isInducing
-/
theorem totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b) := totalSpaceMk_isInducing' b

/--
Definition of `trivializationAtlas` / `trivializationAtlas` 的定义

English:
abbreviation trivializationAtlas
  signature: : Set (Trivialization F (π F E))
  body: trivializationAtlas'

中文:
缩写 trivializationAtlas
  签名: : 集合 (Trivialization F (π F E))
  定义体: trivializationAtlas'

Depends on / 依赖: trivializationAtlas
-/
abbrev trivializationAtlas : Set (Trivialization F (π F E)) := trivializationAtlas'

/--
Definition of `trivializationAt` / `trivializationAt` 的定义

English:
abbreviation trivializationAt
  signature: : Trivialization F (π F E)
  body: trivializationAt' b

中文:
缩写 trivializationAt
  签名: : Trivialization F (π F E)
  定义体: trivializationAt' b

Depends on / 依赖: trivializationAt
-/
abbrev trivializationAt : Trivialization F (π F E) := trivializationAt' b

/--
theorem `mem_baseSet_trivializationAt` / 定理 `mem_baseSet_trivializationAt`

English:
theorem mem_baseSet_trivializationAt
  statement: b in (trivializationAt F E b).baseSet
  proof: mem_baseSet_trivializationAt' b

中文:
定理 mem_baseSet_trivializationAt
  结论: b in (trivializationAt F E b).baseSet
  证明: mem_baseSet_trivializationAt' b

Depends on / 依赖: mem_baseSet_trivializationAt
-/
theorem mem_baseSet_trivializationAt : b in (trivializationAt F E b).baseSet :=
  mem_baseSet_trivializationAt' b

/--
theorem `trivialization_mem_atlas` / 定理 `trivialization_mem_atlas`

English:
theorem trivialization_mem_atlas
  statement: trivializationAt F E b in trivializationAtlas F E
  proof: trivialization_mem_atlas' b

中文:
定理 trivialization_mem_atlas
  结论: trivializationAt F E b in trivializationAtlas F E
  证明: trivialization_mem_atlas' b

Depends on / 依赖: trivialization_mem_atlas
-/
theorem trivialization_mem_atlas : trivializationAt F E b in trivializationAtlas F E :=
  trivialization_mem_atlas' b

end FiberBundle

export FiberBundle (totalSpaceMk_isInducing trivializationAtlas trivializationAt
  mem_baseSet_trivializationAt trivialization_mem_atlas)

variable {F}
variable {E}

/-- Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle. This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
/--
Definition of `MemTrivializationAtlas` / `MemTrivializationAtlas` 的定义

English:
class MemTrivializationAtlas
  parameters: [FiberBundle F E] (e : Trivialization F (π F E))
  axioms and operations (1):
    - out : e in trivializationAtlas F E

中文:
类 MemTrivializationAtlas
  参数: [纤维丛 F E] (e : Trivialization F (π F E))
  公理与运算 (1 个):
    - out : e in trivializationAtlas F E
-/
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π F E)) : Prop where
  out : e in trivializationAtlas F E

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiberBundle
  signature: F E] (b
  body: trivialization_mem_atlas F E b

中文:
实例 [纤维丛
  签名: F E] (b
  定义体: trivialization_mem_atlas F E b

Depends on / 依赖: trivialization_mem_atlas
-/
instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b) where
  out := trivialization_mem_atlas F E b

namespace FiberBundle

variable (F)
variable [FiberBundle F E]

/--
theorem `map_proj_nhds` / 定理 `map_proj_nhds`

English:
theorem map_proj_nhds
  given: (x : TotalSpace F E)
  statement: map (π F E) (𝓝 x) = 𝓝 x.proj
  proof: (trivializationAt F E x.proj).map_proj_nhds
(trivializationAt F E x.proj).mem_source.2 mem_baseSet_trivializationAt F E x.proj

中文:
定理 map_proj_nhds
  条件: (x : 全空间 F E)
  结论: map (π F E) (𝓝 x) = 𝓝 x.proj
  证明: (trivializationAt F E x.proj).map_proj_nhds
(trivializationAt F E x.proj).mem_source.2 mem_baseSet_trivializationAt F E x.proj

Depends on / 依赖: map_proj_nhds, mem_baseSet_trivializationAt, mem_source, trivializationAt, x.proj
-/
theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
(trivializationAt F E x.proj).map_proj_nhds
(trivializationAt F E x.proj).mem_source.2 mem_baseSet_trivializationAt F E x.proj

variable (E)

/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity]
/--
theorem `continuous_proj` / 定理 `continuous_proj`

English:
theorem continuous_proj
  statement: Continuous (π F E)
  proof: continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

中文:
定理 continuous_proj
  结论: 连续 (π F E)
  证明: continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

Depends on / 依赖: continuous_iff_continuousAt, map_proj_nhds
-/
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

/--
theorem `isOpenMap_proj` / 定理 `isOpenMap_proj`

English:
theorem isOpenMap_proj
  statement: IsOpenMap (π F E)
  proof: IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

中文:
定理 isOpenMap_proj
  结论: 是开映射 (π F E)
  证明: IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

Depends on / 依赖: IsOpenMap, IsOpenMap.of_nhds_le, map_proj_nhds, of_nhds_le
-/
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

/--
theorem `surjective_proj` / 定理 `surjective_proj`

English:
theorem surjective_proj
  given: [Nonempty F]
  statement: Function.Surjective (π F E)
  proof: fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩

中文:
定理 surjective_proj
  条件: [非空 F]
  结论: 函数.满射 (π F E)
  证明: fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩
-/
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩

/--
theorem `isQuotientMap_proj` / 定理 `isQuotientMap_proj`

English:
theorem isQuotientMap_proj
  given: [Nonempty F]
  statement: IsQuotientMap (π F E)
  proof: (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)

中文:
定理 isQuotientMap_proj
  条件: [非空 F]
  结论: 是商映射 (π F E)
  证明: (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)

Depends on / 依赖: continuous_proj, isOpenMap_proj, isQuotientMap, surjective_proj
-/
theorem isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E) :=
  (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)

/--
theorem `continuous_totalSpaceMk` / 定理 `continuous_totalSpaceMk`

English:
theorem continuous_totalSpaceMk
  given: (x : B)
  statement: Continuous (@TotalSpace.mk B F E x)
  proof: (totalSpaceMk_isInducing F E x).continuous

中文:
定理 continuous_totalSpaceMk
  条件: (x : B)
  结论: 连续 (@全空间.mk B F E x)
  证明: (totalSpaceMk_isInducing F E x).continuous

Depends on / 依赖: continuous, totalSpaceMk_isInducing
-/
theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpaceMk_isInducing F E x).continuous

/--
theorem `totalSpaceMk_isEmbedding` / 定理 `totalSpaceMk_isEmbedding`

English:
theorem totalSpaceMk_isEmbedding
  given: (x : B)
  statement: IsEmbedding (@TotalSpace.mk B F E x)
  proof: ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩

中文:
定理 totalSpaceMk_isEmbedding
  条件: (x : B)
  结论: 是嵌入 (@全空间.mk B F E x)
  证明: ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩

Depends on / 依赖: TotalSpace, TotalSpace.mk_injective, mk_injective, totalSpaceMk_isInducing
-/
theorem totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩

/--
theorem `totalSpaceMk_isClosedEmbedding` / 定理 `totalSpaceMk_isClosedEmbedding`

English:
theorem totalSpaceMk_isClosedEmbedding
  given: [T1Space B] (x : B)
  proof: ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
exact isClosed_singleton.preimage continuous_proj F E⟩

中文:
定理 totalSpaceMk_isClosedEmbedding
  条件: [T1空间 B] (x : B)
  证明: ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
exact isClosed_singleton.preimage continuous_proj F E⟩

Depends on / 依赖: TotalSpace, TotalSpace.range_mk, continuous_proj, isClosed_singleton, isClosed_singleton.preimage, preimage, range_mk, totalSpaceMk_isEmbedding
-/
theorem totalSpaceMk_isClosedEmbedding [T1Space B] (x : B) :
    IsClosedEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
exact isClosed_singleton.preimage continuous_proj F E⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homeomorphAt` / `homeomorphAt` 的定义

English:
definition homeomorphAt
  signature: (b : B)
  body: ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
Homeomorph.setCongr TotalSpace.range_mk b).trans <|
(trivializationAt F E b).preimageSingletonHomeomorph mem_baseSet_trivializationAt' b

中文:
定义 homeomorphAt
  签名: (b : B)
  定义体: ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
Homeomorph.setCongr TotalSpace.range_mk b).trans <|
(trivializationAt F E b).preimageSingletonHomeomorph mem_baseSet_trivializationAt' b

Depends on / 依赖: Homeomorph, Homeomorph.setCongr, TotalSpace, TotalSpace.range_mk, mem_baseSet_trivializationAt, preimageSingletonHomeomorph, range_mk, setCongr, toHomeomorph, toHomeomorph.trans, totalSpaceMk_isEmbedding, trivializationAt
-/
noncomputable def homeomorphAt (b : B) : E b ≃ₜ F :=
  ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
Homeomorph.setCongr TotalSpace.range_mk b).trans <|
(trivializationAt F E b).preimageSingletonHomeomorph mem_baseSet_trivializationAt' b

/--
lemma `t0Space` / 引理 `t0Space`

English:
lemma t0Space
  given: [T0Space F] (b : B)
  statement: T0Space (E b)
  proof: .symm.t0Space FiberBundle.homeomorphAt F E b

中文:
引理 t0Space
  条件: [T0空间 F] (b : B)
  结论: T0空间 (E b)
  证明: .symm.t0Space FiberBundle.homeomorphAt F E b

Depends on / 依赖: FiberBundle, FiberBundle.homeomorphAt, homeomorphAt, symm.t0Space, t0Space
-/
lemma t0Space [T0Space F] (b : B) : T0Space (E b) :=
.symm.t0Space FiberBundle.homeomorphAt F E b

/--
lemma `t1Space` / 引理 `t1Space`

English:
lemma t1Space
  given: [T1Space F] (b : B)
  statement: T1Space (E b)
  proof: .symm.t1Space FiberBundle.homeomorphAt F E b

中文:
引理 t1Space
  条件: [T1空间 F] (b : B)
  结论: T1空间 (E b)
  证明: .symm.t1Space FiberBundle.homeomorphAt F E b

Depends on / 依赖: FiberBundle, FiberBundle.homeomorphAt, homeomorphAt, symm.t1Space, t1Space
-/
lemma t1Space [T1Space F] (b : B) : T1Space (E b) :=
.symm.t1Space FiberBundle.homeomorphAt F E b

/--
lemma `t2Space` / 引理 `t2Space`

English:
lemma t2Space
  given: [T2Space F] (b : B)
  statement: T2Space (E b)
  proof: .symm.t2Space FiberBundle.homeomorphAt F E b

中文:
引理 t2Space
  条件: [T2空间 F] (b : B)
  结论: T2空间 (E b)
  证明: .symm.t2Space FiberBundle.homeomorphAt F E b

Depends on / 依赖: FiberBundle, FiberBundle.homeomorphAt, homeomorphAt, symm.t2Space, t2Space
-/
lemma t2Space [T2Space F] (b : B) : T2Space (E b) :=
.symm.t2Space FiberBundle.homeomorphAt F E b

/--
lemma `t3Space` / 引理 `t3Space`

English:
lemma t3Space
  given: [T3Space F] (b : B)
  statement: T3Space (E b)
  proof: .symm.t3Space FiberBundle.homeomorphAt F E b

中文:
引理 t3Space
  条件: [T3空间 F] (b : B)
  结论: T3空间 (E b)
  证明: .symm.t3Space FiberBundle.homeomorphAt F E b

Depends on / 依赖: FiberBundle, FiberBundle.homeomorphAt, homeomorphAt, symm.t3Space, t3Space
-/
lemma t3Space [T3Space F] (b : B) : T3Space (E b) :=
.symm.t3Space FiberBundle.homeomorphAt F E b

variable {E F}

@[simp, mfld_simps]
/--
theorem `mem_trivializationAt_proj_source` / 定理 `mem_trivializationAt_proj_source`

English:
theorem mem_trivializationAt_proj_source
  given: {x : TotalSpace F E}
  proof: (Trivialization.mem_source _).mpr mem_baseSet_trivializationAt F E x.proj

中文:
定理 mem_trivializationAt_proj_source
  条件: {x : 全空间 F E}
  证明: (Trivialization.mem_source _).mpr mem_baseSet_trivializationAt F E x.proj

Depends on / 依赖: Trivialization, Trivialization.mem_source, mem_baseSet_trivializationAt, mem_source, x.proj
-/
theorem mem_trivializationAt_proj_source {x : TotalSpace F E} :
    x in (trivializationAt F E x.proj).source :=
(Trivialization.mem_source _).mpr mem_baseSet_trivializationAt F E x.proj

/--
theorem `trivializationAt_proj_fst` / 定理 `trivializationAt_proj_fst`

English:
theorem trivializationAt_proj_fst
  given: {x : TotalSpace F E}
  proof: Trivialization.coe_fst' _ mem_baseSet_trivializationAt F E x.proj

中文:
定理 trivializationAt_proj_fst
  条件: {x : 全空间 F E}
  证明: Trivialization.coe_fst' _ mem_baseSet_trivializationAt F E x.proj

Depends on / 依赖: Trivialization, Trivialization.coe_fst, coe_fst, mem_baseSet_trivializationAt, x.proj
-/
theorem trivializationAt_proj_fst {x : TotalSpace F E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
Trivialization.coe_fst' _ mem_baseSet_trivializationAt F E x.proj

variable (F)

open Trivialization

/--
theorem `continuousWithinAt_totalSpace` / 定理 `continuousWithinAt_totalSpace`

English:
theorem continuousWithinAt_totalSpace
  given: (f : X -> TotalSpace F E) {s : Set X} {x₀ : X}
  proof: (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

中文:
定理 continuousWithinAt_totalSpace
  条件: (f : X -> 全空间 F E) {s : 集合 X} {x₀ : X}
  证明: (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

Depends on / 依赖: mem_trivializationAt_proj_source, tendsto_nhds_iff, trivializationAt
-/
theorem continuousWithinAt_totalSpace (f : X -> TotalSpace F E) {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
        ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/--
theorem `continuousAt_totalSpace` / 定理 `continuousAt_totalSpace`

English:
theorem continuousAt_totalSpace
  given: (f : X -> TotalSpace F E) {x₀ : X}
  proof: (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

中文:
定理 continuousAt_totalSpace
  条件: (f : X -> 全空间 F E) {x₀ : X}
  证明: (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

Depends on / 依赖: mem_trivializationAt_proj_source, tendsto_nhds_iff, trivializationAt
-/
theorem continuousAt_totalSpace (f : X -> TotalSpace F E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/--
theorem `continuousWithinAt_section` / 定理 `continuousWithinAt_section`

English:
theorem continuousWithinAt_section
  given: {s : forall x, E x} {a : Set B} {x₀ : B}
  proof: by
  simp_rw [continuousWithinAt_totalSpace, and_iff_right_iff_imp]
  intro; exact continuousWithinAt_id

中文:
定理 continuousWithinAt_section
  条件: {s : 对任意 x, E x} {a : 集合 B} {x₀ : B}
  证明: by
  simp_rw [continuousWithinAt_totalSpace, and_iff_right_iff_imp]
  intro; exact continuousWithinAt_id

Depends on / 依赖: and_iff_right_iff_imp, continuousWithinAt_id, continuousWithinAt_totalSpace, simp_rw
-/
theorem continuousWithinAt_section {s : forall x, E x} {a : Set B} {x₀ : B} :
    ContinuousWithinAt (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔
      ContinuousWithinAt (fun x => (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [continuousWithinAt_totalSpace, and_iff_right_iff_imp]
  intro; exact continuousWithinAt_id

/--
theorem `continuousAt_section` / 定理 `continuousAt_section`

English:
theorem continuousAt_section
  given: {s : forall x, E x} (x₀ : B)
  proof: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_section F

中文:
定理 continuousAt_section
  条件: {s : 对任意 x, E x} (x₀ : B)
  证明: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_section F

Depends on / 依赖: continuousWithinAt_section, continuousWithinAt_univ, simp_rw
-/
theorem continuousAt_section {s : forall x, E x} (x₀ : B) :
    ContinuousAt (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContinuousAt (fun x => (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_section F

end FiberBundle

variable (F)
variable (E)

/--
theorem `FiberBundle.exists_trivialization_Icc_subset` / 定理 `FiberBundle.exists_trivialization_Icc_subset`

English:
theorem FiberBundle.exists_trivialization_Icc_subset
  statement: [ConditionallyCompleteLinearOrder B]
  proof: by
  obtain ⟨ea, hea⟩ : exists ea : Trivialization F (π F E), a in ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  rcases lt_or_ge b a with _ | hab
  · exact ⟨ea, by simp [*]⟩
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x in Icc a b | exists e : Trivialization F (π F E), Icc a x subseteq e.baseSet }
  have ha : a in s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c subseteq ec.baseSet⟩ : c in s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
      of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : exists ec : Trivialization F (π F E), c in ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : exists c' in Ico a c, Ioc c' c subseteq ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
      `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : exists d in s, d in Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`. If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : exists d in Ioc c b, exists e : Trivialization F (π F E), Icc a d subseteq e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_gt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : exists d in Ioc c b, Ico c d subseteq ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d subseteq ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
      Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
      a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : exists ed : Trivialization F (π F E), d in ed.baseSet :=
      ⟨trivializationAt F E d, mem_baseSet_trivializationAt F E d⟩
    refine ⟨d, hdcb,
      (ec.restrOpen (Iio d) isOpen_Iio).disjointUnion (ed.restrOpen (Ioi c) isOpen_Ioi)
        (he.mono inter_subset_right inter_subset_right), fun x hx => ?_⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
          `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he
    push Not at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩

中文:
定理 纤维丛.存在_trivialization_Icc_subset
  结论: [条件完备线性序 B]
  证明: by
  obtain ⟨ea, hea⟩ : exists ea : Trivialization F (π F E), a in ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  rcases lt_or_ge b a with _ | hab
  · exact ⟨ea, by simp [*]⟩
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x in Icc a b | exists e : Trivialization F (π F E), Icc a x subseteq e.baseSet }
  have ha : a in s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c subseteq ec.baseSet⟩ : c in s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
      of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : exists ec : Trivialization F (π F E), c in ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : exists c' in Ico a c, Ioc c' c subseteq ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
      `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : exists d in s, d in Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`. If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : exists d in Ioc c b, exists e : Trivialization F (π F E), Icc a d subseteq e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_gt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : exists d in Ioc c b, Ico c d subseteq ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d subseteq ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
      Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
      a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : exists ed : Trivialization F (π F E), d in ed.baseSet :=
      ⟨trivializationAt F E d, mem_baseSet_trivializationAt F E d⟩
    refine ⟨d, hdcb,
      (ec.restrOpen (Iio d) isOpen_Iio).disjointUnion (ed.restrOpen (Ioi c) isOpen_Ioi)
        (he.mono inter_subset_right inter_subset_right), fun x hx => ?_⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
          `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he
    push Not at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩

Depends on / 依赖: Trivialization, baseSet, ea.baseSet, mem_baseSet_trivializationAt, trivializationAt
-/
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    exists e : Trivialization F (π F E), Icc a b subseteq e.baseSet := by
  obtain ⟨ea, hea⟩ : exists ea : Trivialization F (π F E), a in ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  rcases lt_or_ge b a with _ | hab
  · exact ⟨ea, by simp [*]⟩
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x in Icc a b | exists e : Trivialization F (π F E), Icc a x subseteq e.baseSet }
  have ha : a in s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c subseteq ec.baseSet⟩ : c in s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
      of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : exists ec : Trivialization F (π F E), c in ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : exists c' in Ico a c, Ioc c' c subseteq ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
      `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : exists d in s, d in Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`. If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : exists d in Ioc c b, exists e : Trivialization F (π F E), Icc a d subseteq e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_gt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : exists d in Ioc c b, Ico c d subseteq ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d subseteq ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
      Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
      a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : exists ed : Trivialization F (π F E), d in ed.baseSet :=
      ⟨trivializationAt F E d, mem_baseSet_trivializationAt F E d⟩
    refine ⟨d, hdcb,
      (ec.restrOpen (Iio d) isOpen_Iio).disjointUnion (ed.restrOpen (Ioi c) isOpen_Ioi)
        (he.mono inter_subset_right inter_subset_right), fun x hx => ?_⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
          `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he
    push Not at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩

end FiberBundle

/-! ### Core construction for constructing fiber bundles -/

/--
Definition of `FiberBundleCore` / `FiberBundleCore` 的定义

English:
structure FiberBundleCore
  parameters: (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
  axioms and operations (8):
    - baseSet : ι -> Set B
    - isOpen_baseSet : forall i, IsOpen (baseSet i)
    - indexAt : B -> ι
    - mem_baseSet_at : forall x, x in baseSet (indexAt x)
    - coordChange : ι -> ι -> B -> F -> F
    - coordChange_self : forall i, forall x in baseSet i, forall v, coordChange i i x v = v
    - continuousOn_coordChange : forall i j, ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i inter baseSet j) ×ˢ univ)
    - coordChange_comp : forall i j k, forall x in baseSet i inter baseSet j inter baseSet k, forall v, (coordChange j k x) (coordChange i j x v) = coordChange i k x v

中文:
结构 纤维丛核心
  参数: (ι : 类型) (B : 类型) [拓扑空间 B] (F : 类型)
  公理与运算 (8 个):
    - baseSet : ι -> 集合 B
    - isOpen_baseSet : 对任意 i, 是开集 (baseSet i)
    - indexAt : B -> ι
    - mem_baseSet_at : 对任意 x, x in baseSet (indexAt x)
    - coordChange : ι -> ι -> B -> F -> F
    - coordChange_self : 对任意 i, 对任意 x in baseSet i, 对任意 v, coordChange i i x v = v
    - continuousOn_coordChange : 对任意 i j, ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i inter baseSet j) ×ˢ univ)
    - coordChange_comp : 对任意 i j k, 对任意 x in baseSet i inter baseSet j inter baseSet k, 对任意 v, (coordChange j k x) (coordChange i j x v) = coordChange i k x v
-/
structure FiberBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] where
  baseSet : ι -> Set B
  isOpen_baseSet : forall i, IsOpen (baseSet i)
  indexAt : B -> ι
  mem_baseSet_at : forall x, x in baseSet (indexAt x)
  coordChange : ι -> ι -> B -> F -> F
  coordChange_self : forall i, forall x in baseSet i, forall v, coordChange i i x v = v
  continuousOn_coordChange : forall i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i inter baseSet j) ×ˢ univ)
  coordChange_comp : forall i j k, forall x in baseSet i inter baseSet j inter baseSet k, forall v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

namespace FiberBundleCore

variable [TopologicalSpace B] [TopologicalSpace F] (Z : FiberBundleCore ι B F)

/-- The index set of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
/--
Definition of `Index` / `Index` 的定义

English:
definition Index
  signature: (_Z : FiberBundleCore ι B F)
  body: ι

中文:
定义 Index
  签名: (_Z : 纤维丛核心 ι B F)
  定义体: ι
-/
def Index (_Z : FiberBundleCore ι B F) := ι

/-- The base space of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
/--
Definition of `Base` / `Base` 的定义

English:
definition Base
  signature: (_Z : FiberBundleCore ι B F)
  body: B

中文:
定义 Base
  签名: (_Z : 纤维丛核心 ι B F)
  定义体: B
-/
def Base (_Z : FiberBundleCore ι B F) := B

/-- The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
/--
Definition of `Fiber` / `Fiber` 的定义

English:
definition Fiber
  signature: (_ : FiberBundleCore ι B F) (_x : B)
  body: F

中文:
定义 Fiber
  签名: (_ : 纤维丛核心 ι B F) (_x : B)
  定义体: F
-/
def Fiber (_ : FiberBundleCore ι B F) (_x : B) := F

/--
Instance `topologicalSpaceFiber` / 实例 `topologicalSpaceFiber`

English:
instance topologicalSpaceFiber
  signature: (x : B)
  body: ‹_›

中文:
实例 topologicalSpaceFiber
  签名: (x : B)
  定义体: ‹_›
-/
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := ‹_›

/--
Definition of `TotalSpace` / `TotalSpace` 的定义

English:
abbreviation TotalSpace
  body: Bundle.TotalSpace F Z.Fiber

中文:
缩写 全空间
  定义体: Bundle.TotalSpace F Z.Fiber

Depends on / 依赖: Bundle, Bundle.TotalSpace, TotalSpace, Z.Fiber
-/
abbrev TotalSpace := Bundle.TotalSpace F Z.Fiber

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: : Z.TotalSpace -> B
  body: Bundle.TotalSpace.proj

中文:
定义 proj
  签名: : Z.全空间 -> B
  定义体: Bundle.TotalSpace.proj

Depends on / 依赖: Bundle, Bundle.TotalSpace.proj, TotalSpace
-/
def proj : Z.TotalSpace -> B :=
  Bundle.TotalSpace.proj

/--
Definition of `trivChange` / `trivChange` 的定义

English:
definition trivChange
  signature: (i j : ι)
  body: (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange j i)

@[simp, mfld_simps]

中文:
定义 trivChange
  签名: (i j : ι)
  定义体: (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange j i)

@[simp, mfld_simps]

Depends on / 依赖: Z.baseSet, baseSet
-/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) where
  source := (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i inter Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange j i)

@[simp, mfld_simps]
/--
theorem `mem_trivChange_source` / 定理 `mem_trivChange_source`

English:
theorem mem_trivChange_source
  given: (i j : ι) (p : B × F)
  proof: by
  rw [trivChange]; rw [mem_prod]
  simp

中文:
定理 mem_trivChange_source
  条件: (i j : ι) (p : B × F)
  证明: by
  rw [trivChange]; rw [mem_prod]
  simp

Depends on / 依赖: mem_prod, trivChange
-/
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p in (Z.trivChange i j).source ↔ p.1 in Z.baseSet i inter Z.baseSet j := by
  rw [trivChange]; rw [mem_prod]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `localTrivAsPartialEquiv` / `localTrivAsPartialEquiv` 的定义

English:
definition localTrivAsPartialEquiv
  signature: (i : ι)
  body: Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.prodMk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x in Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]

中文:
定义 localTrivAsPartialEquiv
  签名: (i : ι)
  定义体: Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.prodMk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x in Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]

Depends on / 依赖: Z.baseSet, Z.proj, baseSet
-/
def localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F) where
  source := Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.prodMk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x in Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp]; rw [Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]

variable (i : ι)

/--
theorem `mem_localTrivAsPartialEquiv_source` / 定理 `mem_localTrivAsPartialEquiv_source`

English:
theorem mem_localTrivAsPartialEquiv_source
  given: (p : Z.TotalSpace)
  proof: Iff.rfl

中文:
定理 mem_localTrivAsPartialEquiv_source
  条件: (p : Z.全空间)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) :
    p in (Z.localTrivAsPartialEquiv i).source ↔ p.1 in Z.baseSet i :=
  Iff.rfl

/--
theorem `mem_localTrivAsPartialEquiv_target` / 定理 `mem_localTrivAsPartialEquiv_target`

English:
theorem mem_localTrivAsPartialEquiv_target
  given: (p : B × F)
  proof: by
  rw [localTrivAsPartialEquiv]; rw [mem_prod]
  simp only [and_true, mem_univ]

中文:
定理 mem_localTrivAsPartialEquiv_target
  条件: (p : B × F)
  证明: by
  rw [localTrivAsPartialEquiv]; rw [mem_prod]
  simp only [and_true, mem_univ]

Depends on / 依赖: and_true, localTrivAsPartialEquiv, mem_prod, mem_univ
-/
theorem mem_localTrivAsPartialEquiv_target (p : B × F) :
    p in (Z.localTrivAsPartialEquiv i).target ↔ p.1 in Z.baseSet i := by
  rw [localTrivAsPartialEquiv]; rw [mem_prod]
  simp only [and_true, mem_univ]

/--
theorem `localTrivAsPartialEquiv_apply` / 定理 `localTrivAsPartialEquiv_apply`

English:
theorem localTrivAsPartialEquiv_apply
  given: (p : Z.TotalSpace)
  proof: rfl

中文:
定理 localTrivAsPartialEquiv_apply
  条件: (p : Z.全空间)
  证明: rfl
-/
theorem localTrivAsPartialEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsPartialEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

/--
theorem `localTrivAsPartialEquiv_trans` / 定理 `localTrivAsPartialEquiv_trans`

English:
theorem localTrivAsPartialEquiv_trans
  given: (i j : ι)
  proof: by
  constructor
  · ext x
    simp only [mem_localTrivAsPartialEquiv_target, mfld_simps]
    rfl
  · rintro ⟨x, v⟩ hx
    simp only [trivChange, localTrivAsPartialEquiv, PartialEquiv.symm,
      Prod.mk_inj, prodMk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      mem_preimage, proj, mem_univ, (· ∘ ·),
      PartialEquiv.coe_trans] at hx ⊢
    simp only [Z.coordChange_comp, hx, mem_inter_iff, and_self_iff, mem_baseSet_at]

中文:
定理 localTrivAsPartialEquiv_trans
  条件: (i j : ι)
  证明: by
  constructor
  · ext x
    simp only [mem_localTrivAsPartialEquiv_target, mfld_simps]
    rfl
  · rintro ⟨x, v⟩ hx
    simp only [trivChange, localTrivAsPartialEquiv, PartialEquiv.symm,
      Prod.mk_inj, prodMk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      mem_preimage, proj, mem_univ, (· ∘ ·),
      PartialEquiv.coe_trans] at hx ⊢
    simp only [Z.coordChange_comp, hx, mem_inter_iff, and_self_iff, mem_baseSet_at]

Depends on / 依赖: PartialEquiv, PartialEquiv.coe_trans, PartialEquiv.symm, PartialEquiv.trans_source, Prod.mk_inj, Z.coordChange_comp, and_self_iff, coe_trans, coordChange_comp, localTrivAsPartialEquiv, mem_baseSet_at, mem_inter_iff, mem_localTrivAsPartialEquiv_target, mem_preimage, mem_univ, mfld_simps, mk_inj, prodMk_mem_set_prod_eq, trans_source, trivChange
-/
theorem localTrivAsPartialEquiv_trans (i j : ι) :
    (Z.localTrivAsPartialEquiv i).symm.trans (Z.localTrivAsPartialEquiv j) ≈
      (Z.trivChange i j).toPartialEquiv := by
  constructor
  · ext x
    simp only [mem_localTrivAsPartialEquiv_target, mfld_simps]
    rfl
  · rintro ⟨x, v⟩ hx
    simp only [trivChange, localTrivAsPartialEquiv, PartialEquiv.symm,
      Prod.mk_inj, prodMk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      mem_preimage, proj, mem_univ, (· ∘ ·),
      PartialEquiv.coe_trans] at hx ⊢
    simp only [Z.coordChange_comp, hx, mem_inter_iff, and_self_iff, mem_baseSet_at]

/--
Instance `toTopologicalSpace` / 实例 `toTopologicalSpace`

English:
instance toTopologicalSpace
  signature: : TopologicalSpace (Bundle.TotalSpace F Z.Fiber)
  body: TopologicalSpace.generateFrom ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source inter Z.localTrivAsPartialEquiv i ⁻¹' s}

中文:
实例 toTopologicalSpace
  签名: : 拓扑空间 (Bundle.全空间 F Z.Fiber)
  定义体: TopologicalSpace.generateFrom ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source inter Z.localTrivAsPartialEquiv i ⁻¹' s}

Depends on / 依赖: IsOpen, TopologicalSpace, TopologicalSpace.generateFrom, Z.localTrivAsPartialEquiv, generateFrom, localTrivAsPartialEquiv, source
-/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber) :=
TopologicalSpace.generateFrom ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source inter Z.localTrivAsPartialEquiv i ⁻¹' s}

variable (b : B) (a : F)

/--
theorem `open_source'` / 定理 `open_source'`

English:
theorem open_source'
  given: (i : ι)
  statement: IsOpen (Z.localTrivAsPartialEquiv i).source
  proof: by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prodMk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]

中文:
定理 open_source'
  条件: (i : ι)
  结论: 是开集 (Z.localTrivAsPartialEquiv i).source
  证明: by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prodMk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]

Depends on / 依赖: GenerateOpen, TopologicalSpace, TopologicalSpace.GenerateOpen.basic, Z.baseSet, Z.isOpen_baseSet, and_self_iff, and_true, baseSet, exists_prop, isOpen_baseSet, isOpen_univ, localTrivAsPartialEquiv_apply, mem_iUnion, mem_inter_iff, mem_localTrivAsPartialEquiv_source, mem_preimage, mem_singleton_iff, mem_univ, prodMk_mem_set_prod_eq
-/
theorem open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prodMk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]

/--
Definition of `localTriv` / `localTriv` 的定义

English:
definition localTriv
  signature: (i : ι)
  body: Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht => ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : exists j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source inter localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [preimage_inter]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source inter f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert! this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp]; rw [inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i

中文:
定义 localTriv
  签名: (i : ι)
  定义体: Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht => ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : exists j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source inter localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [preimage_inter]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source inter f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert! this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp]; rw [inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i

Depends on / 依赖: Z.baseSet, baseSet
-/
def localTriv (i : ι) : Trivialization F Z.proj where
  baseSet := Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht => ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : exists j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source inter localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [preimage_inter]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source inter f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert! this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp]; rw [inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i

/--
Definition of `localTrivAt` / `localTrivAt` 的定义

English:
definition localTrivAt
  signature: (b : B)
  body: Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]

中文:
定义 localTrivAt
  签名: (b : B)
  定义体: Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]

Depends on / 依赖: Z.indexAt, Z.localTriv, indexAt, localTriv
-/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
/--
theorem `localTrivAt_def` / 定理 `localTrivAt_def`

English:
theorem localTrivAt_def
  given: (b : B)
  statement: Z.localTriv (Z.indexAt b) = Z.localTrivAt b
  proof: rfl

中文:
定理 localTrivAt_def
  条件: (b : B)
  结论: Z.localTriv (Z.indexAt b) = Z.localTrivAt b
  证明: rfl
-/
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

/--
theorem `localTrivAt_snd` / 定理 `localTrivAt_snd`

English:
theorem localTrivAt_snd
  given: (b : B) (p)
  proof: rfl

中文:
定理 localTrivAt_snd
  条件: (b : B) (p)
  证明: rfl
-/
theorem localTrivAt_snd (b : B) (p) :
    (Z.localTrivAt b p).2 = Z.coordChange (Z.indexAt p.1) (Z.indexAt b) p.1 p.2 :=
  rfl

/--
theorem `continuous_const_section` / 定理 `continuous_const_section`

English:
theorem continuous_const_section
  statement: (v : F)
  proof: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) in 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prodMk
    simp only [mfld_simps]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy => ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩

@[simp, mfld_simps]

中文:
定理 continuous_const_section
  结论: (v : F)
  证明: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) in 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prodMk
    simp only [mfld_simps]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy => ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩

@[simp, mfld_simps]

Depends on / 依赖: ContinuousOn, IsOpen, IsOpen.mem_nhds, Z.baseSet, Z.indexAt, Z.isOpen_baseSet, Z.localTrivAt, Z.mem_baseSet_at, baseSet, continuousAt, continuousAt_id, continuousAt_id.prodMk, continuousAt_iff_continuousAt_comp_left, continuousOn_const, continuous_iff_continuousAt, indexAt, isOpen_baseSet, localTrivAt, mem_baseSet_at, mem_nhds
-/
theorem continuous_const_section (v : F)
    (h : forall i j, forall x in Z.baseSet i inter Z.baseSet j, Z.coordChange i j x v = v) :
    Continuous (show B -> Z.TotalSpace from fun x => ⟨x, v⟩) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) in 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prodMk
    simp only [mfld_simps]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy => ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩

@[simp, mfld_simps]
/--
theorem `localTrivAsPartialEquiv_coe` / 定理 `localTrivAsPartialEquiv_coe`

English:
theorem localTrivAsPartialEquiv_coe
  statement: ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTrivAsPartialEquiv_coe
  结论: ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i :=
  rfl

@[simp, mfld_simps]
/--
theorem `localTrivAsPartialEquiv_source` / 定理 `localTrivAsPartialEquiv_source`

English:
theorem localTrivAsPartialEquiv_source
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTrivAsPartialEquiv_source
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTrivAsPartialEquiv_source :
    (Z.localTrivAsPartialEquiv i).source = (Z.localTriv i).source :=
  rfl

@[simp, mfld_simps]
/--
theorem `localTrivAsPartialEquiv_target` / 定理 `localTrivAsPartialEquiv_target`

English:
theorem localTrivAsPartialEquiv_target
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTrivAsPartialEquiv_target
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTrivAsPartialEquiv_target :
    (Z.localTrivAsPartialEquiv i).target = (Z.localTriv i).target :=
  rfl

@[simp, mfld_simps]
/--
theorem `localTrivAsPartialEquiv_symm` / 定理 `localTrivAsPartialEquiv_symm`

English:
theorem localTrivAsPartialEquiv_symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTrivAsPartialEquiv_symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTrivAsPartialEquiv_symm :
    (Z.localTrivAsPartialEquiv i).symm = (Z.localTriv i).toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `baseSet_at` / 定理 `baseSet_at`

English:
theorem baseSet_at
  statement: Z.baseSet i = (Z.localTriv i).baseSet
  proof: rfl

@[simp, mfld_simps]

中文:
定理 baseSet_at
  结论: Z.baseSet i = (Z.localTriv i).baseSet
  证明: rfl

@[simp, mfld_simps]
-/
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
/--
theorem `localTriv_apply` / 定理 `localTriv_apply`

English:
theorem localTriv_apply
  given: (p : Z.TotalSpace)
  proof: rfl

中文:
定理 localTriv_apply
  条件: (p : Z.全空间)
  证明: rfl
-/
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/--
theorem `localTrivAt_apply` / 定理 `localTrivAt_apply`

English:
theorem localTrivAt_apply
  given: (p : Z.TotalSpace)
  statement: (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩
  proof: by
  rw [localTrivAt]; rw [localTriv_apply]; rw [coordChange_self]
  exact Z.mem_baseSet_at p.1

@[simp, mfld_simps]

中文:
定理 localTrivAt_apply
  条件: (p : Z.全空间)
  结论: (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩
  证明: by
  rw [localTrivAt]; rw [localTriv_apply]; rw [coordChange_self]
  exact Z.mem_baseSet_at p.1

@[simp, mfld_simps]

Depends on / 依赖: Z.mem_baseSet_at, coordChange_self, localTrivAt, localTriv_apply, mem_baseSet_at
-/
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [localTrivAt]; rw [localTriv_apply]; rw [coordChange_self]
  exact Z.mem_baseSet_at p.1

@[simp, mfld_simps]
/--
theorem `localTrivAt_apply_mk` / 定理 `localTrivAt_apply_mk`

English:
theorem localTrivAt_apply_mk
  given: (b : B) (a : F)
  statement: (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩
  proof: Z.localTrivAt_apply _

@[simp, mfld_simps]

中文:
定理 localTrivAt_apply_mk
  条件: (b : B) (a : F)
  结论: (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩
  证明: Z.localTrivAt_apply _

@[simp, mfld_simps]

Depends on / 依赖: Z.localTrivAt_apply, localTrivAt_apply
-/
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
/--
theorem `mem_localTriv_source` / 定理 `mem_localTriv_source`

English:
theorem mem_localTriv_source
  given: (p : Z.TotalSpace)
  proof: Iff.rfl

@[simp, mfld_simps]

中文:
定理 mem_localTriv_source
  条件: (p : Z.全空间)
  证明: Iff.rfl

@[simp, mfld_simps]

Depends on / 依赖: Iff.rfl
-/
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p in (Z.localTriv i).source ↔ p.1 in (Z.localTriv i).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
/--
theorem `mem_localTrivAt_source` / 定理 `mem_localTrivAt_source`

English:
theorem mem_localTrivAt_source
  given: (p : Z.TotalSpace) (b : B)
  proof: Iff.rfl

@[simp, mfld_simps]

中文:
定理 mem_localTrivAt_source
  条件: (p : Z.全空间) (b : B)
  证明: Iff.rfl

@[simp, mfld_simps]

Depends on / 依赖: Iff.rfl
-/
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p in (Z.localTrivAt b).source ↔ p.1 in (Z.localTrivAt b).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
/--
theorem `mem_localTriv_target` / 定理 `mem_localTriv_target`

English:
theorem mem_localTriv_target
  given: (p : B × F)
  proof: Trivialization.mem_target _

@[simp, mfld_simps]

中文:
定理 mem_localTriv_target
  条件: (p : B × F)
  证明: Trivialization.mem_target _

@[simp, mfld_simps]

Depends on / 依赖: Trivialization, Trivialization.mem_target, mem_target
-/
theorem mem_localTriv_target (p : B × F) :
    p in (Z.localTriv i).target ↔ p.1 in (Z.localTriv i).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
/--
theorem `mem_localTrivAt_target` / 定理 `mem_localTrivAt_target`

English:
theorem mem_localTrivAt_target
  given: (p : B × F) (b : B)
  proof: Trivialization.mem_target _

@[simp, mfld_simps]

中文:
定理 mem_localTrivAt_target
  条件: (p : B × F) (b : B)
  证明: Trivialization.mem_target _

@[simp, mfld_simps]

Depends on / 依赖: Trivialization, Trivialization.mem_target, mem_target
-/
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p in (Z.localTrivAt b).target ↔ p.1 in (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
/--
theorem `localTriv_symm_apply` / 定理 `localTriv_symm_apply`

English:
theorem localTriv_symm_apply
  given: (p : B × F)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 localTriv_symm_apply
  条件: (p : B × F)
  证明: rfl

@[simp, mfld_simps]
-/
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
/--
theorem `mem_localTrivAt_baseSet` / 定理 `mem_localTrivAt_baseSet`

English:
theorem mem_localTrivAt_baseSet
  given: (b : B)
  statement: b in (Z.localTrivAt b).baseSet
  proof: by
  rw [localTrivAt]; rw [← baseSet_at]
  exact Z.mem_baseSet_at b

中文:
定理 mem_localTrivAt_baseSet
  条件: (b : B)
  结论: b in (Z.localTrivAt b).baseSet
  证明: by
  rw [localTrivAt]; rw [← baseSet_at]
  exact Z.mem_baseSet_at b

Depends on / 依赖: Z.mem_baseSet_at, baseSet_at, localTrivAt, mem_baseSet_at
-/
theorem mem_localTrivAt_baseSet (b : B) : b in (Z.localTrivAt b).baseSet := by
  rw [localTrivAt]; rw [← baseSet_at]
  exact Z.mem_baseSet_at b

/--
theorem `mk_mem_localTrivAt_source` / 定理 `mk_mem_localTrivAt_source`

English:
theorem mk_mem_localTrivAt_source
  statement: (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).source
  proof: by
  simp only [mfld_simps]

中文:
定理 mk_mem_localTrivAt_source
  结论: (⟨b, a⟩ : Z.全空间) in (Z.localTrivAt b).source
  证明: by
  simp only [mfld_simps]

Depends on / 依赖: mfld_simps
-/
theorem mk_mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).source := by
  simp only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `fiberBundle` / 实例 `fiberBundle`

English:
instance fiberBundle
  signature: : FiberBundle F Z.Fiber where
  body: isInducing_iff_nhds.2 fun x => by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _)]; rw [comap_inf]; rw [comap_principal]; rw [comap_comap]
    simp only [Function.comp_def, localTrivAt_apply_mk, Trivialization.coe_coe,
      ← (isEmbedding_prodMkRight b).nhds_eq_comap]
    convert_to 𝓝 x = 𝓝 x ⊓ 𝓟 univ
    · congr
      exact eq_univ_of_forall (mk_mem_localTrivAt_source Z _)
    · rw [principal_univ, inf_top_eq]
  trivializationAtlas' := Set.range Z.localTriv
  trivializationAt' := Z.localTrivAt
  mem_baseSet_trivializationAt' := Z.mem_baseSet_at
  trivialization_mem_atlas' b := ⟨Z.indexAt b, rfl⟩

中文:
实例 fiberBundle
  签名: : 纤维丛 F Z.Fiber where
  定义体: isInducing_iff_nhds.2 fun x => by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _)]; rw [comap_inf]; rw [comap_principal]; rw [comap_comap]
    simp only [Function.comp_def, localTrivAt_apply_mk, Trivialization.coe_coe,
      ← (isEmbedding_prodMkRight b).nhds_eq_comap]
    convert_to 𝓝 x = 𝓝 x ⊓ 𝓟 univ
    · congr
      exact eq_univ_of_forall (mk_mem_localTrivAt_source Z _)
    · rw [principal_univ, inf_top_eq]
  trivializationAtlas' := Set.range Z.localTriv
  trivializationAt' := Z.localTrivAt
  mem_baseSet_trivializationAt' := Z.mem_baseSet_at
  trivialization_mem_atlas' b := ⟨Z.indexAt b, rfl⟩

Depends on / 依赖: Function, Function.comp_def, Set.range, Trivialization, Trivialization.coe_coe, Z.localTr, Z.localTriv, Z.localTrivAt, coe_coe, comap_comap, comap_inf, comap_principal, comp_def, convert_to, eq_univ_of_forall, inf_top_eq, isEmbedding_prodMkRight, isInducing_iff_nhds, localTr, localTriv
-/
instance fiberBundle : FiberBundle F Z.Fiber where
  totalSpaceMk_isInducing' b := isInducing_iff_nhds.2 fun x => by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _)]; rw [comap_inf]; rw [comap_principal]; rw [comap_comap]
    simp only [Function.comp_def, localTrivAt_apply_mk, Trivialization.coe_coe,
      ← (isEmbedding_prodMkRight b).nhds_eq_comap]
    convert_to 𝓝 x = 𝓝 x ⊓ 𝓟 univ
    · congr
      exact eq_univ_of_forall (mk_mem_localTrivAt_source Z _)
    · rw [principal_univ, inf_top_eq]
  trivializationAtlas' := Set.range Z.localTriv
  trivializationAt' := Z.localTrivAt
  mem_baseSet_trivializationAt' := Z.mem_baseSet_at
  trivialization_mem_atlas' b := ⟨Z.indexAt b, rfl⟩

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
/--
theorem `continuous_totalSpaceMk` / 定理 `continuous_totalSpaceMk`

English:
theorem continuous_totalSpaceMk
  given: (b : B)
  proof: FiberBundle.continuous_totalSpaceMk F Z.Fiber b

中文:
定理 continuous_totalSpaceMk
  条件: (b : B)
  证明: FiberBundle.continuous_totalSpaceMk F Z.Fiber b

Depends on / 依赖: FiberBundle, FiberBundle.continuous_totalSpaceMk, Z.Fiber, continuous_totalSpaceMk
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous (TotalSpace.mk b : Z.Fiber b -> Bundle.TotalSpace F Z.Fiber) :=
  FiberBundle.continuous_totalSpaceMk F Z.Fiber b

/-- The projection on the base of a fiber bundle created from core is continuous -/
nonrec theorem continuous_proj : Continuous Z.proj :=
  FiberBundle.continuous_proj F Z.Fiber

/-- The projection on the base of a fiber bundle created from core is an open map -/
nonrec theorem isOpenMap_proj : IsOpenMap Z.proj :=
  FiberBundle.isOpenMap_proj F Z.Fiber

end FiberBundleCore

/-! ### Prebundle construction for constructing fiber bundles -/

variable (F)
variable (E : B -> Type*) [TopologicalSpace B] [TopologicalSpace F]
  [forall x, TopologicalSpace (E x)]

/--
Definition of `FiberPrebundle` / `FiberPrebundle` 的定义

English:
structure FiberPrebundle
  parameters: where
  axioms and operations (6):
    - pretrivializationAtlas : Set (Pretrivialization F (π F E))
    - pretrivializationAt : B -> Pretrivialization F (π F E)
    - mem_base_pretrivializationAt : forall x : B, x in (pretrivializationAt x).baseSet
    - pretrivialization_mem_atlas : forall x : B, pretrivializationAt x in pretrivializationAtlas
    - continuous_trivChange : forall e, e in pretrivializationAtlas -> forall e', e' in pretrivializationAtlas -> ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target inter e'.toPartialEquiv.symm ⁻¹' e.source)
    - totalSpaceMk_isInducing : forall b : B, IsInducing (pretrivializationAt b ∘ TotalSpace.mk b)

中文:
结构 FiberPrebundle
  参数: where
  公理与运算 (6 个):
    - pretrivializationAtlas : 集合 (Pretrivialization F (π F E))
    - pretrivializationAt : B -> Pretrivialization F (π F E)
    - mem_base_pretrivializationAt : 对任意 x : B, x in (pretrivializationAt x).baseSet
    - pretrivialization_mem_atlas : 对任意 x : B, pretrivializationAt x in pretrivializationAtlas
    - continuous_trivChange : 对任意 e, e in pretrivializationAtlas -> 对任意 e', e' in pretrivializationAtlas -> ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target inter e'.toPartialEquiv.symm ⁻¹' e.source)
    - totalSpaceMk_isInducing : 对任意 b : B, 是Inducing (pretrivializationAt b ∘ 全空间.mk b)
-/
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B -> Pretrivialization F (π F E)
  mem_base_pretrivializationAt : forall x : B, x in (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : forall x : B, pretrivializationAt x in pretrivializationAtlas
  continuous_trivChange : forall e, e in pretrivializationAtlas -> forall e', e' in pretrivializationAtlas ->
    ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target inter e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpaceMk_isInducing : forall b : B, IsInducing (pretrivializationAt b ∘ TotalSpace.mk b)

namespace FiberPrebundle

variable {F E}
variable (a : FiberPrebundle F E) {e : Pretrivialization F (π F E)}

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[instance_reducible]
/--
Definition of `totalSpaceTopology` / `totalSpaceTopology` 的定义

English:
definition totalSpaceTopology
  signature: (a : FiberPrebundle F E)
  body: ⨆ (e : Pretrivialization F (π F E)) (_ : e in a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype

中文:
定义 totalSpaceTopology
  签名: (a : FiberPrebundle F E)
  定义体: ⨆ (e : Pretrivialization F (π F E)) (_ : e in a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype

Depends on / 依赖: Pretrivialization, a.pretrivializationAtlas, coinduced, e.setSymm, instTopologicalSpaceSubtype, pretrivializationAtlas, setSymm
-/
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (_ : e in a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype

/--
theorem `continuous_symm_of_mem_pretrivializationAtlas` / 定理 `continuous_symm_of_mem_pretrivializationAtlas`

English:
theorem continuous_symm_of_mem_pretrivializationAtlas
  given: (he : e in a.pretrivializationAtlas)
  proof: by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he

中文:
定理 continuous_symm_of_mem_pretrivializationAtlas
  条件: (he : e in a.pretrivializationAtlas)
  证明: by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he

Depends on / 依赖: TopologicalSpace, TotalSpace, le_def, nhds_mono, preimage_nhdsWithin_coinduced
-/
theorem continuous_symm_of_mem_pretrivializationAtlas (he : e in a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toPartialEquiv.symm e.target := by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he

/--
theorem `isOpen_source` / 定理 `isOpen_source`

English:
theorem isOpen_source
  given: (e : Pretrivialization F (π F E))
  proof: by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, domRestrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]

中文:
定理 isOpen_source
  条件: (e : Pretrivialization F (π F E))
  证明: by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, domRestrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]

Depends on / 依赖: Pretrivialization, Pretrivialization.setSymm, domRestrict, e.mem_source, e.mem_target, e.open_target, e.target, isOpen_coinduced, isOpen_coinduced.mpr, isOpen_iSup_iff, isOpen_iSup_iff.mpr, isOpen_induced_iff, isOpen_induced_iff.mpr, mem_preimage, mem_source, mem_target, open_target, proj_symm_apply, setSymm, target
-/
theorem isOpen_source (e : Pretrivialization F (π F E)) :
    IsOpen[a.totalSpaceTopology] e.source := by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, domRestrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]

/--
theorem `isOpen_target_of_mem_pretrivializationAtlas_inter` / 定理 `isOpen_target_of_mem_pretrivializationAtlas_inter`

English:
theorem isOpen_target_of_mem_pretrivializationAtlas_inter
  statement: (e e' : Pretrivialization F (π F E))
  proof: by
  let := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm]; rw [hu2]
  exact hu1.inter e'.open_target

中文:
定理 isOpen_target_of_mem_pretrivializationAtlas_inter
  结论: (e e' : Pretrivialization F (π F E))
  证明: by
  let := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm]; rw [hu2]
  exact hu1.inter e'.open_target

Depends on / 依赖: a.continuous_symm_of_mem_pretrivializationAtlas, a.isOpen_source, a.totalSpaceTopology, continuousOn_iff, continuous_symm_of_mem_pretrivializationAtlas, e.source, hu1.inter, inter_comm, isOpen_source, open_target, source, totalSpaceTopology
-/
theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π F E))
    (he' : e' in a.pretrivializationAtlas) :
    IsOpen (e'.toPartialEquiv.target inter e'.toPartialEquiv.symm ⁻¹' e.source) := by
  let := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm]; rw [hu2]
  exact hu1.inter e'.open_target

/--
Definition of `trivializationOfMemPretrivializationAtlas` / `trivializationOfMemPretrivializationAtlas` 的定义

English:
definition trivializationOfMemPretrivializationAtlas
  signature: (he : e in a.pretrivializationAtlas)
  body: let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s inter e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced]; rw [isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u inter e'.toPartialEquiv.target inter e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }

中文:
定义 trivializationOfMemPretrivializationAtlas
  签名: (he : e in a.pretrivializationAtlas)
  定义体: let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s inter e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced]; rw [isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u inter e'.toPartialEquiv.target inter e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }

Depends on / 依赖: a.continuous_trivChange, a.isOpen_source, a.totalSpaceTopology, congr_arg, continuousOn_iff, continuousOn_toFun, continuous_trivChange, e.source, inter_assoc, inter_self, isOpen_coinduced, isOpen_iSup_iff, isOpen_iSup_iff.mpr, isOpen_induced_iff, isOpen_source, open_source, source, target, totalSpaceTopology
-/
def trivializationOfMemPretrivializationAtlas (he : e in a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s inter e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced]; rw [isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u inter e'.toPartialEquiv.target inter e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }

/--
theorem `mem_pretrivializationAt_source` / 定理 `mem_pretrivializationAt_source`

English:
theorem mem_pretrivializationAt_source
  given: (b : B) (x : E b)
  proof: by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage]
  exact a.mem_base_pretrivializationAt b

@[simp]

中文:
定理 mem_pretrivializationAt_source
  条件: (b : B) (x : E b)
  证明: by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage]
  exact a.mem_base_pretrivializationAt b

@[simp]

Depends on / 依赖: a.mem_base_pretrivializationAt, a.pretrivializationAt, mem_base_pretrivializationAt, mem_preimage, pretrivializationAt, source_eq
-/
theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    ⟨b, x⟩ in (a.pretrivializationAt b).source := by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage]
  exact a.mem_base_pretrivializationAt b

@[simp]
/--
theorem `totalSpaceMk_preimage_source` / 定理 `totalSpaceMk_preimage_source`

English:
theorem totalSpaceMk_preimage_source
  given: (b : B)
  proof: eq_univ_of_forall (a.mem_pretrivializationAt_source b)

@[continuity]

中文:
定理 totalSpaceMk_preimage_source
  条件: (b : B)
  证明: eq_univ_of_forall (a.mem_pretrivializationAt_source b)

@[continuity]

Depends on / 依赖: a.mem_pretrivializationAt_source, eq_univ_of_forall, mem_pretrivializationAt_source
-/
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  eq_univ_of_forall (a.mem_pretrivializationAt_source b)

@[continuity]
/--
theorem `continuous_totalSpaceMk` / 定理 `continuous_totalSpaceMk`

English:
theorem continuous_totalSpaceMk
  given: (b : B)
  proof: by
  let := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le

中文:
定理 continuous_totalSpaceMk
  条件: (b : B)
  证明: by
  let := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le

Depends on / 依赖: a.pretrivialization_mem_atlas, a.totalSpaceMk_isInducing, a.totalSpaceMk_preimage_source, a.totalSpaceTopology, a.trivializationOfMemPretrivializationAtlas, continuous_iff_continuous_comp_left, continuous_iff_le_induced, e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left, eq_induced, eq_induced.le, pretrivialization_mem_atlas, toOpenPartialHomeomorph, totalSpaceMk_isInducing, totalSpaceMk_preimage_source, totalSpaceTopology, trivializationOfMemPretrivializationAtlas
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (TotalSpace.mk b) := by
  let := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le

/--
theorem `inducing_totalSpaceMk_of_inducing_comp` / 定理 `inducing_totalSpaceMk_of_inducing_comp`

English:
theorem inducing_totalSpaceMk_of_inducing_comp
  statement: (b : B)
  proof: by
  let := a.totalSpaceTopology
  rw [← domRestrict_comp_codRestrict (a.mem_pretrivializationAt_source b)] at h
  apply IsInducing.of_codRestrict (a.mem_pretrivializationAt_source b)
  refine h.of_comp ?_ (continuousOn_iff_continuous_domRestrict.mp
    (a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)).continuousOn)
  exact (a.continuous_totalSpaceMk b).codRestrict (a.mem_pretrivializationAt_source b)

中文:
定理 inducing_totalSpaceMk_of_inducing_comp
  结论: (b : B)
  证明: by
  let := a.totalSpaceTopology
  rw [← domRestrict_comp_codRestrict (a.mem_pretrivializationAt_source b)] at h
  apply IsInducing.of_codRestrict (a.mem_pretrivializationAt_source b)
  refine h.of_comp ?_ (continuousOn_iff_continuous_domRestrict.mp
    (a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)).continuousOn)
  exact (a.continuous_totalSpaceMk b).codRestrict (a.mem_pretrivializationAt_source b)

Depends on / 依赖: IsInducing, IsInducing.of_codRestrict, a.continuous_totalSpaceMk, a.mem_pretrivializationAt_source, a.pretrivialization_mem_atlas, a.totalSpaceTopology, a.trivializationOfMemPretrivializationAtlas, codRestrict, continuousOn, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, continuous_totalSpaceMk, domRestrict_comp_codRestrict, h.of_comp, mem_pretrivializationAt_source, of_codRestrict, of_comp, pretrivialization_mem_atlas, totalSpaceTopology, trivializationOfMemPretrivializationAtlas
-/
theorem inducing_totalSpaceMk_of_inducing_comp (b : B)
    (h : IsInducing (a.pretrivializationAt b ∘ TotalSpace.mk b)) :
    @IsInducing _ _ _ a.totalSpaceTopology (TotalSpace.mk b) := by
  let := a.totalSpaceTopology
  rw [← domRestrict_comp_codRestrict (a.mem_pretrivializationAt_source b)] at h
  apply IsInducing.of_codRestrict (a.mem_pretrivializationAt_source b)
  refine h.of_comp ?_ (continuousOn_iff_continuous_domRestrict.mp
    (a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)).continuousOn)
  exact (a.continuous_totalSpaceMk b).codRestrict (a.mem_pretrivializationAt_source b)

/-- Make a `FiberBundle` from a `FiberPrebundle`. Concretely this means
that, given a `FiberPrebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`FiberPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
@[instance_reducible]
/--
Definition of `toFiberBundle` / `toFiberBundle` 的定义

English:
definition toFiberBundle
  signature: : @FiberBundle B F _ _ E a.totalSpaceTopology _
  body: let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b => a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | exists (e₀ : _) (he₀ : e₀ in a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x =>
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }

中文:
定义 toFiberBundle
  签名: : @纤维丛 B F _ _ E a.totalSpaceTopology _
  定义体: let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b => a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | exists (e₀ : _) (he₀ : e₀ in a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x =>
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }

Depends on / 依赖: a.inducing_totalSpaceMk_of_inducing_comp, a.mem_base_pretrivializationAt, a.pretrivializationAtlas, a.pretrivialization_mem_atlas, a.totalSpaceMk_isInducing, a.totalSpaceTopology, a.trivializationOfMemPretrivializationAtlas, inducing_totalSpaceMk_of_inducing_comp, mem_baseSet_trivializationAt, mem_base_pretrivializationAt, pretrivializationAtlas, pretrivialization_mem_atlas, totalSpaceMk_isInducing, totalSpaceTopology, trivializationAt, trivializationAtlas, trivializationOfMemPretrivializationAtlas, trivialization_mem_atlas
-/
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b => a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | exists (e₀ : _) (he₀ : e₀ in a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x =>
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }

/--
theorem `continuous_proj` / 定理 `continuous_proj`

English:
theorem continuous_proj
  statement: @Continuous _ _ a.totalSpaceTopology _ (π F E)
  proof: by
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  exact FiberBundle.continuous_proj F E

中文:
定理 continuous_proj
  结论: @连续 _ _ a.totalSpaceTopology _ (π F E)
  证明: by
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  exact FiberBundle.continuous_proj F E

Depends on / 依赖: FiberBundle, FiberBundle.continuous_proj, a.toFiberBundle, a.totalSpaceTopology, continuous_proj, toFiberBundle, totalSpaceTopology
-/
theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π F E) := by
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  exact FiberBundle.continuous_proj F E

instance {e₀} (he₀ : e₀ in a.pretrivializationAtlas) :
    (letI := a.totalSpaceTopology; letI := a.toFiberBundle
      MemTrivializationAtlas (a.trivializationOfMemPretrivializationAtlas he₀)) :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; ⟨e₀, he₀, rfl⟩

/--
theorem `continuousOn_of_comp_right` / 定理 `continuousOn_of_comp_right`

English:
theorem continuousOn_of_comp_right
  statement: {X : Type*} [TopologicalSpace X] {f : TotalSpace F E -> X}
  proof: by
  let := a.totalSpaceTopology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas z.proj)
  refine (e.continuousAt_of_comp_right ?_
    ((hf z.proj hz).continuousAt (IsOpen.mem_nhds ?_ ?_))).continuousWithinAt
  · exact a.mem_base_pretrivializationAt z.proj
  · exact (hs.inter (a.pretrivializationAt z.proj).open_baseSet).prod isOpen_univ
  refine ⟨?_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivializationAt z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivializationAt z.proj

中文:
定理 continuousOn_of_comp_right
  结论: {X : 类型} [拓扑空间 X] {f : 全空间 F E -> X}
  证明: by
  let := a.totalSpaceTopology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas z.proj)
  refine (e.continuousAt_of_comp_right ?_
    ((hf z.proj hz).continuousAt (IsOpen.mem_nhds ?_ ?_))).continuousWithinAt
  · exact a.mem_base_pretrivializationAt z.proj
  · exact (hs.inter (a.pretrivializationAt z.proj).open_baseSet).prod isOpen_univ
  refine ⟨?_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivializationAt z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivializationAt z.proj

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Trivialization, a.mem_base_pretrivializationAt, a.pretrivializationAt, a.pretrivialization_mem_atlas, a.totalSpaceTopology, a.trivializationOfMemPretrivializationAtlas, coe_fst, continuousAt, continuousAt_of_comp_right, continuousWithinAt, e.coe_fst, e.continuousAt_of_comp_right, hs.inter, isOpen_univ, mem_base_pretrivializationAt, mem_nhds, mem_univ, open_baseSet
-/
theorem continuousOn_of_comp_right {X : Type*} [TopologicalSpace X] {f : TotalSpace F E -> X}
    {s : Set B} (hs : IsOpen s) (hf : forall b in s,
      ContinuousOn (f ∘ (a.pretrivializationAt b).toPartialEquiv.symm)
        ((s inter (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (π F E ⁻¹' s) := by
  let := a.totalSpaceTopology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas z.proj)
  refine (e.continuousAt_of_comp_right ?_
    ((hf z.proj hz).continuousAt (IsOpen.mem_nhds ?_ ?_))).continuousWithinAt
  · exact a.mem_base_pretrivializationAt z.proj
  · exact (hs.inter (a.pretrivializationAt z.proj).open_baseSet).prod isOpen_univ
  refine ⟨?_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivializationAt z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivializationAt z.proj

end FiberPrebundle

namespace FiberBundle
section extend

variable {E} [(x : B) -> Zero (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: {x : B} (v₀ : E x) (x' : B)
  body: letI t := trivializationAt F E x
  letI w : F := (t ⟨x, v₀⟩).2
  -- TODO: use the `funToSec` helper from #36036 once available
  t.symm x' w

中文:
定义 extend
  签名: {x : B} (v₀ : E x) (x' : B)
  定义体: letI t := trivializationAt F E x
  letI w : F := (t ⟨x, v₀⟩).2
  -- TODO: use the `funToSec` helper from #36036 once available
  t.symm x' w

Depends on / 依赖: trivializationAt
-/
noncomputable def extend {x : B} (v₀ : E x) (x' : B) : E x' :=
  letI t := trivializationAt F E x
  letI w : F := (t ⟨x, v₀⟩).2
  -- TODO: use the `funToSec` helper from #36036 once available
  t.symm x' w

/--
lemma `extend_apply_self` / 引理 `extend_apply_self`

English:
lemma extend_apply_self
  given: {x : B} (v : E x)
  statement: extend F v x = v
  proof: by
  simp [extend, FiberBundle.mem_baseSet_trivializationAt' x]

中文:
引理 extend_apply_self
  条件: {x : B} (v : E x)
  结论: extend F v x = v
  证明: by
  simp [extend, FiberBundle.mem_baseSet_trivializationAt' x]
-/
@[simp] lemma extend_apply_self {x : B} (v : E x) : extend F v x = v := by
  simp [extend, FiberBundle.mem_baseSet_trivializationAt' x]

end extend
end FiberBundle
