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

* `Z.Fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.TotalSpace`  : the total space of `Z`, defined as `Bundle.TotalSpace F Z.Fiber` with a custom
                    topology.
* `Z.proj`        : projection from `Z.TotalSpace` to `B`. It is continuous.
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
variable [TopologicalSpace B] [TopologicalSpace F] (E : B → Type*)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
/-
**FiberBundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{B : Type u_2} →   (F : Type u_3) →     [TopologicalSpace B] →       [Topo
logicalSpace F] →         (E : B → Type u_5) →           [TopologicalSpace (Bund
le.TotalSpace F E)] → [(b : B) → TopologicalSpace (E b)] → Type (max (max u_2 u_
3) u_5)
参数：F : Type u_3；E : B → Type u_5；Bundle.TotalSpace F E；b : B；E b；max (max u_2 u_
3) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (topological) fiber bundle with fiber `F` over a base `B` is a space projectin
g on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation 
around each point
is a direct product.
-/
class FiberBundle where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt' : ∀ b : B, b ∈ (trivializationAt' b).baseSet
  trivialization_mem_atlas' : ∀ b : B, trivializationAt' b ∈ trivializationAtlas'

namespace FiberBundle

variable [FiberBundle F E] (b : B)

/-
**FiberBundle.totalSpaceMk_isInducing** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.totalSpaceMk_isInducing'`：∀ {B : Type u_2} {F : Type u_3} {i
nst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5}   {in
st_2 : TopologicalSpace (B…
-/
theorem totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b) := totalSpaceMk_isInducing' b

/-- Atlas of a fiber bundle. -/
/-
**FiberBundle.trivializationAtlas** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAtlas : Set (Trivialization F (π F E))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Atlas of a fiber bundle.
-/
abbrev trivializationAtlas : Set (Trivialization F (π F E)) := trivializationAtlas'

/-- Trivialization of a fiber bundle at a point. -/
/-
**FiberBundle.trivializationAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt : Trivialization F (π F E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Trivialization of a fiber bundle at a point.
-/
abbrev trivializationAt : Trivialization F (π F E) := trivializationAt' b
/-
**FiberBundle.mem_baseSet_trivializationAt** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundl
e`。
形式化陈述：mem_baseSet_trivializationAt : b in (trivializationAt F E b).baseSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
theorem mem_baseSet_trivializationAt : b ∈ (trivializationAt F E b).baseSet :=
  mem_baseSet_trivializationAt' b
/-
**FiberBundle.trivialization_mem_atlas** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：trivialization_mem_atlas : trivializationAt F E b in trivializationAtlas F
 E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.trivialization_mem_atlas'`：∀ {B : Type u_2} {F : Type u_3} {
inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5}   {i
nst_2 : TopologicalSpace (B…
-/
theorem trivialization_mem_atlas : trivializationAt F E b ∈ trivializationAtlas F E :=
  trivialization_mem_atlas' b

end FiberBundle

export FiberBundle (totalSpaceMk_isInducing trivializationAtlas trivializationAt
  mem_baseSet_trivializationAt trivialization_mem_atlas)

variable {F}
variable {E}

/-- Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
/-
**MemTrivializationAtlas** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{B : Type u_2} →   {F : Type u_3} →     [inst : TopologicalSpace B] →     
  [inst_1 : TopologicalSpace F] →         {E : B → Type u_5} →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [inst_3 : (b : B) → T
opologicalSpace (E b)] →               [FiberBundle F E] → Bundle.Trivialization
 F Bundle.TotalSpace.proj → Prop
参数：Bundle.TotalSpace F E；b : B；E b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typecl
ass
for trivializations of `E`, expressing that a trivialization is in the designate
d atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or
 the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functi
ons are only
expected to hold for trivializations in the designated atlas.
-/
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π F E)) : Prop where
  out : e ∈ trivializationAtlas F E
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b) where
  out := trivialization_mem_atlas F E b

namespace FiberBundle

variable (F)
variable [FiberBundle F E]

/-
**FiberBundle.map_proj_nhds** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj
参数：x : TotalSpace F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.map_proj_nhds`：∀ {B : Type u_1} {F : Type u_2} {Z 
: Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z 
→ B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
-/
theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
  (trivializationAt F E x.proj).map_proj_nhds <|
    (trivializationAt F E x.proj).mem_source.2 <| mem_baseSet_trivializationAt F E x.proj

variable (E)

/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity]
/-
**FiberBundle.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：continuous_proj : Continuous (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `FiberBundle.map_proj_nhds`：map_proj_nhds (x : TotalSpace F E) : map (π F
 E) (𝓝 x) = 𝓝 x.proj

--- 原说明 ---
The projection from a fiber bundle to its base is continuous.
-/
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

/-- The projection from a fiber bundle to its base is an open map. -/
/-
**FiberBundle.isOpenMap_proj** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：isOpenMap_proj : IsOpenMap (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `FiberBundle.map_proj_nhds`：map_proj_nhds (x : TotalSpace F E) : map (π F
 E) (𝓝 x) = 𝓝 x.proj

--- 原说明 ---
The projection from a fiber bundle to its base is an open map.
-/
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
/-
**FiberBundle.surjective_proj** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：surjective_proj [Nonempty F] : Function.Surjective (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.proj_surjOn_baseSet`：∀ {B : Type u_1} {F : Type u_
2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {pro
j : Z → B}   [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet

--- 原说明 ---
The projection from a fiber bundle with a nonempty fiber to its base is a surjec
tive
map.
-/
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩

/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
/-
**FiberBundle.isQuotientMap_proj** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `FiberBundle.isOpenMap_proj`：isOpenMap_proj : IsOpenMap (π F E)
· 使用定理 `FiberBundle.continuous_proj`：continuous_proj : Continuous (π F E)
· 使用定理 `FiberBundle.surjective_proj`：surjective_proj [Nonempty F] : Function.Sur
jective (π F E)

--- 原说明 ---
The projection from a fiber bundle with a nonempty fiber to its base is a quotie
nt
map.
-/
theorem isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E) :=
  (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)
/-
**FiberBundle.continuous_totalSpaceMk** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x)
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `FiberBundle.totalSpaceMk_isInducing`：totalSpaceMk_isInducing : IsInducin
g (@TotalSpace.mk B F E b)
-/
theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpaceMk_isInducing F E x).continuous
/-
**FiberBundle.totalSpaceMk_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x)
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.totalSpaceMk_isInducing`：totalSpaceMk_isInducing : IsInducin
g (@TotalSpace.mk B F E b)
· 使用定理 `Bundle.TotalSpace.mk_injective`：∀ {B : Type u_1} {F : Type u_2} {E : B →
 Type u_3} (b : B), Function.Injective (Bundle.TotalSpace.mk b)
-/
theorem totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩
/-
**FiberBundle.totalSpaceMk_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FiberBun
dle`。
形式化陈述：totalSpaceMk_isClosedEmbedding [T1Space B] (x : B) : IsClosedEmbedding (@T
otalSpace.mk B F E x)
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.totalSpaceMk_isEmbedding`：totalSpaceMk_isEmbedding (x : B) :
 IsEmbedding (@TotalSpace.mk B F E x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.TotalSpace.range_mk`：∀ {B : Type u_1} {F : Type u_2} {E : B → Typ
e u_3} (b : B),   Set.range (Bundle.TotalSpace.mk b) = Bundle.TotalSpace.proj ⁻¹
' {b}
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `FiberBundle.continuous_proj`：continuous_proj : Continuous (π F E)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem totalSpaceMk_isClosedEmbedding [T1Space B] (x : B) :
    IsClosedEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
    exact isClosed_singleton.preimage <| continuous_proj F E⟩

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary homeomorphism between any fiber and the model fiber.
This is useful to transfer topological properties of the model fiber. -/
/-
**FiberBundle.homeomorphAt** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundle`。
形式化陈述：homeomorphAt (b : B) : E b ≃ₜ F
参数：b : B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.totalSpaceMk_isEmbedding`：totalSpaceMk_isEmbedding (x : B) :
 IsEmbedding (@TotalSpace.mk B F E x)
· 使用定理 `Bundle.TotalSpace.range_mk`：∀ {B : Type u_1} {F : Type u_2} {E : B → Typ
e u_3} (b : B),   Set.range (Bundle.TotalSpace.mk b) = Bundle.TotalSpace.proj ⁻¹
' {b}
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…

--- 原说明 ---
An arbitrary homeomorphism between any fiber and the model fiber.
This is useful to transfer topological properties of the model fiber.
-/
noncomputable def homeomorphAt (b : B) : E b ≃ₜ F :=
  ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
    Homeomorph.setCongr <| TotalSpace.range_mk b).trans <|
    (trivializationAt F E b).preimageSingletonHomeomorph <| mem_baseSet_trivializationAt' b
/-
**FiberBundle.t0Space** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：t0Space [T0Space F] (b : B) : T0Space (E b)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y),   T0Space Y
-/
lemma t0Space [T0Space F] (b : B) : T0Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t0Space
/-
**FiberBundle.t1Space** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：t1Space [T1Space F] (b : B) : T1Space (E b)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y),   T1Space Y
-/
lemma t1Space [T1Space F] (b : B) : T1Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t1Space
/-
**FiberBundle.t2Space** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：t2Space [T2Space F] (b : B) : T2Space (E b)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
-/
lemma t2Space [T2Space F] (b : B) : T2Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t2Space
/-
**FiberBundle.t3Space** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：t3Space [T3Space F] (b : B) : T3Space (E b)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y),   T3Space Y
-/
lemma t3Space [T3Space F] (b : B) : T3Space (E b) :=
  FiberBundle.homeomorphAt F E b |>.symm.t3Space

variable {E F}

@[simp, mfld_simps]
/-
**FiberBundle.mem_trivializationAt_proj_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberB
undle`。
形式化陈述：mem_trivializationAt_proj_source {x : TotalSpace F E} : x in (trivializati
onAt F E x.proj).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
-/
theorem mem_trivializationAt_proj_source {x : TotalSpace F E} :
    x ∈ (trivializationAt F E x.proj).source :=
  (Trivialization.mem_source _).mpr <| mem_baseSet_trivializationAt F E x.proj
/-
**FiberBundle.trivializationAt_proj_fst** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：trivializationAt_proj_fst {x : TotalSpace F E} : ((trivializationAt F E x.
proj) x).1 = x.proj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
-/
theorem trivializationAt_proj_fst {x : TotalSpace F E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
  Trivialization.coe_fst' _ <| mem_baseSet_trivializationAt F E x.proj

variable (F)

open Trivialization

/-- Characterization of continuous functions (at a point, within a set) into a fiber bundle. -/
/-
**FiberBundle.continuousWithinAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 `FiberBund
le`。
形式化陈述：continuousWithinAt_totalSpace (f : X -> TotalSpace F E) {s : Set X} {x₀ : 
X} : ContinuousWithinAt f s x₀ ↔ ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
 ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀
参数：f : X -> TotalSpace F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.tendsto_nhds_iff`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_trivializationAt_proj_source`：mem_trivializationAt_proj_
source {x : TotalSpace F E} : x in (trivializationAt F E x.proj).source

--- 原说明 ---
Characterization of continuous functions (at a point, within a set) into a fiber
 bundle.
-/
theorem continuousWithinAt_totalSpace (f : X → TotalSpace F E) {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
        ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/-- Characterization of continuous functions (at a point) into a fiber bundle. -/
/-
**FiberBundle.continuousAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：continuousAt_totalSpace (f : X -> TotalSpace F E) {x₀ : X} : ContinuousAt 
f x₀ ↔ ContinuousAt (fun x => (f x).proj) x₀ ∧ ContinuousAt (fun x => ((triviali
zationAt F E (f x₀).proj) (f x)).2) x₀
参数：f : X -> TotalSpace F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.tendsto_nhds_iff`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_trivializationAt_proj_source`：mem_trivializationAt_proj_
source {x : TotalSpace F E} : x in (trivializationAt F E x.proj).source

--- 原说明 ---
Characterization of continuous functions (at a point) into a fiber bundle.
-/
theorem continuousAt_totalSpace (f : X → TotalSpace F E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source

/-- Characterization of continuous sections within a set at a point of a vector bundle. -/
/-
**FiberBundle.continuousWithinAt_section** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`
。
形式化陈述：continuousWithinAt_section {s : forall x, E x} {a : Set B} {x₀ : B} : Cont
inuousWithinAt (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔ ContinuousWithinAt (fu
n x => (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x

--- 原说明 ---
Characterization of continuous sections within a set at a point of a vector bund
le.
-/
theorem continuousWithinAt_section {s : ∀ x, E x} {a : Set B} {x₀ : B} :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x)) a x₀ ↔
      ContinuousWithinAt (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [continuousWithinAt_totalSpace, and_iff_right_iff_imp]
  intro; exact continuousWithinAt_id

/-- Characterization of continuous sections of a vector bundle. -/
/-
**FiberBundle.continuousAt_section** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：continuousAt_section {s : forall x, E x} (x₀ : B) : ContinuousAt (fun x =>
 TotalSpace.mk' F x (s x)) x₀ ↔ ContinuousAt (fun x => (trivializationAt F E x₀ 
⟨x, s x⟩).2) x₀
参数：x₀ : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.continuousWithinAt_section`：continuousWithinAt_section {s : 
forall x, E x} {a : Set B} {x₀ : B} : ContinuousWithinAt (fun x => TotalSpace.mk
' F x (s x)) a x₀ ↔ Continuo…

--- 原说明 ---
Characterization of continuous sections of a vector bundle.
-/
theorem continuousAt_section {s : ∀ x, E x} (x₀ : B) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContinuousAt (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_section F

end FiberBundle

variable (F)
variable (E)

/-- If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
/-
**FiberBundle.exists_trivialization_Icc_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearO
rder B] [OrderTopology B] [FiberBundle F E] (a b : B) : exists e : Trivializatio
n F (π F E), Icc a b subseteq e.baseSet
参数：a b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset`：mem_nhdsLE_iff_exists_mem_Ico_
Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<=] a ↔ exists l in Ic
o l' a, Ioc l a subseteq s
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `IsLUB.exists_between`：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) 
: exists c in s, b < c ∧ c <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.subset_ite`：subset_ite {t s s' u : Set α} : u subseteq t.ite s s' ↔ 
u inter t subseteq s ∧ u \ t subseteq s'
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset`：mem_nhdsGE_iff_exists_mem_Ioc_
Ico_subset {a u' : α} {s : Set α} (hu' : a < u') : s in 𝓝[>=] a ↔ exists u in Io
c a u', Ico a u subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Icc_union_Ico`：Ico_subset_Icc_union_Ico : Ico a c subsete
q Icc a b union Ico b c
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval.
-/
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    ∃ e : Trivialization F (π F E), Icc a b ⊆ e.baseSet := by
  obtain ⟨ea, hea⟩ : ∃ ea : Trivialization F (π F E), a ∈ ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
  rcases lt_or_ge b a with _ | hab
  · exact ⟨ea, by simp [*]⟩
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x ∈ Icc a b | ∃ e : Trivialization F (π F E), Icc a x ⊆ e.baseSet }
  have ha : a ∈ s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c ⊆ ec.baseSet⟩ : c ∈ s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
      of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : ∃ ec : Trivialization F (π F E), c ∈ ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
      `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, ∃ e : Trivialization F (π F E), Icc a d ⊆ e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_gt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d ⊆ ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
      Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
      a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : ∃ ed : Trivialization F (π F E), d ∈ ed.baseSet :=
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

/-- Core data defining a locally trivial bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `baseSet i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coordChange i j` from
`baseSet i ∩ baseSet j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(baseSet i ∩ baseSet j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
/-
**FiberBundleCore** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → (B : Type u_6) → [TopologicalSpace B] → (F : Type u_7) → [Topol
ogicalSpace F] → Type (max (max u_5 u_6) u_7)
参数：B : Type u_6；F : Type u_7；max (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Core data defining a locally trivial bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (co
mputer science)
bundled version, i.e., all the relevant data is contained in the following struc
ture. A family of
local trivializations is indexed by a type `ι`, on open subsets `baseSet i` for 
each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coordChange
 i j` from
`baseSet i ∩ baseSet j` to the set of homeomorphisms of `F`, but we express them
 as maps
`B → F → F` and require continuity on `(baseSet i ∩ baseSet j) × F` to avoid the
 topology on the
space of continuous maps on `F`.
-/
structure FiberBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v

namespace FiberBundleCore

variable [TopologicalSpace B] [TopologicalSpace F] (Z : FiberBundleCore ι B F)

/-- The index set of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments]
/-
**FiberBundleCore.Index** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：Index (_Z : FiberBundleCore ι B F)
参数：_Z : FiberBundleCore ι B F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index set of a fiber bundle core, as a convenience function for dot notation
-/
def Index (_Z : FiberBundleCore ι B F) := ι

/-- The base space of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unusedArguments, reducible]
/-
**FiberBundleCore.Base** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：Base (_Z : FiberBundleCore ι B F)
参数：_Z : FiberBundleCore ι B F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base space of a fiber bundle core, as a convenience function for dot notatio
n
-/
def Base (_Z : FiberBundleCore ι B F) := B

/-- The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unusedArguments]
/-
**FiberBundleCore.Fiber** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：Fiber (_ : FiberBundleCore ι B F) (_x : B)
参数：_ : FiberBundleCore ι B F；_x : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference
-/
def Fiber (_ : FiberBundleCore ι B F) (_x : B) := F
/-
**FiberBundleCore.topologicalSpaceFiber** 是 Mathlib 中的一个实例，位于命名空间 `FiberBundleCo
re`。
形式化陈述：topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x)
参数：x : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := ‹_›

/-- The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`. -/
/-
**FiberBundleCore.TotalSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiberBundleCore`。
形式化陈述：TotalSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `Bundle.TotalSpace F Z.Fiber`.
-/
abbrev TotalSpace := Bundle.TotalSpace F Z.Fiber

/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
/-
**FiberBundleCore.proj** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：proj : Z.TotalSpace -> B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the total space of a fiber bundle core, on its base.
-/
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj

/-- Local homeomorphism version of the trivialization change. -/
/-
**FiberBundleCore.trivChange** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) where source
参数：i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local homeomorphism version of the trivialization change.
-/
def trivChange (i j : ι) : OpenPartialHomeomorph (B × F) (B × F) where
  source := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp, Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prodMk (Z.continuousOn_coordChange j i)

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_trivChange_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCo
re`。
形式化陈述：mem_trivChange_source (i j : ι) (p : B × F) : p in (Z.trivChange i j).sour
ce ↔ p.1 in Z.baseSet i inter Z.baseSet j
参数：i j : ι；p : B × F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundleCore.trivChange.eq_1`：∀ {ι : Type u_1} {B : Type u_2} {F : Ty
pe u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (Z : FiberBu
ndleCore ι B F) (i j …
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j := by
  rw [trivChange, mem_prod]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (baseSet i)` and `baseSet i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be an open partial homeomorphism. For now, we only
introduce the partial equivalence version, denoted with a prime.
In further developments, avoid this auxiliary version, and use `Z.local_triv` instead. -/
/-
**FiberBundleCore.localTrivAsPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundle
Core`。
形式化陈述：localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F) where 
source
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate to a trivialization index `i : ι` the corresponding trivialization, i.
e., a bijection
between `proj ⁻¹ (baseSet i)` and `baseSet i × F`. As the fiber above `x` is `F`
 but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by def
inition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be an open partial homeomorphism. For n
ow, we only
introduce the partial equivalence version, denoted with a prime.
In further developments, avoid this auxiliary version, and use `Z.local_triv` in
stead.
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
    replace hx : x ∈ Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prodMk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]

variable (i : ι)
/-
**FiberBundleCore.mem_localTrivAsPartialEquiv_source** 是 Mathlib 中的一个定理，位于命名空间 `
FiberBundleCore`。
形式化陈述：mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) : p in (Z.localTrivA
sPartialEquiv i).source ↔ p.1 in Z.baseSet i
参数：p : Z.TotalSpace。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsPartialEquiv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl
/-
**FiberBundleCore.mem_localTrivAsPartialEquiv_target** 是 Mathlib 中的一个定理，位于命名空间 `
FiberBundleCore`。
形式化陈述：mem_localTrivAsPartialEquiv_target (p : B × F) : p in (Z.localTrivAsPartia
lEquiv i).target ↔ p.1 in Z.baseSet i
参数：p : B × F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundleCore.localTrivAsPartialEquiv.eq_1`：∀ {ι : Type u_1} {B : Type
 u_2} {F : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]  
 (Z : FiberBundleCore ι B F) (i : …
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_localTrivAsPartialEquiv_target (p : B × F) :
    p ∈ (Z.localTrivAsPartialEquiv i).target ↔ p.1 ∈ Z.baseSet i := by
  rw [localTrivAsPartialEquiv, mem_prod]
  simp only [and_true, mem_univ]
/-
**FiberBundleCore.localTrivAsPartialEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fiber
BundleCore`。
形式化陈述：localTrivAsPartialEquiv_apply (p : Z.TotalSpace) : (Z.localTrivAsPartialEq
uiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
参数：p : Z.TotalSpace。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAsPartialEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsPartialEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

/-- The composition of two local trivializations is the trivialization change `Z.trivChange i j`. -/
/-
**FiberBundleCore.localTrivAsPartialEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Fiber
BundleCore`。
形式化陈述：localTrivAsPartialEquiv_trans (i j : ι) : (Z.localTrivAsPartialEquiv i).sy
mm.trans (Z.localTrivAsPartialEquiv j) ≈ (Z.trivChange i j).toPartialEquiv
参数：i j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiberBundleCore.coordChange_comp`：∀ {ι : Type u_5} {B : Type u_6} [inst 
: TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fib
erBundleCore ι B F) (i…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The composition of two local trivializations is the trivialization change `Z.tri
vChange i j`.
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

/-- Topological structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
/-
**FiberBundleCore.toTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `FiberBundleCore`
。
形式化陈述：toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topological structure on the total space of a fiber bundle created from core, de
signed so
that all the local trivialization are continuous.
-/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber) :=
  TopologicalSpace.generateFrom <| ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source ∩ Z.localTrivAsPartialEquiv i ⁻¹' s}

variable (b : B) (a : F)
/-
**FiberBundleCore.open_source'** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `FiberBundleCore.isOpen_baseSet`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (i…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prodMk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
/-
**FiberBundleCore.localTriv** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：localTriv (i : ι) : Trivialization F Z.proj where baseSet
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.open_source'`：open_source' (i : ι) : IsOpen (Z.localTriv
AsPartialEquiv i).source
· 使用定理 `FiberBundleCore.isOpen_baseSet`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (i…

--- 原说明 ---
Extended version of the local trivialization of a fiber bundle constructed from 
core,
registering additionally in its type that it is a local bundle trivialization.
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
    refine continuousOn_isOpen_of_generateFrom fun t ht ↦ ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source ∩ localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [preimage_inter]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert! this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
/-
**FiberBundleCore.localTrivAt** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundleCore`。
形式化陈述：localTrivAt (b : B) : Trivialization F (π F Z.Fiber)
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preferred local trivialization of a fiber bundle constructed from core, at a giv
en point, as
a bundle trivialization
-/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAt_def** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b
参数：b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
/-
**FiberBundleCore.localTrivAt_snd** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：localTrivAt_snd (b : B) (p) : (Z.localTrivAt b p).2 = Z.coordChange (Z.ind
exAt p.1) (Z.indexAt b) p.1 p.2
参数：b : B；p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAt_snd (b : B) (p) :
    (Z.localTrivAt b p).2 = Z.coordChange (Z.indexAt p.1) (Z.indexAt b) p.1 p.2 :=
  rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
/-
**FiberBundleCore.continuous_const_section** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundl
eCore`。
形式化陈述：continuous_const_section (v : F) (h : forall i j, forall x in Z.baseSet i 
inter Z.baseSet j, Z.coordChange i j x v = v) : Continuous (show B -> Z.TotalSpa
ce from fun x => ⟨x, v⟩)
参数：v : F；h : forall i j, forall x in Z.baseSet i inter Z.baseSet j, Z.coordChang
e i j x v = v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `FiberBundleCore.isOpen_baseSet`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (i…
· 使用定理 `FiberBundleCore.mem_baseSet_at`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (x…
· 使用定理 `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left`：continuou
sAt_iff_continuousAt_comp_left {f : Z -> X} {x : Z} (h : f ⁻¹' e.source in 𝓝 x) 
: ContinuousAt f x ↔ ContinuousAt (e ∘ f) x
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s

--- 原说明 ---
If an element of `F` is invariant under all coordinate changes, then one can def
ine a
corresponding section of the fiber bundle, which is continuous. This applies in 
particular to the
zero section of a vector bundle. Another example (not yet defined) would be the 
identity
section of the endomorphism bundle of a vector bundle.
-/
theorem continuous_const_section (v : F)
    (h : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, Z.coordChange i j x v = v) :
    Continuous (show B → Z.TotalSpace from fun x => ⟨x, v⟩) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) ∈ 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prodMk
    simp only [mfld_simps]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy ↦ ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAsPartialEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `FiberBu
ndleCore`。
形式化陈述：localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv
 i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAsPartialEquiv_source** 是 Mathlib 中的一个定理，位于命名空间 `Fibe
rBundleCore`。
形式化陈述：localTrivAsPartialEquiv_source : (Z.localTrivAsPartialEquiv i).source = (Z
.localTriv i).source
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAsPartialEquiv_source :
    (Z.localTrivAsPartialEquiv i).source = (Z.localTriv i).source :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAsPartialEquiv_target** 是 Mathlib 中的一个定理，位于命名空间 `Fibe
rBundleCore`。
形式化陈述：localTrivAsPartialEquiv_target : (Z.localTrivAsPartialEquiv i).target = (Z
.localTriv i).target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAsPartialEquiv_target :
    (Z.localTrivAsPartialEquiv i).target = (Z.localTriv i).target :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAsPartialEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `FiberB
undleCore`。
形式化陈述：localTrivAsPartialEquiv_symm : (Z.localTrivAsPartialEquiv i).symm = (Z.loc
alTriv i).toPartialEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTrivAsPartialEquiv_symm :
    (Z.localTrivAsPartialEquiv i).symm = (Z.localTriv i).toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.baseSet_at** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.localTriv_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：localTriv_apply (p : Z.TotalSpace) : (Z.localTriv i) p = ⟨p.1, Z.coordChan
ge (Z.indexAt p.1) i p.1 p.2⟩
参数：p : Z.TotalSpace。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCore`。
形式化陈述：localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩
参数：p : Z.TotalSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundleCore.localTrivAt.eq_1`：∀ {ι : Type u_1} {B : Type u_2} {F : T
ype u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (Z : FiberB
undleCore ι B F) (b : …
· 使用定理 `FiberBundleCore.localTriv_apply`：localTriv_apply (p : Z.TotalSpace) : (Z
.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
· 使用定理 `FiberBundleCore.coordChange_self`：∀ {ι : Type u_5} {B : Type u_6} [inst 
: TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fib
erBundleCore ι B F) (i…
· 使用定理 `FiberBundleCore.mem_baseSet_at`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (x…
-/
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [localTrivAt, localTriv_apply, coordChange_self]
  exact Z.mem_baseSet_at p.1

@[simp, mfld_simps]
/-
**FiberBundleCore.localTrivAt_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCor
e`。
形式化陈述：localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩
参数：b : B；a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.localTrivAt_apply`：localTrivAt_apply (p : Z.TotalSpace) 
: (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩
-/
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_localTriv_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCor
e`。
形式化陈述：mem_localTriv_source (p : Z.TotalSpace) : p in (Z.localTriv i).source ↔ p.
1 in (Z.localTriv i).baseSet
参数：p : Z.TotalSpace。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTriv i).source ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_localTrivAt_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleC
ore`。
形式化陈述：mem_localTrivAt_source (p : Z.TotalSpace) (b : B) : p in (Z.localTrivAt b)
.source ↔ p.1 in (Z.localTrivAt b).baseSet
参数：p : Z.TotalSpace；b : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).source ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Iff.rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_localTriv_target** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCor
e`。
形式化陈述：mem_localTriv_target (p : B × F) : p in (Z.localTriv i).target ↔ p.1 in (Z
.localTriv i).baseSet
参数：p : B × F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_localTrivAt_target** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleC
ore`。
形式化陈述：mem_localTrivAt_target (p : B × F) (b : B) : p in (Z.localTrivAt b).target
 ↔ p.1 in (Z.localTrivAt b).baseSet
参数：p : B × F；b : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p ∈ (Z.localTrivAt b).target ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
/-
**FiberBundleCore.localTriv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundleCor
e`。
形式化陈述：localTriv_symm_apply (p : B × F) : (Z.localTriv i).toOpenPartialHomeomorph
.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
参数：p : B × F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toOpenPartialHomeomorph.symm p =
      ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
/-
**FiberBundleCore.mem_localTrivAt_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle
Core`。
形式化陈述：mem_localTrivAt_baseSet (b : B) : b in (Z.localTrivAt b).baseSet
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundleCore.localTrivAt.eq_1`：∀ {ι : Type u_1} {B : Type u_2} {F : T
ype u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   (Z : FiberB
undleCore ι B F) (b : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiberBundleCore.baseSet_at`：baseSet_at : Z.baseSet i = (Z.localTriv i).b
aseSet
· 使用定理 `FiberBundleCore.mem_baseSet_at`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (x…
-/
theorem mem_localTrivAt_baseSet (b : B) : b ∈ (Z.localTrivAt b).baseSet := by
  rw [localTrivAt, ← baseSet_at]
  exact Z.mem_baseSet_at b
/-
**FiberBundleCore.mk_mem_localTrivAt_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberBund
leCore`。
形式化陈述：mk_mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) in (Z.localTrivAt b).s
ource
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mk_mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  simp only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-- A fiber bundle constructed from core is indeed a fiber bundle. -/
/-
**FiberBundleCore.fiberBundle** 是 Mathlib 中的一个实例，位于命名空间 `FiberBundleCore`。
形式化陈述：fiberBundle : FiberBundle F Z.Fiber where totalSpaceMk_isInducing' b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundleCore.mem_baseSet_at`：∀ {ι : Type u_5} {B : Type u_6} [inst : 
TopologicalSpace B] {F : Type u_7} [inst_1 : TopologicalSpace F]   (self : Fiber
BundleCore ι B F) (x…

--- 原说明 ---
A fiber bundle constructed from core is indeed a fiber bundle.
-/
instance fiberBundle : FiberBundle F Z.Fiber where
  totalSpaceMk_isInducing' b := isInducing_iff_nhds.2 fun x ↦ by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _), comap_inf,
      comap_principal, comap_comap]
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
/-
**FiberBundleCore.continuous_totalSpaceMk** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle
Core`。
形式化陈述：continuous_totalSpaceMk (b : B) : Continuous (TotalSpace.mk b : Z.Fiber b 
-> Bundle.TotalSpace F Z.Fiber)
参数：b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuous_totalSpaceMk`：continuous_totalSpaceMk (x : B) : C
ontinuous (@TotalSpace.mk B F E x)

--- 原说明 ---
The inclusion of a fiber into the total space is a continuous map.
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous (TotalSpace.mk b : Z.Fiber b → Bundle.TotalSpace F Z.Fiber) :=
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
variable (E : B → Type*) [TopologicalSpace B] [TopologicalSpace F]
  [∀ x, TopologicalSpace (E x)]

/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the partial equivalences
are also open partial homeomorphisms and hence local trivializations. -/
/-
**FiberPrebundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{B : Type u_2} →   (F : Type u_3) →     (E : B → Type u_5) →       [Topolo
gicalSpace B] → [TopologicalSpace F] → [(x : B) → TopologicalSpace (E x)] → Type
 (max (max u_2 u_3) u_5)
参数：F : Type u_3；E : B → Type u_5；x : B；E x；max (max u_2 u_3) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure permits to define a fiber bundle when trivializations are given a
s local
equivalences but there is not yet a topology on the total space. The total space
 is hence given a
topology in such a way that there is a fiber bundle structure for which the part
ial equivalences
are also open partial homeomorphisms and hence local trivializations.
-/
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  continuous_trivChange : ∀ e, e ∈ pretrivializationAtlas → ∀ e', e' ∈ pretrivializationAtlas →
    ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpaceMk_isInducing : ∀ b : B, IsInducing (pretrivializationAt b ∘ TotalSpace.mk b)

namespace FiberPrebundle

variable {F E}
variable (a : FiberPrebundle F E) {e : Pretrivialization F (π F E)}

/-- Topology on the total space that will make the prebundle into a bundle. -/
@[instance_reducible]
/-
**FiberPrebundle.totalSpaceTopology** 是 Mathlib 中的一个定义，位于命名空间 `FiberPrebundle`。
形式化陈述：{B : Type u_2} →   {F : Type u_3} →     {E : B → Type u_5} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : (x : B) → TopologicalSpace (E x)] → FiberPrebundle F E → TopologicalSpace (Bu
ndle.TotalSpace F E)
参数：x : B；E x；Bundle.TotalSpace F E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on the total space that will make the prebundle into a bundle.
-/
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (_ : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype
/-
**FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas** 是 Mathlib 中的一个定
理，位于命名空间 `FiberPrebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E)   {e : Bundle.Pretrivialization F Bundle.TotalSpace.pr
oj},   e ∈ a.pretrivializationAtlas → ContinuousOn (↑e.symm) e.target
参数：x : B；E x；a : FiberPrebundle F E；↑e.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_nhdsWithin_coinduced'`：preimage_nhdsWithin_coinduced' {X : α ->
 β} {s : Set β} {t : Set α} {a : α} (h : a in t) (hs : s in @nhds β (.coinduced 
(fun x : t => X x) i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem continuous_symm_of_mem_pretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toPartialEquiv.symm e.target := by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he
/-
**FiberPrebundle.isOpen_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberPrebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E)   (e : Bundle.Pretrivialization F Bundle.TotalSpace.pr
oj), IsOpen e.source
参数：x : B；E x；a : FiberPrebundle F E；e : Bundle.Pretrivialization F Bundle.TotalS
pace.proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iSup_iff`：isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ fora
ll i, IsOpen[t i] s
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Bundle.Pretrivialization.open_target`：∀ {B : Type u_1} {F : Type u_2} {Z
 : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z
 → B}   (self : Bundle.Pre…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
· 使用定理 `Bundle.Pretrivialization.mem_source`：mem_source : x in e.source ↔ proj x
 in e.baseSet
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply`：proj_symm_apply {x : B × F} (h
x : x in e.target) : proj (e.toPartialEquiv.symm x) = x.1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_source (e : Pretrivialization F (π F E)) :
    IsOpen[a.totalSpaceTopology] e.source := by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, domRestrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]
/-
**FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_inter** 是 Mathlib 中
的一个定理，位于命名空间 `FiberPrebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E)   (e e' : Bundle.Pretrivialization F Bundle.TotalSpace
.proj),   e' ∈ a.pretrivializationAtlas → IsOpen (e'.target ∩ ↑e'.symm ⁻¹' e.sou
rce)
参数：x : B；E x；a : FiberPrebundle F E；e e' : Bundle.Pretrivialization F Bundle.Tot
alSpace.proj；e'.target ∩ ↑e'.symm ⁻¹' e.source。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas`：∀ {B : Typ
e u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : T
opologicalSpace F]   [inst_2 : (x : B) → Topologic…
· 使用定理 `FiberPrebundle.isOpen_source`：∀ {B : Type u_2} {F : Type u_3} {E : B → T
ype u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : (
x : B) → Topologic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Pretrivialization.open_target`：∀ {B : Type u_1} {F : Type u_2} {Z
 : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z
 → B}   (self : Bundle.Pre…
-/
theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π F E))
    (he' : e' ∈ a.pretrivializationAtlas) :
    IsOpen (e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source) := by
  let := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target

/-- Promotion from a `Pretrivialization` to a `Trivialization`. -/
/-
**FiberPrebundle.trivializationOfMemPretrivializationAtlas** 是 Mathlib 中的一个定义，位于
命名空间 `FiberPrebundle`。
形式化陈述：{B : Type u_2} →   {F : Type u_3} →     {E : B → Type u_5} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : (x : B) → TopologicalSpace (E x)] →             (a : FiberPrebundle F E) →   
            {e : Bundle.Pretrivialization F Bundle.TotalSpace.proj} →           
      e ∈ a.pretrivializationAtlas → Bundle.Trivialization F Bundle.TotalSpace.p
roj
参数：x : B；E x；a : FiberPrebundle F E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas`：∀ {B : Typ
e u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : T
opologicalSpace F]   [inst_2 : (x : B) → Topologic…
· 使用定理 `FiberPrebundle.isOpen_source`：∀ {B : Type u_2} {F : Type u_3} {E : B → T
ype u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : (
x : B) → Topologic…

--- 原说明 ---
Promotion from a `Pretrivialization` to a `Trivialization`.
-/
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s ∩ e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u ∩ e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }
/-
**FiberPrebundle.mem_pretrivializationAt_source** 是 Mathlib 中的一个定理，位于命名空间 `Fiber
Prebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E) (b : B) (x : E b),   ⟨b, x⟩ ∈ (a.pretrivializationAt b
).source
参数：x : B；E x；a : FiberPrebundle F E；b : B；x : E b；a.pretrivializationAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `FiberPrebundle.mem_base_pretrivializationAt`：∀ {B : Type u_2} {F : Type 
u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : (x : B) → Topologic…
-/
theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    ⟨b, x⟩ ∈ (a.pretrivializationAt b).source := by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage]
  exact a.mem_base_pretrivializationAt b

@[simp]
/-
**FiberPrebundle.totalSpaceMk_preimage_source** 是 Mathlib 中的一个定理，位于命名空间 `FiberPr
ebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E) (b : B),   Bundle.TotalSpace.mk b ⁻¹' (a.pretrivializa
tionAt b).source = Set.univ
参数：x : B；E x；a : FiberPrebundle F E；b : B；a.pretrivializationAt b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `FiberPrebundle.mem_pretrivializationAt_source`：∀ {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace
 F]   [inst_2 : (x : B) → Topologic…
-/
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  eq_univ_of_forall (a.mem_pretrivializationAt_source b)

@[continuity]
/-
**FiberPrebundle.continuous_totalSpaceMk** 是 Mathlib 中的一个定理，位于命名空间 `FiberPrebund
le`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E) (b : B), Continuous (Bundle.TotalSpace.mk b)
参数：x : B；E x；a : FiberPrebundle F E；b : B；Bundle.TotalSpace.mk b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.pretrivialization_mem_atlas`：∀ {B : Type u_2} {F : Type u
_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
   [inst_2 : (x : B) → Topologic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.continuous_iff_continuous_comp_left`：continuous_if
f_continuous_comp_left {f : Z -> X} (h : f ⁻¹' e.source = univ) : Continuous f ↔
 Continuous (e ∘ f)
· 使用定理 `FiberPrebundle.totalSpaceMk_preimage_source`：∀ {B : Type u_2} {F : Type 
u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : (x : B) → Topologic…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `FiberPrebundle.totalSpaceMk_isInducing`：∀ {B : Type u_2} {F : Type u_3} 
{E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [
inst_2 : (x : B) → Topologic…
-/
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (TotalSpace.mk b) := by
  let := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le
/-
**FiberPrebundle.inducing_totalSpaceMk_of_inducing_comp** 是 Mathlib 中的一个定理，位于命名空
间 `FiberPrebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E) (b : B),   Topology.IsInducing (↑(a.pretrivializationA
t b) ∘ Bundle.TotalSpace.mk b) →     Topology.IsInducing (Bundle.TotalSpace.mk b
)
参数：x : B；E x；a : FiberPrebundle F E；b : B；↑(a.pretrivializationAt b) ∘ Bundle.To
talSpace.mk b；Bundle.TotalSpace.mk b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.of_codRestrict`：Topology.IsInducing.of_codRestrict {
f : X -> Y} {t : Set Y} (ht : forall x, f x in t) (h : IsInducing (t.codRestrict
 f ht)) : IsInducing f
· 使用定理 `FiberPrebundle.mem_pretrivializationAt_source`：∀ {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace
 F]   [inst_2 : (x : B) → Topologic…
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `FiberPrebundle.pretrivialization_mem_atlas`：∀ {B : Type u_2} {F : Type u
_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
   [inst_2 : (x : B) → Topologic…
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `FiberPrebundle.continuous_totalSpaceMk`：∀ {B : Type u_2} {F : Type u_3} 
{E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [
inst_2 : (x : B) → Topologic…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Bundle.Trivialization.continuousOn`：∀ {B : Type u_1} {F : Type u_2} {E :
 B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst
_2 : TopologicalSpace (B…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.domRestrict_comp_codRestrict`：domRestrict_comp_codRestrict {f : ι ->
 α} {g : α -> β} {b : Set α} (h : forall x, f x in b) : b.domRestrict g ∘ b.codR
estrict f h = g ∘ f
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

/-- Make a `FiberBundle` from a `FiberPrebundle`.  Concretely this means
that, given a `FiberPrebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`FiberPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
@[instance_reducible]
/-
**FiberPrebundle.toFiberBundle** 是 Mathlib 中的一个定义，位于命名空间 `FiberPrebundle`。
形式化陈述：{B : Type u_2} →   {F : Type u_3} →     {E : B → Type u_5} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : (x : B) → TopologicalSpace (E x)] → (a : FiberPrebundle F E) → FiberBundle F 
E
参数：x : B；E x；a : FiberPrebundle F E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.pretrivialization_mem_atlas`：∀ {B : Type u_2} {F : Type u
_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
   [inst_2 : (x : B) → Topologic…
· 使用定理 `FiberPrebundle.mem_base_pretrivializationAt`：∀ {B : Type u_2} {F : Type 
u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : (x : B) → Topologic…

--- 原说明 ---
Make a `FiberBundle` from a `FiberPrebundle`.  Concretely this means
that, given a `FiberPrebundle` structure for a sigma-type `E` -- which consists 
of a
number of "pretrivializations" identifying parts of `E` with product spaces `U ×
 F` -- one
establishes that for the topology constructed on the sigma-type using
`FiberPrebundle.totalSpaceTopology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology
).
-/
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b ↦ a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x ↦
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x ↦ ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }
/-
**FiberPrebundle.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 `FiberPrebundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E), Continuous Bundle.TotalSpace.proj
参数：x : B；E x；a : FiberPrebundle F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuous_proj`：continuous_proj : Continuous (π F E)
-/
theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π F E) := by
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  exact FiberBundle.continuous_proj F E
/-
**FiberPrebundle.** 是 Mathlib 中的一个实例，位于命名空间 `FiberPrebundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {e₀} (he₀ : e₀ ∈ a.pretrivializationAtlas) :
    (letI := a.totalSpaceTopology; letI := a.toFiberBundle
      MemTrivializationAtlas (a.trivializationOfMemPretrivializationAtlas he₀)) :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; ⟨e₀, he₀, rfl⟩

/-- For a fiber bundle `E` over `B` constructed using the `FiberPrebundle` mechanism,
continuity of a function `TotalSpace F E → X` on an open set `s` can be checked by precomposing at
each point with the pretrivialization used for the construction at that point. -/
/-
**FiberPrebundle.continuousOn_of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `FiberPreb
undle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_3} {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 (a : FiberPrebundle F E) {X : Type u_6} [inst_3 : TopologicalSpace X]   {f : Bu
ndle.TotalSpace F E → X} {s : Set B},   IsOpen s →     (∀ b ∈ s,         Continu
ousOn (f ∘ ↑(a.pretrivializationAt b).symm) ((s ∩ (a.pretrivializationAt b).base
Set) ×ˢ Set.univ)) →       ContinuousOn f (Bundle.TotalSpace.proj ⁻¹' s)
参数：x : B；E x；a : FiberPrebundle F E；∀ b ∈ s,         ContinuousOn (f ∘ ↑(a.pretr
ivializationAt b).symm) ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ Set.univ)；Bu
ndle.TotalSpace.proj ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberPrebundle.pretrivialization_mem_atlas`：∀ {B : Type u_2} {F : Type u
_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
   [inst_2 : (x : B) → Topologic…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Bundle.Trivialization.continuousAt_of_comp_right`：∀ {B : Type u_1} {F : 
Type u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace 
F] {proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `FiberPrebundle.mem_base_pretrivializationAt`：∀ {B : Type u_2} {F : Type 
u_3} {E : B → Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
]   [inst_2 : (x : B) → Topologic…
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Pretrivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   (self : Bundle.Pre…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
For a fiber bundle `E` over `B` constructed using the `FiberPrebundle` mechanism
,
continuity of a function `TotalSpace F E → X` on an open set `s` can be checked 
by precomposing at
each point with the pretrivialization used for the construction at that point.
-/
theorem continuousOn_of_comp_right {X : Type*} [TopologicalSpace X] {f : TotalSpace F E → X}
    {s : Set B} (hs : IsOpen s) (hf : ∀ b ∈ s,
      ContinuousOn (f ∘ (a.pretrivializationAt b).toPartialEquiv.symm)
        ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
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

variable {E} [(x : B) → Zero (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
-/
/-
**FiberBundle.extend** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundle`。
形式化陈述：{B : Type u_2} →   (F : Type u_3) →     {E : B → Type u_5} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : (x : B) → TopologicalSpace (E x)] →             [(x : B) → Zero (E x)] →     
          [inst_4 : TopologicalSpace (Bundle.TotalSpace F E)] → [FiberBundle F E
] → {x : B} → E x → (x' : B) → E x'
参数：F : Type u_3；x : B；E x；x : B；E x；Bundle.TotalSpace F E；x' : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is 
`v`.
The details of the extension are mostly unspecified: for covariant derivatives, 
the value of
`s` at points other than `x` will not matter (except for shorter proofs).
-/
noncomputable def extend {x : B} (v₀ : E x) (x' : B) : E x' :=
  letI t := trivializationAt F E x
  letI w : F := (t ⟨x, v₀⟩).2
  -- TODO: use the `funToSec` helper from #36036 once available
  t.symm x' w
/-
**FiberBundle.extend_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：∀ {B : Type u_2} (F : Type u_3) {E : B → Type u_5} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : (x : B) → TopologicalSpace (E x)]
 [inst_3 : (x : B) → Zero (E x)]   [inst_4 : TopologicalSpace (Bundle.TotalSpace
 F E)] [inst_5 : FiberBundle F E] {x : B} (v : E x),   FiberBundle.extend F v x 
= v
参数：F : Type u_3；x : B；E x；x : B；E x；Bundle.TotalSpace F E；v : E x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.symm_apply_apply_mk`：∀ {B : Type u_1} {F : Type u_
2} {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] 
  [inst_2 : TopologicalSpace (B…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma extend_apply_self {x : B} (v : E x) : extend F v x = v := by
  simp [extend, FiberBundle.mem_baseSet_trivializationAt' x]

end extend
end FiberBundle

