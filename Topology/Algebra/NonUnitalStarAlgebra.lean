/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalAlgebra
public import Mathlib.Topology.Algebra.Star

/-!
# Non-unital topological star (sub)algebras

A non-unital topological star algebra over a topological semiring `R` is a topological
(non-unital) semiring with a compatible continuous scalar multiplication by elements
of `R` and a continuous `star` operation. We reuse typeclasses `ContinuousSMul` and
`ContinuousStar` to express the latter two conditions.

## Results

Any non-unital star subalgebra of a non-unital topological star algebra is itself a
non-unital topological star algebra, and its closure is again a non-unital star subalgebra.

-/

@[expose] public section

namespace NonUnitalStarSubalgebra

section Semiring

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
variable [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

/--
Instance `instIsTopologicalSemiring` / 实例 `instIsTopologicalSemiring`

English:
instance instIsTopologicalSemiring
  signature: [IsTopologicalSemiring A] (s : NonUnitalStarSubalgebra R A)
  body: s.toNonUnitalSubalgebra.instIsTopologicalSemiring

中文:
实例 instIsTopologicalSemiring
  签名: [IsTopologicalSemiring A] (s : NonUnitalStarSubalgebra R A)
  定义体: s.toNonUnitalSubalgebra.instIsTopologicalSemiring

Depends on / 依赖: instIsTopologicalSemiring, s.toNonUnitalSubalgebra.instIsTopologicalSemiring, toNonUnitalSubalgebra
-/
instance instIsTopologicalSemiring [IsTopologicalSemiring A] (s : NonUnitalStarSubalgebra R A) :
    IsTopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instIsTopologicalSemiring

/--
Instance `instIsSemitopologicalSemiring` / 实例 `instIsSemitopologicalSemiring`

English:
instance instIsSemitopologicalSemiring
  signature: [IsSemitopologicalSemiring A]
  body: s.toNonUnitalSubalgebra.instIsSemitopologicalSemiring

中文:
实例 instIsSemitopologicalSemiring
  签名: [IsSemitopologicalSemiring A]
  定义体: s.toNonUnitalSubalgebra.instIsSemitopologicalSemiring

Depends on / 依赖: instIsSemitopologicalSemiring, s.toNonUnitalSubalgebra.instIsSemitopologicalSemiring, toNonUnitalSubalgebra
-/
instance instIsSemitopologicalSemiring [IsSemitopologicalSemiring A]
    (s : NonUnitalStarSubalgebra R A) : IsSemitopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instIsSemitopologicalSemiring

variable [IsSemitopologicalSemiring A]

/--
Definition of `topologicalClosure` / `topologicalClosure` 的定义

English:
definition topologicalClosure
  signature: (s : NonUnitalStarSubalgebra R A)
  body: { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h => map_mem_closure continuous_star h fun _ => star_mem
    carrier := _root_.closure (s : Set A) }

中文:
定义 topologicalClosure
  签名: (s : NonUnitalStarSubalgebra R A)
  定义体: { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h => map_mem_closure continuous_star h fun _ => star_mem
    carrier := _root_.closure (s : Set A) }

Depends on / 依赖: _root_, _root_.closure, carrier, closure, continuous_star, map_mem_closure, s.toNonUnitalSubalgebra.topologicalClosure, star_mem, toNonUnitalSubalgebra, topologicalClosure
-/
def topologicalClosure (s : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R A :=
  { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h => map_mem_closure continuous_star h fun _ => star_mem
    carrier := _root_.closure (s : Set A) }

/--
theorem `le_topologicalClosure` / 定理 `le_topologicalClosure`

English:
theorem le_topologicalClosure
  given: (s : NonUnitalStarSubalgebra R A)
  statement: s <= s.topologicalClosure
  proof: subset_closure

中文:
定理 le_topologicalClosure
  条件: (s : NonUnitalStarSubalgebra R A)
  结论: s <= s.topologicalClosure
  证明: subset_closure

Depends on / 依赖: subset_closure
-/
theorem le_topologicalClosure (s : NonUnitalStarSubalgebra R A) : s <= s.topologicalClosure :=
  subset_closure

/--
theorem `isClosed_topologicalClosure` / 定理 `isClosed_topologicalClosure`

English:
theorem isClosed_topologicalClosure
  given: (s : NonUnitalStarSubalgebra R A)
  proof: isClosed_closure

中文:
定理 isClosed_topologicalClosure
  条件: (s : NonUnitalStarSubalgebra R A)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem isClosed_topologicalClosure (s : NonUnitalStarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure

/--
theorem `topologicalClosure_minimal` / 定理 `topologicalClosure_minimal`

English:
theorem topologicalClosure_minimal
  statement: (s : NonUnitalStarSubalgebra R A)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 topologicalClosure_minimal
  结论: (s : NonUnitalStarSubalgebra R A)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem topologicalClosure_minimal (s : NonUnitalStarSubalgebra R A)
    {t : NonUnitalStarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) :
    s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `topologicalClosure_mono` / 定理 `topologicalClosure_mono`

English:
theorem topologicalClosure_mono
  given: {s t : NonUnitalStarSubalgebra R A} (h : s <= t)
  proof: closure_mono h

中文:
定理 topologicalClosure_mono
  条件: {s t : NonUnitalStarSubalgebra R A} (h : s <= t)
  证明: closure_mono h

Depends on / 依赖: closure_mono
-/
theorem topologicalClosure_mono {s t : NonUnitalStarSubalgebra R A} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  closure_mono h

/--
Definition of `nonUnitalCommSemiringTopologicalClosure` / `nonUnitalCommSemiringTopologicalClosure` 的定义

English:
abbreviation nonUnitalCommSemiringTopologicalClosure
  signature: [T2Space A] (s : NonUnitalStarSubalgebra R A)
  body: fast_instance% s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

中文:
缩写 nonUnitalCommSemiringTopologicalClosure
  签名: [T2Space A] (s : NonUnitalStarSubalgebra R A)
  定义体: fast_instance% s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

Depends on / 依赖: fast_instance, nonUnitalCommSemiringTopologicalClosure, s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure, toNonUnitalSubalgebra
-/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : forall x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  fast_instance% s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

variable [TopologicalSpace B] [Star B] [NonUnitalSemiring B] [Module R B]
    [IsSemitopologicalSemiring B] [ContinuousConstSMul R B] [ContinuousStar B]
    (s : NonUnitalStarSubalgebra R A) {φ : A ->⋆ₙₐ[R] B}

/--
lemma `map_topologicalClosure_le` / 引理 `map_topologicalClosure_le`

English:
lemma map_topologicalClosure_le
  given: (hφ : Continuous φ)
  proof: image_closure_subset_closure_image hφ

中文:
引理 map_topologicalClosure_le
  条件: (hφ : Continuous φ)
  证明: image_closure_subset_closure_image hφ

Depends on / 依赖: image_closure_subset_closure_image
-/
lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure <= (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

/--
lemma `topologicalClosure_map_le` / 引理 `topologicalClosure_map_le`

English:
lemma topologicalClosure_map_le
  given: (hφ : IsClosedMap φ)
  proof: hφ.closure_image_subset _

中文:
引理 topologicalClosure_map_le
  条件: (hφ : IsClosedMap φ)
  证明: hφ.closure_image_subset _

Depends on / 依赖: closure_image_subset
-/
lemma topologicalClosure_map_le (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure <= map φ s.topologicalClosure :=
  hφ.closure_image_subset _

/--
lemma `topologicalClosure_map` / 引理 `topologicalClosure_map`

English:
lemma topologicalClosure_map
  given: (hφ : IsClosedMap φ) (hφ' : Continuous φ)
  proof: SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

中文:
引理 topologicalClosure_map
  条件: (hφ : IsClosedMap φ) (hφ' : Continuous φ)
  证明: SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_image_eq_of_continuous, coe_injective
-/
lemma topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

open NonUnitalStarAlgebra in
-- we have to shadow the variables because some things currently require `StarRing`
/--
lemma `topologicalClosure_adjoin_le_centralizer_centralizer` / 引理 `topologicalClosure_adjoin_le_centralizer_centralizer`

English:
lemma topologicalClosure_adjoin_le_centralizer_centralizer
  statement: (R : Type*) {A : Type*}
  proof: topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

中文:
引理 topologicalClosure_adjoin_le_centralizer_centralizer
  结论: (R : 类型) {A : 类型}
  证明: topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

Depends on / 依赖: Set.isClosed_centralizer, adjoin_le_centralizer_centralizer, isClosed_centralizer, topologicalClosure_minimal
-/
lemma topologicalClosure_adjoin_le_centralizer_centralizer (R : Type*) {A : Type*}
    [CommSemiring R] [StarRing R] [TopologicalSpace A] [NonUnitalSemiring A] [StarRing A]
    [Module R A] [IsSemitopologicalSemiring A] [ContinuousStar A] [ContinuousConstSMul R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure <= centralizer R (centralizer R s) :=
  topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [Star A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

/--
Instance `instIsTopologicalRing` / 实例 `instIsTopologicalRing`

English:
instance instIsTopologicalRing
  signature: [IsTopologicalRing A] (s : NonUnitalStarSubalgebra R A)
  body: s.toNonUnitalSubring.instIsTopologicalRing

中文:
实例 instIsTopologicalRing
  签名: [IsTopologicalRing A] (s : NonUnitalStarSubalgebra R A)
  定义体: s.toNonUnitalSubring.instIsTopologicalRing

Depends on / 依赖: instIsTopologicalRing, s.toNonUnitalSubring.instIsTopologicalRing, toNonUnitalSubring
-/
instance instIsTopologicalRing [IsTopologicalRing A] (s : NonUnitalStarSubalgebra R A) :
    IsTopologicalRing s :=
  s.toNonUnitalSubring.instIsTopologicalRing

/--
Instance `instIsSemitopologicalRing` / 实例 `instIsSemitopologicalRing`

English:
instance instIsSemitopologicalRing
  signature: [IsSemitopologicalRing A] (s : NonUnitalStarSubalgebra R A)
  body: s.toNonUnitalSubring.instIsSemitopologicalRing

中文:
实例 instIsSemitopologicalRing
  签名: [IsSemitopologicalRing A] (s : NonUnitalStarSubalgebra R A)
  定义体: s.toNonUnitalSubring.instIsSemitopologicalRing

Depends on / 依赖: instIsSemitopologicalRing, s.toNonUnitalSubring.instIsSemitopologicalRing, toNonUnitalSubring
-/
instance instIsSemitopologicalRing [IsSemitopologicalRing A] (s : NonUnitalStarSubalgebra R A) :
    IsSemitopologicalRing s :=
  s.toNonUnitalSubring.instIsSemitopologicalRing

variable [IsSemitopologicalRing A]

/--
Definition of `nonUnitalCommRingTopologicalClosure` / `nonUnitalCommRingTopologicalClosure` 的定义

English:
abbreviation nonUnitalCommRingTopologicalClosure
  signature: [T2Space A] (s : NonUnitalStarSubalgebra R A)
  body: { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

中文:
缩写 nonUnitalCommRingTopologicalClosure
  签名: [T2Space A] (s : NonUnitalStarSubalgebra R A)
  定义体: { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

Depends on / 依赖: commSemigroupTopologicalClosure, s.toSubsemigroup.commSemigroupTopologicalClosure, s.topologicalClosure.toNonUnitalRing, toNonUnitalRing, toSubsemigroup, topologicalClosure
-/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : forall x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [TopologicalSpace A] [IsSemitopologicalSemiring A] [ContinuousConstSMul R A]
variable [ContinuousStar A]

/--
Definition of `elemental` / `elemental` 的定义

English:
definition elemental
  signature: (x : A)
  body: .topologicalClosure adjoin R {x}

中文:
定义 elemental
  签名: (x : A)
  定义体: .topologicalClosure adjoin R {x}

Depends on / 依赖: adjoin, topologicalClosure
-/
def elemental (x : A) : NonUnitalStarSubalgebra R A :=
.topologicalClosure adjoin R {x}

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `self_mem` / 定理 `self_mem`

English:
theorem self_mem
  given: (x : A)
  statement: x in elemental R x
  proof: le_topologicalClosure _ self_mem_adjoin_singleton R x

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
定理 self_mem
  条件: (x : A)
  结论: x in elemental R x
  证明: le_topologicalClosure _ self_mem_adjoin_singleton R x

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: le_topologicalClosure, self_mem_adjoin_singleton
-/
theorem self_mem (x : A) : x in elemental R x :=
le_topologicalClosure _ self_mem_adjoin_singleton R x

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `star_self_mem` / 定理 `star_self_mem`

English:
theorem star_self_mem
  given: (x : A)
  statement: star x in elemental R x
  proof: le_topologicalClosure _ star_self_mem_adjoin_singleton R x

中文:
定理 star_self_mem
  条件: (x : A)
  结论: star x in elemental R x
  证明: le_topologicalClosure _ star_self_mem_adjoin_singleton R x

Depends on / 依赖: le_topologicalClosure, star_self_mem_adjoin_singleton
-/
theorem star_self_mem (x : A) : star x in elemental R x :=
le_topologicalClosure _ star_self_mem_adjoin_singleton R x

variable {R} in
/--
theorem `le_of_mem` / 定理 `le_of_mem`

English:
theorem le_of_mem
  statement: {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
  proof: topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

中文:
定理 le_of_mem
  结论: {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
  证明: topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

Depends on / 依赖: adjoin_le, topologicalClosure_minimal
-/
theorem le_of_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
    (hx : x in s) : elemental R x <= s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

variable {R} in
/--
theorem `le_iff_mem` / 定理 `le_iff_mem`

English:
theorem le_iff_mem
  given: {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
  proof: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

中文:
定理 le_iff_mem
  条件: {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
  证明: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

Depends on / 依赖: le_of_mem, self_mem
-/
theorem le_iff_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x <= s ↔ x in s :=
  ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (x : A)
  statement: IsClosed (elemental R x : Set A)
  proof: isClosed_topologicalClosure _

中文:
定理 isClosed
  条件: (x : A)
  结论: IsClosed (elemental R x : Set A)
  证明: isClosed_topologicalClosure _

Depends on / 依赖: isClosed_topologicalClosure
-/
theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

open scoped IsMulCommutative in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: A] {x
  body: fast_instance% nonUnitalCommSemiringTopologicalClosure _ mul_comm

中文:
实例 [T2Space
  签名: A] {x
  定义体: fast_instance% nonUnitalCommSemiringTopologicalClosure _ mul_comm

Depends on / 依赖: fast_instance, mul_comm, nonUnitalCommSemiringTopologicalClosure
-/
instance [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommSemiring (elemental R x) :=
  fast_instance% nonUnitalCommSemiringTopologicalClosure _ mul_comm

instance {R A : Type*} [CommRing R] [StarRing R] [NonUnitalRing A] [StarRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    [TopologicalSpace A] [IsSemitopologicalRing A] [ContinuousConstSMul R A] [ContinuousStar A]
    [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/--
theorem `isClosedEmbedding_coe` / 定理 `isClosedEmbedding_coe`

English:
theorem isClosedEmbedding_coe
  given: (x : A)
  statement: Topology.IsClosedEmbedding ((↑) : elemental R x -> A) where
  proof: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

中文:
定理 isClosedEmbedding_coe
  条件: (x : A)
  结论: Topology.IsClosedEmbedding ((↑) : elemental R x -> A) where
  证明: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
-/
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x -> A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

/--
lemma `le_centralizer_centralizer` / 引理 `le_centralizer_centralizer`

English:
lemma le_centralizer_centralizer
  given: [T2Space A] (x : A)
  proof: topologicalClosure_adjoin_le_centralizer_centralizer ..

中文:
引理 le_centralizer_centralizer
  条件: [T2Space A] (x : A)
  证明: topologicalClosure_adjoin_le_centralizer_centralizer ..

Depends on / 依赖: topologicalClosure_adjoin_le_centralizer_centralizer
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x <= centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

end elemental

end NonUnitalStarAlgebra
