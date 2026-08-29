/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous maps sending zero to zero

This is the type of continuous maps from `X` to `R` such that `(0 : X) ↦ (0 : R)` for which we
provide the scoped notation `C(X, R)₀`. We provide this as a dedicated type solely for the
non-unital continuous functional calculus, as using various terms of type `Ideal C(X, R)` were
overly burdensome on type class synthesis.

Of course, one could generalize to maps between pointed topological spaces, but that goes beyond
the purpose of this type.
-/

@[expose] public section

assert_not_exists StarOrderedRing

open Function Set Topology

/--
Definition of `ContinuousMapZero` / `ContinuousMapZero` 的定义

English:
structure ContinuousMapZero
  parameters: (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
  extends: C(X, R)
  axioms and operations (1):
    - map_zero' : toContinuousMap 0 = 0

中文:
结构 余ntinuousMapZero
  参数: (X R : 类型) [零 X] [零 R] [拓扑空间 X]
  继承: C(X, R)
  公理与运算 (1 个):
    - map_zero' : toContinuousMap 0 = 0
-/
structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero

@[inherit_doc]
scoped notation "C(" X ", " R ")₀" => ContinuousMapZero X R

section Basic

variable {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike C(X, R)₀ X R where
  body: f.toFun
  coe_injective _ _ h := congr(⟨⟨$(h), _⟩, _⟩)

中文:
实例 instFunLike
  签名: : 函数状 C(X, R)₀ X R where
  定义体: f.toFun
  coe_injective _ _ h := congr(⟨⟨$(h), _⟩, _⟩)

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike C(X, R)₀ X R where
  coe f := f.toFun
  coe_injective _ _ h := congr(⟨⟨$(h), _⟩, _⟩)

/--
Instance `instContinuousMapClass` / 实例 `instContinuousMapClass`

English:
instance instContinuousMapClass
  signature: : ContinuousMapClass C(X, R)₀ X R where
  body: f.continuous

中文:
实例 instContinuousMapClass
  签名: : 连续映射类 C(X, R)₀ X R where
  定义体: f.continuous

Depends on / 依赖: continuous, f.continuous
-/
instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous

/--
Instance `instZeroHomClass` / 实例 `instZeroHomClass`

English:
instance instZeroHomClass
  signature: : ZeroHomClass C(X, R)₀ X R where
  body: f.map_zero'

中文:
实例 instZeroHomClass
  签名: : 保零态射类 C(X, R)₀ X R where
  定义体: f.map_zero'

Depends on / 依赖: f.map_zero, map_zero
-/
instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

/-- not marked as an instance because it would be a bad one in general, but it can
be useful when working with `ContinuousMapZero` and the non-unital continuous
functional calculus. -/
@[instance_reducible]
/--
Definition of `_root_.Set.zeroOfFactMem` / `_root_.Set.zeroOfFactMem` 的定义

English:
definition _root_.Set.zeroOfFactMem
  signature: {X : Type*} [Zero X] (s : Set X) [Fact (0 in s)]
  body: ⟨0, Fact.out⟩

scoped[ContinuousMapZero] attribute [instance] Set.zeroOfFactMem

@[ext]

中文:
定义 _root_.集合.zeroOfFactMem
  签名: {X : 类型} [零 X] (s : 集合 X) [Fact (0 in s)]
  定义体: ⟨0, Fact.out⟩

scoped[ContinuousMapZero] attribute [instance] Set.zeroOfFactMem

@[ext]

Depends on / 依赖: Fact.out
-/
def _root_.Set.zeroOfFactMem {X : Type*} [Zero X] (s : Set X) [Fact (0 in s)] :
    Zero s where
  zero := ⟨0, Fact.out⟩

scoped[ContinuousMapZero] attribute [instance] Set.zeroOfFactMem

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : C(X, R)₀} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
引理 ext
  条件: {f g : C(X, R)₀} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext {f g : C(X, R)₀} (h : forall x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: {f : C(X, R)} {h0 : f 0 = 0}
  statement: ⇑(mk f h0) = f
  proof: rfl

中文:
引理 coe_mk
  条件: {f : C(X, R)} {h0 : f 0 = 0}
  结论: ⇑(mk f h0) = f
  证明: rfl
-/
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl

/--
lemma `toContinuousMap_injective` / 引理 `toContinuousMap_injective`

English:
lemma toContinuousMap_injective
  statement: Injective ((↑) : C(X, R)₀ -> C(X, R))
  proof: fun _ _ h => congr(.mk $(h) _)

中文:
引理 toContinuousMap_injective
  结论: 单射 ((↑) : C(X, R)₀ -> C(X, R))
  证明: fun _ _ h => congr(.mk $(h) _)
-/
lemma toContinuousMap_injective : Injective ((↑) : C(X, R)₀ -> C(X, R)) :=
  fun _ _ h => congr(.mk $(h) _)

/--
lemma `range_toContinuousMap` / 引理 `range_toContinuousMap`

English:
lemma range_toContinuousMap
  statement: range ((↑) : C(X, R)₀ -> C(X, R)) = {f : C(X, R) | f 0 = 0}
  proof: Set.ext fun f => ⟨fun ⟨f', hf'⟩ => hf' ▸ map_zero f', fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

中文:
引理 range_toContinuousMap
  结论: range ((↑) : C(X, R)₀ -> C(X, R)) = {f : C(X, R) | f 0 = 0}
  证明: Set.ext fun f => ⟨fun ⟨f', hf'⟩ => hf' ▸ map_zero f', fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

Depends on / 依赖: Set.ext, map_zero
-/
lemma range_toContinuousMap : range ((↑) : C(X, R)₀ -> C(X, R)) = {f : C(X, R) | f 0 = 0} :=
  Set.ext fun f => ⟨fun ⟨f', hf'⟩ => hf' ▸ map_zero f', fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : C(Y, R)₀) (f : C(X, Y)₀)
  body: (g : C(Y, R)).comp (f : C(X, Y))
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]

中文:
定义 comp
  签名: (g : C(Y, R)₀) (f : C(X, Y)₀)
  定义体: (g : C(Y, R)).comp (f : C(X, Y))
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
-/
def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := (g : C(Y, R)).comp (f : C(X, Y))
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X)
  statement: g.comp f x = g (f x)
  proof: rfl

中文:
引理 comp_apply
  条件: (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X)
  结论: g.comp f x = g (f x)
  证明: rfl
-/
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: [PartialOrder R]
  body: fast_instance%
  .lift _ DFunLike.coe_injective

中文:
实例 instPartialOrder
  签名: [偏序 R]
  定义体: fast_instance%
  .lift _ DFunLike.coe_injective

Depends on / 依赖: fast_instance
-/
instance instPartialOrder [PartialOrder R] : PartialOrder C(X, R)₀ := fast_instance%
  .lift _ DFunLike.coe_injective

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: [PartialOrder R] (f g : C(X, R)₀)
  statement: f <= g ↔ forall x, f x <= g x
  proof: Iff.rfl

中文:
引理 le_def
  条件: [偏序 R] (f g : C(X, R)₀)
  结论: f <= g ↔ 对任意 x, f x <= g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def [PartialOrder R] (f g : C(X, R)₀) : f <= g ↔ forall x, f x <= g x := Iff.rfl

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace C(X, R)₀
  body: fast_instance%
  TopologicalSpace.induced ((↑) : C(X, R)₀ -> C(X, R)) inferInstance

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 C(X, R)₀
  定义体: fast_instance%
  TopologicalSpace.induced ((↑) : C(X, R)₀ -> C(X, R)) inferInstance
-/
protected instance instTopologicalSpace : TopologicalSpace C(X, R)₀ := fast_instance%
  TopologicalSpace.induced ((↑) : C(X, R)₀ -> C(X, R)) inferInstance

/--
lemma `isEmbedding_toContinuousMap` / 引理 `isEmbedding_toContinuousMap`

English:
lemma isEmbedding_toContinuousMap
  statement: IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where
  proof: rfl
  injective _ _ h := ext fun x => congr($(h) x)

中文:
引理 isEmbedding_toContinuousMap
  结论: 是嵌入 ((↑) : C(X, R)₀ -> C(X, R)) where
  证明: rfl
  injective _ _ h := ext fun x => congr($(h) x)
-/
lemma isEmbedding_toContinuousMap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where
  eq_induced := rfl
  injective _ _ h := ext fun x => congr($(h) x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T0Space
  signature: R] : T0Space C(X, R)₀
  body: isEmbedding_toContinuousMap.t0Space

中文:
实例 [T0空间
  签名: R] : T0空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.t0Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.t0Space, t0Space
-/
instance [T0Space R] : T0Space C(X, R)₀ := isEmbedding_toContinuousMap.t0Space
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R0Space
  signature: R] : R0Space C(X, R)₀
  body: isEmbedding_toContinuousMap.r0Space

中文:
实例 [R0空间
  签名: R] : R0空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.r0Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.r0Space, r0Space
-/
instance [R0Space R] : R0Space C(X, R)₀ := isEmbedding_toContinuousMap.r0Space
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: R] : T1Space C(X, R)₀
  body: isEmbedding_toContinuousMap.t1Space

中文:
实例 [T1空间
  签名: R] : T1空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.t1Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.t1Space, t1Space
-/
instance [T1Space R] : T1Space C(X, R)₀ := isEmbedding_toContinuousMap.t1Space
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R1Space
  signature: R] : R1Space C(X, R)₀
  body: isEmbedding_toContinuousMap.r1Space

中文:
实例 [R1空间
  签名: R] : R1空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.r1Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.r1Space, r1Space
-/
instance [R1Space R] : R1Space C(X, R)₀ := isEmbedding_toContinuousMap.r1Space
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: R] : T2Space C(X, R)₀
  body: isEmbedding_toContinuousMap.t2Space

中文:
实例 [T2空间
  签名: R] : T2空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.t2Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.t2Space, t2Space
-/
instance [T2Space R] : T2Space C(X, R)₀ := isEmbedding_toContinuousMap.t2Space
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RegularSpace
  signature: R] : RegularSpace C(X, R)₀
  body: isEmbedding_toContinuousMap.regularSpace

中文:
实例 [正则空间
  签名: R] : 正则空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.regularSpace

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.regularSpace, regularSpace
-/
instance [RegularSpace R] : RegularSpace C(X, R)₀ := isEmbedding_toContinuousMap.regularSpace
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T3Space
  signature: R] : T3Space C(X, R)₀
  body: isEmbedding_toContinuousMap.t3Space

中文:
实例 [T3空间
  签名: R] : T3空间 C(X, R)₀
  定义体: isEmbedding_toContinuousMap.t3Space

Depends on / 依赖: isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.t3Space, t3Space
-/
instance [T3Space R] : T3Space C(X, R)₀ := isEmbedding_toContinuousMap.t3Space

/--
Instance `instContinuousEvalConst` / 实例 `instContinuousEvalConst`

English:
instance instContinuousEvalConst
  signature: : ContinuousEvalConst C(X, R)₀ X R
  body: .of_continuous_forget isEmbedding_toContinuousMap.continuous

中文:
实例 instContinuousEvalConst
  签名: : 余ntinuousEvalConst C(X, R)₀ X R
  定义体: .of_continuous_forget isEmbedding_toContinuousMap.continuous

Depends on / 依赖: continuous, isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.continuous, of_continuous_forget
-/
instance instContinuousEvalConst : ContinuousEvalConst C(X, R)₀ X R :=
  .of_continuous_forget isEmbedding_toContinuousMap.continuous

/--
Instance `instContinuousEval` / 实例 `instContinuousEval`

English:
instance instContinuousEval
  signature: [LocallyCompactPair X R]
  body: .of_continuous_forget isEmbedding_toContinuousMap.continuous

中文:
实例 instContinuousEval
  签名: [LocallyCompactPair X R]
  定义体: .of_continuous_forget isEmbedding_toContinuousMap.continuous

Depends on / 依赖: continuous, isEmbedding_toContinuousMap, isEmbedding_toContinuousMap.continuous, of_continuous_forget
-/
instance instContinuousEval [LocallyCompactPair X R] : ContinuousEval C(X, R)₀ X R :=
  .of_continuous_forget isEmbedding_toContinuousMap.continuous

/--
lemma `isClosedEmbedding_toContinuousMap` / 引理 `isClosedEmbedding_toContinuousMap`

English:
lemma isClosedEmbedding_toContinuousMap
  given: [T1Space R]
  proof: isEmbedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
exact isClosed_singleton.preimage continuous_eval_const 0

@[fun_prop]

中文:
引理 isClosedEmbedding_toContinuousMap
  条件: [T1空间 R]
  证明: isEmbedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
exact isClosed_singleton.preimage continuous_eval_const 0

@[fun_prop]

Depends on / 依赖: isEmbedding_toContinuousMap
-/
lemma isClosedEmbedding_toContinuousMap [T1Space R] :
    IsClosedEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where
  toIsEmbedding := isEmbedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
exact isClosed_singleton.preimage continuous_eval_const 0

@[fun_prop]
/--
lemma `continuous_precomp` / 引理 `continuous_precomp`

English:
lemma continuous_precomp
  given: (f : C(X, Y)₀)
  statement: Continuous fun g : C(Y, R)₀ => g.comp f
  proof: by
  rw [continuous_induced_rng]
  change Continuous fun g : C(Y, R)₀ => (g : C(Y, R)).comp (f : C(X, Y))
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_comp_left := continuous_precomp

中文:
引理 continuous_precomp
  条件: (f : C(X, Y)₀)
  结论: 连续 fun g : C(Y, R)₀ => g.comp f
  证明: by
  rw [continuous_induced_rng]
  change Continuous fun g : C(Y, R)₀ => (g : C(Y, R)).comp (f : C(X, Y))
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_comp_left := continuous_precomp

Depends on / 依赖: Continuous, continuous_induced_rng, fun_prop
-/
lemma continuous_precomp (f : C(X, Y)₀) : Continuous fun g : C(Y, R)₀ => g.comp f := by
  rw [continuous_induced_rng]
  change Continuous fun g : C(Y, R)₀ => (g : C(Y, R)).comp (f : C(X, Y))
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_comp_left := continuous_precomp

/--
theorem `postcomp_injective` / 定理 `postcomp_injective`

English:
theorem postcomp_injective
  given: (g : C(Y, R)₀) (hg : Injective g)
  proof: fun _ _ h => ext fun x => hg congr($h x)

@[fun_prop]

中文:
定理 postcomp_injective
  条件: (g : C(Y, R)₀) (hg : 单射 g)
  证明: fun _ _ h => ext fun x => hg congr($h x)

@[fun_prop]
-/
theorem postcomp_injective (g : C(Y, R)₀) (hg : Injective g) :
    Injective (g.comp : C(X, Y)₀ -> C(X, R)₀) :=
  fun _ _ h => ext fun x => hg congr($h x)

@[fun_prop]
/--
theorem `continuous_postcomp` / 定理 `continuous_postcomp`

English:
theorem continuous_postcomp
  given: (g : C(Y, R)₀)
  statement: Continuous (g.comp : C(X, Y)₀ -> C(X, R)₀)
  proof: by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
.comp exact g.toContinuousMap.continuous_postcomp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

中文:
定理 continuous_postcomp
  条件: (g : C(Y, R)₀)
  结论: 连续 (g.comp : C(X, Y)₀ -> C(X, R)₀)
  证明: by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
.comp exact g.toContinuousMap.continuous_postcomp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isEmbedding_toContinuousMap.continuous, ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff, continuous, continuous_iff, continuous_postcomp, g.toContinuousMap.continuous_postcomp, isEmbedding_toContinuousMap, toContinuousMap
-/
theorem continuous_postcomp (g : C(Y, R)₀) : Continuous (g.comp : C(X, Y)₀ -> C(X, R)₀) := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
.comp exact g.toContinuousMap.continuous_postcomp
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

/-- The identity function as an element of `C(s, R)₀` when `0 ∈ (s : Set R)`. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (s : Set R) [Fact (0 in s)]
  body: ⟨.restrict s (.id R), rfl⟩

@[simp]

中文:
定义 id
  签名: (s : 集合 R) [Fact (0 in s)]
  定义体: ⟨.restrict s (.id R), rfl⟩

@[simp]
-/
protected def id (s : Set R) [Fact (0 in s)] : C(s, R)₀ :=
  ⟨.restrict s (.id R), rfl⟩

@[simp]
/--
lemma `toContinuousMap_id` / 引理 `toContinuousMap_id`

English:
lemma toContinuousMap_id
  given: {s : Set R} [Fact (0 in s)]
  proof: rfl

中文:
引理 toContinuousMap_id
  条件: {s : 集合 R} [Fact (0 in s)]
  证明: rfl
-/
lemma toContinuousMap_id {s : Set R} [Fact (0 in s)] :
    (ContinuousMapZero.id s : C(s, R)) = .restrict s (.id R) :=
  rfl

end Basic

section mkD

variable {X R : Type*} [Zero R]
variable [TopologicalSpace X] [TopologicalSpace R]

open scoped Classical in
/--
Definition of `mkD` / `mkD` 的定义

English:
definition mkD
  signature: [Zero X] (f : X -> R) (default : C(X, R)₀)
  body: if h : Continuous f ∧ f 0 = 0 then ⟨⟨_, h.1⟩, h.2⟩ else default

中文:
定义 mkD
  签名: [零 X] (f : X -> R) (default : C(X, R)₀)
  定义体: if h : Continuous f ∧ f 0 = 0 then ⟨⟨_, h.1⟩, h.2⟩ else default

Depends on / 依赖: Continuous
-/
noncomputable def mkD [Zero X] (f : X -> R) (default : C(X, R)₀) : C(X, R)₀ :=
  if h : Continuous f ∧ f 0 = 0 then ⟨⟨_, h.1⟩, h.2⟩ else default

/--
lemma `mkD_of_continuous` / 引理 `mkD_of_continuous`

English:
lemma mkD_of_continuous
  given: [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0)
  proof: by
  simp only [mkD, And.intro hf hf₀, true_and, ↓reduceDIte]

中文:
引理 mkD_of_continuous
  条件: [零 X] {f : X -> R} {g : C(X, R)₀} (hf : 连续 f) (hf₀ : f 0 = 0)
  证明: by
  simp only [mkD, And.intro hf hf₀, true_and, ↓reduceDIte]

Depends on / 依赖: And.intro, reduceDIte, true_and
-/
lemma mkD_of_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) :
    mkD f g = ⟨⟨f, hf⟩, hf₀⟩ := by
  simp only [mkD, And.intro hf hf₀, true_and, ↓reduceDIte]

/--
lemma `mkD_of_not_continuous` / 引理 `mkD_of_not_continuous`

English:
lemma mkD_of_not_continuous
  given: [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : ¬ Continuous f)
  proof: by
  simp only [mkD, not_and_of_not_left _ hf, ↓reduceDIte]

中文:
引理 mkD_of_not_continuous
  条件: [零 X] {f : X -> R} {g : C(X, R)₀} (hf : ¬ 连续 f)
  证明: by
  simp only [mkD, not_and_of_not_left _ hf, ↓reduceDIte]

Depends on / 依赖: not_and_of_not_left, reduceDIte
-/
lemma mkD_of_not_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : ¬ Continuous f) :
    mkD f g = g := by
  simp only [mkD, not_and_of_not_left _ hf, ↓reduceDIte]

/--
lemma `mkD_of_not_zero` / 引理 `mkD_of_not_zero`

English:
lemma mkD_of_not_zero
  given: [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : f 0 != 0)
  proof: by
  simp only [mkD, not_and_of_not_right _ hf, ↓reduceDIte]

中文:
引理 mkD_of_not_zero
  条件: [零 X] {f : X -> R} {g : C(X, R)₀} (hf : f 0 != 0)
  证明: by
  simp only [mkD, not_and_of_not_right _ hf, ↓reduceDIte]

Depends on / 依赖: not_and_of_not_right, reduceDIte
-/
lemma mkD_of_not_zero [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : f 0 != 0) :
    mkD f g = g := by
  simp only [mkD, not_and_of_not_right _ hf, ↓reduceDIte]

/--
lemma `mkD_apply_of_continuous` / 引理 `mkD_apply_of_continuous`

English:
lemma mkD_apply_of_continuous
  statement: [Zero X] {f : X -> R} {g : C(X, R)₀} {x : X}
  proof: by
  rw [mkD_of_continuous hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]

中文:
引理 mkD_apply_of_continuous
  结论: [零 X] {f : X -> R} {g : C(X, R)₀} {x : X}
  证明: by
  rw [mkD_of_continuous hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, coe_mk, mkD_of_continuous
-/
lemma mkD_apply_of_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} {x : X}
    (hf : Continuous f) (hf₀ : f 0 = 0) :
    mkD f g x = f x := by
  rw [mkD_of_continuous hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]

/--
lemma `mkD_of_continuousOn` / 引理 `mkD_of_continuousOn`

English:
lemma mkD_of_continuousOn
  statement: {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀}
  proof: mkD_of_continuous hf.domRestrict hf₀

中文:
引理 mkD_of_continuousOn
  结论: {s : 集合 X} [零 s] {f : X -> R} {g : C(s, R)₀}
  证明: mkD_of_continuous hf.domRestrict hf₀

Depends on / 依赖: domRestrict, hf.domRestrict, mkD_of_continuous
-/
lemma mkD_of_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀}
    (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0) :
    mkD (s.domRestrict f) g = ⟨⟨s.domRestrict f, hf.domRestrict⟩, hf₀⟩ :=
  mkD_of_continuous hf.domRestrict hf₀

/--
lemma `mkD_of_not_continuousOn` / 引理 `mkD_of_not_continuousOn`

English:
lemma mkD_of_not_continuousOn
  statement: {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀}
  proof: by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

中文:
引理 mkD_of_not_continuousOn
  结论: {s : 集合 X} [零 s] {f : X -> R} {g : C(s, R)₀}
  证明: by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, mkD_of_not_continuous
-/
lemma mkD_of_not_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀}
    (hf : ¬ ContinuousOn f s) :
    mkD (s.domRestrict f) g = g := by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mkD_apply_of_continuousOn` / 引理 `mkD_apply_of_continuousOn`

English:
lemma mkD_apply_of_continuousOn
  statement: {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀} {x : s}
  proof: by
  rw [mkD_of_continuousOn hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]; rw [domRestrict_apply]

中文:
引理 mkD_apply_of_continuousOn
  结论: {s : 集合 X} [零 s] {f : X -> R} {g : C(s, R)₀} {x : s}
  证明: by
  rw [mkD_of_continuousOn hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]; rw [domRestrict_apply]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, coe_mk, domRestrict_apply, mkD_of_continuousOn
-/
lemma mkD_apply_of_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀} {x : s}
    (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0) :
    mkD (s.domRestrict f) g x = f x := by
  rw [mkD_of_continuousOn hf hf₀]; rw [coe_mk]; rw [ContinuousMap.coe_mk]; rw [domRestrict_apply]

open ContinuousMap in
/--
lemma `mkD_eq_mkD_of_map_zero` / 引理 `mkD_eq_mkD_of_map_zero`

English:
lemma mkD_eq_mkD_of_map_zero
  given: [Zero X] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0)
  proof: by
  ext
  by_cases f_cont : Continuous f <;>
    simp [*, ContinuousMap.mkD_of_continuous, mkD_of_continuous, mkD_of_not_continuous,
      ContinuousMap.mkD_of_not_continuous]

中文:
引理 mkD_eq_mkD_of_map_zero
  条件: [零 X] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0)
  证明: by
  ext
  by_cases f_cont : Continuous f <;>
    simp [*, ContinuousMap.mkD_of_continuous, mkD_of_continuous, mkD_of_not_continuous,
      ContinuousMap.mkD_of_not_continuous]

Depends on / 依赖: Continuous, ContinuousMap, ContinuousMap.mkD_of_continuous, ContinuousMap.mkD_of_not_continuous, f_cont, mkD_of_continuous, mkD_of_not_continuous
-/
lemma mkD_eq_mkD_of_map_zero [Zero X] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0) :
    mkD f g = ContinuousMap.mkD f g := by
  ext
  by_cases f_cont : Continuous f <;>
    simp [*, ContinuousMap.mkD_of_continuous, mkD_of_continuous, mkD_of_not_continuous,
      ContinuousMap.mkD_of_not_continuous]

/--
lemma `mkD_eq_self` / 引理 `mkD_eq_self`

English:
lemma mkD_eq_self
  given: [Zero X] {f g : C(X, R)₀}
  statement: mkD f g = f
  proof: mkD_of_continuous f.continuous (map_zero f)

中文:
引理 mkD_eq_self
  条件: [零 X] {f g : C(X, R)₀}
  结论: mkD f g = f
  证明: mkD_of_continuous f.continuous (map_zero f)

Depends on / 依赖: continuous, f.continuous, map_zero, mkD_of_continuous
-/
lemma mkD_eq_self [Zero X] {f g : C(X, R)₀} : mkD f g = f :=
  mkD_of_continuous f.continuous (map_zero f)

end mkD

section Algebra

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [TopologicalSpace R]

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero R]
  body: ⟨0, rfl⟩

中文:
实例 instZero
  签名: [零 R]
  定义体: ⟨0, rfl⟩
-/
instance instZero [Zero R] : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  given: [Zero R]
  statement: ⇑(0 : C(X, R)₀) = 0
  proof: rfl

中文:
引理 coe_zero
  条件: [零 R]
  结论: ⇑(0 : C(X, R)₀) = 0
  证明: rfl
-/
@[simp] lemma coe_zero [Zero R] : ⇑(0 : C(X, R)₀) = 0 := rfl

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [AddZeroClass R] [ContinuousAdd R]
  body: ⟨f + g, by simp⟩

中文:
实例 instAdd
  签名: [加法零类 R] [连续加法 R]
  定义体: ⟨f + g, by simp⟩
-/
instance instAdd [AddZeroClass R] [ContinuousAdd R] : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: [AddZeroClass R] [ContinuousAdd R] (f g : C(X, R)₀)
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
引理 coe_add
  条件: [加法零类 R] [连续加法 R] (f g : C(X, R)₀)
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
@[simp] lemma coe_add [AddZeroClass R] [ContinuousAdd R] (f g : C(X, R)₀) : ⇑(f + g) = f + g := rfl

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [NegZeroClass R] [ContinuousNeg R]
  body: ⟨- f, by simp⟩

中文:
实例 instNeg
  签名: [NegZero类 R] [连续取负 R]
  定义体: ⟨- f, by simp⟩
-/
instance instNeg [NegZeroClass R] [ContinuousNeg R] : Neg C(X, R)₀ where
  neg f := ⟨- f, by simp⟩

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: [NegZeroClass R] [ContinuousNeg R] (f : C(X, R)₀)
  statement: ⇑(-f) = -f
  proof: rfl

中文:
引理 coe_neg
  条件: [NegZero类 R] [连续取负 R] (f : C(X, R)₀)
  结论: ⇑(-f) = -f
  证明: rfl
-/
@[simp] lemma coe_neg [NegZeroClass R] [ContinuousNeg R] (f : C(X, R)₀) : ⇑(-f) = -f := rfl

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [SubNegZeroMonoid R] [ContinuousSub R]
  body: ⟨f - g, by simp⟩

中文:
实例 instSub
  签名: [SubNegZero幺半群 R] [余ntinuousSub R]
  定义体: ⟨f - g, by simp⟩
-/
instance instSub [SubNegZeroMonoid R] [ContinuousSub R] : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩

/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: [SubNegZeroMonoid R] [ContinuousSub R] (f g : C(X, R)₀)
  proof: rfl

中文:
引理 coe_sub
  条件: [SubNegZero幺半群 R] [余ntinuousSub R] (f g : C(X, R)₀)
  证明: rfl
-/
@[simp] lemma coe_sub [SubNegZeroMonoid R] [ContinuousSub R] (f g : C(X, R)₀) :
    ⇑(f - g) = f - g := rfl

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [MulZeroClass R] [ContinuousMul R]
  body: ⟨f * g, by simp⟩

中文:
实例 instMul
  签名: [乘零类 R] [连续乘法 R]
  定义体: ⟨f * g, by simp⟩
-/
instance instMul [MulZeroClass R] [ContinuousMul R] : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: [MulZeroClass R] [ContinuousMul R] (f g : C(X, R)₀)
  statement: ⇑(f * g) = f * g
  proof: rfl

中文:
引理 coe_mul
  条件: [乘零类 R] [连续乘法 R] (f g : C(X, R)₀)
  结论: ⇑(f * g) = f * g
  证明: rfl
-/
@[simp] lemma coe_mul [MulZeroClass R] [ContinuousMul R] (f g : C(X, R)₀) : ⇑(f * g) = f * g := rfl

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
  body: ⟨m • f, by simp⟩

中文:
实例 instSMul
  签名: {M : 类型} [零 R] [SMulZero类 M R] [连续常数标量乘法 M R]
  定义体: ⟨m • f, by simp⟩
-/
instance instSMul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩

/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  statement: {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
  proof: rfl

中文:
引理 coe_smul
  结论: {M : 类型} [零 R] [SMulZero类 M R] [连续常数标量乘法 M R]
  证明: rfl
-/
@[simp] lemma coe_smul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
    (m : M) (f : C(X, R)₀) : ⇑(m • f) = m • f := rfl

section AddCommMonoid

variable [AddCommMonoid R] [ContinuousAdd R]

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid C(X, R)₀
  body: fast_instance% toContinuousMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 C(X, R)₀
  定义体: fast_instance% toContinuousMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: addCommMonoid, fast_instance, toContinuousMap_injective, toContinuousMap_injective.addCommMonoid
-/
instance instAddCommMonoid : AddCommMonoid C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R]
  body: fast_instance% toContinuousMap_injective.module M
    { toFun := _, map_add' := fun _ _ => rfl, map_zero' := rfl } (fun _ _ => rfl)

中文:
实例 instModule
  签名: {M : 类型} [半环 M] [模 M R] [连续常数标量乘法 M R]
  定义体: fast_instance% toContinuousMap_injective.module M
    { toFun := _, map_add' := fun _ _ => rfl, map_zero' := rfl } (fun _ _ => rfl)

Depends on / 依赖: fast_instance, map_add, map_zero, module, toContinuousMap_injective, toContinuousMap_injective.module
-/
instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.module M
    { toFun := _, map_add' := fun _ _ => rfl, map_zero' := rfl } (fun _ _ => rfl)

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
  body: ext fun _ => smul_comm ..

中文:
实例 instSMulCommClass
  签名: {M N : 类型} [SMulZero类 M R] [连续常数标量乘法 M R]
  定义体: ext fun _ => smul_comm ..

Depends on / 依赖: smul_comm
-/
instance instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] :
    SMulCommClass M N C(X, R)₀ where
  smul_comm _ _ _ := ext fun _ => smul_comm ..

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
  body: ext fun _ => smul_assoc ..

中文:
实例 instIsScalarTower
  签名: {M N : 类型} [SMulZero类 M R] [连续常数标量乘法 M R]
  定义体: ext fun _ => smul_assoc ..

Depends on / 依赖: smul_assoc
-/
instance instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N R] :
    IsScalarTower M N C(X, R)₀ where
  smul_assoc _ _ _ := ext fun _ => smul_assoc ..

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R] [IsTopologicalAddGroup R]

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup C(X, R)₀
  body: fast_instance% toContinuousMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instAddCommGroup
  签名: : 加法交换群 C(X, R)₀
  定义体: fast_instance% toContinuousMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: addCommGroup, fast_instance, toContinuousMap_injective, toContinuousMap_injective.addCommGroup
-/
instance instAddCommGroup : AddCommGroup C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommGroup

section Semiring

variable [CommSemiring R] [IsTopologicalSemiring R]

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: : NonUnitalCommSemiring C(X, R)₀
  body: fast_instance% toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instNonUnitalCommSemiring
  签名: : 非幺交换半环 C(X, R)₀
  定义体: fast_instance% toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: fast_instance, nonUnitalCommSemiring, toContinuousMap_injective, toContinuousMap_injective.nonUnitalCommSemiring
-/
instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R]
  body: ext fun x => smul_comm m (f x) (g x)

中文:
实例 instSMulCommClass'
  签名: {M : 类型} [SMulZero类 M R] [标量交换类 M R R]
  定义体: ext fun x => smul_comm m (f x) (g x)

Depends on / 依赖: smul_comm
-/
instance instSMulCommClass' {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R]
    [ContinuousConstSMul M R] : SMulCommClass M C(X, R)₀ C(X, R)₀ where
  smul_comm m f g := ext fun x => smul_comm m (f x) (g x)

/--
Instance `instIsScalarTower'` / 实例 `instIsScalarTower'`

English:
instance instIsScalarTower'
  signature: {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R]
  body: ext fun x => smul_assoc m (f x) (g x)

中文:
实例 instIsScalarTower'
  签名: {M : 类型} [SMulZero类 M R] [标量塔 M R R]
  定义体: ext fun x => smul_assoc m (f x) (g x)

Depends on / 依赖: smul_assoc
-/
instance instIsScalarTower' {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R]
    [ContinuousConstSMul M R] : IsScalarTower M C(X, R)₀ C(X, R)₀ where
  smul_assoc m f g := ext fun x => smul_assoc m (f x) (g x)

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: [StarRing R] [ContinuousStar R]
  body: ⟨star f, by simp⟩
  star_involutive _ := ext fun _ => star_star _
  star_mul _ _ := ext fun _ => star_mul ..
  star_add _ _ := ext fun _ => star_add ..

中文:
实例 instStarRing
  签名: [对合环 R] [余ntinuousStar R]
  定义体: ⟨star f, by simp⟩
  star_involutive _ := ext fun _ => star_star _
  star_mul _ _ := ext fun _ => star_mul ..
  star_add _ _ := ext fun _ => star_add ..
-/
instance instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where
  star f := ⟨star f, by simp⟩
  star_involutive _ := ext fun _ => star_star _
  star_mul _ _ := ext fun _ => star_mul ..
  star_add _ _ := ext fun _ => star_add ..

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: [StarRing R] {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
  body: ext fun x => star_smul r (f x)

中文:
实例 instStarModule
  签名: [对合环 R] {M : 类型} [SMulZero类 M R] [连续常数标量乘法 M R]
  定义体: ext fun x => star_smul r (f x)

Depends on / 依赖: star_smul
-/
instance instStarModule [StarRing R] {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [Star M] [StarModule M R] [ContinuousStar R] : StarModule M C(X, R)₀ where
  star_smul r f := ext fun x => star_smul r (f x)

/--
lemma `coe_star` / 引理 `coe_star`

English:
lemma coe_star
  given: [StarRing R] [ContinuousStar R] (f : C(X, R)₀)
  statement: ⇑(star f) = star ⇑f
  proof: rfl

中文:
引理 coe_star
  条件: [对合环 R] [余ntinuousStar R] (f : C(X, R)₀)
  结论: ⇑(star f) = star ⇑f
  证明: rfl
-/
@[simp] lemma coe_star [StarRing R] [ContinuousStar R] (f : C(X, R)₀) : ⇑(star f) = star ⇑f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StarRing
  signature: R] [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  body: DFunLike.ext _ _ fun _ => star_trivial _

中文:
实例 [对合环
  签名: R] [余ntinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  定义体: DFunLike.ext _ _ fun _ => star_trivial _

Depends on / 依赖: DFunLike, DFunLike.ext, star_trivial
-/
instance [StarRing R] [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  star_trivial _ := DFunLike.ext _ _ fun _ => star_trivial _

/--
Instance `instCanLift` / 实例 `instCanLift`

English:
instance instCanLift
  signature: : CanLift C(X, R) C(X, R)₀ (↑) (fun f => f 0 = 0) where
  body: ⟨⟨f, hf⟩, rfl⟩

中文:
实例 instCanLift
  签名: : CanLift C(X, R) C(X, R)₀ (↑) (fun f => f 0 = 0) where
  定义体: ⟨⟨f, hf⟩, rfl⟩
-/
instance instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f => f 0 = 0) where
  prf f hf := ⟨⟨f, hf⟩, rfl⟩

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a non-unital star algebra homomorphism. -/
@[simps]
/--
Definition of `toContinuousMapHom` / `toContinuousMapHom` 的定义

English:
definition toContinuousMapHom
  signature: [StarRing R] [ContinuousStar R]
  body: f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

中文:
定义 toContinuousMapHom
  签名: [对合环 R] [余ntinuousStar R]
  定义体: f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
-/
def toContinuousMapHom [StarRing R] [ContinuousStar R] : C(X, R)₀ ->⋆ₙₐ[R] C(X, R) where
  toFun f := f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/--
lemma `coe_toContinuousMapHom` / 引理 `coe_toContinuousMapHom`

English:
lemma coe_toContinuousMapHom
  given: [StarRing R] [ContinuousStar R]
  proof: rfl

中文:
引理 coe_toContinuousMapHom
  条件: [对合环 R] [余ntinuousStar R]
  证明: rfl
-/
@[simp] lemma coe_toContinuousMapHom [StarRing R] [ContinuousStar R] :
    ⇑(toContinuousMapHom (X := X) (R := R)) = (↑) :=
  rfl

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a continuous linear map. -/
@[simps]
/--
Definition of `toContinuousMapCLM` / `toContinuousMapCLM` 的定义

English:
definition toContinuousMapCLM
  signature: (M : Type*) [Semiring M] [Module M R] [ContinuousConstSMul M R]
  body: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 toContinuousMapCLM
  签名: (M : 类型) [半环 M] [模 M R] [连续常数标量乘法 M R]
  定义体: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def toContinuousMapCLM (M : Type*) [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    C(X, R)₀ ->L[M] C(X, R) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `evalCLM` / `evalCLM` 的定义

English:
definition evalCLM
  signature: (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R] (x : X)
  body: (ContinuousMap.evalCLM 𝕜 x).comp (toContinuousMapCLM 𝕜)

@[simp]

中文:
定义 evalCLM
  签名: (𝕜 : 类型) [半环 𝕜] [模 𝕜 R] [连续常数标量乘法 𝕜 R] (x : X)
  定义体: (ContinuousMap.evalCLM 𝕜 x).comp (toContinuousMapCLM 𝕜)

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.evalCLM, evalCLM, toContinuousMapCLM
-/
def evalCLM (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R] (x : X) :
    C(X, R)₀ ->L[𝕜] R :=
  (ContinuousMap.evalCLM 𝕜 x).comp (toContinuousMapCLM 𝕜)

@[simp]
/--
lemma `evalCLM_apply` / 引理 `evalCLM_apply`

English:
lemma evalCLM_apply
  statement: {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R]
  proof: rfl

中文:
引理 evalCLM_apply
  结论: {𝕜 : 类型} [半环 𝕜] [模 𝕜 R] [连续常数标量乘法 𝕜 R]
  证明: rfl
-/
lemma evalCLM_apply {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R]
    (x : X) (f : C(X, R)₀) : evalCLM 𝕜 x f = f x := rfl

/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : C(X, R)₀ ->+ X -> R where
  body: f
  map_zero' := coe_zero
  map_add' f g := by simp

@[simp]

中文:
定义 coeFnAddMonoidHom
  签名: : C(X, R)₀ ->+ X -> R where
  定义体: f
  map_zero' := coe_zero
  map_add' f g := by simp

@[simp]
-/
def coeFnAddMonoidHom : C(X, R)₀ ->+ X -> R where
  toFun f := f
  map_zero' := coe_zero
  map_add' f g := by simp

@[simp]
/--
lemma `coeFnAddMonoidHom_apply` / 引理 `coeFnAddMonoidHom_apply`

English:
lemma coeFnAddMonoidHom_apply
  given: (f : C(X, R)₀)
  statement: coeFnAddMonoidHom f = f
  proof: rfl

中文:
引理 coeFnAddMonoidHom_apply
  条件: (f : C(X, R)₀)
  结论: coeFnAddMonoidHom f = f
  证明: rfl
-/
lemma coeFnAddMonoidHom_apply (f : C(X, R)₀) : coeFnAddMonoidHom f = f := rfl

/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  statement: {ι : Type*} (s : Finset ι)
  proof: map_sum coeFnAddMonoidHom f s

中文:
引理 coe_sum
  结论: {ι : 类型} (s : 有限集 ι)
  证明: map_sum coeFnAddMonoidHom f s
-/
@[simp] lemma coe_sum {ι : Type*} (s : Finset ι)
    (f : ι -> C(X, R)₀) : ⇑(s.sum f) = s.sum (fun i => ⇑(f i)) :=
  map_sum coeFnAddMonoidHom f s

end Semiring

section Ring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: : NonUnitalCommRing C(X, R)₀
  body: fast_instance% toContinuousMap_injective.nonUnitalCommRing _ rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 instNonUnitalCommRing
  签名: : 非幺交换环 C(X, R)₀
  定义体: fast_instance% toContinuousMap_injective.nonUnitalCommRing _ rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: fast_instance, nonUnitalCommRing, toContinuousMap_injective, toContinuousMap_injective.nonUnitalCommRing
-/
instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.nonUnitalCommRing _ rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg C(X, R)₀
  body: by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

中文:
实例 :
  签名: 连续取负 C(X, R)₀
  定义体: by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

Depends on / 依赖: continuous_induced_dom, continuous_induced_rng, continuous_neg, continuous_neg.comp
-/
instance : ContinuousNeg C(X, R)₀ where
  continuous_neg := by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

end Ring

end Algebra

section UniformSpace

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [Zero R] [UniformSpace R]

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace C(X, R)₀
  body: fast_instance% .comap toContinuousMap inferInstance

中文:
实例 instUniformSpace
  签名: : 一致空间 C(X, R)₀
  定义体: fast_instance% .comap toContinuousMap inferInstance
-/
protected instance instUniformSpace : UniformSpace C(X, R)₀ :=
  fast_instance% .comap toContinuousMap inferInstance

/--
lemma `isUniformEmbedding_toContinuousMap` / 引理 `isUniformEmbedding_toContinuousMap`

English:
lemma isUniformEmbedding_toContinuousMap
  proof: rfl
  injective _ _ h := ext fun x => congr($(h) x)

中文:
引理 isUniformEmbedding_toContinuousMap
  证明: rfl
  injective _ _ h := ext fun x => congr($(h) x)
-/
lemma isUniformEmbedding_toContinuousMap :
    IsUniformEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where
  comap_uniformity := rfl
  injective _ _ h := ext fun x => congr($(h) x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: R] [CompleteSpace C(X, R)] : CompleteSpace C(X, R)₀
  body: completeSpace_iff_isComplete_range isUniformEmbedding_toContinuousMap.isUniformInducing
.mpr isClosedEmbedding_toContinuousMap.isClosed_range.isComplete

中文:
实例 [T1空间
  签名: R] [完备空间 C(X, R)] : 完备空间 C(X, R)₀
  定义体: completeSpace_iff_isComplete_range isUniformEmbedding_toContinuousMap.isUniformInducing
.mpr isClosedEmbedding_toContinuousMap.isClosed_range.isComplete

Depends on / 依赖: completeSpace_iff_isComplete_range, isClosedEmbedding_toContinuousMap, isClosedEmbedding_toContinuousMap.isClosed_range.isComplete, isClosed_range, isComplete, isUniformEmbedding_toContinuousMap, isUniformEmbedding_toContinuousMap.isUniformInducing, isUniformInducing
-/
instance [T1Space R] [CompleteSpace C(X, R)] : CompleteSpace C(X, R)₀ :=
  completeSpace_iff_isComplete_range isUniformEmbedding_toContinuousMap.isUniformInducing
.mpr isClosedEmbedding_toContinuousMap.isClosed_range.isComplete

/--
lemma `isUniformEmbedding_comp` / 引理 `isUniformEmbedding_comp`

English:
lemma isUniformEmbedding_comp
  statement: {Y : Type*} [UniformSpace Y] [Zero Y] (g : C(Y, R)₀)
  proof: isUniformEmbedding_toContinuousMap.of_comp_iff.mp
.comp ContinuousMap.isUniformEmbedding_comp g.toContinuousMap hg
      isUniformEmbedding_toContinuousMap

中文:
引理 isUniformEmbedding_comp
  结论: {Y : 类型} [一致空间 Y] [零 Y] (g : C(Y, R)₀)
  证明: isUniformEmbedding_toContinuousMap.of_comp_iff.mp
.comp ContinuousMap.isUniformEmbedding_comp g.toContinuousMap hg
      isUniformEmbedding_toContinuousMap

Depends on / 依赖: ContinuousMap, ContinuousMap.isUniformEmbedding_comp, g.toContinuousMap, isUniformEmbedding_comp, isUniformEmbedding_toContinuousMap, isUniformEmbedding_toContinuousMap.of_comp_iff.mp, of_comp_iff, toContinuousMap
-/
lemma isUniformEmbedding_comp {Y : Type*} [UniformSpace Y] [Zero Y] (g : C(Y, R)₀)
    (hg : IsUniformEmbedding g) : IsUniformEmbedding (g.comp · : C(X, Y)₀ -> C(X, R)₀) :=
isUniformEmbedding_toContinuousMap.of_comp_iff.mp
.comp ContinuousMap.isUniformEmbedding_comp g.toContinuousMap hg
      isUniformEmbedding_toContinuousMap

/--
Definition of `_root_.UniformEquiv.arrowCongrLeft₀` / `_root_.UniformEquiv.arrowCongrLeft₀` 的定义

English:
definition _root_.UniformEquiv.arrowCongrLeft₀
  signature: {Y : Type*} [TopologicalSpace Y] [Zero Y] (f : X ≃ₜ Y)
  body: g.comp ⟨f.symm, (f.eq_symm_apply.eq ▸ hf).symm⟩
  invFun g := g.comp ⟨f, hf⟩
left_inv g := ext fun _ => congrArg g f.left_inv _
right_inv g := ext fun _ => congrArg g f.right_inv _
uniformContinuous_toFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f.symm : C(Y, X))
    isUniformEmbedding_toContinuousMap.uniformContinuous
uniformContinuous_invFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f : C(X, Y))
    isUniformEmbedding_toContinuousMap.uniformContinuous

中文:
定义 _root_.一致等价.arrowCongrLeft₀
  签名: {Y : 类型} [拓扑空间 Y] [零 Y] (f : X ≃ₜ Y)
  定义体: g.comp ⟨f.symm, (f.eq_symm_apply.eq ▸ hf).symm⟩
  invFun g := g.comp ⟨f, hf⟩
left_inv g := ext fun _ => congrArg g f.left_inv _
right_inv g := ext fun _ => congrArg g f.right_inv _
uniformContinuous_toFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f.symm : C(Y, X))
    isUniformEmbedding_toContinuousMap.uniformContinuous
uniformContinuous_invFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f : C(X, Y))
    isUniformEmbedding_toContinuousMap.uniformContinuous

Depends on / 依赖: eq_symm_apply, f.eq_symm_apply.eq, f.symm, g.comp
-/
def _root_.UniformEquiv.arrowCongrLeft₀ {Y : Type*} [TopologicalSpace Y] [Zero Y] (f : X ≃ₜ Y)
    (hf : f 0 = 0) : C(X, R)₀ ≃ᵤ C(Y, R)₀ where
  toFun g := g.comp ⟨f.symm, (f.eq_symm_apply.eq ▸ hf).symm⟩
  invFun g := g.comp ⟨f, hf⟩
left_inv g := ext fun _ => congrArg g f.left_inv _
right_inv g := ext fun _ => congrArg g f.right_inv _
uniformContinuous_toFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f.symm : C(Y, X))
    isUniformEmbedding_toContinuousMap.uniformContinuous
uniformContinuous_invFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr
.comp ContinuousMap.uniformContinuous_comp_left (f : C(X, Y))
    isUniformEmbedding_toContinuousMap.uniformContinuous

end UniformSpace

section CompHoms

variable {X Y M R S : Type*} [Zero X] [Zero Y] [CommSemiring M]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R] [TopologicalSpace S]
  [CommSemiring R] [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R]
  [CommSemiring S] [StarRing S] [IsTopologicalSemiring S] [ContinuousStar S]
  [Module M R] [Module M S] [ContinuousConstSMul M R] [ContinuousConstSMul M S]

variable (R) in
/-- The functor `C(·, R)₀` from topological spaces with zero (and `ContinuousMapZero` maps) to
non-unital star algebras. -/
@[simps]
/--
Definition of `nonUnitalStarAlgHom_precomp` / `nonUnitalStarAlgHom_precomp` 的定义

English:
definition nonUnitalStarAlgHom_precomp
  signature: (f : C(X, Y)₀)
  body: g.comp f
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

中文:
定义 nonUnitalStarAlgHom_precomp
  签名: (f : C(X, Y)₀)
  定义体: g.comp f
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: g.comp
-/
def nonUnitalStarAlgHom_precomp (f : C(X, Y)₀) : C(Y, R)₀ ->⋆ₙₐ[R] C(X, R)₀ where
  toFun g := g.comp f
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/-- The functor `C(X, ·)₀` from non-unital topological star algebras (with non-unital continuous
star homomorphisms) to non-unital star algebras. -/
@[simps apply]
/--
Definition of `nonUnitalStarAlgHom_postcomp` / `nonUnitalStarAlgHom_postcomp` 的定义

English:
definition nonUnitalStarAlgHom_postcomp
  signature: (φ : R ->⋆ₙₐ[M] S) (hφ : Continuous φ)
  body: .comp ⟨⟨φ, hφ⟩, by simp⟩
map_zero' := ext by simp
map_add' _ _ := ext by simp
map_mul' _ _ := ext by simp
map_star' _ := ext by simp [map_star]
map_smul' r f := ext by simp

中文:
定义 nonUnitalStarAlgHom_postcomp
  签名: (φ : R ->⋆ₙₐ[M] S) (hφ : 连续 φ)
  定义体: .comp ⟨⟨φ, hφ⟩, by simp⟩
map_zero' := ext by simp
map_add' _ _ := ext by simp
map_mul' _ _ := ext by simp
map_star' _ := ext by simp [map_star]
map_smul' r f := ext by simp
-/
def nonUnitalStarAlgHom_postcomp (φ : R ->⋆ₙₐ[M] S) (hφ : Continuous φ) :
    C(X, R)₀ ->⋆ₙₐ[M] C(X, S)₀ where
  toFun := .comp ⟨⟨φ, hφ⟩, by simp⟩
map_zero' := ext by simp
map_add' _ _ := ext by simp
map_mul' _ _ := ext by simp
map_star' _ := ext by simp [map_star]
map_smul' r f := ext by simp

end CompHoms

section Norm

variable {α : Type*} {𝕜 : Type*} {R : Type*} [TopologicalSpace α] [CompactSpace α] [Zero α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: R] [Zero R] : MetricSpace C(α, R)₀
  body: ContinuousMapZero.isUniformEmbedding_toContinuousMap.comapMetricSpace _

中文:
实例 [度量空间
  签名: R] [零 R] : 度量空间 C(α, R)₀
  定义体: ContinuousMapZero.isUniformEmbedding_toContinuousMap.comapMetricSpace _

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isUniformEmbedding_toContinuousMap.comapMetricSpace, comapMetricSpace, isUniformEmbedding_toContinuousMap
-/
noncomputable instance [MetricSpace R] [Zero R] : MetricSpace C(α, R)₀ :=
  ContinuousMapZero.isUniformEmbedding_toContinuousMap.comapMetricSpace _

/--
lemma `isometry_toContinuousMap` / 引理 `isometry_toContinuousMap`

English:
lemma isometry_toContinuousMap
  given: [MetricSpace R] [Zero R]
  proof: fun _ _ => rfl

中文:
引理 isometry_toContinuousMap
  条件: [度量空间 R] [零 R]
  证明: fun _ _ => rfl
-/
lemma isometry_toContinuousMap [MetricSpace R] [Zero R] :
    Isometry (toContinuousMap : C(α, R)₀ -> C(α, R)) :=
  fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedAddCommGroup
  signature: R] : Norm C(α, R)₀ where
  body: ‖(f : C(α, R))‖

中文:
实例 [赋范交换加群
  签名: R] : 范数 C(α, R)₀ where
  定义体: ‖(f : C(α, R))‖
-/
noncomputable instance [NormedAddCommGroup R] : Norm C(α, R)₀ where
  norm f := ‖(f : C(α, R))‖

/--
lemma `norm_def` / 引理 `norm_def`

English:
lemma norm_def
  given: [NormedAddCommGroup R] (f : C(α, R)₀)
  statement: ‖f‖ = ‖(f : C(α, R))‖
  proof: rfl

中文:
引理 norm_def
  条件: [赋范交换加群 R] (f : C(α, R)₀)
  结论: ‖f‖ = ‖(f : C(α, R))‖
  证明: rfl
-/
lemma norm_def [NormedAddCommGroup R] (f : C(α, R)₀) : ‖f‖ = ‖(f : C(α, R))‖ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedAddCommGroup
  signature: R] : NormedAddCommGroup C(α, R)₀ where
  body: NormedAddGroup.dist_eq (f : C(α, R)) g

中文:
实例 [赋范交换加群
  签名: R] : 赋范交换加群 C(α, R)₀ where
  定义体: NormedAddGroup.dist_eq (f : C(α, R)) g

Depends on / 依赖: NormedAddGroup, NormedAddGroup.dist_eq, dist_eq
-/
noncomputable instance [NormedAddCommGroup R] : NormedAddCommGroup C(α, R)₀ where
  dist_eq f g := NormedAddGroup.dist_eq (f : C(α, R)) g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedCommRing
  signature: R] : NonUnitalNormedCommRing C(α, R)₀ where
  body: NormedAddGroup.dist_eq (f : C(α, R)) g
  norm_mul_le f g := norm_mul_le (f : C(α, R)) g
  mul_comm f g := mul_comm f g

中文:
实例 [NormedComm环
  签名: R] : 非幺NormedComm环 C(α, R)₀ where
  定义体: NormedAddGroup.dist_eq (f : C(α, R)) g
  norm_mul_le f g := norm_mul_le (f : C(α, R)) g
  mul_comm f g := mul_comm f g

Depends on / 依赖: NormedAddGroup, NormedAddGroup.dist_eq, dist_eq
-/
noncomputable instance [NormedCommRing R] : NonUnitalNormedCommRing C(α, R)₀ where
  dist_eq f g := NormedAddGroup.dist_eq (f : C(α, R)) g
  norm_mul_le f g := norm_mul_le (f : C(α, R)) g
  mul_comm f g := mul_comm f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] :
  body: norm_smul_le r (f : C(α, R))

中文:
实例 [赋范域
  签名: 𝕜] [NormedComm环 R] [赋范代数 𝕜 R] :
  定义体: norm_smul_le r (f : C(α, R))

Depends on / 依赖: norm_smul_le
-/
noncomputable instance [NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] :
    NormedSpace 𝕜 C(α, R)₀ where
  norm_smul_le r f := norm_smul_le r (f : C(α, R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedCommRing
  signature: R] [StarRing R] [CStarRing R] : CStarRing C(α, R)₀ where
  body: CStarRing.norm_mul_self_le (f : C(α, R))

中文:
实例 [NormedComm环
  签名: R] [对合环 R] [CStar环 R] : CStar环 C(α, R)₀ where
  定义体: CStarRing.norm_mul_self_le (f : C(α, R))

Depends on / 依赖: CStarRing, CStarRing.norm_mul_self_le, norm_mul_self_le
-/
instance [NormedCommRing R] [StarRing R] [CStarRing R] : CStarRing C(α, R)₀ where
  norm_mul_self_le f := CStarRing.norm_mul_self_le (f : C(α, R))

end Norm

end ContinuousMapZero
