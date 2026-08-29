/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous alternating multilinear maps

In this file we define bundled continuous alternating maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and alternating maps.

## Notation

`M [⋀^ι]→L[R] N`: notation for `R`-linear continuous alternating maps from `M` to `N`; the arguments
are indexed by `i : ι`.

## Keywords

multilinear map, alternating map, continuous
-/

@[expose] public section

open Function Matrix

/--
Definition of `ContinuousAlternatingMap` / `ContinuousAlternatingMap` 的定义

English:
structure ContinuousAlternatingMap
  parameters: (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  (no additional axioms)

中文:
结构 余ntinuousAlternating映射
  参数: (R M N ι : 类型) [半环 R] [加法交换幺半群 M] [模 R M]
  (无附加公理)
-/
structure ContinuousAlternatingMap (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι => M) N, M [⋀^ι]->ₗ[R] N where

/-- Projection to `ContinuousMultilinearMap`s. -/
add_decl_doc ContinuousAlternatingMap.toContinuousMultilinearMap

/-- Projection to `AlternatingMap`s. -/
add_decl_doc ContinuousAlternatingMap.toAlternatingMap

@[inherit_doc]
notation M " [⋀^" ι "]->L[" R "] " N:100 => ContinuousAlternatingMap R M N ι

namespace ContinuousAlternatingMap

section Semiring

variable {R M M' N N' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : Nat}
  (f g : M [⋀^ι]->L[R] N)

/--
theorem `toContinuousMultilinearMap_injective` / 定理 `toContinuousMultilinearMap_injective`

English:
theorem toContinuousMultilinearMap_injective

中文:
定理 toContinuousMultilinearMap_injective
-/
theorem toContinuousMultilinearMap_injective :
    Injective (ContinuousAlternatingMap.toContinuousMultilinearMap :
      M [⋀^ι]->L[R] N -> ContinuousMultilinearMap R (fun _ : ι => M) N)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `range_toContinuousMultilinearMap` / 定理 `range_toContinuousMultilinearMap`

English:
theorem range_toContinuousMultilinearMap
  proof: Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

中文:
定理 range_toContinuousMultilinearMap
  证明: Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

Depends on / 依赖: Set.ext
-/
theorem range_toContinuousMultilinearMap :
    Set.range
        (toContinuousMultilinearMap :
          M [⋀^ι]->L[R] N -> ContinuousMultilinearMap R (fun _ : ι => M) N) =
      {f | forall (v : ι -> M) (i j : ι), v i = v j -> i != j -> f v = 0} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (M [⋀^ι]->L[R] N) (ι -> M) N where
  body: f.toFun
coe_injective _ _ h := toContinuousMultilinearMap_injective DFunLike.ext' h

中文:
实例 funLike
  签名: : 函数状 (M [⋀^ι]->L[R] N) (ι -> M) N where
  定义体: f.toFun
coe_injective _ _ h := toContinuousMultilinearMap_injective DFunLike.ext' h

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (M [⋀^ι]->L[R] N) (ι -> M) N where
  coe f := f.toFun
coe_injective _ _ h := toContinuousMultilinearMap_injective DFunLike.ext' h

/--
Instance `continuousMapClass` / 实例 `continuousMapClass`

English:
instance continuousMapClass
  signature: : ContinuousMapClass (M [⋀^ι]->L[R] N) (ι -> M) N where
  body: f.cont

initialize_simps_projections ContinuousAlternatingMap (toFun -> apply)

@[continuity]

中文:
实例 continuousMapClass
  签名: : 连续映射类 (M [⋀^ι]->L[R] N) (ι -> M) N where
  定义体: f.cont

initialize_simps_projections ContinuousAlternatingMap (toFun -> apply)

@[continuity]

Depends on / 依赖: f.cont
-/
instance continuousMapClass : ContinuousMapClass (M [⋀^ι]->L[R] N) (ι -> M) N where
  map_continuous f := f.cont

initialize_simps_projections ContinuousAlternatingMap (toFun -> apply)

@[continuity]
/--
theorem `coe_continuous` / 定理 `coe_continuous`

English:
theorem coe_continuous
  statement: Continuous f
  proof: f.cont

@[simp]

中文:
定理 coe_continuous
  结论: 连续 f
  证明: f.cont

@[simp]

Depends on / 依赖: f.cont
-/
theorem coe_continuous : Continuous f := f.cont

@[simp]
/--
theorem `coe_toContinuousMultilinearMap` / 定理 `coe_toContinuousMultilinearMap`

English:
theorem coe_toContinuousMultilinearMap
  statement: ⇑f.toContinuousMultilinearMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousMultilinearMap
  结论: ⇑f.toContinuousMultilinearMap = f
  证明: rfl

@[simp]
-/
theorem coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h)
  statement: ⇑(mk f h) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : 连续多重线性映射 R (fun _ : ι => M) N) (h)
  结论: ⇑(mk f h) = f
  证明: rfl
-/
theorem coe_mk (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h) : ⇑(mk f h) = f :=
  rfl

-- not a `simp` lemma because this projection is a reducible call to `mk`, so `simp` can prove
-- this lemma
/--
theorem `coe_toAlternatingMap` / 定理 `coe_toAlternatingMap`

English:
theorem coe_toAlternatingMap
  statement: ⇑f.toAlternatingMap = f
  proof: rfl

@[ext]

中文:
定理 coe_toAlternatingMap
  结论: ⇑f.toAlternatingMap = f
  证明: rfl

@[ext]
-/
theorem coe_toAlternatingMap : ⇑f.toAlternatingMap = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M [⋀^ι]->L[R] N} (H : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: {f g : M [⋀^ι]->L[R] N} (H : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : M [⋀^ι]->L[R] N} (H : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ H

/--
theorem `toAlternatingMap_injective` / 定理 `toAlternatingMap_injective`

English:
theorem toAlternatingMap_injective
  proof: fun f g h =>
DFunLike.ext' by convert! DFunLike.ext'_iff.1 h

@[simp]

中文:
定理 toAlternatingMap_injective
  证明: fun f g h =>
DFunLike.ext' by convert! DFunLike.ext'_iff.1 h

@[simp]
-/
theorem toAlternatingMap_injective :
    Injective (toAlternatingMap : (M [⋀^ι]->L[R] N) -> (M [⋀^ι]->ₗ[R] N)) := fun f g h =>
DFunLike.ext' by convert! DFunLike.ext'_iff.1 h

@[simp]
/--
theorem `range_toAlternatingMap` / 定理 `range_toAlternatingMap`

English:
theorem range_toAlternatingMap
  proof: Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, DFunLike.ext' rfl⟩⟩

@[simp]

中文:
定理 range_toAlternatingMap
  证明: Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, DFunLike.ext' rfl⟩⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext, Set.ext, g.cont
-/
theorem range_toAlternatingMap :
    Set.range (toAlternatingMap : M [⋀^ι]->L[R] N -> (M [⋀^ι]->ₗ[R] N)) =
      {f : M [⋀^ι]->ₗ[R] N | Continuous f} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, DFunLike.ext' rfl⟩⟩

@[simp]
/--
theorem `map_update_add` / 定理 `map_update_add`

English:
theorem map_update_add
  given: [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M)
  proof: f.map_update_add' m i x y

@[simp]

中文:
定理 map_update_add
  条件: [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M)
  证明: f.map_update_add' m i x y

@[simp]

Depends on / 依赖: f.map_update_add, map_update_add
-/
theorem map_update_add [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
/--
theorem `map_update_smul` / 定理 `map_update_smul`

English:
theorem map_update_smul
  given: [DecidableEq ι] (m : ι -> M) (i : ι) (c : R) (x : M)
  proof: f.map_update_smul' m i c x

中文:
定理 map_update_smul
  条件: [DecidableEq ι] (m : ι -> M) (i : ι) (c : R) (x : M)
  证明: f.map_update_smul' m i c x

Depends on / 依赖: f.map_update_smul, map_update_smul
-/
theorem map_update_smul [DecidableEq ι] (m : ι -> M) (i : ι) (c : R) (x : M) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x

/--
theorem `map_coord_zero` / 定理 `map_coord_zero`

English:
theorem map_coord_zero
  given: {m : ι -> M} (i : ι) (h : m i = 0)
  statement: f m = 0
  proof: f.toMultilinearMap.map_coord_zero i h

@[simp]

中文:
定理 map_coord_zero
  条件: {m : ι -> M} (i : ι) (h : m i = 0)
  结论: f m = 0
  证明: f.toMultilinearMap.map_coord_zero i h

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_coord_zero, map_coord_zero, toMultilinearMap
-/
theorem map_coord_zero {m : ι -> M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/--
theorem `map_update_zero` / 定理 `map_update_zero`

English:
theorem map_update_zero
  given: [DecidableEq ι] (m : ι -> M) (i : ι)
  statement: f (update m i 0) = 0
  proof: f.toMultilinearMap.map_update_zero m i

@[simp]

中文:
定理 map_update_zero
  条件: [DecidableEq ι] (m : ι -> M) (i : ι)
  结论: f (update m i 0) = 0
  证明: f.toMultilinearMap.map_update_zero m i

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_update_zero, map_update_zero, toMultilinearMap
-/
theorem map_update_zero [DecidableEq ι] (m : ι -> M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: [Nonempty ι]
  statement: f 0 = 0
  proof: f.toMultilinearMap.map_zero

中文:
定理 map_zero
  条件: [非空 ι]
  结论: f 0 = 0
  证明: f.toMultilinearMap.map_zero

Depends on / 依赖: f.toMultilinearMap.map_zero, map_zero, toMultilinearMap
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

/--
theorem `map_eq_zero_of_eq` / 定理 `map_eq_zero_of_eq`

English:
theorem map_eq_zero_of_eq
  given: (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j)
  statement: f v = 0
  proof: f.map_eq_zero_of_eq' v i j h hij

中文:
定理 map_eq_zero_of_eq
  条件: (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j)
  结论: f v = 0
  证明: f.map_eq_zero_of_eq' v i j h hij

Depends on / 依赖: f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
theorem map_eq_zero_of_eq (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

/--
theorem `map_eq_zero_of_not_injective` / 定理 `map_eq_zero_of_not_injective`

English:
theorem map_eq_zero_of_not_injective
  given: (v : ι -> M) (hv : ¬Function.Injective v)
  statement: f v = 0
  proof: f.toAlternatingMap.map_eq_zero_of_not_injective v hv

中文:
定理 map_eq_zero_of_not_injective
  条件: (v : ι -> M) (hv : ¬函数.单射 v)
  结论: f v = 0
  证明: f.toAlternatingMap.map_eq_zero_of_not_injective v hv

Depends on / 依赖: f.toAlternatingMap.map_eq_zero_of_not_injective, map_eq_zero_of_not_injective, toAlternatingMap
-/
theorem map_eq_zero_of_not_injective (v : ι -> M) (hv : ¬Function.Injective v) : f v = 0 :=
  f.toAlternatingMap.map_eq_zero_of_not_injective v hv

/-- Restrict the codomain of a continuous alternating map to a submodule. -/
@[simps!]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : M [⋀^ι]->L[R] N) (p : Submodule R N) (h : forall v, f v in p)
  body: { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }

中文:
定义 codRestrict
  签名: (f : M [⋀^ι]->L[R] N) (p : 子模 R N) (h : 对任意 v, f v in p)
  定义体: { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }

Depends on / 依赖: codRestrict, f.toAlternatingMap.codRestrict, toAlternatingMap, toContinuousMultilinearMap
-/
def codRestrict (f : M [⋀^ι]->L[R] N) (p : Submodule R N) (h : forall v, f v in p) : M [⋀^ι]->L[R] p :=
  { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M [⋀^ι]->L[R] N)
  body: ⟨⟨0, (0 : M [⋀^ι]->ₗ[R] N).map_eq_zero_of_eq⟩⟩

中文:
实例 :
  签名: 零 (M [⋀^ι]->L[R] N)
  定义体: ⟨⟨0, (0 : M [⋀^ι]->ₗ[R] N).map_eq_zero_of_eq⟩⟩

Depends on / 依赖: map_eq_zero_of_eq
-/
instance : Zero (M [⋀^ι]->L[R] N) :=
  ⟨⟨0, (0 : M [⋀^ι]->ₗ[R] N).map_eq_zero_of_eq⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M [⋀^ι]->L[R] N)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (M [⋀^ι]->L[R] N)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (M [⋀^ι]->L[R] N) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : M [⋀^ι]->L[R] N) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : M [⋀^ι]->L[R] N) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : M [⋀^ι]->L[R] N) = 0 :=
  rfl

@[simp]
/--
theorem `toContinuousMultilinearMap_zero` / 定理 `toContinuousMultilinearMap_zero`

English:
theorem toContinuousMultilinearMap_zero
  statement: (0 : M [⋀^ι]->L[R] N).toContinuousMultilinearMap = 0
  proof: rfl

@[simp]

中文:
定理 toContinuousMultilinearMap_zero
  结论: (0 : M [⋀^ι]->L[R] N).toContinuousMultilinearMap = 0
  证明: rfl

@[simp]
-/
theorem toContinuousMultilinearMap_zero : (0 : M [⋀^ι]->L[R] N).toContinuousMultilinearMap = 0 :=
  rfl

@[simp]
/--
theorem `toAlternatingMap_zero` / 定理 `toAlternatingMap_zero`

English:
theorem toAlternatingMap_zero
  statement: (0 : M [⋀^ι]->L[R] N).toAlternatingMap = 0
  proof: rfl

中文:
定理 toAlternatingMap_zero
  结论: (0 : M [⋀^ι]->L[R] N).toAlternatingMap = 0
  证明: rfl
-/
theorem toAlternatingMap_zero : (0 : M [⋀^ι]->L[R] N).toAlternatingMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M] [Module A N]
  [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N] [DistribMulAction R'' N]
  [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R' (M [⋀^ι]->L[A] N)
  body: ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]

中文:
实例 :
  签名: 标量乘法 R' (M [⋀^ι]->L[A] N)
  定义体: ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]

Depends on / 依赖: f.toAlternatingMap, map_eq_zero_of_eq, toAlternatingMap
-/
instance : SMul R' (M [⋀^ι]->L[A] N) :=
  ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (f : M [⋀^ι]->L[A] N) (c : R')
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

中文:
定理 coe_smul
  条件: (f : M [⋀^ι]->L[A] N) (c : R')
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl
-/
theorem coe_smul (f : M [⋀^ι]->L[A] N) (c : R') : ⇑(c • f) = c • ⇑f :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (f : M [⋀^ι]->L[A] N) (c : R') (v : ι -> M)
  statement: (c • f) v = c • f v
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: (f : M [⋀^ι]->L[A] N) (c : R') (v : ι -> M)
  结论: (c • f) v = c • f v
  证明: rfl

@[simp]
-/
theorem smul_apply (f : M [⋀^ι]->L[A] N) (c : R') (v : ι -> M) : (c • f) v = c • f v :=
  rfl

@[simp]
/--
theorem `toContinuousMultilinearMap_smul` / 定理 `toContinuousMultilinearMap_smul`

English:
theorem toContinuousMultilinearMap_smul
  given: (c : R') (f : M [⋀^ι]->L[A] N)
  proof: rfl

@[simp]

中文:
定理 toContinuousMultilinearMap_smul
  条件: (c : R') (f : M [⋀^ι]->L[A] N)
  证明: rfl

@[simp]
-/
theorem toContinuousMultilinearMap_smul (c : R') (f : M [⋀^ι]->L[A] N) :
    (c • f).toContinuousMultilinearMap = c • f.toContinuousMultilinearMap :=
  rfl

@[simp]
/--
theorem `toAlternatingMap_smul` / 定理 `toAlternatingMap_smul`

English:
theorem toAlternatingMap_smul
  given: (c : R') (f : M [⋀^ι]->L[A] N)
  proof: rfl

中文:
定理 toAlternatingMap_smul
  条件: (c : R') (f : M [⋀^ι]->L[A] N)
  证明: rfl
-/
theorem toAlternatingMap_smul (c : R') (f : M [⋀^ι]->L[A] N) :
    (c • f).toAlternatingMap = c • f.toAlternatingMap :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R' R'' N] : SMulCommClass R' R'' (M [⋀^ι]->L[A] N)
  body: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

中文:
实例 [标量交换类
  签名: R' R'' N] : 标量交换类 R' R'' (M [⋀^ι]->L[A] N)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' (M [⋀^ι]->L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' (M [⋀^ι]->L[A] N)
  body: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

中文:
实例 [标量乘法
  签名: R' R''] [标量塔 R' R'' N] : 标量塔 R' R'' (M [⋀^ι]->L[A] N)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc
-/
instance [SMul R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' (M [⋀^ι]->L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribMulAction
  signature: R'ᵐᵒᵖ N] [IsCentralScalar R' N] : IsCentralScalar R' (M [⋀^ι]->L[A] N)
  body: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

中文:
实例 [分配乘法作用
  签名: R'ᵐᵒᵖ N] [中心标量 R' N] : 中心标量 R' (M [⋀^ι]->L[A] N)
  定义体: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: op_smul_eq_smul
-/
instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] : IsCentralScalar R' (M [⋀^ι]->L[A] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction R' (M [⋀^ι]->L[A] N)
  body: fast_instance%
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

中文:
实例 :
  签名: 乘法作用 R' (M [⋀^ι]->L[A] N)
  定义体: fast_instance%
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : MulAction R' (M [⋀^ι]->L[A] N) := fast_instance%
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M [⋀^ι]->L[R] N)
  body: ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]

中文:
实例 :
  签名: 加法 (M [⋀^ι]->L[R] N)
  定义体: ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]

Depends on / 依赖: f.toAlternatingMap, g.toAlternatingMap, map_eq_zero_of_eq, toAlternatingMap
-/
instance : Add (M [⋀^ι]->L[R] N) :=
  ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ⇑(f + g) = ⇑f + ⇑g
  proof: rfl

@[simp]

中文:
定理 coe_add
  结论: ⇑(f + g) = ⇑f + ⇑g
  证明: rfl

@[simp]
-/
theorem coe_add : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (v : ι -> M)
  statement: (f + g) v = f v + g v
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (v : ι -> M)
  结论: (f + g) v = f v + g v
  证明: rfl

@[simp]
-/
theorem add_apply (v : ι -> M) : (f + g) v = f v + g v :=
  rfl

@[simp]
/--
theorem `toContinuousMultilinearMap_add` / 定理 `toContinuousMultilinearMap_add`

English:
theorem toContinuousMultilinearMap_add
  given: (f g : M [⋀^ι]->L[R] N)
  statement: (f + g).1 = f.1 + g.1
  proof: rfl

@[simp]

中文:
定理 toContinuousMultilinearMap_add
  条件: (f g : M [⋀^ι]->L[R] N)
  结论: (f + g).1 = f.1 + g.1
  证明: rfl

@[simp]
-/
theorem toContinuousMultilinearMap_add (f g : M [⋀^ι]->L[R] N) : (f + g).1 = f.1 + g.1 :=
  rfl

@[simp]
/--
theorem `toAlternatingMap_add` / 定理 `toAlternatingMap_add`

English:
theorem toAlternatingMap_add
  given: (f g : M [⋀^ι]->L[R] N)
  proof: rfl

中文:
定理 toAlternatingMap_add
  条件: (f g : M [⋀^ι]->L[R] N)
  证明: rfl
-/
theorem toAlternatingMap_add (f g : M [⋀^ι]->L[R] N) :
    (f + g).toAlternatingMap = f.toAlternatingMap + g.toAlternatingMap :=
  rfl

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (M [⋀^ι]->L[R] N)
  body: fast_instance%
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (M [⋀^ι]->L[R] N)
  定义体: fast_instance%
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance addCommMonoid : AddCommMonoid (M [⋀^ι]->L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Definition of `applyAddHom` / `applyAddHom` 的定义

English:
definition applyAddHom
  signature: (v : ι -> M)
  body: ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩

@[simp]

中文:
定义 applyAddHom
  签名: (v : ι -> M)
  定义体: ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩

@[simp]
-/
def applyAddHom (v : ι -> M) : M [⋀^ι]->L[R] N ->+ N :=
  ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: {α : Type*} (f : α -> M [⋀^ι]->L[R] N) (m : ι -> M) {s : Finset α}
  proof: map_sum (applyAddHom m) f s

中文:
定理 sum_apply
  条件: {α : 类型} (f : α -> M [⋀^ι]->L[R] N) (m : ι -> M) {s : 有限集 α}
  证明: map_sum (applyAddHom m) f s

Depends on / 依赖: applyAddHom, map_sum
-/
theorem sum_apply {α : Type*} (f : α -> M [⋀^ι]->L[R] N) (m : ι -> M) {s : Finset α} :
    (∑ a in s, f a) m = ∑ a in s, f a m :=
  map_sum (applyAddHom m) f s

/-- Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`. -/
@[simps]
/--
Definition of `toMultilinearAddHom` / `toMultilinearAddHom` 的定义

English:
definition toMultilinearAddHom
  signature: : M [⋀^ι]->L[R] N ->+ ContinuousMultilinearMap R (fun _ : ι => M) N
  body: ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩

中文:
定义 toMultilinearAddHom
  签名: : M [⋀^ι]->L[R] N ->+ 连续多重线性映射 R (fun _ : ι => M) N
  定义体: ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩
-/
def toMultilinearAddHom : M [⋀^ι]->L[R] N ->+ ContinuousMultilinearMap R (fun _ : ι => M) N :=
  ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩

end ContinuousAdd

/-- If `f` is a continuous alternating map, then `f.toContinuousLinearMap m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
@[simps! apply]
/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: [DecidableEq ι] (m : ι -> M) (i : ι)
  body: f.1.toContinuousLinearMap m i

中文:
定义 toContinuousLinearMap
  签名: [DecidableEq ι] (m : ι -> M) (i : ι)
  定义体: f.1.toContinuousLinearMap m i

Depends on / 依赖: toContinuousLinearMap
-/
def toContinuousLinearMap [DecidableEq ι] (m : ι -> M) (i : ι) : M ->L[R] N :=
  f.1.toContinuousLinearMap m i

/-- The Cartesian product of two continuous alternating maps, as a continuous alternating map. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : M [⋀^ι]->L[R] N) (g : M [⋀^ι]->L[R] N')
  body: ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩

中文:
定义 乘积
  签名: (f : M [⋀^ι]->L[R] N) (g : M [⋀^ι]->L[R] N')
  定义体: ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩

Depends on / 依赖: f.toAlternatingMap.prod, g.toAlternatingMap, map_eq_zero_of_eq, toAlternatingMap
-/
def prod (f : M [⋀^ι]->L[R] N) (g : M [⋀^ι]->L[R] N') : M [⋀^ι]->L[R] (N × N') :=
  ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, TopologicalSpace (M' i)]
  body: ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩

@[simp]

中文:
定义 pi
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)] [对任意 i, 拓扑空间 (M' i)]
  定义体: ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.pi, ContinuousMultilinearMap, ContinuousMultilinearMap.pi, map_eq_zero_of_eq, toAlternatingMap
-/
def pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, TopologicalSpace (M' i)]
    [forall i, Module R (M' i)] (f : forall i, M [⋀^ι]->L[R] M' i) : M [⋀^ι]->L[R] forall i, M' i :=
  ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩

@[simp]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  statement: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  proof: rfl

中文:
定理 coe_pi
  结论: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  证明: rfl
-/
theorem coe_pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, M [⋀^ι]->L[R] M' i) :
    ⇑(pi f) = fun m j => f j m :=
  rfl

/--
theorem `pi_apply` / 定理 `pi_apply`

English:
theorem pi_apply
  statement: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  proof: rfl

中文:
定理 pi_apply
  结论: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  证明: rfl
-/
theorem pi_apply {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, M [⋀^ι]->L[R] M' i) (m : ι -> M)
    (j : ι') : pi f m j = f j m :=
  rfl

section

variable (R M N)

/-- The natural equivalence between continuous linear maps from `M` to `N`
and continuous 1-multilinear alternating maps from `M` to `N`. -/
@[simps! apply_apply symm_apply_apply apply_toContinuousMultilinearMap]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: [Subsingleton ι] (i : ι)
  body: { AlternatingMap.ofSubsingleton R M N i f with
      toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R M N i f }
  invFun f := (ContinuousMultilinearMap.ofSubsingleton R M N i).symm f.1
right_inv _ := toContinuousMultilinearMap_injective
    (ContinuousMultilinearMap.ofSubsingl

中文:
定义 ofSubsingleton
  签名: [子单例 ι] (i : ι)
  定义体: { AlternatingMap.ofSubsingleton R M N i f with
      toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R M N i f }
  invFun f := (ContinuousMultilinearMap.ofSubsingleton R M N i).symm f.1
right_inv _ := toContinuousMultilinearMap_injective
    (ContinuousMultilinearMap.ofSubsingl

Depends on / 依赖: AlternatingMap, AlternatingMap.ofSubsingleton, ContinuousMultilinearMap, ContinuousMultilinearMap.ofSubsingleton, apply_symm_apply, invFun, ofSubsingleton, right_inv, toContinuousMultilinearMap, toContinuousMultilinearMap_injective
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M ->L[R] N) ≃ M [⋀^ι]->L[R] N where
  toFun f :=
    { AlternatingMap.ofSubsingleton R M N i f with
      toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R M N i f }
  invFun f := (ContinuousMultilinearMap.ofSubsingleton R M N i).symm f.1
right_inv _ := toContinuousMultilinearMap_injective
    (ContinuousMultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

@[simp]
/--
theorem `ofSubsingleton_toAlternatingMap` / 定理 `ofSubsingleton_toAlternatingMap`

English:
theorem ofSubsingleton_toAlternatingMap
  given: [Subsingleton ι] (i : ι) (f : M ->L[R] N)
  proof: rfl

中文:
定理 ofSubsingleton_toAlternatingMap
  条件: [子单例 ι] (i : ι) (f : M ->L[R] N)
  证明: rfl
-/
theorem ofSubsingleton_toAlternatingMap [Subsingleton ι] (i : ι) (f : M ->L[R] N) :
    (ofSubsingleton R M N i f).toAlternatingMap = AlternatingMap.ofSubsingleton R M N i f :=
  rfl

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps! toContinuousMultilinearMap apply]
/--
Definition of `constOfIsEmpty` / `constOfIsEmpty` 的定义

English:
definition constOfIsEmpty
  signature: [IsEmpty ι] (m : N)
  body: { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }

@[simp]

中文:
定义 constOfIsEmpty
  签名: [是空 ι] (m : N)
  定义体: { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.constOfIsEmpty, ContinuousMultilinearMap, ContinuousMultilinearMap.constOfIsEmpty, constOfIsEmpty, toContinuousMultilinearMap
-/
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]->L[R] N :=
  { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }

@[simp]
/--
theorem `constOfIsEmpty_toAlternatingMap` / 定理 `constOfIsEmpty_toAlternatingMap`

English:
theorem constOfIsEmpty_toAlternatingMap
  given: [IsEmpty ι] (m : N)
  proof: rfl

中文:
定理 constOfIsEmpty_toAlternatingMap
  条件: [是空 ι] (m : N)
  证明: rfl
-/
theorem constOfIsEmpty_toAlternatingMap [IsEmpty ι] (m : N) :
    (constOfIsEmpty R M ι m).toAlternatingMap = AlternatingMap.constOfIsEmpty R M ι m :=
  rfl

end

/--
Definition of `compContinuousLinearMap` / `compContinuousLinearMap` 的定义

English:
definition compContinuousLinearMap
  signature: (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M)
  body: { g.toAlternatingMap.compLinearMap (f : M' ->ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }

@[simp]

中文:
定义 compContinuousLinearMap
  签名: (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M)
  定义体: { g.toAlternatingMap.compLinearMap (f : M' ->ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }

@[simp]

Depends on / 依赖: compContinuousLinearMap, compLinearMap, g.toAlternatingMap.compLinearMap, toAlternatingMap, toContinuousMultilinearMap
-/
def compContinuousLinearMap (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) : M' [⋀^ι]->L[R] N :=
  { g.toAlternatingMap.compLinearMap (f : M' ->ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }

@[simp]
/--
theorem `compContinuousLinearMap_apply` / 定理 `compContinuousLinearMap_apply`

English:
theorem compContinuousLinearMap_apply
  given: (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) (m : ι -> M')
  proof: rfl

中文:
定理 compContinuousLinearMap_apply
  条件: (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) (m : ι -> M')
  证明: rfl
-/
theorem compContinuousLinearMap_apply (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) (m : ι -> M') :
    g.compContinuousLinearMap f m = g (f ∘ m) :=
  rfl

/--
Definition of `_root_.ContinuousLinearMap.compContinuousAlternatingMap` / `_root_.ContinuousLinearMap.compContinuousAlternatingMap` 的定义

English:
definition _root_.ContinuousLinearMap.compContinuousAlternatingMap
  signature: (g : N ->L[R] N') (f : M [⋀^ι]->L[R] N)
  body: { (g : N ->ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]

中文:
定义 _root_.连续线性映射.compContinuousAlternatingMap
  签名: (g : N ->L[R] N') (f : M [⋀^ι]->L[R] N)
  定义体: { (g : N ->ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]

Depends on / 依赖: compAlternatingMap, compContinuousMultilinearMap, f.toAlternatingMap, g.compContinuousMultilinearMap, toAlternatingMap, toContinuousMultilinearMap
-/
def _root_.ContinuousLinearMap.compContinuousAlternatingMap (g : N ->L[R] N') (f : M [⋀^ι]->L[R] N) :
    M [⋀^ι]->L[R] N' :=
  { (g : N ->ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]
/--
theorem `_root_.ContinuousLinearMap.compContinuousAlternatingMap_coe` / 定理 `_root_.ContinuousLinearMap.compContinuousAlternatingMap_coe`

English:
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe
  statement: (g : N ->L[R] N')
  proof: rfl

中文:
定理 _root_.连续线性映射.compContinuousAlternatingMap_coe
  结论: (g : N ->L[R] N')
  证明: rfl
-/
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe (g : N ->L[R] N')
    (f : M [⋀^ι]->L[R] N) : ⇑(g.compContinuousAlternatingMap f) = g ∘ f :=
  rfl

/-- A continuous linear equivalence of domains
defines an equivalence between continuous alternating maps.

This is available as a continuous linear isomorphism at
`ContinuousLinearEquiv.continuousAlternatingMapCongrLeft`.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence. -/
@[simps -fullyApplied apply]
/--
Definition of `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrLeftEquiv` / `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrLeftEquiv` 的定义

English:
definition _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrLeftEquiv
  signature: (e : M ≃L[R] M')
  body: f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [Function.comp_def]
  right_inv f := by ext; simp [Function.comp_def]

中文:
定义 _root_.连续线性等价.continuousAlternatingMapCongrLeftEquiv
  签名: (e : M ≃L[R] M')
  定义体: f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [Function.comp_def]
  right_inv f := by ext; simp [Function.comp_def]

Depends on / 依赖: compContinuousLinearMap, e.symm, f.compContinuousLinearMap
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrLeftEquiv (e : M ≃L[R] M') :
    M [⋀^ι]->L[R] N ≃ M' [⋀^ι]->L[R] N where
  toFun f := f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [Function.comp_def]
  right_inv f := by ext; simp [Function.comp_def]

/-- A continuous linear equivalence of codomains
defines an equivalence between continuous alternating maps. -/
@[simps -fullyApplied apply]
/--
Definition of `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRightEquiv` / `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRightEquiv` 的定义

English:
definition _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRightEquiv
  signature: (e : N ≃L[R] N')
  body: (e : N ->L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' ->L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]

@[simp]

中文:
定义 _root_.连续线性等价.continuousAlternatingMapCongrRightEquiv
  签名: (e : N ≃L[R] N')
  定义体: (e : N ->L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' ->L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]

@[simp]

Depends on / 依赖: compContinuousAlternatingMap
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRightEquiv (e : N ≃L[R] N') :
    M [⋀^ι]->L[R] N ≃ M [⋀^ι]->L[R] N' where
  toFun := (e : N ->L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' ->L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe` / 定理 `_root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe`

English:
theorem _root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe
  proof: rfl

中文:
定理 _root_.连续线性等价.compContinuousAlternatingMap_coe
  证明: rfl
-/
theorem _root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe
    (e : N ≃L[R] N') (f : M [⋀^ι]->L[R] N) :
    ⇑(e.continuousAlternatingMapCongrRightEquiv f) = e ∘ f :=
  rfl

/--
Definition of `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrEquiv` / `_root_.ContinuousLinearEquiv.continuousAlternatingMapCongrEquiv` 的定义

English:
definition _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrEquiv
  body: e.continuousAlternatingMapCongrLeftEquiv.trans e'.continuousAlternatingMapCongrRightEquiv

中文:
定义 _root_.连续线性等价.continuousAlternatingMapCongrEquiv
  定义体: e.continuousAlternatingMapCongrLeftEquiv.trans e'.continuousAlternatingMapCongrRightEquiv

Depends on / 依赖: continuousAlternatingMapCongrLeftEquiv, continuousAlternatingMapCongrRightEquiv, e.continuousAlternatingMapCongrLeftEquiv.trans
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrEquiv
    (e : M ≃L[R] M') (e' : N ≃L[R] N') : M [⋀^ι]->L[R] N ≃ M' [⋀^ι]->L[R] N' :=
  e.continuousAlternatingMapCongrLeftEquiv.trans e'.continuousAlternatingMapCongrRightEquiv

/-- `ContinuousAlternatingMap.pi` as an `Equiv`. -/
@[simps]
/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, TopologicalSpace (N i)]
  body: pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] N i).compContinuousAlternatingMap f

中文:
定义 piEquiv
  签名: {ι' : 类型} {N : ι' -> 类型} [对任意 i, 加法交换幺半群 (N i)] [对任意 i, 拓扑空间 (N i)]
  定义体: pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] N i).compContinuousAlternatingMap f
-/
def piEquiv {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, TopologicalSpace (N i)]
    [forall i, Module R (N i)] : (forall i, M [⋀^ι]->L[R] N i) ≃ M [⋀^ι]->L[R] forall i, N i where
  toFun := pi
  invFun f i := (ContinuousLinearMap.proj i : _ ->L[R] N i).compContinuousAlternatingMap f

/--
theorem `cons_add` / 定理 `cons_add`

English:
theorem cons_add
  given: (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (x y : M)
  proof: f.toMultilinearMap.cons_add m x y

中文:
定理 cons_add
  条件: (f : 余ntinuousAlternating映射 R M N (有限集 (n + 1))) (m : 有限集 n -> M) (x y : M)
  证明: f.toMultilinearMap.cons_add m x y

Depends on / 依赖: cons_add, f.toMultilinearMap.cons_add, toMultilinearMap
-/
theorem cons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (x y : M) :
    f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m) :=
  f.toMultilinearMap.cons_add m x y

/--
theorem `vecCons_add` / 定理 `vecCons_add`

English:
theorem vecCons_add
  given: (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (x y : M)
  proof: f.toMultilinearMap.cons_add m x y

中文:
定理 vecCons_add
  条件: (f : 余ntinuousAlternating映射 R M N (有限集 (n + 1))) (m : 有限集 n -> M) (x y : M)
  证明: f.toMultilinearMap.cons_add m x y

Depends on / 依赖: cons_add, f.toMultilinearMap.cons_add, toMultilinearMap
-/
theorem vecCons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (x y : M) :
    f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m) :=
  f.toMultilinearMap.cons_add m x y

/--
theorem `cons_smul` / 定理 `cons_smul`

English:
theorem cons_smul
  statement: (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (c : R)
  proof: f.toMultilinearMap.cons_smul m c x

中文:
定理 cons_smul
  结论: (f : 余ntinuousAlternating映射 R M N (有限集 (n + 1))) (m : 有限集 n -> M) (c : R)
  证明: f.toMultilinearMap.cons_smul m c x

Depends on / 依赖: cons_smul, f.toMultilinearMap.cons_smul, toMultilinearMap
-/
theorem cons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (c : R)
    (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m) :=
  f.toMultilinearMap.cons_smul m c x

/--
theorem `vecCons_smul` / 定理 `vecCons_smul`

English:
theorem vecCons_smul
  statement: (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (c : R)
  proof: f.toMultilinearMap.cons_smul m c x

中文:
定理 vecCons_smul
  结论: (f : 余ntinuousAlternating映射 R M N (有限集 (n + 1))) (m : 有限集 n -> M) (c : R)
  证明: f.toMultilinearMap.cons_smul m c x

Depends on / 依赖: cons_smul, f.toMultilinearMap.cons_smul, toMultilinearMap
-/
theorem vecCons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> M) (c : R)
    (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m) :=
  f.toMultilinearMap.cons_smul m c x

/--
theorem `map_piecewise_add` / 定理 `map_piecewise_add`

English:
theorem map_piecewise_add
  given: [DecidableEq ι] (m m' : ι -> M) (t : Finset ι)
  proof: f.toMultilinearMap.map_piecewise_add _ _ _

中文:
定理 map_piecewise_add
  条件: [DecidableEq ι] (m m' : ι -> M) (t : 有限集 ι)
  证明: f.toMultilinearMap.map_piecewise_add _ _ _

Depends on / 依赖: f.toMultilinearMap.map_piecewise_add, map_piecewise_add, toMultilinearMap
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : ι -> M) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/--
theorem `map_add_univ` / 定理 `map_add_univ`

English:
theorem map_add_univ
  given: [DecidableEq ι] [Fintype ι] (m m' : ι -> M)
  proof: f.toMultilinearMap.map_add_univ _ _

中文:
定理 map_add_univ
  条件: [DecidableEq ι] [有限类型 ι] (m m' : ι -> M)
  证明: f.toMultilinearMap.map_add_univ _ _

Depends on / 依赖: f.toMultilinearMap.map_add_univ, map_add_univ, toMultilinearMap
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι -> M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι -> Type*} [Fintype ι] [DecidableEq ι] (g' : forall i, α i -> M) (A : forall i, Finset (α i))

/--
theorem `map_sum_finset` / 定理 `map_sum_finset`

English:
theorem map_sum_finset
  proof: f.toMultilinearMap.map_sum_finset _ _

中文:
定理 map_sum_finset
  证明: f.toMultilinearMap.map_sum_finset _ _

Depends on / 依赖: f.toMultilinearMap.map_sum_finset, map_sum_finset, toMultilinearMap
-/
theorem map_sum_finset :
    (f fun i => ∑ j in A i, g' i j) = ∑ r in piFinset A, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: [forall i, Fintype (α i)]
  proof: f.toMultilinearMap.map_sum _

中文:
定理 map_sum
  条件: [对任意 i, 有限类型 (α i)]
  证明: f.toMultilinearMap.map_sum _

Depends on / 依赖: f.toMultilinearMap.map_sum, map_sum, toMultilinearMap
-/
theorem map_sum [forall i, Fintype (α i)] :
    (f fun i => ∑ j, g' i j) = ∑ r : forall i, α i, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [Module A M] [Module A N] [IsScalarTower R A M]
  [IsScalarTower R A N]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : M [⋀^ι]->L[A] N)
  body: { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]

中文:
定义 restrictScalars
  签名: (f : M [⋀^ι]->L[A] N)
  定义体: { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]

Depends on / 依赖: restrictScalars, toContinuousMultilinearMap
-/
def restrictScalars (f : M [⋀^ι]->L[A] N) : M [⋀^ι]->L[R] N :=
  { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : M [⋀^ι]->L[A] N)
  statement: ⇑(f.restrictScalars R) = f
  proof: rfl

中文:
定理 coe_restrictScalars
  条件: (f : M [⋀^ι]->L[A] N)
  结论: ⇑(f.restrictScalars R) = f
  证明: rfl
-/
theorem coe_restrictScalars (f : M [⋀^ι]->L[A] N) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  (f g : M [⋀^ι]->L[R] N)

@[simp]
/--
theorem `map_update_sub` / 定理 `map_update_sub`

English:
theorem map_update_sub
  given: [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M)
  proof: f.toMultilinearMap.map_update_sub _ _ _ _

@[simp]

中文:
定理 map_update_sub
  条件: [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M)
  证明: f.toMultilinearMap.map_update_sub _ _ _ _

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_update_sub, map_update_sub, toMultilinearMap
-/
theorem map_update_sub [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _

@[simp]
/--
theorem `map_vecCons_sub` / 定理 `map_vecCons_sub`

English:
theorem map_vecCons_sub
  given: {n} (f : M [⋀^Fin (n + 1)]->L[R] N) (x y : M) (v : Fin n -> M)
  proof: by
  rw [vecCons]; rw [← Fin.update_cons_zero 0]; rw [map_update_sub]
  simp [vecCons]

中文:
定理 map_vecCons_sub
  条件: {n} (f : M [⋀^有限集 (n + 1)]->L[R] N) (x y : M) (v : 有限集 n -> M)
  证明: by
  rw [vecCons]; rw [← Fin.update_cons_zero 0]; rw [map_update_sub]
  simp [vecCons]

Depends on / 依赖: Fin.update_cons_zero, map_update_sub, update_cons_zero, vecCons
-/
theorem map_vecCons_sub {n} (f : M [⋀^Fin (n + 1)]->L[R] N) (x y : M) (v : Fin n -> M) :
    f (Matrix.vecCons (x - y) v) = f (Matrix.vecCons x v) - f (Matrix.vecCons y v) := by
  rw [vecCons]; rw [← Fin.update_cons_zero 0]; rw [map_update_sub]
  simp [vecCons]

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M [⋀^ι]->L[R] N)
  body: ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]

中文:
实例 :
  签名: 取负 (M [⋀^ι]->L[R] N)
  定义体: ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]

Depends on / 依赖: f.toAlternatingMap, toAlternatingMap, toContinuousMultilinearMap
-/
instance : Neg (M [⋀^ι]->L[R] N) :=
  ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ⇑(-f) = -f
  proof: rfl

中文:
定理 coe_neg
  结论: ⇑(-f) = -f
  证明: rfl
-/
theorem coe_neg : ⇑(-f) = -f :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (m : ι -> M)
  statement: (-f) m = -f m
  proof: rfl

中文:
定理 neg_apply
  条件: (m : ι -> M)
  结论: (-f) m = -f m
  证明: rfl
-/
theorem neg_apply (m : ι -> M) : (-f) m = -f m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (M [⋀^ι]->L[R] N)
  body: ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

中文:
实例 :
  签名: 减法 (M [⋀^ι]->L[R] N)
  定义体: ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

Depends on / 依赖: f.toAlternatingMap, g.toAlternatingMap, toAlternatingMap, toContinuousMultilinearMap
-/
instance : Sub (M [⋀^ι]->L[R] N) :=
  ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ⇑(f - g) = ⇑f - ⇑g
  proof: rfl

中文:
定理 coe_sub
  结论: ⇑(f - g) = ⇑f - ⇑g
  证明: rfl
-/
@[simp] theorem coe_sub : ⇑(f - g) = ⇑f - ⇑g := rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (m : ι -> M)
  statement: (f - g) m = f m - g m
  proof: rfl

中文:
定理 sub_apply
  条件: (m : ι -> M)
  结论: (f - g) m = f m - g m
  证明: rfl
-/
theorem sub_apply (m : ι -> M) : (f - g) m = f m - g m := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (M [⋀^ι]->L[R] N)
  body: fast_instance%
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法交换群 (M [⋀^ι]->L[R] N)
  定义体: fast_instance%
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance : AddCommGroup (M [⋀^ι]->L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end IsTopologicalAddGroup

end Ring

section CommSemiring

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  (f : M [⋀^ι]->L[R] N)

/--
theorem `map_piecewise_smul` / 定理 `map_piecewise_smul`

English:
theorem map_piecewise_smul
  given: [DecidableEq ι] (c : ι -> R) (m : ι -> M) (s : Finset ι)
  proof: f.toMultilinearMap.map_piecewise_smul _ _ _

中文:
定理 map_piecewise_smul
  条件: [DecidableEq ι] (c : ι -> R) (m : ι -> M) (s : 有限集 ι)
  证明: f.toMultilinearMap.map_piecewise_smul _ _ _

Depends on / 依赖: f.toMultilinearMap.map_piecewise_smul, map_piecewise_smul, toMultilinearMap
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : ι -> M) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/--
theorem `map_smul_univ` / 定理 `map_smul_univ`

English:
theorem map_smul_univ
  given: [Fintype ι] (c : ι -> R) (m : ι -> M)
  proof: f.toMultilinearMap.map_smul_univ _ _

中文:
定理 map_smul_univ
  条件: [有限类型 ι] (c : ι -> R) (m : ι -> M)
  证明: f.toMultilinearMap.map_smul_univ _ _

Depends on / 依赖: f.toMultilinearMap.map_smul_univ, map_smul_univ, toMultilinearMap
-/
theorem map_smul_univ [Fintype ι] (c : ι -> R) (m : ι -> M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

/-- If two continuous `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `ContinuousLinearMap.ext_ring`. -/
@[ext]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: [Finite ι] [TopologicalSpace R] ⦃f g
  statement: R [⋀^ι]->L[R] M⦄
  proof: toAlternatingMap_injective AlternatingMap.ext_ring h

中文:
定理 ext_ring
  条件: [有限 ι] [拓扑空间 R] ⦃f g
  结论: R [⋀^ι]->L[R] M⦄
  证明: toAlternatingMap_injective AlternatingMap.ext_ring h

Depends on / 依赖: AlternatingMap, AlternatingMap.ext_ring, ext_ring, toAlternatingMap_injective
-/
theorem ext_ring [Finite ι] [TopologicalSpace R] ⦃f g : R [⋀^ι]->L[R] M⦄
    (h : f (fun _ => 1) = g (fun _ => 1)) : f = g :=
toAlternatingMap_injective AlternatingMap.ext_ring h

/--
Instance `uniqueOfCommRing` / 实例 `uniqueOfCommRing`

English:
instance uniqueOfCommRing
  signature: [Finite ι] [Nontrivial ι] [TopologicalSpace R]
  body: toAlternatingMap_injective Subsingleton.elim _ _

中文:
实例 uniqueOfCommRing
  签名: [有限 ι] [非平凡 ι] [拓扑空间 R]
  定义体: toAlternatingMap_injective Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, toAlternatingMap_injective
-/
instance uniqueOfCommRing [Finite ι] [Nontrivial ι] [TopologicalSpace R] :
    Unique (R [⋀^ι]->L[R] N) where
uniq _ := toAlternatingMap_injective Subsingleton.elim _ _

end CommSemiring

section DistribMulAction

variable {R A M N ι : Type*} [Monoid R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [Module A M] [Module A N] [DistribMulAction R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousAdd
  signature: N] : DistribMulAction R (M [⋀^ι]->L[A] N)
  body: fast_instance%
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

中文:
实例 [连续加法
  签名: N] : 分配乘法作用 R (M [⋀^ι]->L[A] N)
  定义体: fast_instance%
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [ContinuousAdd N] : DistribMulAction R (M [⋀^ι]->L[A] N) := fast_instance%
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

end DistribMulAction

section Module

variable {R A M N ι : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (M [⋀^ι]->L[A] N)
  body: fast_instance%
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

中文:
实例 :
  签名: 模 R (M [⋀^ι]->L[A] N)
  定义体: fast_instance%
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

Depends on / 依赖: fast_instance
-/
instance : Module R (M [⋀^ι]->L[A] N) := fast_instance%
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

/-- Linear map version of the map `toMultilinearMap` associating to a continuous alternating map
the corresponding multilinear map. -/
@[simps]
/--
Definition of `toContinuousMultilinearMapLinear` / `toContinuousMultilinearMapLinear` 的定义

English:
definition toContinuousMultilinearMapLinear
  signature: :
  body: toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 toContinuousMultilinearMapLinear
  签名: :
  定义体: toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: toContinuousMultilinearMap
-/
def toContinuousMultilinearMapLinear :
    M [⋀^ι]->L[A] N ->ₗ[R] ContinuousMultilinearMap A (fun _ : ι => M) N where
  toFun := toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear map version of the map `toAlternatingMap`
associating to a continuous alternating map the corresponding alternating map. -/
@[simps -fullyApplied apply]
/--
Definition of `toAlternatingMapLinear` / `toAlternatingMapLinear` 的定义

English:
definition toAlternatingMapLinear
  signature: : (M [⋀^ι]->L[A] N) ->ₗ[R] (M [⋀^ι]->ₗ[A] N) where
  body: toAlternatingMap
  map_add' := by simp
  map_smul' := by simp

中文:
定义 toAlternatingMapLinear
  签名: : (M [⋀^ι]->L[A] N) ->ₗ[R] (M [⋀^ι]->ₗ[A] N) where
  定义体: toAlternatingMap
  map_add' := by simp
  map_smul' := by simp

Depends on / 依赖: toAlternatingMap
-/
def toAlternatingMapLinear : (M [⋀^ι]->L[A] N) ->ₗ[R] (M [⋀^ι]->ₗ[A] N) where
  toFun := toAlternatingMap
  map_add' := by simp
  map_smul' := by simp

/-- `ContinuousAlternatingMap.pi` as a `LinearEquiv`. -/
@[simps +simpRhs]
/--
Definition of `piLinearEquiv` / `piLinearEquiv` 的定义

English:
definition piLinearEquiv
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
  body: { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 piLinearEquiv
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)]
  定义体: { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: map_add, map_smul, piEquiv
-/
def piLinearEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)]
    [forall i, TopologicalSpace (M' i)] [forall i, ContinuousAdd (M' i)] [forall i, Module R (M' i)]
    [forall i, Module A (M' i)] [forall i, SMulCommClass A R (M' i)] [forall i, ContinuousConstSMul R (M' i)] :
    (forall i, M [⋀^ι]->L[A] M' i) ≃ₗ[R] M [⋀^ι]->L[A] forall i, M' i :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Module

section SMulRight

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N] [ContinuousSMul R N]
  (f : M [⋀^ι]->L[R] R) (z : N)

/-- Given a continuous `R`-alternating map `f` taking values in `R`, `f.smulRight z` is the
continuous alternating map sending `m` to `f m • z`. -/
@[simps! toContinuousMultilinearMap apply]
/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: : M [⋀^ι]->L[R] N
  body: { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

中文:
定义 smulRight
  签名: : M [⋀^ι]->L[R] N
  定义体: { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

Depends on / 依赖: f.toAlternatingMap.smulRight, smulRight, toAlternatingMap, toContinuousMultilinearMap
-/
def smulRight : M [⋀^ι]->L[R] N :=
  { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

end SMulRight

section Semiring

variable {R M M' N N' ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul R N] [AddCommMonoid N']
  [Module R N'] [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul R N']

/-- `ContinuousAlternatingMap.compContinuousLinearMap` as a bundled `LinearMap`. -/
@[simps]
/--
Definition of `compContinuousLinearMapₗ` / `compContinuousLinearMapₗ` 的定义

English:
definition compContinuousLinearMapₗ
  signature: (f : M ->L[R] M')
  body: g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

中文:
定义 compContinuousLinearMapₗ
  签名: (f : M ->L[R] M')
  定义体: g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

Depends on / 依赖: compContinuousLinearMap, g.compContinuousLinearMap
-/
def compContinuousLinearMapₗ (f : M ->L[R] M') : (M' [⋀^ι]->L[R] N) ->ₗ[R] (M [⋀^ι]->L[R] N) where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

variable (R M N N')

/--
Definition of `_root_.ContinuousLinearMap.compContinuousAlternatingMapₗ` / `_root_.ContinuousLinearMap.compContinuousAlternatingMapₗ` 的定义

English:
definition _root_.ContinuousLinearMap.compContinuousAlternatingMapₗ
  signature: :
  body: LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp

中文:
定义 _root_.连续线性映射.compContinuousAlternatingMapₗ
  签名: :
  定义体: LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compContinuousAlternatingMap, LinearMap, LinearMap.mk, compContinuousAlternatingMap, f.map_add, map_add
-/
def _root_.ContinuousLinearMap.compContinuousAlternatingMapₗ :
    (N ->L[R] N') ->ₗ[R] (M [⋀^ι]->L[R] N) ->ₗ[R] (M [⋀^ι]->L[R] N') :=
  LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp

end Semiring

end ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [Fintype ι]
  [DecidableEq ι] (f : ContinuousMultilinearMap R (fun _ : ι => M) N)

/-- Alternatization of a continuous multilinear map. -/
@[simps -isSimp apply_toContinuousMultilinearMap]
/--
Definition of `alternatization` / `alternatization` 的定义

English:
definition alternatization
  signature: : ContinuousMultilinearMap R (fun _ : ι => M) N ->+ M [⋀^ι]->L[R] N where
  body: { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
  map_add'

中文:
定义 alternatization
  签名: : 连续多重线性映射 R (fun _ : ι => M) N ->+ M [⋀^ι]->L[R] N where
  定义体: { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
  map_add'

Depends on / 依赖: Equiv.Perm, Equiv.Perm.sign, Finset, Finset.sum_add_distrib, MultilinearMap, MultilinearMap.alternatization_apply, alternatization, alternatization.map_eq_zero_of_eq, alternatization_apply, domDomCongr, f.domDomCongr, map_add, map_eq_zero_of_eq, map_zero, sum_add_distrib, toContinuousMultilinearMap
-/
def alternatization : ContinuousMultilinearMap R (fun _ : ι => M) N ->+ M [⋀^ι]->L[R] N where
  toFun f :=
    { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]

/--
theorem `alternatization_apply_apply` / 定理 `alternatization_apply_apply`

English:
theorem alternatization_apply_apply
  given: (v : ι -> M)
  proof: by
  simp [alternatization, Function.comp_def]

@[simp]

中文:
定理 alternatization_apply_apply
  条件: (v : ι -> M)
  证明: by
  simp [alternatization, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, alternatization, comp_def
-/
theorem alternatization_apply_apply (v : ι -> M) :
    alternatization f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) := by
  simp [alternatization, Function.comp_def]

@[simp]
/--
theorem `alternatization_apply_toAlternatingMap` / 定理 `alternatization_apply_toAlternatingMap`

English:
theorem alternatization_apply_toAlternatingMap
  proof: by
  ext v
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, Function.comp_def]

中文:
定理 alternatization_apply_toAlternatingMap
  证明: by
  ext v
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, MultilinearMap, MultilinearMap.alternatization_apply, alternatization_apply, alternatization_apply_apply, comp_def
-/
theorem alternatization_apply_toAlternatingMap :
    (alternatization f).toAlternatingMap = MultilinearMap.alternatization f.1 := by
  ext v
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, Function.comp_def]

end ContinuousMultilinearMap
