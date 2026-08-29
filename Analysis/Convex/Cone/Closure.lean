/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Closure of cones

We define the closures of convex and pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

@[expose] public section

namespace ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (K : ConvexCone 𝕜 E)
  body: closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ => K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

@[simp, norm_cast]

中文:
定义 closure
  签名: (K : 余nvexCone 𝕜 E)
  定义体: closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ => K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

@[simp, norm_cast]
-/
protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ => K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

@[simp, norm_cast]
/--
theorem `coe_closure` / 定理 `coe_closure`

English:
theorem coe_closure
  given: (K : ConvexCone 𝕜 E)
  statement: (K.closure : Set E) = closure K
  proof: rfl

@[simp]

中文:
定理 coe_closure
  条件: (K : 余nvexCone 𝕜 E)
  结论: (K.closure : 集合 E) = closure K
  证明: rfl

@[simp]
-/
theorem coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {K : ConvexCone 𝕜 E} {a : E}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_closure
  条件: {K : 余nvexCone 𝕜 E} {a : E}
  证明: Iff.rfl

@[simp]
-/
protected theorem mem_closure {K : ConvexCone 𝕜 E} {a : E} :
    a in K.closure ↔ a in closure (K : Set E) :=
  Iff.rfl

@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: {K L : ConvexCone 𝕜 E}
  statement: K.closure = L ↔ closure (K : Set E) = L
  proof: SetLike.ext'_iff

中文:
定理 closure_eq
  条件: {K L : 余nvexCone 𝕜 E}
  结论: K.closure = L ↔ closure (K : 集合 E) = L
  证明: SetLike.ext'_iff

Depends on / 依赖: SetLike, SetLike.ext, _iff
-/
theorem closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end ConvexCone



namespace PointedCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/--
lemma `toConvexCone_closure_pointed` / 引理 `toConvexCone_closure_pointed`

English:
lemma toConvexCone_closure_pointed
  given: (K : PointedCone 𝕜 E)
  statement: (K : ConvexCone 𝕜 E).closure.Pointed
  proof: subset_closure PointedCone.pointed_toConvexCone _

中文:
引理 toConvexCone_closure_pointed
  条件: (K : PointedCone 𝕜 E)
  结论: (K : 余nvexCone 𝕜 E).closure.Pointed
  证明: subset_closure PointedCone.pointed_toConvexCone _

Depends on / 依赖: PointedCone, PointedCone.pointed_toConvexCone, pointed_toConvexCone, subset_closure
-/
lemma toConvexCone_closure_pointed (K : PointedCone 𝕜 E) : (K : ConvexCone 𝕜 E).closure.Pointed :=
subset_closure PointedCone.pointed_toConvexCone _

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (K : PointedCone 𝕜 E)
  body: closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ => K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb => K.add_mem ha hb)

@[simp, norm_cast]

中文:
定义 closure
  签名: (K : PointedCone 𝕜 E)
  定义体: closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ => K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb => K.add_mem ha hb)

@[simp, norm_cast]
-/
protected def closure (K : PointedCone 𝕜 E) : PointedCone 𝕜 E where
  carrier := closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ => K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb => K.add_mem ha hb)

@[simp, norm_cast]
/--
theorem `coe_closure` / 定理 `coe_closure`

English:
theorem coe_closure
  given: (K : PointedCone 𝕜 E)
  statement: (K.closure : Set E) = closure K
  proof: rfl

@[simp]

中文:
定理 coe_closure
  条件: (K : PointedCone 𝕜 E)
  结论: (K.closure : 集合 E) = closure K
  证明: rfl

@[simp]
-/
theorem coe_closure (K : PointedCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {K : PointedCone 𝕜 E} {a : E}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_closure
  条件: {K : PointedCone 𝕜 E} {a : E}
  证明: Iff.rfl

@[simp]
-/
protected theorem mem_closure {K : PointedCone 𝕜 E} {a : E} :
    a in K.closure ↔ a in closure (K : Set E) :=
  Iff.rfl

@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: {K L : PointedCone 𝕜 E}
  statement: K.closure = L ↔ closure (K : Set E) = L
  proof: SetLike.ext'_iff

中文:
定理 closure_eq
  条件: {K L : PointedCone 𝕜 E}
  结论: K.closure = L ↔ closure (K : 集合 E) = L
  证明: SetLike.ext'_iff

Depends on / 依赖: SetLike, SetLike.ext, _iff
-/
theorem closure_eq {K L : PointedCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end PointedCone
