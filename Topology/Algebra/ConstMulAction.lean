/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.ULift
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Support

/-!
# Monoid actions continuous in the second variable

In this file we define class `ContinuousConstSMul`. We say `ContinuousConstSMul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`ContinuousSMul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `ContinuousConstSMul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `ProperlyDiscontinuousSMul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `Homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.
* `Homeomorph.smulOfNeZero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `Homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.

## Main results

* `isOpenMap_quotient_mk'_mul` : The quotient map by a group action is open.
* `t2Space_of_properlyDiscontinuousSMul_of_t2Space` : The quotient by a discontinuous group
  action of a locally compact T₂ space is T₂.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

@[expose] public section

assert_not_exists IsOrderedRing

open Topology Pointwise Filter Set TopologicalSpace

/--
Definition of `ContinuousConstSMul` / `ContinuousConstSMul` 的定义

English:
class ContinuousConstSMul
  parameters: (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T]
  axioms and operations (1):
    - continuous_const_smul : forall γ : Γ, Continuous fun x : T => γ • x

中文:
类 连续常数标量乘法
  参数: (Γ : 类型) (T : 类型) [拓扑空间 T] [标量乘法 Γ T]
  公理与运算 (1 个):
    - continuous_const_smul : 对任意 γ : Γ, 连续 fun x : T => γ • x
-/
class ContinuousConstSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_smul : forall γ : Γ, Continuous fun x : T => γ • x

/--
Definition of `ContinuousConstVAdd` / `ContinuousConstVAdd` 的定义

English:
class ContinuousConstVAdd
  parameters: (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T]
  axioms and operations (1):
    - continuous_const_vadd : forall γ : Γ, Continuous fun x : T => γ +ᵥ x

中文:
类 连续常数向量加法
  参数: (Γ : 类型) (T : 类型) [拓扑空间 T] [向量加法 Γ T]
  公理与运算 (1 个):
    - continuous_const_vadd : 对任意 γ : Γ, 连续 fun x : T => γ +ᵥ x
-/
class ContinuousConstVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] : Prop where
  /-- The additive action `(+ᵥ) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_vadd : forall γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)
export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type*}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousConstSMul (ULift M) α
  body: ⟨fun γ => continuous_const_smul (ULift.down γ)⟩

@[to_additive]

中文:
实例 :
  签名: 连续常数标量乘法 (类型层提升 M) α
  定义体: ⟨fun γ => continuous_const_smul (ULift.down γ)⟩

@[to_additive]

Depends on / 依赖: ULift.down, continuous_const_smul
-/
instance : ContinuousConstSMul (ULift M) α := ⟨fun γ => continuous_const_smul (ULift.down γ)⟩

@[to_additive]
/--
theorem `Filter.Tendsto.const_smul` / 定理 `Filter.Tendsto.const_smul`

English:
theorem Filter.Tendsto.const_smul
  statement: {f : β -> α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
  proof: ((continuous_const_smul _).tendsto _).comp hf

中文:
定理 滤子.收敛.const_smul
  结论: {f : β -> α} {l : 滤子 β} {a : α} (hf : 收敛 f l (𝓝 a))
  证明: ((continuous_const_smul _).tendsto _).comp hf

Depends on / 依赖: continuous_const_smul, tendsto
-/
theorem Filter.Tendsto.const_smul {f : β -> α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
    (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).tendsto _).comp hf

variable [TopologicalSpace β] {g : β -> α} {b : β} {s : Set β}

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (c • g) s b :=
  hg.const_smul c

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) :
    ContinuousAt (c • g) b :=
  hg.const_smul c

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.const_smul` / 定理 `ContinuousOn.const_smul`

English:
theorem ContinuousOn.const_smul
  given: (hg : ContinuousOn g s) (c : M)
  proof: fun x hx => (hg x hx).const_smul c

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]

中文:
定理 ContinuousOn.const_smul
  条件: (hg : ContinuousOn g s) (c : M)
  证明: fun x hx => (hg x hx).const_smul c

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]

Depends on / 依赖: const_smul
-/
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) :
    ContinuousOn (c • g) s := fun x hx => (hg x hx).const_smul c

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/--
theorem `Continuous.const_smul` / 定理 `Continuous.const_smul`

English:
theorem Continuous.const_smul
  given: (hg : Continuous g) (c : M)
  statement: Continuous (c • g)
  proof: (continuous_const_smul _).comp hg

中文:
定理 连续.const_smul
  条件: (hg : 连续 g) (c : M)
  结论: 连续 (c • g)
  证明: (continuous_const_smul _).comp hg

Depends on / 依赖: continuous_const_smul
-/
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous (c • g) :=
  (continuous_const_smul _).comp hg

/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
/--
Instance `ContinuousConstSMul.op` / 实例 `ContinuousConstSMul.op`

English:
instance ContinuousConstSMul.op
  signature: [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
  body: ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]

中文:
实例 连续常数标量乘法.op
  签名: [标量乘法 Mᵐᵒᵖ α] [中心标量 M α]
  定义体: ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.rec, continuous_const_smul, op_smul_eq_smul
-/
instance ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    ContinuousConstSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]
/--
Instance `MulOpposite.continuousConstSMul` / 实例 `MulOpposite.continuousConstSMul`

English:
instance MulOpposite.continuousConstSMul
  signature: : ContinuousConstSMul M αᵐᵒᵖ
  body: ⟨fun c => MulOpposite.continuous_op.comp MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]

中文:
实例 MulOpposite.continuousConstSMul
  签名: : 连续常数标量乘法 M αᵐᵒᵖ
  定义体: ⟨fun c => MulOpposite.continuous_op.comp MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.continuous_op.comp, MulOpposite.continuous_unop.const_smul, const_smul, continuous_op, continuous_unop
-/
instance MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ :=
⟨fun c => MulOpposite.continuous_op.comp MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousConstSMul M αᵒᵈ
  body: ‹ContinuousConstSMul M α›

@[to_additive]

中文:
实例 :
  签名: 连续常数标量乘法 M αᵒᵈ
  定义体: ‹ContinuousConstSMul M α›

@[to_additive]

Depends on / 依赖: ContinuousConstSMul
-/
instance : ContinuousConstSMul M αᵒᵈ := ‹ContinuousConstSMul M α›

@[to_additive]
/--
Instance `OrderDual.continuousConstSMul'` / 实例 `OrderDual.continuousConstSMul'`

English:
instance OrderDual.continuousConstSMul'
  signature: : ContinuousConstSMul Mᵒᵈ α
  body: ‹ContinuousConstSMul M α›

@[to_additive]

中文:
实例 OrderDual.continuousConstSMul'
  签名: : 连续常数标量乘法 Mᵒᵈ α
  定义体: ‹ContinuousConstSMul M α›

@[to_additive]

Depends on / 依赖: ContinuousConstSMul
-/
instance OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α :=
  ‹ContinuousConstSMul M α›

@[to_additive]
/--
Instance `Prod.continuousConstSMul` / 实例 `Prod.continuousConstSMul`

English:
instance Prod.continuousConstSMul
  signature: [SMul M β] [ContinuousConstSMul M β]
  body: ⟨fun _ => (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)⟩

@[to_additive]

中文:
实例 积类型.continuousConstSMul
  签名: [标量乘法 M β] [连续常数标量乘法 M β]
  定义体: ⟨fun _ => (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)⟩

@[to_additive]

Depends on / 依赖: const_smul, continuous_fst, continuous_fst.const_smul, continuous_snd, continuous_snd.const_smul, prodMk
-/
instance Prod.continuousConstSMul [SMul M β] [ContinuousConstSMul M β] :
    ContinuousConstSMul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type*} {γ : ι -> Type*} [forall i, TopologicalSpace (γ i)] [forall i, SMul M (γ i)]
    [forall i, ContinuousConstSMul M (γ i)] : ContinuousConstSMul M (forall i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

@[to_additive]
/--
theorem `IsCompact.smul` / 定理 `IsCompact.smul`

English:
theorem IsCompact.smul
  statement: {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
  proof: hs.image (continuous_id.const_smul a)

@[to_additive]

中文:
定理 是紧集.smul
  结论: {α β} [标量乘法 α β] [拓扑空间 β] [连续常数标量乘法 α β] (a : α)
  证明: hs.image (continuous_id.const_smul a)

@[to_additive]

Depends on / 依赖: const_smul, continuous_id, continuous_id.const_smul, hs.image
-/
theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
    {s : Set β} (hs : IsCompact s) : IsCompact (a • s) :=
  hs.image (continuous_id.const_smul a)

@[to_additive]
/--
theorem `Specializes.const_smul` / 定理 `Specializes.const_smul`

English:
theorem Specializes.const_smul
  given: {x y : α} (h : x ⤳ y) (c : M)
  statement: (c • x) ⤳ (c • y)
  proof: h.map (continuous_const_smul c)

@[to_additive]

中文:
定理 Specializes.const_smul
  条件: {x y : α} (h : x ⤳ y) (c : M)
  结论: (c • x) ⤳ (c • y)
  证明: h.map (continuous_const_smul c)

@[to_additive]

Depends on / 依赖: continuous_const_smul, h.map
-/
theorem Specializes.const_smul {x y : α} (h : x ⤳ y) (c : M) : (c • x) ⤳ (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
/--
theorem `Inseparable.const_smul` / 定理 `Inseparable.const_smul`

English:
theorem Inseparable.const_smul
  given: {x y : α} (h : Inseparable x y) (c : M)
  proof: h.map (continuous_const_smul c)

@[to_additive]

中文:
定理 不可分.const_smul
  条件: {x y : α} (h : 不可分 x y) (c : M)
  证明: h.map (continuous_const_smul c)

@[to_additive]

Depends on / 依赖: continuous_const_smul, h.map
-/
theorem Inseparable.const_smul {x y : α} (h : Inseparable x y) (c : M) :
    Inseparable (c • x) (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
/--
theorem `Topology.IsInducing.continuousConstSMul` / 定理 `Topology.IsInducing.continuousConstSMul`

English:
theorem Topology.IsInducing.continuousConstSMul
  statement: {N β : Type*} [SMul N β] [TopologicalSpace β]
  proof: by
    simpa only [Function.comp_def, hf, hg.continuous_iff] using hg.continuous.fun_const_smul (f c)

@[to_additive]

中文:
定理 拓扑.是Inducing.continuousConstSMul
  结论: {N β : 类型} [标量乘法 N β] [拓扑空间 β]
  证明: by
    simpa only [Function.comp_def, hf, hg.continuous_iff] using hg.continuous.fun_const_smul (f c)

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous, continuous_iff, fun_const_smul, hg.continuous.fun_const_smul, hg.continuous_iff
-/
theorem Topology.IsInducing.continuousConstSMul {N β : Type*} [SMul N β] [TopologicalSpace β]
    {g : β -> α} (hg : IsInducing g) (f : N -> M) (hf : forall {c : N} {x : β}, g (c • x) = f c • g x) :
    ContinuousConstSMul N β where
  continuous_const_smul c := by
    simpa only [Function.comp_def, hf, hg.continuous_iff] using hg.continuous.fun_const_smul (f c)

@[to_additive]
/--
theorem `smul_closure_subset` / 定理 `smul_closure_subset`

English:
theorem smul_closure_subset
  given: (c : M) (s : Set α)
  statement: c • closure s subseteq closure (c • s)
  proof: ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset

@[to_additive]

中文:
定理 smul_closure_subset
  条件: (c : M) (s : 集合 α)
  结论: c • closure s subseteq closure (c • s)
  证明: ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset

@[to_additive]

Depends on / 依赖: Set.mapsTo_image, closure, continuous_const_smul, image_subset, mapsTo_image
-/
theorem smul_closure_subset (c : M) (s : Set α) : c • closure s subseteq closure (c • s) :=
  ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset

@[to_additive]
/--
theorem `set_smul_closure_subset` / 定理 `set_smul_closure_subset`

English:
theorem set_smul_closure_subset
  given: (s : Set M) (t : Set α)
  statement: s • closure t subseteq closure (s • t)
  proof: by
  simp only [← iUnion_smul_set]
exact iUnion₂_subset fun c hc => (smul_closure_subset c t).trans closure_mono
    subset_biUnion_of_mem (u := (· • t)) hc

中文:
定理 set_smul_closure_subset
  条件: (s : 集合 M) (t : 集合 α)
  结论: s • closure t subseteq closure (s • t)
  证明: by
  simp only [← iUnion_smul_set]
exact iUnion₂_subset fun c hc => (smul_closure_subset c t).trans closure_mono
    subset_biUnion_of_mem (u := (· • t)) hc

Depends on / 依赖: closure_mono, iUnion_smul_set, smul_closure_subset, subset_biUnion_of_mem
-/
theorem set_smul_closure_subset (s : Set M) (t : Set α) : s • closure t subseteq closure (s • t) := by
  simp only [← iUnion_smul_set]
exact iUnion₂_subset fun c hc => (smul_closure_subset c t).trans closure_mono
    subset_biUnion_of_mem (u := (· • t)) hc

/--
theorem `isClosed_setOfPred_map_smul` / 定理 `isClosed_setOfPred_map_smul`

English:
theorem isClosed_setOfPred_map_smul
  statement: {N : Type*} (α β) [SMul M α] [SMul N β]
  proof: by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_smul := isClosed_setOfPred_map_smul

中文:
定理 isClosed_setOfPred_map_smul
  结论: {N : 类型} (α β) [标量乘法 M α] [标量乘法 N β]
  证明: by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_smul := isClosed_setOfPred_map_smul

Depends on / 依赖: Set.ofPred_forall, const_smul, continuous_apply, isClosed_eq, isClosed_iInter, ofPred_forall
-/
theorem isClosed_setOfPred_map_smul {N : Type*} (α β) [SMul M α] [SMul N β]
    [TopologicalSpace β] [T2Space β] [ContinuousConstSMul N β] (σ : M -> N) :
    IsClosed { f : α -> β | forall c x, f (c • x) = σ c • f x } := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_smul := isClosed_setOfPred_map_smul

end SMul

section SMulZeroClass

variable [TopologicalSpace α] [Zero α] [SMulZeroClass M α] [ContinuousConstSMul M α]

/--
theorem `Filter.Tendsto.const_smul_zero` / 定理 `Filter.Tendsto.const_smul_zero`

English:
theorem Filter.Tendsto.const_smul_zero
  statement: {g : β -> α} {l : Filter β}
  proof: smul_zero c (A := α) ▸ hg.const_smul c

中文:
定理 滤子.收敛.const_smul_zero
  结论: {g : β -> α} {l : 滤子 β}
  证明: smul_zero c (A := α) ▸ hg.const_smul c
-/
protected theorem Filter.Tendsto.const_smul_zero {g : β -> α} {l : Filter β}
    (c : M) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => c • g x) l (𝓝 0) :=
  smul_zero c (A := α) ▸ hg.const_smul c

end SMulZeroClass

section Monoid

variable [TopologicalSpace α]
variable [Monoid M] [MulAction M α] [ContinuousConstSMul M α]

@[to_additive]
/--
Instance `Units.continuousConstSMul` / 实例 `Units.continuousConstSMul`

English:
instance Units.continuousConstSMul
  signature: : ContinuousConstSMul Mˣ α where
  body: continuous_const_smul (m : M)

@[to_additive]

中文:
实例 单位群.continuousConstSMul
  签名: : 连续常数标量乘法 Mˣ α where
  定义体: continuous_const_smul (m : M)

@[to_additive]

Depends on / 依赖: continuous_const_smul
-/
instance Units.continuousConstSMul : ContinuousConstSMul Mˣ α where
  continuous_const_smul m := continuous_const_smul (m : M)

@[to_additive]
/--
theorem `smul_closure_orbit_subset` / 定理 `smul_closure_orbit_subset`

English:
theorem smul_closure_orbit_subset
  given: (c : M) (x : α)
  proof: (smul_closure_subset c _).trans closure_mono MulAction.smul_orbit_subset _ _

中文:
定理 smul_closure_orbit_subset
  条件: (c : M) (x : α)
  证明: (smul_closure_subset c _).trans closure_mono MulAction.smul_orbit_subset _ _

Depends on / 依赖: MulAction, MulAction.smul_orbit_subset, closure_mono, smul_closure_subset, smul_orbit_subset
-/
theorem smul_closure_orbit_subset (c : M) (x : α) :
    c • closure (MulAction.orbit M x) subseteq closure (MulAction.orbit M x) :=
(smul_closure_subset c _).trans closure_mono MulAction.smul_orbit_subset _ _

end Monoid

section Group

variable {G : Type*} [TopologicalSpace α] [Group G] [MulAction G α] [ContinuousConstSMul G α]

@[to_additive]
/--
theorem `tendsto_const_smul_iff` / 定理 `tendsto_const_smul_iff`

English:
theorem tendsto_const_smul_iff
  given: {f : β -> α} {l : Filter β} {a : α} (c : G)
  proof: ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

中文:
定理 tendsto_const_smul_iff
  条件: {f : β -> α} {l : 滤子 β} {a : α} (c : G)
  证明: ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

Depends on / 依赖: const_smul, h.const_smul, inv_smul_smul
-/
theorem tendsto_const_smul_iff {f : β -> α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

variable [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β}

@[to_additive]
/--
theorem `continuousWithinAt_const_smul_iff` / 定理 `continuousWithinAt_const_smul_iff`

English:
theorem continuousWithinAt_const_smul_iff
  given: (c : G)
  proof: tendsto_const_smul_iff c

@[to_additive]

中文:
定理 continuousWithinAt_const_smul_iff
  条件: (c : G)
  证明: tendsto_const_smul_iff c

@[to_additive]

Depends on / 依赖: tendsto_const_smul_iff
-/
theorem continuousWithinAt_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[to_additive]
/--
theorem `continuousOn_const_smul_iff` / 定理 `continuousOn_const_smul_iff`

English:
theorem continuousOn_const_smul_iff
  given: (c : G)
  proof: forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c

@[to_additive]

中文:
定理 continuousOn_const_smul_iff
  条件: (c : G)
  证明: forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c

@[to_additive]

Depends on / 依赖: continuousWithinAt_const_smul_iff
-/
theorem continuousOn_const_smul_iff (c : G) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c

@[to_additive]
/--
theorem `continuousAt_const_smul_iff` / 定理 `continuousAt_const_smul_iff`

English:
theorem continuousAt_const_smul_iff
  given: (c : G)
  proof: tendsto_const_smul_iff c

@[to_additive]

中文:
定理 continuousAt_const_smul_iff
  条件: (c : G)
  证明: tendsto_const_smul_iff c

@[to_additive]

Depends on / 依赖: tendsto_const_smul_iff
-/
theorem continuousAt_const_smul_iff (c : G) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[to_additive]
/--
theorem `continuous_const_smul_iff` / 定理 `continuous_const_smul_iff`

English:
theorem continuous_const_smul_iff
  given: (c : G)
  statement: (Continuous fun x => c • f x) ↔ Continuous f
  proof: by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]

中文:
定理 continuous_const_smul_iff
  条件: (c : G)
  结论: (连续 fun x => c • f x) ↔ 连续 f
  证明: by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]

Depends on / 依赖: continuousAt_const_smul_iff, continuous_iff_continuousAt
-/
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive (attr := simps!)]
/--
Definition of `Homeomorph.smul` / `Homeomorph.smul` 的定义

English:
definition Homeomorph.smul
  signature: (γ : G)
  body: MulAction.toPerm γ

@[to_additive]

中文:
定义 同胚.smul
  签名: (γ : G)
  定义体: MulAction.toPerm γ

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, toPerm
-/
def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ

@[to_additive]
/--
lemma `Homeomorph.smul_symm` / 引理 `Homeomorph.smul_symm`

English:
lemma Homeomorph.smul_symm
  given: {g : G}
  statement: (Homeomorph.smul (α := α) g).symm = Homeomorph.smul g⁻¹
  proof: Homeomorph.ext_iff.mpr smul_symm_apply g

中文:
引理 同胚.smul_symm
  条件: {g : G}
  结论: (同胚.smul (α := α) g).symm = 同胚.smul g⁻¹
  证明: Homeomorph.ext_iff.mpr smul_symm_apply g

Depends on / 依赖: Homeomorph, Homeomorph.smul
-/
lemma Homeomorph.smul_symm {g : G} : (Homeomorph.smul (α := α) g).symm = Homeomorph.smul g⁻¹ :=
Homeomorph.ext_iff.mpr smul_symm_apply g

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

@[to_additive]
/--
theorem `isHomeomorph_smul` / 定理 `isHomeomorph_smul`

English:
theorem isHomeomorph_smul
  given: (c : G)
  statement: IsHomeomorph fun x : α => c • x
  proof: (Homeomorph.smul c).isHomeomorph

@[to_additive]

中文:
定理 isHomeomorph_smul
  条件: (c : G)
  结论: 是同胚 fun x : α => c • x
  证明: (Homeomorph.smul c).isHomeomorph

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.smul, isHomeomorph
-/
theorem isHomeomorph_smul (c : G) : IsHomeomorph fun x : α => c • x :=
  (Homeomorph.smul c).isHomeomorph

@[to_additive]
/--
theorem `isOpenMap_smul` / 定理 `isOpenMap_smul`

English:
theorem isOpenMap_smul
  given: (c : G)
  statement: IsOpenMap fun x : α => c • x
  proof: (Homeomorph.smul c).isOpenMap

@[to_additive]

中文:
定理 isOpenMap_smul
  条件: (c : G)
  结论: 是开映射 fun x : α => c • x
  证明: (Homeomorph.smul c).isOpenMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.smul, isOpenMap
-/
theorem isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).isOpenMap

@[to_additive]
/--
theorem `IsOpen.smul` / 定理 `IsOpen.smul`

English:
theorem IsOpen.smul
  given: {s : Set α} (hs : IsOpen s) (c : G)
  statement: IsOpen (c • s)
  proof: isOpenMap_smul c s hs

@[to_additive]

中文:
定理 是开集.smul
  条件: {s : 集合 α} (hs : 是开集 s) (c : G)
  结论: 是开集 (c • s)
  证明: isOpenMap_smul c s hs

@[to_additive]

Depends on / 依赖: isOpenMap_smul
-/
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  isOpenMap_smul c s hs

@[to_additive]
/--
theorem `isClosedMap_smul` / 定理 `isClosedMap_smul`

English:
theorem isClosedMap_smul
  given: (c : G)
  statement: IsClosedMap fun x : α => c • x
  proof: (Homeomorph.smul c).isClosedMap

@[to_additive]

中文:
定理 isClosedMap_smul
  条件: (c : G)
  结论: 是闭映射 fun x : α => c • x
  证明: (Homeomorph.smul c).isClosedMap

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.smul, isClosedMap
-/
theorem isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).isClosedMap

@[to_additive]
/--
theorem `IsClosed.smul` / 定理 `IsClosed.smul`

English:
theorem IsClosed.smul
  given: {s : Set α} (hs : IsClosed s) (c : G)
  statement: IsClosed (c • s)
  proof: isClosedMap_smul c s hs

@[to_additive]

中文:
定理 是闭集.smul
  条件: {s : 集合 α} (hs : 是闭集 s) (c : G)
  结论: 是闭集 (c • s)
  证明: isClosedMap_smul c s hs

@[to_additive]

Depends on / 依赖: isClosedMap_smul
-/
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  isClosedMap_smul c s hs

@[to_additive]
/--
theorem `closure_smul` / 定理 `closure_smul`

English:
theorem closure_smul
  given: (c : G) (s : Set α)
  statement: closure (c • s) = c • closure s
  proof: ((Homeomorph.smul c).image_closure s).symm

@[to_additive]

中文:
定理 closure_smul
  条件: (c : G) (s : 集合 α)
  结论: closure (c • s) = c • closure s
  证明: ((Homeomorph.smul c).image_closure s).symm

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.smul, image_closure
-/
theorem closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s :=
  ((Homeomorph.smul c).image_closure s).symm

@[to_additive]
/--
theorem `Dense.smul` / 定理 `Dense.smul`

English:
theorem Dense.smul
  given: (c : G) {s : Set α} (hs : Dense s)
  statement: Dense (c • s)
  proof: by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]

@[to_additive]

中文:
定理 稠密.smul
  条件: (c : G) {s : 集合 α} (hs : 稠密 s)
  结论: 稠密 (c • s)
  证明: by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]

@[to_additive]

Depends on / 依赖: closure_smul, dense_iff_closure_eq, smul_set_univ
-/
theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]

@[to_additive]
/--
theorem `interior_smul` / 定理 `interior_smul`

English:
theorem interior_smul
  given: (c : G) (s : Set α)
  statement: interior (c • s) = c • interior s
  proof: ((Homeomorph.smul c).image_interior s).symm

中文:
定理 interior_smul
  条件: (c : G) (s : 集合 α)
  结论: interior (c • s) = c • interior s
  证明: ((Homeomorph.smul c).image_interior s).symm

Depends on / 依赖: Homeomorph, Homeomorph.smul, image_interior
-/
theorem interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smul c).image_interior s).symm

open scoped Pointwise in
@[to_additive]
/--
lemma `nhds_smul` / 引理 `nhds_smul`

English:
lemma nhds_smul
  given: (c : G) (x : α)
  statement: 𝓝 (c • x) = c • 𝓝 x
  proof: .symm (Homeomorph.smul c).map_nhds_eq x

中文:
引理 nhds_smul
  条件: (c : G) (x : α)
  结论: 𝓝 (c • x) = c • 𝓝 x
  证明: .symm (Homeomorph.smul c).map_nhds_eq x

Depends on / 依赖: Homeomorph, Homeomorph.smul, map_nhds_eq
-/
lemma nhds_smul (c : G) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
.symm (Homeomorph.smul c).map_nhds_eq x

open scoped Pointwise in
@[to_additive]
/--
lemma `punctured_nhds_smul` / 引理 `punctured_nhds_smul`

English:
lemma punctured_nhds_smul
  given: (c : G) (x : α)
  statement: 𝓝[!=] (c • x) = c • 𝓝[!=] x
  proof: .symm (Homeomorph.smul c).map_punctured_nhds_eq x

@[to_additive]

中文:
引理 punctured_nhds_smul
  条件: (c : G) (x : α)
  结论: 𝓝[!=] (c • x) = c • 𝓝[!=] x
  证明: .symm (Homeomorph.smul c).map_punctured_nhds_eq x

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.smul, map_punctured_nhds_eq
-/
lemma punctured_nhds_smul (c : G) (x : α) : 𝓝[!=] (c • x) = c • 𝓝[!=] x :=
.symm (Homeomorph.smul c).map_punctured_nhds_eq x

@[to_additive]
/--
theorem `IsOpen.smul_left` / 定理 `IsOpen.smul_left`

English:
theorem IsOpen.smul_left
  given: {s : Set G} {t : Set α} (ht : IsOpen t)
  statement: IsOpen (s • t)
  proof: by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _

@[to_additive]

中文:
定理 是开集.smul_left
  条件: {s : 集合 G} {t : 集合 α} (ht : 是开集 t)
  结论: 是开集 (s • t)
  证明: by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _

@[to_additive]

Depends on / 依赖: ht.smul, iUnion_smul_set, isOpen_biUnion
-/
theorem IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen t) : IsOpen (s • t) := by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _

@[to_additive]
/--
theorem `subset_interior_smul_right` / 定理 `subset_interior_smul_right`

English:
theorem subset_interior_smul_right
  given: {s : Set G} {t : Set α}
  statement: s • interior t subseteq interior (s • t)
  proof: interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left

@[to_additive (attr := simp)]

中文:
定理 subset_interior_smul_right
  条件: {s : 集合 G} {t : 集合 α}
  结论: s • interior t subseteq interior (s • t)
  证明: interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left

@[to_additive (attr := simp)]

Depends on / 依赖: Set.smul_subset_smul_left, interior_maximal, interior_subset, isOpen_interior, isOpen_interior.smul_left, smul_left, smul_subset_smul_left
-/
theorem subset_interior_smul_right {s : Set G} {t : Set α} : s • interior t subseteq interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left

@[to_additive (attr := simp)]
/--
theorem `smul_mem_nhds_smul_iff` / 定理 `smul_mem_nhds_smul_iff`

English:
theorem smul_mem_nhds_smul_iff
  given: {t : Set α} (g : G) {a : α}
  statement: g • t in 𝓝 (g • a) ↔ t in 𝓝 a
  proof: (Homeomorph.smul g).isOpenEmbedding.image_mem_nhds

@[to_additive] alias ⟨_, smul_mem_nhds_smul⟩ := smul_mem_nhds_smul_iff

@[to_additive (attr := simp)]

中文:
定理 smul_mem_nhds_smul_iff
  条件: {t : 集合 α} (g : G) {a : α}
  结论: g • t in 𝓝 (g • a) ↔ t in 𝓝 a
  证明: (Homeomorph.smul g).isOpenEmbedding.image_mem_nhds

@[to_additive] alias ⟨_, smul_mem_nhds_smul⟩ := smul_mem_nhds_smul_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Homeomorph, Homeomorph.smul, image_mem_nhds, isOpenEmbedding, isOpenEmbedding.image_mem_nhds
-/
theorem smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : α} : g • t in 𝓝 (g • a) ↔ t in 𝓝 a :=
  (Homeomorph.smul g).isOpenEmbedding.image_mem_nhds

@[to_additive] alias ⟨_, smul_mem_nhds_smul⟩ := smul_mem_nhds_smul_iff

@[to_additive (attr := simp)]
/--
theorem `smul_mem_nhds_self` / 定理 `smul_mem_nhds_self`

English:
theorem smul_mem_nhds_self
  given: [TopologicalSpace G] [ContinuousConstSMul G G] {g : G} {s : Set G}
  proof: by
  rw [← smul_mem_nhds_smul_iff g⁻¹]; simp

中文:
定理 smul_mem_nhds_self
  条件: [拓扑空间 G] [连续常数标量乘法 G G] {g : G} {s : 集合 G}
  证明: by
  rw [← smul_mem_nhds_smul_iff g⁻¹]; simp

Depends on / 依赖: smul_mem_nhds_smul_iff
-/
theorem smul_mem_nhds_self [TopologicalSpace G] [ContinuousConstSMul G G] {g : G} {s : Set G} :
    g • s in 𝓝 g ↔ s in 𝓝 1 := by
  rw [← smul_mem_nhds_smul_iff g⁻¹]; simp

namespace MulAction.IsPretransitive

variable (G)

@[to_additive]
/--
lemma `t1Space_iff` / 引理 `t1Space_iff`

English:
lemma t1Space_iff
  given: (x : α) [IsPretransitive G α]
  proof: by
  refine ⟨fun H => isClosed_singleton, fun hx => ⟨fun y => ?_⟩⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

@[to_additive]

中文:
引理 t1Space_iff
  条件: (x : α) [是Pretransitive G α]
  证明: by
  refine ⟨fun H => isClosed_singleton, fun hx => ⟨fun y => ?_⟩⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

@[to_additive]

Depends on / 依赖: MulAction, MulAction.exists_smul_eq, exists_smul_eq, hx.smul, image_singleton, image_smul, isClosed_singleton
-/
lemma t1Space_iff (x : α) [IsPretransitive G α] :
    T1Space α ↔ IsClosed {x} := by
  refine ⟨fun H => isClosed_singleton, fun hx => ⟨fun y => ?_⟩⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

@[to_additive]
/--
lemma `discreteTopology_iff` / 引理 `discreteTopology_iff`

English:
lemma discreteTopology_iff
  given: (x : α) [IsPretransitive G α]
  proof: by
  rw [discreteTopology_iff_isOpen_singleton]
  refine ⟨fun H => H _, fun hx y => ?_⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

中文:
引理 discreteTopology_iff
  条件: (x : α) [是Pretransitive G α]
  证明: by
  rw [discreteTopology_iff_isOpen_singleton]
  refine ⟨fun H => H _, fun hx y => ?_⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

Depends on / 依赖: MulAction, MulAction.exists_smul_eq, discreteTopology_iff_isOpen_singleton, exists_smul_eq, hx.smul, image_singleton, image_smul
-/
lemma discreteTopology_iff (x : α) [IsPretransitive G α] :
    DiscreteTopology α ↔ IsOpen {x} := by
  rw [discreteTopology_iff_isOpen_singleton]
  refine ⟨fun H => H _, fun hx y => ?_⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton]; rw [image_smul]
  exact hx.smul _

end MulAction.IsPretransitive

end Group

section GroupWithZero

variable {G₀ : Type*} [TopologicalSpace α] [GroupWithZero G₀] [MulAction G₀ α]
  [ContinuousConstSMul G₀ α]

/--
theorem `tendsto_const_smul_iff₀` / 定理 `tendsto_const_smul_iff₀`

English:
theorem tendsto_const_smul_iff₀
  given: {f : β -> α} {l : Filter β} {a : α} {c : G₀} (hc : c != 0)
  proof: tendsto_const_smul_iff (Units.mk0 c hc)

中文:
定理 tendsto_const_smul_iff₀
  条件: {f : β -> α} {l : 滤子 β} {a : α} {c : G₀} (hc : c != 0)
  证明: tendsto_const_smul_iff (Units.mk0 c hc)

Depends on / 依赖: Units.mk0, tendsto_const_smul_iff
-/
theorem tendsto_const_smul_iff₀ {f : β -> α} {l : Filter β} {a : α} {c : G₀} (hc : c != 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable [TopologicalSpace β] {f : β -> α} {b : β} {c : G₀} {s : Set β}

/--
theorem `continuousWithinAt_const_smul_iff₀` / 定理 `continuousWithinAt_const_smul_iff₀`

English:
theorem continuousWithinAt_const_smul_iff₀
  given: (hc : c != 0)
  proof: tendsto_const_smul_iff (Units.mk0 c hc)

中文:
定理 continuousWithinAt_const_smul_iff₀
  条件: (hc : c != 0)
  证明: tendsto_const_smul_iff (Units.mk0 c hc)

Depends on / 依赖: Units.mk0, tendsto_const_smul_iff
-/
theorem continuousWithinAt_const_smul_iff₀ (hc : c != 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)

/--
theorem `continuousOn_const_smul_iff₀` / 定理 `continuousOn_const_smul_iff₀`

English:
theorem continuousOn_const_smul_iff₀
  given: (hc : c != 0)
  proof: continuousOn_const_smul_iff (Units.mk0 c hc)

中文:
定理 continuousOn_const_smul_iff₀
  条件: (hc : c != 0)
  证明: continuousOn_const_smul_iff (Units.mk0 c hc)

Depends on / 依赖: Units.mk0, continuousOn_const_smul_iff
-/
theorem continuousOn_const_smul_iff₀ (hc : c != 0) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff (Units.mk0 c hc)

/--
theorem `continuousAt_const_smul_iff₀` / 定理 `continuousAt_const_smul_iff₀`

English:
theorem continuousAt_const_smul_iff₀
  given: (hc : c != 0)
  proof: continuousAt_const_smul_iff (Units.mk0 c hc)

中文:
定理 continuousAt_const_smul_iff₀
  条件: (hc : c != 0)
  证明: continuousAt_const_smul_iff (Units.mk0 c hc)

Depends on / 依赖: Units.mk0, continuousAt_const_smul_iff
-/
theorem continuousAt_const_smul_iff₀ (hc : c != 0) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff (Units.mk0 c hc)

/--
theorem `continuous_const_smul_iff₀` / 定理 `continuous_const_smul_iff₀`

English:
theorem continuous_const_smul_iff₀
  given: (hc : c != 0)
  statement: (Continuous fun x => c • f x) ↔ Continuous f
  proof: continuous_const_smul_iff (Units.mk0 c hc)

中文:
定理 continuous_const_smul_iff₀
  条件: (hc : c != 0)
  结论: (连续 fun x => c • f x) ↔ 连续 f
  证明: continuous_const_smul_iff (Units.mk0 c hc)

Depends on / 依赖: Units.mk0, continuous_const_smul_iff
-/
theorem continuous_const_smul_iff₀ (hc : c != 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
@[simps! -fullyApplied apply]
/--
Definition of `Homeomorph.smulOfNeZero` / `Homeomorph.smulOfNeZero` 的定义

English:
definition Homeomorph.smulOfNeZero
  signature: (c : G₀) (hc : c != 0)
  body: Homeomorph.smul (Units.mk0 c hc)

@[simp]

中文:
定义 同胚.smulOfNeZero
  签名: (c : G₀) (hc : c != 0)
  定义体: Homeomorph.smul (Units.mk0 c hc)

@[simp]
-/
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c != 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)

@[simp]
/--
theorem `Homeomorph.smulOfNeZero_symm_apply` / 定理 `Homeomorph.smulOfNeZero_symm_apply`

English:
theorem Homeomorph.smulOfNeZero_symm_apply
  given: {c : G₀} (hc : c != 0)
  proof: rfl

中文:
定理 同胚.smulOfNeZero_symm_apply
  条件: {c : G₀} (hc : c != 0)
  证明: rfl
-/
theorem Homeomorph.smulOfNeZero_symm_apply {c : G₀} (hc : c != 0) :
    ⇑(Homeomorph.smulOfNeZero c hc).symm = (c⁻¹ • · : α -> α) :=
  rfl

/--
theorem `isHomeomorph_smul₀` / 定理 `isHomeomorph_smul₀`

English:
theorem isHomeomorph_smul₀
  given: {c : G₀} (hc : c != 0)
  statement: IsHomeomorph fun x : α => c • x
  proof: (Homeomorph.smulOfNeZero c hc).isHomeomorph

中文:
定理 isHomeomorph_smul₀
  条件: {c : G₀} (hc : c != 0)
  结论: 是同胚 fun x : α => c • x
  证明: (Homeomorph.smulOfNeZero c hc).isHomeomorph

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, isHomeomorph, smulOfNeZero
-/
theorem isHomeomorph_smul₀ {c : G₀} (hc : c != 0) : IsHomeomorph fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isHomeomorph

/--
theorem `isOpenMap_smul₀` / 定理 `isOpenMap_smul₀`

English:
theorem isOpenMap_smul₀
  given: {c : G₀} (hc : c != 0)
  statement: IsOpenMap fun x : α => c • x
  proof: (Homeomorph.smulOfNeZero c hc).isOpenMap

中文:
定理 isOpenMap_smul₀
  条件: {c : G₀} (hc : c != 0)
  结论: 是开映射 fun x : α => c • x
  证明: (Homeomorph.smulOfNeZero c hc).isOpenMap

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, isOpenMap, smulOfNeZero
-/
theorem isOpenMap_smul₀ {c : G₀} (hc : c != 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isOpenMap

/--
theorem `IsOpen.smul₀` / 定理 `IsOpen.smul₀`

English:
theorem IsOpen.smul₀
  given: {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c != 0)
  statement: IsOpen (c • s)
  proof: isOpenMap_smul₀ hc s hs

中文:
定理 是开集.smul₀
  条件: {c : G₀} {s : 集合 α} (hs : 是开集 s) (hc : c != 0)
  结论: 是开集 (c • s)
  证明: isOpenMap_smul₀ hc s hs
-/
theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c != 0) : IsOpen (c • s) :=
  isOpenMap_smul₀ hc s hs

/--
theorem `interior_smul₀` / 定理 `interior_smul₀`

English:
theorem interior_smul₀
  given: {c : G₀} (hc : c != 0) (s : Set α)
  statement: interior (c • s) = c • interior s
  proof: ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

中文:
定理 interior_smul₀
  条件: {c : G₀} (hc : c != 0) (s : 集合 α)
  结论: interior (c • s) = c • interior s
  证明: ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, image_interior, smulOfNeZero
-/
theorem interior_smul₀ {c : G₀} (hc : c != 0) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

/--
theorem `closure_smul₀'` / 定理 `closure_smul₀'`

English:
theorem closure_smul₀'
  given: {c : G₀} (hc : c != 0) (s : Set α)
  proof: ((Homeomorph.smulOfNeZero c hc).image_closure s).symm

中文:
定理 closure_smul₀'
  条件: {c : G₀} (hc : c != 0) (s : 集合 α)
  证明: ((Homeomorph.smulOfNeZero c hc).image_closure s).symm

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, image_closure, smulOfNeZero
-/
theorem closure_smul₀' {c : G₀} (hc : c != 0) (s : Set α) :
    closure (c • s) = c • closure s :=
  ((Homeomorph.smulOfNeZero c hc).image_closure s).symm

/--
theorem `closure_smul₀` / 定理 `closure_smul₀`

English:
theorem closure_smul₀
  statement: {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact closure_smul₀' hc s

中文:
定理 closure_smul₀
  结论: {E} [零 E] [带零乘法作用 G₀ E] [拓扑空间 E] [T1空间 E]
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact closure_smul₀' hc s

Depends on / 依赖: closure, closure_singleton, eq_empty_or_nonempty, eq_or_ne, hs.closure, zero_smul_set
-/
theorem closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
    [ContinuousConstSMul G₀ E] (c : G₀) (s : Set E) : closure (c • s) = c • closure s := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact closure_smul₀' hc s

open scoped Pointwise in
/--
lemma `nhds_smul₀` / 引理 `nhds_smul₀`

English:
lemma nhds_smul₀
  given: {c : G₀} (hc : c != 0) (x : α)
  statement: 𝓝 (c • x) = c • 𝓝 x
  proof: nhds_smul (Units.mk0 c hc) x

中文:
引理 nhds_smul₀
  条件: {c : G₀} (hc : c != 0) (x : α)
  结论: 𝓝 (c • x) = c • 𝓝 x
  证明: nhds_smul (Units.mk0 c hc) x

Depends on / 依赖: Units.mk0, nhds_smul
-/
lemma nhds_smul₀ {c : G₀} (hc : c != 0) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
  nhds_smul (Units.mk0 c hc) x

open scoped Pointwise in
/--
lemma `punctured_nhds_smul₀` / 引理 `punctured_nhds_smul₀`

English:
lemma punctured_nhds_smul₀
  given: {c : G₀} (hc : c != 0) (x : α)
  statement: 𝓝[!=] (c • x) = c • 𝓝[!=] x
  proof: punctured_nhds_smul (Units.mk0 c hc) x

中文:
引理 punctured_nhds_smul₀
  条件: {c : G₀} (hc : c != 0) (x : α)
  结论: 𝓝[!=] (c • x) = c • 𝓝[!=] x
  证明: punctured_nhds_smul (Units.mk0 c hc) x

Depends on / 依赖: Units.mk0, punctured_nhds_smul
-/
lemma punctured_nhds_smul₀ {c : G₀} (hc : c != 0) (x : α) : 𝓝[!=] (c • x) = c • 𝓝[!=] x :=
  punctured_nhds_smul (Units.mk0 c hc) x

/--
theorem `isClosedMap_smul_of_ne_zero` / 定理 `isClosedMap_smul_of_ne_zero`

English:
theorem isClosedMap_smul_of_ne_zero
  given: {c : G₀} (hc : c != 0)
  statement: IsClosedMap fun x : α => c • x
  proof: (Homeomorph.smulOfNeZero c hc).isClosedMap

中文:
定理 isClosedMap_smul_of_ne_zero
  条件: {c : G₀} (hc : c != 0)
  结论: 是闭映射 fun x : α => c • x
  证明: (Homeomorph.smulOfNeZero c hc).isClosedMap

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, isClosedMap, smulOfNeZero
-/
theorem isClosedMap_smul_of_ne_zero {c : G₀} (hc : c != 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isClosedMap

/--
theorem `IsClosed.smul_of_ne_zero` / 定理 `IsClosed.smul_of_ne_zero`

English:
theorem IsClosed.smul_of_ne_zero
  given: {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c != 0)
  proof: isClosedMap_smul_of_ne_zero hc s hs

中文:
定理 是闭集.smul_of_ne_zero
  条件: {c : G₀} {s : 集合 α} (hs : 是闭集 s) (hc : c != 0)
  证明: isClosedMap_smul_of_ne_zero hc s hs

Depends on / 依赖: isClosedMap_smul_of_ne_zero
-/
theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c != 0) :
    IsClosed (c • s) :=
  isClosedMap_smul_of_ne_zero hc s hs

/--
theorem `isClosedMap_smul₀` / 定理 `isClosedMap_smul₀`

English:
theorem isClosedMap_smul₀
  statement: {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
  proof: by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap

中文:
定理 isClosedMap_smul₀
  结论: {E : 类型} [零 E] [带零乘法作用 G₀ E] [拓扑空间 E]
  证明: by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, eq_or_ne, isClosedMap, isClosedMap_const, smulOfNeZero, zero_smul
-/
theorem isClosedMap_smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) : IsClosedMap fun x : E => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap

/--
theorem `IsClosed.smul₀` / 定理 `IsClosed.smul₀`

English:
theorem IsClosed.smul₀
  statement: {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
  proof: isClosedMap_smul₀ c s hs

中文:
定理 是闭集.smul₀
  结论: {E : 类型} [零 E] [带零乘法作用 G₀ E] [拓扑空间 E]
  证明: isClosedMap_smul₀ c s hs
-/
theorem IsClosed.smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) {s : Set E} (hs : IsClosed s) :
    IsClosed (c • s) :=
  isClosedMap_smul₀ c s hs

/--
theorem `HasCompactMulSupport.comp_smul` / 定理 `HasCompactMulSupport.comp_smul`

English:
theorem HasCompactMulSupport.comp_smul
  statement: {β : Type*} [One β] {f : α -> β} (h : HasCompactMulSupport f)
  proof: h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

中文:
定理 HasCompactMulSupport.comp_smul
  结论: {β : 类型} [幺 β] {f : α -> β} (h : HasCompactMulSupport f)
  证明: h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, comp_homeomorph, h.comp_homeomorph, smulOfNeZero
-/
theorem HasCompactMulSupport.comp_smul {β : Type*} [One β] {f : α -> β} (h : HasCompactMulSupport f)
    {c : G₀} (hc : c != 0) : HasCompactMulSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

/--
theorem `HasCompactSupport.comp_smul` / 定理 `HasCompactSupport.comp_smul`

English:
theorem HasCompactSupport.comp_smul
  statement: {β : Type*} [Zero β] {f : α -> β} (h : HasCompactSupport f)
  proof: h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

中文:
定理 HasCompactSupport.comp_smul
  结论: {β : 类型} [零 β] {f : α -> β} (h : HasCompactSupport f)
  证明: h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

Depends on / 依赖: Homeomorph, Homeomorph.smulOfNeZero, comp_homeomorph, h.comp_homeomorph, smulOfNeZero
-/
theorem HasCompactSupport.comp_smul {β : Type*} [Zero β] {f : α -> β} (h : HasCompactSupport f)
    {c : G₀} (hc : c != 0) : HasCompactSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

end GroupWithZero

namespace IsUnit

variable [Monoid M] [TopologicalSpace α] [MulAction M α] [ContinuousConstSMul M α]

nonrec theorem tendsto_const_smul_iff {f : β -> α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff hc.unit

variable [TopologicalSpace β] {f : β -> α} {b : β} {c : M} {s : Set β}

nonrec theorem continuousWithinAt_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  continuousWithinAt_const_smul_iff hc.unit

nonrec theorem continuousOn_const_smul_iff (hc : IsUnit c) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff hc.unit

nonrec theorem continuousAt_const_smul_iff (hc : IsUnit c) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff hc.unit

nonrec theorem continuous_const_smul_iff (hc : IsUnit c) :
    (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff hc.unit

nonrec theorem isHomeomorph_smul (hc : IsUnit c) : IsHomeomorph fun x : α => c • x :=
  isHomeomorph_smul hc.unit

nonrec theorem isOpenMap_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  isOpenMap_smul hc.unit

nonrec theorem isClosedMap_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  isClosedMap_smul hc.unit

nonrec theorem smul_mem_nhds_smul_iff (hc : IsUnit c) {s : Set α} {a : α} :
    c • s in 𝓝 (c • a) ↔ s in 𝓝 a :=
  smul_mem_nhds_smul_iff hc.unit

/--
theorem `isQuotientMap_smul` / 定理 `isQuotientMap_smul`

English:
theorem isQuotientMap_smul
  statement: {S β} [SMul S M] [SMul S α] [IsScalarTower S M α]
  proof: hf.of_comp_isQuotientMap by convert! hf.comp hc.isHomeomorph_smul.isQuotientMap; ext; simp

中文:
定理 isQuotientMap_smul
  结论: {S β} [标量乘法 S M] [标量乘法 S α] [标量塔 S M α]
  证明: hf.of_comp_isQuotientMap by convert! hf.comp hc.isHomeomorph_smul.isQuotientMap; ext; simp

Depends on / 依赖: convert, hc.isHomeomorph_smul.isQuotientMap, hf.comp, hf.of_comp_isQuotientMap, isHomeomorph_smul, isQuotientMap, of_comp_isQuotientMap
-/
theorem isQuotientMap_smul {S β} [SMul S M] [SMul S α] [IsScalarTower S M α]
    [SMul S β] (f : α ->[S] β) [TopologicalSpace β] (hf : IsQuotientMap f)
    (c : S) (hc : IsUnit (c • 1 : M)) : IsQuotientMap (c • · : β -> β) :=
hf.of_comp_isQuotientMap by convert! hf.comp hc.isHomeomorph_smul.isQuotientMap; ext; simp

/--
theorem `isQuotientMap_nsmul` / 定理 `isQuotientMap_nsmul`

English:
theorem isQuotientMap_nsmul
  statement: {M β} [Semiring M] [AddCommMonoid α] [Module M α]
  proof: isQuotientMap_smul (M := M) ⟨f, map_nsmul f⟩ hf _ by rwa [nsmul_one]

中文:
定理 isQuotientMap_nsmul
  结论: {M β} [半环 M] [加法交换幺半群 α] [模 M α]
  证明: isQuotientMap_smul (M := M) ⟨f, map_nsmul f⟩ hf _ by rwa [nsmul_one]

Depends on / 依赖: isQuotientMap_smul, map_nsmul, nsmul_one
-/
theorem isQuotientMap_nsmul {M β} [Semiring M] [AddCommMonoid α] [Module M α]
    [ContinuousConstSMul M α] [AddMonoid β] (f : α ->+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : Nat) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β -> β) :=
isQuotientMap_smul (M := M) ⟨f, map_nsmul f⟩ hf _ by rwa [nsmul_one]

/--
theorem `isQuotientMap_zsmul` / 定理 `isQuotientMap_zsmul`

English:
theorem isQuotientMap_zsmul
  statement: {M β} [Ring M] [AddCommGroup α] [Module M α]
  proof: isQuotientMap_smul (M := M) ⟨f, map_zsmul f⟩ hf _ by rwa [zsmul_one n]

中文:
定理 isQuotientMap_zsmul
  结论: {M β} [环 M] [加法交换群 α] [模 M α]
  证明: isQuotientMap_smul (M := M) ⟨f, map_zsmul f⟩ hf _ by rwa [zsmul_one n]

Depends on / 依赖: isQuotientMap_smul, map_zsmul, zsmul_one
-/
theorem isQuotientMap_zsmul {M β} [Ring M] [AddCommGroup α] [Module M α]
    [ContinuousConstSMul M α] [AddGroup β] (f : α ->+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : Int) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β -> β) :=
isQuotientMap_smul (M := M) ⟨f, map_zsmul f⟩ hf _ by rwa [zsmul_one n]

end IsUnit

/--
Definition of `ProperlyDiscontinuousSMul` / `ProperlyDiscontinuousSMul` 的定义

English:
class ProperlyDiscontinuousSMul
  parameters: (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T]
  axioms and operations (1):
    - finite_disjoint_inter_image : forall {K L : Set T}, IsCompact K -> IsCompact L -> Set.Finite { γ : Γ | ((γ • ·) '' K inter L).Nonempty }

中文:
类 ProperlyDiscontinuousSMul
  参数: (Γ : 类型) (T : 类型) [拓扑空间 T] [标量乘法 Γ T]
  公理与运算 (1 个):
    - finite_disjoint_inter_image : 对任意 {K L : 集合 T}, 是紧集 K -> 是紧集 L -> 集合.有限 { γ : Γ | ((γ • ·) '' K inter L).非空 }
-/
class ProperlyDiscontinuousSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] :
    Prop where
  /-- Given two compact sets `K` and `L`, `γ • K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    forall {K L : Set T}, IsCompact K -> IsCompact L -> Set.Finite { γ : Γ | ((γ • ·) '' K inter L).Nonempty }

/--
Definition of `ProperlyDiscontinuousVAdd` / `ProperlyDiscontinuousVAdd` 的定义

English:
class ProperlyDiscontinuousVAdd
  parameters: (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T]
  axioms and operations (1):
    - finite_disjoint_inter_image : forall {K L : Set T}, IsCompact K -> IsCompact L -> Set.Finite { γ : Γ | ((γ +ᵥ ·) '' K inter L).Nonempty }

中文:
类 ProperlyDiscontinuousVAdd
  参数: (Γ : 类型) (T : 类型) [拓扑空间 T] [向量加法 Γ T]
  公理与运算 (1 个):
    - finite_disjoint_inter_image : 对任意 {K L : 集合 T}, 是紧集 K -> 是紧集 L -> 集合.有限 { γ : Γ | ((γ +ᵥ ·) '' K inter L).非空 }
-/
class ProperlyDiscontinuousVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] :
  Prop where
  /-- Given two compact sets `K` and `L`, `γ +ᵥ K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    forall {K L : Set T}, IsCompact K -> IsCompact L -> Set.Finite { γ : Γ | ((γ +ᵥ ·) '' K inter L).Nonempty }

attribute [to_additive] ProperlyDiscontinuousSMul

export ProperlyDiscontinuousSMul (finite_disjoint_inter_image)
export ProperlyDiscontinuousVAdd (finite_disjoint_inter_image)

@[to_additive]
/--
lemma `properlyDiscontinuousSMul_iff` / 引理 `properlyDiscontinuousSMul_iff`

English:
lemma properlyDiscontinuousSMul_iff
  given: [TopologicalSpace α] [SMul M α]
  proof: ⟨fun _ _ _ => ProperlyDiscontinuousSMul.finite_disjoint_inter_image, .mk⟩

中文:
引理 properlyDiscontinuousSMul_iff
  条件: [拓扑空间 α] [标量乘法 M α]
  证明: ⟨fun _ _ _ => ProperlyDiscontinuousSMul.finite_disjoint_inter_image, .mk⟩

Depends on / 依赖: ProperlyDiscontinuousSMul, ProperlyDiscontinuousSMul.finite_disjoint_inter_image, finite_disjoint_inter_image
-/
lemma properlyDiscontinuousSMul_iff [TopologicalSpace α] [SMul M α] :
    ProperlyDiscontinuousSMul M α ↔
      forall {K L : Set α}, IsCompact K -> IsCompact L -> {m : M | (m • K inter L).Nonempty}.Finite :=
  ⟨fun _ _ _ => ProperlyDiscontinuousSMul.finite_disjoint_inter_image, .mk⟩

section

variable (Γ : Type*) {T : Type*}
variable [TopologicalSpace T] [SMul Γ T] [ProperlyDiscontinuousSMul Γ T] (x : T)

/--
lemma `ProperlyDiscontinuousSMul.finite_stabilizer'` / 引理 `ProperlyDiscontinuousSMul.finite_stabilizer'`

English:
lemma ProperlyDiscontinuousSMul.finite_stabilizer'
  statement: {γ : Γ | γ • x = x}.Finite
  proof: by
  simp_rw [← mem_singleton_iff, ← singleton_inter_nonempty, ← image_singleton]
  exact finite_disjoint_inter_image isCompact_singleton isCompact_singleton

中文:
引理 ProperlyDiscontinuousSMul.finite_stabilizer'
  结论: {γ : Γ | γ • x = x}.有限
  证明: by
  simp_rw [← mem_singleton_iff, ← singleton_inter_nonempty, ← image_singleton]
  exact finite_disjoint_inter_image isCompact_singleton isCompact_singleton
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer' : {γ : Γ | γ • x = x}.Finite := by
  simp_rw [← mem_singleton_iff, ← singleton_inter_nonempty, ← image_singleton]
  exact finite_disjoint_inter_image isCompact_singleton isCompact_singleton

variable [T2Space T] [LocallyCompactSpace T] [ContinuousConstSMul Γ T] (x : T)

/--
lemma `ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self` / 引理 `ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self`

English:
lemma ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self
  proof: by
  obtain ⟨V, V_cpt, V_nhd⟩ := exists_compact_mem_nhds x
  let Γ₀ := {γ : Γ | ((γ • ·) '' V inter V).Nonempty ∧ γ • x != x}
  have : Finite Γ₀ := (finite_disjoint_inter_image V_cpt V_cpt).subset fun _ => And.left
  choose u v hu hv u_v_disjoint using fun γ : Γ₀ => t2_separation_nhds γ.2.2
  refine

中文:
引理 ProperlyDiscontinuousSMul.存在_nhds_image_smul_eq_self
  证明: by
  obtain ⟨V, V_cpt, V_nhd⟩ := exists_compact_mem_nhds x
  let Γ₀ := {γ : Γ | ((γ • ·) '' V inter V).Nonempty ∧ γ • x != x}
  have : Finite Γ₀ := (finite_disjoint_inter_image V_cpt V_cpt).subset fun _ => And.left
  choose u v hu hv u_v_disjoint using fun γ : Γ₀ => t2_separation_nhds γ.2.2
  refine
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self :
    exists U in 𝓝 x, forall γ : Γ, ((γ • ·) '' U inter U).Nonempty -> γ • x = x := by
  obtain ⟨V, V_cpt, V_nhd⟩ := exists_compact_mem_nhds x
  let Γ₀ := {γ : Γ | ((γ • ·) '' V inter V).Nonempty ∧ γ • x != x}
  have : Finite Γ₀ := (finite_disjoint_inter_image V_cpt V_cpt).subset fun _ => And.left
  choose u v hu hv u_v_disjoint using fun γ : Γ₀ => t2_separation_nhds γ.2.2
  refine ⟨V inter ⋂ γ : Γ₀, (γ.1 • ·) ⁻¹' u γ inter v γ, inter_mem V_nhd (iInter_mem.mpr fun γ =>
    inter_mem ((continuous_const_smul _).continuousAt <| hu γ) (hv γ)), fun γ hγ => ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hγz⟩ := hγ
  by_contra h
  rw [mem_inter_iff]; rw [mem_iInter] at hz hγz
  let γ : Γ₀ := ⟨γ, ⟨_, ⟨z, hz.1, rfl⟩, hγz.1⟩, h⟩
  exact (u_v_disjoint γ).le_bot ⟨(hz.2 γ).1, (hγz.2 γ).2⟩

/--
lemma `ProperlyDiscontinuousSMul.exists_nhds_disjoint_image` / 引理 `ProperlyDiscontinuousSMul.exists_nhds_disjoint_image`

English:
lemma ProperlyDiscontinuousSMul.exists_nhds_disjoint_image
  proof: by
  convert! exists_nhds_image_smul_eq_self Γ x using 4
  rw [← not_imp_not]
  simp [Set.not_disjoint_iff_nonempty_inter]

中文:
引理 ProperlyDiscontinuousSMul.存在_nhds_disjoint_image
  证明: by
  convert! exists_nhds_image_smul_eq_self Γ x using 4
  rw [← not_imp_not]
  simp [Set.not_disjoint_iff_nonempty_inter]
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_disjoint_image :
    exists U in 𝓝 x, forall γ : Γ, γ • x != x -> Disjoint ((γ • ·) '' U) U := by
  convert! exists_nhds_image_smul_eq_self Γ x using 4
  rw [← not_imp_not]
  simp [Set.not_disjoint_iff_nonempty_inter]

end

variable {Γ : Type*} [Group Γ] {T : Type*} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous. -/
@[to_additive /-- A finite group action is always properly discontinuous. -/]
instance (priority := 100) Finite.to_properlyDiscontinuousSMul [Finite Γ] :
    ProperlyDiscontinuousSMul Γ T where finite_disjoint_inter_image _ _ := Set.toFinite _

/--
lemma `ProperlyDiscontinuousSMul.finite_stabilizer` / 引理 `ProperlyDiscontinuousSMul.finite_stabilizer`

English:
lemma ProperlyDiscontinuousSMul.finite_stabilizer
  statement: [ProperlyDiscontinuousSMul Γ T]
  proof: ProperlyDiscontinuousSMul.finite_stabilizer' Γ x

中文:
引理 ProperlyDiscontinuousSMul.finite_stabilizer
  结论: [ProperlyDiscontinuousSMul Γ T]
  证明: ProperlyDiscontinuousSMul.finite_stabilizer' Γ x
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer [ProperlyDiscontinuousSMul Γ T]
    (x : T) : (MulAction.stabilizer Γ x : Set Γ).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer' Γ x

/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive /-- The quotient map by a group action is open, i.e. the quotient by a group
action is an open quotient. -/]
/--
theorem `isOpenMap_quotient_mk'_mul` / 定理 `isOpenMap_quotient_mk'_mul`

English:
theorem isOpenMap_quotient_mk'_mul
  given: [ContinuousConstSMul Γ T]
  proof: MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T -> Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced]; rw [MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU

@[to_additive]

中文:
定理 isOpenMap_quotient_mk'_mul
  条件: [连续常数标量乘法 Γ T]
  证明: MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T -> Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced]; rw [MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU

@[to_additive]

Depends on / 依赖: MulAction, MulAction.orbitRel, orbitRel
-/
theorem isOpenMap_quotient_mk'_mul [ContinuousConstSMul Γ T] :
    letI := MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T -> Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced]; rw [MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU

@[to_additive]
/--
theorem `MulAction.isOpenQuotientMap_quotientMk` / 定理 `MulAction.isOpenQuotientMap_quotientMk`

English:
theorem MulAction.isOpenQuotientMap_quotientMk
  given: [ContinuousConstSMul Γ T]
  proof: ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quotient_mk'_mul⟩

中文:
定理 乘法作用.isOpenQuotientMap_quotientMk
  条件: [连续常数标量乘法 Γ T]
  证明: ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quotient_mk'_mul⟩

Depends on / 依赖: Quot.mk_surjective, _mul, continuous_quot_mk, isOpenMap_quotient_mk, mk_surjective
-/
theorem MulAction.isOpenQuotientMap_quotientMk [ContinuousConstSMul Γ T] :
    IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel Γ T)) :=
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quotient_mk'_mul⟩

/-- The quotient by a discontinuous group action of a locally compact T₂ space is T₂. -/
@[to_additive /-- The quotient by a discontinuous group action of a locally compact T₂
space is T₂. -/]
instance (priority := 100) t2Space_of_properlyDiscontinuousSMul_of_t2Space [T2Space T]
    [LocallyCompactSpace T] [ContinuousConstSMul Γ T] [ProperlyDiscontinuousSMul Γ T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) := by
  let := MulAction.orbitRel Γ T
  set Q := Quotient (MulAction.orbitRel Γ T)
  rw [t2Space_iff_nhds]
  let f : T -> Q := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ != f y₀)
  change exists U in 𝓝 (f x₀), exists V in 𝓝 (f y₀), _
  have hγx₀y₀ : forall γ : Γ, γ • x₀ != y₀ := not_exists.mp (mt Quotient.sound hxy.symm :)
  obtain ⟨K₀, hK₀, K₀_in⟩ := exists_compact_mem_nhds x₀
  obtain ⟨L₀, hL₀, L₀_in⟩ := exists_compact_mem_nhds y₀
  let bad_Γ_set := { γ : Γ | ((γ • ·) '' K₀ inter L₀).Nonempty }
  have bad_Γ_finite : bad_Γ_set.Finite := finite_disjoint_inter_image (Γ := Γ) hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ in bad_Γ_set, (γ • ·) ⁻¹' u γ
  let U₀ := U₀₀ inter K₀
  let V₀₀ := ⋂ γ in bad_Γ_set, v γ
  let V₀ := V₀₀ inter L₀
  have U_nhds : f '' U₀ in 𝓝 (f x₀) := by
    refine f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => ?_) K₀_in)
    exact (continuous_const_smul _).continuousAt (hu γ)
  have V_nhds : f '' V₀ in 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => hv γ) L₀_in)
  refine ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 ?_⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases H : γ in bad_Γ_set
  · exact fun h => (u_v_disjoint γ).le_bot ⟨mem_iInter₂.mp x_in_U₀₀ γ H, mem_iInter₂.mp h.1 γ H⟩
  · rintro ⟨-, h'⟩
    simp only [bad_Γ_set, image_smul, not_nonempty_iff_eq_empty, mem_ofPred_eq] at H
    exact eq_empty_iff_forall_notMem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩

/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive /-- The quotient of a second countable space by an additive group action is second
countable. -/]
/--
theorem `ContinuousConstSMul.secondCountableTopology` / 定理 `ContinuousConstSMul.secondCountableTopology`

English:
theorem ContinuousConstSMul.secondCountableTopology
  statement: [SecondCountableTopology T]
  proof: TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

中文:
定理 连续常数标量乘法.secondCountableTopology
  结论: [第二可数拓扑 T]
  证明: TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

Depends on / 依赖: Quotient, TopologicalSpace, TopologicalSpace.Quotient.secondCountableTopology, _mul, isOpenMap_quotient_mk, secondCountableTopology
-/
theorem ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T]
    [ContinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel Γ T)) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

section nhds

section MulAction

variable {G₀ : Type*} [GroupWithZero G₀] [MulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/--
theorem `smul_mem_nhds_smul_iff₀` / 定理 `smul_mem_nhds_smul_iff₀`

English:
theorem smul_mem_nhds_smul_iff₀
  given: {c : G₀} {s : Set α} {x : α} (hc : c != 0)
  proof: smul_mem_nhds_smul_iff (Units.mk0 c hc)

alias ⟨_, smul_mem_nhds_smul₀⟩ := smul_mem_nhds_smul_iff₀

中文:
定理 smul_mem_nhds_smul_iff₀
  条件: {c : G₀} {s : 集合 α} {x : α} (hc : c != 0)
  证明: smul_mem_nhds_smul_iff (Units.mk0 c hc)

alias ⟨_, smul_mem_nhds_smul₀⟩ := smul_mem_nhds_smul_iff₀

Depends on / 依赖: Units.mk0, smul_mem_nhds_smul_iff
-/
theorem smul_mem_nhds_smul_iff₀ {c : G₀} {s : Set α} {x : α} (hc : c != 0) :
    c • s in 𝓝 (c • x : α) ↔ s in 𝓝 x :=
  smul_mem_nhds_smul_iff (Units.mk0 c hc)

alias ⟨_, smul_mem_nhds_smul₀⟩ := smul_mem_nhds_smul_iff₀

end MulAction

section DistribMulAction

variable {G₀ : Type*} [GroupWithZero G₀] [AddMonoid α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/--
theorem `set_smul_mem_nhds_zero_iff` / 定理 `set_smul_mem_nhds_zero_iff`

English:
theorem set_smul_mem_nhds_zero_iff
  given: {s : Set α} {c : G₀} (hc : c != 0)
  proof: by
  refine Iff.trans ?_ (smul_mem_nhds_smul_iff₀ hc)
  rw [smul_zero]

中文:
定理 set_smul_mem_nhds_zero_iff
  条件: {s : 集合 α} {c : G₀} (hc : c != 0)
  证明: by
  refine Iff.trans ?_ (smul_mem_nhds_smul_iff₀ hc)
  rw [smul_zero]

Depends on / 依赖: Iff.trans, smul_zero
-/
theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c != 0) :
    c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α) := by
  refine Iff.trans ?_ (smul_mem_nhds_smul_iff₀ hc)
  rw [smul_zero]

end DistribMulAction

end nhds
