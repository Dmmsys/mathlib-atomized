/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Topological torsors of groups

This file defines topological torsors of additive and multiplicative groups, that is, torsors where
`+ᵥ` and `-ᵥ` resp. `•` and `/ₛ` are continuous.
-/

@[expose] public section

open Topology

section Torsor

/--
Definition of `IsTopologicalAddTorsor` / `IsTopologicalAddTorsor` 的定义

English:
class IsTopologicalAddTorsor
  parameters: {V : Type*} [AddGroup V] [TopologicalSpace V]
  extends: ContinuousVAdd V P
  axioms and operations (1):
    - continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

中文:
类 是TopologicalAddTorsor
  参数: {V : 类型} [加法群 V] [拓扑空间 V]
  继承: 连续向量加法 V P
  公理与运算 (1 个):
    - continuous_vsub : 连续 (fun x : P × P => x.1 -ᵥ x.2)
-/
class IsTopologicalAddTorsor {V : Type*} [AddGroup V] [TopologicalSpace V]
    (P : Type*) [AddTorsor V P] [TopologicalSpace P] extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

/-- A topological torsor over a topological group is a torsor where `•` and `/ₛ` are continuous. -/
@[to_additive]
/--
Definition of `IsTopologicalTorsor` / `IsTopologicalTorsor` 的定义

English:
class IsTopologicalTorsor
  parameters: {V : Type*} [Group V] [TopologicalSpace V]
  extends: ContinuousSMul V P
  axioms and operations (1):
    - continuous_sdiv : Continuous (fun x : P × P => x.1 /ₛ x.2)

中文:
类 是TopologicalTorsor
  参数: {V : 类型} [群 V] [拓扑空间 V]
  继承: 连续标量乘法 V P
  公理与运算 (1 个):
    - continuous_sdiv : 连续 (fun x : P × P => x.1 /ₛ x.2)
-/
class IsTopologicalTorsor {V : Type*} [Group V] [TopologicalSpace V]
    (P : Type*) [Torsor V P] [TopologicalSpace P] extends ContinuousSMul V P where
  continuous_sdiv : Continuous (fun x : P × P => x.1 /ₛ x.2)

variable {V P α : Type*} [Group V] [TopologicalSpace V] [Torsor V P] [TopologicalSpace P]

export IsTopologicalAddTorsor (continuous_vsub)

export IsTopologicalTorsor (continuous_sdiv)

attribute [fun_prop] continuous_vsub continuous_sdiv

variable [IsTopologicalTorsor P]

@[to_additive]
/--
theorem `Filter.Tendsto.sdiv` / 定理 `Filter.Tendsto.sdiv`

English:
theorem Filter.Tendsto.sdiv
  statement: {l : Filter α} {f g : α -> P} {x y : P} (hf : Tendsto f l (𝓝 x))
  proof: (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.sdiv
  结论: {l : 滤子 α} {f g : α -> P} {x y : P} (hf : 收敛 f l (𝓝 x))
  证明: (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_sdiv, continuous_sdiv.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.sdiv {l : Filter α} {f g : α -> P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f /ₛ g) l (𝓝 (x /ₛ y)) :=
  (continuous_sdiv.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]

@[to_additive (attr := fun_prop)]
/--
theorem `Continuous.sdiv` / 定理 `Continuous.sdiv`

English:
theorem Continuous.sdiv
  given: {f g : α -> P} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_sdiv.comp₂ hf hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.sdiv {f g : α -> P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x /ₛ g x) x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.sdiv {f g : α -> P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x /ₛ g x) s x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]

中文:
定理 连续.sdiv
  条件: {f g : α -> P} (hf : 连续 f) (hg : 连续 g)
  证明: continuous_sdiv.comp₂ hf hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.sdiv {f g : α -> P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x /ₛ g x) x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.sdiv {f g : α -> P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x /ₛ g x) s x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]

Depends on / 依赖: continuous_sdiv, continuous_sdiv.comp
-/
theorem Continuous.sdiv {f g : α -> P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x /ₛ g x) :=
  continuous_sdiv.comp₂ hf hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousAt.sdiv {f g : α -> P} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x /ₛ g x) x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.sdiv {f g : α -> P} {x : α} {s : Set α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x /ₛ g x) s x :=
  hf.sdiv hg

@[to_additive (attr := fun_prop)]
/--
theorem `ContinuousOn.sdiv` / 定理 `ContinuousOn.sdiv`

English:
theorem ContinuousOn.sdiv
  statement: {f g : α -> P} {s : Set α} (hf : ContinuousOn f s)
  proof: fun x hx =>
  (hf x hx).sdiv (hg x hx)

include P in

中文:
定理 ContinuousOn.sdiv
  结论: {f g : α -> P} {s : 集合 α} (hf : ContinuousOn f s)
  证明: fun x hx =>
  (hf x hx).sdiv (hg x hx)

include P in
-/
theorem ContinuousOn.sdiv {f g : α -> P} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => f x /ₛ g x) s := fun x hx =>
  (hf x hx).sdiv (hg x hx)

include P in
variable (V P) in
/-- The underlying group of a topological torsor is a topological group. This is not an instance, as
`P` cannot be inferred. -/
@[to_additive /-- The underlying group of a topological additive torsor is a topological additive
group. This is not an instance, as `P` cannot be inferred. -/]
/--
theorem `IsTopologicalTorsor.to_isTopologicalGroup` / 定理 `IsTopologicalTorsor.to_isTopologicalGroup`

English:
theorem IsTopologicalTorsor.to_isTopologicalGroup
  statement: IsTopologicalGroup V where
  proof: by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

中文:
定理 是TopologicalTorsor.to_isTopologicalGroup
  结论: 是拓扑群 V where
  证明: by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

Depends on / 依赖: Nonempty, Trivialization, VectorBundle, continuous_inv, equals, fun_prop, one_div, sdiv_self, sdiv_smul_eq_sdiv_div, smul_sdiv, smul_smul, trivialization_linear
-/
theorem IsTopologicalTorsor.to_isTopologicalGroup : IsTopologicalGroup V where
  continuous_mul := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, x]
      equals (x.1 • x.2 • p) /ₛ p => rw [smul_smul, smul_sdiv]
    fun_prop
  continuous_inv := by
    have ⟨p⟩ : Nonempty P := inferInstance
    conv =>
      enter [1, v]
      equals p /ₛ (v • p) => rw [sdiv_smul_eq_sdiv_div, sdiv_self, one_div]
    fun_prop

/-- The map `v ↦ v • p` as a homeomorphism between `V` and `P`. -/
@[to_additive (attr := simps!) /-- The map `v ↦ v +ᵥ p` as a homeomorphism between `V` and `P`. -/]
/--
Definition of `Homeomorph.smulConst` / `Homeomorph.smulConst` 的定义

English:
definition Homeomorph.smulConst
  signature: (p : P)
  body: Equiv.smulConst p

中文:
定义 同胚.smulConst
  签名: (p : P)
  定义体: Equiv.smulConst p

Depends on / 依赖: Equiv.smulConst, smulConst
-/
def Homeomorph.smulConst (p : P) : V ≃ₜ P where
  __ := Equiv.smulConst p

/-- The map `p' ↦ p /ₛ p'` as a homeomorphism: `Equiv.constSDiv` as a homeomorphism -/
@[to_additive (attr := simps!)
/-- The map `p' ↦ p -ᵥ p'` as a homeomorphism: `Equiv.constVSub` as a homeomorphism -/]
/--
Definition of `Homeomorph.constSDiv` / `Homeomorph.constSDiv` 的定义

English:
definition Homeomorph.constSDiv
  signature: (p : P)
  body: Equiv.constSDiv p
  continuous_invFun := by
    have := IsTopologicalTorsor.to_isTopologicalGroup V P
    fun_prop

中文:
定义 同胚.constSDiv
  签名: (p : P)
  定义体: Equiv.constSDiv p
  continuous_invFun := by
    have := IsTopologicalTorsor.to_isTopologicalGroup V P
    fun_prop

Depends on / 依赖: Equiv.constSDiv, constSDiv
-/
def Homeomorph.constSDiv (p : P) : P ≃ₜ V where
  toEquiv := Equiv.constSDiv p
  continuous_invFun := by
    have := IsTopologicalTorsor.to_isTopologicalGroup V P
    fun_prop

/--
Definition of `Homeomorph.pointReflection` / `Homeomorph.pointReflection` 的定义

English:
definition Homeomorph.pointReflection
  signature: {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
  body: (Homeomorph.constVSub p).trans (Homeomorph.vaddConst p)

@[simp]

中文:
定义 同胚.pointReflection
  签名: {V P : 类型} [加法群 V] [拓扑空间 V] [加法Torsor V P]
  定义体: (Homeomorph.constVSub p).trans (Homeomorph.vaddConst p)

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.constVSub, Homeomorph.vaddConst, constVSub, vaddConst
-/
def Homeomorph.pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
    [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) : P ≃ₜ P :=
  (Homeomorph.constVSub p).trans (Homeomorph.vaddConst p)

@[simp]
/--
lemma `Homeomorph.coe_pointReflection` / 引理 `Homeomorph.coe_pointReflection`

English:
lemma Homeomorph.coe_pointReflection
  statement: {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
  proof: rfl

中文:
引理 同胚.coe_pointReflection
  结论: {V P : 类型} [加法群 V] [拓扑空间 V] [加法Torsor V P]
  证明: rfl
-/
lemma Homeomorph.coe_pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
    [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) :
    (Homeomorph.pointReflection p : P -> P) = Equiv.pointReflection p := rfl

end Torsor

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalTorsor G
  body: by simp only [sdiv_eq_div]; fun_prop

中文:
实例 :
  签名: 是TopologicalTorsor G
  定义体: by simp only [sdiv_eq_div]; fun_prop

Depends on / 依赖: fun_prop, sdiv_eq_div
-/
instance : IsTopologicalTorsor G where
  continuous_sdiv := by simp only [sdiv_eq_div]; fun_prop

end Group

section Prod

variable
  {V W P Q : Type*}
  [CommGroup V] [TopologicalSpace V]
  [Torsor V P] [TopologicalSpace P] [IsTopologicalTorsor P]
  [CommGroup W] [TopologicalSpace W]
  [Torsor W Q] [TopologicalSpace Q] [IsTopologicalTorsor Q]

@[to_additive instIsTopologicalAddTorsorProd]
/--
Instance `instIsTopologicalTorsorProd` / 实例 `instIsTopologicalTorsorProd`

English:
instance instIsTopologicalTorsorProd
  signature: : IsTopologicalTorsor (P × Q) where
  body: Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

中文:
实例 instIsTopologicalTorsorProd
  签名: : 是TopologicalTorsor (P × Q) where
  定义体: Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

Depends on / 依赖: Continuous, Continuous.prodMk, fun_prop, prodMk
-/
instance instIsTopologicalTorsorProd : IsTopologicalTorsor (P × Q) where
  continuous_smul := Continuous.prodMk (by fun_prop) (by fun_prop)
  continuous_sdiv := Continuous.prodMk (by fun_prop) (by fun_prop)

end Prod

section Pi

variable
  {ι : Type*} {V P : ι -> Type*}
  [forall i, CommGroup (V i)] [forall i, TopologicalSpace (V i)]
  [forall i, Torsor (V i) (P i)] [forall i, TopologicalSpace (P i)] [forall i, IsTopologicalTorsor (P i)]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalTorsor ((i : ι) -> P i)
  body: continuous_pi by simp only [Pi.smul_apply']; fun_prop
continuous_sdiv := continuous_pi by simp only [Pi.sdiv_apply]; fun_prop

中文:
实例 :
  签名: 是TopologicalTorsor ((i : ι) -> P i)
  定义体: continuous_pi by simp only [Pi.smul_apply']; fun_prop
continuous_sdiv := continuous_pi by simp only [Pi.sdiv_apply]; fun_prop

Depends on / 依赖: Pi.smul_apply, continuous_pi, fun_prop, smul_apply
-/
instance : IsTopologicalTorsor ((i : ι) -> P i) where
continuous_smul := continuous_pi by simp only [Pi.smul_apply']; fun_prop
continuous_sdiv := continuous_pi by simp only [Pi.sdiv_apply]; fun_prop

end Pi
