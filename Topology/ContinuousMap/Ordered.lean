/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/

@[expose] public section


variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace ContinuousMap


/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: [PartialOrder β]
  body: fast_instance%
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by aesop)

中文:
实例 partialOrder
  签名: [偏序 β]
  定义体: fast_instance%
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by aesop)

Depends on / 依赖: fast_instance
-/
instance partialOrder [PartialOrder β] : PartialOrder C(α, β) := fast_instance%
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by aesop)

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [PartialOrder β] {f g : C(α, β)}
  statement: f <= g ↔ forall a, f a <= g a
  proof: Pi.le_def

中文:
定理 le_def
  条件: [偏序 β] {f g : C(α, β)}
  结论: f <= g ↔ 对任意 a, f a <= g a
  证明: Pi.le_def

Depends on / 依赖: Pi.le_def, le_def
-/
theorem le_def [PartialOrder β] {f g : C(α, β)} : f <= g ↔ forall a, f a <= g a :=
  Pi.le_def

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [PartialOrder β] {f g : C(α, β)}
  statement: f < g ↔ (forall a, f a <= g a) ∧ exists a, f a < g a
  proof: Pi.lt_def

中文:
定理 lt_def
  条件: [偏序 β] {f g : C(α, β)}
  结论: f < g ↔ (对任意 a, f a <= g a) ∧ 存在 a, f a < g a
  证明: Pi.lt_def

Depends on / 依赖: Pi.lt_def, lt_def
-/
theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (forall a, f a <= g a) ∧ exists a, f a < g a :=
  Pi.lt_def

section SemilatticeSup
variable [SemilatticeSup β] [ContinuousSup β]

/--
Instance `sup` / 实例 `sup`

English:
instance sup
  signature: : Max C(α, β) where max f g
  body: { toFun := fun a => f a ⊔ g a }

中文:
实例 上确界
  签名: : 最大值 C(α, β) where 最大值 f g
  定义体: { toFun := fun a => f a ⊔ g a }
-/
instance sup : Max C(α, β) where max f g := { toFun := fun a => f a ⊔ g a }

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (f g : C(α, β))
  statement: ⇑(f ⊔ g) = ⇑f ⊔ g
  proof: rfl

中文:
引理 coe_sup
  条件: (f g : C(α, β))
  结论: ⇑(f ⊔ g) = ⇑f ⊔ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (f g : C(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl

/--
lemma `sup_apply` / 引理 `sup_apply`

English:
lemma sup_apply
  given: (f g : C(α, β)) (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

中文:
引理 sup_apply
  条件: (f g : C(α, β)) (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl
-/
@[simp] lemma sup_apply (f g : C(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: : SemilatticeSup C(α, β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

中文:
实例 semilatticeSup
  签名: : SemilatticeSup C(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance semilatticeSup : SemilatticeSup C(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

/--
lemma `sup'_apply` / 引理 `sup'_apply`

English:
lemma sup'_apply
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) (a : α)
  proof: Finset.apply_sup'_eq_sup'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

中文:
引理 上确界'_apply
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C(α, β)) (a : α)
  证明: Finset.apply_sup'_eq_sup'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.apply_sup, _comp, _eq_sup, apply_sup
-/
lemma sup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i => f i a :=
  Finset.apply_sup'_eq_sup'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]
/--
lemma `coe_sup'` / 引理 `coe_sup'`

English:
lemma coe_sup'
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β))
  proof: by ext; simp [sup'_apply]

中文:
引理 coe_sup'
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C(α, β))
  证明: by ext; simp [sup'_apply]

Depends on / 依赖: _apply
-/
lemma coe_sup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i => ⇑(f i) := by ext; simp [sup'_apply]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf β] [ContinuousInf β]

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: : Min C(α, β) where min f g
  body: { toFun := fun a => f a ⊓ g a }

中文:
实例 下确界
  签名: : 最小值 C(α, β) where 最小值 f g
  定义体: { toFun := fun a => f a ⊓ g a }
-/
instance inf : Min C(α, β) where min f g := { toFun := fun a => f a ⊓ g a }

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (f g : C(α, β))
  statement: ⇑(f ⊓ g) = ⇑f ⊓ g
  proof: rfl

中文:
引理 coe_inf
  条件: (f g : C(α, β))
  结论: ⇑(f ⊓ g) = ⇑f ⊓ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (f g : C(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl

/--
lemma `inf_apply` / 引理 `inf_apply`

English:
lemma inf_apply
  given: (f g : C(α, β)) (a : α)
  statement: (f ⊓ g) a = f a ⊓ g a
  proof: rfl

中文:
引理 inf_apply
  条件: (f g : C(α, β)) (a : α)
  结论: (f ⊓ g) a = f a ⊓ g a
  证明: rfl
-/
@[simp] lemma inf_apply (f g : C(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: : SemilatticeInf C(α, β)
  body: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

中文:
实例 semilatticeInf
  签名: : SemilatticeInf C(α, β)
  定义体: fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance semilatticeInf : SemilatticeInf C(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

/--
lemma `inf'_apply` / 引理 `inf'_apply`

English:
lemma inf'_apply
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) (a : α)
  proof: Finset.apply_inf'_eq_inf'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

中文:
引理 下确界'_apply
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C(α, β)) (a : α)
  证明: Finset.apply_inf'_eq_inf'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.apply_inf, _comp, _eq_inf, apply_inf
-/
lemma inf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i => f i a :=
  Finset.apply_inf'_eq_inf'_comp H (fun g : C(α, β) => g a) fun _ _ => rfl

@[simp, norm_cast]
/--
lemma `coe_inf'` / 引理 `coe_inf'`

English:
lemma coe_inf'
  given: {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β))
  proof: by ext; simp [inf'_apply]

中文:
引理 coe_inf'
  条件: {ι : 类型} {s : 有限集 ι} (H : s.非空) (f : ι -> C(α, β))
  证明: by ext; simp [inf'_apply]

Depends on / 依赖: _apply
-/
lemma coe_inf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i => ⇑(f i) := by ext; simp [inf'_apply]

end SemilatticeInf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: β] [TopologicalLattice β] : Lattice C(α, β) where

中文:
实例 [格
  签名: β] [拓扑格 β] : 格 C(α, β) where
-/
instance [Lattice β] [TopologicalLattice β] : Lattice C(α, β) where

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a <= b)

/--
Definition of `IccExtend` / `IccExtend` 的定义

English:
definition IccExtend
  signature: (f : C(Set.Icc a b, β))
  body: Set.IccExtend h f

@[simp]

中文:
定义 IccExtend
  签名: (f : C(集合.闭区间 a b, β))
  定义体: Set.IccExtend h f

@[simp]

Depends on / 依赖: IccExtend, Set.IccExtend
-/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f

@[simp]
/--
theorem `coe_IccExtend` / 定理 `coe_IccExtend`

English:
theorem coe_IccExtend
  given: (f : C(Set.Icc a b, β))
  proof: rfl

中文:
定理 coe_IccExtend
  条件: (f : C(集合.闭区间 a b, β))
  证明: rfl
-/
theorem coe_IccExtend (f : C(Set.Icc a b, β)) :
    ((IccExtend h f : C(α, β)) : α -> β) = Set.IccExtend h f :=
  rfl

end Extend

end ContinuousMap
