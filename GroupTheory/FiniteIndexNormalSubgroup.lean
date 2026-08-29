/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Finite-index normal subgroups

This file builds the lattice `FiniteIndexNormalSubgroup G` of finite-index normal subgroups of a
group `G`, and its additive version `FiniteIndexNormalAddSubgroup`.

This is used primarily in the definition of the profinite completion of a group.
-/

@[expose] public section

section

/-- The type of finite-index normal subgroups of a group. -/
@[ext]
/--
Definition of `FiniteIndexNormalSubgroup` / `FiniteIndexNormalSubgroup` 的定义

English:
structure FiniteIndexNormalSubgroup
  parameters: (G : Type*) [Group G]
  extends: Subgroup G
  axioms and operations (2):
    - isNormal' : toSubgroup.Normal  [default: by infer_instance]
    - isFiniteIndex' : toSubgroup.FiniteIndex  [default: by infer_instance]

中文:
结构 FiniteIndexNormal子群
  参数: (G : 类型) [群 G]
  继承: 子群 G
  公理与运算 (2 个):
    - isNormal' : toSubgroup.正规  [默认: by infer_instance]
    - isFiniteIndex' : toSubgroup.FiniteIndex  [默认: by infer_instance]

Depends on / 依赖: FiniteIndex, infer_instance, isFiniteIndex, toSubgroup, toSubgroup.FiniteIndex
-/
structure FiniteIndexNormalSubgroup (G : Type*) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance
  isFiniteIndex' : toSubgroup.FiniteIndex := by infer_instance

/-- The type of finite-index normal additive subgroups of an additive group. -/
@[ext]
/--
Definition of `FiniteIndexNormalAddSubgroup` / `FiniteIndexNormalAddSubgroup` 的定义

English:
structure FiniteIndexNormalAddSubgroup
  parameters: (G : Type*) [AddGroup G]
  extends: AddSubgroup G
  axioms and operations (2):
    - isNormal' : toAddSubgroup.Normal  [default: by infer_instance]
    - isFiniteIndex' : toAddSubgroup.FiniteIndex  [default: by infer_instance]

中文:
结构 FiniteIndexNormalAdd子群
  参数: (G : 类型) [加法群 G]
  继承: 加法子群 G
  公理与运算 (2 个):
    - isNormal' : toAddSubgroup.正规  [默认: by infer_instance]
    - isFiniteIndex' : toAddSubgroup.FiniteIndex  [默认: by infer_instance]

Depends on / 依赖: FiniteIndex, infer_instance, isFiniteIndex, toAddSubgroup, toAddSubgroup.FiniteIndex
-/
structure FiniteIndexNormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance
  isFiniteIndex' : toAddSubgroup.FiniteIndex := by infer_instance

attribute [to_additive] FiniteIndexNormalSubgroup

namespace FiniteIndexNormalSubgroup

variable {G : Type*} [Group G]

@[to_additive]
/--
theorem `toSubgroup_injective` / 定理 `toSubgroup_injective`

English:
theorem toSubgroup_injective
  statement: Function.Injective
  proof: fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]

中文:
定理 toSubgroup_injective
  结论: 函数.单射
  证明: fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]
-/
theorem toSubgroup_injective : Function.Injective
    (fun H => H.toSubgroup : FiniteIndexNormalSubgroup G -> Subgroup G) :=
  fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (FiniteIndexNormalSubgroup G) G
  body: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

@[to_additive]

中文:
实例 :
  签名: 集合状 (FiniteIndexNormal子群 G) G
  定义体: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

@[to_additive]
-/
instance : SetLike (FiniteIndexNormalSubgroup G) G where
  coe U := U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (FiniteIndexNormalSubgroup G)
  body: .ofSetLike (FiniteIndexNormalSubgroup G) G

@[to_additive]

中文:
实例 :
  签名: 偏序 (FiniteIndexNormal子群 G)
  定义体: .ofSetLike (FiniteIndexNormalSubgroup G) G

@[to_additive]

Depends on / 依赖: FiniteIndexNormalSubgroup, ofSetLike
-/
instance : PartialOrder (FiniteIndexNormalSubgroup G) := .ofSetLike (FiniteIndexNormalSubgroup G) G

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (FiniteIndexNormalSubgroup G) G
  body: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

中文:
实例 :
  签名: 子群类 (FiniteIndexNormal子群 G) G
  定义体: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.mul_mem, mul_mem
-/
instance : SubgroupClass (FiniteIndexNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (FiniteIndexNormalSubgroup G) (Subgroup G)
  body: H.toSubgroup

@[to_additive]

中文:
实例 :
  签名: Coe (FiniteIndexNormal子群 G) (子群 G)
  定义体: H.toSubgroup

@[to_additive]

Depends on / 依赖: H.toSubgroup, toSubgroup
-/
instance : Coe (FiniteIndexNormalSubgroup G) (Subgroup G) where
  coe H := H.toSubgroup

@[to_additive]
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.FiniteIndex := H.isFiniteIndex'

@[to_additive]
/--
Instance `instPartialOrderFiniteIndexNormalSubgroup` / 实例 `instPartialOrderFiniteIndexNormalSubgroup`

English:
instance instPartialOrderFiniteIndexNormalSubgroup
  signature: : PartialOrder (FiniteIndexNormalSubgroup G)
  body: inferInstance

@[to_additive]

中文:
实例 instPartialOrderFiniteIndexNormalSubgroup
  签名: : 偏序 (FiniteIndexNormal子群 G)
  定义体: inferInstance

@[to_additive]
-/
instance instPartialOrderFiniteIndexNormalSubgroup : PartialOrder (FiniteIndexNormalSubgroup G) :=
  inferInstance

@[to_additive]
/--
Instance `instInfFiniteIndexNormalSubgroup` / 实例 `instInfFiniteIndexNormalSubgroup`

English:
instance instInfFiniteIndexNormalSubgroup
  signature: : Min (FiniteIndexNormalSubgroup G)
  body: ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊓ V.toSubgroup
    isNormal' := Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup
  }⟩

@[to_additive]

中文:
实例 instInfFiniteIndexNormalSubgroup
  签名: : 最小值 (FiniteIndexNormal子群 G)
  定义体: ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊓ V.toSubgroup
    isNormal' := Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup
  }⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.normal_inf_normal, U.toSubgroup, V.toSubgroup, isNormal, normal_inf_normal, toSubgroup
-/
instance instInfFiniteIndexNormalSubgroup : Min (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊓ V.toSubgroup
    isNormal' := Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup
  }⟩

@[to_additive]
/--
Instance `instSemilatticeInfFiniteIndexNormalSubgroup` / 实例 `instSemilatticeInfFiniteIndexNormalSubgroup`

English:
instance instSemilatticeInfFiniteIndexNormalSubgroup
  signature: :
  body: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeInfFiniteIndexNormalSubgroup
  签名: :
  定义体: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeInf, coe_injective, semilatticeInf
-/
instance instSemilatticeInfFiniteIndexNormalSubgroup :
    SemilatticeInf (FiniteIndexNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (FiniteIndexNormalSubgroup G)
  body: ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊔ V.toSubgroup
    isNormal' := Subgroup.sup_normal U.toSubgroup V.toSubgroup
    isFiniteIndex' := Subgroup.finiteIndex_of_le
      (H := U.toSubgroup) (K := U.toSubgroup ⊔ V.toSubgroup) le_sup_left
  }⟩

@[to_additive]

中文:
实例 :
  签名: 最大值 (FiniteIndexNormal子群 G)
  定义体: ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊔ V.toSubgroup
    isNormal' := Subgroup.sup_normal U.toSubgroup V.toSubgroup
    isFiniteIndex' := Subgroup.finiteIndex_of_le
      (H := U.toSubgroup) (K := U.toSubgroup ⊔ V.toSubgroup) le_sup_left
  }⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.finiteIndex_of_le, Subgroup.sup_normal, U.toSubgroup, V.toSubgroup, finiteIndex_of_le, isFiniteIndex, isNormal, le_sup_left, sup_normal, toSubgroup
-/
instance : Max (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V => {
    toSubgroup := U.toSubgroup ⊔ V.toSubgroup
    isNormal' := Subgroup.sup_normal U.toSubgroup V.toSubgroup
    isFiniteIndex' := Subgroup.finiteIndex_of_le
      (H := U.toSubgroup) (K := U.toSubgroup ⊔ V.toSubgroup) le_sup_left
  }⟩

@[to_additive]
/--
Instance `instSemilatticeSupFiniteIndexNormalSubgroup` / 实例 `instSemilatticeSupFiniteIndexNormalSubgroup`

English:
instance instSemilatticeSupFiniteIndexNormalSubgroup
  signature: :
  body: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeSupFiniteIndexNormalSubgroup
  签名: :
  定义体: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: semilatticeSup, toSubgroup_injective, toSubgroup_injective.semilatticeSup
-/
instance instSemilatticeSupFiniteIndexNormalSubgroup :
    SemilatticeSup (FiniteIndexNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (FiniteIndexNormalSubgroup G)

中文:
实例 :
  签名: 格 (FiniteIndexNormal子群 G)
-/
instance : Lattice (FiniteIndexNormalSubgroup G) where

@[to_additive]
/--
theorem `mem_toSubgroup_iff` / 定理 `mem_toSubgroup_iff`

English:
theorem mem_toSubgroup_iff
  given: {H : FiniteIndexNormalSubgroup G} {g : G}
  statement: g in H.toSubgroup ↔ g in H
  proof: .rfl

中文:
定理 mem_toSubgroup_iff
  条件: {H : FiniteIndexNormal子群 G} {g : G}
  结论: g in H.toSubgroup ↔ g in H
  证明: .rfl
-/
theorem mem_toSubgroup_iff {H : FiniteIndexNormalSubgroup G} {g : G} : g in H.toSubgroup ↔ g in H :=
  .rfl

/-- Bundle a subgroup with typeclass assumptions of normality and finite index. -/
@[to_additive
  /-- Bundle an additive subgroup with typeclass assumptions of normality and finite index. -/]
/--
Definition of `ofSubgroup` / `ofSubgroup` 的定义

English:
definition ofSubgroup
  signature: (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  body: { toSubgroup := H }

@[to_additive (attr := simp)]

中文:
定义 ofSubgroup
  签名: (H : 子群 G) [H.正规] [H.FiniteIndex]
  定义体: { toSubgroup := H }

@[to_additive (attr := simp)]

Depends on / 依赖: toSubgroup
-/
def ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] : FiniteIndexNormalSubgroup G :=
  { toSubgroup := H }

@[to_additive (attr := simp)]
/--
theorem `toSubgroup_ofSubgroup` / 定理 `toSubgroup_ofSubgroup`

English:
theorem toSubgroup_ofSubgroup
  given: (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  proof: rfl

中文:
定理 toSubgroup_ofSubgroup
  条件: (H : 子群 G) [H.正规] [H.FiniteIndex]
  证明: rfl
-/
theorem toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] :
    ((ofSubgroup H : FiniteIndexNormalSubgroup G) : Subgroup G) = H :=
  rfl

section Comap

variable {H : Type*} {N : Type*} [Group H] [Group N]

/-- The preimage of a finite-index normal subgroup under a group homomorphism. -/
@[to_additive
  /-- The preimage of a finite-index normal additive subgroup under an additive homomorphism. -/]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : G ->* H) (K : FiniteIndexNormalSubgroup H)
  body: K.toSubgroup.comap f
  isFiniteIndex' := by
    let g : G ->* (H ⧸ K.toSubgroup) := (QuotientGroup.mk' K.toSubgroup).comp f
    have hker : K.toSubgroup.comap f = g.ker := by
      simpa using MonoidHom.comap_ker (g := QuotientGroup.mk' K.toSubgroup) (f := f)
    simpa [hker] using (inferInstance : 

中文:
定义 comap
  签名: (f : G ->* H) (K : FiniteIndexNormal子群 H)
  定义体: K.toSubgroup.comap f
  isFiniteIndex' := by
    let g : G ->* (H ⧸ K.toSubgroup) := (QuotientGroup.mk' K.toSubgroup).comp f
    have hker : K.toSubgroup.comap f = g.ker := by
      simpa using MonoidHom.comap_ker (g := QuotientGroup.mk' K.toSubgroup) (f := f)
    simpa [hker] using (inferInstance : 

Depends on / 依赖: K.toSubgroup.comap, toSubgroup
-/
def comap (f : G ->* H) (K : FiniteIndexNormalSubgroup H) : FiniteIndexNormalSubgroup G where
  toSubgroup := K.toSubgroup.comap f
  isFiniteIndex' := by
    let g : G ->* (H ⧸ K.toSubgroup) := (QuotientGroup.mk' K.toSubgroup).comp f
    have hker : K.toSubgroup.comap f = g.ker := by
      simpa using MonoidHom.comap_ker (g := QuotientGroup.mk' K.toSubgroup) (f := f)
    simpa [hker] using (inferInstance : g.ker.FiniteIndex)

@[to_additive (attr := simp)]
/--
theorem `toSubgroup_comap` / 定理 `toSubgroup_comap`

English:
theorem toSubgroup_comap
  given: (f : G ->* H) (K : FiniteIndexNormalSubgroup H)
  proof: rfl

@[to_additive (attr := gcongr)]

中文:
定理 toSubgroup_comap
  条件: (f : G ->* H) (K : FiniteIndexNormal子群 H)
  证明: rfl

@[to_additive (attr := gcongr)]
-/
theorem toSubgroup_comap (f : G ->* H) (K : FiniteIndexNormalSubgroup H) :
    ((comap f K : FiniteIndexNormalSubgroup G) : Subgroup G) = (K : Subgroup H).comap f :=
  rfl

@[to_additive (attr := gcongr)]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: (f : G ->* H) {K L : FiniteIndexNormalSubgroup H} (h : K <= L)
  proof: fun _ hx => h hx

@[to_additive (attr := simp)]

中文:
定理 comap_mono
  条件: (f : G ->* H) {K L : FiniteIndexNormal子群 H} (h : K <= L)
  证明: fun _ hx => h hx

@[to_additive (attr := simp)]
-/
theorem comap_mono (f : G ->* H) {K L : FiniteIndexNormalSubgroup H} (h : K <= L) :
    comap f K <= comap f L :=
  fun _ hx => h hx

@[to_additive (attr := simp)]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (K : FiniteIndexNormalSubgroup G)
  statement: comap (MonoidHom.id G) K = K
  proof: by
  rfl

@[to_additive (attr := simp)]

中文:
定理 comap_id
  条件: (K : FiniteIndexNormal子群 G)
  结论: comap (幺半群态射.id G) K = K
  证明: by
  rfl

@[to_additive (attr := simp)]
-/
theorem comap_id (K : FiniteIndexNormalSubgroup G) : comap (MonoidHom.id G) K = K := by
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (f : G ->* H) (g : H ->* N) (K : FiniteIndexNormalSubgroup N)
  proof: by
  rfl

中文:
定理 comap_comp
  条件: (f : G ->* H) (g : H ->* N) (K : FiniteIndexNormal子群 N)
  证明: by
  rfl
-/
theorem comap_comp (f : G ->* H) (g : H ->* N) (K : FiniteIndexNormalSubgroup N) :
    comap (g.comp f) K = comap f (comap g K) := by
  rfl

end Comap

end FiniteIndexNormalSubgroup

end
