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
/-
**FiniteIndexNormalSubgroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：FiniteIndexNormalSubgroup (G : Type*) [Group G] extends Subgroup G where i
sNormal' : toSubgroup.Normal
参数：G : Type*。
继承自：Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of finite-index normal subgroups of a group.
-/
structure FiniteIndexNormalSubgroup (G : Type*) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance
  isFiniteIndex' : toSubgroup.FiniteIndex := by infer_instance

/-- The type of finite-index normal additive subgroups of an additive group. -/
@[ext]
/-
**FiniteIndexNormalAddSubgroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：FiniteIndexNormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup 
G where isNormal' : toAddSubgroup.Normal
参数：G : Type*。
继承自：AddSubgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of finite-index normal additive subgroups of an additive group.
-/
structure FiniteIndexNormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance
  isFiniteIndex' : toAddSubgroup.FiniteIndex := by infer_instance

attribute [to_additive] FiniteIndexNormalSubgroup

namespace FiniteIndexNormalSubgroup

variable {G : Type*} [Group G]

@[to_additive]
/-
**FiniteIndexNormalSubgroup.toSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fini
teIndexNormalSubgroup`。
形式化陈述：toSubgroup_injective : Function.Injective (fun H => H.toSubgroup : FiniteI
ndexNormalSubgroup G -> Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteIndexNormalSubgroup.ext`：∀ {G : Type u_1} {inst : Group G} {x y : 
FiniteIndexNormalSubgroup G}, x.carrier = y.carrier → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubgroup_injective : Function.Injective
    (fun H ↦ H.toSubgroup : FiniteIndexNormalSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  dsimp at h
  rw [h]

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (FiniteIndexNormalSubgroup G) G where
  coe U := U.1
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (FiniteIndexNormalSubgroup G) := .ofSetLike (FiniteIndexNormalSubgroup G) G

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (FiniteIndexNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (FiniteIndexNormalSubgroup G) (Subgroup G) where
  coe H := H.toSubgroup

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.FiniteIndex := H.isFiniteIndex'

@[to_additive]
/-
**FiniteIndexNormalSubgroup.instPartialOrderFiniteIndexNormalSubgroup** 是 Mathli
b 中的一个实例，位于命名空间 `FiniteIndexNormalSubgroup`。
形式化陈述：instPartialOrderFiniteIndexNormalSubgroup : PartialOrder (FiniteIndexNorma
lSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrderFiniteIndexNormalSubgroup : PartialOrder (FiniteIndexNormalSubgroup G) :=
  inferInstance

@[to_additive]
/-
**FiniteIndexNormalSubgroup.instInfFiniteIndexNormalSubgroup** 是 Mathlib 中的一个实例，
位于命名空间 `FiniteIndexNormalSubgroup`。
形式化陈述：instInfFiniteIndexNormalSubgroup : Min (FiniteIndexNormalSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfFiniteIndexNormalSubgroup : Min (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V ↦ {
    toSubgroup := U.toSubgroup ⊓ V.toSubgroup
    isNormal' := Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup
  }⟩

@[to_additive]
/-
**FiniteIndexNormalSubgroup.instSemilatticeInfFiniteIndexNormalSubgroup** 是 Math
lib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgroup`。
形式化陈述：instSemilatticeInfFiniteIndexNormalSubgroup : SemilatticeInf (FiniteIndexN
ormalSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInfFiniteIndexNormalSubgroup :
    SemilatticeInf (FiniteIndexNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V ↦ {
    toSubgroup := U.toSubgroup ⊔ V.toSubgroup
    isNormal' := Subgroup.sup_normal U.toSubgroup V.toSubgroup
    isFiniteIndex' := Subgroup.finiteIndex_of_le
      (H := U.toSubgroup) (K := U.toSubgroup ⊔ V.toSubgroup) le_sup_left
  }⟩

@[to_additive]
/-
**FiniteIndexNormalSubgroup.instSemilatticeSupFiniteIndexNormalSubgroup** 是 Math
lib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgroup`。
形式化陈述：instSemilatticeSupFiniteIndexNormalSubgroup : SemilatticeSup (FiniteIndexN
ormalSubgroup G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteIndexNormalSubgroup.toSubgroup_injective`：toSubgroup_injective : F
unction.Injective (fun H => H.toSubgroup : FiniteIndexNormalSubgroup G -> Subgro
up G)
-/
instance instSemilatticeSupFiniteIndexNormalSubgroup :
    SemilatticeSup (FiniteIndexNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**FiniteIndexNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteIndexNormalSubgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (FiniteIndexNormalSubgroup G) where

@[to_additive]
/-
**FiniteIndexNormalSubgroup.mem_toSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finite
IndexNormalSubgroup`。
形式化陈述：mem_toSubgroup_iff {H : FiniteIndexNormalSubgroup G} {g : G} : g in H.toSu
bgroup ↔ g in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubgroup_iff {H : FiniteIndexNormalSubgroup G} {g : G} : g ∈ H.toSubgroup ↔ g ∈ H :=
  .rfl

/-- Bundle a subgroup with typeclass assumptions of normality and finite index. -/
@[to_additive
  /-- Bundle an additive subgroup with typeclass assumptions of normality and finite index. -/]
/-
**FiniteIndexNormalSubgroup.ofSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `FiniteIndexNor
malSubgroup`。
形式化陈述：ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] : FiniteIndexNormal
Subgroup G
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] : FiniteIndexNormalSubgroup G :=
  { toSubgroup := H }

@[to_additive (attr := simp)]
/-
**FiniteIndexNormalSubgroup.toSubgroup_ofSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Fin
iteIndexNormalSubgroup`。
形式化陈述：toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] : ((ofSu
bgroup H : FiniteIndexNormalSubgroup G) : Subgroup G) = H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] :
    ((ofSubgroup H : FiniteIndexNormalSubgroup G) : Subgroup G) = H :=
  rfl

section Comap

variable {H : Type*} {N : Type*} [Group H] [Group N]

/-- The preimage of a finite-index normal subgroup under a group homomorphism. -/
@[to_additive
  /-- The preimage of a finite-index normal additive subgroup under an additive homomorphism. -/]
/-
**FiniteIndexNormalSubgroup.comap** 是 Mathlib 中的一个定义，位于命名空间 `FiniteIndexNormalSu
bgroup`。
形式化陈述：comap (f : G ->* H) (K : FiniteIndexNormalSubgroup H) : FiniteIndexNormalS
ubgroup G where toSubgroup
参数：f : G ->* H；K : FiniteIndexNormalSubgroup H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap (f : G →* H) (K : FiniteIndexNormalSubgroup H) : FiniteIndexNormalSubgroup G where
  toSubgroup := K.toSubgroup.comap f
  isFiniteIndex' := by
    let g : G →* (H ⧸ K.toSubgroup) := (QuotientGroup.mk' K.toSubgroup).comp f
    have hker : K.toSubgroup.comap f = g.ker := by
      simpa using MonoidHom.comap_ker (g := QuotientGroup.mk' K.toSubgroup) (f := f)
    simpa [hker] using (inferInstance : g.ker.FiniteIndex)

@[to_additive (attr := simp)]
/-
**FiniteIndexNormalSubgroup.toSubgroup_comap** 是 Mathlib 中的一个定理，位于命名空间 `FiniteIn
dexNormalSubgroup`。
形式化陈述：toSubgroup_comap (f : G ->* H) (K : FiniteIndexNormalSubgroup H) : ((comap
 f K : FiniteIndexNormalSubgroup G) : Subgroup G) = (K : Subgroup H).comap f
参数：f : G ->* H；K : FiniteIndexNormalSubgroup H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_comap (f : G →* H) (K : FiniteIndexNormalSubgroup H) :
    ((comap f K : FiniteIndexNormalSubgroup G) : Subgroup G) = (K : Subgroup H).comap f :=
  rfl

@[to_additive (attr := gcongr)]
/-
**FiniteIndexNormalSubgroup.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `FiniteIndexNor
malSubgroup`。
形式化陈述：comap_mono (f : G ->* H) {K L : FiniteIndexNormalSubgroup H} (h : K <= L) 
: comap f K <= comap f L
参数：f : G ->* H；h : K <= L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mono (f : G →* H) {K L : FiniteIndexNormalSubgroup H} (h : K ≤ L) :
    comap f K ≤ comap f L :=
  fun _ hx ↦ h hx

@[to_additive (attr := simp)]
/-
**FiniteIndexNormalSubgroup.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `FiniteIndexNorma
lSubgroup`。
形式化陈述：comap_id (K : FiniteIndexNormalSubgroup G) : comap (MonoidHom.id G) K = K
参数：K : FiniteIndexNormalSubgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (K : FiniteIndexNormalSubgroup G) : comap (MonoidHom.id G) K = K := by
  rfl

@[to_additive (attr := simp)]
/-
**FiniteIndexNormalSubgroup.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `FiniteIndexNor
malSubgroup`。
形式化陈述：comap_comp (f : G ->* H) (g : H ->* N) (K : FiniteIndexNormalSubgroup N) :
 comap (g.comp f) K = comap f (comap g K)
参数：f : G ->* H；g : H ->* N；K : FiniteIndexNormalSubgroup N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (f : G →* H) (g : H →* N) (K : FiniteIndexNormalSubgroup N) :
    comap (g.comp f) K = comap f (comap g K) := by
  rfl

end Comap

end FiniteIndexNormalSubgroup

end

