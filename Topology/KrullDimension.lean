/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Alessandro D'Angelo
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topologicalKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

@[expose] public section

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/--
The Krull dimension of a topological space is the supremum of lengths of chains of
closed irreducible sets.
-/
/-
**topologicalKrullDim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot Nat∞
参数：T : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Krull dimension of a topological space is the supremum of lengths of chains 
of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
### Main dimension theorems -/

/-- If `f : Y → X` is inducing, then `dim(Y) ≤ dim(X)`. -/
/-
**Topology.IsInducing.topologicalKrullDim_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.topologicalKrullDim_le {f : Y -> X} (hf : IsInducing f
) : topologicalKrullDim Y <= topologicalKrullDim X
参数：hf : IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用引理 `TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing`：map_st
rictMono_of_isInducing {f : β -> α} (hf : IsInducing f) : StrictMono (map f hf.c
ontinuous)

--- 原说明 ---
If `f : Y → X` is inducing, then `dim(Y) ≤ dim(X)`.
-/
theorem Topology.IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)

/-- The topological Krull dimension is invariant under homeomorphisms -/
/-
**IsHomeomorph.topologicalKrullDim_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHomeomorph.topologicalKrullDim_eq (f : X -> Y) (h : IsHomeomorph f) : to
pologicalKrullDim X = topologicalKrullDim Y
参数：f : X -> Y；h : IsHomeomorph f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.topologicalKrullDim_le`：Topology.IsInducing.topologi
calKrullDim_le {f : Y -> X} (hf : IsInducing f) : topologicalKrullDim Y <= topol
ogicalKrullDim X
· 使用引理 `IsHomeomorph.isInducing`：isInducing : IsInducing f
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
The topological Krull dimension is invariant under homeomorphisms
-/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  have fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    h.isInducing.topologicalKrullDim_le
  have bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    (h.homeomorph f).symm.isInducing.topologicalKrullDim_le
  le_antisymm fwd bwd

/-- The topological Krull dimension of any subspace is at most the dimension of the
ambient space. -/
/-
**topologicalKrullDim_subspace_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set 
X) : topologicalKrullDim Y <= topologicalKrullDim X
参数：X : Type*；Y : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.topologicalKrullDim_le`：Topology.IsInducing.topologi
calKrullDim_le {f : Y -> X} (hf : IsInducing f) : topologicalKrullDim Y <= topol
ogicalKrullDim X
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)

--- 原说明 ---
The topological Krull dimension of any subspace is at most the dimension of the
ambient space.
-/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  IsInducing.subtypeVal.topologicalKrullDim_le
/-
**topologicalKrullDim_zero_of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalKrullDim_zero_of_discreteTopology (X : Type*) [TopologicalSpace
 X] [DiscreteTopology X] : topologicalKrullDim X <= 0
参数：X : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Order.krullDim_nonpos_iff_forall_isMax`：krullDim_nonpos_iff_forall_isMax
 : krullDim α <= 0 ↔ forall x : α, IsMax x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
· 使用定理 `TopologicalSpace.IrreducibleCloseds.isIrreducible'`：∀ {α : Type u_4} [in
st : TopologicalSpace α] (self : TopologicalSpace.IrreducibleCloseds α), IsIrred
ucible self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsDiscrete.subsingleton_of_isPreirreducible`：IsDiscrete.subsingleton_of_
isPreirreducible (hs : IsDiscrete s) (hs' : IsPreirreducible s) : s.Subsingleton
· 使用引理 `DiscreteTopology.isDiscrete`：DiscreteTopology.isDiscrete [DiscreteTopolo
gy s] : IsDiscrete s
· 使用定理 `instDiscreteTopologySubtype`：∀ {X : Type u} {p : X → Prop} [inst : Topol
ogicalSpace X] [DiscreteTopology X], DiscreteTopology (Subtype p)
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
-/
theorem topologicalKrullDim_zero_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    topologicalKrullDim X ≤ 0 := by
  refine krullDim_nonpos_iff_forall_isMax.mpr fun Z Y h ↦ (h.antisymm' fun x hx ↦ ?_).le
  obtain ⟨z, hz⟩ := Z.2.nonempty
  rwa [DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible Y.2.isPreirreducible hx (h hz)]
/-
**Topology.IsOpenEmbedding.coheight_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.coheight_map {f : X -> Y} (hf : IsOpenEmbedding f
) (Z : TopologicalSpace.IrreducibleCloseds X) : Order.coheight (map f hf.continu
ous Z) = Order.coheight Z
参数：hf : IsOpenEmbedding f；Z : TopologicalSpace.IrreducibleCloseds X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_orderIso`：coheight_orderIso (f : α ≃o β) (x : α) : coheig
ht (f x) = coheight x
· 使用引理 `Order.coheight_eq_of_strictMono`：coheight_eq_of_strictMono (f : α -> β) 
(hf : StrictMono f) (h : forall a : α, forall b : β, f a < b -> exists (a' : α),
 a < a' ∧ f a' = b) (…
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Topology.IsOpenEmbedding.coheight_map {f : X → Y} (hf : IsOpenEmbedding f)
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Order.coheight (map f hf.continuous Z) = Order.coheight Z := by
  rw [← coheight_orderIso (orderIsoOfIsOpenEmbedding f hf) Z]
  refine .symm (coheight_eq_of_strictMono Subtype.val (Subtype.strictMono_coe _) ?_ _)
  intro a b hlt
  exact ⟨⟨b, a.2.mono (Set.preimage_mono hlt.le)⟩, hlt, rfl⟩

attribute [local instance] specializationOrder in
/-
**Topology.IsOpenEmbedding.coheight_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.coheight_eq [QuasiSober Y] [T0Space Y] [QuasiSobe
r X] [T0Space X] {x : X} (f : X -> Y) (hf : IsOpenEmbedding f) : coheight (f x) 
= coheight x
参数：f : X -> Y；hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Order.coheight_orderIso`：coheight_orderIso (f : α ≃o β) (x : α) : coheig
ht (f x) = coheight x
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用引理 `Topology.IsOpenEmbedding.coheight_map`：Topology.IsOpenEmbedding.coheight
_map {f : X -> Y} (hf : IsOpenEmbedding f) (Z : TopologicalSpace.IrreducibleClos
eds X) : Order.coheight (ma…
· 使用定理 `TopologicalSpace.IrreducibleCloseds.ext`：∀ {α : Type u_2} [inst : Topolo
gicalSpace α] {s t : TopologicalSpace.IrreducibleCloseds α}, ↑s = ↑t → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closure_image_closure`：closure_image_closure (h : Continuous f) : closur
e (f '' closure s) = closure (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Topology.IsOpenEmbedding.coheight_eq [QuasiSober Y] [T0Space Y] [QuasiSober X] [T0Space X]
    {x : X} (f : X → Y) (hf : IsOpenEmbedding f) : coheight (f x) = coheight x := by
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := Y)).symm (f x),
    ← coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x,
    ← Topology.IsOpenEmbedding.coheight_map hf]
  congr
  ext : 1
  simp [closure_image_closure hf.continuous]
