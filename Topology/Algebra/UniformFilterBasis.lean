/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Uniform properties of neighborhood bases in topological algebra

This file contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/

@[expose] public section


open uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type*} [AddCommGroup G] (B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
@[instance_reducible]
/-
**AddGroupFilterBasis.uniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `AddGroupFilterBasi
s`。
形式化陈述：{G : Type u_1} → [inst : AddCommGroup G] → AddGroupFilterBasis G → Uniform
Space G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform space structure associated to an abelian group filter basis via the 
associated
topological abelian group structure.
-/
protected def uniformSpace : UniformSpace G :=
  @IsTopologicalAddGroup.rightUniformSpace G _ B.topology B.isTopologicalAddGroup

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
/-
**AddGroupFilterBasis.isUniformAddGroup** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupFilte
rBasis`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] (B : AddGroupFilterBasis G), IsUn
iformAddGroup G
参数：B : AddGroupFilterBasis G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G

--- 原说明 ---
The uniform space structure associated to an abelian group filter basis via the 
associated
topological abelian group structure is compatible with its group structure.
-/
protected theorem isUniformAddGroup : @IsUniformAddGroup G B.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup G _ B.topology B.isTopologicalAddGroup
/-
**AddGroupFilterBasis.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupFilterBasis`
。
形式化陈述：cauchy_iff {F : Filter G} : @Cauchy G B.uniformSpace F ↔ F.NeBot ∧ forall 
U in B, exists M in F, forallᵉ (x in M) (y in M), y - x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupFilterBasis.isUniformAddGroup`：∀ {G : Type u_1} [inst : AddCommG
roup G] (B : AddGroupFilterBasis G), IsUniformAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_zero`：∀ (Gᵣ : Type u_3) [inst : UniformSpace Gᵣ
] [inst_1 : AddGroup Gᵣ] [IsRightUniformAddGroup Gᵣ],   uniformity Gᵣ = Filter.c
omap (fun x => x.2 …
· 使用定理 `IsUniformAddGroup.isRightUniformAddGroup`：∀ (α : Type u_1) [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsRightUniformAddGroup α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `AddGroupFilterBasis.nhds_zero_hasBasis`：∀ {G : Type u} [inst : AddGroup 
G] (B : AddGroupFilterBasis G), (nhds 0).HasBasis (fun V => V ∈ B) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.uniformSpace F ↔
      F.NeBot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U := by
  let := B.uniformSpace
  have := B.isUniformAddGroup
  suffices F ×ˢ F ≤ uniformity G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_comm (_ ∈ _) G]

end AddGroupFilterBasis

