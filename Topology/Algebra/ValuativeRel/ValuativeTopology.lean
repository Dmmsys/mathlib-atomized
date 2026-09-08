/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# The topology on a ring induced by a valuation

In this file, we define the non-Archimedean topology induced by a valuation on a ring.

## Main definitions

* If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[IsValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
* `ValuativeRel.uniformSpace`: The uniform structure introduced by a `ValuativeRel`.

*NOTE* (2026-03-17): The `Valued` instance on a ring `R` would be
replaced by `[ValuativeRel R] [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R]`
(or `[ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]` when the uniformity is
not relevant). Additional input `(v : Valuation R Γ₀) [v.Compatible]` can be introduced whenever
a specific compatible valuation is chosen.

The canonical way to introduce the topological structure from a chosen valuation is:
1. First define the `ValuativeRel` structure using `ValuativeRel.ofValuation`;
2. Then define the `UniformSpace` structure using `ValuativeRel.uniformSpace`.
-/

public section

open scoped Topology Uniformity
open Set Filter Valuation ValuativeRel MonoidWithZeroHom ValueGroup₀ ValueGroupWithZero

noncomputable section

variable (R : Type*) [Ring R] [ValuativeRel R]

variable {R} in
/-
**Valuation.exists_setOfPred_restrict_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Valuation.exists_setOfPred_restrict_le_iff {Γ₀ : Type*} [LinearOrderedComm
GroupWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible] (x : R) (s : Set R) : (exi
sts γ : (ValueGroup₀ (.ofClass v))ˣ, {z | v.restrict (z - x) < γ.val} subseteq s
) ↔ exists γ : (ValueGroupWithZero R)ˣ, {a | valuation R (a - x) < γ} subseteq s
参数：v : Valuation R Γ₀；x : R；s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Valuation.exists_setOfPred_restrict_le_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (s : Set R) :
    (∃ γ : (ValueGroup₀ (.ofClass v))ˣ, {z | v.restrict (z - x) < γ.val} ⊆ s) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, {a | valuation R (a - x) < γ} ⊆ s := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r.mapEquiv (orderMonoidIso v).symm, ?_⟩,
    fun ⟨r, hr⟩ ↦ ⟨r.mapEquiv (orderMonoidIso v), ?_⟩⟩
  all_goals convert! hr; simp

@[deprecated (since := "2026-07-09")]
alias Valuation.exists_setOf_restrict_le_iff := Valuation.exists_setOfPred_restrict_le_iff

/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the valuative relation `· ≤ᵥ ·`. -/
/-
**IsValuativeTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [inst : Ring R] → [ValuativeRel R] → [TopologicalSpace R]
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the valuative relation `· ≤ᵥ ·`.
-/
class IsValuativeTopology [TopologicalSpace R] where
  mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 (x : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } ⊆ s

namespace ValuativeRel

/-- The topology induced by a valuative relation. Note that this is not made into a global instance
to avoid diamonds. If desired, one can equip a ring with a topological space from a valuative
relation by hand. But as long as they do so, the fact that the topology is valuative and
nonarchemidean can be automatically inferred. -/
local instance topologicalSpace : TopologicalSpace R := (valuation R).subgroups_basis.topology

/-
**ValuativeRel.nonarchimedeanRing** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
形式化陈述：nonarchimedeanRing : NonarchimedeanRing R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingSubgroupsBasis.nonarchimedean`：nonarchimedean : @NonarchimedeanRing 
A _ hB.topology
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
-/
instance nonarchimedeanRing : NonarchimedeanRing R :=
  (valuation R).subgroups_basis.nonarchimedean
/-
**ValuativeRel.isValuativeTopology** 是 Mathlib 中的一个实例，位于命名空间 `ValuativeRel`。
形式化陈述：isValuativeTopology : IsValuativeTopology R where mem_nhds_iff {s x}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.hasBasis_iff`：hasBasis_iff : l.HasBasis p s ↔ forall t, t in l ↔ 
exists i, p i ∧ s i subseteq t
· 使用定理 `RingSubgroupsBasis.hasBasis_nhds`：hasBasis_nhds (a : A) : HasBasis (@nhd
s A hB.topology a) (fun _ => True) fun i => { b | b - a in B i }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.exists_setOfPred_restrict_le_iff`：Valuation.exists_setOfPred_r
estrict_le_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R
 Γ₀) [v.Compatible] (x : R) (s :…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance isValuativeTopology : IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    rw [Filter.hasBasis_iff.mp ((valuation R).subgroups_basis.hasBasis_nhds x) s]
    simp [neg_add_eq_sub, ← (valuation R).exists_setOfPred_restrict_le_iff,
      ← restrict_lt_iff_lt_embedding]

/-- The uniform structure induced by a valuative relation. Note that this is not made into a
global instance to avoid diamonds. If desired, one can equip a ring with a uniform space
from a valuative relation by hand. But as long as they do so, the fact that the topology is
valuative and nonarchimedean, and the addition is uniformly continuous,
can be automatically inferred. -/
local instance uniformSpace : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R

/-- This is not made into a global instance to avoid diamonds. -/
local instance isUniformAddGroup : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup

end ValuativeRel

variable {R}

variable {K : Type*} [DivisionRing K] [ValuativeRel K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀]

section TopologicalSpace

variable [TopologicalSpace R] (v : Valuation R Γ₀) [v.Compatible]
namespace IsValuativeTopology

/-- If the neighborhoods of every point for a given topology are defined by a valuation `v`
compatible with the valuative relation, then the topology is a valuative topology. -/
/-
**IsValuativeTopology.of_mem_nhds_iff_vle** 是 Mathlib 中的一个定理，位于命名空间 `IsValuative
Topology`。
形式化陈述：of_mem_nhds_iff_vle (H : forall {s : Set R} {x : R}, s in 𝓝 x ↔ exists (γ 
: (ValueGroup₀ (.ofClass v))ˣ), {z : R | v.restrict (z - x) < γ} subseteq s) : I
sValuativeTopology R
参数：H : forall {s : Set R} {x : R}, s in 𝓝 x ↔ exists (γ : (ValueGroup₀ (.ofClass
 v))ˣ), {z : R | v.restrict (z - x) < γ} subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
If the neighborhoods of every point for a given topology are defined by a valuat
ion `v`
compatible with the valuative relation, then the topology is a valuative topolog
y.
-/
theorem of_mem_nhds_iff_vle (H : ∀ {s : Set R} {x : R}, s ∈ 𝓝 x ↔
    ∃ (γ : (ValueGroup₀ (.ofClass v))ˣ), {z : R | v.restrict (z - x) < γ} ⊆ s) :
    IsValuativeTopology R := by
  constructor
  refine fun {s x} ↦ ⟨fun h_mem ↦ ?_, fun ⟨γ, hγ⟩ ↦
    H.mpr ⟨.mk0 ((orderMonoidIso v) γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩⟩
  obtain ⟨γ, hγ⟩ := H.mp h_mem
  exact ⟨.mk0 ((orderMonoidIso v).symm γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩

open scoped Pointwise in
/-- In a topological group, if the neighborhoods of zero are defined by a valuation `v` compatible
with the valuative relation, then the underlying topology is valuative. -/
/-
**IsValuativeTopology.of_mem_nhds_zero_iff_vle** 是 Mathlib 中的一个定理，位于命名空间 `IsValu
ativeTopology`。
形式化陈述：of_mem_nhds_zero_iff_vle [IsTopologicalAddGroup R] (H : forall {s : Set R}
, s in 𝓝 0 ↔ exists (γ : (ValueGroup₀ (.ofClass v))ˣ), {z : R | v.restrict z < γ
} subseteq s) : IsValuativeTopology R
参数：H : forall {s : Set R}, s in 𝓝 0 ↔ exists (γ : (ValueGroup₀ (.ofClass v))ˣ), 
{z : R | v.restrict z < γ} subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsValuativeTopology.of_mem_nhds_iff_vle`：of_mem_nhds_iff_vle (H : forall
 {s : Set R} {x : R}, s in 𝓝 x ↔ exists (γ : (ValueGroup₀ (.ofClass v))ˣ), {z : 
R | v.restrict (z - x) < γ} s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_mem_nhds_vadd_iff`：∀ {α : Type u_2} {G : Type u_4} [inst : Topologi
calSpace α] [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [ContinuousConstVAd
d G α] {t : …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a

--- 原说明 ---
In a topological group, if the neighborhoods of zero are defined by a valuation 
`v` compatible
with the valuative relation, then the underlying topology is valuative.
-/
theorem of_mem_nhds_zero_iff_vle [IsTopologicalAddGroup R]
    (H : ∀ {s : Set R}, s ∈ 𝓝 0 ↔ ∃ (γ : (ValueGroup₀ (.ofClass v))ˣ),
    {z : R | v.restrict z < γ} ⊆ s) : IsValuativeTopology R := by
  apply of_mem_nhds_iff_vle v (fun {s x} ↦ ?_)
  rw [← vadd_mem_nhds_vadd_iff (g := -x)]
  simp only [vadd_eq_add, neg_add_cancel, H, subset_vadd_set_iff, neg_neg]
  suffices ∀ (γ : (ValueGroup₀ (.ofClass v))ˣ), (x +ᵥ {z | v.restrict z < ↑γ}) =
    {a | v.restrict (-x + a) < ↑γ} by simp_all [neg_add_eq_sub]
  simp [Set.ext_iff, mem_vadd_set_iff_neg_vadd_mem]

variable [IsValuativeTopology R]

/-- A variant of `IsValuativeTopology.mem_nhds_iff` using subtraction. -/
/-
**IsValuativeTopology.mem_nhds_iff'** 是 Mathlib 中的一个引理，位于命名空间 `IsValuativeTopolo
gy`。
形式化陈述：mem_nhds_iff' {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (ValueGroupWithZ
ero R)ˣ, { z | valuation R (z - x) < γ } subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsValuativeTopology.mem_nhds_iff`：∀ {R : Type u_1} {inst : Ring R} {inst
_1 : ValuativeRel R} {inst_2 : TopologicalSpace R} [self : IsValuativeTopology R
]   {s : Set R} {x : R…

--- 原说明 ---
A variant of `IsValuativeTopology.mem_nhds_iff` using subtraction.
-/
lemma mem_nhds_iff' {s : Set R} {x : R} :
    s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { z | valuation R (z - x) < γ } ⊆ s := by
  convert! mem_nhds_iff (s := s) using 4
  simp [neg_add_eq_sub]
/-
**IsValuativeTopology.mem_nhds_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsValuativeTo
pology`。
形式化陈述：mem_nhds_zero_iff (s : Set R) : s in 𝓝 0 ↔ exists γ : (ValueGroupWithZero 
R)ˣ, { x | valuation R x < γ } subseteq s
参数：s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_nhds_zero_iff (s : Set R) :
    s ∈ 𝓝 0 ↔ ∃ γ : (ValueGroupWithZero R)ˣ, { x | valuation R x < γ } ⊆ s := by
  simp [mem_nhds_iff']
/-
**IsValuativeTopology.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 `IsValuativeTopolo
gy`。
形式化陈述：hasBasis_nhds (x : R) : (𝓝 x).HasBasis (fun _ => True) fun γ : (ValueGroup
WithZero R)ˣ => { z | valuation R (z - x) < γ }
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { z | valuation R (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

/-- A variant of `hasBasis_nhds` where `· ≠ 0` is unbundled. -/
/-
**IsValuativeTopology.hasBasis_nhds'** 是 Mathlib 中的一个引理，位于命名空间 `IsValuativeTopol
ogy`。
形式化陈述：hasBasis_nhds' (x : R) : (𝓝 x).HasBasis (· != 0) ({ y | valuation R (y - x
) < · })
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `IsValuativeTopology.hasBasis_nhds`：hasBasis_nhds (x : R) : (𝓝 x).HasBasi
s (fun _ => True) fun γ : (ValueGroupWithZero R)ˣ => { z | valuation R (z - x) <
 γ }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A variant of `hasBasis_nhds` where `· ≠ 0` is unbundled.
-/
lemma hasBasis_nhds' (x : R) :
    (𝓝 x).HasBasis (· ≠ 0) ({ y | valuation R (y - x) < · }) :=
  (hasBasis_nhds x).to_hasBasis (fun γ _ ↦ ⟨γ, by simp⟩)
    fun γ hγ ↦ ⟨.mk0 γ hγ, by simp⟩

variable (R) in
/-
**IsValuativeTopology.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsValuativeT
opology`。
形式化陈述：hasBasis_nhds_zero : (𝓝 0).HasBasis (fun _ => True) fun γ : (ValueGroupWit
hZero R)ˣ => { x | valuation R x < γ }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsValuativeTopology.hasBasis_nhds`：hasBasis_nhds (x : R) : (𝓝 x).HasBasi
s (fun _ => True) fun γ : (ValueGroupWithZero R)ˣ => { z | valuation R (z - x) <
 γ }
-/
theorem hasBasis_nhds_zero :
    (𝓝 0).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroupWithZero R)ˣ ↦ { x | valuation R x < γ } := by
  convert! hasBasis_nhds (0 : R)
  rw [sub_zero]

variable (R) in
/-- A variant of `hasBasis_nhds_zero` where `· ≠ 0` is unbundled. -/
/-
**IsValuativeTopology.hasBasis_nhds_zero'** 是 Mathlib 中的一个引理，位于命名空间 `IsValuative
Topology`。
形式化陈述：hasBasis_nhds_zero' : (𝓝 0).HasBasis (· != 0) ({ x | valuation R x < · })
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `IsValuativeTopology.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 0).HasBa
sis (fun _ => True) fun γ : (ValueGroupWithZero R)ˣ => { x | valuation R x < γ }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A variant of `hasBasis_nhds_zero` where `· ≠ 0` is unbundled.
-/
lemma hasBasis_nhds_zero' :
    (𝓝 0).HasBasis (· ≠ 0) ({ x | valuation R x < · }) :=
  (hasBasis_nhds_zero R).to_hasBasis (fun γ _ ↦ ⟨γ, by simp⟩)
    fun γ hγ ↦ ⟨.mk0 γ hγ, by simp⟩

end IsValuativeTopology

open IsValuativeTopology

variable [IsValuativeTopology R]

namespace Valuation

/-
**Valuation.mem_nhds_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ exists γ : (ValueGroup₀ (.of
Class v))ˣ, { z | v.restrict (z - x) < γ.val } subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用引理 `Valuation.exists_setOfPred_restrict_le_iff`：Valuation.exists_setOfPred_r
estrict_le_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R
 Γ₀) [v.Compatible] (x : R) (s :…
· 使用定理 `IsValuativeTopology.mem_nhds_iff`：∀ {R : Type u_1} {inst : Ring R} {inst
_1 : ValuativeRel R} {inst_2 : TopologicalSpace R} [self : IsValuativeTopology R
]   {s : Set R} {x : R…
-/
lemma mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 x ↔
    ∃ γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } ⊆ s := by
  convert! IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOfPred_restrict_le_iff _ _
/-
**Valuation.mem_nhds_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_nhds_zero_iff (s : Set R) : s in 𝓝 0 ↔ exists γ : (ValueGroup₀ (.ofCla
ss v))ˣ, { x | v.restrict x < γ.val } subseteq s
参数：s : Set R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 0 ↔
    ∃ γ : (ValueGroup₀ (.ofClass v))ˣ, { x | v.restrict x < γ.val } ⊆ s := by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff
/-
**Valuation.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：hasBasis_nhds (x : R) : (𝓝 x).HasBasis (fun _ => True) fun γ : (ValueGroup
₀ (.ofClass v))ˣ => { z | v.restrict (z - x) < γ.val }
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroup₀ (.ofClass v))ˣ ↦ { z | v.restrict (z - x) < γ.val } := by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]
/-
**Valuation.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : (ValueGr
oup₀ (.ofClass v))ˣ => { x | v.restrict x < γ.val }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.is_topological_valuation`：∀ {R : Type u_1} [inst : Ring R] [in
st_1 : ValuativeRel R] {Γ₀ : Type u_3} [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀]   [inst_3 : Topologi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroup₀ (.ofClass v))ˣ ↦ { x | v.restrict x < γ.val } := by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

set_option backward.isDefEq.respectTransparency.types false in
/-- The set `{ y : R | v y = v x }` is a neighbourhood of `x`.
This does not imply that `v` is locally constant everywhere (since `v ⁻¹' {0}` is not open),
but it is equivalent to the restriction of `v` to the complement of its support being
locally constant. -/
/-
**Valuation.locally_const** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：locally_const {x : R} (h : (v x : Γ₀) != 0) : { y : R | v y = v x } in 𝓝 x
参数：h : (v x : Γ₀) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Valuation.map_eq_of_sub_lt`：map_eq_of_sub_lt (h : v (y - x) < v x) : v y
 = v x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.restrict_lt_iff`：restrict_lt_iff {x y : R} : v.restrict x < v.
restrict y ↔ v x < v y

--- 原说明 ---
The set `{ y : R | v y = v x }` is a neighbourhood of `x`.
This does not imply that `v` is locally constant everywhere (since `v ⁻¹' {0}` i
s not open),
but it is equivalent to the restriction of `v` to the complement of its support 
being
locally constant.
-/
theorem locally_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [v.mem_nhds_iff]
  have h' : v.restrict x ≠ 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

end Valuation

namespace IsValuativeTopology

variable (R) in
/-
**IsValuativeTopology.** 是 Mathlib 中的一个实例，位于命名空间 `IsValuativeTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : IsTopologicalAddGroup R := by
  have cts_add : ContinuousConstVAdd R R :=
    ⟨fun x ↦ continuous_iff_continuousAt.2 fun z ↦
      (((valuation R).hasBasis_nhds z).tendsto_iff ((valuation R).hasBasis_nhds (x + z))).2
        fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩⟩
  have basis := (valuation R).hasBasis_nhds_zero
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ ↦ (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ ↦
      ⟨γ, trivial, fun ⟨_, _⟩ hx ↦ (valuation R).restrict.map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ ↦ ⟨γ, trivial, fun y hy ↦ by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (cts_add.1 x₀).continuousAt (x := 0)
  · simpa [ContinuousAt] using (cts_add.1 (-x₀)).continuousAt (x := x₀)

end IsValuativeTopology

end TopologicalSpace

namespace Valuation

section UniformSpace

variable [_u : UniformSpace R] [IsUniformAddGroup R] [IsValuativeTopology R] (v : Valuation R Γ₀)
  [v.Compatible]

/-
**Valuation.hasBasis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True) fun γ : (ValueGroup₀ 
(.ofClass v))ˣ => { p : R × R | v.restrict (p.2 - p.1) < γ.1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_comap_nhds_zero`：∀ (Gᵣ : Type u_3) [inst : UniformSpace Gᵣ
] [inst_1 : AddGroup Gᵣ] [IsRightUniformAddGroup Gᵣ],   uniformity Gᵣ = Filter.c
omap (fun x => x.2 …
· 使用定理 `IsUniformAddGroup.isRightUniformAddGroup`：∀ (α : Type u_1) [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsRightUniformAddGroup α
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Valuation.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis 
(fun _ => True) fun γ : (ValueGroup₀ (.ofClass v))ˣ => { x | v.restrict x < γ.va
l }
-/
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ ↦ True)
    fun γ : (ValueGroup₀ (.ofClass v))ˣ ↦
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _
/-
**Valuation.toUniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：toUniformSpace_eq : _u = @IsTopologicalAddGroup.rightUniformSpace R _ v.su
bgroups_basis.topology _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Valuation.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 R).HasBasis (fun
 _ => True) fun γ : (ValueGroup₀ (.ofClass v))ˣ => { p : R × R | v.restrict (p.2
 - p.1) < γ.1 }
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.coe_ltAddSubgroup`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ri
ng R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   (γ : Γ
₀ˣ), ↑(v.ltAddSub…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `RingSubgroupsBasis.hasBasis_nhds_zero`：hasBasis_nhds_zero : HasBasis (@n
hds A hB.topology 0) (fun _ => True) fun i => B i
-/
theorem toUniformSpace_eq : _u =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
/-
**Valuation.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：cauchy_iff {F : Filter R} : Cauchy F ↔ F.NeBot ∧ forall γ : (MonoidWithZer
oHom.ValueGroup₀ (.ofClass v))ˣ, exists M in F, forallᵉ (x in M) (y in M), v.res
trict (y - x) < γ.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.toUniformSpace_eq`：toUniformSpace_eq : _u = @IsTopologicalAddG
roup.rightUniformSpace R _ v.subgroups_basis.topology _
· 使用定理 `AddGroupFilterBasis.cauchy_iff`：cauchy_iff {F : Filter G} : @Cauchy G B.
uniformSpace F ↔ F.NeBot ∧ forall U in B, exists M in F, forallᵉ (x in M) (y in 
M), y - x in U
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingSubgroupsBasis.mem_addGroupFilterBasis_iff`：mem_addGroupFilterBasis_
iff {V : Set A} : V in hB.toRingFilterBasis.toAddGroupFilterBasis ↔ exists i, V 
= B i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingSubgroupsBasis.mem_addGroupFilterBasis`：mem_addGroupFilterBasis (i) 
: (B i : Set A) in hB.toRingFilterBasis.toAddGroupFilterBasis
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ,
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), v.restrict (y - x) < γ.1 := by
  rw [v.toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

end UniformSpace

section TopologicalSpace

variable [_t : TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]
  [TopologicalSpace K] [IsValuativeTopology K]

/-
**Valuation.toTopologicalSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：toTopologicalSpace_eq : _t = v.subgroups_basis.topology
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsValuativeTopology.instIsTopologicalAddGroup`：∀ (R : Type u_1) [inst : 
Ring R] [inst_1 : ValuativeRel R] [inst_2 : TopologicalSpace R] [IsValuativeTopo
logy R],   IsTopologicalAddGroup R
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.subgroups_basis`：subgroups_basis : RingSubgroupsBasis fun γ : 
(ValueGroup₀ (.ofClass v))ˣ => v.ltAddSubgroup Units.map (ValueGroup₀.embedding 
(f
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `Valuation.toUniformSpace_eq`：toUniformSpace_eq : _u = @IsTopologicalAddG
roup.rightUniformSpace R _ v.subgroups_basis.topology _
-/
theorem toTopologicalSpace_eq :
    _t = v.subgroups_basis.topology := by
  let u := IsTopologicalAddGroup.rightUniformSpace R
  let := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u ↦ @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) _root_.IsValuativeTopology.isTopologicalRing : IsTopologicalRing R := by
  convert! (ValuativeRel.nonarchimedeanRing R).toIsTopologicalRing
  exact toTopologicalSpace_eq _

section Discrete

/-
**Valuation.discreteTopology_of_forall_map_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Val
uation`。
形式化陈述：discreteTopology_of_forall_map_eq_one (h : forall x : R, x != 0 -> v x = 1
) : DiscreteTopology R
参数：h : forall x : R, x != 0 -> v x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsValuativeTopology.isTopologicalRing`：∀ {R : Type u_1} [inst : Ring R] 
[inst_1 : ValuativeRel R] [_t : TopologicalSpace R] [IsValuativeTopology R],   I
sTopologicalRing R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Valuation.mem_nhds_zero_iff`：mem_nhds_zero_iff (s : Set R) : s in 𝓝 0 ↔ 
exists γ : (ValueGroup₀ (.ofClass v))ˣ, { x | v.restrict x < γ.val } subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
-/
lemma discreteTopology_of_forall_map_eq_one (h : ∀ x : R, x ≠ 0 → v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, v.mem_nhds_zero_iff, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding, Units.val_one, map_one] at hx
  exact ⟨x, hx', hx.ne⟩
/-
**Valuation.discreteTopology_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：discreteTopology_of_forall_lt [MulArchimedean Γ₀] (v : Valuation K Γ₀) [v.
Compatible] {r : Γ₀} (hr : r != 0) (h : forall x : K, v x != 0 -> r < v x) : Dis
creteTopology K
参数：v : Valuation K Γ₀；hr : r != 0；h : forall x : K, v x != 0 -> r < v x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.discreteTopology_of_forall_map_eq_one`：discreteTopology_of_for
all_map_eq_one (h : forall x : R, x != 0 -> v x = 1) : DiscreteTopology R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.map_eq_one_of_forall_lt`：map_eq_one_of_forall_lt [MulArchimede
an Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r != 0) (h : forall x : K, v x != 0 -
> r < v x) (x : K) (hx …
-/
lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] (v : Valuation K Γ₀)
    [v.Compatible] {r : Γ₀} (hr : r ≠ 0) (h : ∀ x : K, v x ≠ 0 → r < v x) :
    DiscreteTopology K :=
  v.discreteTopology_of_forall_map_eq_one (by simpa using v.map_eq_one_of_forall_lt hr h)

end Discrete

variable {v}

/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is open in the valuative topology. -/
/-
**Valuation.isOpen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isOpen_ball (r : ValueGroup₀ (.ofClass v)) : IsOpen {x | v.restrict x < r}
参数：r : ValueGroup₀ (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the open `r
`-ball
around zero `{x | v.restrict x < r}` is open in the valuative topology.
-/
theorem isOpen_ball (r : ValueGroup₀ (.ofClass v)) : IsOpen {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy ↦ (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is closed in the valuative topology. -/
/-
**Valuation.isClosed_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClosed_ball (r : ValueGroup₀ (.ofClass v)) : IsClosed {x | v.restrict x 
< r}
参数：r : ValueGroup₀ (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.isClosed_of_isOpen`：∀ {G : Type u_1} [inst : AddGroup G] [in
st_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (U : AddSubgroup G),   Is
Open ↑U → IsClosed ↑…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsValuativeTopology.isTopologicalRing`：∀ {R : Type u_1} [inst : Ring R] 
[inst_1 : ValuativeRel R] [_t : TopologicalSpace R] [IsValuativeTopology R],   I
sTopologicalRing R
· 使用定理 `Valuation.isOpen_ball`：isOpen_ball (r : ValueGroup₀ (.ofClass v)) : IsOp
en {x | v.restrict x < r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the open `r
`-ball
around zero `{x | v.restrict x < r}` is closed in the valuative topology.
-/
theorem isClosed_ball (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

/-- For any valuation `v` compatible with the valuative relation on `R`, the open `r`-ball
around zero `{x | v.restrict x < r}` is clopen in the valuative topology. -/
/-
**Valuation.isClopen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClopen_ball (r : ValueGroup₀ (.ofClass v)) : IsClopen {x | v.restrict x 
< r}
参数：r : ValueGroup₀ (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.isClosed_ball`：isClosed_ball (r : ValueGroup₀ (.ofClass v)) : 
IsClosed {x | v.restrict x < r}
· 使用定理 `Valuation.isOpen_ball`：isOpen_ball (r : ValueGroup₀ (.ofClass v)) : IsOp
en {x | v.restrict x < r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the open `r
`-ball
around zero `{x | v.restrict x < r}` is clopen in the valuative topology.
-/
theorem isClopen_ball (r : ValueGroup₀ (.ofClass v)) :
    IsClopen {x | v.restrict x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is open in the valuative topology. -/
/-
**Valuation.isOpen_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isOpen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) : IsOpen {x
 | v.restrict x <= r}
参数：.ofClass v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
`r`-ball
around zero `{x | v.restrict x ≤ r}` is open in the valuative topology.
-/
theorem isOpen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r ≠ 0) :
  IsOpen {x | v.restrict x ≤ r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [v.mem_nhds_iff, ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy ↦
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is closed in the valuative topology. -/
/-
**Valuation.isClosed_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClosed_closedBall (r : ValueGroup₀ (.ofClass v)) : IsClosed {x | v.restr
ict x <= r}
参数：r : ValueGroup₀ (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用引理 `Valuation.mem_nhds_iff`：mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔ ex
ists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subsete
q s
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Valuation.map_sub_eq_of_lt_left`：map_sub_eq_of_lt_left (h : v y < v x) :
 v (x - y) = v x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
`r`-ball
around zero `{x | v.restrict x ≤ r}` is closed in the valuative topology.
-/
theorem isClosed_closedBall (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x ≠ 0 := hx.ne_zero
  exact ⟨Units.mk0 _ hx', fun y hy hy' ↦ ne_of_lt hy <| map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed `r`-ball
around zero `{x | v.restrict x ≤ r}` is clopen in the valuative topology. -/
/-
**Valuation.isClopen_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClopen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) : IsClope
n {x | v.restrict x <= r}
参数：.ofClass v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.of
Class v)) : IsClosed {x | v.restrict x <= r}
· 使用定理 `Valuation.isOpen_closedBall`：isOpen_closedBall {r : ValueGroup₀ (.ofClas
s v)} (hr : r != 0) : IsOpen {x | v.restrict x <= r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
`r`-ball
around zero `{x | v.restrict x ≤ r}` is clopen in the valuative topology.
-/
theorem isClopen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r ≠ 0) :
    IsClopen {x | v.restrict x ≤ r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is clopen in the valuative topology. -/
/-
**Valuation.isClopen_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClopen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) : IsClopen {x
 | v.restrict x = r}
参数：.ofClass v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClopen.diff`：IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClo
pen (s \ t)
· 使用定理 `Valuation.isClopen_closedBall`：isClopen_closedBall {r : ValueGroup₀ (.of
Class v)} (hr : r != 0) : IsClopen {x | v.restrict x <= r}
· 使用定理 `Valuation.isClopen_ball`：isClopen_ball (r : ValueGroup₀ (.ofClass v)) : 
IsClopen {x | v.restrict x < r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the sphere 
of radius `r`
around zero `{x | v.restrict x = r}` is clopen in the valuative topology.
-/
theorem isClopen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r ≠ 0) :
    IsClopen {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x ≤ r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is open in the valuative topology. -/
/-
**Valuation.isOpen_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isOpen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) : IsOpen {x | v
.restrict x = r}
参数：.ofClass v；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Valuation.isClopen_sphere`：isClopen_sphere {r : ValueGroup₀ (.ofClass v)
} (hr : r != 0) : IsClopen {x | v.restrict x = r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the sphere 
of radius `r`
around zero `{x | v.restrict x = r}` is open in the valuative topology.
-/
theorem isOpen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r ≠ 0) :
    IsOpen {x | v.restrict x = r} :=
  isClopen_sphere hr |>.isOpen

/-- For any valuation `v` compatible with the valuative relation on `R`, the sphere of radius `r`
around zero `{x | v.restrict x = r}` is closed in the valuative topology. -/
/-
**Valuation.isClosed_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClosed_sphere (r : ValueGroup₀ (.ofClass v)) : IsClosed {x | v.restrict 
x = r}
参数：r : ValueGroup₀ (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Valuation.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.of
Class v)) : IsClosed {x | v.restrict x <= r}
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `Valuation.isClopen_sphere`：isClopen_sphere {r : ValueGroup₀ (.ofClass v)
} (hr : r != 0) : IsClopen {x | v.restrict x = r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the sphere 
of radius `r`
around zero `{x | v.restrict x = r}` is closed in the valuative topology.
-/
theorem isClosed_sphere (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · convert! v.isClosed_closedBall 0 using 3
    simp
  exact isClopen_sphere hr |>.isClosed

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is open in the valuative topology. -/
/-
**Valuation.isOpen_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isOpen_integer : IsOpen (v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Subsemiring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocSemiring R] (t
oSubmonoid toSubmonoid_1 : Submonoid R)   (e_toSubmonoid : toSubmonoid = toSubmo
noid_1)   (add_…
· 使用定理 `Subring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (toSubsemi
ring toSubsemiring_1 : Subsemiring R)   (e_toSubsemiring : toSubsemiring = toSub
semiring_1)…
· 使用定理 `Valuation.isOpen_closedBall`：isOpen_closedBall {r : ValueGroup₀ (.ofClas
s v)} (hr : r != 0) : IsOpen {x | v.restrict x <= r}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
unit ball
around zero `{x | v x ≤ 1}` is open in the valuative topology.
-/
theorem isOpen_integer : IsOpen (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is closed in the valuative topology. -/
/-
**Valuation.isClosed_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClosed_integer : IsClosed (v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Subsemiring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocSemiring R] (t
oSubmonoid toSubmonoid_1 : Submonoid R)   (e_toSubmonoid : toSubmonoid = toSubmo
noid_1)   (add_…
· 使用定理 `Subring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (toSubsemi
ring toSubsemiring_1 : Subsemiring R)   (e_toSubsemiring : toSubsemiring = toSub
semiring_1)…
· 使用定理 `Valuation.isClosed_closedBall`：isClosed_closedBall (r : ValueGroup₀ (.of
Class v)) : IsClosed {x | v.restrict x <= r}

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
unit ball
around zero `{x | v x ≤ 1}` is closed in the valuative topology.
-/
theorem isClosed_integer : IsClosed (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

/-- For any valuation `v` compatible with the valuative relation on `R`, the closed unit ball
around zero `{x | v x ≤ 1}` is clopen in the valuative topology. -/
/-
**Valuation.isClopen_integer** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClopen_integer : IsClopen (v.integer : Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isClosed_integer`：isClosed_integer : IsClosed (v.integer : Set
 R)
· 使用定理 `Valuation.isOpen_integer`：isOpen_integer : IsOpen (v.integer : Set R)

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on `R`, the closed 
unit ball
around zero `{x | v x ≤ 1}` is clopen in the valuative topology.
-/
theorem isClopen_integer : IsClopen (v.integer : Set R) :=
  ⟨isClosed_integer, isOpen_integer⟩

section Field

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is open in the valuative topology. -/
/-
**Valuation.isOpen_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isOpen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] : IsOpen (v.va
luationSubring : Set K)
参数：v : Valuation K Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isOpen_integer`：isOpen_integer : IsOpen (v.integer : Set R)

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on a field `K`, the
 valuation
subring defined by `v` is open in the valuative topology.
-/
theorem isOpen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsOpen (v.valuationSubring : Set K) :=
  isOpen_integer

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is closed in the valuative topology. -/
/-
**Valuation.isClosed_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClosed_valuationSubring (v : Valuation K Γ₀) [v.Compatible] : IsClosed (
v.valuationSubring : Set K)
参数：v : Valuation K Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isClosed_integer`：isClosed_integer : IsClosed (v.integer : Set
 R)

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on a field `K`, the
 valuation
subring defined by `v` is closed in the valuative topology.
-/
theorem isClosed_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClosed (v.valuationSubring : Set K) :=
  isClosed_integer

/-- For any valuation `v` compatible with the valuative relation on a field `K`, the valuation
subring defined by `v` is clopen in the valuative topology. -/
/-
**Valuation.isClopen_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isClopen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] : IsClopen (
v.valuationSubring : Set K)
参数：v : Valuation K Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isClopen_integer`：isClopen_integer : IsClopen (v.integer : Set
 R)

--- 原说明 ---
For any valuation `v` compatible with the valuative relation on a field `K`, the
 valuation
subring defined by `v` is clopen in the valuative topology.
-/
theorem isClopen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClopen (v.valuationSubring : Set K) :=
  isClopen_integer

end Field

end TopologicalSpace

end Valuation

namespace IsValuativeTopology

@[deprecated (since := "2026-03-17")] alias isOpen_ball := Valuation.isOpen_ball
@[deprecated (since := "2026-03-17")] alias isClosed_ball := Valuation.isClosed_ball
@[deprecated (since := "2026-03-17")] alias isClopen_ball := Valuation.isClopen_ball
@[deprecated (since := "2026-03-17")] alias isOpen_closedBall := Valuation.isOpen_closedBall
@[deprecated (since := "2026-03-17")] alias isClosed_closedBall := Valuation.isClosed_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_closedBall := Valuation.isClopen_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_sphere := Valuation.isClopen_sphere
@[deprecated (since := "2026-03-17")] alias isOpen_sphere := Valuation.isOpen_sphere

end IsValuativeTopology

