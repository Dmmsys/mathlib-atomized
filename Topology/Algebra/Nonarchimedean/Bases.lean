/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Neighborhood bases for non-archimedean rings and modules

This file contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `RingSubgroupsBasis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`RingSubgroupsBasis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular, the given subgroups become open subgroups
(bundled in `RingSubgroupsBasis.openAddSubgroup`) and we get a non-archimedean topological ring
(`RingSubgroupsBasis.nonarchimedean`).

A special case of this construction is given by `SubmodulesBasis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rise to the adic topology
(studied in its own file).
-/

@[expose] public section

open Set Filter Function Lattice

open Topology Filter Pointwise

/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
/-
**RingSubgroupsBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{A : Type u_1} → {ι : Type u_2} → [inst : Ring A] → (ι → AddSubgroup A) → 
Prop
参数：ι → AddSubgroup A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of additive subgroups on a ring `A` is a subgroups basis if it satisfie
s some
axioms ensuring there is a topology on `A` which is compatible with the ring str
ucture and
admits this family as a basis of neighborhoods of zero.
-/
structure RingSubgroupsBasis {A ι : Type*} [Ring A] (B : ι → AddSubgroup A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `B' * x` is in `B`. -/
  leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (x * ·) ⁻¹' B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `x * B'` is in `B`. -/
  rightMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (· * x) ⁻¹' B i

namespace RingSubgroupsBasis

variable {A ι : Type*} [Ring A]

/-
**RingSubgroupsBasis.of_comm** 是 Mathlib 中的一个定理，位于命名空间 `RingSubgroupsBasis`。
形式化陈述：of_comm {A ι : Type*} [CommRing A] (B : ι -> AddSubgroup A) (inter : foral
l i j, exists k, B k <= B i ⊓ B j) (mul : forall i, exists j, (B j : Set A) * B 
j subseteq B i) (leftMul : forall x : A, forall i, exists j, (B j : Set A) subse
teq (fun y : A => x * y) ⁻¹' B i) : RingSubgroupsBasis B
参数：B : ι -> AddSubgroup A；inter : forall i j, exists k, B k <= B i ⊓ B j；mul : f
orall i, exists j, (B j : Set A) * B j subseteq B i；leftMul : forall x : A, fora
ll i, exists j, (B j : Set A) subseteq (fun y : A => x * y) ⁻¹' B i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem of_comm {A ι : Type*} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := fun x i ↦ (leftMul x i).imp fun j hj ↦ by simpa only [mul_comm] using hj }

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
@[instance_reducible]
/-
**RingSubgroupsBasis.toRingFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 `RingSubgroupsB
asis`。
形式化陈述：toRingFilterBasis [Nonempty ι] {B : ι -> AddSubgroup A} (hB : RingSubgroup
sBasis B) : RingFilterBasis A where sets
参数：hB : RingSubgroupsBasis B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every subgroups basis on a ring leads to a ring filter basis.
-/
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.mul i
    use B k
    constructor
    · use k
    · exact hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.leftMul x₀ i
    use B k
    constructor
    · use k
    · exact hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.rightMul x₀ i
    use B k
    constructor
    · use k
    · exact hk

variable [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B)
/-
**RingSubgroupsBasis.mem_addGroupFilterBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ring
SubgroupsBasis`。
形式化陈述：mem_addGroupFilterBasis_iff {V : Set A} : V in hB.toRingFilterBasis.toAddG
roupFilterBasis ↔ exists i, V = B i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V ∈ hB.toRingFilterBasis.toAddGroupFilterBasis ↔ ∃ i, V = B i :=
  Iff.rfl
/-
**RingSubgroupsBasis.mem_addGroupFilterBasis** 是 Mathlib 中的一个定理，位于命名空间 `RingSubg
roupsBasis`。
形式化陈述：mem_addGroupFilterBasis (i) : (B i : Set A) in hB.toRingFilterBasis.toAddG
roupFilterBasis
参数：i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_addGroupFilterBasis (i) : (B i : Set A) ∈ hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
@[instance_reducible]
/-
**RingSubgroupsBasis.topology** 是 Mathlib 中的一个定义，位于命名空间 `RingSubgroupsBasis`。
形式化陈述：topology : TopologicalSpace A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology defined from a subgroups basis, admitting the given subgroups as a 
basis
of neighborhoods of zero.
-/
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology
/-
**RingSubgroupsBasis.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingSubgroups
Basis`。
形式化陈述：hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun 
i => B i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `AddGroupFilterBasis.nhds_zero_hasBasis`：∀ {G : Type u} [inst : AddGroup 
G] (B : AddGroupFilterBasis G), (nhds 0).HasBasis (fun V => V ∈ B) id
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩
/-
**RingSubgroupsBasis.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 `RingSubgroupsBasis
`。
形式化陈述：hasBasis_nhds (a : A) : HasBasis (@nhds A hB.topology a) (fun _ => True) f
un i => { b | b - a in B i }
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `AddGroupFilterBasis.nhds_hasBasis`：∀ {G : Type u} [inst : AddGroup G] (B
 : AddGroupFilterBasis G) (x₀ : G),   (nhds x₀).HasBasis (fun V => V ∈ B) fun V 
=> (fun y => x₀ + y) ''…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a ∈ B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp only [image_add_left, neg_add_eq_sub]
      ext b
      simp
    · rintro ⟨i, hi⟩
      use B i
      constructor
      · use i
      · rw [image_subset_iff]
        rintro b b_in
        apply hi
        simpa using b_in⟩

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
/-
**RingSubgroupsBasis.openAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `RingSubgroupsBas
is`。
形式化陈述：openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgroups basis, the basis elements as open additive subgroups in the as
sociated
topology.
-/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }

-- See note [non-Archimedean non-instances]
/-
**RingSubgroupsBasis.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `RingSubgroupsBasi
s`。
形式化陈述：nonarchimedean : @NonarchimedeanRing A _ hB.topology
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingFilterBasis.isTopologicalRing`：∀ {R : Type u} [inst : Ring R] (B : R
ingFilterBasis R), IsTopologicalRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `RingSubgroupsBasis.hasBasis_nhds_zero`：hasBasis_nhds_zero : HasBasis (@n
hds A hB.topology 0) (fun _ => True) fun i => B i
-/
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

end RingSubgroupsBasis

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
/-
**SubmodulesRingBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {A : Type u_3} → [inst : CommRing 
R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ι → Submodule R A) → Prop
参数：ι → Submodule R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of submodules in a commutative `R`-algebra `A` is a submodules basis if
 it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the rin
g structure and
admits this family as a basis of neighborhoods of zero.
-/
structure SubmodulesRingBasis (B : ι → Submodule R A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `a : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `a • B'` is in `B`. -/
  leftMul : ∀ (a : A) (i), ∃ j, a • B j ≤ B i
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i

namespace SubmodulesRingBasis

variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)

/-
**SubmodulesRingBasis.toRing_subgroups_basis** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
esRingBasis`。
形式化陈述：toRing_subgroups_basis (hB : SubmodulesRingBasis B) : RingSubgroupsBasis f
un i => (B i).toAddSubgroup
参数：hB : SubmodulesRingBasis B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingSubgroupsBasis.of_comm`：of_comm {A ι : Type*} [CommRing A] (B : ι ->
 AddSubgroup A) (inter : forall i j, exists k, B k <= B i ⊓ B j) (mul : forall i
, exists j, (B j…
· 使用定理 `SubmodulesRingBasis.inter`：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_3
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   {B : ι → Su
bmodule R A}, S…
· 使用定理 `SubmodulesRingBasis.mul`：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   {B : ι → Subm
odule R A}, S…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubmodulesRingBasis.leftMul`：∀ {ι : Type u_1} {R : Type u_2} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   {B : ι → 
Submodule R A}, S…
-/
theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup := by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b ∈ B j)
  exact hj ⟨b, b_in, rfl⟩

/-- The topology associated to a basis of submodules in an algebra. -/
@[instance_reducible]
/-
**SubmodulesRingBasis.topology** 是 Mathlib 中的一个定义，位于命名空间 `SubmodulesRingBasis`。
形式化陈述：topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A
参数：hB : SubmodulesRingBasis B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SubmodulesRingBasis.toRing_subgroups_basis`：toRing_subgroups_basis (hB :
 SubmodulesRingBasis B) : RingSubgroupsBasis fun i => (B i).toAddSubgroup

--- 原说明 ---
The topology associated to a basis of submodules in an algebra.
-/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology

end SubmodulesRingBasis

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
/-
**SubmodulesBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     [inst : CommRing R] →       {M : T
ype u_4} →         [inst_1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → [T
opologicalSpace R] → (ι → Submodule R M) → Prop
参数：ι → Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of submodules in an `R`-module `M` is a submodules basis if it satisfie
s
some axioms ensuring there is a topology on `M` which is compatible with the mod
ule structure and
admits this family as a basis of neighborhoods of zero.
-/
structure SubmodulesBasis [TopologicalSpace R] (B : ι → Submodule R M) : Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `m : M` and any set `B` in the basis, `a • m` lies in `B` for all
  `a` sufficiently close to `0`. -/
  smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)

/-- The image of a submodules basis is a module filter basis. -/
/-
**SubmodulesBasis.toModuleFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 `SubmodulesBasis
`。
形式化陈述：toModuleFilterBasis : ModuleFilterBasis R M where sets
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a submodules basis is a module filter basis.
-/
def toModuleFilterBasis : ModuleFilterBasis R M where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ
    constructor
    · exact univ_mem
    · use B i
      constructor
      · use i
      · rintro _ ⟨a, -, m, hm, rfl⟩
        exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro m
      exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i

/-- The topology associated to a basis of submodules in a module. -/
@[instance_reducible]
/-
**SubmodulesBasis.topology** 是 Mathlib 中的一个定义，位于命名空间 `SubmodulesBasis`。
形式化陈述：topology : TopologicalSpace M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology associated to a basis of submodules in a module.
-/
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology

/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
/-
**SubmodulesBasis.openAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SubmodulesBasis`。
形式化陈述：openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submodules basis, the basis elements as open additive subgroups in the a
ssociated
topology.
-/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology
  { (B i).toAddSubgroup with
    isOpen' := by
      let := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rfl⟩
        exact (B i).add_mem a_in b_in }

-- See note [non-Archimedean non-instances]
/-
**SubmodulesBasis.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `SubmodulesBasis`。
形式化陈述：nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.t
opology
参数：hB : SubmodulesBasis B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `AddGroupFilterBasis.nhds_zero_hasBasis`：∀ {G : Type u} [inst : AddGroup 
G] (B : AddGroupFilterBasis G), (nhds 0).HasBasis (fun V => V ∈ B) id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  let := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note «non-Archimedean non-instances» /--
The non-Archimedean subgroup basis lemmas cannot be instances because some instances
(such as `MeasureTheory.AEEqFun.instAddMonoid` or `IsTopologicalAddGroup.toContinuousAdd`)
cause the search for `@IsTopologicalAddGroup β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/


end SubmodulesBasis

section

/-
In this section, we check that in an `R`-algebra `A` over a ring equipped with a topology,
a basis of `R`-submodules which is compatible with the topology on `R` is also a submodule basis
in the sense of `R`-modules (forgetting about the ring structure on `A`) and those two points of
view definitionaly gives the same topology on `A`.
-/
variable [TopologicalSpace R] {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : ∀ (m : A) (i : ι), ∀ᶠ a : R in 𝓝 0, a • m ∈ B i)
include hB hsmul

/-
**SubmodulesRingBasis.toSubmodulesBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmodulesRingBasis.inter`：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_3
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   {B : ι → Su
bmodule R A}, S…
-/
theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

end

/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of an `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
/-
**RingFilterBasis.SubmodulesBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingFilterBasis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     [inst : CommRing R] →       {M : T
ype u_4} →         [inst_1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → Ri
ngFilterBasis R → (ι → Submodule R M) → Prop
参数：ι → Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring filter basis on a commutative ring `R`, define a compatibility cond
ition
on a family of submodules of an `R`-module `M`. This compatibility condition all
ows to get
a topological module structure.
-/
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι → Submodule R M) :
    Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `m : M` and any set `B i` in the submodule basis on `M`,
  there is a `U` in the ring filter basis on `R` such that `U * m` is in `B i`. -/
  smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (· • m) ⁻¹' B i
/-
**RingFilterBasis.submodulesBasisIsBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι -> 
Submodule R M} (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _
 BR.topology B
参数：BR : RingFilterBasis R；hB : BR.SubmodulesBasis B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingFilterBasis.SubmodulesBasis.inter`：∀ {ι : Type u_1} {R : Type u_2} [
inst : CommRing R] {M : Type u_4} [inst_1 : AddCommGroup M]   [inst_2 : _root_.M
odule R M] {BR : RingFilter…
· 使用定理 `RingFilterBasis.SubmodulesBasis.smul`：∀ {ι : Type u_1} {R : Type u_2} [i
nst : CommRing R] {M : Type u_4} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Mo
dule R M] {BR : RingFilter…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `AddGroupFilterBasis.mem_nhds_zero`：∀ {G : Type u} [inst : AddGroup G] (B
 : AddGroupFilterBasis G) {U : Set G}, U ∈ B → U ∈ nhds 0
-/
theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _ BR.topology B :=
  let _ := BR.topology
  { inter := hB.inter
    smul := by
      let := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
/-
**RingFilterBasis.moduleFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B
 : ι -> Submodule R M} (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR
.topology _ _
参数：BR : RingFilterBasis R；hB : BR.SubmodulesBasis B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingFilterBasis.submodulesBasisIsBasis`：RingFilterBasis.submodulesBasisI
sBasis (BR : RingFilterBasis R) {B : ι -> Submodule R M} (hB : BR.SubmodulesBasi
s B) : @_root_.SubmodulesBas…

--- 原说明 ---
The module filter basis associated to a ring filter basis and a compatible submo
dule basis.
This allows to build a topological module structure compatible with the given mo
dule structure
and the topology associated to the given ring filter basis.
-/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)
