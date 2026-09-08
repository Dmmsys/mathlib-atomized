/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: a predicate stating that all Sylow subgroups of `G` are cyclic.

## Main results

* `IsZGroup.isCyclic_abelianization`: a finite Z-group has cyclic abelianization.
* `IsZGroup.isCyclic_commutator`: a finite Z-group has cyclic commutator subgroup.
* `IsZGroup.coprime_commutator_index`: the commutator subgroup of a finite Z-group is a
  Hall-subgroup (the commutator subgroup has cardinality coprime to its index).
* `isZGroup_iff_exists_mulEquiv`: a finite group `G` is a Z-group if and only if `G` is isomorphic
  to a semidirect product of two cyclic subgroups of coprime order.

-/

public section

variable (G G' G'' : Type*) [Group G] [Group G'] [Group G''] (f : G →* G') (f' : G' →* G'')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
/-
**IsZGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Z-group is a group whose Sylow subgroups are all cyclic.
-/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' G'' f f'}

namespace IsZGroup

/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCyclic G] : IsZGroup G :=
  ⟨inferInstance⟩
/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsZGroup G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P
/-
**IsZGroup._root_.IsPGroup.isCyclic_of_isZGroup** 是 Mathlib 中的一个定理，位于命名空间 `IsZGr
oup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsPGroup.isCyclic_of_isZGroup [IsZGroup G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact Subgroup.isCyclic_of_le hQ
/-
**IsZGroup.of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：of_squarefree (hG : Squarefree (Nat.card G)) : IsZGroup G
参数：hG : Squarefree (Nat.card G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `IsPGroup.exists_card_eq`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [Fact
 (Nat.Prime p)] [Finite G], IsPGroup p G → ∃ n, Nat.card G = p ^ n
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `isCyclic_of_card_dvd_prime`：isCyclic_of_card_dvd_prime {p : Nat} [hp : F
act p.Prime] (h : Nat.card α ∣ p) : IsCyclic α
· 使用定理 `Squarefree.pow_dvd_of_pow_dvd`：Squarefree.pow_dvd_of_pow_dvd [Monoid R] 
{x y : R} {n : Nat} (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
-/
theorem of_squarefree (hG : Squarefree (Nat.card G)) : IsZGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)
/-
**IsZGroup.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isZGroup_iff`：∀ (G : Type u_1) [inst : Group G], IsZGroup G ↔ ∀ (p : ℕ),
 Nat.Prime p → ∀ (P : Sylow p G), IsCyclic ↥↑P
· 使用定理 `Sylow.exists_comap_eq_of_injective`：exists_comap_eq_of_injective {H : Ty
pe*} [Group H] (P : Sylow p H) {f : H ->* G} (hf : Function.Injective f) : exist
s Q : Sylow p G, Q.comap…
· 使用定理 `Subgroup.map_comap_le`：map_comap_le (H : Subgroup N) : map f (comap f H)
 <= H
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective
/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective
/-
**IsZGroup.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：of_surjective [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f) : 
IsZGroup G'
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isZGroup_iff`：∀ (G : Type u_1) [inst : Group G], IsZGroup G ↔ ∀ (p : ℕ),
 Nat.Prime p → ∀ (P : Sylow p G), IsCyclic ↥↑P
· 使用定理 `Sylow.mapSurjective_surjective`：mapSurjective_surjective (p : Nat) [Fact
 p.Prime] : Function.Surjective (Sylow.mapSurjective hf : Sylow p G -> Sylow p G
')
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MonoidHom.subgroupMap_surjective`：subgroupMap_surjective (f : G ->* G') 
(H : Subgroup G) : Function.Surjective (f.subgroupMap H)
-/
theorem of_surjective [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f) : IsZGroup G' := by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)
/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G] [IsZGroup G] (H : Subgroup G) [H.Normal] : IsZGroup (G ⧸ H) :=
  of_surjective (QuotientGroup.mk'_surjective H)

section Solvable

open scoped IsMulCommutative in
variable (G) in
/-
**IsZGroup.commutator_lt** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：commutator_lt [Finite G] [IsZGroup G] [Nontrivial G] : commutator G < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `IsZGroup.isZGroup`：∀ {G : Type u_1} {inst : Group G} [self : IsZGroup G]
 (p : ℕ), Nat.Prime p → ∀ (P : Sylow p G), IsCyclic ↥↑P
· 使用定理 `IsCyclic.normalizer_le_centralizer`：normalizer_le_centralizer (hP : IsCy
clic P) : normalizer P <= centralizer (P : Set G)
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Abelianization.commutator_subset_ker`：commutator_subset_ker : commutator
 G <= f.ker
· 使用定理 `Sylow.ne_bot_of_dvd_card`：ne_bot_of_dvd_card [Finite G] {p : Nat} [hp : 
Fact p.Prime] (P : Sylow p G) (hdvd : p ∣ Nat.card G) : (P : Subgroup G) != ⊥
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.isComplement'_top_left`：∀ {G : Type u_1} [inst : Group G] {H : 
Subgroup G}, ⊤.IsComplement' H ↔ H = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt_top_iff`：not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤
· 使用定理 `IsCyclic.isComplement'`：isComplement' (hP : IsCyclic P) : (MonoidHom.tra
nsferSylow P (hP.normalizer_le_centralizer hp)).ker.IsComplement' P
-/
theorem commutator_lt [Finite G] [IsZGroup G] [Nontrivial G] : commutator G < ⊤ := by
  let p := (Nat.card G).minFac
  have hp : p.Prime := Nat.minFac_prime Finite.one_lt_card.ne'
  have := Fact.mk hp
  let P : Sylow p G := default
  have hP := isZGroup p hp P
  let f := MonoidHom.transferSylow P (hP.normalizer_le_centralizer rfl)
  refine lt_of_le_of_lt (Abelianization.commutator_subset_ker f) ?_
  have h := P.ne_bot_of_dvd_card (Nat.card G).minFac_dvd
  contrapose h
  rw [← Subgroup.isComplement'_top_left, ← (not_lt_top_iff.mp h)]
  exact hP.isComplement' rfl
/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G] [IsZGroup G] : Group.IsSolvable G := by
  rw [Group.isSolvable_iff_commutator_lt]
  intro H h
  rw [← H.nontrivial_iff_ne_bot] at h
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    Subgroup.map_subtype_lt_map_subtype]
  exact commutator_lt H

end Solvable

section Nilpotent

variable (G) in
/-
**IsZGroup.exponent_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：exponent_eq_card [Finite G] [IsZGroup G] : Monoid.exponent G = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Group.exponent_dvd_nat_card`：Group.exponent_dvd_nat_card : Monoid.expone
nt G ∣ Nat.card G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_prime_le_iff_dvd`：factorization_prime_le_iff_dvd {d n 
: Nat} (hd : d != 0) (hn : n != 0) : (forall p : Nat, p.Prime -> d.factorization
 p <= n.factorization p)…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Monoid.exponent_ne_zero_of_finite`：exponent_ne_zero_of_finite : exponent
 G != 0
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `Sylow.card_eq_multiplicity`：card_eq_multiplicity [Finite G] {p : Nat} [h
p : Fact p.Prime] (P : Sylow p G) : Nat.card P = p ^ Nat.factorization (Nat.card
 G) p
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
· 使用定理 `IsZGroup.isZGroup`：∀ {G : Type u_1} {inst : Group G} [self : IsZGroup G]
 (p : ℕ), Nat.Prime p → ∀ (P : Sylow p G), IsCyclic ↥↑P
· 使用定理 `Monoid.exponent_dvd_of_monoidHom`：exponent_dvd_of_monoidHom (e : G ->* H
) (e_inj : Function.Injective e) : Monoid.exponent G ∣ Monoid.exponent H
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem exponent_eq_card [Finite G] [IsZGroup G] : Monoid.exponent G = Nat.card G := by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite,
      ← P.card_eq_multiplicity, ← (isZGroup p hp P).exponent_eq_card]
  exact Monoid.exponent_dvd_of_monoidHom P.1.subtype P.1.subtype_injective

open scoped IsMulCommutative in
/-
**IsZGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G] [IsZGroup G] [hG : Group.IsNilpotent G] : IsCyclic G := by
  have (p : { x // x ∈ (Nat.card G).primeFactors }) : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  obtain ⟨ϕ⟩ := ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h ↦ by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  exact IsCyclic.of_exponent_eq_card (exponent_eq_card G)

/-- A finite Z-group has cyclic abelianization. -/
/-
**IsZGroup.isCyclic_abelianization** 是 Mathlib 中的一个实例，位于命名空间 `IsZGroup`。
形式化陈述：isCyclic_abelianization [Finite G] [IsZGroup G] : IsCyclic (Abelianization
 G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsZGroup.instIsCyclicOfFiniteOfIsNilpotent`：∀ {G : Type u_1} [inst : Gro
up G] [Finite G] [IsZGroup G] [hG : Group.IsNilpotent G], IsCyclic G
· 使用定理 `instFiniteAbelianization`：∀ {G : Type u_1} [inst : Group G] [Finite G], 
Finite (Abelianization G)
· 使用定理 `CommGroup.isNilpotent`：∀ {G : Type u_2} [inst : CommGroup G], Group.IsNi
lpotent G

--- 原说明 ---
A finite Z-group has cyclic abelianization.
-/
instance isCyclic_abelianization [Finite G] [IsZGroup G] : IsCyclic (Abelianization G) :=
  let _ : IsZGroup (Abelianization G) := inferInstanceAs (IsZGroup (G ⧸ commutator G))
  inferInstance

end Nilpotent

section Commutator

variable (G) in
/-- A finite Z-group has cyclic commutator subgroup. -/
/-
**IsZGroup.isCyclic_commutator** 是 Mathlib 中的一个定理，位于命名空间 `IsZGroup`。
形式化陈述：isCyclic_commutator [Finite G] [IsZGroup G] : IsCyclic (commutator G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commutator_def`：commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Subgroup.commutator_bot_left`：commutator_bot_left : ⁅(⊥ : Subgroup G), H
₁⁆ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `Group.IsSolvable.commutator_lt_of_ne_bot`：∀ {G : Type u_1} [inst : Group
 G] [Group.IsSolvable G] {H : Subgroup G}, H ≠ ⊥ → ⁅H, H⁆ < H
· 使用定理 `IsZGroup.instIsSolvableOfFinite`：∀ {G : Type u_1} [inst : Group G] [Fini
te G] [IsZGroup G], Group.IsSolvable G
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用引理 `Subgroup.map_subtype_commutator`：Subgroup.map_subtype_commutator (H : Su
bgroup G) : (_root_.commutator H).map H.subtype = ⁅H, H⁆
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `Subgroup.le_centralizer_iff`：le_centralizer_iff : H <= centralizer K ↔ K
 <= centralizer H
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `Abelianization.commutator_subset_ker`：commutator_subset_ker : commutator
 G <= f.ker
· 使用定理 `Subgroup.map_subgroupOf_eq_of_le`：map_subgroupOf_eq_of_le {H K : Subgrou
p G} (h : H <= K) : (H.subgroupOf K).map K.subtype = H
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Subgroup.map_subtype_le_map_subtype`：map_subtype_le_map_subtype {G' : Su
bgroup G} {H K : Subgroup G'} : H.map G'.subtype <= K.map G'.subtype ↔ H <= K
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
· 使用定理 `Subgroup.normalizerMonoidHom_ker`：normalizerMonoidHom_ker : H.normalizer
MonoidHom.ker = (centralizer H).subgroupOf (normalizer H : Subgroup G)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
A finite Z-group has cyclic commutator subgroup.
-/
theorem isCyclic_commutator [Finite G] [IsZGroup G] : IsCyclic (commutator G) := by
  rw [commutator_def]
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h
  · rw [Subgroup.commutator_bot_left]
    infer_instance
  · specialize hH ⁅H, H⁆ (Group.IsSolvable.commutator_lt_of_ne_bot h)
    replace hH : IsCyclic (⁅commutator H, commutator H⁆ : Subgroup H) := by
      let f := Subgroup.equivMapOfInjective ⁅commutator H, commutator H⁆ _ H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f.symm f.symm.surjective
    suffices IsCyclic (commutator H) by
      let f := Subgroup.equivMapOfInjective (commutator H) _ H.subtype_injective
      rw [Subgroup.map_subtype_commutator] at f
      exact isCyclic_of_surjective f f.surjective
    suffices h : commutator (commutator H) ≤ Subgroup.center (commutator H) by
      rw [← Abelianization.ker_of (commutator H)] at h
      let _ := commGroupOfCyclicCenterQuotient Abelianization.of h
      infer_instance
    suffices h : (commutator (commutator H)).map (commutator H).subtype ≤
        Subgroup.centralizer (commutator H) by
      simpa [SetLike.le_def, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff] using h
    rw [Subgroup.map_subtype_commutator, Subgroup.le_centralizer_iff]
    let _ := (hH.mulAutMulEquiv _).toMonoidHom.commGroupOfInjective (hH.mulAutMulEquiv _).injective
    have h := Abelianization.commutator_subset_ker ⁅commutator H, commutator H⁆.normalizerMonoidHom
    rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.normalizer_eq_top,
      ← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subtype_commutator,
        Subgroup.map_subgroupOf_eq_of_le le_top] at h

end Commutator

end IsZGroup

section Hall

variable {p : ℕ} [Fact p.Prime]

namespace IsPGroup

/-- If a group `K` acts on a cyclic `p`-group `G` of coprime order, then the map `K × G → G`
  defined by `(k, g) ↦ k • g * g⁻¹` is either trivial or surjective. -/
/-
**IsPGroup.smul_mul_inv_trivial_or_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsPGrou
p`。
形式化陈述：smul_mul_inv_trivial_or_surjective [IsCyclic G] (hG : IsPGroup p G) {K : T
ype*} [Group K] [MulDistribMulAction K G] (hGK : (Nat.card G).Coprime (Nat.card 
K)) : (forall g : G, forall k : K, k • g * g⁻¹ = 1) ∨ (forall g : G, exists k : 
K, exists q : G, k • q * q⁻¹ = g)
参数：hG : IsPGroup p G；hGK : (Nat.card G).Coprime (Nat.card K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply`：MulDistribMulAction
.toMonoidHomZModOfIsCyclic_apply {M : Type*} [Monoid M] [IsCyclic G] [MulDistrib
MulAction M G] {n : Nat} (hn : Nat.card G…
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `IsPGroup.exists_card_eq`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [Fact
 (Nat.Prime p)] [Finite G], IsPGroup p G → ∃ n, Nat.card G = p ^ n
· 使用定理 `ZMod.eq_one_or_isUnit_sub_one`：ZMod.eq_one_or_isUnit_sub_one {n p k : Na
t} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n) (ha : (orderOf a).Coprime n) : a
 = 1 ∨ IsUnit (a - …
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `orderOf_map_dvd`：orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G ->* H) (x
 : G) : orderOf (ψ x) ∣ orderOf x
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If a group `K` acts on a cyclic `p`-group `G` of coprime order, then the map `K 
× G → G`
  defined by `(k, g) ↦ k • g * g⁻¹` is either trivial or surjective.
-/
theorem smul_mul_inv_trivial_or_surjective [IsCyclic G] (hG : IsPGroup p G)
    {K : Type*} [Group K] [MulDistribMulAction K G] (hGK : (Nat.card G).Coprime (Nat.card K)) :
    (∀ g : G, ∀ k : K, k • g * g⁻¹ = 1) ∨ (∀ g : G, ∃ k : K, ∃ q : G, k • q * q⁻¹ = g) := by
  by_cases hc : Nat.card G = 0
  · rw [hc, Nat.coprime_zero_left, Nat.card_eq_one_iff_unique] at hGK
    simp [← hGK.1.elim 1]
  have := Nat.finite_of_card_ne_zero hc
  let ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic G K rfl
  have h (g : G) (k : K) (n : ℤ) (h : ϕ k - 1 = n) : k • g * g⁻¹ = g ^ n := by
    rw [sub_eq_iff_eq_add, ← Int.cast_one, ← Int.cast_add] at h
    rw [MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply rfl k g (n + 1) h,
      zpow_add_one, mul_inv_cancel_right]
  replace hG k : ϕ k = 1 ∨ IsUnit (ϕ k - 1) := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    exact ZMod.eq_one_or_isUnit_sub_one hn (ϕ k)
      (hGK.symm.coprime_dvd_left ((orderOf_map_dvd ϕ k).trans (orderOf_dvd_natCard k)))
  rcases forall_or_exists_not (fun k : K ↦ ϕ k = 1) with hϕ | ⟨k, hk⟩
  · exact Or.inl fun p k ↦ by rw [h p k 0 (by rw [hϕ, sub_self, Int.cast_zero]), zpow_zero]
  · obtain ⟨⟨u, v, -, hvu⟩, hu : u = ϕ k - 1⟩ := (hG k).resolve_left hk
    rw [← u.intCast_zmod_cast] at hu hvu
    rw [← v.intCast_zmod_cast, ← Int.cast_mul, ← Int.cast_one, ZMod.intCast_eq_intCast_iff] at hvu
    refine Or.inr fun p ↦ zpow_one p ▸ ⟨k, p ^ (v.cast : ℤ), ?_⟩
    rw [h (p ^ v.cast) k u.cast hu.symm, ← zpow_mul, zpow_eq_zpow_iff_modEq]
    exact hvu.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard p))

/-- If a cyclic `p`-subgroup `P` acts by conjugation on a subgroup `K` of coprime order, then
  either `⁅K, P⁆ = ⊥` or `⁅K, P⁆ = P`. -/
/-
**IsPGroup.commutator_eq_bot_or_commutator_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Is
PGroup`。
形式化陈述：commutator_eq_bot_or_commutator_eq_self {P K : Subgroup G} [IsCyclic P] (h
P : IsPGroup p P) (hKP : K <= Subgroup.normalizer P) (hPK : (Nat.card P).Coprime
 (Nat.card K)) : ⁅K, P⁆ = ⊥ ∨ ⁅K, P⁆ = P
参数：hP : IsPGroup p P；hKP : K <= Subgroup.normalizer P；hPK : (Nat.card P).Coprime
 (Nat.card K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subgroup.commutator_le`：commutator_le : ⁅H₁, H₂⁆ <= H₃ ↔ forall g₁ in H₁
, forall g₂ in H₂, ⁅g₁, g₂⁆ in H₃
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subgroup.commutator_mem_commutator`：commutator_mem_commutator (h₁ : g₁ i
n H₁) (h₂ : g₂ in H₂) : ⁅g₁, g₂⁆ in ⁅H₁, H₂⁆
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsPGroup.smul_mul_inv_trivial_or_surjective`：smul_mul_inv_trivial_or_sur
jective [IsCyclic G] (hG : IsPGroup p G) {K : Type*} [Group K] [MulDistribMulAct
ion K G] (hGK : (Nat.card G).Copr…

--- 原说明 ---
If a cyclic `p`-subgroup `P` acts by conjugation on a subgroup `K` of coprime or
der, then
  either `⁅K, P⁆ = ⊥` or `⁅K, P⁆ = P`.
-/
theorem commutator_eq_bot_or_commutator_eq_self {P K : Subgroup G} [IsCyclic P]
    (hP : IsPGroup p P) (hKP : K ≤ Subgroup.normalizer P)
    (hPK : (Nat.card P).Coprime (Nat.card K)) : ⁅K, P⁆ = ⊥ ∨ ⁅K, P⁆ = P := by
  let _ := MulDistribMulAction.compHom P (P.normalizerMonoidHom.comp (Subgroup.inclusion hKP))
  refine (smul_mul_inv_trivial_or_surjective hP hPK).imp (fun h ↦ ?_) fun h ↦ ?_
  · rw [eq_bot_iff, Subgroup.commutator_le]
    exact fun k hk g hg ↦ Subtype.ext_iff.mp (h ⟨g, hg⟩ ⟨k, hk⟩)
  · rw [le_antisymm_iff, Subgroup.commutator_le]
    refine ⟨fun k hk g hg ↦ P.mul_mem ((hKP hk g).mp hg) (P.inv_mem hg), fun g hg ↦ ?_⟩
    obtain ⟨k, q, hkq⟩ := h ⟨g, hg⟩
    rw [← Subtype.coe_mk g hg, ← hkq]
    exact Subgroup.commutator_mem_commutator k.2 q.2

end IsPGroup

namespace Sylow

variable [Finite G] (P : Sylow p G) [IsCyclic P]

/-- If a normal cyclic Sylow `p`-subgroup `P` has a complement `K`, then either `⁅K, P⁆ = ⊥` or
  `⁅K, P⁆ = P`. -/
/-
**Sylow.commutator_eq_bot_or_commutator_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Sylow
`。
形式化陈述：commutator_eq_bot_or_commutator_eq_self [P.Normal] {K : Subgroup G} (h : K
.IsComplement' P) : ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P
参数：h : K.IsComplement' P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.commutator_eq_bot_or_commutator_eq_self`：commutator_eq_bot_or_c
ommutator_eq_self {P K : Subgroup G} [IsCyclic P] (hP : IsPGroup p P) (hKP : K <
= Subgroup.normalizer P) (hPK : (Nat.c…
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
· 使用定理 `Sylow.card_coprime_index`：card_coprime_index [Finite G] {p : Nat} [hp : 
Fact p.Prime] (P : Sylow p G) : (Nat.card P).Coprime P.index
· 使用定理 `Subgroup.IsComplement'.index_eq_card`：∀ {G : Type u_1} [inst : Group G] 
{H K : Subgroup G}, H.IsComplement' K → K.index = Nat.card ↥H

--- 原说明 ---
If a normal cyclic Sylow `p`-subgroup `P` has a complement `K`, then either `⁅K,
 P⁆ = ⊥` or
  `⁅K, P⁆ = P`.
-/
theorem commutator_eq_bot_or_commutator_eq_self [P.Normal] {K : Subgroup G}
    (h : K.IsComplement' P) : ⁅K, P.1⁆ = ⊥ ∨ ⁅K, P.1⁆ = P :=
  P.2.commutator_eq_bot_or_commutator_eq_self (P.normalizer_eq_top ▸ le_top)
    (h.index_eq_card ▸ P.card_coprime_index)

/-- A normal cyclic Sylow subgroup is either central or contained in the commutator subgroup. -/
/-
**Sylow.le_center_or_le_commutator** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：le_center_or_le_commutator [P.Normal] : P <= Subgroup.center G ∨ P <= comm
utator G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.exists_left_complement'_of_coprime`：∀ {G : Type u} [inst : Grou
p G] {N : Subgroup G} [N.Normal], (Nat.card ↥N).Coprime N.index → ∃ H, H.IsCompl
ement' N
· 使用定理 `Sylow.card_coprime_index`：card_coprime_index [Finite G] {p : Nat} [hp : 
Fact p.Prime] (P : Sylow p G) : (Nat.card P).Coprime P.index
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.commutator_eq_bot_iff_le_centralizer`：commutator_eq_bot_iff_le_
centralizer : ⁅H₁, H₂⁆ = ⊥ ↔ H₁ <= centralizer H₂
· 使用定理 `Subgroup.le_centralizer`：le_centralizer [h : IsMulCommutative H] : H <= 
centralizer H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset {s
 : Set G} : centralizer s = ⊤ ↔ s subseteq center G
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subgroup.IsComplement'.sup_eq_top`：∀ {G : Type u_1} [inst : Group G] {H 
K : Subgroup G}, H.IsComplement' K → H ⊔ K = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `commutator_def`：commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Sylow.commutator_eq_bot_or_commutator_eq_self`：commutator_eq_bot_or_comm
utator_eq_self [P.Normal] {K : Subgroup G} (h : K.IsComplement' P) : ⁅K, P.1⁆ = 
⊥ ∨ ⁅K, P.1⁆ = P

--- 原说明 ---
A normal cyclic Sylow subgroup is either central or contained in the commutator 
subgroup.
-/
theorem le_center_or_le_commutator [P.Normal] : P ≤ Subgroup.center G ∨ P ≤ commutator G := by
  obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime P.card_coprime_index
  refine (commutator_eq_bot_or_commutator_eq_self P hK).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · replace h := sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) P.le_centralizer
    rwa [hK.sup_eq_top, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at h
  · rw [← h, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/-- A cyclic Sylow subgroup is either central in its normalizer or contained in the commutator
  subgroup. -/
/-
**Sylow.normalizer_le_centralizer_or_le_commutator** 是 Mathlib 中的一个定理，位于命名空间 `Sy
low`。
形式化陈述：normalizer_le_centralizer_or_le_commutator : Subgroup.normalizer P <= Subg
roup.centralizer (P : Set G) ∨ P <= commutator G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.map_subtype_le_map_subtype`：map_subtype_le_map_subtype {G' : Su
bgroup G} {H K : Subgroup G'} : H.map G'.subtype <= K.map G'.subtype ↔ H <= K
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subgroup.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset {s
 : Set G} : centralizer s = ⊤ ↔ s subseteq center G
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Subgroup.map_centralizer_le_centralizer_image`：map_centralizer_le_centra
lizer_image (s : Set G) (f : G ->* G') : (Subgroup.centralizer s).map f <= Subgr
oup.centralizer (f '' s)
· 使用定理 `Subgroup.map_subgroupOf_eq_of_le`：map_subgroupOf_eq_of_le {H K : Subgrou
p G} (h : H <= K) : (H.subgroupOf K).map K.subtype = H
· 使用定理 `Sylow.coe_coe`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G)
, ↑↑P = ↑P
· 使用定理 `Sylow.coe_subtype`：coe_subtype (h : P <= N) : P.subtype h = subgroupOf P
 N
· 使用定理 `Subgroup.coe_map`：coe_map (f : G ->* N) (K : Subgroup G) : (K.map f : Se
t N) = f '' K
· 使用引理 `Subgroup.map_subtype_commutator`：Subgroup.map_subtype_commutator (H : Su
bgroup G) : (_root_.commutator H).map H.subtype = ⁅H, H⁆
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Sylow.le_center_or_le_commutator`：le_center_or_le_commutator [P.Normal] 
: P <= Subgroup.center G ∨ P <= commutator G
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K

--- 原说明 ---
A cyclic Sylow subgroup is either central in its normalizer or contained in the 
commutator
  subgroup.
-/
theorem normalizer_le_centralizer_or_le_commutator :
    Subgroup.normalizer P ≤ Subgroup.centralizer (P : Set G) ∨ P ≤ commutator G := by
  let Q : Sylow p (Subgroup.normalizer P) := P.subtype P.le_normalizer
  have : Q.Normal := P.normal_in_normalizer
  have : IsCyclic Q :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe P.le_normalizer).symm.surjective
  refine (le_center_or_le_commutator Q).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · rw [← SetLike.coe_subset_coe, ← Subgroup.centralizer_eq_top_iff_subset, eq_top_iff,
      ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      (Subgroup.normalizer (P : Set G)).range_subtype] at h
    replace h := h.trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    rwa [← Subgroup.coe_map, P.coe_subtype, ← P.coe_coe,
      Subgroup.map_subgroupOf_eq_of_le P.le_normalizer] at h
  · rw [P.coe_subtype, ← Subgroup.map_subtype_le_map_subtype, ← P.coe_coe,
      Subgroup.map_subgroupOf_eq_of_le P.le_normalizer, Subgroup.map_subtype_commutator] at h
    exact h.trans (Subgroup.commutator_mono le_top le_top)

open scoped IsMulCommutative in
include P in
/-- If `G` has a cyclic Sylow `p`-subgroup, then the cardinality and index of the commutator
  subgroup of `G` cannot both be divisible by `p`. -/
/-
**Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator** 是 Mathlib 中的一个定理，位
于命名空间 `Sylow`。
形式化陈述：not_dvd_card_commutator_or_not_dvd_index_commutator : ¬ p ∣ Nat.card (comm
utator G) ∨ ¬ p ∣ (commutator G).index
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement'.index_eq_card`：∀ {G : Type u_1} [inst : Group G] 
{H K : Subgroup G}, H.IsComplement' K → K.index = Nat.card ↥H
· 使用定理 `MonoidHom.ker_transferSylow_isComplement'`：ker_transferSylow_isComplemen
t' : IsComplement' (transferSylow P hP).ker P
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `Subgroup.card_dvd_of_le`：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K
) : Nat.card H ∣ Nat.card K
· 使用定理 `Abelianization.commutator_subset_ker`：commutator_subset_ker : commutator
 G <= f.ker
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
· 使用定理 `Sylow.normalizer_le_centralizer_or_le_commutator`：normalizer_le_centrali
zer_or_le_commutator : Subgroup.normalizer P <= Subgroup.centralizer (P : Set G)
 ∨ P <= commutator G

--- 原说明 ---
If `G` has a cyclic Sylow `p`-subgroup, then the cardinality and index of the co
mmutator
  subgroup of `G` cannot both be divisible by `p`.
-/
theorem not_dvd_card_commutator_or_not_dvd_index_commutator :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  refine (normalizer_le_centralizer_or_le_commutator P).imp ?_ ?_ <;>
      refine fun hP h ↦ P.not_dvd_index (h.trans ?_)
  · rw [(MonoidHom.ker_transferSylow_isComplement' P hP).index_eq_card]
    exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
  · exact Subgroup.index_dvd_of_le hP

end Sylow

variable (G) in
/-- If `G` is a finite Z-group, then `commutator G` is a Hall subgroup of `G`. -/
/-
**IsZGroup.coprime_commutator_index** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsZGroup.coprime_commutator_index [Finite G] [IsZGroup G] : (Nat.card (com
mutator G)).Coprime (commutator G).index
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator`：not_dvd_card_
commutator_or_not_dvd_index_commutator : ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (
commutator G).index
· 使用定理 `IsZGroup.instIsCyclicSubtypeMemSubgroupOfFactPrime`：∀ {G : Type u_1} [in
st : Group G] [IsZGroup G] {p : ℕ} [Fact (Nat.Prime p)] (P : Sylow p G), IsCycli
c ↥↑P
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n

--- 原说明 ---
If `G` is a finite Z-group, then `commutator G` is a Hall subgroup of `G`.
-/
theorem IsZGroup.coprime_commutator_index [Finite G] [IsZGroup G] :
    (Nat.card (commutator G)).Coprime (commutator G).index := by
  suffices h : ∀ p, p.Prime → (¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index) by
    contrapose! h
    exact Nat.Prime.not_coprime_iff_dvd.mp h
  intro p hp
  have := Fact.mk hp
  exact Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator default

end Hall

section Classification

/-- An extension of coprime Z-groups is a Z-group. -/
/-
**isZGroup_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isZGroup_of_coprime [Finite G] [IsZGroup G] [IsZGroup G''] (h_le : f'.ker 
<= f.range) (h_cop : (Nat.card G).Coprime (Nat.card G'')) : IsZGroup G'
参数：h_le : f'.ker <= f.range；h_cop : (Nat.card G).Coprime (Nat.card G'')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.of_dvd`：∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ ∣ a₂ → b₁ ∣ b₂ → a₂.Coprime 
b₂ → a₁.Coprime b₁
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Subgroup.card_dvd_of_le`：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K
) : Nat.card H ∣ Nat.card K
· 使用定理 `Subgroup.card_range_dvd`：card_range_dvd (f : G ->* G') : Nat.card f.rang
e ∣ Nat.card G
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `IsPGroup.le_or_disjoint_of_coprime`：le_or_disjoint_of_coprime [hp : Fact
 p.Prime] {P : Subgroup G} (hP : IsPGroup p P) {H : Subgroup G} [H.Normal] (h_co
p : (Nat.card H).Coprime…
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
· 使用定理 `Sylow.mapSurjective_surjective`：mapSurjective_surjective (p : Nat) [Fact
 p.Prime] : Function.Surjective (Sylow.mapSurjective hf : Sylow p G -> Sylow p G
')
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `IsZGroup.instIsCyclicSubtypeMemSubgroupOfFactPrime`：∀ {G : Type u_1} [in
st : Group G] [IsZGroup G] {p : ℕ} [Fact (Nat.Prime p)] (P : Sylow p G), IsCycli
c ↥↑P
· 使用定理 `MonoidHom.subgroupMap_surjective`：subgroupMap_surjective (f : G ->* G') 
(H : Subgroup G) : Function.Surjective (f.subgroupMap H)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sylow.coe_subtype`：coe_subtype (h : P <= N) : P.subtype h = subgroupOf P
 N
· 使用定理 `Sylow.coe_mapSurjective`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [inst
_1 : Finite G] {G' : Type u_2} [inst_2 : Group G'] {f : G →* G'}   (hf : Functio
n.Surjective …
· 使用定理 `Sylow.ext_iff`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {P Q : Sylow p 
G}, P = Q ↔ ↑P = ↑Q
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `IsPGroup.isCyclic_of_isZGroup`：∀ {G : Type u_1} [inst : Group G] [IsZGro
up G] {p : ℕ} [Fact (Nat.Prime p)] {P : Subgroup G},   IsPGroup p ↥P → IsCyclic 
↥P
· 使用定理 `IsPGroup.map`：map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Grou
p K] (ϕ : G ->* K) : IsPGroup p (H.map ϕ)
· 使用定理 `isCyclic_of_injective`：isCyclic_of_injective [IsCyclic G'] (f : G ->* G'
) (hf : Function.Injective f) : IsCyclic G
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `Subgroup.ker_subgroupMap`：ker_subgroupMap : (f.subgroupMap H).ker = f.ke
r.subgroupOf H
· 使用定理 `Subgroup.subgroupOf_eq_bot`：subgroupOf_eq_bot {H K : Subgroup G} : H.sub
groupOf K = ⊥ ↔ Disjoint H K

--- 原说明 ---
An extension of coprime Z-groups is a Z-group.
-/
theorem isZGroup_of_coprime [Finite G] [IsZGroup G] [IsZGroup G'']
    (h_le : f'.ker ≤ f.range) (h_cop : (Nat.card G).Coprime (Nat.card G'')) :
    IsZGroup G' := by
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  replace h_cop := (h_cop.of_dvd ((Subgroup.card_dvd_of_le h_le).trans
    (Subgroup.card_range_dvd f)) (Subgroup.index_ker f' ▸ f'.range.card_subgroup_dvd_card))
  rcases P.2.le_or_disjoint_of_coprime h_cop with h | h
  · replace h_le : P ≤ f.range := h.trans h_le
    suffices IsCyclic (P.subgroupOf f.range) by
      have key := Subgroup.subgroupOfEquivOfLe h_le
      exact isCyclic_of_surjective key key.surjective
    obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective p (P.subtype h_le)
    rw [Sylow.ext_iff, Sylow.coe_mapSurjective, Sylow.coe_subtype] at hQ
    exact hQ ▸ isCyclic_of_surjective _ (f.rangeRestrict.subgroupMap_surjective Q)
  · have := (P.2.map f').isCyclic_of_isZGroup
    apply isCyclic_of_injective (f'.subgroupMap P)
    rwa [← MonoidHom.ker_eq_bot_iff, P.ker_subgroupMap f', Subgroup.subgroupOf_eq_bot]

/-- A finite group `G` is a Z-group if and only if `G` is isomorphic to a semidirect product of two
  cyclic subgroups of coprime order. -/
/-
**isZGroup_iff_exists_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isZGroup_iff_exists_mulEquiv [Finite G] : IsZGroup G ↔ exists (N H : Subgr
oup G) (φ : H ->* MulAut N) (_ : G ≃* N ⋊[φ] H), IsCyclic H ∧ IsCyclic N ∧ (Nat.
card N).Coprime (Nat.card H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.exists_right_complement'_of_coprime`：∀ {G : Type u} [inst : Gro
up G] {N : Subgroup G} [N.Normal], (Nat.card ↥N).Coprime N.index → ∃ H, N.IsComp
lement' H
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
· 使用定理 `IsZGroup.coprime_commutator_index`：IsZGroup.coprime_commutator_index [Fi
nite G] [IsZGroup G] : (Nat.card (commutator G)).Coprime (commutator G).index
· 使用定理 `Subgroup.IsComplement'.symm`：∀ {G : Type u_1} [inst : Group G] {H K : Su
bgroup G}, H.IsComplement' K → K.IsComplement' H
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `IsZGroup.isCyclic_commutator`：isCyclic_commutator [Finite G] [IsZGroup G
] : IsCyclic (commutator G)
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `isZGroup_of_coprime`：isZGroup_of_coprime [Finite G] [IsZGroup G] [IsZGro
up G''] (h_le : f'.ker <= f.range) (h_cop : (Nat.card G).Coprime (Nat.card G''))
 : IsZGro…
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `IsZGroup.instOfIsCyclic`：∀ {G : Type u_1} [inst : Group G] [IsCyclic G],
 IsZGroup G
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `SemidirectProduct.range_inl_eq_ker_rightHom`：range_inl_eq_ker_rightHom :
 (inl : N ->* N ⋊[φ] G).range = rightHom.ker
· 使用定理 `IsZGroup.of_injective`：of_injective [hG' : IsZGroup G'] (hf : Function.I
njective f) : IsZGroup G
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e

--- 原说明 ---
A finite group `G` is a Z-group if and only if `G` is isomorphic to a semidirect
 product of two
  cyclic subgroups of coprime order.
-/
theorem isZGroup_iff_exists_mulEquiv [Finite G] :
    IsZGroup G ↔ ∃ (N H : Subgroup G) (φ : H →* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) := by
  refine ⟨fun hG ↦ ?_, ?_⟩
  · obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hG.coprime_commutator_index
    have h1 : Abelianization G ≃* H := hH.symm.QuotientMulEquiv
    refine ⟨commutator G, H, _, (SemidirectProduct.mulEquivSubgroup hH).symm,
      isCyclic_of_surjective _ h1.surjective, hG.isCyclic_commutator, ?_⟩
    exact Nat.card_congr h1.toEquiv ▸ hG.coprime_commutator_index
  · rintro ⟨N, H, φ, e, hH, hN, hHN⟩
    have : IsZGroup (N ⋊[φ] H) :=
      isZGroup_of_coprime SemidirectProduct.range_inl_eq_ker_rightHom.ge hHN
    exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective

end Classification

