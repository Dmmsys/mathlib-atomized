/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `Sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `Sylow.exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
  where `n` is the multiplicity of `p` in the group order.
* `Sylow.isPretransitive_of_finite`: a generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modEq_one`: a generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

@[expose] public section


open MulAction Subgroup

section InfiniteSylow

variable (p : ℕ) (G : Type*) [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
/-
**Sylow** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → (G : Type u_1) → [Group G] → Type u_1
参数：G : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Sylow `p`-subgroup is a maximal `p`-subgroup.
-/
structure Sylow extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → toSubgroup ≤ Q → Q = toSubgroup

variable {p} {G}

namespace Sylow

attribute [coe] toSubgroup

/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[ext]
/-
**Sylow.ext** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q
参数：h : (P : Subgroup G) = Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr
/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Sylow p G) G where
  coe := (↑)
  coe_injective _ _ h := ext (SetLike.coe_injective h)
/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Sylow p G) := .ofSetLike (Sylow p G) G
/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

@[simp]
/-
**Sylow.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G), ↑↑P = ↑P
参数：P : Sylow p G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe (P : Sylow p G) : (P : Subgroup G) = (P : Set G) :=
  rfl

/-- A `p`-subgroup with index indivisible by `p` is a Sylow subgroup. -/
/-
**Sylow._root_.IsPGroup.toSylow** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `p`-subgroup with index indivisible by `p` is a Sylow subgroup.
-/
def _root_.IsPGroup.toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : Sylow p G :=
  { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have : P.FiniteIndex := ⟨fun h ↦ hP2 (h ▸ (dvd_zero p))⟩
      obtain ⟨k, hk⟩ := (hQ.to_quotient (P.normalCore.subgroupOf Q)).exists_card_eq
      have h := hk ▸ Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hP2
      exact le_antisymm (Subgroup.relIndex_eq_one.mp
        (Nat.eq_one_of_dvd_coprimes h (Subgroup.relIndex_dvd_index_of_le hPQ)
        (Subgroup.relIndex_dvd_of_le_left Q P.normalCore_le))) hPQ }
/-
**Sylow._root_.IsPGroup.toSylow_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.IsPGroup.toSylow_coe [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : (hP1.toSylow hP2) = P :=
  rfl
/-
**Sylow._root_.IsPGroup.mem_toSylow** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.IsPGroup.mem_toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) {g : G} : g ∈ hP1.toSylow hP2 ↔ g ∈ P :=
  .rfl
/-
**Sylow._root_.IsPGroup.le_sylow_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsPGroup.le_sylow_of_normal {N : Subgroup G} [N.Normal] (h : IsPGroup p N)
    (H : Sylow p G) : N ≤ H :=
  sup_eq_right.mp <| H.is_maximal' (h.to_sup_of_normal_left H.isPGroup') le_sup_right

/-- A subgroup with cardinality `p ^ n` is a Sylow subgroup
where `n` is the multiplicity of `p` in the group order. -/
/-
**Sylow.ofCard** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：ofCard [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G) (card_eq : Nat
.card H = p ^ (Nat.card G).factorization p) : Sylow p G
参数：H : Subgroup G；card_eq : Nat.card H = p ^ (Nat.card G).factorization p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup with cardinality `p ^ n` is a Sylow subgroup
where `n` is the multiplicity of `p` in the group order.
-/
def ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G :=
  (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne', card_mul_index, card_eq, ← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]
/-
**Sylow.coe_ofCard** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_ofCard [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G) (card_eq :
 Nat.card H = p ^ (Nat.card G).factorization p) : ofCard H card_eq = H
参数：H : Subgroup G；card_eq : Nat.card H = p ^ (Nat.card G).factorization p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : ofCard H card_eq = H :=
  rfl
/-
**Sylow.eq_top_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：eq_top_of_zero (H : Sylow 0 G) : (H : Subgroup G) = ⊤
参数：H : Sylow 0 G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `IsPGroup.zero`：∀ (G : Type u_1) [inst : Group G], IsPGroup 0 G
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem eq_top_of_zero (H : Sylow 0 G) : (H : Subgroup G) = ⊤ :=
  (H.is_maximal' (.zero _) le_top).symm
/-
**Sylow.eq_bot_of_one** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：eq_bot_of_one (H : Sylow 1 G) : (H : Subgroup G) = ⊥
参数：H : Sylow 1 G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPGroup_one_iff_subsingleton`：∀ {G : Type u_1} [inst : Group G], IsPGro
up 1 G ↔ Subsingleton G
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥
-/
theorem eq_bot_of_one (H : Sylow 1 G) : (H : Subgroup G) = ⊥ :=
  have := isPGroup_one_iff_subsingleton.mp H.isPGroup'
  eq_bot_of_subsingleton _

/-- The type of Sylow `p`-subgroups depends only on the prime factors of `p`. -/
/-
**Sylow.equivProdPrimeFactors** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：equivProdPrimeFactors (h : p != 0) : Sylow p G ≃ Sylow (p.primeFactors.pro
d id) G where toFun H
参数：h : p != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Sylow `p`-subgroups depends only on the prime factors of `p`.
-/
def equivProdPrimeFactors (h : p ≠ 0) : Sylow p G ≃ Sylow (p.primeFactors.prod id) G where
  toFun H := { H with
    isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h |>.mp H.isPGroup',
    is_maximal' hQ := H.is_maximal' <| isPGroup_iff_isPGroup_prod_primeFactors h |>.mpr hQ }
  invFun H := { H with
    isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h |>.mpr H.isPGroup',
    is_maximal' hQ := H.is_maximal' <| isPGroup_iff_isPGroup_prod_primeFactors h |>.mp hQ }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/-
**Sylow.coe_equivProdPrimeFactors_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_equivProdPrimeFactors_apply (h : p != 0) (H : Sylow p G) : (equivProdP
rimeFactors h H : Subgroup G) = H
参数：h : p != 0；H : Sylow p G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivProdPrimeFactors_apply (h : p ≠ 0) (H : Sylow p G) :
    (equivProdPrimeFactors h H : Subgroup G) = H :=
  rfl

@[simp]
/-
**Sylow.coe_symm_equivProdPrimeFactors_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_symm_equivProdPrimeFactors_apply (h : p != 0) (H : Sylow (p.primeFacto
rs.prod id) G) : (equivProdPrimeFactors h |>.symm H : Subgroup G) = H
参数：h : p != 0；H : Sylow (p.primeFactors.prod id) G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_equivProdPrimeFactors_apply (h : p ≠ 0) (H : Sylow (p.primeFactors.prod id) G) :
    (equivProdPrimeFactors h |>.symm H : Subgroup G) = H :=
  rfl

variable (P : Sylow p G)

variable {K : Type*} [Group K] (ϕ : K →* G) {N : Subgroup G}

/-- The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow subgroup. -/
/-
**Sylow.comapOfKerIsPGroup** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range) : Sylow p K
参数：hϕ : IsPGroup p ϕ.ker；h : P <= ϕ.range。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow 
subgroup.
-/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp]
/-
**Sylow.coe_comapOfKerIsPGroup** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range) : P.coma
pOfKerIsPGroup ϕ hϕ h = P.comap ϕ
参数：hϕ : IsPGroup p ϕ.ker；h : P <= ϕ.range。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) :
    P.comapOfKerIsPGroup ϕ hϕ h = P.comap ϕ :=
  rfl

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup. -/
/-
**Sylow.comapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：comapOfInjective (hϕ : Function.Injective ϕ) (h : P <= ϕ.range) : Sylow p 
K
参数：hϕ : Function.Injective ϕ；h : P <= ϕ.range。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.ker_isPGroup_of_injective`：ker_isPGroup_of_injective {K : Type*
} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ) : IsPGroup p ϕ.ker

--- 原说明 ---
The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subg
roup.
-/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) : Sylow p K :=
  P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]
/-
**Sylow.coe_comapOfInjective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : P <= ϕ.range) : P.co
mapOfInjective ϕ hϕ h = P.comap ϕ
参数：hϕ : Function.Injective ϕ；h : P <= ϕ.range。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) :
    P.comapOfInjective ϕ hϕ h = P.comap ϕ :=
  rfl

/-- A sylow subgroup of G is also a sylow subgroup of a subgroup of G. -/
/-
**Sylow.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：{p : ℕ} → {G : Type u_1} → [inst : Group G] → (P : Sylow p G) → {N : Subgr
oup G} → ↑P ≤ N → Sylow p ↥N
参数：P : Sylow p G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sylow subgroup of G is also a sylow subgroup of a subgroup of G.
-/
protected def subtype (h : P ≤ N) : Sylow p N :=
  P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]
/-
**Sylow.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_subtype (h : P <= N) : P.subtype h = subgroupOf P N
参数：h : P <= N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype (h : P ≤ N) : P.subtype h = subgroupOf P N :=
  rfl
/-
**Sylow.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：subtype_injective {P Q : Sylow p G} {hP : P <= N} {hQ : Q <= N} (h : P.sub
type hP = Q.subtype hQ) : P = Q
参数：h : P.subtype hP = Q.subtype hQ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem subtype_injective {P Q : Sylow p G} {hP : P ≤ N} {hQ : Q ≤ N}
    (h : P.subtype hP = Q.subtype hQ) : P = Q := by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩

end Sylow

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
/-
**IsPGroup.exists_le_sylow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : exists Q :
 Sylow p G, P <= Q
参数：hP : IsPGroup p P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Maximal.eq_of_ge`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → y = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
-/
theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{  carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_} _ ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine Exists.imp (fun k hk => ?_) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk ⊢, fun M hM _ hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun {Q} h => ⟨⟨Q, h.2.prop, h.2.eq_of_ge⟩, h.1⟩

namespace Sylow

/-
**Sylow.nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
形式化陈述：nonempty : Nonempty (Sylow p G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `IsPGroup.exists_le_sylow`：IsPGroup.exists_le_sylow {P : Subgroup G} (hP 
: IsPGroup p P) : exists Q : Sylow p G, P <= Q
· 使用定理 `IsPGroup.of_bot`：of_bot : IsPGroup p (⊥ : Subgroup G)
-/
instance nonempty : Nonempty (Sylow p G) :=
  IsPGroup.of_bot.exists_le_sylow.nonempty
/-
**Sylow.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
形式化陈述：inhabited : Inhabited (Sylow p G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance inhabited : Inhabited (Sylow p G) :=
  Classical.inhabited_of_nonempty nonempty
/-
**Sylow.exists_comap_eq_of_ker_isPGroup** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f :
 H ->* G} (hf : IsPGroup p f.ker) : exists Q : Sylow p G, Q.comap f = P
参数：P : Sylow p H；hf : IsPGroup p f.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `IsPGroup.comap_of_ker_isPGroup`：comap_of_ker_isPGroup {H : Subgroup G} (
hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G) (hϕ : IsPGroup p ϕ.ker) :
 IsPGroup p (H.comap…
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `IsPGroup.exists_le_sylow`：IsPGroup.exists_le_sylow {P : Subgroup G} (hP 
: IsPGroup p P) : exists Q : Sylow p G, P <= Q
· 使用定理 `IsPGroup.map`：map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Grou
p K] (ϕ : G ->* K) : IsPGroup p (H.map ϕ)
-/
theorem exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : IsPGroup p f.ker) : ∃ Q : Sylow p G, Q.comap f = P :=
  Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow
/-
**Sylow.exists_comap_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H 
->* G} (hf : Function.Injective f) : exists Q : Sylow p G, Q.comap f = P
参数：P : Sylow p H；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.exists_comap_eq_of_ker_isPGroup`：exists_comap_eq_of_ker_isPGroup {
H : Type*} [Group H] (P : Sylow p H) {f : H ->* G} (hf : IsPGroup p f.ker) : exi
sts Q : Sylow p G, Q.comap …
· 使用定理 `IsPGroup.ker_isPGroup_of_injective`：ker_isPGroup_of_injective {K : Type*
} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ) : IsPGroup p ϕ.ker
-/
theorem exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : Function.Injective f) : ∃ Q : Sylow p G, Q.comap f = P :=
  P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)
/-
**Sylow.exists_comap_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) : exists Q : Sylo
w p G, Q.comap H.subtype = P
参数：P : Sylow p H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.exists_comap_eq_of_injective`：exists_comap_eq_of_injective {H : Ty
pe*} [Group H] (P : Sylow p H) {f : H ->* G} (hf : Function.Injective f) : exist
s Q : Sylow p G, Q.comap…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    ∃ Q : Sylow p G, Q.comap H.subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective
/-
**Sylow.iSup_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：iSup_of_normal {ι : Type*} (H : ι -> Subgroup G) [forall i, (H i).Normal] 
(h : forall i, IsPGroup p (H i)) : IsPGroup p (⨆ i, H i : Subgroup G)
参数：H : ι -> Subgroup G；H i；h : forall i, IsPGroup p (H i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_le`：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <=
 K) : IsPGroup p H
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `IsPGroup.le_sylow_of_normal`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {
N : Subgroup G} [N.Normal], IsPGroup p ↥N → ∀ (H : Sylow p G), N ≤ ↑H
-/
theorem iSup_of_normal {ι : Type*} (H : ι → Subgroup G) [∀ i, (H i).Normal]
    (h : ∀ i, IsPGroup p (H i)) : IsPGroup p (⨆ i, H i : Subgroup G) :=
  have H' := Classical.arbitrary <| Sylow p G
  H'.isPGroup'.to_le <| iSup_le (h · |>.le_sylow_of_normal H')
/-
**Sylow.biSup_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：biSup_of_normal {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall 
i in s, IsPGroup p (H i)) (hn : forall i in s, (H i).Normal) : IsPGroup p (⨆ i i
n s, H i : Subgroup G)
参数：s : Set ι；H : ι -> Subgroup G；h : forall i in s, IsPGroup p (H i)；hn : forall
 i in s, (H i).Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Sylow.iSup_of_normal`：iSup_of_normal {ι : Type*} (H : ι -> Subgroup G) [
forall i, (H i).Normal] (h : forall i, IsPGroup p (H i)) : IsPGroup p (⨆ i, H i 
: Subgroup…
-/
theorem biSup_of_normal {ι : Type*} (s : Set ι) (H : ι → Subgroup G) (h : ∀ i ∈ s, IsPGroup p (H i))
    (hn : ∀ i ∈ s, (H i).Normal) : IsPGroup p (⨆ i ∈ s, H i : Subgroup G) := by
  rw [← iSup_subtype'']
  have : ∀ i : s, (H i).Normal := fun i ↦ hn i i.property
  exact iSup_of_normal _ fun i ↦ h i i.property
/-
**Sylow.sSup_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：sSup_of_normal (Hs : Set (Subgroup G)) (h : forall H in Hs, IsPGroup p H) 
(hn : forall H in Hs, H.Normal) : IsPGroup p (sSup Hs : Subgroup G)
参数：Hs : Set (Subgroup G)；h : forall H in Hs, IsPGroup p H；hn : forall H in Hs, H
.Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Sylow.biSup_of_normal`：biSup_of_normal {ι : Type*} (s : Set ι) (H : ι ->
 Subgroup G) (h : forall i in s, IsPGroup p (H i)) (hn : forall i in s, (H i).No
rmal) : IsP…
-/
theorem sSup_of_normal (Hs : Set (Subgroup G)) (h : ∀ H ∈ Hs, IsPGroup p H)
    (hn : ∀ H ∈ Hs, H.Normal) : IsPGroup p (sSup Hs : Subgroup G) := by
  rw [sSup_eq_iSup]
  exact biSup_of_normal Hs id h hn

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
/-
**Sylow.finite_of_ker_is_pGroup** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：finite_of_ker_is_pGroup {H : Type*} [Group H] {f : H ->* G} (hf : IsPGroup
 p f.ker) [Finite (Sylow p G)] : Finite (Sylow p H)
参数：hf : IsPGroup p f.ker；Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.exists_comap_eq_of_ker_isPGroup`：exists_comap_eq_of_ker_isPGroup {
H : Type*} [Group H] (P : Sylow p H) {f : H ->* G} (hf : IsPGroup p f.ker) : exi
sts Q : Sylow p G, Q.comap …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Sylow.ext`：ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
If the kernel of `f : H →* G` is a `p`-group,
  then `Finite (Sylow p G)` implies `Finite (Sylow p H)`.
-/
theorem finite_of_ker_is_pGroup {H : Type*} [Group H] {f : H →* G}
    (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H → Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : ∀ P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [← hg, h]; exact (h_exists Q).choose_spec)

/-- If `f : H →* G` is injective, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
/-
**Sylow.finite_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：finite_of_injective {H : Type*} [Group H] {f : H ->* G} (hf : Function.Inj
ective f) [Finite (Sylow p G)] : Finite (Sylow p H)
参数：hf : Function.Injective f；Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.finite_of_ker_is_pGroup`：finite_of_ker_is_pGroup {H : Type*} [Grou
p H] {f : H ->* G} (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow 
p H)
· 使用定理 `IsPGroup.ker_isPGroup_of_injective`：ker_isPGroup_of_injective {K : Type*
} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ) : IsPGroup p ϕ.ker

--- 原说明 ---
If `f : H →* G` is injective, then `Finite (Sylow p G)` implies `Finite (Sylow p
 H)`.
-/
theorem finite_of_injective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

/-- If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p 
H)`.
-/
instance (H : Subgroup G) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_injective H.subtype_injective

/-- If a Sylow `p`-subgroup has finite index, then the number of Sylow `p`-subgroups is finite. -/
/-
**Sylow.finite_of_finiteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：finite_of_finiteIndex (P : Sylow p G) [P.FiniteIndex] : Finite (Sylow p G)
参数：P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.finite_of_ker_is_pGroup`：finite_of_ker_is_pGroup {H : Type*} [Grou
p H] {f : H ->* G} (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow 
p H)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `IsPGroup.to_le`：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <=
 K) : IsPGroup p H
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A

--- 原说明 ---
If a Sylow `p`-subgroup has finite index, then the number of Sylow `p`-subgroups
 is finite.
-/
theorem finite_of_finiteIndex (P : Sylow p G) [P.FiniteIndex] : Finite (Sylow p G) := by
  apply finite_of_ker_is_pGroup (f := QuotientGroup.mk' P.normalCore)
  rw [QuotientGroup.ker_mk']
  exact P.isPGroup'.to_le P.normalCore_le

open scoped Pointwise

/-- `Subgroup.pointwiseMulAction` preserves Sylow subgroups. -/
/-
**Sylow.pointwiseMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
形式化陈述：pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] : MulAc
tion α (Sylow p G) where smul g P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subgroup.pointwiseMulAction` preserves Sylow subgroups.
-/
instance pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] :
    MulAction α (Sylow p G) where
  smul g P :=
    ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· ∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSubgroup)
  mul_smul g h P := ext (mul_smul g h P.toSubgroup)
/-
**Sylow.pointwise_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
 {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
    {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G) :=
  rfl
/-
**Sylow.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
形式化陈述：mulAction : MulAction G (Sylow p G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj
/-
**Sylow.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl
/-
**Sylow.coe_subgroup_smul** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_subgroup_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P 
: Subgroup G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subgroup_smul {g : G} {P : Sylow p G} :
    ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl
/-
**Sylow.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl
/-
**Sylow.smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：smul_le {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H) : ↑(h • P) 
<= H
参数：hP : P <= H；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.conj_smul_le_of_le`：conj_smul_le_of_le {P H : Subgroup G} (hP :
 P <= H) (h : H) : MulAut.conj (h : G) • P <= H
-/
theorem smul_le {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) : ↑(h • P) ≤ H :=
  Subgroup.conj_smul_le_of_le hP h
/-
**Sylow.smul_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H) : h • 
P.subtype hP = (h • P).subtype (smul_le hP h)
参数：hP : P <= H；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.ext`：ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q
· 使用定理 `Sylow.smul_le`：smul_le {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h
 : H) : ↑(h • P) <= H
· 使用定理 `Subgroup.conj_smul_subgroupOf`：conj_smul_subgroupOf {P H : Subgroup G} (
hP : P <= H) (h : H) : MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P
).subgroupOf H
-/
theorem smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) :
    h • P.subtype hP = (h • P).subtype (smul_le hP h) :=
  ext (Subgroup.conj_smul_subgroupOf hP h)
/-
**Sylow.smul_eq_iff_mem_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} : g • P = P ↔ g in norm
alizer P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_set_normalizer_iff`：mem_set_normalizer_iff : g in normalize
r S ↔ forall h, h in S ↔ g * h * g⁻¹ in S
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `iff_congr`：∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ 
(p₂ ↔ q₂))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulDistribMulAction.toMonoidEnd_apply`：∀ (M : Type u_2) (A : Type u_3) [
inst : Monoid M] [inst_1 : Monoid A] [inst_2 : MulDistribMulAction M A] (r : M),
   (MulDistribMulAction.toM…
· 使用定理 `MulDistribMulAction.toMonoidHom_apply`：∀ {M : Type u_2} (A : Type u_3) [
inst : Monoid M] [inst_1 : Monoid A] [inst_2 : MulDistribMulAction M A] (r : M) 
  (x : A), (MulDistribMulAc…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulAut.apply_inv_self`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m
 : M), e (e⁻¹ m) = m
-/
theorem smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} :
    g • P = P ↔ g ∈ normalizer P := by
  rw [eq_comm, SetLike.ext_iff, ← inv_mem_iff (G := G) (H := normalizer P),
      mem_set_normalizer_iff, inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
/-
**Sylow.smul_eq_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：smul_eq_of_normal {g : G} {P : Sylow p G} [h : P.Normal] : g • P = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
-/
theorem smul_eq_of_normal {g : G} {P : Sylow p G} [h : P.Normal] : g • P = P := by
  simp only [smul_eq_iff_mem_normalizer, ← P.coe_coe, P.normalizer_eq_top, mem_top]

end Sylow

/-
**Subgroup.sylow_mem_fixedPoints_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} : P in
 fixedPoints H (Sylow p G) ↔ H <= normalizer P
参数：H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ fixedPoints H (Sylow p G) ↔ H ≤ normalizer P := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall
/-
**IsPGroup.inf_normalizer_sylow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sy
low p G) : P ⊓ normalizer Q = P ⊓ Q
参数：hP : IsPGroup p P；Q : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `IsPGroup.to_sup_of_normal_right'`：to_sup_of_normal_right' {H K : Subgrou
p G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : H <= Subgroup.normalizer K) 
: IsPGroup p (H ⊔ K : …
· 使用定理 `IsPGroup.to_inf_left`：to_inf_left {H K : Subgroup G} (hH : IsPGroup p H)
 : IsPGroup p (H ⊓ K : Subgroup G)
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
-/
theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P ⊓ normalizer Q = P ⊓ Q :=
  le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)
/-
**IsPGroup.sylow_mem_fixedPoints_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q
 : Sylow p G} : Q in fixedPoints P (Sylow p G) ↔ P <= Q
参数：hP : IsPGroup p P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.sylow_mem_fixedPoints_iff`：Subgroup.sylow_mem_fixedPoints_iff (
H : Subgroup G) {P : Sylow p G} : P in fixedPoints H (Sylow p G) ↔ H <= normaliz
er P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `IsPGroup.inf_normalizer_sylow`：IsPGroup.inf_normalizer_sylow {P : Subgro
up G} (hP : IsPGroup p P) (Q : Sylow p G) : P ⊓ normalizer Q = P ⊓ Q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by
  rw [P.sylow_mem_fixedPoints_iff, ← inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
/-
**Sylow.isPretransitive_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sylow.isPretransitive_of_finite [hp : Fact p.Prime] [Finite (Sylow p G)] :
 IsPretransitive G (Sylow p G)
参数：Sylow p G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `IsPGroup.sylow_mem_fixedPoints_iff`：IsPGroup.sylow_mem_fixedPoints_iff {
P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} : Q in fixedPoints P (Sylow 
p G) ↔ P <= Q
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card`：nonempty_fixed_poin
t_of_prime_not_dvd_card (α) [MulAction G α] (hpα : ¬p ∣ Nat.card α) : (fixedPoin
ts G α).Nonempty
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Sylow.ext`：ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups a
re conjugate.
-/
instance Sylow.isPretransitive_of_finite [hp : Fact p.Prime] [Finite (Sylow p G)] :
    IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc
        S ∈ fixedPoints R (orbit G P) ↔ S.1 ∈ fixedPoints R (Sylow p G) :=
          forall_congr' fun a => Subtype.ext_iff
        _ ↔ R.1 ≤ S := R.2.sylow_mem_fixedPoints_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
    suffices Set.Nonempty (fixedPoints Q (orbit G P)) by
      exact Exists.elim this fun R hR => by
        rw [← Sylow.ext (H.mp hR)]
        exact R.2
    apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
    refine fun h => hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.mp ?_)
    calc
      1 = Nat.card (fixedPoints P (orbit G P)) := ?_
      _ ≡ Nat.card (orbit G P) [MOD p] := (P.2.card_modEq_card_fixedPoints (orbit G P)).symm
      _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    rw [← Nat.card_unique (α := ({⟨P, mem_orbit_self P⟩} : Set (orbit G P))), eq_comm]
    congr
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
/-
**card_sylow_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow p G)] : Nat.card (Sylow
 p G) ≡ 1 [MOD p]
参数：Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsPGroup.sylow_mem_fixedPoints_iff`：IsPGroup.sylow_mem_fixedPoints_iff {
P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} : Q in fixedPoints P (Sylow 
p G) ↔ P <= Q
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Sylow.ext_iff`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {P Q : Sylow p 
G}, P = Q ↔ ↑P = ↑Q
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]
· 使用定理 `Nat.ModEq.refl`：∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]

--- 原说明 ---
A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` mo
dulo `p`.
-/
theorem card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  refine Sylow.nonempty.elim fun P : Sylow p G => ?_
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q ∈ fixedPoints P (Sylow p G) ↔ P.1 ≤ Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q ∈ {P} := Sylow.ext_iff.symm.trans Set.mem_singleton_iff.symm
  have : Nat.card (fixedPoints P.1 (Sylow p G)) = 1 := by simp [this]
  exact (P.2.card_modEq_card_fixedPoints (Sylow p G)).trans (by rw [this])
/-
**not_dvd_card_sylow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] : ¬p ∣ Nat.car
d (Sylow p G)
参数：Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `card_sylow_modEq_one`：card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow
 p G)] : Nat.card (Sylow p G) ≡ 1 [MOD p]
-/
theorem not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] : ¬p ∣ Nat.card (Sylow p G) :=
  fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

variable {p} {G}

namespace Sylow

/-- Sylow subgroups are isomorphic -/
nonrec def equivSMul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSMul (MulAut.conj g) P.toSubgroup

/-- Sylow subgroups are isomorphic -/
/-
**Sylow.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q
参数：Sylow p G；P Q : Sylow p G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sylow subgroups are isomorphic
-/
noncomputable def equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))

@[simp]
/-
**Sylow.orbit_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G
 P = ⊤
参数：Sylow p G；P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
-/
theorem orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q _ => exists_smul_eq G P Q
/-
**Sylow.stabilizer_eq_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：stabilizer_eq_normalizer (P : Sylow p G) : stabilizer G P = normalizer P
参数：P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = normalizer P := by
  ext; simp [smul_eq_iff_mem_normalizer]
/-
**Sylow.conj_eq_normalizer_conj_of_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Sy
low`。
形式化陈述：conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p
 G)] (P : Sylow p G) (x g : G) (hx : x in centralizer P) (hy : g⁻¹ * x * g in ce
ntralizer P) : exists n in normalizer P, g⁻¹ * x * g = n⁻¹ * x * n
参数：Sylow p G；P : Sylow p G；x g : G；hx : x in centralizer P；hy : g⁻¹ * x * g in c
entralizer P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.le_centralizer_iff`：le_centralizer_iff : H <= centralizer K ↔ K
 <= centralizer H
· 使用定理 `Subgroup.zpowers_le`：zpowers_le {g : G} {H : Subgroup G} : zpowers g <= 
H ↔ g in H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Sylow.instFiniteSubtypeMemSubgroup`：∀ {p : ℕ} {G : Type u_1} [inst : Gro
up G] (H : Subgroup G) [Finite (Sylow p G)], Finite (Sylow p ↥H)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sylow.smul_eq_iff_mem_normalizer`：smul_eq_iff_mem_normalizer {g : G} {P 
: Sylow p G} : g • P = P ↔ g in normalizer P
· 使用定理 `Sylow.subtype_injective`：subtype_injective {P Q : Sylow p G} {hP : P <= 
N} {hQ : Q <= N} (h : P.subtype hP = Q.subtype hQ) : P = Q
· 使用定理 `Sylow.smul_le`：smul_le {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h
 : H) : ↑(h • P) <= H
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sylow.subtype.congr_simp`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P P
_1 : Sylow p G) (e_P : P = P_1) {N : Subgroup G} (h : ↑P ≤ N),   P.subtype h = P
_1.subtype ⋯
· 使用定理 `Sylow.smul_subtype`：smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : 
P <= H) (h : H) : h • P.subtype hP = (h • P).subtype (smul_le hP h)
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (x g : G) (hx : x ∈ centralizer P)
    (hy : g⁻¹ * x * g ∈ centralizer P) :
    ∃ n ∈ normalizer P, g⁻¹ * x * g = n⁻¹ * x * n := by
  have h1 : P ≤ centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) ≤ centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff, zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc,
      eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc] at hy
  obtain ⟨h, hh⟩ :=
    exists_smul_eq (centralizer (zpowers x : Set G)) ((g • P).subtype h2) (P.subtype h1)
  simp_rw [smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨h * g, smul_eq_iff_mem_normalizer.mp (subtype_injective hh), ?_⟩
  rw [← mul_assoc, Commute.right_comm (h.prop x (mem_zpowers x)), mul_inv_rev, inv_mul_cancel_right]
/-
**Sylow.conj_eq_normalizer_conj_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sy
low p G) [_hP : IsMulCommutative P] (x g : G) (hx : x in P) (hy : g⁻¹ * x * g in
 P) : exists n in normalizer P, g⁻¹ * x * g = n⁻¹ * x * n
参数：Sylow p G；P : Sylow p G；x g : G；hx : x in P；hy : g⁻¹ * x * g in P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.conj_eq_normalizer_conj_of_mem_centralizer`：conj_eq_normalizer_con
j_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) (x g : 
G) (hx : x in centralizer P) (hy : g⁻¹…
· 使用定理 `Subgroup.le_centralizer`：le_centralizer [h : IsMulCommutative H] : H <= 
centralizer H
-/
theorem conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    [_hP : IsMulCommutative P] (x g : G) (hx : x ∈ P) (hy : g⁻¹ * x * g ∈ P) :
    ∃ n ∈ normalizer P, g⁻¹ * x * g = n⁻¹ * x * n :=
  P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
/-
**Sylow.equivQuotientNormalizer** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：equivQuotientNormalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G
) : Sylow p G ≃ G ⧸ normalizer P
参数：Sylow p G；P : Sylow p G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p
`-subgroup
-/
noncomputable def equivQuotientNormalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Sylow p G ≃ G ⧸ normalizer P :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ normalizer P := by rw [P.stabilizer_eq_normalizer]
/-
**Sylow.** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Finite (G ⧸ normalizer P) :=
  Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer
/-
**Sylow.card_eq_card_quotient_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_eq_card_quotient_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : 
Sylow p G) : Nat.card (Sylow p G) = Nat.card (G ⧸ normalizer P)
参数：Sylow p G；P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_eq_card_quotient_normalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = Nat.card (G ⧸ normalizer P) :=
  Nat.card_congr P.equivQuotientNormalizer
/-
**Sylow.card_eq_index_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_eq_index_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p 
G) : Nat.card (Sylow p G) = (normalizer (P : Set G)).index
参数：Sylow p G；P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.card_eq_card_quotient_normalizer`：card_eq_card_quotient_normalizer
 [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : Nat.card (Sylow p G) = Na
t.card (G ⧸ normalizer P)
-/
theorem card_eq_index_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = (normalizer (P : Set G)).index :=
  P.card_eq_card_quotient_normalizer
/-
**Sylow.card_dvd_index** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : Nat.c
ard (Sylow p G) ∣ P.index
参数：Sylow p G；P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Sylow.card_eq_index_normalizer`：card_eq_index_normalizer [Fact p.Prime] 
[Finite (Sylow p G)] (P : Sylow p G) : Nat.card (Sylow p G) = (normalizer (P : S
et G)).index
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
-/
theorem card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

/-- Auxiliary lemma for `Sylow.not_dvd_index` which is strictly stronger. -/
/-
**Sylow.not_dvd_index_aux** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `Sylow.not_dvd_index` which is strictly stronger.
-/
private theorem not_dvd_index_aux [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
    [P.FiniteIndex] : ¬ p ∣ P.index := by
  intro h
  rw [P.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card (((Nat.card_zpowers x).trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q := by
    apply h.comap_of_ker_isPGroup
    rw [QuotientGroup.ker_mk']
    exact P.2
  replace hp := mt orderOf_eq_one_iff.mpr (ne_of_eq_of_ne hx hp.1.ne_one)
  rw [← zpowers_eq_bot, ← Ne, ← bot_lt_iff_ne_bot, ←
    comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective _), MonoidHom.comap_bot,
    QuotientGroup.ker_mk'] at hp
  exact hp.ne' (P.3 hQ hp.le)

/-- A Sylow p-subgroup has index indivisible by `p`, assuming [N(P) : P] < ∞. -/
/-
**Sylow.not_dvd_index'** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) (h
P : P.relIndex (normalizer P) != 0) : ¬ p ∣ P.index
参数：Sylow p G；P : Sylow p G；hP : P.relIndex (normalizer P) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Sylow.coe_coe`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G)
, ↑↑P = ↑P
· 使用定理 `Sylow.card_eq_index_normalizer`：card_eq_index_normalizer [Fact p.Prime] 
[Finite (Sylow p G)] (P : Sylow p G) : Nat.card (Sylow p G) = (normalizer (P : S
et G)).index
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
· 使用定理 `_private.Mathlib.GroupTheory.Sylow.0.Sylow.not_dvd_index_aux`：∀ {p : ℕ} 
{G : Type u_1} [inst : Group G] [hp : Fact (Nat.Prime p)] (P : Sylow p G) [(↑P).
Normal] [(↑P).FiniteIndex],   ¬p ∣ (↑P).index
· 使用定理 `Nat.Prime.not_dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → ¬p ∣ m → ¬p ∣ n → ¬p
 ∣ m * n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_dvd_card_sylow`：not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylo
w p G)] : ¬p ∣ Nat.card (Sylow p G)

--- 原说明 ---
A Sylow p-subgroup has index indivisible by `p`, assuming [N(P) : P] < ∞.
-/
theorem not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : P.relIndex (normalizer P) ≠ 0) : ¬ p ∣ P.index := by
  rw [← relIndex_mul_index le_normalizer, P.coe_coe, ← card_eq_index_normalizer]
  have : (P.subtype le_normalizer).Normal :=
    Subgroup.normal_in_normalizer
  have : (P.subtype le_normalizer).FiniteIndex := ⟨hP⟩
  replace hP := not_dvd_index_aux (P.subtype le_normalizer)
  exact hp.1.not_dvd_mul hP (not_dvd_card_sylow p G)

/-- A Sylow p-subgroup has index indivisible by `p`. -/
/-
**Sylow.not_dvd_index** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] : ¬ p ∣ P.ind
ex
参数：P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.finite_of_finiteIndex`：finite_of_finiteIndex (P : Sylow p G) [P.Fi
niteIndex] : Finite (Sylow p G)
· 使用定理 `Sylow.not_dvd_index'`：not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow 
p G)] (P : Sylow p G) (hP : P.relIndex (normalizer P) != 0) : ¬ p ∣ P.index
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A Sylow p-subgroup has index indivisible by `p`.
-/
theorem not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] :
    ¬ p ∣ P.index := by
  have := P.finite_of_finiteIndex
  exact P.not_dvd_index' Nat.card_pos.ne'

section mapSurjective

variable [Finite G] {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Surjective f)

/-- Surjective group homomorphisms map Sylow subgroups to Sylow subgroups. -/
/-
**Sylow.mapSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：mapSurjective [Fact p.Prime] (P : Sylow p G) : Sylow p G'
参数：P : Sylow p G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Surjective group homomorphisms map Sylow subgroups to Sylow subgroups.
-/
def mapSurjective [Fact p.Prime] (P : Sylow p G) : Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ ↦ ((P.2.map f).toSylow
      (fun h ↦ P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }
/-
**Sylow.coe_mapSurjective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [inst_1 : Finite G] {G' : Type u
_2} [inst_2 : Group G'] {f : G →* G'}   (hf : Function.Surjective ⇑f) [inst_3 : 
Fact (Nat.Prime p)] (P : Sylow p G),   ↑(Sylow.mapSurjective hf P) = Subgroup.ma
p f ↑P
参数：hf : Function.Surjective ⇑f；Nat.Prime p；P : Sylow p G；Sylow.mapSurjective hf 
P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mapSurjective [Fact p.Prime] (P : Sylow p G) : P.mapSurjective hf = P.map f :=
  rfl
/-
**Sylow.mapSurjective_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：mapSurjective_surjective (p : Nat) [Fact p.Prime] : Function.Surjective (S
ylow.mapSurjective hf : Sylow p G -> Sylow p G')
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.map_subtype_le`：map_subtype_le {H : Subgroup G} (K : Subgroup H
) : K.map H.subtype <= H
· 使用定理 `IsPGroup.map`：map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Grou
p K] (ϕ : G ->* K) : IsPGroup p (H.map ϕ)
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_map_subtype`：index_map_subtype {H : Subgroup G} (K : Subg
roup H) : (K.map H.subtype).index = K.index * H.index
· 使用定理 `Subgroup.index_comap_of_surjective`：index_comap_of_surjective {f : G' ->
* G} (hf : Function.Surjective f) : (H.comap f).index = H.index
· 使用定理 `Nat.Prime.not_dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → ¬p ∣ m → ¬p ∣ n → ¬p
 ∣ m * n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.ext_iff`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {P Q : Sylow p 
G}, P = Q ↔ ↑P = ↑Q
· 使用定理 `Sylow.coe_mapSurjective`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [inst
_1 : Finite G] {G' : Type u_2} [inst_2 : Group G'] {f : G →* G'}   (hf : Functio
n.Surjective …
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Sylow.is_maximal'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Syl
ow p G) {Q : Subgroup G}, IsPGroup p ↥Q → ↑self ≤ Q → Q = ↑self
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Subgroup.index_map_dvd`：index_map_dvd {f : G ->* G'} (hf : Function.Surj
ective f) : (H.map f).index ∣ H.index
-/
theorem mapSurjective_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G → Sylow p G') := by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q₀ : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q : Subgroup G := Q₀.map (P.comap f).subtype
  have hPQ : Q.map f ≤ P := Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le Q₀.1)
  have hpQ : IsPGroup p Q := Q₀.2.map (P.comap f).subtype
  have hQ : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_subtype Q₀.1, P.index_comap_of_surjective hf]
    exact Nat.Prime.not_dvd_mul Fact.out Q₀.not_dvd_index P.not_dvd_index
  use hpQ.toSylow hQ
  rw [Sylow.ext_iff, Sylow.coe_mapSurjective, eq_comm]
  exact ((hpQ.map f).toSylow (fun h ↦ hQ (h.trans (Q.index_map_dvd hf)))).3 P.2 hPQ

end mapSurjective

set_option backward.isDefEq.respectTransparency false in
/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
/-
**Sylow.normalizer_sup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normalizer_sup_eq_top {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal]
 [Finite (Sylow p N)] (P : Sylow p N) : normalizer (P.map N.subtype) ⊔ N = ⊤
参数：Sylow p N；P : Sylow p N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Subgroup.mul_mem_sup`：mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x i
n S) (hy : y in T) : x * y in S ⊔ T
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subgroup.mem_map_iff_mem`：mem_map_iff_mem {f : G ->* N} (hf : Function.I
njective f) {K : Subgroup G} {x : G} : f x in K.map f ↔ x in K
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subgroup.pointwise_smul_def`：pointwise_smul_def {a : α} (S : Subgroup G)
 : a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a)
· 使用定理 `Sylow.pointwise_smul_def`：pointwise_smul_def {α : Type*} [Group α] [MulD
istribMulAction α G] {g : α} {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G)
· 使用定理 `Sylow.ext_iff`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {P Q : Sylow p 
G}, P = Q ↔ ↑P = ↑Q
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MulAut.conjNormal_val`：∀ {G : Type u_3} [inst : Group G] {H : Subgroup G
} [inst_1 : H.Normal] {h : ↥H}, MulAut.conjNormal ↑h = MulAut.conj h
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Sylow.smul_def`：smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g
 • P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
**Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Syl
ow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`.
-/
theorem normalizer_sup_eq_top {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p N) :
    normalizer (P.map N.subtype) ⊔ N = ⊤ := by
  refine top_le_iff.mp fun g _ => ?_
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g, sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [smul_def, ← mul_smul, ← MulAut.conjNormal_val, ← MulAut.conjNormal.map_mul,
    Sylow.ext_iff, pointwise_smul_def, Subgroup.pointwise_smul_def] at hn
  have : Function.Injective (MulAut.conj (n * g)).toMonoidHom := (MulAut.conj (n * g)).injective
  refine fun x ↦ (mem_map_iff_mem this).symm.trans ?_
  rw [map_map, ← congr_arg (map N.subtype) hn, map_map]
  rfl

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
/-
**Sylow.normalizer_sup_eq_top'** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normalizer_sup_eq_top' {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal
] [Finite (Sylow p N)] (P : Sylow p G) (hP : P <= N) : normalizer P ⊔ N = ⊤
参数：Sylow p N；P : Sylow p G；hP : P <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sylow.normalizer_sup_eq_top`：normalizer_sup_eq_top {p : Nat} [Fact p.Pri
me] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)] (P : Sylow p N) : normalize
r (P.map N.subtyp…
· 使用定理 `Sylow.coe_subtype`：coe_subtype (h : P <= N) : P.subtype h = subgroupOf P
 N
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Sylow.coe_coe`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G)
, ↑↑P = ↑P

--- 原说明 ---
**Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Syl
ow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`.
-/
theorem normalizer_sup_eq_top' {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p G) (hP : P ≤ N) : normalizer P ⊔ N = ⊤ := by
  rw [← normalizer_sup_eq_top (P.subtype hP), P.coe_subtype, subgroupOf_map_subtype,
    inf_of_le_left hP, P.coe_coe]

end Sylow

end InfiniteSylow

open Equiv Equiv.Perm Finset Function List QuotientGroup

universe u

variable {G : Type u} [Group G]

/-
**QuotientGroup.card_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientGroup.card_preimage_mk (s : Subgroup G) (t : Set (G ⧸ s)) : Nat.ca
rd (QuotientGroup.mk ⁻¹' t) = Nat.card s * Nat.card t
参数：s : Subgroup G；t : Set (G ⧸ s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem QuotientGroup.card_preimage_mk (s : Subgroup G) (t : Set (G ⧸ s)) :
    Nat.card (QuotientGroup.mk ⁻¹' t) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod, Nat.card_congr (preimageMkEquivSubgroupProdSet _ _)]

namespace Sylow
/-
**Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer** 是 Mathlib 中的一个定理，位于
命名空间 `Sylow`。
形式化陈述：mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finit
e (H : Set G)] {x : G} : (x : G ⧸ H) in MulAction.fixedPoints H (G ⧸ H) ↔ x in n
ormalizer H
参数：H : Set G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_fixedPoints'`：mem_fixedPoints' {a : α} : a in fixedPoints 
M α ↔ forall a', a' in orbit M a -> a' = a
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_normalizer_fintype`：mem_normalizer_fintype {S : Set G} [Fin
ite S] {x : G} (h : forall n, n in S -> x * n * x⁻¹ in S) : x in Subgroup.normal
izer S
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finite (H : Set G)]
    {x : G} : (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n ∈ H) =>
        have : (n⁻¹ * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ ∈ H by
          rw [mul_inv_rev, inv_inv] at this
          convert! this
          rw [inv_inv]),
    fun hx : ∀ n : G, n ∈ H ↔ x * n * x⁻¹ ∈ H =>
    mem_fixedPoints'.2 fun y =>
      Quotient.inductionOn' y fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y ∈ H := QuotientGroup.eq.1 hb₂
          (inv_mem_iff (G := G)).1 <|
            (hx _).2 <|
              (mul_mem_cancel_left (inv_mem hb₁)).1 <| by
                rw [hx] at hb₂; simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

/-- The fixed points of the action of `H` on its cosets correspond to `normalizer H / H`. -/
/-
**Sylow.fixedPointsMulLeftCosetsEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)
] : MulAction.fixedPoints H (G ⧸ H) ≃ normalizer H ⧸ H.comap (normalizer (H : Se
t G)).subtype
参数：H : Subgroup G；H : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fixed points of the action of `H` on its cosets correspond to `normalizer H 
/ H`.
-/
def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)] :
    MulAction.fixedPoints H (G ⧸ H) ≃
      normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype :=
  @subtypeQuotientEquivQuotientSubtype G (· ∈ normalizer H) (_) (_)
    (· ∈ MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer (H : Set G)), leftRel_apply]
      rfl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`. -/
/-
**Sylow.card_quotient_normalizer_modEq_card_quotient** 是 Mathlib 中的一个定理，位于命名空间 `
Sylow`。
形式化陈述：card_quotient_normalizer_modEq_card_quotient [Finite G] {p : Nat} {n : Nat
} [hp : Fact p.Prime] {H : Subgroup G} (hH : Nat.card H = p ^ n) : Nat.card (nor
malizer H ⧸ H.comap (normalizer (H : Set G)).subtype) ≡ Nat.card (G ⧸ H) [MOD p]
参数：hH : Nat.card H = p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]
· 使用定理 `IsPGroup.of_card`：of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup
 p G
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex

--- 原说明 ---
If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is 
congruent
  mod `p` to the index of `H`.
-/
theorem card_quotient_normalizer_modEq_card_quotient [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) ≡
      Nat.card (G ⧸ H) [MOD p] := by
  rw [← Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`. -/
/-
**Sylow.card_normalizer_modEq_card** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_normalizer_modEq_card [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Pri
me] {H : Subgroup G} (hH : Nat.card H = p ^ n) : Nat.card (normalizer (H : Set G
)) ≡ Nat.card G [MOD p ^ (n + 1)]
参数：hH : Nat.card H = p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.ModEq.mul_right'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b *
 c [MOD n * c]
· 使用定理 `Sylow.card_quotient_normalizer_modEq_card_quotient`：card_quotient_normal
izer_modEq_card_quotient [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime] {H :
 Subgroup G} (hH : Nat.card H = p ^ n) :…

--- 原说明 ---
If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.
-/
theorem card_normalizer_modEq_card [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer (H : Set G)) ≡ Nat.card G [MOD p ^ (n + 1)] := by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H,
    card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H)), Nat.card_congr this,
    hH, pow_succ']
  exact (card_quotient_normalizer_modEq_card_quotient hH).mul_right' _

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
/-
**Sylow.prime_dvd_card_quotient_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：prime_dvd_card_quotient_normalizer [Finite G] {p : Nat} {n : Nat} [Fact p.
Prime] (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^
 n) : p ∣ Nat.card (normalizer (H : Set G) ⧸ H.comap (normalizer (H : Set G)).su
btype)
参数：hdvd : p ^ (n + 1) ∣ Nat.card G；hH : Nat.card H = p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Sylow.card_quotient_normalizer_modEq_card_quotient`：card_quotient_normal
izer_modEq_card_quotient [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime] {H :
 Subgroup G} (hH : Nat.card H = p ^ n) :…
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.mod_eq_zero_of_dvd`：∀ {m n : ℕ}, m ∣ n → n % m = 0
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a

--- 原说明 ---
If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer.
-/
theorem prime_dvd_card_quotient_normalizer [Finite G] {p : ℕ} {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ∣ Nat.card (normalizer (H : Set G) ⧸ H.comap (normalizer (H : Set G)).subtype) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm :
    s * p % p =
      Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) % p :=
    hcard ▸ (card_quotient_normalizer_modEq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
/-
**Sylow.prime_pow_dvd_card_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：prime_pow_dvd_card_normalizer [Finite G] {p : Nat} {n : Nat} [_hp : Fact p
.Prime] (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p 
^ n) : p ^ (n + 1) ∣ Nat.card (normalizer (H : Set G))
参数：hdvd : p ^ (n + 1) ∣ Nat.card G；hH : Nat.card H = p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Sylow.card_normalizer_modEq_card`：card_normalizer_modEq_card [Finite G] 
{p : Nat} {n : Nat} [hp : Fact p.Prime] {H : Subgroup G} (hH : Nat.card H = p ^ 
n) : Nat.card (normali…
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]

--- 原说明 ---
If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`.
-/
theorem prime_pow_dvd_card_normalizer [Finite G] {p : ℕ} {n : ℕ} [_hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ^ (n + 1) ∣ Nat.card (normalizer (H : Set G)) :=
  Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
/-
**Sylow.exists_subgroup_card_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_subgroup_card_pow_succ [Finite G] {p : Nat} {n : Nat} [hp : Fact p.
Prime] (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^
 n) : exists K : Subgroup G, Nat.card K = p ^ (n + 1) ∧ H <= K
参数：hdvd : p ^ (n + 1) ∣ Nat.card G；hH : Nat.card H = p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]
· 使用定理 `IsPGroup.of_card`：of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup
 p G
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.mod_eq_zero_of_dvd`：∀ {m n : ℕ}, m ∣ n → n % m = 0
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
· 使用定理 `exists_prime_orderOf_dvd_card'`：∀ {G : Type u_3} [inst : Group G] [Finit
e G] (p : ℕ) [hp : Fact (Nat.Prime p)], p ∣ Nat.card G → ∃ x, orderOf x = p
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用引理 `Nat.card_image_of_injective`：card_image_of_injective {f : α -> β} (hf : 
Injective f) (s : Set α) : Nat.card (f '' s) = Nat.card s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G`
-/
theorem exists_subgroup_card_pow_succ [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    ∃ K : Subgroup G, Nat.card K = p ^ (n + 1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm : s * p % p = Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) % p :=
    Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modEq_card_fixedPoints _
  have hm' : p ∣ Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) :=
    Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ H.subgroupOf (normalizer H) := (subgroupOfEquivOfLe le_normalizer).symm.toEquiv
  ⟨((zpowers x).comap (mk' (H.subgroupOf (normalizer H)))).map (normalizer H).subtype, by
    show Nat.card (Subgroup.map (normalizer (H : Set G)).subtype
      (comap (mk' (H.subgroupOf (normalizer H))) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices Nat.card (Subtype.val ''
      ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer H))) = p ^ (n + 1)
      by convert! this using 2
    rw [Nat.card_image_of_injective Subtype.val_injective
        ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer (H : Set G))),
      pow_succ, ← hH, Nat.card_congr hequiv, ← hx, ← Nat.card_zpowers, ← Nat.card_prod]
    exact Nat.card_congr
      (preimageMkEquivSubgroupProdSet (H.subgroupOf (normalizer H)) (zpowers x)), by
    intro y hy
    simp only [Subgroup.coe_subtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine ⟨⟨y, le_normalizer hy⟩, ⟨0, ?_⟩, rfl⟩
    dsimp only
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using! hy⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
/-
**Sylow.exists_subgroup_card_pow_prime_le** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_subgroup_card_pow_prime_le [Finite G] (p : Nat) : forall {n m : Nat
} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ Nat.card G) (H : Subgroup G) (_hH : Nat.
card H = p ^ n) (_hnm : n <= m), exists K : Subgroup G, Nat.card K = p ^ m ∧ H <
= K | n, m => fun {hdvd H hH hnm} => (lt_or_eq_of_le hnm).elim (fun hnm : n < m 
=> have h0m : 0 < m
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.exists_subgroup_card_pow_prime_le._unary`：∀ {G : Type u} [inst : G
roup G] [Finite G] (p : ℕ) [_hp : Fact (Nat.Prime p)] (_x : (_ : ℕ) ×' ℕ),   p ^
 _x.2 ∣ Nat.card G → ∀ (H : Subgroup…

--- 原说明 ---
If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G`
-/
theorem exists_subgroup_card_pow_prime_le [Finite G] (p : ℕ) :
    ∀ {n m : ℕ} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ Nat.card G) (H : Subgroup G)
      (_hH : Nat.card H = p ^ n) (_hnm : n ≤ m), ∃ K : Subgroup G, Nat.card K = p ^ m ∧ H ≤ K
  | n, m => fun {hdvd H hH hnm} =>
    (lt_or_eq_of_le hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_lt n.zero_le hnm
        have hnm1 : n ≤ m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le _ _ n (m - 1) _
            (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : p ^ (m - 1 + 1) ∣ Nat.card G := by rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ _ hdvd' K hK.1
        ⟨K', by rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_trans hK.2 hK'.2⟩)
      fun hnm : n = m => ⟨H, by simp [hH, hnm]⟩

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
/-
**Sylow.exists_subgroup_card_pow_prime** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：exists_subgroup_card_pow_prime [Finite G] (p : Nat) {n : Nat} [Fact p.Prim
e] (hdvd : p ^ n ∣ Nat.card G) : exists K : Subgroup G, Nat.card K = p ^ n
参数：p : Nat；hdvd : p ^ n ∣ Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.exists_subgroup_card_pow_prime_le`：exists_subgroup_card_pow_prime_
le [Finite G] (p : Nat) : forall {n m : Nat} [_hp : Fact p.Prime] (_hdvd : p ^ m
 ∣ Nat.card G) (H : Subgroup …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_bot`：card_bot : Nat.card (⊥ : Subgroup G) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n`
-/
theorem exists_subgroup_card_pow_prime [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group of size at least `p ^ n`
then there is a subgroup of cardinality `p ^ n`. -/
/-
**Sylow.exists_subgroup_card_pow_prime_of_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Syl
ow`。
形式化陈述：exists_subgroup_card_pow_prime_of_le_card {n p : Nat} (hp : p.Prime) (h : 
IsPGroup p G) (hn : p ^ n <= Nat.card G) : exists H : Subgroup G, Nat.card H = p
 ^ n
参数：hp : p.Prime；h : IsPGroup p G；hn : p ^ n <= Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
A special case of **Sylow's first theorem**. If `G` is a `p`-group of size at le
ast `p ^ n`
then there is a subgroup of cardinality `p ^ n`.
-/
lemma exists_subgroup_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    (hn : p ^ n ≤ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite G := Nat.finite_of_card_ne_zero <| by linarith [Nat.one_le_pow n p hp.pos]
  obtain ⟨m, hm⟩ := h.exists_card_eq
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
  exact pow_dvd_pow _ <| (Nat.pow_le_pow_iff_right hp.one_lt).1 hn

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `p ^ n` then there is a subgroup of `H` of cardinality `p ^ n`. -/
/-
**Sylow.exists_subgroup_le_card_pow_prime_of_le_card** 是 Mathlib 中的一个引理，位于命名空间 `
Sylow`。
形式化陈述：exists_subgroup_le_card_pow_prime_of_le_card {n p : Nat} (hp : p.Prime) (h
 : IsPGroup p G) {H : Subgroup G} (hn : p ^ n <= Nat.card H) : exists H' <= H, N
at.card H' = p ^ n
参数：hp : p.Prime；h : IsPGroup p G；hn : p ^ n <= Nat.card H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sylow.exists_subgroup_card_pow_prime_of_le_card`：exists_subgroup_card_po
w_prime_of_le_card {n p : Nat} (hp : p.Prime) (h : IsPGroup p G) (hn : p ^ n <= 
Nat.card G) : exists H : Subgroup G, …
· 使用定理 `IsPGroup.to_subgroup`：to_subgroup (H : Subgroup G) : IsPGroup p H
· 使用定理 `Subgroup.map_subtype_le`：map_subtype_le {H : Subgroup G} (K : Subgroup H
) : K.map H.subtype <= H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β

--- 原说明 ---
A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a sub
group of size at
least `p ^ n` then there is a subgroup of `H` of cardinality `p ^ n`.
-/
lemma exists_subgroup_le_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    {H : Subgroup G} (hn : p ^ n ≤ Nat.card H) : ∃ H' ≤ H, Nat.card H' = p ^ n := by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `k` then there is a subgroup of `H` of cardinality between `k / p` and `k`. -/
/-
**Sylow.exists_subgroup_le_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Sylow`。
形式化陈述：exists_subgroup_le_card_le {k p : Nat} (hp : p.Prime) (h : IsPGroup p G) {
H : Subgroup G} (hk : k <= Nat.card H) (hk₀ : k != 0) : exists H' <= H, Nat.card
 H' <= k ∧ k < p * Nat.card H'
参数：hp : p.Prime；h : IsPGroup p G；hk : k <= Nat.card H；hk₀ : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_pow_near`：exists_nat_pow_near (hx : 1 <= x) (hy : 1 < y) : ex
ists n : Nat, y ^ n <= x ∧ x < y ^ (n + 1)
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `Sylow.exists_subgroup_le_card_pow_prime_of_le_card`：exists_subgroup_le_c
ard_pow_prime_of_le_card {n p : Nat} (hp : p.Prime) (h : IsPGroup p G) {H : Subg
roup G} (hn : p ^ n <= Nat.card H) : exi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n

--- 原说明 ---
A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a sub
group of size at
least `k` then there is a subgroup of `H` of cardinality between `k / p` and `k`
.
-/
lemma exists_subgroup_le_card_le {k p : ℕ} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
    (hk : k ≤ Nat.card H) (hk₀ : k ≠ 0) : ∃ H' ≤ H, Nat.card H' ≤ k ∧ k < p * Nat.card H' := by
  obtain ⟨m, hmk, hkm⟩ : ∃ s, p ^ s ≤ k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ', H'card] using And.intro hmk hkm
/-
**Sylow.pow_dvd_card_of_pow_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：pow_dvd_card_of_pow_dvd_card [Finite G] {p n : Nat} [hp : Fact p.Prime] (P
 : Sylow p G) (hdvd : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P
参数：P : Sylow p G；hdvd : p ^ n ∣ Nat.card G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.Prime.coprime_pow_of_not_dvd`：∀ {p m a : ℕ}, Nat.Prime p → ¬p ∣ a → 
a.Coprime (p ^ m)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.index_mul_card`：index_mul_card : H.index * Nat.card H = Nat.car
d G
-/
theorem pow_dvd_card_of_pow_dvd_card [Finite G] {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P := by
  rw [← index_mul_card P.1] at hdvd
  exact (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm.dvd_of_dvd_mul_left hdvd
/-
**Sylow.dvd_card_of_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：dvd_card_of_dvd_card [Finite G] {p : Nat} [Fact p.Prime] (P : Sylow p G) (
hdvd : p ∣ Nat.card G) : p ∣ Nat.card P
参数：P : Sylow p G；hdvd : p ∣ Nat.card G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sylow.pow_dvd_card_of_pow_dvd_card`：pow_dvd_card_of_pow_dvd_card [Finite
 G] {p n : Nat} [hp : Fact p.Prime] (P : Sylow p G) (hdvd : p ^ n ∣ Nat.card G) 
: p ^ n ∣ Nat.card P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem dvd_card_of_dvd_card [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card P := by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key

/-- Sylow subgroups are Hall subgroups. -/
/-
**Sylow.card_coprime_index** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_coprime_index [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G
) : (Nat.card P).Coprime P.index
参数：P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.Prime.coprime_pow_of_not_dvd`：∀ {p m a : ℕ}, Nat.Prime p → ¬p ∣ a → 
a.Coprime (p ^ m)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Sylow.not_dvd_index`：not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.Fin
iteIndex] : ¬ p ∣ P.index
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Sylow subgroups are Hall subgroups.
-/
theorem card_coprime_index [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    (Nat.card P).Coprime P.index :=
  let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm
/-
**Sylow.ne_bot_of_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：ne_bot_of_dvd_card [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G
) (hdvd : p ∣ Nat.card G) : (P : Subgroup G) != ⊥
参数：P : Sylow p G；hdvd : p ∣ Nat.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Sylow.dvd_card_of_dvd_card`：dvd_card_of_dvd_card [Finite G] {p : Nat} [F
act p.Prime] (P : Sylow p G) (hdvd : p ∣ Nat.card G) : p ∣ Nat.card P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_bot`：card_bot : Nat.card (⊥ : Subgroup G) = 1
-/
theorem ne_bot_of_dvd_card [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : (P : Subgroup G) ≠ ⊥ := by
  refine fun h => hp.out.not_dvd_one ?_
  have key : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

/-- The cardinality of a Sylow subgroup is `p ^ n`
where `n` is the multiplicity of `p` in the group order. -/
/-
**Sylow.card_eq_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：card_eq_multiplicity [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p
 G) : Nat.card P = p ^ Nat.factorization (Nat.card G) p
参数：P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.pow_dvd_iff_dvd_ordProj`：∀ {p k n : ℕ}, Nat.Prime p → n ≠ 0 → 
(p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
· 使用定理 `Sylow.pow_dvd_card_of_pow_dvd_card`：pow_dvd_card_of_pow_dvd_card [Finite
 G] {p n : Nat} [hp : Fact p.Prime] (P : Sylow p G) (hdvd : p ^ n ∣ Nat.card G) 
: p ^ n ∣ Nat.card P
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n

--- 原说明 ---
The cardinality of a Sylow subgroup is `p ^ n`
where `n` is the multiplicity of `p` in the group order.
-/
theorem card_eq_multiplicity [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ Nat.factorization (Nat.card G) p := by
  obtain ⟨n, heq : Nat.card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine Nat.dvd_antisymm ?_ (P.pow_dvd_card_of_pow_dvd_card (Nat.ordProj_dvd _ p))
  rw [heq, ← hp.out.pow_dvd_iff_dvd_ordProj (show Nat.card G ≠ 0 from Nat.card_pos.ne'), ← heq]
  exact P.1.card_subgroup_dvd_card

variable (G) in
/-
**Sylow._root_.Group.card_dvd_prod_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Group.card_dvd_prod_orderOf [Fintype G] : Nat.card G ∣ ∏ g : G, orderOf g := by
  classical
  refine Nat.dvd_iff_prime_pow_dvd_dvd .. |>.mpr fun p k hp h ↦ ?_
  have := Fact.mk hp
  have ⟨H, hH⟩ := exists_subgroup_card_pow_prime p h
  have (g : G) (hg : g ∈ (H \ {1} : Set G).toFinset) : p ∣ orderOf g := by
    have ⟨hg, hg1⟩ : g ∈ H ∧ g ≠ 1 := by simpa using hg
    simpa using IsPGroup.of_card hH |>.dvd_orderOf (g := ⟨g, hg⟩) <| by simpa
  grw [← prod_dvd_prod_of_subset _ _ _ (H \ {1} : Set G).toFinset.subset_univ,
    ← prod_dvd_prod_of_dvd _ _ this, prod_const, k.le_sub_one_of_lt <| k.lt_pow_self hp.one_lt]
  simp [Finset.card_sdiff, ← Nat.card_eq_fintype_card, hH]

/-- If `G` has a normal Sylow `p`-subgroup, then it is the only Sylow `p`-subgroup. -/
@[instance_reducible]
/-
**Sylow.unique_of_normal** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：unique_of_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow 
p G) (h : P.Normal) : Unique (Sylow p G)
参数：Sylow p G；P : Sylow p G；h : P.Normal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` has a normal Sylow `p`-subgroup, then it is the only Sylow `p`-subgroup.
-/
noncomputable def unique_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : Unique (Sylow p G) := by
  refine { uniq := fun Q ↦ ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [smul_eq_of_normal] at h1 h2
  rw [← h1, ← h2]
/-
**Sylow.characteristic_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Sylow`。
形式化陈述：characteristic_of_subsingleton {p : Nat} [Subsingleton (Sylow p G)] (P : S
ylow p G) : P.Characteristic
参数：Sylow p G；P : Sylow p G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_map_eq`：characteristic_iff_map_eq : H.Charac
teristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom = H
· 使用定理 `Subgroup.pointwise_smul_def`：pointwise_smul_def {a : α} (S : Subgroup G)
 : a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sylow.pointwise_smul_def`：pointwise_smul_def {α : Type*} [Group α] [MulD
istribMulAction α G] {g : α} {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G)
-/
instance characteristic_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ ↦ ?_
  have h := Subgroup.pointwise_smul_def (a := ϕ) (P : Subgroup G)
  rwa [← pointwise_smul_def, Subsingleton.elim (ϕ • P) P, eq_comm] at h
/-
**Sylow.normal_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normal_of_subsingleton {p : Nat} [Subsingleton (Sylow p G)] (P : Sylow p G
) : P.Normal
参数：Sylow p G；P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_characteristic`：∀ {G : Type u_1} [inst : Group G] (H 
: Subgroup G) [h : H.Characteristic], H.Normal
-/
theorem normal_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Normal :=
  Subgroup.normal_of_characteristic _
/-
**Sylow.characteristic_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：characteristic_of_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P 
: Sylow p G) (h : P.Normal) : P.Characteristic
参数：Sylow p G；P : Sylow p G；h : P.Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem characteristic_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : P.Characteristic := by
  have _ := unique_of_normal P h
  exact characteristic_of_subsingleton _
/-
**Sylow.normal_of_normalizer_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normal_of_normalizer_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] 
(P : Sylow p G) (hn : (normalizer (P : Set G)).Normal) : P.Normal
参数：Sylow p G；P : Sylow p G；hn : (normalizer (P : Set G)).Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `Sylow.normalizer_sup_eq_top'`：normalizer_sup_eq_top' {p : Nat} [Fact p.P
rime] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)] (P : Sylow p G) (hP : P <
= N) : normalizer …
· 使用定理 `Sylow.instFiniteSubtypeMemSubgroup`：∀ {p : ℕ} {G : Type u_1} [inst : Gro
up G] (H : Subgroup G) [Finite (Sylow p G)], Finite (Sylow p ↥H)
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Sylow.coe_coe`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G)
, ↑↑P = ↑P
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
theorem normal_of_normalizer_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hn : (normalizer (P : Set G)).Normal) : P.Normal := by
  rw [← normalizer_eq_top_iff, ← normalizer_sup_eq_top' P le_normalizer, P.coe_coe, sup_idem]

@[simp]
/-
**Sylow.normalizer_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normalizer_normalizer {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : S
ylow p G) : normalizer (normalizer (P : Set G)) = normalizer (P : Set G)
参数：Sylow p G；P : Sylow p G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Sylow.normal_of_normalizer_normal`：normal_of_normalizer_normal {p : Nat}
 [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) (hn : (normalizer (P : Set 
G)).Normal) : P.Normal
· 使用定理 `Sylow.instFiniteSubtypeMemSubgroup`：∀ {p : ℕ} {G : Type u_1} [inst : Gro
up G] (H : Subgroup G) [Finite (Sylow p G)], Finite (Sylow p ↥H)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.subgroupOf_normalizer_eq`：subgroupOf_normalizer_eq {H N : Subgr
oup G} (h : H <= N) : (normalizer H).subgroupOf N = normalizer (H.subgroupOf N)
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `Sylow.coe_subtype`：coe_subtype (h : P <= N) : P.subtype h = subgroupOf P
 N
· 使用定理 `Sylow.coe_coe`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (P : Sylow p G)
, ↑↑P = ↑P
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
-/
theorem normalizer_normalizer {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    normalizer (normalizer (P : Set G)) = normalizer (P : Set G) := by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  rw [← (P.subtype _).coe_coe, coe_subtype,
    normal_subgroupOf_iff_le_normalizer (le_normalizer.trans le_normalizer),
    ← subgroupOf_normalizer_eq (le_normalizer.trans le_normalizer)] at this
  exact le_antisymm (this normal_in_normalizer) le_normalizer
/-
**Sylow.normal_of_all_max_subgroups_normal** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normal_of_all_max_subgroups_normal [Finite G] (hnc : forall H : Subgroup G
, IsCoatom H -> H.Normal) {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Syl
ow p G) : P.Normal
参数：hnc : forall H : Subgroup G, IsCoatom H -> H.Normal；Sylow p G；P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `instIsStronglyCoatomicOfWellFoundedGT`：∀ {α : Type u_2} [inst : PartialO
rder α] [WellFoundedGT α], IsStronglyCoatomic α
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Sylow.normalizer_sup_eq_top'`：normalizer_sup_eq_top' {p : Nat} [Fact p.P
rime] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)] (P : Sylow p G) (hP : P <
= N) : normalizer …
· 使用定理 `Sylow.instFiniteSubtypeMemSubgroup`：∀ {p : ℕ} {G : Type u_1} [inst : Gro
up G] (H : Subgroup G) [Finite (Sylow p G)], Finite (Sylow p ↥H)
-/
theorem normal_of_all_max_subgroups_normal [Finite G]
    (hnc : ∀ H : Subgroup G, IsCoatom H → H.Normal) {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom (normalizer (P : Set G))
        with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · have := hnc _ hK
        have hPK : P ≤ K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK, P.normalizer_sup_eq_top' hPK])
/-
**Sylow.normal_of_normalizerCondition** 是 Mathlib 中的一个定理，位于命名空间 `Sylow`。
形式化陈述：normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : Nat} [Fac
t p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : P.Normal
参数：hnc : NormalizerCondition G；Sylow p G；P : Sylow p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `normalizerCondition_iff_only_full_group_self_normalizing`：∀ {G : Type u_
1} [inst : Group G], NormalizerCondition G ↔ ∀ (H : Subgroup G), Subgroup.normal
izer ↑H = H → H = ⊤
· 使用定理 `Sylow.normalizer_normalizer`：normalizer_normalizer {p : Nat} [Fact p.Pri
me] [Finite (Sylow p G)] (P : Sylow p G) : normalizer (normalizer (P : Set G)) =
 normalizer (P : …
-/
theorem normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp <|
    normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ <| normalizer_normalizer _

/-- If all its Sylow subgroups are normal, then a finite group is isomorphic to the direct product
of these Sylow subgroups.
-/
/-
**Sylow.directProductOfNormal** 是 Mathlib 中的一个定义，位于命名空间 `Sylow`。
形式化陈述：directProductOfNormal [Finite G] (hn : forall {p : Nat} [Fact p.Prime] (P 
: Sylow p G), P.Normal) : (forall p : (Nat.card G).primeFactors, forall P : Sylo
w p G, P) ≃* G
参数：hn : forall {p : Nat} [Fact p.Prime] (P : Sylow p G), P.Normal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all its Sylow subgroups are normal, then a finite group is isomorphic to the 
direct product
of these Sylow subgroups.
-/
noncomputable def directProductOfNormal [Finite G]
    (hn : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p G), P.Normal) :
    (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, P) ≃* G := by
  have := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : ∀ p, Sylow p G := default
  have : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps => ∀ x y : G, x ∈ P p₁ → y ∈ P p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P p₁)) (hn (P p₂))
    apply IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  refine MulEquiv.trans (N := ∀ p : ps, P p) ?_ ?_
  -- There is only one Sylow subgroup for each p, so the inner product is trivial
  · -- here we need to help the elaborator with an explicit instantiation
    apply @MulEquiv.piCongrRight ps (fun p => ∀ P : Sylow p G, P) (fun p => P p) _ _
    rintro ⟨p, hp⟩
    haveI hp' := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    letI := unique_of_normal _ (hn (P p))
    apply MulEquiv.piUnique
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    apply IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (∀ p : ps, P p) = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card G).factorization p.1 := by
        congr 1 with ⟨p, hp⟩
        exact @card_eq_multiplicity _ _ _ p ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card G).factorization p :=
        (Finset.prod_finset_coe (fun p => p ^ (Nat.card G).factorization p) _)
      _ = (Nat.card G).factorization.prod (· ^ ·) := rfl
      _ = Nat.card G := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

end Sylow

