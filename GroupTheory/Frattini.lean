/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Radical

/-!
# The Frattini subgroup

We give the definition of the Frattini subgroup of a group, and three elementary results:
* The Frattini subgroup is characteristic.
* If every subgroup of a group is contained in a maximal subgroup, then
  the Frattini subgroup consists of the non-generating elements of the group.
* The Frattini subgroup of a finite group is nilpotent.
-/

@[expose] public section

/-- The Frattini subgroup of a group is the intersection of the maximal subgroups. -/
/-
**frattini** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：frattini (G : Type*) [Group G] : Subgroup G
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frattini subgroup of a group is the intersection of the maximal subgroups.
-/
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)

variable {G H : Type*} [Group G] [Group H] {φ : G →* H}
/-
**frattini_le_coatom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G <= K
参数：h : IsCoatom K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.radical_le_coatom`：Order.radical_le_coatom {a : α} (h : IsCoatom a
) : radical α <= a
-/
lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G ≤ K :=
  Order.radical_le_coatom h

open Subgroup
/-
**frattini_le_comap_frattini_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frattini_le_comap_frattini_of_surjective (hφ : Function.Surjective φ) : fr
attini G <= (frattini H).comap φ
参数：hφ : Function.Surjective φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.comap_iInf`：comap_iInf {ι : Sort*} (f : G ->* N) (s : ι -> Subg
roup N) : (iInf s).comap f = ⨅ i, (s i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用引理 `Subgroup.isCoatom_comap_of_surjective`：isCoatom_comap_of_surjective {H :
 Type*} [Group H] {φ : G ->* H} (hφ : Function.Surjective φ) {M : Subgroup H} (h
M : IsCoatom M) : IsCoatom …
-/
lemma frattini_le_comap_frattini_of_surjective (hφ : Function.Surjective φ) :
    frattini G ≤ (frattini H).comap φ := by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM

/-- The Frattini subgroup is characteristic. -/
/-
**frattini_characteristic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：frattini_characteristic : (frattini G).Characteristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.characteristic_iff_comap_eq`：characteristic_iff_comap_eq : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
· 使用定理 `OrderIso.map_radical`：OrderIso.map_radical (f : α ≃o β) : f (Order.radic
al α) = Order.radical β

--- 原说明 ---
The Frattini subgroup is characteristic.
-/
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

/--
The Frattini subgroup consists of "non-generating" elements in the following sense:

If a subgroup together with the Frattini subgroup generates the whole group,
then the subgroup is already the whole group.
-/
/-
**frattini_nongenerating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G} (h : K ⊔
 frattini G = ⊤) : K = ⊤
参数：Subgroup G；h : K ⊔ frattini G = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.radical_nongenerating`：Order.radical_nongenerating [IsCoatomic α] 
{a : α} (h : a ⊔ radical α = ⊤) : a = ⊤

--- 原说明 ---
The Frattini subgroup consists of "non-generating" elements in the following sen
se:

If a subgroup together with the Frattini subgroup generates the whole group,
then the subgroup is already the whole group.
-/
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G}
    (h : K ⊔ frattini G = ⊤) : K = ⊤ :=
  Order.radical_nongenerating h

/-- When `G` is finite, the Frattini subgroup is nilpotent. -/
/-
**frattini_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frattini_nilpotent [Finite G] : Group.IsNilpotent (frattini G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Group.isNilpotent_of_finite_tfae`：Group.isNilpotent_of_finite_tfae : Lis
t.TFAE [IsNilpotent G, NormalizerCondition G, forall H : Subgroup G, IsCoatom H 
-> H.Normal, forall (p…
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sylow.normalizer_sup_eq_top`：normalizer_sup_eq_top {p : Nat} [Fact p.Pri
me] {N : Subgroup G} [N.Normal] [Finite (Sylow p N)] (P : Sylow p N) : normalize
r (P.map N.subtyp…
· 使用定理 `Subgroup.normal_of_characteristic`：∀ {G : Type u_1} [inst : Group G] (H 
: Subgroup G) [h : H.Characteristic], H.Normal
· 使用定理 `Sylow.instFiniteSubtypeMemSubgroup`：∀ {p : ℕ} {G : Type u_1} [inst : Gro
up G] (H : Subgroup G) [Finite (Sylow p G)], Finite (Sylow p ↥H)
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `frattini_nongenerating`：frattini_nongenerating [IsCoatomic (Subgroup G)]
 {K : Subgroup G} (h : K ⊔ frattini G = ⊤) : K = ⊤
· 使用定理 `instIsStronglyCoatomicOfWellFoundedGT`：∀ {α : Type u_2} [inst : PartialO
rder α] [WellFoundedGT α], IsStronglyCoatomic α
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `Subgroup.Normal.of_map_subtype`：∀ {G : Type u_1} [inst : Group G] {K : S
ubgroup G} {L : Subgroup ↥K}, (Subgroup.map K.subtype L).Normal → L.Normal

--- 原说明 ---
When `G` is finite, the Frattini subgroup is nilpotent.
-/
theorem frattini_nilpotent [Finite G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (Group.isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype P).Normal := normalizer_eq_top_iff.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact P_normal_in_G.of_map_subtype
