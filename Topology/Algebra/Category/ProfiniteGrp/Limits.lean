/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the projective limit of finite groups

We define the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `toFiniteQuotientFunctor` : The functor from `OpenNormalSubgroup P` to `FiniteGrp`
  sending an open normal subgroup `U` to `P ⧸ U`, where `P : ProfiniteGrp`.

* `toLimit` : The continuous homomorphism from a profinite group `P` to
  the projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimittoFiniteQuotientFunctor` : The `toLimit` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained in it.

-/

@[expose] public section

universe u

open CategoryTheory IsTopologicalGroup

namespace ProfiniteGrp

/-- The functor from `OpenNormalSubgroup P` to `FiniteGrp` sending `U` to `P ⧸ U`,
where `P : ProfiniteGrp`. -/
@[to_additive /-- The functor from `OpenNormalAddSubgroup P` to `FiniteAddGrp` sending `U` to
`P ⧸ U`, where `P : ProfiniteAddGrp`. -/]
/-
**ProfiniteGrp.toFiniteQuotientFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ Finite
Grp where obj
参数：P : ProfiniteGrp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ FiniteGrp where
  obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <| (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

/-- The diagram of finite quotients of `P` viewed in `ProfiniteGrp`. -/
@[to_additive (attr := simps! obj map)
/-- The diagram of finite quotients of `P` viewed in `ProfiniteAddGrp`. -/]
/-
**ProfiniteGrp.diagram** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：diagram (P : ProfiniteGrp.{u}) : OpenNormalSubgroup P ⥤ ProfiniteGrp.{u}
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def diagram (P : ProfiniteGrp.{u}) : OpenNormalSubgroup P ⥤ ProfiniteGrp.{u} :=
  toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The `MonoidHom` from a profinite group `P` to the projective limit of its quotients by
open normal subgroups ordered by inclusion -/
@[to_additive /-- The `AddMonoidHom` from a profinite additive group `P` to the projective limit of
its quotients by open normal subgroups ordered by inclusion -/]
/-
**ProfiniteGrp.toLimitFun** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：toLimitFun (P : ProfiniteGrp.{u}) : P ->* limit (diagram P) where toFun p
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toLimitFun (P : ProfiniteGrp.{u}) : P →* limit (diagram P) where
  toFun p := ⟨fun _ => QuotientGroup.mk p, fun _ ↦ fun _ _ ↦ rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**ProfiniteGrp.toLimitFun_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：toLimitFun_continuous (P : ProfiniteGrp.{u}) : Continuous (toLimitFun P)
参数：P : ProfiniteGrp.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuotientGroup.out_eq'`：out_eq' (a : α ⧸ s) : mk a.out = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
· 使用定理 `IsOpen.leftCoset`：IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : 
IsOpen (x • U)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
· 使用定理 `OpenSubgroup.isOpen'`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolo
gicalSpace G] (self : OpenSubgroup G), IsOpen (↑self).carrier
-/
lemma toLimitFun_continuous (P : ProfiniteGrp.{u}) : Continuous (toLimitFun P) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  dsimp only [Functor.comp_obj, CompHausLike.coe_of, Functor.comp_map,
    CompHausLike.toCompHausLike_map, CompHausLike.compHausLikeToTop_map, Set.mem_ofPred_eq,
    toLimitFun, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  apply Continuous.mk
  intro s _
  rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert! IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

/-- The morphism in the category of `ProfiniteGrp` from a profinite group `P` to
the projective limit of its quotients by open normal subgroups ordered by inclusion -/
@[to_additive /-- The morphism in the category of `ProfiniteAddGrp` from a profinite additive group
`P` to the projective limit of its quotients by open normal subgroups ordered by inclusion -/]
/-
**ProfiniteGrp.toLimit** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：toLimit (P : ProfiniteGrp.{u}) : P ⟶ limit (diagram P)
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
· 使用引理 `ProfiniteGrp.toLimitFun_continuous`：toLimitFun_continuous (P : Profinite
Grp.{u}) : Continuous (toLimitFun P)
-/
def toLimit (P : ProfiniteGrp.{u}) : P ⟶ limit (diagram P) :=
  ofHom { toLimitFun P with
  continuous_toFun := toLimitFun_continuous P }

/-- An auxiliary result, superseded by `toLimit_surjective` -/
/-
**ProfiniteGrp.denseRange_toLimit** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteGrp`。
形式化陈述：denseRange_toLimit (P : ProfiniteGrp.{u}) : DenseRange (toLimit P)
参数：P : ProfiniteGrp.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_pi_iff`：isOpen_pi_iff {s : Set (forall a, A a)} : IsOpen s ↔ fora
ll f, f in s -> exists (I : Finset ι) (u : forall a, Set (A a)), (forall a, a in
 I …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normal_iInf_normal`：normal_iInf_normal {ι : Sort*} {a : ι -> Su
bgroup G} (norm : forall i : ι, (a i).Normal) : (iInf a).Normal
· 使用定理 `OpenNormalSubgroup.isNormal'`：∀ {G : Type u} [inst : Group G] [inst_1 : 
TopologicalSpace G] (self : OpenNormalSubgroup G),   (↑self.toOpenSubgroup).Norm
al
· 使用定理 `Subgroup.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subgroup G} : (↑(⨅ i, 
S i) : Set G) = ⋂ i, S i
· 使用定理 `isOpen_iInter_of_finite`：isOpen_iInter_of_finite [Finite ι] {s : ι -> Se
t X} (h : forall i, IsOpen (s i)) : IsOpen (⋂ i, s i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `OpenSubgroup.isOpen'`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolo
gicalSpace G] (self : OpenSubgroup G), IsOpen (↑self).carrier
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
An auxiliary result, superseded by `toLimit_surjective`
-/
theorem denseRange_toLimit (P : ProfiniteGrp.{u}) : DenseRange (toLimit P) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use (toLimit P) origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (P.toLimit origin).property M_to_Na]
  change (P.toFiniteQuotientFunctor.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2
/-
**ProfiniteGrp.toLimit_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteGrp`。
形式化陈述：toLimit_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (toLimit P
)
参数：P : ProfiniteGrp.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `ContinuousMonoidHom.continuous_toFun`：∀ {A : Type u_2} {B : Type u_3} [i
nst : Monoid A] [inst_1 : Monoid B] [inst_2 : TopologicalSpace A]   [inst_3 : To
pologicalSpace B] (self : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `ProfiniteGrp.denseRange_toLimit`：denseRange_toLimit (P : ProfiniteGrp.{u
}) : DenseRange (toLimit P)
-/
theorem toLimit_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (toLimit P) := by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr this,
    Dense.closure_eq (denseRange_toLimit P)]

@[to_additive]
/-
**ProfiniteGrp.toLimit_injective** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteGrp`。
形式化陈述：toLimit_injective (P : ProfiniteGrp.{u}) : Function.Injective (toLimit P)
参数：P : ProfiniteGrp.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `Subgroup.eq_bot_iff_forall`：eq_bot_iff_forall : H = ⊥ ↔ forall x in H, x
 = (1 : G)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`：exist_openNo
rmalSubgroup_sub_open_nhds_of_one {U : Set G} (UOpen : IsOpen U) (einU : 1 in U)
 : exists H : OpenNormalSubgroup G, (H : Set G) …
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `TotallyDisconnectedSpace.t1Space`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [h : TotallyDisconnectedSpace X], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
-/
theorem toLimit_injective (P : ProfiniteGrp.{u}) : Function.Injective (toLimit P) := by
  change Function.Injective (toLimit P).hom.toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

/-- The topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups -/
/-
**ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor** 是 Mathlib 中的一个定义
，位于命名空间 `ProfiniteGrp`。
形式化陈述：continuousMulEquivLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) : P 
≃ₜ* (limit <| diagram P)
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological group isomorphism between a profinite group and the projective l
imit of
its quotients by open normal subgroups
-/
noncomputable def continuousMulEquivLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (limit <| diagram P) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }
/-
**ProfiniteGrp.isIso_toLimit** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
形式化陈述：isIso_toLimit (P : ProfiniteGrp.{u}) : IsIso (toLimit P)
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `ProfiniteGrp.instReflectsIsomorphismsForgetContinuousMonoidHomCarrierToT
opTotallyDisconnectedSpaceToProfinite`：(CategoryTheory.forget ProfiniteGrp.{u}).
ReflectsIsomorphisms
· 使用定理 `ProfiniteGrp.toLimit_injective`：toLimit_injective (P : ProfiniteGrp.{u})
 : Function.Injective (toLimit P)
· 使用定理 `ProfiniteGrp.toLimit_surjective`：toLimit_surjective (P : ProfiniteGrp.{u
}) : Function.Surjective (toLimit P)
-/
instance isIso_toLimit (P : ProfiniteGrp.{u}) : IsIso (toLimit P) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

/-- The isomorphism in the category of profinite group between a profinite group and
the projective limit of its quotients by open normal subgroups -/
/-
**ProfiniteGrp.isoLimittoFiniteQuotientFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Profin
iteGrp`。
形式化陈述：isoLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) : P ≅ (limit <| dia
gram P)
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism in the category of profinite group between a profinite group and
the projective limit of its quotients by open normal subgroups
-/
noncomputable def isoLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≅ (limit <| diagram P) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

set_option backward.isDefEq.respectTransparency.types false in
/-- The projection from `P` to the quotient by an open normal subgroup. -/
@[to_additive /-- The projection from `P` to the quotient by an open normal subgroup. -/]
/-
**ProfiniteGrp.proj** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：proj {P : ProfiniteGrp.{u}} (U : OpenNormalSubgroup P) : P ⟶ (diagram P).o
bj U
参数：U : OpenNormalSubgroup P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop

--- 原说明 ---
The projection from `P` to the quotient by an open normal subgroup.
-/
def proj {P : ProfiniteGrp.{u}} (U : OpenNormalSubgroup P) : P ⟶ (diagram P).obj U :=
  ProfiniteGrp.ofHom (Y := (diagram P).obj U) {
    toFun := QuotientGroup.mk
    map_one' := rfl
    map_mul' _ _ := rfl
    continuous_toFun := show Continuous ((limitCone <| diagram P).π.app U ∘ toLimit P) by
      fun_prop
  }

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical cone over `diagram P` with point `P`. -/
@[to_additive (attr := simps) /-- The canonical cone over `diagram P` with point `P`. -/]
/-
**ProfiniteGrp.cone** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：cone (P : ProfiniteGrp.{u}) : Limits.Cone (diagram P) where pt
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical cone over `diagram P` with point `P`.
-/
def cone (P : ProfiniteGrp.{u}) : Limits.Cone (diagram P) where
  pt := P
  π := { app := proj }

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical cone over `diagram P` is a limit cone. -/
/-
**ProfiniteGrp.isLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：isLimitCone (P : ProfiniteGrp.{u}) : Limits.IsLimit P.cone
参数：P : ProfiniteGrp.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical cone over `diagram P` is a limit cone.
-/
noncomputable def isLimitCone (P : ProfiniteGrp.{u}) : Limits.IsLimit P.cone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) <| .symm <|
    Limits.Cone.ext (isoLimittoFiniteQuotientFunctor _) fun _ => rfl

end ProfiniteGrp

