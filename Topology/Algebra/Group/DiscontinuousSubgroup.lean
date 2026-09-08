/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Properly discontinuous actions of subgroups
-/

open Topology Pointwise Filter Set TopologicalSpace Subgroup

public section

variable {Γ α : Type*} [Group Γ] [TopologicalSpace α]

@[to_additive]
/-
**Subgroup.properlyDiscontinuousSMul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {Γ : Type u_1} {α : Type u_2} [inst : Group Γ] [inst_1 : TopologicalSpac
e α] [inst_2 : SMul Γ α] (S : Subgroup Γ),   ProperlyDiscontinuousSMul (↥S) α ↔ 
    ∀ {K L : Set α}, IsCompact K → IsCompact L → {g | g ∈ S ∧ (g • K ∩ L).Nonemp
ty}.Finite
参数：S : Subgroup Γ；↥S；g • K ∩ L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `properlyDiscontinuousSMul_iff`：properlyDiscontinuousSMul_iff [Topologica
lSpace α] [SMul M α] : ProperlyDiscontinuousSMul M α ↔ forall {K L : Set α}, IsC
ompact K -> IsCompa…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.BijOn.finite_iff_finite`：∀ {α : Type u} {β : Type v} {f : α → β} {s 
: Set α} {t : Set β}, Set.BijOn f s t → (s.Finite ↔ t.Finite)
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.injOn_subtype_val`：injOn_subtype_val {p : α -> Prop} {s : Set {x // 
p x}} : Set.InjOn Subtype.val s
-/
protected lemma Subgroup.properlyDiscontinuousSMul_iff
    [SMul Γ α] (S : Subgroup Γ) : ProperlyDiscontinuousSMul S α ↔ ∀ {K L : Set α},
      IsCompact K → IsCompact L →  {g : Γ | g ∈ S ∧ (g • K ∩ L).Nonempty}.Finite := by
  rw [properlyDiscontinuousSMul_iff]
  congr! with K L hK hL
  convert! injOn_subtype_val (s := {m : S | (m • K ∩ L).Nonempty}) |>.bijOn_image.finite_iff_finite
  ext g
  simp [Set.subtype_smul_set, and_comm]

@[to_additive]
/-
**Subgroup.properlyDiscontinuousSMul_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.properlyDiscontinuousSMul_of_le [SMul Γ α] {G H : Subgroup Γ} (hG
 : ProperlyDiscontinuousSMul G α) (hGH : H <= G) : ProperlyDiscontinuousSMul H α
参数：hG : ProperlyDiscontinuousSMul G α；hGH : H <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.properlyDiscontinuousSMul_iff`：∀ {Γ : Type u_1} {α : Type u_2} 
[inst : Group Γ] [inst_1 : TopologicalSpace α] [inst_2 : SMul Γ α] (S : Subgroup
 Γ),   ProperlyDiscontinuous…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
-/
lemma Subgroup.properlyDiscontinuousSMul_of_le
    [SMul Γ α] {G H : Subgroup Γ} (hG : ProperlyDiscontinuousSMul G α) (hGH : H ≤ G) :
    ProperlyDiscontinuousSMul H α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hG ⊢
  intro K L hK hL
  exact (hG hK hL).subset fun _ ⟨hg, hg'⟩ ↦ ⟨hGH hg, hg'⟩

/-- If `Γ` acts properly discontinuously, so does every subgroup of `Γ`. -/
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Γ` acts properly discontinuously, so does every subgroup of `Γ`.
-/
instance [SMul Γ α] [ProperlyDiscontinuousSMul Γ α] (G : Subgroup Γ) :
    ProperlyDiscontinuousSMul G α := by
  refine Subgroup.properlyDiscontinuousSMul_of_le ?_ le_top
  simp only [Subgroup.properlyDiscontinuousSMul_iff, Subgroup.mem_top, true_and]
  exact finite_disjoint_inter_image

open Pointwise in
/-- If `G, H` are subgroups of `Γ` which acts on `α`, and `G ∩ H` has finite index in `G`,
then `G` acts properly discontinuously if `H` does. -/
@[to_additive]
/-
**ProperlyDiscontinuousSMul.ofFiniteRelIndex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperlyDiscontinuousSMul.ofFiniteRelIndex [MulAction Γ α] [ContinuousCons
tSMul Γ α] (G H : Subgroup Γ) [hH : ProperlyDiscontinuousSMul H α] [H.IsFiniteRe
lIndex G] : ProperlyDiscontinuousSMul G α
参数：G H : Subgroup Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.properlyDiscontinuousSMul_iff`：∀ {Γ : Type u_1} {α : Type u_2} 
[inst : Group Γ] [inst_1 : TopologicalSpace α] [inst_2 : SMul Γ α] (S : Subgroup
 Γ),   ProperlyDiscontinuous…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用引理 `Subgroup.exists_isComplement_right`：exists_isComplement_right (H : Subgr
oup G) (g : G) : exists T, IsComplement H T ∧ g in T
· 使用定理 `Subgroup.IsFiniteRelIndex.to_finiteIndex_subgroupOf`：∀ {G : Type u_1} [i
nst : Group G] {H K : Subgroup G} [H.IsFiniteRelIndex K], (H.subgroupOf K).Finit
eIndex
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Subgroup.IsComplement.existsUnique`：∀ {G : Type u_1} [inst : Group G] {S
 T : Set G}, Subgroup.IsComplement S T → ∀ (g : G), ∃! x, ↑x.1 * ↑x.2 = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.Finite.map`：∀ {α β : Type u_1} {s : Set α} (f : α → β), s.Finite → (
f <$> s).Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩

--- 原说明 ---
If `G, H` are subgroups of `Γ` which acts on `α`, and `G ∩ H` has finite index i
n `G`,
then `G` acts properly discontinuously if `H` does.
-/
lemma ProperlyDiscontinuousSMul.ofFiniteRelIndex [MulAction Γ α] [ContinuousConstSMul Γ α]
    (G H : Subgroup Γ) [hH : ProperlyDiscontinuousSMul H α] [H.IsFiniteRelIndex G] :
    ProperlyDiscontinuousSMul G α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hH ⊢
  intro K L hK hL
  have (t : Γ) : {g | g ∈ H ∧ (g • t • K ∩ L).Nonempty}.Finite :=
    hH (hK.image <| continuous_const_smul t) hL
  obtain ⟨S, hS, -⟩ := (H.subgroupOf G).exists_isComplement_right 1
  have hT : (Subtype.val '' S).Finite := by
    have : Fintype (G ⧸ H.subgroupOf G) := Subgroup.fintypeQuotientOfFiniteIndex
    have : Fintype S := .ofEquiv _ hS.rightQuotientEquiv
    exact (toFinite S).image _
  have hS' {g : Γ} (hg : g ∈ G) : ∃ t ∈ Subtype.val '' S, g * t⁻¹ ∈ H := by
    obtain ⟨p, hp⟩ := (hS.existsUnique ⟨g, hg⟩).exists
    aesop
  refine (hT.biUnion <| fun t ht ↦ (this t).map fun g ↦ g * t).subset fun g ↦ ?_
  simp [mul_smul]
  grind

@[to_additive]
/-
**Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex [MulAction Γ α]
 [ContinuousConstSMul Γ α] {G H : Subgroup Γ} (hGH : G <= H) [IsFiniteRelIndex G
 H] : ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α
参数：hGH : G <= H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProperlyDiscontinuousSMul.ofFiniteRelIndex`：ProperlyDiscontinuousSMul.of
FiniteRelIndex [MulAction Γ α] [ContinuousConstSMul Γ α] (G H : Subgroup Γ) [hH 
: ProperlyDiscontinuousSMul H α]…
· 使用引理 `Subgroup.properlyDiscontinuousSMul_of_le`：Subgroup.properlyDiscontinuous
SMul_of_le [SMul Γ α] {G H : Subgroup Γ} (hG : ProperlyDiscontinuousSMul G α) (h
GH : H <= G) : ProperlyDiscont…
-/
lemma Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (hGH : G ≤ H) [IsFiniteRelIndex G H] :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α :=
  ⟨fun _ ↦ .ofFiniteRelIndex H G, (properlyDiscontinuousSMul_of_le · hGH)⟩

@[to_additive]
/-
**Subgroup.Commensurable.properlyDiscontinuousSMul_iff** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Subgroup.Commensurable.properlyDiscontinuousSMul_iff [MulAction Γ α] [Cont
inuousConstSMul Γ α] {G H : Subgroup Γ} (h : G.Commensurable H) : ProperlyDiscon
tinuousSMul G α ↔ ProperlyDiscontinuousSMul H α
参数：h : G.Commensurable H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subgroup.inf_relIndex_left`：inf_relIndex_left : (H ⊓ K).relIndex H = K.r
elIndex H
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex`：Subgroup.pro
perlyDiscontinuousSMul_iff_of_isFiniteRelIndex [MulAction Γ α] [ContinuousConstS
Mul Γ α] {G H : Subgroup Γ} (hGH : G <= H) [IsFi…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma Subgroup.Commensurable.properlyDiscontinuousSMul_iff
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (h : G.Commensurable H) :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α := by
  have : IsFiniteRelIndex (G ⊓ H) H := ⟨Subgroup.inf_relIndex_right G H ▸ h.1⟩
  have : IsFiniteRelIndex (G ⊓ H) G := ⟨Subgroup.inf_relIndex_left G H ▸ h.2⟩
  calc ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul ↑(G ⊓ H) α :=
    (properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ ProperlyDiscontinuousSMul H α :=
    properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_right

end

