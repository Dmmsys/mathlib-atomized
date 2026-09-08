/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# When a proper action is properly discontinuous

This file proves that if a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact.

## Main statements

* `properlyDiscontinuousSMul_iff_properSMul`: If a discrete group acts on a T2 space `X` such that
  `X × X` is compactly generated, and if the action is continuous in the second variable,
  then the action is properly discontinuous if and only if it is proper.
* `MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty`: if `G` is a topological group
  acting continuously on a T2 space `X` such that `X × X` is compactly generated, then the action is
  proper iff, for each pair of compacts `U, V ⊆ X`, the set of `g : G` such that `g • U` intersects
  `V` is compact.

## Tags

group action, proper action, properly discontinuous, compactly generated
-/

open scoped Pointwise

open Prod Set

public section

variable {G X : Type*} [TopologicalSpace X] [Group G]
  [TopologicalSpace G] [MulAction G X] [CompactlyGeneratedSpace (X × X)] [T2Space X]

/-- The `G`-action on `X` is proper iff, for each pair of compacts `U, V` in `X`,
the set of `g` such that `U` intersects `g • V` is compact.

See `ProperSMul.isCompact_setOfPred_inter_nonempty`
for a one-way implication with fewer conditions.

**Note**: We assume `CompactlyCoherentSpace (X × X)`
as this is the minimal assumption needed to make the proof work;
but this follows from various more familiar conditions,
such as `FirstCountableTopology X`.
Importing `Mathlib.Topology.Sequences` makes this implication available.
-/
@[to_additive /--
The `G`-action on `X` is proper iff, for each pair of compacts `U, V` in `X`,
the set of `g` such that `U` intersects `g +ᵥ V` is compact.

See `ProperVAdd.isCompact_setOfPred_inter_nonempty`
for a one-way implication with fewer conditions.

**Note**: We assume `CompactlyCoherentSpace (X × X)`
as this is the minimal assumption needed to make the proof work;
but this follows from various more familiar conditions,
such as `FirstCountableTopology X`.
Importing `Mathlib.Topology.Sequences` makes this implication available.
-/]
/-
**MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty [ContinuousSMu
l G X] : ProperSMul G X ↔ (forall {U V : Set X}, IsCompact U -> IsCompact V -> I
sCompact {g : G | (g • U inter V).Nonempty})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProperSMul.isCompact_setOfPred_inter_nonempty`：ProperSMul.isCompact_setO
fPred_inter_nonempty {G : Type*} [Group G] [MulAction G X] [TopologicalSpace G] 
[ProperSMul G X] {U V : Set X} (hU …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isProperMap_iff_isCompact_preimage`：isProperMap_iff_isCompact_preimage :
 IsProperMap f ↔ Continuous f ∧ forall ⦃K⦄, IsCompact K -> IsCompact (f ⁻¹' K) w
here mp hf
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.subset_fst_image_prod_snd_image`：subset_fst_image_prod_snd_image {s 
: Set (α × β)} : s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s)
-/
lemma MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty [ContinuousSMul G X] :
    ProperSMul G X ↔
    (∀ {U V : Set X}, IsCompact U → IsCompact V → IsCompact {g : G | (g • U ∩ V).Nonempty}) := by
  refine ⟨fun h ↦ ProperSMul.isCompact_setOfPred_inter_nonempty, fun h ↦ ⟨?_⟩⟩
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun {K} hK ↦ ?_⟩
  -- First reduce to the case `K = U × V`.
  let U := Prod.fst '' K
  let V := Prod.snd '' K
  have hU : IsCompact U := hK.image continuous_fst
  have hV : IsCompact V := hK.image continuous_snd
  suffices IsCompact ((fun (gx : G × X) ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (U ×ˢ V)) by
    apply this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop)
    exact Set.preimage_mono Set.subset_fst_image_prod_snd_image
  apply ((h hV hU).prod hV).of_isClosed_subset
  · exact (hU.prod hV).isClosed.preimage (by fun_prop)
  · exact fun ⟨g, x⟩ ⟨hgx, hgx'⟩ ↦ ⟨⟨g • x, smul_mem_smul_set hgx', hgx⟩, hgx'⟩

@[deprecated (since := "2026-07-09")]
alias MulAction.properSMul_iff_isCompact_setOf_inter_nonempty :=
  MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty

@[deprecated (since := "2026-07-09")]
alias AddAction.properVAdd_iff_isCompact_setOf_inter_nonempty :=
  AddAction.properVAdd_iff_isCompact_setOfPred_inter_nonempty

/-- If a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the action is properly
discontinuous if and only if it is proper. This is in particular true if `X` is first-countable or
weakly locally compact. -/
@[to_additive]
/-
**properlyDiscontinuousSMul_iff_properSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：properlyDiscontinuousSMul_iff_properSMul [DiscreteTopology G] [ContinuousC
onstSMul G X] : ProperlyDiscontinuousSMul G X ↔ ProperSMul G X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_prod_of_discrete_left`：continuous_prod_of_discrete_left [Disc
reteTopology α] {f : α × β -> γ} : Continuous f ↔ forall a, Continuous (f ⟨a, ·⟩
)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `properlyDiscontinuousSMul_iff`：properlyDiscontinuousSMul_iff [Topologica
lSpace α] [SMul M α] : ProperlyDiscontinuousSMul M α ↔ forall {K L : Set α}, IsC
ompact K -> IsCompa…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a discrete group acts on a T2 space `X` such that `X × X` is compactly
generated, and if the action is continuous in the second variable, then the acti
on is properly
discontinuous if and only if it is proper. This is in particular true if `X` is 
first-countable or
weakly locally compact.
-/
theorem properlyDiscontinuousSMul_iff_properSMul [DiscreteTopology G] [ContinuousConstSMul G X] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by
  have : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  simp only [MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty, isCompact_iff_finite]
  rw [properlyDiscontinuousSMul_iff]

end

