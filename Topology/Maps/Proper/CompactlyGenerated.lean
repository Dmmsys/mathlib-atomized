/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# A map is proper iff preimage of compact sets are compact

This file proves that if `Y` is a Hausdorff and compactly generated space, a continuous map
`f : X → Y` is proper if and only if preimage of compact sets are compact.
-/

public section

open Set Filter

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space Y] [CompactlyCoherentSpace Y]
variable {f : X → Y}

/-- If `Y` is Hausdorff and compactly generated, then proper maps `X → Y` are exactly
continuous maps such that the preimage of any compact set is compact. This is in particular true
if `Y` is Hausdorff and sequential or locally compact.

There was an older version of this theorem which was changed to this one to make use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10) -/
/-
**isProperMap_iff_isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_iff_isCompact_preimage : IsProperMap f ↔ Continuous f ∧ forall
 ⦃K⦄, IsCompact K -> IsCompact (f ⁻¹' K) where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.continuous`：IsProperMap.continuous (h : IsProperMap f) : Con
tinuous f
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isProperMap_iff_isClosedMap_and_compact_fibers`：isProperMap_iff_isClosed
Map_and_compact_fibers : IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ forall y
, IsCompact (f ⁻¹' {y})
· 使用引理 `CompactlyCoherentSpace.isClosed_iff`：isClosed_iff [CompactlyCoherentSpac
e X] (A : Set X) : IsClosed A ↔ forall K, IsCompact K -> IsClosed (K ↓inter A)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.inter_left`：IsCompact.inter_left (ht : IsCompact t) (hs : IsCl
osed s) : IsCompact (s inter t)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)

--- 原说明 ---
If `Y` is Hausdorff and compactly generated, then proper maps `X → Y` are exactl
y
continuous maps such that the preimage of any compact set is compact. This is in
 particular true
if `Y` is Hausdorff and sequential or locally compact.

There was an older version of this theorem which was changed to this one to make
 use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10)
-/
theorem isProperMap_iff_isCompact_preimage :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) where
  mp hf := ⟨hf.continuous, fun _ ↦ hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ ↦ isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun s hs ↦ (CompactlyCoherentSpace.isClosed_iff _).mpr fun K hK ↦ by
        convert! (((h hK).inter_left hs).image hf).isClosed.preimage continuous_subtype_val using 1
        aesop, fun _ ↦ h isCompact_singleton⟩

/-- Version of `isProperMap_iff_isCompact_preimage` in terms of `cocompact`.

There was an older version of this theorem which was changed to this one to make use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10) -/
/-
**isProperMap_iff_tendsto_cocompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_iff_tendsto_cocompact : IsProperMap f ↔ Continuous f ∧ Tendsto
 f (cocompact X) (cocompact Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y

--- 原说明 ---
Version of `isProperMap_iff_isCompact_preimage` in terms of `cocompact`.

There was an older version of this theorem which was changed to this one to make
 use
of the `CompactlyGeneratedSpace` typeclass. (since 2024-11-10)
-/
lemma isProperMap_iff_tendsto_cocompact :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont ↦
    ⟨fun H K hK ↦ (H hK).compl_mem_cocompact, fun H K hK ↦ ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact hK'.of_isClosed_subset (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)
