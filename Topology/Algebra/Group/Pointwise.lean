/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Pointwise operations on sets in topological groups

-/

public section

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}


/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `Submonoid.top_closure_mul_self_eq` in
`Topology.Algebra.Monoid`.
-/

section ContinuousConstSMul

variable [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousConstSMul α β] {s : Set α}
  {t : Set β}

variable [TopologicalSpace α]

@[to_additive]
/-
**subset_interior_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_smul : interior s • interior t subseteq interior (s • t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_subset_smul_right`：smul_subset_smul_right : s₁ subseteq s₂ -> s
₁ • t subseteq s₂ • t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_interior_smul_right`：subset_interior_smul_right {s : Set G} {t : 
Set α} : s • interior t subseteq interior (s • t)
-/
theorem subset_interior_smul : interior s • interior t ⊆ interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace α] [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousInv α]
  [ContinuousSMul α β] {s : Set α} {t : Set β}

open Prod in
/-- If `G` acts on `X` continuously, the set `s • t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.smul_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/
@[to_additive
/-- If `G` acts on `X` continuously, the set `s +ᵥ t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.vadd_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/]
/-
**IsClosed.smul_left_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.smul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsC
losed (s • t)
参数：ht : IsClosed t；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_subset_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {
s : Set α} {t u : Set β}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `isProperMap_snd_of_compactSpace`：isProperMap_snd_of_compactSpace [Compac
tSpace X] : IsProperMap (Prod.snd : X × Y -> Y)
· 使用定理 `Homeomorph.isProperMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y), IsProperMap ⇑e
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem IsClosed.smul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (s • t) := by
  let Φ : s × β ≃ₜ s × β :=
  { toFun := fun gx ↦ (gx.1, (gx.1 : α) • gx.2)
    invFun := fun gx ↦ (gx.1, (gx.1 : α)⁻¹ • gx.2)
    left_inv := fun _ ↦ by simp
    right_inv := fun _ ↦ by simp }
  have : s • t = (snd ∘ Φ) '' snd ⁻¹' t :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx ↦ mem_image_of_mem (snd ∘ Φ) (x := ⟨⟨g, hg⟩, x⟩) hx)
      (image_subset_iff.mpr fun ⟨⟨g, hg⟩, x⟩ hx ↦ smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact (isProperMap_snd_of_compactSpace.comp Φ.isProperMap).isClosedMap _
    (ht.preimage continuous_snd)

@[to_additive]
/-
**MulAction.isClosedMap_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.isClosedMap_quotient [CompactSpace α] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
· 使用定理 `MulAction.quotient_preimage_image_eq_union_mul`：quotient_preimage_image_
eq_union_mul (U : Set α) : letI
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
· 使用定理 `Set.iUnion_smul_left_image`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul
 α β] {s : Set α} {t : Set β}, ⋃ a ∈ s, a • t = s • t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsClosed.smul_left_of_isCompact`：IsClosed.smul_left_of_isCompact (ht : I
sClosed t) (hs : IsCompact s) : IsClosed (s • t)
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
theorem MulAction.isClosedMap_quotient [CompactSpace α] :
    letI := orbitRel α β
    IsClosedMap (Quotient.mk' : β → Quotient (orbitRel α β)) := by
  intro t ht
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage,
    MulAction.quotient_preimage_image_eq_union_mul]
  convert! ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ, ← iUnion_smul_left_image]
  simp only [image_smul]

end ContinuousSMul

section ContinuousConstSMul

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul α α] {s t : Set α}

@[to_additive]
/-
**IsOpen.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mul_left : IsOpen t -> IsOpen (s * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.smul_left`：IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen 
t) : IsOpen (s • t)
-/
theorem IsOpen.mul_left : IsOpen t → IsOpen (s * t) :=
  IsOpen.smul_left

@[to_additive]
/-
**subset_interior_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_mul_right : s * interior t subseteq interior (s * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_interior_smul_right`：subset_interior_smul_right {s : Set G} {t : 
Set α} : s • interior t subseteq interior (s • t)
-/
theorem subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
  subset_interior_smul_right

@[to_additive]
/-
**subset_interior_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_mul : interior s * interior t subseteq interior (s * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_interior_smul`：subset_interior_smul : interior s • interior t sub
seteq interior (s • t)
-/
theorem subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
  subset_interior_smul

@[to_additive]
/-
**singleton_mul_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_mem_nhds (a : α) {b : α} (h : s in 𝓝 b) : {a} * s in 𝓝 (a * 
b)
参数：a : α；h : s in 𝓝 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `Set.singleton_smul`：singleton_smul : ({a} : Set α) • t = a • t
· 使用定理 `smul_mem_nhds_smul_iff`：smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : 
α} : g • t in 𝓝 (g • a) ↔ t in 𝓝 a
-/
theorem singleton_mul_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : {a} * s ∈ 𝓝 (a * b) := by
  rwa [← smul_eq_mul, ← smul_eq_mul, singleton_smul, smul_mem_nhds_smul_iff]

@[to_additive]
/-
**singleton_mul_mem_nhds_of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s in 𝓝 (1 : α)) : {a} * s 
in 𝓝 a
参数：a : α；h : s in 𝓝 (1 : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `singleton_mul_mem_nhds`：singleton_mul_mem_nhds (a : α) {b : α} (h : s in
 𝓝 b) : {a} * s in 𝓝 (a * b)
-/
theorem singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : {a} * s ∈ 𝓝 a := by
  simpa only [mul_one] using singleton_mul_mem_nhds a h

end ContinuousConstSMul

section ContinuousConstSMulOp

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul αᵐᵒᵖ α] {s t : Set α}

@[to_additive]
/-
**IsOpen.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_op_smul`：image_op_smul : (op '' s) • t = t * s
· 使用定理 `IsOpen.smul_left`：IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen 
t) : IsOpen (s • t)
-/
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← image_op_smul]
  exact hs.smul_left

@[to_additive]
/-
**subset_interior_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_mul_left : interior s * t subseteq interior (s * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.mul_right`：IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right

@[to_additive]
/-
**subset_interior_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_mul' : interior s * interior t subseteq interior (s * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_interior_mul_left`：subset_interior_mul_left : interior s * t subs
eteq interior (s * t)
-/
theorem subset_interior_mul' : interior s * interior t ⊆ interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

@[to_additive]
/-
**mul_singleton_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_singleton_mem_nhds (a : α) {b : α} (h : s in 𝓝 b) : s * {a} in 𝓝 (b * 
a)
参数：a : α；h : s in 𝓝 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `smul_mem_nhds_smul`：∀ {α : Type u_2} {G : Type u_4} [inst : TopologicalS
pace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [ContinuousConstSMul G α] 
{t : Set…
-/
theorem mul_singleton_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : s * {a} ∈ 𝓝 (b * a) := by
  rw [mul_singleton]
  exact smul_mem_nhds_smul (op a) h

@[to_additive]
/-
**mul_singleton_mem_nhds_of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s in 𝓝 (1 : α)) : s * {a} 
in 𝓝 a
参数：a : α；h : s in 𝓝 (1 : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_singleton_mem_nhds`：mul_singleton_mem_nhds (a : α) {b : α} (h : s in
 𝓝 b) : s * {a} in 𝓝 (b * a)
-/
theorem mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : s * {a} ∈ 𝓝 a := by
  simpa only [one_mul] using mul_singleton_mem_nhds a h

end ContinuousConstSMulOp

section SeparatelyContinuousMul

variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]

@[to_additive]
/-
**closure_subset_mul_left_of_mem_nhds_one_of_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_mul_left_of_mem_nhds_one_of_inv {s : Set G} (s' : Set G) (h
s₀ : s in 𝓝 1) (h_symm : forall x in s, x⁻¹ in s) : closure s' subseteq s * s'
参数：s' : Set G；hs₀ : s in 𝓝 1；h_symm : forall x in s, x⁻¹ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
· 使用定理 `isOpenMap_mul_right`：isOpenMap_mul_right (a : G) : IsOpenMap (· * a)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
-/
theorem closure_subset_mul_left_of_mem_nhds_one_of_inv {s : Set G} (s' : Set G)
    (hs₀ : s ∈ 𝓝 1) (h_symm : ∀ x ∈ s, x⁻¹ ∈ s) :
    closure s' ⊆ s * s' := by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((· * y) '' s)
      (by simpa using (isOpenMap_mul_right y).image_mem_nhds hs₀)
  simpa using Set.mul_mem_mul (h_symm b hb) hc

@[to_additive]
/-
**closure_subset_mul_right_of_mem_nhds_one_of_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_mul_right_of_mem_nhds_one_of_inv (s : Set G) {s' : Set G} (
hs'₀ : s' in 𝓝 1) (h_symm : forall x in s', x⁻¹ in s') : closure s subseteq s * 
s'
参数：s : Set G；hs'₀ : s' in 𝓝 1；h_symm : forall x in s', x⁻¹ in s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
· 使用引理 `isOpenMap_mul_left`：isOpenMap_mul_left (a : G) : IsOpenMap (a * ·)
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
-/
theorem closure_subset_mul_right_of_mem_nhds_one_of_inv (s : Set G) {s' : Set G}
    (hs'₀ : s' ∈ 𝓝 1) (h_symm : ∀ x ∈ s', x⁻¹ ∈ s') :
    closure s ⊆ s * s' := by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((y * ·) '' s')
      (by simpa using (isOpenMap_mul_left y).image_mem_nhds hs'₀)
  simpa using Set.mul_mem_mul hc (h_symm b hb)

@[to_additive]
/-
**closure_subset_of_mem_nhds_one_of_inv_mul_left_subset** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：closure_subset_of_mem_nhds_one_of_inv_mul_left_subset {s s' t : Set G} (hs
₀ : s in 𝓝 1) (h_symm : forall x in s, x⁻¹ in s) (hs : s * s' subseteq t) : clos
ure s' subseteq t
参数：hs₀ : s in 𝓝 1；h_symm : forall x in s, x⁻¹ in s；hs : s * s' subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_subset_mul_left_of_mem_nhds_one_of_inv`：closure_subset_mul_left_
of_mem_nhds_one_of_inv {s : Set G} (s' : Set G) (hs₀ : s in 𝓝 1) (h_symm : foral
l x in s, x⁻¹ in s) : closure s' sub…
-/
theorem closure_subset_of_mem_nhds_one_of_inv_mul_left_subset {s s' t : Set G}
    (hs₀ : s ∈ 𝓝 1) (h_symm : ∀ x ∈ s, x⁻¹ ∈ s) (hs : s * s' ⊆ t) :
    closure s' ⊆ t :=
  closure_subset_mul_left_of_mem_nhds_one_of_inv s' hs₀ h_symm |>.trans hs

@[to_additive]
/-
**closure_subset_of_mem_nhds_one_of_inv_mul_right_subset** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：closure_subset_of_mem_nhds_one_of_inv_mul_right_subset {s s' t : Set G} (h
s'₀ : s' in 𝓝 1) (h_symm : forall x in s', x⁻¹ in s') (hs : s * s' subseteq t) :
 closure s subseteq t
参数：hs'₀ : s' in 𝓝 1；h_symm : forall x in s', x⁻¹ in s'；hs : s * s' subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_subset_mul_right_of_mem_nhds_one_of_inv`：closure_subset_mul_righ
t_of_mem_nhds_one_of_inv (s : Set G) {s' : Set G} (hs'₀ : s' in 𝓝 1) (h_symm : f
orall x in s', x⁻¹ in s') : closure s…
-/
theorem closure_subset_of_mem_nhds_one_of_inv_mul_right_subset {s s' t : Set G}
    (hs'₀ : s' ∈ 𝓝 1) (h_symm : ∀ x ∈ s', x⁻¹ ∈ s') (hs : s * s' ⊆ t) :
    closure s ⊆ t :=
  closure_subset_mul_right_of_mem_nhds_one_of_inv s hs'₀ h_symm |>.trans hs

end SeparatelyContinuousMul

section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {s t : Set G}

@[to_additive]
/-
**IsOpen.div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t)
参数：ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_div_left_image`：iUnion_div_left_image : ⋃ a in s, (a / ·) '' 
t = s / t
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `isOpenMap_div_left`：isOpenMap_div_left (a : G) : IsOpenMap (a / ·)
-/
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht

@[to_additive]
/-
**IsOpen.div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_div_right_image`：iUnion_div_right_image : ⋃ a in t, (· / a) '
' s = s / t
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用引理 `isOpenMap_div_right`：isOpenMap_div_right (a : G) : IsOpenMap (· / a)
-/
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs

@[to_additive]
/-
**subset_interior_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_div_left : interior s / t subseteq interior (s / t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.div_subset_div_right`：div_subset_div_right : s₁ subseteq s₂ -> s₁ / 
t subseteq s₂ / t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.div_right`：IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right

@[to_additive]
/-
**subset_interior_div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_div_right : s / interior t subseteq interior (s / t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.div_subset_div_left`：div_subset_div_left : t₁ subseteq t₂ -> s / t₁ 
subseteq s / t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.div_left`：IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left

@[to_additive]
/-
**subset_interior_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_div : interior s / interior t subseteq interior (s / t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.div_subset_div_left`：div_subset_div_left : t₁ subseteq t₂ -> s / t₁ 
subseteq s / t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `subset_interior_div_left`：subset_interior_div_left : interior s / t subs
eteq interior (s / t)
-/
theorem subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]
/-
**IsOpen.mul_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s * closure t = s * t
参数：hs : IsOpen s；t : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `Set.inv_mem_inv`：inv_mem_inv : a⁻¹ in s⁻¹ ↔ a in s
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `IsOpen.mul_right`：IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsOpen.inv`：IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s * closure t = s * t := by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩

@[to_additive]
/-
**IsOpen.closure_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : closure s * t = s * t
参数：ht : IsOpen t；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_closure`：inv_closure : forall s : Set G, (closure s)⁻¹ = closure s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `IsOpen.mul_closure`：IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s *
 closure t = s * t
· 使用定理 `IsOpen.inv`：IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹
-/
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
    inv_inv]

@[to_additive]
/-
**IsOpen.div_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.div_closure (hs : IsOpen s) (t : Set G) : s / closure t = s / t
参数：hs : IsOpen s；t : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_closure`：inv_closure : forall s : Set G, (closure s)⁻¹ = closure s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOpen.mul_closure`：IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s *
 closure t = s * t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set G) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]
/-
**IsOpen.closure_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.closure_div (ht : IsOpen t) (s : Set G) : closure s / t = s / t
参数：ht : IsOpen t；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOpen.closure_mul`：IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : clo
sure s * t = s * t
· 使用定理 `IsOpen.inv`：IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set G) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

@[to_additive]
/-
**IsClosed.mul_left_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsCl
osed (s * t)
参数：ht : IsClosed t；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.smul_left_of_isCompact`：IsClosed.smul_left_of_isCompact (ht : I
sClosed t) (hs : IsCompact s) : IsClosed (s • t)
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem IsClosed.mul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsClosed (s * t) :=
  ht.smul_left_of_isCompact hs

@[to_additive]
/-
**IsClosed.mul_right_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mul_right_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsC
losed (t * s)
参数：ht : IsClosed t；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_op_smul`：image_op_smul : (op '' s) • t = t * s
· 使用定理 `IsClosed.smul_left_of_isCompact`：IsClosed.smul_left_of_isCompact (ht : I
sClosed t) (hs : IsCompact s) : IsClosed (s • t)
· 使用定理 `instContinuousInvMulOpposite`：∀ {α : Type u} [inst : TopologicalSpace α]
 [inst_1 : Inv α] [ContinuousInv α], ContinuousInv αᵐᵒᵖ
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
-/
theorem IsClosed.mul_right_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (t * s) := by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]
/-
**subset_mul_closure_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_mul_closure_one {G} [MulOneClass G] [TopologicalSpace G] (s : Set G
) : s subseteq s * (closure {1} : Set G)
参数：s : Set G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_subset_smul_left`：smul_subset_smul_left : t₁ subseteq t₂ -> s •
 t₁ subseteq s • t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma subset_mul_closure_one {G} [MulOneClass G] [TopologicalSpace G] (s : Set G) :
    s ⊆ s * (closure {1} : Set G) := by
  have : s ⊆ s * ({1} : Set G) := by simp
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]
/-
**IsCompact.mul_closure_one_eq_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.mul_closure_one_eq_closure {K : Set G} (hK : IsCompact K) : K * 
(closure {1} : Set G) = closure K
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Set.smul_subset_smul_right`：smul_subset_smul_right : s₁ subseteq s₂ -> s
₁ • t subseteq s₂ • t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `smul_set_closure_subset`：smul_set_closure_subset (K : Set M) (L : Set X)
 : closure K • closure L subseteq closure (K • L)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsClosed.smul_left_of_isCompact`：IsClosed.smul_left_of_isCompact (ht : I
sClosed t) (hs : IsCompact s) : IsClosed (s • t)
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `subset_mul_closure_one`：subset_mul_closure_one {G} [MulOneClass G] [Topo
logicalSpace G] (s : Set G) : s subseteq s * (closure {1} : Set G)
-/
lemma IsCompact.mul_closure_one_eq_closure {K : Set G} (hK : IsCompact K) :
    K * (closure {1} : Set G) = closure K := by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) ⊆ closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ ⊆ closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]
/-
**IsClosed.mul_closure_one_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.mul_closure_one_eq {F : Set G} (hF : IsClosed F) : F * (closure {
1} : Set G) = F
参数：hF : IsClosed F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `smul_set_closure_subset`：smul_set_closure_subset (K : Set M) (L : Set X)
 : closure K • closure L subseteq closure (K • L)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `subset_mul_closure_one`：subset_mul_closure_one {G} [MulOneClass G] [Topo
logicalSpace G] (s : Set G) : s subseteq s * (closure {1} : Set G)
-/
lemma IsClosed.mul_closure_one_eq {F : Set G} (hF : IsClosed F) :
    F * (closure {1} : Set G) = F := by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ ⊆ closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp

@[to_additive]
/-
**compl_mul_closure_one_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compl_mul_closure_one_eq {t : Set G} (ht : t * (closure {1} : Set G) = t) 
: tᶜ * (closure {1} : Set G) = tᶜ
参数：ht : t * (closure {1} : Set G) = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.coe_topologicalClosure_bot`：Subgroup.coe_topologicalClosure_bot
 : ((⊥ : Subgroup G).topologicalClosure : Set G) = _root_.closure ({1} : Set G)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `subset_mul_closure_one`：subset_mul_closure_one {G} [MulOneClass G] [Topo
logicalSpace G] (s : Set G) : s subseteq s * (closure {1} : Set G)
-/
lemma compl_mul_closure_one_eq {t : Set G} (ht : t * (closure {1} : Set G) = t) :
    tᶜ * (closure {1} : Set G) = tᶜ := by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x ∈ t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]
/-
**compl_mul_closure_one_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compl_mul_closure_one_eq_iff {t : Set G} : tᶜ * (closure {1} : Set G) = tᶜ
 ↔ t * (closure {1} : Set G) = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `compl_mul_closure_one_eq`：compl_mul_closure_one_eq {t : Set G} (ht : t *
 (closure {1} : Set G) = t) : tᶜ * (closure {1} : Set G) = tᶜ
-/
lemma compl_mul_closure_one_eq_iff {t : Set G} :
    tᶜ * (closure {1} : Set G) = tᶜ ↔ t * (closure {1} : Set G) = t :=
  ⟨fun h ↦ by simpa using compl_mul_closure_one_eq h, fun h ↦ compl_mul_closure_one_eq h⟩

@[to_additive]
/-
**IsOpen.mul_closure_one_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.mul_closure_one_eq {U : Set G} (hU : IsOpen U) : U * (closure {1} :
 Set G) = U
参数：hU : IsOpen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `compl_mul_closure_one_eq_iff`：compl_mul_closure_one_eq_iff {t : Set G} :
 tᶜ * (closure {1} : Set G) = tᶜ ↔ t * (closure {1} : Set G) = t
· 使用引理 `IsClosed.mul_closure_one_eq`：IsClosed.mul_closure_one_eq {F : Set G} (hF
 : IsClosed F) : F * (closure {1} : Set G) = F
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
-/
lemma IsOpen.mul_closure_one_eq {U : Set G} (hU : IsOpen U) :
    U * (closure {1} : Set G) = U :=
  compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

@[to_additive]
/-
**closure_subset_mul_self_of_mem_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_mul_self_of_mem_nhds_one {U : Set G} (hU : U in 𝓝 1) : clos
ure U subseteq U * U
参数：hU : U in 𝓝 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `ContinuousAt.fun_div'`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Div G]   [ContinuousDiv G] {f
 g : X → G}…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem closure_subset_mul_self_of_mem_nhds_one {U : Set G} (hU : U ∈ 𝓝 1) :
    closure U ⊆ U * U := by
  intro x hx
  rw [mem_closure_iff_nhds] at hx
  have hkey : (fun y => x / y) ⁻¹' U ∈ 𝓝 x :=
    ContinuousAt.preimage_mem_nhds (by fun_prop) (by simpa)
  obtain ⟨a, ha_mem, ha_s⟩ := hx _ hkey
  exact Set.mem_mul.mpr ⟨x / a, ha_mem, a, ha_s, div_mul_cancel x a⟩

end IsTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsTopologicalGroup.regularSpace : RegularSpace G := by
  refine .of_exists_mem_nhds_isClosed_subset fun a s hs ↦ ?_
  have : Tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff, image_prod] at hUV
  refine ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, ?_⟩
  calc
    closure U ⊆ closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := isOpen_interior.closure_mul U
    _ ⊆ U * V := mul_subset_mul_left interior_subset
    _ ⊆ s := hUV

variable {G}

@[to_additive]
/-
**group_inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：group_inseparable_iff {x y : G} : Inseparable x y ↔ x / y in closure (1 : 
Set G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_one`：singleton_one : ({1} : Set α) = 1
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
· 使用定理 `specializes_comm`：specializes_comm : x ⤳ y ↔ y ⤳ x
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `specializes_iff_inseparable`：specializes_iff_inseparable : x ⤳ y ↔ Insep
arable x y
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem group_inseparable_iff {x y : G} : Inseparable x y ↔ x / y ∈ closure (1 : Set G) := by
  rw [← singleton_one, ← specializes_iff_mem_closure, specializes_comm, specializes_iff_inseparable,
    ← (Homeomorph.mulRight y⁻¹).isEmbedding.inseparable_iff]
  simp [div_eq_mul_inv]

@[to_additive]
/-
**IsTopologicalGroup.t2Space_iff_one_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Se
t G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `IsTopologicalGroup.t1Space`：IsTopologicalGroup.t1Space (h : @IsClosed G 
_ {1}) : T1Space G
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
-/
theorem IsTopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  ⟨fun _ ↦ isClosed_singleton, fun h ↦
    have := IsTopologicalGroup.t1Space G h; inferInstance⟩

@[to_additive]
/-
**IsTopologicalGroup.t2Space_of_one_sep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.t2Space_of_one_sep (H : forall x : G, x != 1 -> exists 
U in 𝓝 (1 : G), x ∉ U) : T2Space G
参数：H : forall x : G, x != 1 -> exists U in 𝓝 (1 : G), x ∉ U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t1Space_iff_specializes_imp_eq`：t1Space_iff_specializes_imp_eq : T1Space
 X ↔ forall ⦃x y : X⦄, x ⤳ y -> x = y
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
-/
theorem IsTopologicalGroup.t2Space_of_one_sep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ 𝓝 (1 : G), x ∉ U) :
    T2Space G := by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec ↦ by_contra fun hne ↦ ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
  exact hU <| mem_of_mem_nhds <| hspec.map (continuous_mul_const y⁻¹) (by rwa [mul_inv_cancel])

/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is closed, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive /-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is closed, symmetric, and satisfies `V + V ⊆ U`. -/]
/-
**exists_closed_nhds_one_inv_eq_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_closed_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U in 𝓝 1) : exi
sts V in 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧ V * V subseteq U
参数：hU : U in 𝓝 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_open_nhds_one_mul_subset`：exists_open_nhds_one_mul_subset {U : Se
t M} (hU : U in 𝓝 (1 : M)) : exists V : Set M, IsOpen V ∧ (1 : M) in V ∧ V * V s
ubseteq U
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `inv_mem_nhds_one`：inv_mem_nhds_one {S : Set G} (hS : S in (𝓝 1 : Filter 
G)) : S⁻¹ in 𝓝 (1 : G)
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.inv`：IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mul_subset_mul`：mul_subset_mul : s₁ subseteq t₁ -> s₂ subseteq t₂ ->
 s₁ * s₂ subseteq t₁ * t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem exists_closed_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ V ∈ 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W ∩ W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W ∩ W⁻¹ * (W ∩ W⁻¹)
    ⊆ W * W := mul_subset_mul inter_subset_left inter_subset_left
  _ ⊆ V * V := mul_subset_mul hW hW
  _ ⊆ U := hV
/-
**IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty** 是 Mathlib 中的一个
定理，位于命名空间 `IsDiscrete`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologic
alGroup G] (S : Subgroup G),   IsDiscrete ↑S → ∃ U ∈ nhds 1, U⁻¹ = U ∧ ∀ g ∈ S, 
((fun x => g * x) '' U ∩ U).Nonempty → g = 1
参数：S : Subgroup G；(fun x => g * x) '' U ∩ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_inter_eq_singleton_of_mem_discrete`：nhds_inter_eq_singleton_of_mem_
discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) : exists U in 𝓝 x
, U inter s = {x}
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `exists_closed_nhds_one_inv_eq_mul_subset`：exists_closed_nhds_one_inv_eq_
mul_subset {U : Set G} (hU : U in 𝓝 1) : exists V in 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧
 V * V subseteq U
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    ∃ U ∈ 𝓝 (1 : G), U⁻¹ = U ∧ ∀ g ∈ S, ((g * ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨V, hV⟩ := nhds_inter_eq_singleton_of_mem_discrete hS S.one_mem
  obtain ⟨U, hU, -, hUinv, hUV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV.1
  refine ⟨U, hU, hUinv, fun g hgS ↦ ?_⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  refine hV.2.subset ⟨hUV ?_, hgS⟩
  rw [← hUinv] at hx
  exact ⟨_, hgx, _, hx, by simp⟩
/-
**IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty** 是 Mathlib 中的一
个定理，位于命名空间 `IsDiscrete`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologic
alGroup G] (S : Subgroup G),   IsDiscrete ↑S → ∃ U ∈ nhds 1, U⁻¹ = U ∧ ∀ g ∈ S, 
((fun x => x * g) '' U ∩ U).Nonempty → g = 1
参数：S : Subgroup G；(fun x => x * g) '' U ∩ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty`：∀ {G : Ty
pe w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S :
 Subgroup G),   IsDiscrete ↑S → ∃ U ∈ nhds 1, U⁻¹ =…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_eq_one`：inv_eq_one : a⁻¹ = 1 ↔ a = 1
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_image_mulLeft_inv_inter_iff`：∀ {α : Type u_2} [inst : Divis
ionMonoid α] {s t : Set α} {a : α},   ((fun x => a⁻¹ * x) '' s ∩ t).Nonempty ↔ (
(fun x => x * a) '' s⁻¹ ∩ t⁻¹)…
-/
@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    ∃ U ∈ 𝓝 (1 : G), U⁻¹ = U ∧ ∀ g ∈ S, ((· * g) '' U ∩ U).Nonempty → g = 1 := by
  have ⟨U, hU, hUinv, h⟩ := hS.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  refine ⟨U, hU, hUinv, fun g hgS hgU ↦ inv_eq_one.mp (h _ (S.inv_mem hgS) ?_)⟩
  rwa [Set.nonempty_image_mulLeft_inv_inter_iff, hUinv]

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- If a point in a topological group has a compact neighborhood, then the group is
locally compact. -/
@[to_additive]
/-
**IsCompact.locallyCompactSpace_of_mem_nhds_of_group** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsCompact.locallyCompactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCom
pact K) {x : G} (h : K in 𝓝 x) : LocallyCompactSpace G
参数：hK : IsCompact K；h : K in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.smul`：IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [Co
ntinuousConstSMul α β] (a : α) {s : Set β} (hs : IsCompact s) : IsCompact (a • s
)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G

--- 原说明 ---
If a point in a topological group has a compact neighborhood, then the group is
locally compact.
-/
theorem IsCompact.locallyCompactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G}
    (h : K ∈ 𝓝 x) : LocallyCompactSpace G := by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y ↦ ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

/-- If a function defined on a topological group has a support contained in a
compact set, then either the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has a support contained in a compact
      set, then either the function is trivial or the group is locally compact. -/]
/-
**eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group [Topol
ogicalSpace α] [Zero α] [T1Space α] {f : G -> α} {k : Set G} (hk : IsCompact k) 
(hf : support f subseteq k) (h'f : Continuous f) : f = 0 ∨ LocallyCompactSpace G
参数：hk : IsCompact k；hf : support f subseteq k；h'f : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Continuous.isOpen_support`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [T1Space X] [inst_2 : Zero X] [inst_3 : TopologicalSpace Y]   {f 
: Y → X}, Conti…
· 使用定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_group`：IsCompact.locallyCom
pactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G} (h : K in 
𝓝 x) : LocallyCompactSpace G
-/
theorem eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} {k : Set G} (hk : IsCompact k) (hf : support f ⊆ k) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push Not at h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := h
  have : k ∈ 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

/-- If a function defined on a topological group has compact support, then either
the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has compact support,
      then either the function is trivial or the group is locally compact. -/]
/-
**HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group [TopologicalSpac
e α] [Zero α] [T1Space α] {f : G -> α} (hf : HasCompactSupport f) (h'f : Continu
ous f) : f = 0 ∨ LocallyCompactSpace G
参数：hf : HasCompactSupport f；h'f : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group`：eq_
zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group [TopologicalSpa
ce α] [Zero α] [T1Space α] {f : G -> α} {k : Set G} (hk :…
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
-/
theorem HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G :=
  eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

end

end FilterMul

