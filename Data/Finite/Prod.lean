/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.ULift
public import Mathlib.Data.Set.NAry

/-!
# Finiteness of products
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

variable {α β : Type*}

namespace Finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] [Finite β] : Finite (α × β)
  body: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

中文:
实例 [有限
  签名: α] [有限 β] : 有限 (α × β)
  定义体: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

Depends on / 依赖: Fintype, Fintype.ofFinite, infer_instance, ofFinite
-/
instance [Finite α] [Finite β] : Finite (α × β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

instance {α β : Sort*} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm

/--
theorem `prod_left` / 定理 `prod_left`

English:
theorem prod_left
  given: (β) [Finite (α × β)] [Nonempty β]
  statement: Finite α
  proof: of_surjective (Prod.fst : α × β -> α) Prod.fst_surjective

中文:
定理 prod_left
  条件: (β) [有限 (α × β)] [非空 β]
  结论: 有限 α
  证明: of_surjective (Prod.fst : α × β -> α) Prod.fst_surjective

Depends on / 依赖: Prod.fst, Prod.fst_surjective, fst_surjective, of_surjective
-/
theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β -> α) Prod.fst_surjective

/--
theorem `prod_right` / 定理 `prod_right`

English:
theorem prod_right
  given: (α) [Finite (α × β)] [Nonempty α]
  statement: Finite β
  proof: of_surjective (Prod.snd : α × β -> β) Prod.snd_surjective

中文:
定理 prod_right
  条件: (α) [有限 (α × β)] [非空 α]
  结论: 有限 β
  证明: of_surjective (Prod.snd : α × β -> β) Prod.snd_surjective

Depends on / 依赖: Prod.snd, Prod.snd_surjective, of_surjective, snd_surjective
-/
theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β -> β) Prod.snd_surjective

end Finite

/--
lemma `Prod.finite_iff` / 引理 `Prod.finite_iff`

English:
lemma Prod.finite_iff
  given: [Nonempty α] [Nonempty β]
  statement: Finite (α × β) ↔ Finite α ∧ Finite β where
  proof: ⟨.prod_left β, .prod_right α⟩
  mpr | ⟨_, _⟩ => inferInstance

中文:
引理 积类型.finite_iff
  条件: [非空 α] [非空 β]
  结论: 有限 (α × β) ↔ 有限 α ∧ 有限 β where
  证明: ⟨.prod_left β, .prod_right α⟩
  mpr | ⟨_, _⟩ => inferInstance

Depends on / 依赖: prod_left, prod_right
-/
lemma Prod.finite_iff [Nonempty α] [Nonempty β] : Finite (α × β) ↔ Finite α ∧ Finite β where
  mp _ := ⟨.prod_left β, .prod_right α⟩
  mpr | ⟨_, _⟩ => inferInstance

/--
Instance `Pi.finite` / 实例 `Pi.finite`

English:
instance Pi.finite
  signature: {α : Sort*} {β : α -> Sort*} [Finite α] [forall a, Finite (β a)]
  body: by
  classical
  have := Fintype.ofFinite (PLift α)
  have := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (forall a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)

中文:
实例 依赖函数类型.finite
  签名: {α : 类型层*} {β : α -> 类型层*} [有限 α] [对任意 a, 有限 (β a)]
  定义体: by
  classical
  have := Fintype.ofFinite (PLift α)
  have := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (forall a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)

Depends on / 依赖: Equiv.piCongr, Equiv.plift, Finite, Finite.of_equiv, Fintype, Fintype.ofFinite, classical, ofFinite, of_equiv, piCongr
-/
instance Pi.finite {α : Sort*} {β : α -> Sort*} [Finite α] [forall a, Finite (β a)] :
    Finite (forall a, β a) := by
  classical
  have := Fintype.ofFinite (PLift α)
  have := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (forall a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)

/--
Instance `Function.Embedding.finite` / 实例 `Function.Embedding.finite`

English:
instance Function.Embedding.finite
  signature: {α β : Sort*} [Finite β]
  body: by
  rcases isEmpty_or_nonempty (α ↪ β) with _ | h
  · infer_instance
  · refine h.elim fun f => ?_
    have : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective

中文:
实例 函数.嵌入.finite
  签名: {α β : 类型层*} [有限 β]
  定义体: by
  rcases isEmpty_or_nonempty (α ↪ β) with _ | h
  · infer_instance
  · refine h.elim fun f => ?_
    have : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finite, Finite.of_injective, coe_injective, f.injective, h.elim, infer_instance, injective, isEmpty_or_nonempty, of_injective
-/
instance Function.Embedding.finite {α β : Sort*} [Finite β] : Finite (α ↪ β) := by
  rcases isEmpty_or_nonempty (α ↪ β) with _ | h
  · infer_instance
  · refine h.elim fun f => ?_
    have : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ DFunLike.coe_injective

/--
Instance `Equiv.finite_right` / 实例 `Equiv.finite_right`

English:
instance Equiv.finite_right
  signature: {α β : Sort*} [Finite β]
  body: Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext by
    convert! DFunLike.congr_fun h using 0

中文:
实例 等价.finite_right
  签名: {α β : 类型层*} [有限 β]
  定义体: Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext by
    convert! DFunLike.congr_fun h using 0

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Equiv.ext, Equiv.toEmbedding, Finite, Finite.of_injective, congr_fun, convert, of_injective, toEmbedding
-/
instance Equiv.finite_right {α β : Sort*} [Finite β] : Finite (α ≃ β) :=
Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext by
    convert! DFunLike.congr_fun h using 0

/--
Instance `Equiv.finite_left` / 实例 `Equiv.finite_left`

English:
instance Equiv.finite_left
  signature: {α β : Sort*} [Finite α]
  body: Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩

@[to_additive]

中文:
实例 等价.finite_left
  签名: {α β : 类型层*} [有限 α]
  定义体: Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩

@[to_additive]

Depends on / 依赖: Equiv.symm, Equiv.symm_symm, Finite, Finite.of_equiv, of_equiv, symm_symm
-/
instance Equiv.finite_left {α β : Sort*} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩

@[to_additive]
/--
Instance `MulEquiv.finite_left` / 实例 `MulEquiv.finite_left`

English:
instance MulEquiv.finite_left
  signature: {α β : Type*} [Mul α] [Mul β] [Finite α]
  body: Finite.of_injective toEquiv toEquiv_injective

@[to_additive]

中文:
实例 乘法等价.finite_left
  签名: {α β : 类型} [乘法 α] [乘法 β] [有限 α]
  定义体: Finite.of_injective toEquiv toEquiv_injective

@[to_additive]

Depends on / 依赖: Finite, Finite.of_injective, of_injective, toEquiv, toEquiv_injective
-/
instance MulEquiv.finite_left {α β : Type*} [Mul α] [Mul β] [Finite α] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

@[to_additive]
/--
Instance `MulEquiv.finite_right` / 实例 `MulEquiv.finite_right`

English:
instance MulEquiv.finite_right
  signature: {α β : Type*} [Mul α] [Mul β] [Finite β]
  body: Finite.of_injective toEquiv toEquiv_injective

中文:
实例 乘法等价.finite_right
  签名: {α β : 类型} [乘法 α] [乘法 β] [有限 β]
  定义体: Finite.of_injective toEquiv toEquiv_injective

Depends on / 依赖: Finite, Finite.of_injective, of_injective, toEquiv, toEquiv_injective
-/
instance MulEquiv.finite_right {α β : Type*} [Mul α] [Mul β] [Finite β] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

open Set Function

variable {γ : Type*}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/--
Instance `fintypeProd` / 实例 `fintypeProd`

English:
instance fintypeProd
  signature: (s : Set α) (t : Set β) [Fintype s] [Fintype t]
  body: Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) by simp

中文:
实例 fintypeProd
  签名: (s : 集合 α) (t : 集合 β) [有限类型 s] [有限类型 t]
  定义体: Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, s.toFinset, t.toFinset, toFinset
-/
instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) by simp

/--
Instance `fintypeOffDiag` / 实例 `fintypeOffDiag`

English:
instance fintypeOffDiag
  signature: (s : Set α) [Fintype s]
  body: Fintype.ofFinset s.toFinset.offDiag by simp

中文:
实例 fintypeOffDiag
  签名: (s : 集合 α) [有限类型 s]
  定义体: Fintype.ofFinset s.toFinset.offDiag by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, ofFinset, offDiag, s.toFinset.offDiag, toFinset
-/
instance fintypeOffDiag (s : Set α) [Fintype s] : Fintype s.offDiag :=
Fintype.ofFinset s.toFinset.offDiag by simp

/--
Instance `fintypeImage2` / 实例 `fintypeImage2`

English:
instance fintypeImage2
  signature: [DecidableEq γ] (f : α -> β -> γ) (s : Set α) (t : Set β) [hs : Fintype s]
  body: by
  rw [← image_prod]
  apply Set.fintypeImage

中文:
实例 fintypeImage2
  签名: [DecidableEq γ] (f : α -> β -> γ) (s : 集合 α) (t : 集合 β) [hs : 有限类型 s]
  定义体: by
  rw [← image_prod]
  apply Set.fintypeImage

Depends on / 依赖: Set.fintypeImage, fintypeImage, image_prod
-/
instance fintypeImage2 [DecidableEq γ] (f : α -> β -> γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/--
Instance `finite_prod` / 实例 `finite_prod`

English:
instance finite_prod
  signature: (s : Set α) (t : Set β) [Finite s] [Finite t]
  body: Finite.of_equiv _ (Equiv.Set.prod s t).symm

中文:
实例 finite_prod
  签名: (s : 集合 α) (t : 集合 β) [有限 s] [有限 t]
  定义体: Finite.of_equiv _ (Equiv.Set.prod s t).symm

Depends on / 依赖: Equiv.Set.prod, Finite, Finite.of_equiv, of_equiv
-/
instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm

/--
Instance `finite_image2` / 实例 `finite_image2`

English:
instance finite_image2
  signature: (f : α -> β -> γ) (s : Set α) (t : Set β) [Finite s] [Finite t]
  body: by
  rw [← image_prod]
  infer_instance

中文:
实例 finite_image2
  签名: (f : α -> β -> γ) (s : 集合 α) (t : 集合 β) [有限 s] [有限 t]
  定义体: by
  rw [← image_prod]
  infer_instance

Depends on / 依赖: image_prod, infer_instance
-/
instance finite_image2 (f : α -> β -> γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Prod

variable {s : Set α} {t : Set β}

/--
theorem `Finite.prod` / 定理 `Finite.prod`

English:
theorem Finite.prod
  given: (hs : s.Finite) (ht : t.Finite)
  statement: (s ×ˢ t : Set (α × β)).Finite
  proof: by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

中文:
定理 有限.乘积
  条件: (hs : s.有限) (ht : t.有限)
  结论: (s ×ˢ t : 集合 (α × β)).有限
  证明: by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite
-/
protected theorem Finite.prod (hs : s.Finite) (ht : t.Finite) : (s ×ˢ t : Set (α × β)).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

/--
theorem `Finite.of_prod_left` / 定理 `Finite.of_prod_left`

English:
theorem Finite.of_prod_left
  given: (h : (s ×ˢ t : Set (α × β)).Finite)
  statement: t.Nonempty -> s.Finite
  proof: fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

中文:
定理 有限.of_prod_left
  条件: (h : (s ×ˢ t : 集合 (α × β)).有限)
  结论: t.非空 -> s.有限
  证明: fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

Depends on / 依赖: Prod.fst, h.image, subset
-/
theorem Finite.of_prod_left (h : (s ×ˢ t : Set (α × β)).Finite) : t.Nonempty -> s.Finite :=
  fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/--
theorem `Finite.of_prod_right` / 定理 `Finite.of_prod_right`

English:
theorem Finite.of_prod_right
  given: (h : (s ×ˢ t : Set (α × β)).Finite)
  statement: s.Nonempty -> t.Finite
  proof: fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

中文:
定理 有限.of_prod_right
  条件: (h : (s ×ˢ t : 集合 (α × β)).有限)
  结论: s.非空 -> t.有限
  证明: fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

Depends on / 依赖: Prod.snd, h.image, subset
-/
theorem Finite.of_prod_right (h : (s ×ˢ t : Set (α × β)).Finite) : s.Nonempty -> t.Finite :=
  fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/--
theorem `Infinite.prod_left` / 定理 `Infinite.prod_left`

English:
theorem Infinite.prod_left
  given: (hs : s.Infinite) (ht : t.Nonempty)
  statement: (s ×ˢ t).Infinite
  proof: fun h => hs h.of_prod_left ht

中文:
定理 无限.prod_left
  条件: (hs : s.无限) (ht : t.非空)
  结论: (s ×ˢ t).无限
  证明: fun h => hs h.of_prod_left ht
-/
protected theorem Infinite.prod_left (hs : s.Infinite) (ht : t.Nonempty) : (s ×ˢ t).Infinite :=
fun h => hs h.of_prod_left ht

/--
theorem `Infinite.prod_right` / 定理 `Infinite.prod_right`

English:
theorem Infinite.prod_right
  given: (ht : t.Infinite) (hs : s.Nonempty)
  statement: (s ×ˢ t).Infinite
  proof: fun h => ht h.of_prod_right hs

中文:
定理 无限.prod_right
  条件: (ht : t.无限) (hs : s.非空)
  结论: (s ×ˢ t).无限
  证明: fun h => ht h.of_prod_right hs
-/
protected theorem Infinite.prod_right (ht : t.Infinite) (hs : s.Nonempty) : (s ×ˢ t).Infinite :=
fun h => ht h.of_prod_right hs

/--
theorem `infinite_prod` / 定理 `infinite_prod`

English:
theorem infinite_prod
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2

中文:
定理 infinite_prod
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2
-/
protected theorem infinite_prod :
    (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2

/--
theorem `finite_prod` / 定理 `finite_prod`

English:
theorem finite_prod
  statement: (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅)
  proof: by
  contrapose! +distrib; exact Set.infinite_prod

中文:
定理 finite_prod
  结论: (s ×ˢ t).有限 ↔ (s.有限 ∨ t = ∅) ∧ (t.有限 ∨ s = ∅)
  证明: by
  contrapose! +distrib; exact Set.infinite_prod

Depends on / 依赖: Set.infinite_prod, contrapose, distrib, infinite_prod
-/
theorem finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅) := by
  contrapose! +distrib; exact Set.infinite_prod

/--
theorem `Finite.offDiag` / 定理 `Finite.offDiag`

English:
theorem Finite.offDiag
  given: {s : Set α} (hs : s.Finite)
  statement: s.offDiag.Finite
  proof: (hs.prod hs).subset s.offDiag_subset_prod

中文:
定理 有限.offDiag
  条件: {s : 集合 α} (hs : s.有限)
  结论: s.offDiag.有限
  证明: (hs.prod hs).subset s.offDiag_subset_prod
-/
protected theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite :=
  (hs.prod hs).subset s.offDiag_subset_prod

/--
theorem `Finite.image2` / 定理 `Finite.image2`

English:
theorem Finite.image2
  given: (f : α -> β -> γ) (hs : s.Finite) (ht : t.Finite)
  proof: by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

中文:
定理 有限.image2
  条件: (f : α -> β -> γ) (hs : s.有限) (ht : t.有限)
  证明: by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite
-/
protected theorem Finite.image2 (f : α -> β -> γ) (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

end Prod

end SetFiniteConstructors


/--
theorem `Finite.toFinset_prod` / 定理 `Finite.toFinset_prod`

English:
theorem Finite.toFinset_prod
  given: {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite)
  proof: Finset.ext by simp

中文:
定理 有限.toFinset_prod
  条件: {s : 集合 α} {t : 集合 β} (hs : s.有限) (ht : t.有限)
  证明: Finset.ext by simp

Depends on / 依赖: Finset, Finset.ext
-/
theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.prod ht).toFinset :=
Finset.ext by simp

/--
theorem `Finite.toFinset_offDiag` / 定理 `Finite.toFinset_offDiag`

English:
theorem Finite.toFinset_offDiag
  given: {s : Set α} (hs : s.Finite)
  proof: Finset.ext by simp

中文:
定理 有限.toFinset_offDiag
  条件: {s : 集合 α} (hs : s.有限)
  证明: Finset.ext by simp

Depends on / 依赖: Finset, Finset.ext
-/
theorem Finite.toFinset_offDiag {s : Set α} (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
Finset.ext by simp

/--
theorem `finite_image_fst_and_snd_iff` / 定理 `finite_image_fst_and_snd_iff`

English:
theorem finite_image_fst_and_snd_iff
  given: {s : Set (α × β)}
  proof: ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

中文:
定理 finite_image_fst_and_snd_iff
  条件: {s : 集合 (α × β)}
  证明: ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

Depends on / 依赖: h.image, mem_image_of_mem, subset
-/
theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

/-! ### Infinite sets -/

variable {s t : Set α}

section Image2

variable {f : α -> β -> γ} {s : Set α} {t : Set β} {a : α} {b : β}

/--
theorem `Infinite.image2_left` / 定理 `Infinite.image2_left`

English:
theorem Infinite.image2_left
  statement: (hs : s.Infinite) (hb : b in t)
  proof: (hs.image hf).mono image_subset_image2_left hb

中文:
定理 无限.image2_left
  结论: (hs : s.无限) (hb : b in t)
  证明: (hs.image hf).mono image_subset_image2_left hb
-/
protected theorem Infinite.image2_left (hs : s.Infinite) (hb : b in t)
    (hf : InjOn (fun a => f a b) s) : (image2 f s t).Infinite :=
(hs.image hf).mono image_subset_image2_left hb

/--
theorem `Infinite.image2_right` / 定理 `Infinite.image2_right`

English:
theorem Infinite.image2_right
  given: (ht : t.Infinite) (ha : a in s) (hf : InjOn (f a) t)
  proof: (ht.image hf).mono image_subset_image2_right ha

中文:
定理 无限.image2_right
  条件: (ht : t.无限) (ha : a in s) (hf : 单射限制 (f a) t)
  证明: (ht.image hf).mono image_subset_image2_right ha
-/
protected theorem Infinite.image2_right (ht : t.Infinite) (ha : a in s) (hf : InjOn (f a) t) :
    (image2 f s t).Infinite :=
(ht.image hf).mono image_subset_image2_right ha

/--
theorem `infinite_image2` / 定理 `infinite_image2`

English:
theorem infinite_image2
  given: (hfs : forall b in t, InjOn (fun a => f a b) s) (hft : forall a in s, InjOn (f a) t)
  proof: by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)

中文:
定理 infinite_image2
  条件: (hfs : 对任意 b in t, 单射限制 (fun a => f a b) s) (hft : 对任意 a in s, 单射限制 (f a) t)
  证明: by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)

Depends on / 依赖: Set.infinite_prod, h.of_image, hs.image2_left, ht.image2_right, image2_left, image2_right, image_uncurry_prod, infinite_prod, of_image
-/
theorem infinite_image2 (hfs : forall b in t, InjOn (fun a => f a b) s) (hft : forall a in s, InjOn (f a) t) :
    (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)

/--
lemma `finite_image2` / 引理 `finite_image2`

English:
lemma finite_image2
  given: (hfs : forall b in t, InjOn (f · b) s) (hft : forall a in s, InjOn (f a) t)
  proof: by
  contrapose! +distrib
  rw [Set.infinite_image2 hfs hft]
  grind only [Set.Infinite.nonempty]

中文:
引理 finite_image2
  条件: (hfs : 对任意 b in t, 单射限制 (f · b) s) (hft : 对任意 a in s, 单射限制 (f a) t)
  证明: by
  contrapose! +distrib
  rw [Set.infinite_image2 hfs hft]
  grind only [Set.Infinite.nonempty]

Depends on / 依赖: Infinite, Set.Infinite.nonempty, Set.infinite_image2, contrapose, distrib, infinite_image2, nonempty
-/
lemma finite_image2 (hfs : forall b in t, InjOn (f · b) s) (hft : forall a in s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  contrapose! +distrib
  rw [Set.infinite_image2 hfs hft]
  grind only [Set.Infinite.nonempty]

end Image2

end Set
