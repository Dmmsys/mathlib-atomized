/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Envelopes of Semicontinuous functions on Hereditarily Lindelöf spaces

In this file, we show that, if `X` is a hereditarily Lindelöf space and `𝓕` is any family
of upper semicontinuous functions on `X`, then there is a countable subfamily `𝓕'`
with the same infimum / lower envelope. Most importantly, this applies whenever `X` has a
`SecondCountableTopology`.

The codomain `E` of the functions is assumed to be linearly ordered, and to admit a countable
order-dense subset. In particular we do not assume that arbitrary infima exist in `E`, so our
result is of the form "if `IsGLB 𝓕 s`, then there is a countable `𝓕' ⊆ 𝓕` such that `IsGLB 𝓕' s`".

Of course we also provide the dual statements for lower semicontinuous functions.

## Implementation Notes

There is currently no way to state the hypothesis "`E` admits a countable order-dense subset"
which would be inferrable by typeclass inference. Instead, we assume
`[TopologicalSpace E] [OrderClosedTopology E] [DenselyOrdered E] [SeparableSpace E]`, and
use `Dense.exists_between` to show that a chosen countable dense subset is order-dense.

This is not completely satisfying because the hypotheses on `E` should be purely order-theoretic,
but in practice `E` is either `Real`, `NNReal`, `ENNReal` or `EReal`, all of which are already
equipped with the order topology.

## References

* [N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I][bourbaki1974] (this appendix does
  not seem to exist in the English translation)
-/

public section

open Set TopologicalSpace

variable {X E : Type*} [TopologicalSpace X] [HereditarilyLindelofSpace X] [LinearOrder E]
  [TopologicalSpace E] [OrderClosedTopology E] [DenselyOrdered E] [SeparableSpace E]
-- Note: we shouldn't really need a topology on `E`: we just want the conclusion of
-- `SeparableSpace` + `Dense.exists_between`.

/-- If a function `s : X → E` can be written as the infimum of a family `𝓕` of upper semicontinuous
functions then, assuming that `X` is hereditarily Lindelöf (for example, second countable),
`s` can in fact be written as the infimum of some *countable* subfamily `𝓕'`.

This is implication a) ⇒ b) in
[N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I, Proposition 3][bourbaki1974]

See the module docstring for a discussion of the assumptions on `E`. -/
/-
**exists_countable_upperSemicontinuous_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_countable_upperSemicontinuous_isGLB {s : X -> E} {𝓕 : Set (X -> E)}
 (h𝓕_cont : forall f in 𝓕, UpperSemicontinuous f) (h𝓕 : IsGLB 𝓕 s) : exists 𝓕' s
ubseteq 𝓕, 𝓕'.Countable ∧ IsGLB 𝓕' s
参数：X -> E；h𝓕_cont : forall f in 𝓕, UpperSemicontinuous f；h𝓕 : IsGLB 𝓕 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `UpperSemicontinuous.isOpen_preimage`：UpperSemicontinuous.isOpen_preimage
 (hf : UpperSemicontinuous f) (y : β) : IsOpen (f ⁻¹' Iio y)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isGLB_lt_iff`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α} {a b :
 α}, IsGLB s a → (a < b ↔ ∃ c ∈ s, c < b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `eq_open_union_countable`：eq_open_union_countable [HereditarilyLindelofSp
ace X] {ι : Type*} (U : ι -> Set X) (h : forall i, IsOpen (U i)) : exists t : Se
t ι, t.Counta…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Countable.biUnion`：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a :
 α) → a ∈ s → Set β},   s.Countable → (∀ (a : α) (ha : a ∈ s), (t a ha).Countabl
e) → (⋃ a, …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lowerBounds_mono_set`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄
, s ⊆ t → lowerBounds t ⊆ lowerBounds s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Dense.exists_between`：Dense.exists_between [DenselyOrdered α] {s : Set α
} (hs : Dense s) {x y : α} (h : x < y) : exists z in s, z in Ioo x y
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `s : X → E` can be written as the infimum of a family `𝓕` of upper
 semicontinuous
functions then, assuming that `X` is hereditarily Lindelöf (for example, second 
countable),
`s` can in fact be written as the infimum of some *countable* subfamily `𝓕'`.

This is implication a) ⇒ b) in
[N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I, Proposition 3][bou
rbaki1974]

See the module docstring for a discussion of the assumptions on `E`.
-/
theorem exists_countable_upperSemicontinuous_isGLB {s : X → E} {𝓕 : Set (X → E)}
    (h𝓕_cont : ∀ f ∈ 𝓕, UpperSemicontinuous f) (h𝓕 : IsGLB 𝓕 s) :
    ∃ 𝓕' ⊆ 𝓕, 𝓕'.Countable ∧ IsGLB 𝓕' s := by
  simp_rw [isGLB_pi] at *
  rcases exists_countable_dense E with ⟨D, D_count, D_dense⟩
  let U (f : X → E) (d : E) : Set X := {x | f x < d}
  have U_open {f} (hf : f ∈ 𝓕) (d : E) : IsOpen (U f d) := h𝓕_cont f hf |>.isOpen_preimage d
  have (d : E) : {x | s x < d} = ⋃ f : 𝓕, U f d := by
    ext x
    simp [U, isGLB_lt_iff (h𝓕 x)]
  have (d : E) : ∃ A ⊆ 𝓕, A.Countable ∧ {x | s x < d} = ⋃ f ∈ A, U f d := by
    simp_rw [this d]
    rcases eq_open_union_countable (fun f : 𝓕 ↦ U f d) (fun f ↦ U_open f.2 d) with ⟨t, t_count, ht⟩
    use (↑) '' t, image_val_subset, t_count.image _
    rw [← ht, biUnion_image]
  choose A A_sub A_count hA using this
  set 𝓕' := ⋃ d ∈ D, A d
  have 𝓕'_sub : 𝓕' ⊆ 𝓕 := iUnion₂_subset fun d _ ↦ A_sub d
  use 𝓕', 𝓕'_sub, D_count.biUnion fun d _ ↦ A_count d
  refine fun x ↦ ⟨lowerBounds_mono_set (image_mono 𝓕'_sub) (h𝓕 x).1, fun e he ↦ ?_⟩
  by_contra! H
  rcases D_dense.exists_between H with ⟨d, d_mem, hd⟩
  obtain ⟨f, f_mem, hf⟩ : ∃ f ∈ A d, f x < d := by
    have : x ∈ {y | s y < d} := hd.1
    simpa only [hA d, mem_iUnion₂, exists_prop, U, mem_ofPred_eq] using this
  suffices e < e by simpa
  exact (he (mem_image_of_mem _ (mem_iUnion₂_of_mem d_mem f_mem))).trans_lt hf |>.trans hd.2

/-- If a function `s : X → E` can be written as the supremum of a family `𝓕` of lower semicontinuous
functions then, assuming that `X` is hereditarily Lindelöf (for example, second countable),
`s` can in fact be written as the supremum of some *countable* subfamily `𝓕'`.

This is implication a) ⇒ b) in
[N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I, Proposition 3][bourbaki1974]

See the module docstring for a discussion of the assumptions on `E`. -/
/-
**exists_countable_lowerSemicontinuous_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_countable_lowerSemicontinuous_isLUB {s : X -> E} {𝓕 : Set (X -> E)}
 (h𝓕_cont : forall f in 𝓕, LowerSemicontinuous f) (h𝓕 : IsLUB 𝓕 s) : exists 𝓕' s
ubseteq 𝓕, 𝓕'.Countable ∧ IsLUB 𝓕' s
参数：X -> E；h𝓕_cont : forall f in 𝓕, LowerSemicontinuous f；h𝓕 : IsLUB 𝓕 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_countable_upperSemicontinuous_isGLB`：exists_countable_upperSemico
ntinuous_isGLB {s : X -> E} {𝓕 : Set (X -> E)} (h𝓕_cont : forall f in 𝓕, UpperSe
micontinuous f) (h𝓕 : IsGLB 𝓕 s)…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `instSeparableSpaceOrderDual`：∀ {α : Type u} [inst : TopologicalSpace α] 
[h : TopologicalSpace.SeparableSpace α], TopologicalSpace.SeparableSpace αᵒᵈ

--- 原说明 ---
If a function `s : X → E` can be written as the supremum of a family `𝓕` of lowe
r semicontinuous
functions then, assuming that `X` is hereditarily Lindelöf (for example, second 
countable),
`s` can in fact be written as the supremum of some *countable* subfamily `𝓕'`.

This is implication a) ⇒ b) in
[N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I, Proposition 3][bou
rbaki1974]

See the module docstring for a discussion of the assumptions on `E`.
-/
theorem exists_countable_lowerSemicontinuous_isLUB {s : X → E} {𝓕 : Set (X → E)}
    (h𝓕_cont : ∀ f ∈ 𝓕, LowerSemicontinuous f) (h𝓕 : IsLUB 𝓕 s) :
    ∃ 𝓕' ⊆ 𝓕, 𝓕'.Countable ∧ IsLUB 𝓕' s :=
  exists_countable_upperSemicontinuous_isGLB (E := Eᵒᵈ) h𝓕_cont h𝓕

end

