/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.
* `ennrealVariation_eq_self`: if `μ : VectorMeasure X ℝ≥0∞` then `μ.ennrealVariation = μ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset Set
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

/-- The sum of a vector measure `μ` on a `Finpartition` of `Subtype MeasurableSet` equals `μ s`. -/
/-
**MeasureTheory.VectorMeasure.sum_finpartition** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：sum_finpartition [AddCommMonoid V] [TopologicalSpace V] [T2Space V] (μ : V
ectorMeasure X V) {s : Set X} {hs : MeasurableSet s} (P : Finpartition (⟨s, hs⟩ 
: Subtype MeasurableSet)) : ∑ p in P.parts, μ p.val = μ s
参数：μ : VectorMeasure X V；P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.of_biUnion_finset`：of_biUnion_finset {ι : Ty
pe*} {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall
 b in s, MeasurableSet (f b)) : v (…
· 使用定理 `Finpartition.pairwiseDisjoint_apply`：pairwiseDisjoint_apply [Semilattice
Inf β] [OrderBot β] (hf : forall x y, f (x ⊓ y) = f x ⊓ f y) (hbot : f ⊥ = ⊥) : 
(P.parts : Set α).Pairwis…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Finpartition.sup_parts_apply`：sup_parts_apply [SemilatticeSup β] [OrderB
ot β] (hf : forall x y, f (x ⊔ y) = f x ⊔ f y) (hbot : f ⊥ = ⊥) : P.parts.sup f 
= f a

--- 原说明 ---
The sum of a vector measure `μ` on a `Finpartition` of `Subtype MeasurableSet` e
quals `μ s`.
-/
lemma sum_finpartition [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
    (μ : VectorMeasure X V) {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p ∈ P.parts, μ p.val = μ s := by
  rw [← μ.of_biUnion_finset (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl) (fun p _ => p.prop),
      ← Finset.sup_set_eq_biUnion, P.sup_parts_apply (fun _ _ => rfl) rfl]

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]
  {μ ν : VectorMeasure X V} {s : Set X}

/-
**MeasureTheory.VectorMeasure.variation_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：variation_apply (μ : VectorMeasure X V) (s : Set X) : μ.variation s = preV
ariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s
参数：μ : VectorMeasure X V；s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
/-
**MeasureTheory.VectorMeasure.ennrealVariation_apply** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : Measurabl
eSet s) : μ.ennrealVariation s = μ.variation s
参数：μ : VectorMeasure X V；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable`：toENNReal
VectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i
) : μ.toENNRealVectorMeasure i = μ i
-/
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `sum_le_preVariationFun_of_subset`. -/
/-
**MeasureTheory.VectorMeasure.le_variation** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P
 : Finset (Set X)} (hP₁ : forall t in P, t subseteq s) (hP₂ : (P : Set (Set X)).
PairwiseDisjoint id) : ∑ p in P, ‖μ p‖ₑ <= μ.variation s
参数：μ : VectorMeasure X V；hs : MeasurableSet s；Set X；hP₁ : forall t in P, t subse
teq s；hP₂ : (P : Set (Set X)).PairwiseDisjoint id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finpartition.ofPairwiseDisjoint_parts`：∀ {α : Type u_1} [inst : DistribL
attice α] [inst_1 : OrderBot α] [inst_2 : DecidableEq α] (parts : Finset α)   (h
disjoint : (↑parts).Pairwis…
· 使用定理 `Finpartition.ofSubset.congr_simp`：∀ {α : Type u_1} [inst : Lattice α] [i
nst_1 : OrderBot α] {a b : α} (P P_1 : Finpartition a) (e_P : P = P_1)   {parts 
parts_1 : Finset α} (e…
· 使用定理 `Finpartition.ofSubset_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1
 : OrderBot α] {a b : α} (P : Finpartition a) {parts : Finset α}   (subset : par
ts ⊆ P.parts) (su…
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finpartition.sum_ofPairwiseDisjoint_eq_sum`：sum_ofPairwiseDisjoint_eq_su
m {parts : Finset α} (hdisjoint : (parts : Set α).PairwiseDisjoint id) {X : Type
*} [AddCommMonoid X] {f : α -> X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finpartition.sum_ofSubset_eq_sum`：sum_ofSubset_eq_sum {a b : α} (P : Fin
partition a) {parts : Finset α} (subset : parts subseteq P.parts) (sup_parts : p
arts.sup id = b) {X : …
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `Finpartition.parts_subset_extendOfLE`：parts_subset_extendOfLE (hab : a <
= b) : P.parts subseteq (P.extendOfLE hab).parts
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Measure version of `sum_le_preVariationFun_of_subset`.
-/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : ∀ t ∈ Q'.parts, t ⊆ s := by simp [Q', Q]; grind
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
      exact hs.diff <| .biUnion (Finset.countable_toSet _) (by simp)

/-- Measure version of `preVariation.exists_Finpartition_sum_gt`. -/
/-
**MeasureTheory.VectorMeasure.exists_lt_sum_of_lt_variation** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_lt_sum_of_lt_variation (μ : VectorMeasure X V) {s : Set X} (hs : Me
asurableSet s) {a : Real>=0∞} (ha : a < μ.variation s) : exists (P : Finset (Set
 X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧ 
(forall t in P, MeasurableSet t) ∧ a < ∑ p in P, ‖μ p‖ₑ
参数：μ : VectorMeasure X V；hs : MeasurableSet s；ha : a < μ.variation s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.preVariation.exists_Finpartition_sum_gt`：exists_Finpartiti
on_sum_gt {s : Set X} (hs : MeasurableSet s) {a : Real>=0∞} (ha : a < preVariati
onFun f s) : exists P : Finpartition (⟨s, h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用引理 `disjoint_subtype_iff`：disjoint_subtype_iff {pr : α -> Prop} (Pinf : fora
ll ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t)) (hbot : pr (⊥ : α)) {a b : Subtype pr}
 : letI : …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
Measure version of `preVariation.exists_Finpartition_sum_gt`.
-/
lemma exists_lt_sum_of_lt_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.variation s) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ a < ∑ p ∈ P, ‖μ p‖ₑ := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at ha ⊢
  obtain ⟨P, hP⟩ : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      a < ∑ p ∈ P.parts, (fun x ↦ ‖μ x‖ₑ) p :=
    preVariation.exists_Finpartition_sum_gt (‖μ ·‖ₑ) _ ha
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi  j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht ↦ hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/-- Measure version of `preVariation.exists_Finpartition_sum_ge'`. -/
/-
**MeasureTheory.VectorMeasure.exists_variation_le_add'** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_variation_le_add' (μ : VectorMeasure X V) {s : Set X} (hs : Measura
bleSet s) {ε : Real>=0∞} (hε : 0 < ε) (hμ : μ.variation s != ∞) : exists (P : Fi
nset (Set X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoi
nt id) ∧ (forall t in P, MeasurableSet t) ∧ μ.variation s <= ∑ p in P, ‖μ p‖ₑ + 
ε
参数：μ : VectorMeasure X V；hs : MeasurableSet s；hε : 0 < ε；hμ : μ.variation s != ∞
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用引理 `MeasureTheory.preVariation.exists_Finpartition_sum_ge'`：exists_Finpartit
ion_sum_ge' {s : Set X} (hs : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε) (h : 
preVariationFun f s != ∞) : exists P : Finpa…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用引理 `disjoint_subtype_iff`：disjoint_subtype_iff {pr : α -> Prop} (Pinf : fora
ll ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t)) (hbot : pr (⊥ : α)) {a b : Subtype pr}
 : letI : …
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …

--- 原说明 ---
Measure version of `preVariation.exists_Finpartition_sum_ge'`.
-/
lemma exists_variation_le_add' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hμ : μ.variation s ≠ ∞) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at hμ ⊢
  obtain ⟨P, hP⟩ : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      preVariationFun (fun x ↦ ‖μ x‖ₑ) s ≤ ∑ p ∈ P.parts, (fun x ↦ ‖μ x‖ₑ) ↑p + ε :=
    preVariation.exists_Finpartition_sum_ge' (‖μ ·‖ₑ) hs hε hμ
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi  j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht ↦ hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/-- Measure version of `preVariation.exists_Finpartition_sum_ge`. -/
/-
**MeasureTheory.VectorMeasure.exists_variation_le_add** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：exists_variation_le_add (μ : VectorMeasure X V) {s : Set X} (hs : Measurab
leSet s) {ε : Real>=0} (hε : 0 < ε) (hμ : μ.variation s != ∞) : exists (P : Fins
et (Set X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoint
 id) ∧ (forall t in P, MeasurableSet t) ∧ μ.variation s <= ∑ p in P, ‖μ p‖ₑ + ε
参数：μ : VectorMeasure X V；hs : MeasurableSet s；hε : 0 < ε；hμ : μ.variation s != ∞
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.exists_variation_le_add'`：exists_variation_l
e_add' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {ε : Real>=0∞}
 (hε : 0 < ε) (hμ : μ.variation s != ∞) : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
Measure version of `preVariation.exists_Finpartition_sum_ge`.
-/
lemma exists_variation_le_add (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : ℝ≥0} (hε : 0 < ε) (hμ : μ.variation s ≠ ∞) :
    ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (∀ t ∈ P, MeasurableSet t) ∧ μ.variation s ≤ ∑ p ∈ P, ‖μ p‖ₑ + ε :=
  exists_variation_le_add' μ hs (mod_cast hε) hμ
/-
**MeasureTheory.VectorMeasure.enorm_measure_le_variation** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <=
 variation μ E
参数：μ : VectorMeasure X V；E : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finpartition.indiscrete_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst
_1 : OrderBot α] {a : α} (ha : a ≠ ⊥), (Finpartition.indiscrete ha).parts = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.preVariation.sum_le`：sum_le {s : Set X} (hs : MeasurableSe
t s) (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p in P.parts, f p 
<= preVariationFun f s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
/-
**MeasureTheory.VectorMeasure.variation_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：variation_zero : (0 : VectorMeasure X V).variation = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.preVariation.congr_simp`：∀ {X : Type u_1} [inst : Measurab
leSpace X] (f f_1 : Set X → ENNReal) (e_f : f = f_1)   (hf : MeasureTheory.IsSig
maSubadditiveSetFun f) (hf'…
· 使用引理 `MeasureTheory.preVariation_zero`：preVariation_zero : preVariation (0 : S
et X -> Real>=0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0
-/
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, zero_apply, enorm_zero]
  exact preVariation_zero
/-
**MeasureTheory.VectorMeasure.absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation
参数：μ : VectorMeasure X V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.VectorMeasure.ennrealVariation_apply`：ennrealVariation_app
ly (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) : μ.ennrealVariati
on s = μ.variation s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
-/
lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable hsm
/-
**MeasureTheory.VectorMeasure.variation_apply_le_of_forall_enorm_le** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：variation_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet 
s) (h : forall E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ <= m E) : μ.variatio
n s <= m s
参数：hs : MeasurableSet s；h : forall E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ 
<= m E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
-/
lemma variation_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s)
    (h : ∀ E, MeasurableSet E → E ⊆ s → ‖μ E‖ₑ ≤ m E) :
    μ.variation s ≤ m s := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x ∈ i.parts, ‖μ x‖ₑ ≤ ∑ x ∈ i.parts, m x := Finset.sum_le_sum
        (fun s hs => h s s.property (i.le hs))
    _ = m (i.parts.sup Subtype.val) := by
      rw [sup_set_eq_biUnion]
      refine (MeasureTheory.measure_biUnion_finset ?_ fun b _ => b.property).symm
      intro a ha b hb hab
      simpa [disjoint_iff, Subtype.ext_iff] using i.disjoint ha hb hab
    _ ≤ m s := by
      rw [sup_set_eq_biUnion]
      exact measure_mono <| Set.iUnion₂_subset fun _ hp => Subtype.coe_le_coe.mpr (i.le hp)
/-
**MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：variation_le_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableS
et E -> ‖μ E‖ₑ <= m E) : μ.variation <= m
参数：h : forall E, MeasurableSet E -> ‖μ E‖ₑ <= m E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.le_intro`：le_intro (h : forall s, MeasurableSet s 
-> s.Nonempty -> μ₁ s <= μ₂ s) : μ₁ <= μ₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_apply_le_of_forall_enorm_le`：varia
tion_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s) (h : for
all E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ <= m E…
-/
lemma variation_le_of_forall_enorm_le {m : Measure X} (h : ∀ E, MeasurableSet E → ‖μ E‖ₑ ≤ m E) :
    μ.variation ≤ m :=
  Measure.le_intro fun _ hs _ => variation_apply_le_of_forall_enorm_le hs (fun E hE _ ↦ h E hE)
/-
**MeasureTheory.VectorMeasure.variation_add_le** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：variation_add_le [ContinuousAdd V] : variation (μ + ν) <= variation μ + va
riation ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
-/
lemma variation_add_le [ContinuousAdd V] : variation (μ + ν) ≤ variation μ + variation ν := by
  refine variation_le_of_forall_enorm_le fun E _ => ?_
  calc
    _ ≤ ‖μ E‖ₑ + ‖ν E‖ₑ := enorm_add_le _ _
    _ ≤ μ.variation E + ν.variation E := by
      gcongr <;> exact enorm_measure_le_variation _ E
/-
**MeasureTheory.VectorMeasure.variation_finsetSum_le** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：variation_finsetSum_le [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι -> Vect
orMeasure X V) : (∑ i in s, μ i).variation <= ∑ i in s, (μ i).variation
参数：s : Finset ι；μ : ι -> VectorMeasure X V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.VectorMeasure.variation_add_le`：variation_add_le [Continuo
usAdd V] : variation (μ + ν) <= variation μ + variation ν
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma variation_finsetSum_le [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι → VectorMeasure X V) :
    (∑ i ∈ s, μ i).variation ≤ ∑ i ∈ s, (μ i).variation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))
/-
**MeasureTheory.VectorMeasure.variation_apply_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：variation_apply_eq_zero (hs : MeasurableSet s) : μ.variation s = 0 ↔ foral
l t, t subseteq s -> MeasurableSet t -> μ t = 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `enorm_eq_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : EN
ormedAddMonoid E] {a : E}, ‖a‖ₑ = 0 ↔ a = 0
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.VectorMeasure.variation_apply_le_of_forall_enorm_le`：varia
tion_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s) (h : for
all E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ <= m E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
-/
lemma variation_apply_eq_zero (hs : MeasurableSet s) :
    μ.variation s = 0 ↔ ∀ t, t ⊆ s → MeasurableSet t → μ t = 0 := by
  refine ⟨fun h t hts ht ↦ ?_, fun h ↦ ?_⟩
  · rw [← enorm_eq_zero, ← le_zero_iff, ← h]
    apply (enorm_measure_le_variation _ _).trans (measure_mono hts)
  · suffices μ.variation s ≤ (0 : Measure X) s by simpa
    apply variation_apply_le_of_forall_enorm_le hs (fun t ht hts ↦ ?_)
    simp [h t hts ht]
/-
**MeasureTheory.VectorMeasure.variation_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：∀ {X : Type u_1} {V : Type u_2} {mX : MeasurableSpace X} [inst : Topologic
alSpace V] [inst_1 : ENormedAddCommMonoid V]   [inst_2 : T2Space V] {μ : Measure
Theory.VectorMeasure X V}, μ.variation = 0 ↔ μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `enorm_eq_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : EN
ormedAddMonoid E] {a : E}, ‖a‖ₑ = 0 ↔ a = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma variation_eq_zero :
    μ.variation = 0 ↔ μ = 0 where
  mp h := by
    ext s hs
    apply enorm_eq_zero.1
    apply le_antisymm ?_ (by simp)
    grw [enorm_measure_le_variation]
    simp [h]
  mpr h := by simp [h]
/-
**MeasureTheory.VectorMeasure.variation_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：variation_restrict (hs : MeasurableSet s) : (μ.restrict s).variation = μ.v
ariation.restrict s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.VectorMeasure.variation_apply_le_of_forall_enorm_le`：varia
tion_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s) (h : for
all E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ <= m E…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_eq_self`：restrict_eq_self {i : Set 
α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) (hij : j subseteq i
) : v.restrict i j = v j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma variation_restrict (hs : MeasurableSet s) :
    (μ.restrict s).variation = μ.variation.restrict s := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht ↦ ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variation (t ∩ s)
    _ ≤ (μ.restrict s).variation (t ∩ s) := by
      apply variation_apply_le_of_forall_enorm_le (ht.inter hs) (fun u u_meas hu ↦ ?_)
      have : μ u = μ.restrict s u :=
        (VectorMeasure.restrict_eq_self _ hs u_meas (hu.trans inter_subset_right)).symm
      rw [this]
      apply enorm_measure_le_variation
    _ ≤ (μ.restrict s).variation t := by
      gcongr
      exact Set.inter_subset_left
/-
**MeasureTheory.VectorMeasure.variation_restrict_le** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：variation_restrict_le : (μ.restrict s).variation <= μ.variation.restrict s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
-/
lemma variation_restrict_le : (μ.restrict s).variation ≤ μ.variation.restrict s := by
  by_cases hs : MeasurableSet s
  · simp [variation_restrict hs]
  · simp [restrict_not_measurable _ hs, Measure.zero_le]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.restrict s).variation :=
  isFiniteMeasure_of_le _ variation_restrict_le

variable {Y : Type*} [MeasurableSpace Y] {φ : X → Y}
/-
**MeasureTheory.VectorMeasure.variation_map_le** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：variation_map_le : (μ.map φ).variation <= μ.variation.map φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
-/
lemma variation_map_le : (μ.map φ).variation ≤ μ.variation.map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ, Measure.zero_le]
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  simp [VectorMeasure.map_apply _ hφ hs, Measure.map_apply hφ hs, enorm_measure_le_variation]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.map φ).variation :=
  isFiniteMeasure_of_le _ variation_map_le
/-
**MeasureTheory.VectorMeasure._root_.MeasurableEmbedding.variation_map** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.variation_map (hφ : MeasurableEmbedding φ) :
    (μ.map φ).variation = μ.variation.map φ := by
  apply le_antisymm variation_map_le ?_
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  simp only [hφ.measurable, hs, Measure.map_apply]
  have : (μ.map φ).variation s = (μ.map φ).variation (s ∩ range φ) := by
    nth_rw 1 [← inter_union_sdiff s (range φ)]
    have : (μ.map φ).variation (s \ range φ) = 0 := by
      apply (variation_apply_eq_zero (hs.diff hφ.measurableSet_range)).2 (fun t ht t_meas ↦ ?_)
      have : φ ⁻¹' t = ∅ := by grind
      simp [map_apply, t_meas, hφ.measurable, this]
    rw [measure_union (by grind) (hs.diff hφ.measurableSet_range), this, add_zero]
  rw [this, ← hφ.comap_preimage]
  apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
  simp only [hφ.comap_apply]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  rw [map_apply _ hφ.measurable (hφ.measurableSet_image.2 ht), preimage_image_eq _ hφ.injective]
/-
**MeasureTheory.VectorMeasure.variation_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：∀ {X : Type u_1} {V : Type u_2} {mX : MeasurableSpace X} [inst : Topologic
alSpace V] [inst_1 : ENormedAddCommMonoid V]   [inst_2 : T2Space V] {x : X} {v :
 V},   (MeasureTheory.VectorMeasure.dirac x v).variation = ‖v‖ₑ • MeasureTheory.
Measure.dirac x
参数：MeasureTheory.VectorMeasure.dirac x v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_mem`：∀ {β : Type u_2} {M : Ty
pe u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Measura
bleSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_notMem`：∀ {β : Type u_2} {M :
 Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Meas
urableSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
-/
@[simp] lemma variation_dirac {x : X} {v : V} :
    (VectorMeasure.dirac x v).variation = ‖v‖ₑ • Measure.dirac x := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    by_cases hx : x ∈ s <;> simp [hs, hx]
  · apply Measure.le_iff.2 (fun s hs ↦ ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    by_cases hx : x ∈ s <;> simp [hs, hx]

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ ν : VectorMeasure X V}

/-
**MeasureTheory.VectorMeasure.norm_measure_le_variation** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：norm_measure_le_variation {E : Set X} (hE : μ.variation E != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
-/
theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E ≠ ∞ := by finiteness) :
    ‖μ E‖ ≤ μ.variation.real E := by
  rw [measureReal_def, ← toReal_enorm, ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
/-
**MeasureTheory.VectorMeasure.variation_neg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：variation_neg : (-μ).variation = μ.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.preVariation.congr_simp`：∀ {X : Type u_1} [inst : Measurab
leSpace X] (f f_1 : Set X → ENNReal) (e_f : f = f_1)   (hf : MeasureTheory.IsSig
maSubadditiveSetFun f) (hf'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]
/-
**MeasureTheory.VectorMeasure.variation_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：variation_sub_le : (μ - ν).variation <= μ.variation + ν.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.VectorMeasure.variation_add_le`：variation_add_le [Continuo
usAdd V] : variation (μ + ν) <= variation μ + variation ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.VectorMeasure.variation_neg`：variation_neg : (-μ).variatio
n = μ.variation
-/
lemma variation_sub_le : (μ - ν).variation ≤ μ.variation + ν.variation := by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]
/-
**MeasureTheory.VectorMeasure.variation_smul_le** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma variation_smul_le {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation ≤ ‖c‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  simp only [smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [enorm_measure_le_variation, enorm_eq_nnnorm]
/-
**MeasureTheory.VectorMeasure.variation_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：variation_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} : (c 
• μ).variation = ‖c‖₊ • μ.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Variation.Basic.0.MeasureTh
eory.VectorMeasure.variation_smul_le`：∀ {X : Type u_1} {V : Type u_2} {mX : Meas
urableSpace X} [inst : NormedAddCommGroup V]   {μ : MeasureTheory.VectorMeasure 
X V} {𝕜 : Type u_3…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.VectorMeasure.variation.congr_simp`：∀ {X : Type u_1} {mX :
 MeasurableSpace X} {V : Type u_2} [inst : TopologicalSpace V] [inst_1 : ENormed
AddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_le_smul_left`：smul_le_smul_left [SMul M α] [Preorder α] [CovariantC
lass M α HSMul.hSMul LE.le] (m : M) {a b : α} (h : a <= b) : m • a <= m • b
· 使用定理 `MeasureTheory.Measure.instCovariantClassHSMulLeOfENNReal`：∀ {α : Type u_
1} {R : Type u_6} {m0 : MeasurableSpace α} [inst : SMul R ENNReal]   [inst_1 : I
sScalarTower R ENNReal ENNReal] [CovariantClas…
· 使用定理 `instCovariantClassHSMulLeOfIsOrderedSMul`：∀ {G : Type u_1} {P : Type u_2
} [inst : LE G] [inst_1 : LE P] [inst_2 : SMul G P] [IsOrderedSMul G P],   Covar
iantClass G P (fun x1 x2 => x1…
· 使用定理 `ENNReal.instIsOrderedSMulNNReal`：IsOrderedSMul NNReal ENNReal
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
（共 32 条，此处仅展示前 30 条）
-/
lemma variation_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation = ‖c‖₊ • μ.variation := by
  apply le_antisymm variation_smul_le ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ • μ.variation
  _ = ‖c‖₊ • (c⁻¹ • (c • μ)).variation := by simp [smul_smul, inv_mul_cancel₀ hc]
  _ ≤ ‖c‖₊ • ‖c⁻¹‖₊ • (c • μ).variation := by
    gcongr
    exact variation_smul_le
  _ = (c • μ).variation := by
    simp [smul_smul, mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hc)]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (c • μ).variation := by
  simp only [variation_smul]
  infer_instance
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite X] : IsFiniteMeasure μ.variation where
  measure_univ_lt_top := by
    classical
    let : Fintype X := Fintype.ofFinite X
    simp only [variation_apply, preVariation_apply, MeasurableSet.univ, ennrealToMeasure_apply,
      ennrealPreVariation_apply, preVariationFun, ↓reduceDIte, ← sup_univ_eq_ciSup]
    exact (Finset.sup_lt_iff (by simp)).2 (fun b hb ↦ by simp [ENNReal.sum_lt_top, enorm_lt_top])
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : X} {v : V} : IsFiniteMeasure (VectorMeasure.dirac x v).variation := by
  simp only [variation_dirac, enorm_eq_nnnorm, Measure.coe_nnreal_smul]
  infer_instance
/-
**MeasureTheory.VectorMeasure._root_.MeasureTheory.Measure.variation_toSignedMea
sure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.MeasureTheory.Measure.variation_toSignedMeasure
    {μ : Measure X} [IsFiniteMeasure μ] :
    μ.toSignedMeasure.variation = μ := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs ↦ ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]

/-- For a signed measure, the variation is realized by the norm of the measure of a single set, up
to a factor of `2` and an arbitrarily small error. -/
/-
**MeasureTheory.VectorMeasure._root_.MeasureTheory.SignedMeasure.exists_subset_l
t_enorm_apply_of_lt_variation** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMea
sure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a signed measure, the variation is realized by the norm of the measure of a 
single set, up
to a factor of `2` and an arbitrarily small error.
-/
lemma _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
    (μ : SignedMeasure X) {s : Set X} (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.variation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  /- One may almost realize the variation through a partition into finitely many sets.
  As their measures are real numbers, we can group together those of positive measure, and
  also those of negative measure. This gives two measurable sets. Among these two, the one with the
  largest measure in absolute value satisfies the result. -/
  obtain ⟨P, Ps, P_disj, P_meas, hP⟩ : ∃ (P : Finset (Set X)), (∀ t ∈ P, t ⊆ s) ∧
    ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (∀ t ∈ P, MeasurableSet t) ∧ a < ∑ p ∈ P, ‖μ p‖ₑ := exists_lt_sum_of_lt_variation _ hs ha
  have I : (∑ p ∈ P.filter (fun p ↦ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ := by
    simp only [Real.norm_eq_abs, enorm_eq_nnnorm,
      ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_inj, ← NNReal.coe_inj,
      NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with 0 ≤ μ x, |μ x| = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := calc
      _ = ∑ x ∈ P with 0 ≤ μ x, μ x := by
        apply Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp]
      _ = μ (⋃ x ∈ P.filter (fun x ↦ 0 ≤ μ x), x) := by
        rw [of_biUnion_finset]
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonneg]
    rw [← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  have J : (∑ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ := by
    simp only [not_le, enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_inj, ← NNReal.coe_inj, NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x ∈ P with μ x < 0, |μ x| = - μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := calc
      ∑ x ∈ P with μ x < 0, |μ x|
      _ = ∑ x ∈ P with μ x < 0, -μ x := by
        refine Finset.sum_congr rfl (fun p hp ↦ ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp.2.le]
      _ = -μ (⋃ x ∈ P.filter (fun x ↦ μ x < 0), x) := by
        rw [of_biUnion_finset]
        · simp
        · apply P_disj.subset (by grind)
        · grind
    rw [A, abs_of_nonpos]
    rw [← neg_nonneg, ← A]
    exact Finset.sum_nonneg (fun p hp ↦ by positivity)
  simp_rw [two_mul]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p ↦ 0 ≤ μ p), I, J] at hP
  rcases le_total (‖μ (⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p)‖ₑ)
    (‖μ (⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p)‖ₑ) with h | h
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)
  · refine ⟨⋃ p ∈ P.filter (fun p ↦ ¬ 0 ≤ μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)

end NormedAddCommGroup

section ENNReal

variable (μ : VectorMeasure X ℝ≥0∞)

/-- For `μ : VectorMeasure X ℝ≥0∞` and measurable `s`, the supremum over Finpartitions of
`⟨s, hs⟩ : Subtype MeasurableSet` of the sum of `μ` over parts equals `μ s`. -/
@[simp]
/-
**MeasureTheory.VectorMeasure.iSup_sum_finpartition_parts** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：iSup_sum_finpartition_parts {s : Set X} (hs : MeasurableSet s) : ⨆ (P : Fi
npartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p in P.parts, μ p.val = μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.VectorMeasure.sum_finpartition`：sum_finpartition [AddCommM
onoid V] [TopologicalSpace V] [T2Space V] (μ : VectorMeasure X V) {s : Set X} {h
s : MeasurableSet s} (P : Finparti…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For `μ : VectorMeasure X ℝ≥0∞` and measurable `s`, the supremum over Finpartitio
ns of
`⟨s, hs⟩ : Subtype MeasurableSet` of the sum of `μ` over parts equals `μ s`.
-/
lemma iSup_sum_finpartition_parts {s : Set X} (hs : MeasurableSet s) :
    ⨆ (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, μ p.val = μ s := by
  simp_rw [μ.sum_finpartition, iSup_const]

/-- For `μ : VectorMeasure X ℝ≥0∞`, `preVariationFun μ s = μ s` for any `s`. -/
/-
**MeasureTheory.VectorMeasure.preVariationFun_apply_of_ennreal** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：preVariationFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.preVariationFun_apply`：preVariationFun_apply {s : Set X} (
h : MeasurableSet s) : preVariationFun f s = ⨆ (P : Finpartition (⟨s, h⟩ : Subty
pe MeasurableSet)), ∑ p i…
· 使用引理 `MeasureTheory.VectorMeasure.iSup_sum_finpartition_parts`：iSup_sum_finpar
tition_parts {s : Set X} (hs : MeasurableSet s) : ⨆ (P : Finpartition (⟨s, hs⟩ :
 Subtype MeasurableSet)), ∑ p in P.parts, μ p…
· 使用引理 `MeasureTheory.preVariationFun_of_not_measurableSet`：preVariationFun_of_n
ot_measurableSet {s : Set X} (h : ¬ MeasurableSet s) : preVariationFun f s = 0
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0

--- 原说明 ---
For `μ : VectorMeasure X ℝ≥0∞`, `preVariationFun μ s = μ s` for any `s`.
-/
lemma preVariationFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s := by
  by_cases h : MeasurableSet s
  · rw [preVariationFun_apply]
    exact iSup_sum_finpartition_parts μ h
  · rw [preVariationFun_of_not_measurableSet μ h, not_measurable μ h]
/-
**MeasureTheory.VectorMeasure.variation_eq_ennrealToMeasure** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：variation_eq_ennrealToMeasure : μ.variation = μ.ennrealToMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_apply`：ennrealToMeasure_app
ly {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α} (hs : Meas
urableSet s) : ennrealToMeasure v s = v …
· 使用引理 `MeasureTheory.VectorMeasure.preVariationFun_apply_of_ennreal`：preVariati
onFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem variation_eq_ennrealToMeasure : μ.variation = μ.ennrealToMeasure := by
  ext _ hs
  simp [preVariationFun_apply_of_ennreal, variation_apply, preVariation_apply,
    ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.ennrealVariation_eq_self** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：ennrealVariation_eq_self : μ.ennrealVariation = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.variation_eq_ennrealToMeasure`：variation_eq_
ennrealToMeasure : μ.variation = μ.ennrealToMeasure
· 使用定理 `MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} (μ : MeasureTheory.VectorMeasure α ENNReal),   μ
.ennrealToMeasure.toENNRealVectorMeasure = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ennrealVariation_eq_self : μ.ennrealVariation = μ := by
  simp [variation_eq_ennrealToMeasure, ennrealVariation]

end ENNReal

end MeasureTheory.VectorMeasure

