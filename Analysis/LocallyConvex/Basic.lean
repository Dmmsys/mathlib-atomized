/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Bornology.Absorbs
/-!
# Local convexity

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `Absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `Absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `Balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## Main Results
* `Absorbent.submodule_eq_top` shows that when the base field is nontrivially normed, an absorbent
  submodule is actually the whole space. As an application, we show in
  `Absorbent.subset_image_iff_surjective` that a linear function is surjective if and only if its
  image contains an absorbent set.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/

@[expose] public section

assert_not_exists NormedSpace

open Set
open scoped Pointwise Topology

variable {𝕜 𝕝 E F : Type*} {ι : Sort*} {κ : ι → Sort*}

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable [SMul 𝕜 E] {s A B : Set E}

variable (𝕜) in
/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
/-
**Balanced** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Balanced (A : Set E)
参数：A : Set E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at mo
st `1`.
-/
def Balanced (A : Set E) :=
  ∀ a : 𝕜, ‖a‖ ≤ 1 → a • A ⊆ A
/-
**absorbs_iff_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absorbs_iff_norm : Absorbs 𝕜 A B ↔ exists r, forall c : 𝕜, r <= ‖c‖ -> B s
ubseteq c • A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.cobounded_of_norm`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set ℝ},   Filter.atTop.HasBasis
 p s → (Bornology.cobou…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma absorbs_iff_norm : Absorbs 𝕜 A B ↔ ∃ r, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans <| by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm
/-
**Absorbs.exists_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 0, forall c : 𝕜, r <= 
‖c‖ -> B subseteq c • A
参数：h : Absorbs 𝕜 A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.cobounded_of_norm`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set ℝ},   Filter.atTop.HasBasis
 p s → (Bornology.cobou…
· 使用定理 `Filter.atTop_basis'`：atTop_basis' (a : α) : atTop.HasBasis (a <= ·) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma Absorbs.exists_pos (h : Absorbs 𝕜 A B) : ∃ r > 0, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩
/-
**balanced_iff_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iff_smul_mem : Balanced 𝕜 s ↔ forall ⦃a : 𝕜⦄, ‖a‖ <= 1 -> forall 
⦃x : E⦄, x in s -> a • x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
-/
theorem balanced_iff_smul_mem : Balanced 𝕜 s ↔ ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x : E⦄, x ∈ s → a • x ∈ s :=
  forall₂_congr fun _a _ha => smul_set_subset_iff

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem
/-
**balanced_iff_closedBall_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iff_closedBall_smul : Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 
• s subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem balanced_iff_closedBall_smul : Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 • s ⊆ s := by
  simp [balanced_iff_smul_mem, smul_subset_iff]

@[simp]
/-
**balanced_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_empty : Balanced 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem balanced_empty : Balanced 𝕜 (∅ : Set E) := fun _ _ => by rw [smul_set_empty]

@[simp]
/-
**balanced_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_univ : Balanced 𝕜 (univ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem balanced_univ : Balanced 𝕜 (univ : Set E) := fun _a _ha => subset_univ _
/-
**Balanced.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A uni
on B)
参数：hA : Balanced 𝕜 A；hB : Balanced 𝕜 B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
-/
theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := fun _a ha =>
  smul_set_union.subset.trans <| union_subset_union (hA _ ha) <| hB _ ha
/-
**Balanced.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A int
er B)
参数：hA : Balanced 𝕜 A；hB : Balanced 𝕜 B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_set_inter_subset`：smul_set_inter_subset : a • (t₁ inter t₂) sub
seteq a • t₁ inter a • t₂
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
-/
theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := fun _a ha =>
  smul_set_inter_subset.trans <| inter_subset_inter (hA _ ha) <| hB _ ha
/-
**balanced_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iUnion {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanc
ed 𝕜 (⋃ i, f i)
参数：h : forall i, Balanced 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Set.smul_set_iUnion`：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i,
 s i = ⋃ i, a • s i
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
-/
theorem balanced_iUnion {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋃ i, f i) :=
  fun _a ha => (smul_set_iUnion _ _).subset.trans <| iUnion_mono fun _ => h _ _ ha
/-
**balanced_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iUnion {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanc
ed 𝕜 (⋃ i, f i)
参数：h : forall i, Balanced 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Set.smul_set_iUnion`：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i,
 s i = ⋃ i, a • s i
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
-/
theorem balanced_iUnion₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋃ (i) (j), f i j) :=
  balanced_iUnion fun _ => balanced_iUnion <| h _
/-
**Balanced.sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.sInter {S : Set (Set E)} (h : forall s in S, Balanced 𝕜 s) : Bala
nced 𝕜 (⋂₀ S)
参数：Set E；h : forall s in S, Balanced 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_set_sInter_subset`：smul_set_sInter_subset (a : α) (S : Set (Set
 β)) : a • ⋂₀ S subseteq ⋂ s in S, a • s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem Balanced.sInter {S : Set (Set E)} (h : ∀ s ∈ S, Balanced 𝕜 s) : Balanced 𝕜 (⋂₀ S) :=
  fun _ _ => (smul_set_sInter_subset ..).trans (fun _ _ => by aesop)
/-
**balanced_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iInter {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanc
ed 𝕜 (⋂ i, f i)
参数：h : forall i, Balanced 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_set_iInter_subset`：smul_set_iInter_subset (a : α) (t : ι -> Set
 β) : a • ⋂ i, t i subseteq ⋂ i, a • t i
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
-/
theorem balanced_iInter {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋂ i, f i) :=
  fun _a ha => (smul_set_iInter_subset _ _).trans <| iInter_mono fun _ => h _ _ ha
/-
**balanced_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iInter {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanc
ed 𝕜 (⋂ i, f i)
参数：h : forall i, Balanced 𝕜 (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_set_iInter_subset`：smul_set_iInter_subset (a : α) (t : ι -> Set
 β) : a • ⋂ i, t i subseteq ⋂ i, a • t i
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
-/
theorem balanced_iInter₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋂ (i) (j), f i j) :=
  balanced_iInter fun _ => balanced_iInter <| h _
/-
**Balanced.mulActionHom_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.mulActionHom_preimage [SMul 𝕜 F] {s : Set F} (hs : Balanced 𝕜 s) 
(f : E ->[𝕜] F) : Balanced 𝕜 (f ⁻¹' s)
参数：hs : Balanced 𝕜 s；f : E ->[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem Balanced.mulActionHom_preimage [SMul 𝕜 F] {s : Set F} (hs : Balanced 𝕜 s)
    (f : E →[𝕜] F) : Balanced 𝕜 (f ⁻¹' s) := fun a ha x ⟨y,⟨hy₁,hy₂⟩⟩ => by
  rw [mem_preimage, ← hy₂, map_smul]
  exact hs a ha (smul_mem_smul_set hy₁)

variable [SMul 𝕝 E] [SMulCommClass 𝕜 𝕝 E]
/-
**Balanced.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s)
参数：a : 𝕝；hs : Balanced 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
-/
theorem Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s) := fun _b hb =>
  (smul_comm _ _ _).subset.trans <| smul_set_mono <| hs _ hb

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/-
**Balanced.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.neg : Balanced 𝕜 s -> Balanced 𝕜 (-s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Set.smul_set_neg`：smul_set_neg : a • -t = -(a • t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.neg_subset_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s t : Set
 α}, -s ⊆ -t ↔ s ⊆ t
-/
theorem Balanced.neg : Balanced 𝕜 s → Balanced 𝕜 (-s) :=
  forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans <| neg_subset_neg.2 h

@[simp]
/-
**balanced_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_neg : Balanced 𝕜 (-s) ↔ Balanced 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.neg`：Balanced.neg : Balanced 𝕜 s -> Balanced 𝕜 (-s)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem balanced_neg : Balanced 𝕜 (-s) ↔ Balanced 𝕜 s :=
  ⟨fun h ↦ neg_neg s ▸ h.neg, fun h ↦ h.neg⟩
/-
**Balanced.neg_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balanced 𝕜 s) {x : E} : -x in s
 ↔ x in s
参数：h : Balanced 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
-/
theorem Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balanced 𝕜 s) {x : E} : -x ∈ s ↔ x ∈ s :=
  ⟨fun hx ↦ by simpa using h.smul_mem (a := -1) (by simp) hx,
    fun hx ↦ by simpa using h.smul_mem (a := -1) (by simp) hx⟩
/-
**Balanced.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.neg_eq [NormOneClass 𝕜] (h : Balanced 𝕜 s) : -s = s
参数：h : Balanced 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Balanced.neg_mem_iff`：Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balance
d 𝕜 s) {x : E} : -x in s ↔ x in s
-/
theorem Balanced.neg_eq [NormOneClass 𝕜] (h : Balanced 𝕜 s) : -s = s :=
  Set.ext fun _ ↦ h.neg_mem_iff
/-
**Balanced.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t)
参数：hs : Balanced 𝕜 s；ht : Balanced 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
-/
theorem Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t) := fun _a ha =>
  (smul_add _ _ _).subset.trans <| add_subset_add (hs _ ha) <| ht _ ha
/-
**Balanced.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t)
参数：hs : Balanced 𝕜 s；ht : Balanced 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Balanced.add`：Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Bal
anced 𝕜 (s + t)
· 使用定理 `Balanced.neg`：Balanced.neg : Balanced 𝕜 s -> Balanced 𝕜 (-s)
-/
theorem Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg
/-
**balanced_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_zero : Balanced 𝕜 (0 : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem balanced_zero : Balanced 𝕜 (0 : Set E) := fun _a _ha => (smul_zero _).subset

end Module

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/-
**absorbs_iff_eventually_nhdsNE_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbs_iff_eventually_nhdsNE_zero : Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝[!=
] 0, MapsTo (c • ·) t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `absorbs_iff_eventually_cobounded_mapsTo`：absorbs_iff_eventually_cobounde
d_mapsTo : Absorbs G₀ s t ↔ forallᶠ c in cobounded G₀, MapsTo (c⁻¹ • ·) t s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.inv_cobounded₀`：inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[!=] 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem absorbs_iff_eventually_nhdsNE_zero :
    Absorbs 𝕜 s t ↔ ∀ᶠ c : 𝕜 in 𝓝[≠] 0, MapsTo (c • ·) t s := by
  rw [absorbs_iff_eventually_cobounded_mapsTo, ← Filter.inv_cobounded₀]; rfl

alias ⟨Absorbs.eventually_nhdsNE_zero, _⟩ := absorbs_iff_eventually_nhdsNE_zero
/-
**absorbent_iff_eventually_nhdsNE_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbent_iff_eventually_nhdsNE_zero : Absorbent 𝕜 s ↔ forall x : E, foral
lᶠ c : 𝕜 in 𝓝[!=] 0, c • x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem absorbent_iff_eventually_nhdsNE_zero :
    Absorbent 𝕜 s ↔ ∀ x : E, ∀ᶠ c : 𝕜 in 𝓝[≠] 0, c • x ∈ s :=
  forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_nhdsNE_zero, mapsTo_singleton]

alias ⟨Absorbent.eventually_nhdsNE_zero, _⟩ := absorbent_iff_eventually_nhdsNE_zero
/-
**absorbs_iff_eventually_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbs_iff_eventually_nhds_zero (h₀ : 0 in s) : Absorbs 𝕜 s t ↔ forallᶠ c
 : 𝕜 in 𝓝 0, MapsTo (c • ·) t s
参数：h₀ : 0 in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsNE_sup_pure`：nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Filter.eventually_pure`：eventually_pure {a : α} {p : α -> Prop} : (foral
lᶠ x in pure a, p x) ↔ p a
· 使用定理 `absorbs_iff_eventually_nhdsNE_zero`：absorbs_iff_eventually_nhdsNE_zero :
 Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝[!=] 0, MapsTo (c • ·) t s
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem absorbs_iff_eventually_nhds_zero (h₀ : 0 ∈ s) :
    Absorbs 𝕜 s t ↔ ∀ᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s := by
  rw [← nhdsNE_sup_pure, Filter.eventually_sup, Filter.eventually_pure,
    ← absorbs_iff_eventually_nhdsNE_zero, and_iff_left]
  intro x _
  simpa only [zero_smul]
/-
**Absorbs.eventually_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Absorbs.eventually_nhds_zero (h : Absorbs 𝕜 s t) (h₀ : 0 in s) : forallᶠ c
 : 𝕜 in 𝓝 0, MapsTo (c • ·) t s
参数：h : Absorbs 𝕜 s t；h₀ : 0 in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `absorbs_iff_eventually_nhds_zero`：absorbs_iff_eventually_nhds_zero (h₀ :
 0 in s) : Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s
-/
theorem Absorbs.eventually_nhds_zero (h : Absorbs 𝕜 s t) (h₀ : 0 ∈ s) :
    ∀ᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s :=
  (absorbs_iff_eventually_nhds_zero h₀).1 h

variable [NormedRing 𝕝] [Module 𝕜 𝕝] [NormSMulClass 𝕜 𝕝] [SMulWithZero 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
  {a b : 𝕜} {x : E}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
/-
**Balanced.smul_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : ‖a‖ <= ‖b‖) : a • s su
bseteq b • s
参数：hs : Balanced 𝕝 s；h : ‖a‖ <= ‖b‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Scalar multiplication (by possibly different types) of a balanced set is monoton
e.
-/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : ‖a‖ ≤ ‖b‖) : a • s ⊆ b • s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero, norm_le_zero_iff] at h
    simp only [h, ← image_smul, zero_smul, Subset.rfl]
  · calc
      a • s = b • (b⁻¹ • a) • s := by rw [smul_assoc, smul_inv_smul₀ hb]
      _ ⊆ b • s := smul_set_mono <| hs _ <| by
        rw [norm_smul, norm_inv, ← div_eq_inv_mul]
        exact div_le_one_of_le₀ h (norm_nonneg _)
/-
**Balanced.smul_mem_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul_mem_mono [SMulCommClass 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {b : 𝕝} (
ha : a • x in s) (hba : ‖b‖ <= ‖a‖) : b • x in s
参数：hs : Balanced 𝕝 s；ha : a • x in s；hba : ‖b‖ <= ‖a‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem Balanced.smul_mem_mono [SMulCommClass 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {b : 𝕝}
    (ha : a • x ∈ s) (hba : ‖b‖ ≤ ‖a‖) : b • x ∈ s := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp_all
  · calc
      (a⁻¹ • b) • a • x ∈ s := by
        refine hs.smul_mem ?_ ha
        rw [norm_smul, norm_inv, ← div_eq_inv_mul]
        exact div_le_one_of_le₀ hba (norm_nonneg _)
      (a⁻¹ • b) • a • x = b • x := by rw [smul_comm, smul_assoc, smul_inv_smul₀ ha₀]
/-
**Balanced.subset_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.subset_smul (hs : Balanced 𝕜 s) (ha : 1 <= ‖a‖) : s subseteq a • 
s
参数：hs : Balanced 𝕜 s；ha : 1 <= ‖a‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Balanced.smul_mono`：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : 
‖a‖ <= ‖b‖) : a • s subseteq b • s
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem Balanced.subset_smul (hs : Balanced 𝕜 s) (ha : 1 ≤ ‖a‖) : s ⊆ a • s := by
  rw [← @norm_one 𝕜] at ha; simpa using hs.smul_mono ha
/-
**Balanced.smul_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul_congr (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • s = b • s
参数：hs : Balanced 𝕜 s；h : ‖a‖ = ‖b‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Balanced.smul_mono`：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : 
‖a‖ <= ‖b‖) : a • s subseteq b • s
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem Balanced.smul_congr (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • s = b • s :=
  (hs.smul_mono h.le).antisymm (hs.smul_mono h.ge)
/-
**Balanced.smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul_eq (hs : Balanced 𝕜 s) (ha : ‖a‖ = 1) : a • s = s
参数：hs : Balanced 𝕜 s；ha : ‖a‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Balanced.subset_smul`：Balanced.subset_smul (hs : Balanced 𝕜 s) (ha : 1 <
= ‖a‖) : s subseteq a • s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem Balanced.smul_eq (hs : Balanced 𝕜 s) (ha : ‖a‖ = 1) : a • s = s :=
  (hs _ ha.le).antisymm <| hs.subset_smul ha.ge

/-- A balanced set absorbs itself. -/
/-
**Balanced.absorbs_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.absorbs_self (hs : Balanced 𝕜 s) : Absorbs 𝕜 s s
参数：hs : Balanced 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbs.of_norm`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 
𝕜] [inst_1 : SMul 𝕜 E] {A B : Set E},   (∃ r, ∀ (c : 𝕜), r ≤ ‖c‖ → B ⊆ c • A) → 
Absor…
· 使用定理 `Balanced.subset_smul`：Balanced.subset_smul (hs : Balanced 𝕜 s) (ha : 1 <
= ‖a‖) : s subseteq a • s

--- 原说明 ---
A balanced set absorbs itself.
-/
theorem Balanced.absorbs_self (hs : Balanced 𝕜 s) : Absorbs 𝕜 s s :=
  .of_norm ⟨1, fun _ => hs.subset_smul⟩

end NormedDivisionRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s A : Set E} {x : E} {a b : 𝕜}

/-
**Balanced.smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.smul_mem_iff (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x in s ↔ b
 • x in s
参数：hs : Balanced 𝕜 s；h : ‖a‖ = ‖b‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.smul_mem_mono`：Balanced.smul_mem_mono [SMulCommClass 𝕝 𝕜 E] (hs
 : Balanced 𝕝 s) {b : 𝕝} (ha : a • x in s) (hba : ‖b‖ <= ‖a‖) : b • x in s
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Balanced.smul_mem_iff (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x ∈ s ↔ b • x ∈ s :=
  ⟨(hs.smul_mem_mono · h.ge), (hs.smul_mem_mono · h.le)⟩

variable [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
/-
**absorbent_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbent 𝕜 A
参数：hA : A in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `absorbent_iff_inv_smul`：absorbent_iff_inv_smul {s : Set α} : Absorbent G
₀ s ↔ forall x, forallᶠ c in cobounded G₀, c⁻¹ • x in s
· 使用定理 `Filter.Tendsto.zero_smul_const`：∀ {M : Type u_1} {X : Type u_2} {α : Typ
e u_4} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Zer
o M] [inst_3 : Zero …
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)

--- 原说明 ---
Every neighbourhood of the origin is absorbent.
-/
theorem absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : Absorbent 𝕜 A :=
  absorbent_iff_inv_smul.2 fun _ ↦ Filter.tendsto_inv₀_cobounded.zero_smul_const _ hA

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
/-
**Balanced.zero_insert_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.zero_insert_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 (insert 0 (
interior A))
参数：hA : Balanced 𝕜 A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `IsOpenMap.mapsTo_interior`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {s :
 Set X} {t : Se…
· 使用定理 `isOpenMap_smul₀`：isOpenMap_smul₀ {c : G₀} (hc : c != 0) : IsOpenMap fun 
x : α => c • x
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …

--- 原说明 ---
The union of `{0}` with the interior of a balanced set is balanced.
-/
theorem Balanced.zero_insert_interior (hA : Balanced 𝕜 A) :
    Balanced 𝕜 (insert 0 (interior A)) := by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left, ⟨0, Or.inl rfl⟩]
  · rw [← image_smul, image_insert_eq, smul_zero]
    apply insert_subset_insert
    exact ((isOpenMap_smul₀ h).mapsTo_interior <| hA.smul_mem ha).image_subset

/-- The interior of a balanced set is balanced if it contains the origin. -/
/-
**Balanced.interior** 是 Mathlib 中的一个定理，位于命名空间 `Balanced`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {A : Set E} [inst_3 : TopologicalSpace E] 
[ContinuousSMul 𝕜 E],   Balanced 𝕜 A → 0 ∈ interior A → Balanced 𝕜 (interior A)
参数：interior A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_eq_self`：insert_eq_self : insert a s = s ↔ a in s
· 使用定理 `Balanced.zero_insert_interior`：Balanced.zero_insert_interior (hA : Balan
ced 𝕜 A) : Balanced 𝕜 (insert 0 (interior A))

--- 原说明 ---
The interior of a balanced set is balanced if it contains the origin.
-/
protected theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
    Balanced 𝕜 (interior A) := by
  rw [← insert_eq_self.2 h]
  exact hA.zero_insert_interior
/-
**Balanced.closure** 是 Mathlib 中的一个定理，位于命名空间 `Balanced`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {A : Set E} [inst_3 : TopologicalSpace E] 
[ContinuousSMul 𝕜 E], Balanced 𝕜 A → Balanced 𝕜 (closure A)
参数：closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
protected theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (closure A) := fun _a ha =>
  (image_closure_subset_closure_image <| continuous_const_smul _).trans <|
    closure_mono <| hA _ ha

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

variable [PartialOrder 𝕜] in
/-
**Balanced.convexHull** 是 Mathlib 中的一个定理，位于命名空间 `Balanced`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {s : Set E} [inst_3 : PartialO
rder 𝕜], Balanced 𝕜 s → Balanced 𝕜 ((convexHull 𝕜) s)
参数：(convexHull 𝕜) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `balanced_iff_smul_mem`：balanced_iff_smul_mem : Balanced 𝕜 s ↔ forall ⦃a 
: 𝕜⦄, ‖a‖ <= 1 -> forall ⦃x : E⦄, x in s -> a • x in s
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
protected theorem Balanced.convexHull (hs : Balanced 𝕜 s) : Balanced 𝕜 (convexHull 𝕜 s) := by
  suffices Convex 𝕜 { x | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ convexHull 𝕜 s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ this hx a ha
    exact fun y hy a ha => subset_convexHull 𝕜 s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  rw [smul_add, ← smul_comm u, ← smul_comm v]
  exact convex_convexHull 𝕜 s (hx a ha) (hy a ha) hu hv huv

variable {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E]
/-
**Absorbent.eq_univ_of_smulMemClass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Absorbent.eq_univ_of_smulMemClass {V : S} (hV : Absorbent 𝕜 (V : Set E)) :
 (V : Set E) = univ
参数：hV : Absorbent 𝕜 (V : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `absorbent_iff_eventually_nhdsNE_zero`：absorbent_iff_eventually_nhdsNE_ze
ro : Absorbent 𝕜 s ↔ forall x : E, forallᶠ c : 𝕜 in 𝓝[!=] 0, c • x in s
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
theorem Absorbent.eq_univ_of_smulMemClass {V : S} (hV : Absorbent 𝕜 (V : Set E)) :
    (V : Set E) = univ := by
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨c, hc, hc'⟩ :=
    ((absorbent_iff_eventually_nhdsNE_zero.mp hV x).and eventually_mem_nhdsWithin).exists
  rw [← inv_smul_smul₀ hc' x]
  exact SMulMemClass.smul_mem c⁻¹ hc
/-
**Absorbent.submodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Absorbent.submodule_eq_top {V : Submodule 𝕜 E} (hV : Absorbent 𝕜 (V : Set 
E)) : V = ⊤
参数：hV : Absorbent 𝕜 (V : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.apply_eq_top_iff`：StrictMono.apply_eq_top_iff (hf : StrictMon
o f) : f a = f ⊤ ↔ a = ⊤
· 使用定理 `Absorbent.eq_univ_of_smulMemClass`：Absorbent.eq_univ_of_smulMemClass {V 
: S} (hV : Absorbent 𝕜 (V : Set E)) : (V : Set E) = univ
-/
theorem Absorbent.submodule_eq_top {V : Submodule 𝕜 E} (hV : Absorbent 𝕜 (V : Set E)) :
    V = ⊤ := (StrictMono.apply_eq_top_iff (α := Submodule 𝕜 E) (β := Set E) (fun _ _ a_1 ↦ a_1)).mp
  hV.eq_univ_of_smulMemClass

variable {F 𝕜₂ : Type*} [Semiring 𝕜₂] {σ : 𝕜₂ →+* 𝕜}
variable [AddCommGroup F] [Module 𝕜₂ F]
/-
**Absorbent.subset_range_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Absorbent.subset_range_iff_surjective [RingHomSurjective σ] {f : F ->ₛₗ[σ]
 E} {s : Set E} (hs_abs : Absorbent 𝕜 s) : s subseteq f.range ↔ (⇑f).Surjective
参数：hs_abs : Absorbent 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Absorbent.submodule_eq_top`：Absorbent.submodule_eq_top {V : Submodule 𝕜 
E} (hV : Absorbent 𝕜 (V : Set E)) : V = ⊤
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
-/
theorem Absorbent.subset_range_iff_surjective [RingHomSurjective σ] {f : F →ₛₗ[σ] E} {s : Set E}
    (hs_abs : Absorbent 𝕜 s) : s ⊆ f.range ↔ (⇑f).Surjective :=
  ⟨fun hs_sub ↦ LinearMap.range_eq_top.mp ((hs_abs.mono hs_sub).submodule_eq_top), fun h a _ ↦ h a⟩

end NontriviallyNormedField

section Real

variable [AddCommGroup E] [Module ℝ E] {s : Set E}

/-
**balanced_iff_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_iff_neg_mem (hs : Convex Real s) : Balanced Real s ↔ forall ⦃x⦄, 
x in s -> -x in s
参数：hs : Convex Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Balanced.neg_mem_iff`：Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balance
d 𝕜 s) {x : E} : -x in s ↔ x in s
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
（共 78 条，此处仅展示前 30 条）
-/
theorem balanced_iff_neg_mem (hs : Convex ℝ s) : Balanced ℝ s ↔ ∀ ⦃x⦄, x ∈ s → -x ∈ s := by
  refine ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => ?_⟩
  rw [Real.norm_eq_abs, abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring, add_smul, neg_smul, ← smul_neg]
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_le_two)
    (div_nonneg (sub_nonneg_of_le ha.1) zero_le_two) (by ring)
/-
**Balanced.starConvex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Balanced.starConvex (hs : Balanced Real s) : StarConvex Real 0 s
参数：hs : Balanced Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `starConvex_zero_iff`：starConvex_zero_iff : StarConvex 𝕜 0 s ↔ forall ⦃x 
: E⦄, x in s -> forall ⦃a : 𝕜⦄, 0 <= a -> a <= 1 -> a • x in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem Balanced.starConvex (hs : Balanced ℝ s) : StarConvex ℝ 0 s :=
  starConvex_zero_iff.2 fun _ hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)

end Real

