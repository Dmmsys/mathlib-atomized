/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Radon's theorem on convex sets

Radon's theorem states that any affine dependent set can be partitioned into two sets whose convex
hulls intersect nontrivially.

As a corollary, we prove Helly's theorem, which is a basic result in discrete geometry on the
intersection of convex sets. Let `X₁, ⋯, Xₙ` be a finite family of convex sets in `ℝᵈ` with
`n ≥ d + 1`. The theorem states that if any `d + 1` sets from this family intersect nontrivially,
then the whole family intersects nontrivially. For the infinite family of sets it is not true, as
the example of `Set.Ioo 0 (1 / n)` for `n : ℕ` shows. But the statement is true if we assume
compactness of sets (see `helly_theorem_compact`).

## Tags

convex hull, affine independence, Radon, Helly
-/

public section

open Fintype Finset Set

namespace Convex

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- **Radon's theorem on convex sets**.

Any family `f` of affine dependent vectors contains a set `I` with the property that convex hulls of
`I` and `Iᶜ` intersect nontrivially.
In particular, any `d + 2` points in a `d`-dimensional space can be partitioned this way, since they
are affinely dependent (see `finrank_vectorSpan_le_iff_not_affineIndependent`). -/
/-
**Convex.radon_partition** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：radon_partition {f : ι -> E} (h : ¬ AffineIndependent 𝕜 f) : exists I, (co
nvexHull 𝕜 (f '' I) inter convexHull 𝕜 (f '' Iᶜ)).Nonempty
参数：h : ¬ AffineIndependent 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `affineIndependent_iff`：affineIndependent_iff {ι} {p : ι -> V} : AffineIn
dependent k p ↔ forall (s : Finset ι) (w : ι -> k), s.sum w = 0 -> ∑ e in s, w e
 • p e = 0 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `Finset.exists_pos_of_sum_zero_of_exists_nonzero`：∀ {ι : Type u_1} {M : T
ype u_4} [inst : AddCommMonoid M] [inst_1 : LinearOrder M] {s : Finset ι}   [IsO
rderedCancelAddMonoid M] (f : ι → M),…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Finset.centerMass_of_sum_add_sum_eq_zero`：Finset.centerMass_of_sum_add_s
um_eq_zero {s t : Finset ι} (hw : ∑ i in s, w i + ∑ i in t, w i = 0) (hz : ∑ i i
n s, w i • z i + ∑ i in t, w i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
**Radon's theorem on convex sets**.

Any family `f` of affine dependent vectors contains a set `I` with the property 
that convex hulls of
`I` and `Iᶜ` intersect nontrivially.
In particular, any `d + 2` points in a `d`-dimensional space can be partitioned 
this way, since they
are affinely dependent (see `finrank_vectorSpan_le_iff_not_affineIndependent`).
-/
theorem radon_partition {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by
  rw [affineIndependent_iff] at h
  push Not at h
  obtain ⟨s, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩ := h
  let I : Finset ι := {i ∈ s | 0 ≤ w i}
  let J : Finset ι := {i ∈ s | w i < 0}
  let p : E := centerMass I w f -- point of intersection
  have hJI : ∑ j ∈ J, w j + ∑ i ∈ I, w i = 0 := by
    simpa only [h_wsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) w
  have hI : 0 < ∑ i ∈ I, w i := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos' (fun _i hi ↦ (mem_filter.1 hi).2)
      ⟨pos_w_index, by simp only [I, mem_filter, h1', h2'.le, and_self, h2']⟩
  have hp : centerMass J w f = p := centerMass_of_sum_add_sum_eq_zero hJI <| by
    simpa only [← h_vsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) _
  refine ⟨I, p, ?_, ?_⟩
  · exact centerMass_mem_convexHull _ (fun _i hi ↦ (mem_filter.mp hi).2) hI
      (fun _i hi ↦ mem_image_of_mem _ hi)
  rw [← hp]
  refine centerMass_mem_convexHull_of_nonpos _ (fun _ hi ↦ (mem_filter.mp hi).2.le) ?_
    (fun _i hi ↦ mem_image_of_mem _ fun hi' ↦ ?_)
  · linarith only [hI, hJI]
  · exact (mem_filter.mp hi').2.not_gt (mem_filter.mp hi).2

open Module

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Corner case for `helly_theorem'`. -/
/-
**Convex.helly_theorem_corner** 是 Mathlib 中的一个引理，位于命名空间 `Convex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corner case for `helly_theorem'`.
-/
private lemma helly_theorem_corner {F : ι → Set E} {s : Finset ι}
    (h_card_small : #s ≤ finrank 𝕜 E + 1)
    (h_inter : ∀ I ⊆ s, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := h_inter s (by simp) h_card_small

variable [FiniteDimensional 𝕜 E]

/-- **Helly's theorem** for finite families of convex sets.

If `F` is a finite family of convex sets in a vector space of finite dimension `d`, and any
`k ≤ d + 1` sets of `F` intersect nontrivially, then all sets of `F` intersect nontrivially. -/
/-
**Convex.helly_theorem'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem' {F : ι -> Set E} {s : Finset ι} (h_convex : forall i in s, 
Convex 𝕜 (F i)) (h_inter : forall I subseteq s, #I <= finrank 𝕜 E + 1 -> (⋂ i in
 I, F i).Nonempty) : (⋂ i in s, F i).Nonempty
参数：h_convex : forall i in s, Convex 𝕜 (F i)；h_inter : forall I subseteq s, #I <=
 finrank 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `_private.Mathlib.Analysis.Convex.Radon.0.Convex.helly_theorem_corner`：∀ 
{ι : Type u_1} {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1 : AddCommG
roup E] [inst_2 : _root_.Module 𝕜 E]   {F : ι → Set E} {s …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_vectorSpan_le_iff_not_affineIndependent`：finrank_vectorSpan_le_i
ff_not_affineIndependent [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι
 = n + 2) : finrank k (vectorSpan k (…
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `Convex.radon_partition`：radon_partition {f : ι -> E} (h : ¬ AffineIndepe
ndent 𝕜 f) : exists I, (convexHull 𝕜 (f '' I) inter convexHull 𝕜 (f '' Iᶜ)).None
mpty
· 使用定理 `Set.mem_biInter`：mem_biInter {s : Set α} {t : α -> Set β} {y : β} (h : f
orall x in s, y in t x) : y in ⋂ x in s, t x
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.FinsetCoe.canLift`：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s
) Subtype.val fun a => a ∈ s
· 使用定理 `Convex.convexHull_subset_iff`：Convex.convexHull_subset_iff (ht : Convex 
𝕜 t) : convexHull 𝕜 s subseteq t ↔ s subseteq t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Helly's theorem** for finite families of convex sets.

If `F` is a finite family of convex sets in a vector space of finite dimension `
d`, and any
`k ≤ d + 1` sets of `F` intersect nontrivially, then all sets of `F` intersect n
ontrivially.
-/
theorem helly_theorem' {F : ι → Set E} {s : Finset ι}
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := by
  classical
  obtain h_card | h_card := lt_or_ge #s (finrank 𝕜 E + 1)
  · exact helly_theorem_corner (le_of_lt h_card) h_inter
  generalize hn : #s = n
  rw [hn] at h_card
  induction n, h_card using Nat.le_induction generalizing ι with
  | base => exact helly_theorem_corner (le_of_eq hn) h_inter
  /- Construct a family of vectors indexed by `ι` such that the vector corresponding to `i : ι`
  is an arbitrary element of the intersection of all `F j` except `F i`. -/
  | succ k h_card hk =>
  let a (i : s) : E := Set.Nonempty.some (s := ⋂ j ∈ s.erase i, F j) <| by
    apply hk (s := s.erase i)
    · exact fun i hi ↦ h_convex i (mem_of_mem_erase hi)
    · intro J hJ_ss hJ_card
      exact h_inter J (subset_trans hJ_ss (erase_subset i.val s)) hJ_card
    · simp only [coe_mem, card_erase_of_mem]; lia
  /- This family of vectors is not affine independent because the number of them exceeds the
  dimension of the space. -/
  have h_ind : ¬AffineIndependent 𝕜 a := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a (n := (k - 1))]
    · exact (Submodule.finrank_le (vectorSpan 𝕜 (range a))).trans (Nat.le_pred_of_lt h_card)
    · simp only [card_coe]; lia
  /- Use `radon_partition` to conclude there is a subset `I` of `s` and a point `p : E` which
  lies in the convex hull of either `a '' I` or `a '' Iᶜ`. We claim that `p ∈ ⋂ i ∈ s, F i`. -/
  obtain ⟨I, p, hp_I, hp_Ic⟩ := radon_partition h_ind
  use p
  apply mem_biInter
  intro i hi
  lift i to s using hi
  /- It suffices to show that for any subcollection `J` of `s` containing `i`, the convex
  hull of `a '' (s \ J)` is contained in `F i`. -/
  suffices ∀ J : Set s, (i ∈ J) → (convexHull 𝕜) (a '' Jᶜ) ⊆ F i by
    by_cases h : i ∈ I
    · exact this I h hp_Ic
    · apply this Iᶜ h; rwa [compl_compl]
  /- Given any subcollection `J` of `ι` containing `i`, because `F i` is convex, we need only
  show that `a j ∈ F i` for each `j ∈ s \ J`. -/
  intro J hi
  rw [convexHull_subset_iff (h_convex i.1 i.2)]
  rintro v ⟨j, hj, hj_v⟩
  rw [← hj_v]
  /- Since `j ∈ Jᶜ` and `i ∈ J`, we conclude that `i ≠ j`, and hence by the definition of `a`:
  `a j ∈ ⋂ F '' (Set.univ \ {j}) ⊆ F i`. -/
  apply mem_of_subset_of_mem (s₁ := ⋂ k ∈ (s.erase j), F k)
  · apply iInter₂_subset
    simp [mem_erase, ne_of_mem_of_not_mem hi hj]
  · apply Nonempty.some_mem

/-- **Helly's theorem** for finite families of convex sets in its classical form.

If `F` is a family of `n` convex sets in a vector space of finite dimension `d`, with `n ≥ d + 1`,
and any `d + 1` sets of `F` intersect nontrivially, then all sets of `F` intersect nontrivially. -/
/-
**Convex.helly_theorem** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem {F : ι -> Set E} {s : Finset ι} (h_card : finrank 𝕜 E + 1 <=
 #s) (h_convex : forall i in s, Convex 𝕜 (F i)) (h_inter : forall I subseteq s, 
#I = finrank 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty) : (⋂ i in s, F i).Nonempty
参数：h_card : finrank 𝕜 E + 1 <= #s；h_convex : forall i in s, Convex 𝕜 (F i)；h_int
er : forall I subseteq s, #I = finrank 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.helly_theorem'`：helly_theorem' {F : ι -> Set E} {s : Finset ι} (h
_convex : forall i in s, Convex 𝕜 (F i)) (h_inter : forall I subseteq s, #I <= f
inrank 𝕜 E …
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.biInter_mono`：biInter_mono {s s' : Set α} {t t' : α -> Set β} (hs : 
s subseteq s') (h : forall x in s, t x subseteq t' x) : ⋂ x in s', t x subseteq 
⋂ x in…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
**Helly's theorem** for finite families of convex sets in its classical form.

If `F` is a family of `n` convex sets in a vector space of finite dimension `d`,
 with `n ≥ d + 1`,
and any `d + 1` sets of `F` intersect nontrivially, then all sets of `F` interse
ct nontrivially.
-/
theorem helly_theorem {F : ι → Set E} {s : Finset ι}
    (h_card : finrank 𝕜 E + 1 ≤ #s)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := by
  apply helly_theorem' h_convex
  intro I hI_ss hI_card
  obtain ⟨J, hI_ss_J, hJ_ss, hJ_card⟩ := exists_subsuperset_card_eq hI_ss hI_card h_card
  apply Set.Nonempty.mono <| biInter_mono hI_ss_J (fun _ _ ↦ Set.Subset.rfl)
  exact h_inter J hJ_ss hJ_card

/-- **Helly's theorem** for finite sets of convex sets.

If `F` is a finite set of convex sets in a vector space of finite dimension `d`, and any `k ≤ d + 1`
sets from `F` intersect nontrivially, then all sets from `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_set'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_set' {F : Finset (Set E)} (h_convex : forall X in F, Convex 
𝕜 X) (h_inter : forall G : Finset (Set E), G subseteq F -> #G <= finrank 𝕜 E + 1
 -> (⋂₀ G : Set E).Nonempty) : (⋂₀ (F : Set (Set E))).Nonempty
参数：Set E；h_convex : forall X in F, Convex 𝕜 X；h_inter : forall G : Finset (Set E
), G subseteq F -> #G <= finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Convex.helly_theorem'`：helly_theorem' {F : ι -> Set E} {s : Finset ι} (h
_convex : forall i in s, Convex 𝕜 (F i)) (h_inter : forall I subseteq s, #I <= f
inrank 𝕜 E …

--- 原说明 ---
**Helly's theorem** for finite sets of convex sets.

If `F` is a finite set of convex sets in a vector space of finite dimension `d`,
 and any `k ≤ d + 1`
sets from `F` intersect nontrivially, then all sets from `F` intersect nontrivia
lly.
-/
theorem helly_theorem_set' {F : Finset (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G ≤ finrank 𝕜 E + 1 → (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  classical -- for DecidableEq, required for the family version
  rw [show ⋂₀ F = ⋂ X ∈ F, (X : Set E) by ext; simp]
  apply helly_theorem' h_convex
  intro G hG_ss hG_card
  rw [show ⋂ X ∈ G, X = ⋂₀ G by ext; simp]
  exact h_inter G hG_ss hG_card

/-- **Helly's theorem** for finite sets of convex sets in its classical form.

If `F` is a finite set of convex sets in a vector space of finite dimension `d`, with `n ≥ d + 1`,
and any `d + 1` sets from `F` intersect nontrivially,
then all sets from `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_set** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_set {F : Finset (Set E)} (h_card : finrank 𝕜 E + 1 <= #F) (h
_convex : forall X in F, Convex 𝕜 X) (h_inter : forall G : Finset (Set E), G sub
seteq F -> #G = finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty) : (⋂₀ (F : Set (Set 
E))).Nonempty
参数：Set E；h_card : finrank 𝕜 E + 1 <= #F；h_convex : forall X in F, Convex 𝕜 X；h_i
nter : forall G : Finset (Set E), G subseteq F -> #G = finrank 𝕜 E + 1 -> (⋂₀ G 
: Set E).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.helly_theorem_set'`：helly_theorem_set' {F : Finset (Set E)} (h_co
nvex : forall X in F, Convex 𝕜 X) (h_inter : forall G : Finset (Set E), G subset
eq F -> #G <= f…
· 使用引理 `Finset.exists_subsuperset_card_eq`：exists_subsuperset_card_eq (hst : s s
ubseteq t) (hsn : #s <= n) (hnt : n <= #t) : exists u, s subseteq u ∧ u subseteq
 t ∧ #u = n
· 使用定理 `Set.sInter_mono`：∀ {α : Type u_1} {S T : Set (Set α)}, S ⊆ T → ⋂₀ T ⊆ ⋂₀
 S
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty

--- 原说明 ---
**Helly's theorem** for finite sets of convex sets in its classical form.

If `F` is a finite set of convex sets in a vector space of finite dimension `d`,
 with `n ≥ d + 1`,
and any `d + 1` sets from `F` intersect nontrivially,
then all sets from `F` intersect nontrivially.
-/
theorem helly_theorem_set {F : Finset (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ #F)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G = finrank 𝕜 E + 1 → (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  apply helly_theorem_set' h_convex
  intro I hI_ss hI_card
  obtain ⟨J, _, hJ_ss, hJ_card⟩ := exists_subsuperset_card_eq hI_ss hI_card h_card
  have : ⋂₀ (J : Set (Set E)) ⊆ ⋂₀ I := sInter_mono (by simpa [hI_ss])
  apply Set.Nonempty.mono this
  exact h_inter J hJ_ss (by lia)

/-- **Helly's theorem** for families of compact convex sets.

If `F` is a family of compact convex sets in a vector space of finite dimension `d`, and any
`k ≤ d + 1` sets of `F` intersect nontrivially, then all sets of `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_compact'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_compact' [TopologicalSpace E] [T2Space E] {F : ι -> Set E} (
h_convex : forall i, Convex 𝕜 (F i)) (h_compact : forall i, IsCompact (F i)) (h_
inter : forall I : Finset ι, #I <= finrank 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty) 
: (⋂ i, F i).Nonempty
参数：h_convex : forall i, Convex 𝕜 (F i)；h_compact : forall i, IsCompact (F i)；h_i
nter : forall I : Finset ι, #I <= finrank 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Convex.helly_theorem'`：helly_theorem' {F : ι -> Set E} {s : Finset ι} (h
_convex : forall i in s, Convex 𝕜 (F i)) (h_inter : forall I subseteq s, #I <= f
inrank 𝕜 E …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …

--- 原说明 ---
**Helly's theorem** for families of compact convex sets.

If `F` is a family of compact convex sets in a vector space of finite dimension 
`d`, and any
`k ≤ d + 1` sets of `F` intersect nontrivially, then all sets of `F` intersect n
ontrivially.
-/
theorem helly_theorem_compact' [TopologicalSpace E] [T2Space E] {F : ι → Set E}
    (h_convex : ∀ i, Convex 𝕜 (F i)) (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty := by
  classical
  /- If `ι` is empty the statement is trivial. -/
  rcases isEmpty_or_nonempty ι with _ | h_nonempty
  · simp only [iInter_of_empty, Set.univ_nonempty]
  /- By the finite version of theorem, every finite subfamily has an intersection. -/
  have h_fin (I : Finset ι) : (⋂ i ∈ I, F i).Nonempty := by
    apply helly_theorem' (s := I) (𝕜 := 𝕜) (by simp [h_convex])
    exact fun J _ hJ_card ↦ h_inter J hJ_card
  /- The following is a clumsy proof that family of compact sets with the finite intersection
  property has a nonempty intersection. -/
  have i0 : ι := Nonempty.some h_nonempty
  rw [show ⋂ i, F i = (F i0) ∩ ⋂ i, F i by simp [iInter_subset]]
  apply IsCompact.inter_iInter_nonempty
  · exact h_compact i0
  · intro i
    exact (h_compact i).isClosed
  · intro I
    simpa using h_fin ({i0} ∪ I)

/-- **Helly's theorem** for families of compact convex sets in its classical form.

If `F` is a (possibly infinite) family of more than `d + 1` compact convex sets in a vector space of
finite dimension `d`, and any `d + 1` sets of `F` intersect nontrivially,
then all sets of `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_compact** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_compact [TopologicalSpace E] [T2Space E] {F : ι -> Set E} (h
_card : finrank 𝕜 E + 1 <= ENat.card ι) (h_convex : forall i, Convex 𝕜 (F i)) (h
_compact : forall i, IsCompact (F i)) (h_inter : forall I : Finset ι, #I = finra
nk 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty) : (⋂ i, F i).Nonempty
参数：h_card : finrank 𝕜 E + 1 <= ENat.card ι；h_convex : forall i, Convex 𝕜 (F i)；h
_compact : forall i, IsCompact (F i)；h_inter : forall I : Finset ι, #I = finrank
 𝕜 E + 1 -> (⋂ i in I, F i).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.helly_theorem_compact'`：helly_theorem_compact' [TopologicalSpace 
E] [T2Space E] {F : ι -> Set E} (h_convex : forall i, Convex 𝕜 (F i)) (h_compact
 : forall i, IsComp…
· 使用定理 `Infinite.exists_superset_card_eq`：exists_superset_card_eq [Infinite α] (
s : Finset α) (n : Nat) (hn : #s <= n) : exists t : Finset α, s subseteq t ∧ #t 
= n
· 使用定理 `Finite.of_not_infinite`：∀ {α : Sort u_1}, ¬Infinite α → Finite α
· 使用引理 `Finset.exists_superset_card_eq`：Finset.exists_superset_card_eq [Fintype 
α] {n : Nat} {s : Finset α} (hsn : #s <= n) (hnα : n <= Fintype.card α) : exists
 t, s subseteq t ∧ #…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.biInter_mono`：biInter_mono {s s' : Set α} {t t' : α -> Set β} (hs : 
s subseteq s') (h : forall x in s, t x subseteq t' x) : ⋂ x in s', t x subseteq 
⋂ x in…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
**Helly's theorem** for families of compact convex sets in its classical form.

If `F` is a (possibly infinite) family of more than `d + 1` compact convex sets 
in a vector space of
finite dimension `d`, and any `d + 1` sets of `F` intersect nontrivially,
then all sets of `F` intersect nontrivially.
-/
theorem helly_theorem_compact [TopologicalSpace E] [T2Space E] {F : ι → Set E}
    (h_card : finrank 𝕜 E + 1 ≤ ENat.card ι)
    (h_convex : ∀ i, Convex 𝕜 (F i)) (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty := by
  apply helly_theorem_compact' h_convex h_compact
  intro I hI_card
  have hJ : ∃ J : Finset ι, I ⊆ J ∧ #J = finrank 𝕜 E + 1 := by
    by_cases h : Infinite ι
    · exact Infinite.exists_superset_card_eq _ _ hI_card
    · have : Finite ι := Finite.of_not_infinite h
      have : Fintype ι := Fintype.ofFinite ι
      apply exists_superset_card_eq hI_card
      simp only [ENat.card_eq_coe_fintype_card] at h_card
      rwa [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at h_card
  obtain ⟨J, hJ_ss, hJ_card⟩ := hJ
  apply Set.Nonempty.mono <| biInter_mono hJ_ss (by intro _ _; rfl)
  exact h_inter J hJ_card

/-- **Helly's theorem** for sets of compact convex sets.

If `F` is a set of compact convex sets in a vector space of finite dimension `d`, and any
`k ≤ d + 1` sets from `F` intersect nontrivially, then all sets from `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_set_compact'** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_set_compact' [TopologicalSpace E] [T2Space E] {F : Set (Set 
E)} (h_convex : forall X in F, Convex 𝕜 X) (h_compact : forall X in F, IsCompact
 X) (h_inter : forall G : Finset (Set E), (G : Set (Set E)) subseteq F -> #G <= 
finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty) : (⋂₀ (F : Set (Set E))).Nonempty
参数：Set E；h_convex : forall X in F, Convex 𝕜 X；h_compact : forall X in F, IsCompa
ct X；h_inter : forall G : Finset (Set E), (G : Set (Set E)) subseteq F -> #G <= 
finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Convex.helly_theorem_compact'`：helly_theorem_compact' [TopologicalSpace 
E] [T2Space E] {F : ι -> Set E} (h_convex : forall i, Convex 𝕜 (F i)) (h_compact
 : forall i, IsComp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s

--- 原说明 ---
**Helly's theorem** for sets of compact convex sets.

If `F` is a set of compact convex sets in a vector space of finite dimension `d`
, and any
`k ≤ d + 1` sets from `F` intersect nontrivially, then all sets from `F` interse
ct nontrivially.
-/
theorem helly_theorem_set_compact' [TopologicalSpace E] [T2Space E] {F : Set (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X) (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G ≤ finrank 𝕜 E + 1 →
    (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  classical -- for DecidableEq, required for the family version
  rw [show ⋂₀ F = ⋂ X : F, (X : Set E) by ext; simp]
  refine helly_theorem_compact' (F := fun x : F ↦ x.val)
    (fun X ↦ h_convex X (by simp)) (fun X ↦ h_compact X (by simp)) ?_
  intro G _
  let G' : Finset (Set E) := image Subtype.val G
  rw [show ⋂ i ∈ G, ↑i = ⋂₀ (G' : Set (Set E)) by simp [G']]
  apply h_inter G'
  · simp [G']
  · apply le_trans card_image_le
    assumption

/-- **Helly's theorem** for sets of compact convex sets in its classical version.

If `F` is a (possibly infinite) set of more than `d + 1` compact convex sets in a vector space of
finite dimension `d`, and any `d + 1` sets from `F` intersect nontrivially,
then all sets from `F` intersect nontrivially. -/
/-
**Convex.helly_theorem_set_compact** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：helly_theorem_set_compact [TopologicalSpace E] [T2Space E] {F : Set (Set E
)} (h_card : finrank 𝕜 E + 1 <= F.encard) (h_convex : forall X in F, Convex 𝕜 X)
 (h_compact : forall X in F, IsCompact X) (h_inter : forall G : Finset (Set E), 
(G : Set (Set E)) subseteq F -> #G = finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty)
 : (⋂₀ (F : Set (Set E))).Nonempty
参数：Set E；h_card : finrank 𝕜 E + 1 <= F.encard；h_convex : forall X in F, Convex 𝕜
 X；h_compact : forall X in F, IsCompact X；h_inter : forall G : Finset (Set E), (
G : Set (Set E)) subseteq F -> #G = finrank 𝕜 E + 1 -> (⋂₀ G : Set E).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.helly_theorem_set_compact'`：helly_theorem_set_compact' [Topologic
alSpace E] [T2Space E] {F : Set (Set E)} (h_convex : forall X in F, Convex 𝕜 X) 
(h_compact : forall X i…
· 使用定理 `Set.exists_superset_subset_encard_eq`：exists_superset_subset_encard_eq {
k : Nat∞} (hst : s subseteq t) (hsk : s.encard <= k) (hkt : k <= t.encard) : exi
sts r, s subseteq r ∧ r su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.encard_coe_eq_coe_finsetCard`：∀ {α : Type u_1} (s : Finset α), (↑s).
encard = ↑s.card
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.sInter_mono`：∀ {α : Type u_1} {S T : Set (Set α)}, S ⊆ T → ⋂₀ T ⊆ ⋂₀
 S
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用定理 `Set.encard_eq_coe_toFinset_card`：encard_eq_coe_toFinset_card (s : Set α)
 [Fintype s] : encard s = s.toFinset.card

--- 原说明 ---
**Helly's theorem** for sets of compact convex sets in its classical version.

If `F` is a (possibly infinite) set of more than `d + 1` compact convex sets in 
a vector space of
finite dimension `d`, and any `d + 1` sets from `F` intersect nontrivially,
then all sets from `F` intersect nontrivially.
-/
theorem helly_theorem_set_compact [TopologicalSpace E] [T2Space E] {F : Set (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ F.encard)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X) (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G = finrank 𝕜 E + 1 →
    (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  apply helly_theorem_set_compact' h_convex h_compact
  intro I hI_ss hI_card
  obtain ⟨J, _, hJ_ss, hJ_card⟩ := exists_superset_subset_encard_eq hI_ss (by norm_cast) h_card
  apply Set.Nonempty.mono <| sInter_mono (by simpa [hI_ss])
  have hJ_fin : Fintype J := Finite.fintype <| finite_of_encard_eq_coe hJ_card
  let J' := J.toFinset
  rw [← coe_toFinset J]
  apply h_inter J'
  · simpa [J']
  · rwa [encard_eq_coe_toFinset_card J, ← ENat.natCast_one, ← ENat.natCast_add, Nat.cast_inj]
      at hJ_card

end Convex

