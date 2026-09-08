/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Join

/-!
# Stone's separation theorem

This file proves Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

In locally convex real topological vector spaces, the Hahn-Banach separation theorems provide
stronger statements: one may find a separating hyperplane, instead of merely a convex set whose
complement is convex.
-/

public section


open Set

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/-- In a tetrahedron with vertices `x`, `y`, `p`, `q`, any segment `[u, v]` joining the opposite
edges `[x, p]` and `[y, q]` passes through any triangle of vertices `p`, `q`, `z` where
`z ∈ [x, y]`. -/
/-
**not_disjoint_segment_convexHull_triple** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_disjoint_segment_convexHull_triple {p q u v x y z : E} (hz : z in segm
ent 𝕜 x y) (hu : u in segment 𝕜 x p) (hv : v in segment 𝕜 y q) : ¬Disjoint (segm
ent 𝕜 u v) (convexHull 𝕜 {p, q, z})
参数：hz : z in segment 𝕜 x y；hu : u in segment 𝕜 x p；hv : v in segment 𝕜 y q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `right_mem_segment`：right_mem_segment (x y : E) : y in [x -[𝕜] y]
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `segment_subset_convexHull`：segment_subset_convexHull (hx : x in s) (hy :
 y in s) : segment 𝕜 x y subseteq convexHull 𝕜 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 112 条，此处仅展示前 30 条）

--- 原说明 ---
In a tetrahedron with vertices `x`, `y`, `p`, `q`, any segment `[u, v]` joining 
the opposite
edges `[x, p]` and `[y, q]` passes through any triangle of vertices `p`, `q`, `z
` where
`z ∈ [x, y]`.
-/
theorem not_disjoint_segment_convexHull_triple {p q u v x y z : E} (hz : z ∈ segment 𝕜 x y)
    (hu : u ∈ segment 𝕜 x p) (hv : v ∈ segment 𝕜 y q) :
    ¬Disjoint (segment 𝕜 u v) (convexHull 𝕜 {p, q, z}) := by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz
    rw [zero_smul, zero_add, habz, one_smul]
    refine ⟨v, by apply right_mem_segment, segment_subset_convexHull ?_ ?_ hv⟩ <;> simp
  obtain ⟨av, bv, hav, hbv, habv, rfl⟩ := hv
  obtain rfl | hav' := hav.eq_or_lt
  · rw [zero_add] at habv
    rw [zero_smul, zero_add, habv, one_smul]
    exact ⟨q, right_mem_segment _ _ _, subset_convexHull _ _ <| by simp⟩
  obtain ⟨au, bu, hau, hbu, habu, rfl⟩ := hu
  have hab : 0 < az * av + bz * au := by positivity
  refine ⟨(az * av / (az * av + bz * au)) • (au • x + bu • p) +
    (bz * au / (az * av + bz * au)) • (av • y + bv • q), ⟨_, _, ?_, ?_, ?_, rfl⟩, ?_⟩
  · positivity
  · positivity
  · rw [← add_div, div_self]; positivity
  classical
    let w : Fin 3 → 𝕜 := ![az * av * bu, bz * au * bv, au * av]
    let z : Fin 3 → E := ![p, q, az • x + bz • y]
    have hw₀ : ∀ i, 0 ≤ w i := by
      rintro i
      fin_cases i
      · exact mul_nonneg (mul_nonneg haz hav) hbu
      · exact mul_nonneg (mul_nonneg hbz hau) hbv
      · exact mul_nonneg hau hav
    have hw : ∑ i, w i = az * av + bz * au := by
      trans az * av * bu + (bz * au * bv + au * av)
      · simp [w, Fin.sum_univ_succ]
      linear_combination (au * bv - 1 * au) * habz + (-(1 * az * au) + au) * habv + az * av * habu
    have hz : ∀ i, z i ∈ ({p, q, az • x + bz • y} : Set E) := fun i => by fin_cases i <;> simp [z]
    convert!
      (Finset.centerMass_mem_convexHull (Finset.univ : Finset (Fin 3)) (fun i _ => hw₀ i)
          (by rwa [hw]) fun i _ => hz i :
        Finset.univ.centerMass w z ∈ _)
    rw [Finset.centerMass, hw]
    trans (az * av + bz * au)⁻¹ •
      ((az * av * bu) • p + ((bz * au * bv) • q + (au * av) • (az • x + bz • y)))
    · module
    congr 3
    simp [w, z]

/-- **Stone's Separation Theorem** -/
/-
**exists_convex_convex_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_convex_convex_compl_subset (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst
 : Disjoint s t) : exists C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s subseteq C ∧ t
 subseteq Cᶜ
参数：hs : Convex 𝕜 s；ht : Convex 𝕜 t；hst : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `DirectedOn.convex_sUnion`：DirectedOn.convex_sUnion {c : Set (Set E)} (hd
ir : DirectedOn (· subseteq ·) c) (hc : forall ⦃A : Set E⦄, A in c -> Convex 𝕜 A
) : Convex 𝕜 (…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_sUnion_left`：disjoint_sUnion_left {S : Set (Set α)} {t : Se
t α} : Disjoint (⋃₀ S) t ↔ forall s in S, Disjoint s t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_insert`：convexHull_insert (hs : s.Nonempty) : convexHull 𝕜 (i
nsert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s)
· 使用定理 `convexJoin_singleton_left`：convexJoin_singleton_left (t : Set E) (x : E)
 : convexJoin 𝕜 {x} t = ⋃ y in t, segment 𝕜 x y
· 使用定理 `Set.disjoint_iUnion₂_left`：disjoint_iUnion₂_left {s : forall i, κ i -> S
et α} {t : Set α} : Disjoint (⋃ (i) (j), s i j) t ↔ forall i j, Disjoint (s i j)
 t
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `not_disjoint_segment_convexHull_triple`：not_disjoint_segment_convexHull_
triple {p q u v x y z : E} (hz : z in segment 𝕜 x y) (hu : u in segment 𝕜 x p) (
hv : v in segment 𝕜 y q) : ¬…
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
**Stone's Separation Theorem**
-/
theorem exists_convex_convex_compl_subset (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ := by
  let S : Set (Set E) := { C | Convex 𝕜 C ∧ Disjoint C t }
  obtain ⟨C, hsC, hmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨_, _⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directedOn.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s => subset_sUnion_of_mem⟩)
      s ⟨hs, hst⟩
  obtain hC : _ ∧ _ := hmax.prop
  refine
    ⟨C, hC.1, convex_iff_segment_subset.2 fun x hx y hy z hz hzC => ?_, hsC, hC.2.subset_compl_left⟩
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).Nonempty by
    obtain ⟨p, hp, u, hu, hut⟩ := h x hx
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy
    refine
      not_disjoint_segment_convexHull_triple hz hu hv
        (hC.2.symm.mono (ht.segment_subset hut hvt) <| convexHull_min ?_ hC.1)
    simp [insert_subset_iff, hp, hq, singleton_subset_iff.2 hzC]
  rintro c hc
  by_contra! h
  suffices h : Disjoint (convexHull 𝕜 (insert c C)) t by
    rw [hmax.eq_of_subset ⟨convex_convexHull _ _, h⟩ <|
      (subset_insert ..).trans <| subset_convexHull ..] at hc
    exact hc (subset_convexHull _ _ <| mem_insert _ _)
  rw [convexHull_insert ⟨z, hzC⟩, convexJoin_singleton_left]
  refine disjoint_iUnion₂_left.2 fun a ha => disjoint_iff_inter_eq_empty.2 (h a ?_)
  rwa [← hC.1.convexHull_eq]
