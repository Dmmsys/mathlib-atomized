/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Simplices in normed affine spaces

We prove the following facts:

* `exists_mem_interior_convexHull_affineBasis` : We can intercalate a simplex between a point and
  one of its neighborhoods.
* `Convex.exists_subset_interior_convexHull_finset_of_isCompact`: We can intercalate a convex
  polytope between a compact convex set and one of its neighborhoods.
-/

public section

variable {E P : Type*}

open AffineBasis Module Metric Set
open scoped Convex Pointwise Topology

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P] [NormedAddTorsor E P]
variable {s : Set E}

/-
**Wbtw.dist_add_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.dist_add_dist {x y z : P} (h : Wbtw Real x y z) : dist x y + dist y z
 = dist x z
参数：h : Wbtw Real x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_left_lineMap`：dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (line
Map p₁ p₂ c) = ‖c‖ * dist p₁ p₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_lineMap_right`：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineM
ap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Wbtw.dist_add_dist {x y z : P} (h : Wbtw ℝ x y z) :
    dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha₀, ha₁⟩, rfl⟩ := h
  simp [abs_of_nonneg, ha₀, ha₁, sub_mul]
/-
**dist_add_dist_of_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_add_dist_of_mem_segment {x y z : E} (h : y in [x -[Real] z]) : dist x
 y + dist y z = dist x z
参数：h : y in [x -[Real] z]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.dist_add_dist`：Wbtw.dist_add_dist {x y z : P} (h : Wbtw Real x y z)
 : dist x y + dist y z = dist x z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_segment_iff_wbtw`：mem_segment_iff_wbtw {x y z : V} : y in segment R 
x z ↔ Wbtw R x y z
-/
theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
    dist x y + dist y z = dist x z :=
  (mem_segment_iff_wbtw.1 h).dist_add_dist

end SeminormedAddCommGroup

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s t : Set E} {x : E}

/-- We can intercalate a simplex between a point and one of its neighborhoods. -/
/-
**exists_mem_interior_convexHull_affineBasis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_mem_interior_convexHull_affineBasis (hs : s in 𝓝 x) : exists b : Af
fineBasis (Fin (finrank Real E + 1)) Real E, x in interior (convexHull Real (ran
ge b)) ∧ convexHull Real (range b) subseteq s
参数：hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AffineBasis.exists_affineBasis_of_finiteDimensional`：exists_affineBasis_
of_finiteDimensional [Fintype ι] [FiniteDimensional k V] (h : Fintype.card ι = M
odule.finrank k V + 1) : Nonempty (Affine…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centroid_eq_centerMass`：Finset.centroid_eq_centerMass (s : Finset
 ι) (hs : s.Nonempty) (p : ι -> E) : s.centroid R p = s.centerMass (s.centroidWe
ights R) p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.range_add`：∀ {α : Type u_2} [inst : Add α] {ι : Sort u_7} (a : α) (f
 : ι → α), (Set.range fun i => a + f i) = a +ᵥ Set.range f
· 使用引理 `convexHull_vadd`：convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +
ᵥ s) = x +ᵥ convexHull 𝕜 s
· 使用定理 `interior_vadd`：∀ {α : Type u_2} {G : Type u_4} [inst : TopologicalSpace 
α] [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [ContinuousConstVAdd G α] (c
 : …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AffineBasis.centroid_mem_interior_convexHull`：AffineBasis.centroid_mem_i
nterior_convexHull {ι} [Fintype ι] (b : AffineBasis ι Real V) : Finset.univ.cent
roid Real b in interior (convexHul…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 125 条，此处仅展示前 30 条）

--- 原说明 ---
We can intercalate a simplex between a point and one of its neighborhoods.
-/
lemma exists_mem_interior_convexHull_affineBasis (hs : s ∈ 𝓝 x) :
    ∃ b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E,
      x ∈ interior (convexHull ℝ (range b)) ∧ convexHull ℝ (range b) ⊆ s := by
  -- By translating, WLOG `x` is the origin.
  wlog hx : x = 0
  · obtain ⟨b, hb⟩ := this (s := -x +ᵥ s) (by simpa using vadd_mem_nhds_vadd (-x) hs) rfl
    use x +ᵥ b
    simpa [subset_vadd_set_iff, mem_vadd_set_iff_neg_vadd_mem, convexHull_vadd, interior_vadd,
      Pi.vadd_def, -vadd_eq_add, vadd_eq_add (a := -x), ← Set.vadd_set_range] using hb
  subst hx
  -- The strategy is now to find an arbitrary maximal spanning simplex (aka an affine basis)...
  obtain ⟨b⟩ := exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  -- ... translate it to contain the origin...
  set c : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := -Finset.univ.centroid ℝ b +ᵥ b
  have hc₀ : 0 ∈ interior (convexHull ℝ (range c) : Set E) := by
    simpa [c, convexHull_vadd, interior_vadd, range_add, Pi.vadd_def, mem_vadd_set_iff_neg_vadd_mem]
      using b.centroid_mem_interior_convexHull
  set cnorm := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖c i‖)
  have hcnorm : range c ⊆ closedBall 0 (cnorm + 1) := by
    simpa only [cnorm, subset_def, Finset.mem_coe, mem_closedBall, dist_zero_right,
      ← sub_le_iff_le_add, Finset.le_sup'_iff, forall_mem_range] using fun i ↦ ⟨i, by simp⟩
  -- ... and finally scale it to fit inside the neighborhood `s`.
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  set ε' : ℝ := ε / 2 / (cnorm + 1)
  have hc' : 0 < cnorm + 1 := by
    have : 0 ≤ cnorm := Finset.le_sup'_of_le _ (Finset.mem_univ 0) (norm_nonneg _)
    positivity
  have hε' : 0 < ε' := by positivity
  set d : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := Units.mk0 ε' hε'.ne' • c
  have hε₀ : 0 < ε / 2 := by positivity
  have hdnorm : (range d : Set E) ⊆ closedBall 0 (ε / 2) := by
    simp [d, abs_of_nonneg hε'.le, range_subset_iff, norm_smul]
    simpa [ε', hε₀.ne', range_subset_iff, ← mul_div_right_comm (ε / 2), div_le_iff₀ hc', hε₀]
      using hcnorm
  refine ⟨d, ?_, ?_⟩
  · simpa [d, Pi.smul_def, range_smul, interior_smul₀, convexHull_smul, zero_mem_smul_set_iff,
      hε'.ne']
  · calc
      convexHull ℝ (range d) ⊆ closedBall 0 (ε / 2) := convexHull_min hdnorm (convex_closedBall ..)
      _ ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
      _ ⊆ s := hεs

/-- We can intercalate a convex polytope between a compact convex set and one of its neighborhoods.
-/
/-
**Convex.exists_subset_interior_convexHull_finset_of_isCompact** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：Convex.exists_subset_interior_convexHull_finset_of_isCompact (hs₁ : Convex
 Real s) (hs₂ : IsCompact s) (ht : t in 𝓝ˢ s) : exists u : Finset E, s subseteq 
interior (convexHull Real u) ∧ convexHull Real u subseteq t
参数：hs₁ : Convex Real s；hs₂ : IsCompact s；ht : t in 𝓝ˢ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
· 使用定理 `compact_open_separated_add_left`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddZeroClass G] [ContinuousAdd G] {K U : Set G},   IsCompact K → I
sOpen U → K ⊆ U → ∃ V…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `exists_mem_interior_convexHull_affineBasis`：exists_mem_interior_convexHu
ll_affineBasis (hs : s in 𝓝 x) : exists b : AffineBasis (Fin (finrank Real E + 1
)) Real E, x in interior (convex…
· 使用定理 `IsCompact.elim_finite_subcover_image`：IsCompact.elim_finite_subcover_ima
ge {b : Set ι} {c : ι -> Set X} (hs : IsCompact s) (hc₁ : forall i in b, IsOpen 
(c i)) (hc₂ : s subseteq ⋃…
· 使用定理 `IsOpen.add_right`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : A
ddGroup α] [ContinuousConstVAdd αᵃᵒᵖ α] {s t : Set α},   IsOpen s → IsOpen (s + 
t)
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd_op`：∀ {M : Type u_3} [inst : T
opologicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConst
VAdd Mᵃᵒᵖ M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Finset.coe_add`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Add α]
 (s t : Finset α), ↑(s + t) = ↑s + ↑t
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `convexHull_add`：convexHull_add (s t : Set E) : convexHull R (s + t) = co
nvexHull R s + convexHull R t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `subset_interior_add_left`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : AddGroup α] [ContinuousConstVAdd αᵃᵒᵖ α] {s t : Set α},   interior s + t 
⊆ interior (s …
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
We can intercalate a convex polytope between a compact convex set and one of its
 neighborhoods.
-/
theorem Convex.exists_subset_interior_convexHull_finset_of_isCompact
    (hs₁ : Convex ℝ s) (hs₂ : IsCompact s) (ht : t ∈ 𝓝ˢ s) :
    ∃ u : Finset E, s ⊆ interior (convexHull ℝ u) ∧ convexHull ℝ u ⊆ t := by
  classical
  rcases mem_nhdsSet_iff_exists.1 ht with ⟨U, hU₁, hU₂, hU₃⟩
  rcases compact_open_separated_add_left hs₂ hU₁ hU₂ with ⟨V, hV₁, hV₂⟩
  rcases exists_mem_interior_convexHull_affineBasis hV₁ with ⟨b, hb₁, hb₂⟩
  rcases hs₂.elim_finite_subcover_image (b := s)
      (c := fun x => interior (convexHull ℝ (Set.range b)) + {x})
      (fun _ _ => isOpen_interior.add_right)
      (fun x hx => Set.mem_iUnion₂_of_mem hx <| by simpa using hb₁)
    with ⟨u, hu₁, hu₂, hu₃⟩
  lift u to Finset E using hu₂
  refine ⟨Finset.univ.image b + u, ?_, ?_⟩
  all_goals rw [Finset.coe_add, Finset.coe_image, Finset.coe_univ, Set.image_univ, convexHull_add]
  · grw [hu₃, ← subset_interior_add_left, Set.iUnion₂_subset_iff, ← subset_convexHull _ (u : Set E)]
    intros
    gcongr
    simpa
  · grw [hu₁, hs₁.convexHull_eq, hb₂, hV₂, hU₃]

end NormedAddCommGroup

