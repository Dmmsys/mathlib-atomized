/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

* `continuous_barycentric_coord`
* `isOpenMap_barycentric_coord`
* `AffineBasis.interior_convexHull`
* `IsOpen.exists_subset_affineIndependent_span_eq_top`
* `interior_convexHull_nonempty_iff_affineSpan_eq_top`
-/

public section

assert_not_exists HasFDerivAt

section Barycentric

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]

/-
**isOpenMap_barycentric_coord** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_barycentric_coord [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι)
 : IsOpenMap (b.coord i)
参数：b : AffineBasis ι 𝕜 P；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineMap.isOpenMap_linear_iff`：isOpenMap_linear_iff {f : P ->ᵃ[R] Q} : 
IsOpenMap f.linear ↔ IsOpenMap f
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `LinearMap.isOpenMap_of_finiteDimensional`：isOpenMap_of_finiteDimensional
 (f : F ->ₗ[𝕜] E) (hf : Function.Surjective f) : IsOpenMap f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineMap.linear_surjective_iff`：linear_surjective_iff (f : P1 ->ᵃ[k] P2
) : Function.Surjective f.linear ↔ Function.Surjective f
· 使用定理 `AffineBasis.surjective_coord`：surjective_coord [Nontrivial ι] (i : ι) : 
Function.Surjective b.coord i
-/
theorem isOpenMap_barycentric_coord [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι) :
    IsOpenMap (b.coord i) :=
  AffineMap.isOpenMap_linear_iff.mp <|
    (b.coord i).linear.isOpenMap_of_finiteDimensional <|
      (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

variable [FiniteDimensional 𝕜 E] (b : AffineBasis ι 𝕜 P)

@[continuity]
/-
**continuous_barycentric_coord** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_barycentric_coord (i : ι) : Continuous (b.coord i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.continuous_of_finiteDimensional`：AffineMap.continuous_of_finit
eDimensional (f : PE ->ᵃ[𝕜] PF) : Continuous f
-/
theorem continuous_barycentric_coord (i : ι) : Continuous (b.coord i) :=
  (b.coord i).continuous_of_finiteDimensional

end Barycentric

open Set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
/-
**AffineBasis.interior_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineBasis.interior_convexHull {ι E : Type*} [Finite ι] [NormedAddCommGro
up E] [NormedSpace Real E] (b : AffineBasis ι Real E) : interior (convexHull Rea
l (range b)) = {x | forall i, 0 < b.coord i x}
参数：b : AffineBasis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `AffineSubspace.eq_univ_of_subsingleton_span_eq_top`：eq_univ_of_subsingle
ton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ : affineSpan k s = ⊤) : s 
= (univ : Set P)
· 使用定理 `Set.subsingleton_range`：subsingleton_range {α : Sort*} [Subsingleton α] 
(f : α -> β) : (range f).Subsingleton
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_univ`：convexHull_univ : convexHull 𝕜 (univ : Set E) = univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineBasis.coe_coord_of_subsingleton_eq_one`：coe_coord_of_subsingleton_
eq_one [Subsingleton ι] (i : ι) : (b.coord i : P -> k) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineBasis.finiteDimensional`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u
₃} {P : Type u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Di
visionRing k] [inst…
· 使用定理 `AffineBasis.convexHull_eq_nonneg_coord`：AffineBasis.convexHull_eq_nonneg
_coord {ι : Type*} (b : AffineBasis ι R E) : convexHull R (range b) = { x | fora
ll i, 0 <= b.coord i x }
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_iInter_of_finite`：interior_iInter_of_finite [Finite ι] (f : ι -
> Set X) : interior (⋂ i, f i) = ⋂ i, interior (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `isOpenMap_barycentric_coord`：isOpenMap_barycentric_coord [Nontrivial ι] 
(b : AffineBasis ι 𝕜 P) (i : ι) : IsOpenMap (b.coord i)
· 使用定理 `continuous_barycentric_coord`：continuous_barycentric_coord (i : ι) : Con
tinuous (b.coord i)
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Given a finite-dimensional normed real vector space, the interior of the convex 
hull of an
affine basis is the set of points whose barycentric coordinates are strictly pos
itive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the d
efinition of
convexity is generalised to this setting.
-/
theorem AffineBasis.interior_convexHull {ι E : Type*} [Finite ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : AffineBasis ι ℝ E) :
    interior (convexHull ℝ (range b)) = {x | ∀ i, 0 < b.coord i x} := by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    have : range b = univ :=
      AffineSubspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot
    simp [this]
  · -- The positive-dimensional case.
    have : FiniteDimensional ℝ E := b.finiteDimensional
    have : convexHull ℝ (range b) = ⋂ i, b.coord i ⁻¹' Ici 0 := by
      rw [b.convexHull_eq_nonneg_coord, ofPred_forall]; rfl
    ext
    simp only [this, interior_iInter_of_finite, ←
      IsOpenMap.preimage_interior_eq_interior_preimage (isOpenMap_barycentric_coord b _)
        (continuous_barycentric_coord b _),
      interior_Ici, mem_iInter, mem_ofPred_eq, mem_Ioi, mem_preimage]

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
/-
**IsOpen.exists_between_affineIndependent_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：IsOpen.exists_between_affineIndependent_span_eq_top {s u : Set P} (hu : Is
Open u) (hsu : s subseteq u) (hne : s.Nonempty) (h : AffineIndependent Real ((↑)
 : s -> P)) : exists t : Set P, s subseteq t ∧ t subseteq u ∧ AffineIndependent 
Real ((↑) : t -> P) ∧ affineSpan Real t = ⊤
参数：hu : IsOpen u；hsu : s subseteq u；hne : s.Nonempty；h : AffineIndependent Real 
((↑) : s -> P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `exists_subset_affineIndependent_affineSpan_eq_top`：exists_subset_affineI
ndependent_affineSpan_eq_top {s : Set P} (h : AffineIndependent k (fun p => p : 
s -> P)) : exists t : Set P, s subseteq…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_self_le_one`：div_self_le_one (a : G₀) : a / a <= 1
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Given a set `s` of affine-independent points belonging to an open set `u`, we ma
y extend `s` to
an affine basis, all of whose elements belong to `u`.
-/
theorem IsOpen.exists_between_affineIndependent_span_eq_top {s u : Set P} (hu : IsOpen u)
    (hsu : s ⊆ u) (hne : s.Nonempty) (h : AffineIndependent ℝ ((↑) : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent ℝ ((↑) : t → P) ∧ affineSpan ℝ t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, ε0, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds <| hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affineIndependent_affineSpan_eq_top h
  let f : P → P := fun y => lineMap q y (ε / dist y q)
  have hf : ∀ y, f y ∈ u := by
    refine fun y => hεu ?_
    simp only [f]
    rw [Metric.mem_closedBall, lineMap_apply, dist_vadd_left, norm_smul, Real.norm_eq_abs,
      dist_eq_norm_vsub V y q, abs_div, abs_of_pos ε0, abs_of_nonneg (norm_nonneg _), div_mul_comm]
    exact mul_le_of_le_one_left ε0.le (div_self_le_one _)
  have hεyq : ∀ y ∉ s, ε / dist y q ≠ 0 := fun y hy =>
    div_ne_zero ε0.ne' (dist_ne_zero.2 (ne_of_mem_of_not_mem hq hy).symm)
  classical
  let w : t → ℝˣ := fun p => if hp : (p : P) ∈ s then 1 else Units.mk0 _ (hεyq (↑p) hp)
  refine ⟨Set.range fun p : t => lineMap q p (w p : ℝ), ?_, ?_, ?_, ?_⟩
  · intro p hp; use ⟨p, ht₁ hp⟩; simp [w, hp]
  · rintro y ⟨⟨p, hp⟩, rfl⟩
    by_cases hps : p ∈ s <;>
    simp only [w, hps, lineMap_apply_one, Units.val_mk0, dif_neg, dif_pos, not_false_iff,
      Units.val_one] <;>
    [exact hsu hps; exact hf p]
  · exact (ht₂.units_lineMap ⟨q, ht₁ hq⟩ w).range
  · rw [affineSpan_eq_affineSpan_lineMap_units (ht₁ hq) w, ht₃]
/-
**IsOpen.exists_subset_affineIndependent_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsOpen.exists_subset_affineIndependent_span_eq_top {u : Set P} (hu : IsOpe
n u) (hne : u.Nonempty) : exists s subseteq u, AffineIndependent Real ((↑) : s -
> P) ∧ affineSpan Real s = ⊤
参数：hu : IsOpen u；hne : u.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.exists_between_affineIndependent_span_eq_top`：IsOpen.exists_betwe
en_affineIndependent_span_eq_top {s u : Set P} (hu : IsOpen u) (hsu : s subseteq
 u) (hne : s.Nonempty) (h : AffineIndepen…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `affineIndependent_of_subsingleton`：affineIndependent_of_subsingleton [Su
bsingleton ι] (p : ι -> P) : AffineIndependent k p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem IsOpen.exists_subset_affineIndependent_span_eq_top {u : Set P} (hu : IsOpen u)
    (hne : u.Nonempty) : ∃ s ⊆ u, AffineIndependent ℝ ((↑) : s → P) ∧ affineSpan ℝ s = ⊤ := by
  rcases hne with ⟨x, hx⟩
  rcases hu.exists_between_affineIndependent_span_eq_top (singleton_subset_iff.mpr hx)
    (singleton_nonempty _) (affineIndependent_of_subsingleton _ _) with ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩

/-- The affine span of a nonempty open set is `⊤`. -/
/-
**IsOpen.affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.affineSpan_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) : 
affineSpan Real u = ⊤
参数：hu : IsOpen u；hne : u.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.exists_subset_affineIndependent_span_eq_top`：IsOpen.exists_subset
_affineIndependent_span_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) : 
exists s subseteq u, AffineIndependent R…
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂

--- 原说明 ---
The affine span of a nonempty open set is `⊤`.
-/
theorem IsOpen.affineSpan_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) :
    affineSpan ℝ u = ⊤ :=
  let ⟨_, hsu, _, hs'⟩ := hu.exists_subset_affineIndependent_span_eq_top hne
  top_unique <| hs' ▸ affineSpan_mono _ hsu
/-
**affineSpan_eq_top_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_eq_top_of_nonempty_interior {s : Set V} (hs : (interior <| conv
exHull Real s).Nonempty) : affineSpan Real s = ⊤
参数：hs : (interior <| convexHull Real s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `affineSpan_convexHull`：affineSpan_convexHull (s : Set E) : affineSpan 𝕜 
(convexHull 𝕜 s) = affineSpan 𝕜 s
· 使用定理 `IsOpen.affineSpan_eq_top`：IsOpen.affineSpan_eq_top {u : Set P} (hu : IsO
pen u) (hne : u.Nonempty) : affineSpan Real u = ⊤
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem affineSpan_eq_top_of_nonempty_interior {s : Set V}
    (hs : (interior <| convexHull ℝ s).Nonempty) : affineSpan ℝ s = ⊤ :=
  top_unique <| isOpen_interior.affineSpan_eq_top hs ▸
    (affineSpan_mono _ interior_subset).trans_eq (affineSpan_convexHull _)
/-
**AffineBasis.centroid_mem_interior_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineBasis.centroid_mem_interior_convexHull {ι} [Fintype ι] (b : AffineBa
sis ι Real V) : Finset.univ.centroid Real b in interior (convexHull Real (range 
b))
参数：b : AffineBasis ι Real V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.nonempty`：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P 
: Type u_7} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k]
 [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineBasis.interior_convexHull`：AffineBasis.interior_convexHull {ι E : 
Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace Real E] (b : AffineBasis ι
 Real E) : interior (…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AffineBasis.coord_apply_centroid`：coord_apply_centroid [CharZero k] (b :
 AffineBasis ι k P) {s : Finset ι} {i : ι} (hi : i in s) : b.coord i (s.centroid
 k b) = (s.card : k)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem AffineBasis.centroid_mem_interior_convexHull {ι} [Fintype ι] (b : AffineBasis ι ℝ V) :
    Finset.univ.centroid ℝ b ∈ interior (convexHull ℝ (range b)) := by
  have := b.nonempty
  simp only [b.interior_convexHull, mem_ofPred_eq, b.coord_apply_centroid (Finset.mem_univ _),
    inv_pos, Nat.cast_pos, Finset.card_pos, Finset.univ_nonempty, forall_true_iff]
/-
**interior_convexHull_nonempty_iff_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：interior_convexHull_nonempty_iff_affineSpan_eq_top [FiniteDimensional Real
 V] {s : Set V} : (interior (convexHull Real s)).Nonempty ↔ affineSpan Real s = 
⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_eq_top_of_nonempty_interior`：affineSpan_eq_top_of_nonempty_in
terior {s : Set V} (hs : (interior <| convexHull Real s).Nonempty) : affineSpan 
Real s = ⊤
· 使用定理 `AffineBasis.exists_affine_subbasis`：exists_affine_subbasis {t : Set P} (
ht : affineSpan k t = ⊤) : exists s subseteq t, exists b : AffineBasis s k P, ⇑b
 = ((↑) : s -> P)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `AffineBasis.finite_set`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P :
 Type u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : DivisionR
ing k] [inst…
· 使用定理 `AffineBasis.centroid_mem_interior_convexHull`：AffineBasis.centroid_mem_i
nterior_convexHull {ι} [Fintype ι] (b : AffineBasis ι Real V) : Finset.univ.cent
roid Real b in interior (convexHul…
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem interior_convexHull_nonempty_iff_affineSpan_eq_top [FiniteDimensional ℝ V] {s : Set V} :
    (interior (convexHull ℝ s)).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  refine ⟨affineSpan_eq_top_of_nonempty_interior, fun h => ?_⟩
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
  suffices (interior (convexHull ℝ (range b))).Nonempty by
    rw [hb, Subtype.range_coe_subtype, ofPred_mem_eq] at this
    refine this.mono (by gcongr)
  lift t to Finset V using b.finite_set
  exact ⟨_, b.centroid_mem_interior_convexHull⟩
/-
**Convex.interior_nonempty_iff_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.interior_nonempty_iff_affineSpan_eq_top [FiniteDimensional Real V] 
{s : Set V} (hs : Convex Real s) : (interior s).Nonempty ↔ affineSpan Real s = ⊤
参数：hs : Convex Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_convexHull_nonempty_iff_affineSpan_eq_top`：interior_convexHull_
nonempty_iff_affineSpan_eq_top [FiniteDimensional Real V] {s : Set V} : (interio
r (convexHull Real s)).Nonempty ↔ affine…
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Convex.interior_nonempty_iff_affineSpan_eq_top [FiniteDimensional ℝ V] {s : Set V}
    (hs : Convex ℝ s) : (interior s).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top, hs.convexHull_eq]
