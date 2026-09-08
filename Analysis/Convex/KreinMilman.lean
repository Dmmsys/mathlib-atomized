/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# The Krein-Milman theorem

This file proves the Krein-Milman lemma and the Krein-Milman theorem.

## The lemma

The lemma states that a nonempty compact set `s` has an extreme point. The proof goes:
1. Using Zorn's lemma, find a minimal nonempty closed `t` that is an extreme subset of `s`. We will
  show that `t` is a singleton, thus corresponding to an extreme point.
2. By contradiction, `t` contains two distinct points `x` and `y`.
3. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` and `y`.
4. Look at the extreme (actually exposed) subset of `t` obtained by going the furthest away from
  the separating hyperplane in the direction of `x`. It is nonempty, closed and an extreme subset
  of `s`.
5. It is a strict subset of `t` (`y` isn't in it), so `t` isn't minimal. Absurd.

## The theorem

The theorem states that a compact convex set `s` is the closure of the convex hull of its extreme
points. It is an almost immediate strengthening of the lemma. The proof goes:
1. By contradiction, `s \ closure (convexHull ℝ (extremePoints ℝ s))` is nonempty, say with `x`.
2. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` from
  `closure (convexHull ℝ (extremePoints ℝ s))`.
3. Look at the extreme (actually exposed) subset of
  `s \ closure (convexHull ℝ (extremePoints ℝ s))` obtained by going the furthest away from the
  separating hyperplane. It is nonempty by assumption of nonemptiness and compactness, so by the
  lemma it has an extreme point.
4. This point is also an extreme point of `s`. Absurd.

## Related theorems

When the space is finite dimensional, the `closure` can be dropped to strengthen the result of the
Krein-Milman theorem. This leads to the Minkowski-Carathéodory theorem (currently not in mathlib).
Birkhoff's theorem is the Minkowski-Carathéodory theorem applied to the set of bistochastic
matrices, permutation matrices being the extreme points.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

-/

public section

open Set

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T1Space F]

/-- **Krein-Milman lemma**: In an LCTVS, any nonempty compact set has an extreme point. -/
/-
**IsCompact.extremePoints_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.extremePoints_nonempty (hscomp : IsCompact s) (hsnemp : s.Nonemp
ty) : (s.extremePoints Real).Nonempty
参数：hscomp : IsCompact s；hsnemp : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_superset`：zorn_superset (S : Set (Set α)) (h : forall c subseteq S,
 IsChain (· subseteq ·) c -> exists lb in S, forall s in c, lb subseteq s) : exi
sts…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsExtreme.rfl`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst
_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A : Set E
}, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsExtreme.subset`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜 E] {A B : 
Set E}…
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `isExtreme_sInter`：isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (
hAF : forall B in F, IsExtreme 𝕜 A B) : IsExtreme 𝕜 A (⋂₀ F)
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `IsExtreme.mem_extremePoints`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : SMul 𝕜
 E] {A : Set E} {…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `geometric_hahn_banach_point_point`：geometric_hahn_banach_point_point [T1
Space E] (hxy : x != y) : exists f : StrongDual Real E, f x < f y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Krein-Milman lemma**: In an LCTVS, any nonempty compact set has an extreme poi
nt.
-/
theorem IsCompact.extremePoints_nonempty (hscomp : IsCompact s) (hsnemp : s.Nonempty) :
    (s.extremePoints ℝ).Nonempty := by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme ℝ s t }
  rsuffices ⟨t, ht⟩ : ∃ t, Minimal (· ∈ S) t
  · obtain ⟨⟨x, hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_contra hyx
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx
    obtain ⟨z, hzt, hz⟩ :=
      (hscomp.of_isClosed_subset htclos hst.1).exists_isMaxOn ⟨x, hxt⟩
        l.continuous.continuousOn
    have h : IsExposed ℝ t ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }) := fun _ => ⟨l, rfl⟩
    rw [ht.eq_of_ge (y := ({ z ∈ t | ∀ w ∈ t, l w ≤ l z }))
      ⟨⟨z, hzt, hz⟩, h.isClosed htclos, hst.trans h.isExtreme⟩ (t.sep_subset _)] at hyB
    exact hl.not_ge (hyB.2 x hxt)
  refine zorn_superset _ fun F hFS hF => ?_
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  · exact ⟨s, ⟨hsnemp, hscomp.isClosed, IsExtreme.rfl⟩, fun _ => False.elim⟩
  refine ⟨⋂₀ F, ⟨?_, isClosed_sInter fun t ht => (hFS ht).2.1,
    isExtreme_sInter hFnemp fun t ht => (hFS ht).2.2⟩, fun t ht => sInter_subset_of_mem ht⟩
  have : Nonempty (↥F) := hFnemp.to_subtype
  rw [sInter_eq_iInter]
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun t u => ?_)
    (fun t => (hFS t.mem).1)
    (fun t => hscomp.of_isClosed_subset (hFS t.mem).2.1 (hFS t.mem).2.2.1) fun t =>
      (hFS t.mem).2.1
  obtain htu | hut := hF.total t.mem u.mem
  exacts [⟨t, Subset.rfl, htu⟩, ⟨u, hut, Subset.rfl⟩]

/-- **Krein-Milman theorem**: In an LCTVS, any compact convex set is the closure of the convex hull
of its extreme points. -/
/-
**closure_convexHull_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex R
eal s) : closure (convexHull Real <| s.extremePoints Real) = s
参数：hscomp : IsCompact s；hAconv : Convex Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `geometric_hahn_banach_closed_point`：geometric_hahn_banach_closed_point (
hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) : exists (f : StrongDual 
Real E) (u : Real), (for…
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `IsCompact.extremePoints_nonempty`：IsCompact.extremePoints_nonempty (hsco
mp : IsCompact s) (hsnemp : s.Nonempty) : (s.extremePoints Real).Nonempty
· 使用定理 `IsExposed.isCompact`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Topological
Space 𝕜] [inst_1 : Ring 𝕜] [inst_2 : PartialOrder 𝕜]   [inst_3 : AddCommMonoid E
] [inst_4…
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
**Krein-Milman theorem**: In an LCTVS, any compact convex set is the closure of 
the convex hull
of its extreme points.
-/
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed ℝ s ({ y ∈ s | ∀ z ∈ s, l z ≤ l y }) := fun _ => ⟨l, rfl⟩
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_isMaxOn ⟨x, hxA⟩ l.continuous.continuousOn
  obtain ⟨y, hy⟩ := (h.isCompact hscomp).extremePoints_nonempty ⟨z, hzA, hz⟩
  linarith [hlr _ (subset_closure <| subset_convexHull _ _ <|
    h.isExtreme.extremePoints_subset_extremePoints hy), hy.1.2 x hxA]

/-- A continuous affine map is surjective from the extreme points of a compact set to the extreme
points of the image of that set. This inclusion is in general strict. -/
/-
**surjOn_extremePoints_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：surjOn_extremePoints_image (f : E ->ᴬ[Real] F) (hs : IsCompact s) : SurjOn
 f (extremePoints Real s) (extremePoints Real (f '' s))
参数：f : E ->ᴬ[Real] F；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousAffineMap.continuous`：∀ {R : Type u_1} {V : Type u_2} {W : Typ
e u_3} {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup V]  
 [inst_2 : _root_.Mo…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `IsCompact.extremePoints_nonempty`：IsCompact.extremePoints_nonempty (hsco
mp : IsCompact s) (hsnemp : s.Nonempty) : (s.extremePoints Real).Nonempty
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `image_openSegment`：image_openSegment (f : E ->ᵃ[𝕜] F) (a b : E) : f '' o
penSegment 𝕜 a b = openSegment 𝕜 (f a) (f b)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_extremePoints`：mem_extremePoints : x in A.extremePoints 𝕜 ↔ x in A ∧
 forallᵉ (x₁ in A) (x₂ in A), x in openSegment 𝕜 x₁ x₂ -> x₁ = x ∧ x₂ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A continuous affine map is surjective from the extreme points of a compact set t
o the extreme
points of the image of that set. This inclusion is in general strict.
-/
lemma surjOn_extremePoints_image (f : E →ᴬ[ℝ] F) (hs : IsCompact s) :
    SurjOn f (extremePoints ℝ s) (extremePoints ℝ (f '' s)) := by
  rintro w hw
  -- The fiber of `w` is nonempty and compact
  have ht : IsCompact {x ∈ s | f x = w} :=
    hs.inter_right <| isClosed_singleton.preimage f.continuous
  have ht₀ : {x ∈ s | f x = w}.Nonempty := by simpa using! extremePoints_subset hw
  -- Hence by the Krein-Milman lemma it has an extreme point `x`
  obtain ⟨x, ⟨hx, rfl⟩, hyt⟩ := ht.extremePoints_nonempty ht₀
  -- `f x = w` and `x` is an extreme point of `s`, so we're done
  refine mem_image_of_mem _ ⟨hx, fun y hy z hz hxyz ↦ ?_⟩
  have := by simpa using! image_openSegment _ f.toAffineMap y z
  rw [mem_extremePoints] at hw
  have := hw.2 _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hz) <| by
    rw [← this]; exact mem_image_of_mem _ hxyz
  exact hyt ⟨hy, this.1⟩ ⟨hz, this.2⟩ hxyz
