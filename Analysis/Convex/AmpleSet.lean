/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Floris van Doorn
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Ample subsets of real vector spaces

In this file we study ample sets in real vector spaces. A set is ample if all its connected
component have full convex hull. Ample sets are an important ingredient for defining ample
differential relations.

## Main results
- `ampleSet_empty` and `ampleSet_univ`: the empty set and `univ` are ample
- `AmpleSet.union`: the union of two ample sets is ample
- `AmpleSet.{pre}image`: being ample is invariant under continuous affine equivalences;
  `AmpleSet.{pre}image_iff` are "iff" versions of these
- `AmpleSet.vadd`: in particular, ample-ness is invariant under affine translations
- `AmpleSet.of_one_lt_codim`: a linear subspace of codimension at least two has an ample complement.
  This is the crucial geometric ingredient which allows to apply convex integration
  to the theory of immersions in positive codimension.

## Implementation notes

A priori, the definition of ample subset asks for a vector space structure and a topology on the
ambient type without any link between those structures. In practice, we care most about using these
for finite-dimensional vector spaces with their natural topology.

All vector spaces in the file are real vector spaces. While the definition generalises to other
connected fields, that is not useful in practice.

## Tags
ample set
-/

@[expose] public section

/-! ## Definition and invariance -/

open Set

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A subset of a topological real vector space is ample
if the convex hull of each of its connected components is the full space. -/
/-
**AmpleSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AmpleSet (s : Set F) : Prop
参数：s : Set F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a topological real vector space is ample
if the convex hull of each of its connected components is the full space.
-/
def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ

/-- A whole vector space is ample. -/
@[simp]
/-
**ampleSet_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] : Am
pleSet (univ : Set F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn_univ`：connectedComponentIn_univ (x : α) : connected
ComponentIn univ x = connectedComponent x
· 使用定理 `PreconnectedSpace.connectedComponent_eq_univ`：PreconnectedSpace.connecte
dComponent_eq_univ {X : Type*} [TopologicalSpace X] [h : PreconnectedSpace X] (x
 : X) : connectedComponent x = uni…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `ContractibleSpace.instPathConnectedSpace`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [ContractibleSpace X], PathConnectedSpace X
· 使用定理 `RealTopologicalVectorSpace.contractibleSpace`：∀ {E : Type u_1} [inst : A
ddCommGroup E] [inst_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [Conti
nuousAdd E]   [ContinuousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convexHull_univ`：convexHull_univ : convexHull 𝕜 (univ : Set E) = univ

--- 原说明 ---
A whole vector space is ample.
-/
theorem ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]

/-- The empty set in a vector space is ample. -/
@[simp]
/-
**ampleSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ampleSet_empty : AmpleSet (∅ : Set F)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty set in a vector space is ample.
-/
theorem ampleSet_empty : AmpleSet (∅ : Set F) := fun _ ↦ False.elim

namespace AmpleSet

/-- The union of two ample sets is ample. -/
/-
**AmpleSet.union** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s unio
n t)
参数：hs : AmpleSet s；ht : AmpleSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `connectedComponentIn_mono`：connectedComponentIn_mono (x : α) {F G : Set 
α} (h : F subseteq G) : connectedComponentIn F x subseteq connectedComponentIn G
 x
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t

--- 原说明 ---
The union of two ample sets is ample.
-/
theorem union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s ∪ t) := by
  intro x hx
  rcases hx with (h | h) <;>
  -- The connected component of `x ∈ s` in `s ∪ t` contains the connected component of `x` in `s`,
  -- hence is also full; similarly for `t`.
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff, ← hx] <;>
  apply convexHull_mono <;>
  apply connectedComponentIn_mono <;>
  [apply subset_union_left; apply subset_union_right]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Images of ample sets under continuous affine equivalences are ample. -/
/-
**AmpleSet.image** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : AmpleSet (L '' s)
参数：h : AmpleSet s；L : E ≃ᴬ[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.image_connectedComponentIn`：image_connectedComponentIn {s : S
et X} (h : X ≃ₜ Y) {x : X} (hx : x in s) : h '' connectedComponentIn s x = conne
ctedComponentIn (h '' s) (h…
· 使用定理 `AffineMap.image_convexHull`：AffineMap.image_convexHull (f : E ->ᵃ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `ContinuousAffineEquiv.surjective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ :
 Type u_3} {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGr
oup V₁] [inst_2 : _roo…

--- 原说明 ---
Images of ample sets under continuous affine equivalences are ample.
-/
theorem image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L '' s) := forall_mem_image.mpr fun x hx ↦
  calc (convexHull ℝ) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull ℝ) (L '' (connectedComponentIn s x)) :=
          .symm <| congrArg _ <| L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull ℝ (connectedComponentIn s x)) :=
          .symm <| L.toAffineMap.image_convexHull _
    _ = univ := by rw [h x hx, image_univ, L.surjective.range_eq]

/-- A set is ample iff its image under a continuous affine equivalence is. -/
/-
**AmpleSet.image_iff** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：image_iff {s : Set E} (L : E ≃ᴬ[Real] F) : AmpleSet (L '' s) ↔ AmpleSet s
参数：L : E ≃ᴬ[Real] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AmpleSet.image`：image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : 
AmpleSet (L '' s)
· 使用定理 `ContinuousAffineEquiv.symm_image_image`：symm_image_image (e : P₁ ≃ᴬ[k] P
₂) (s : Set P₁) : e.symm '' e '' s = s

--- 原说明 ---
A set is ample iff its image under a continuous affine equivalence is.
-/
theorem image_iff {s : Set E} (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L '' s) ↔ AmpleSet s :=
  ⟨fun h ↦ (L.symm_image_image s) ▸ h.image L.symm, fun h ↦ h.image L⟩

/-- Pre-images of ample sets under continuous affine equivalences are ample. -/
/-
**AmpleSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : AmpleSet (L ⁻¹'
 s)
参数：h : AmpleSet s；L : E ≃ᴬ[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAffineEquiv.image_symm_eq_preimage`：∀ {k : Type u_1} {P₁ : Typ
e u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1
 : AddCommGroup V₁] [inst_2 : _roo…
· 使用定理 `AmpleSet.image`：image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : 
AmpleSet (L '' s)

--- 原说明 ---
Pre-images of ample sets under continuous affine equivalences are ample.
-/
theorem preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[ℝ] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

/-- A set is ample iff its pre-image under a continuous affine equivalence is. -/
/-
**AmpleSet.preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：preimage_iff {s : Set F} (L : E ≃ᴬ[Real] F) : AmpleSet (L ⁻¹' s) ↔ AmpleSe
t s
参数：L : E ≃ᴬ[Real] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AmpleSet.image`：image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : 
AmpleSet (L '' s)
· 使用定理 `ContinuousAffineEquiv.image_preimage`：image_preimage (e : P₁ ≃ᴬ[k] P₂) (
s : Set P₂) : e '' e ⁻¹' s = s
· 使用定理 `AmpleSet.preimage`：preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[Real]
 F) : AmpleSet (L ⁻¹' s)

--- 原说明 ---
A set is ample iff its pre-image under a continuous affine equivalence is.
-/
theorem preimage_iff {s : Set F} (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L ⁻¹' s) ↔ AmpleSet s :=
  ⟨fun h ↦ L.image_preimage s ▸ h.image L, fun h ↦ h.preimage L⟩

open scoped Pointwise

/-- Affine translations of ample sets are ample. -/
/-
**AmpleSet.vadd** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} : AmpleSet (y 
+ᵥ s)
参数：h : AmpleSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AmpleSet.image`：image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[Real] F) : 
AmpleSet (L '' s)
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
Affine translations of ample sets are ample.
-/
theorem vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} :
    AmpleSet (y +ᵥ s) :=
  h.image (ContinuousAffineEquiv.constVAdd ℝ E y)

/-- A set is ample iff its affine translation is. -/
/-
**AmpleSet.vadd_iff** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：vadd_iff [ContinuousAdd E] {s : Set E} {y : E} : AmpleSet (y +ᵥ s) ↔ Ample
Set s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AmpleSet.image_iff`：image_iff {s : Set E} (L : E ≃ᴬ[Real] F) : AmpleSet 
(L '' s) ↔ AmpleSet s
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
A set is ample iff its affine translation is.
-/
theorem vadd_iff [ContinuousAdd E] {s : Set E} {y : E} :
    AmpleSet (y +ᵥ s) ↔ AmpleSet s :=
  AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd ℝ E y)

/-! ## Subspaces of codimension at least two have ample complement -/
section Codimension

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is ample. -/
/-
**AmpleSet.of_one_lt_codim** 是 Mathlib 中的一个定理，位于命名空间 `AmpleSet`。
形式化陈述：of_one_lt_codim [IsTopologicalAddGroup F] [ContinuousSMul Real F] {E : Sub
module Real F} (hcodim : 1 < Module.rank Real (F ⧸ E)) : AmpleSet (Eᶜ : Set F)
参数：hcodim : 1 < Module.rank Real (F ⧸ E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.connectedComponentIn_eq_self_of_one_lt_codim`：Submodule.connec
tedComponentIn_eq_self_of_one_lt_codim (E : Submodule Real F) (hcodim : 1 < Modu
le.rank Real (F ⧸ E)) {x : F} (hx : x ∉ E) :…
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `segment_subset_convexHull`：segment_subset_convexHull (hx : x in s) (hy :
 y in s) : segment 𝕜 x y subseteq convexHull 𝕜 s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `mem_segment_sub_add`：mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) 
: x in [x - y -[𝕜] x + y]
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s

--- 原说明 ---
Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is ample.
-/
theorem of_one_lt_codim [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {E : Submodule ℝ F}
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx ↦ by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ E := by
      rw [← not_forall, ← Submodule.eq_top_iff']
      rintro rfl
      simp at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull ℝ (Eᶜ : Set F) h

end Codimension

end AmpleSet

