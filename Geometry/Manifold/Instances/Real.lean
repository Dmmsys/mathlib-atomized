/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`, and prove that its boundary is indeed `{x, y}`
whenever `x < y`. As a corollary, a product `M × [x, y]` with a manifold `M` without boundary
has boundary `M × {x, y}`.

More specifically, we introduce
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notation

In the scope `Manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `EuclideanSpace ℝ (Fin n)`
* `𝓡∂ n` for `modelWithCornersEuclideanHalfSpace n`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `EuclideanSpace ℝ (Fin m)`,
and `N` is smooth with boundary modelled on `EuclideanHalfSpace n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners cannot be implicit, see the discussion in
`Geometry.Manifold.IsManifold`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[Fact (x < y)]`.
-/

@[expose] public section

noncomputable section

open Set Function WithLp

open scoped Manifold ContDiff ENNReal

/-- The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
@[implicit_reducible, wikidata Q644719]
/-
**EuclideanHalfSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EuclideanHalfSpace (n : Nat) [NeZero n] : Type
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The half-space in `ℝ^n`, used to model manifolds with boundary. We only define i
t when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def EuclideanHalfSpace (n : ℕ) [NeZero n] : Type :=
  { x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0 }
deriving TopologicalSpace

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
@[implicit_reducible]
/-
**EuclideanQuadrant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EuclideanQuadrant (n : Nat) : Type
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors
 with nonnegative
coordinates.
-/
def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) // ∀ i : Fin n, 0 ≤ x i }
deriving TopologicalSpace

section

/- Register class instances for Euclidean half-space and quadrant, that cannot be noticed
without the following reducibility attribute (which is only set in this section). -/

variable {n : ℕ}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} [NeZero n] : Zero (EuclideanHalfSpace n) := ⟨⟨0, by simp⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Zero (EuclideanQuadrant n) := ⟨⟨0, by simp⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NeZero n] : Inhabited (EuclideanHalfSpace n) :=
  ⟨0⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (EuclideanQuadrant n) :=
  ⟨0⟩

@[ext]
/-
**EuclideanQuadrant.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanQuadrant.ext (x y : EuclideanQuadrant n) (h : x.1 = y.1) : x = y
参数：x y : EuclideanQuadrant n；h : x.1 = y.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem EuclideanQuadrant.ext (x y : EuclideanQuadrant n) (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[ext]
/-
**EuclideanHalfSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanHalfSpace.ext [NeZero n] (x y : EuclideanHalfSpace n) (h : x.1 = 
y.1) : x = y
参数：x y : EuclideanHalfSpace n；h : x.1 = y.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem EuclideanHalfSpace.ext [NeZero n] (x y : EuclideanHalfSpace n)
    (h : x.1 = y.1) : x = y :=
  Subtype.ext h
/-
**EuclideanHalfSpace.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanHalfSpace.convex [NeZero n] : Convex Real { x : EuclideanSpace Re
al (Fin n) | 0 <= x 0 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem EuclideanHalfSpace.convex [NeZero n] :
    Convex ℝ { x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 } :=
  fun _ hx _ hy _ _ _ _ _ ↦ by dsimp at hx hy ⊢; positivity
/-
**EuclideanQuadrant.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanQuadrant.convex : Convex Real { x : EuclideanSpace Real (Fin n) |
 forall i, 0 <= x i }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem EuclideanQuadrant.convex :
    Convex ℝ { x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i } :=
  fun _ hx _ hy _ _ _ _ _ i ↦ by dsimp at hx hy ⊢; specialize hx i; specialize hy i; positivity
/-
**EuclideanHalfSpace.pathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EuclideanHalfSpace.pathConnectedSpace [NeZero n] : PathConnectedSpace (Euc
lideanHalfSpace n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `EuclideanHalfSpace.convex`：EuclideanHalfSpace.convex [NeZero n] : Convex
 Real { x : EuclideanSpace Real (Fin n) | 0 <= x 0 }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
instance EuclideanHalfSpace.pathConnectedSpace [NeZero n] :
    PathConnectedSpace (EuclideanHalfSpace n) :=
  isPathConnected_iff_pathConnectedSpace.mp <| convex.isPathConnected ⟨0, by simp⟩
/-
**EuclideanQuadrant.pathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EuclideanQuadrant.pathConnectedSpace : PathConnectedSpace (EuclideanQuadra
nt n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `EuclideanQuadrant.convex`：EuclideanQuadrant.convex : Convex Real { x : E
uclideanSpace Real (Fin n) | forall i, 0 <= x i }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance EuclideanQuadrant.pathConnectedSpace : PathConnectedSpace (EuclideanQuadrant n) :=
  isPathConnected_iff_pathConnectedSpace.mp <| convex.isPathConnected ⟨0, by simp⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NeZero n] : LocallyPathConnectedSpace (EuclideanHalfSpace n) :=
  EuclideanHalfSpace.convex.locallyPathConnectedSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyPathConnectedSpace (EuclideanQuadrant n) :=
  EuclideanQuadrant.convex.locallyPathConnectedSpace
/-
**range_euclideanHalfSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_euclideanHalfSpace (n : Nat) [NeZero n] : range (Subtype.val : Eucli
deanHalfSpace n -> _) = { y | 0 <= y 0 }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem range_euclideanHalfSpace (n : ℕ) [NeZero n] :
    range (Subtype.val : EuclideanHalfSpace n → _) = { y | 0 ≤ y 0 } :=
  Subtype.range_val

@[simp]
/-
**interior_halfSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) : inter
ior { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a < y i }
参数：p : Real>=0∞；a : Real；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用引理 `PiLp.isOpenMap_apply`：isOpenMap_apply [forall i, TopologicalSpace (β i)]
 (i : ι) : IsOpenMap (fun f : PiLp p β => f i)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
theorem interior_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    interior { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a < y i } := by
  let f : PiLp p (fun _ : Fin n ↦ ℝ) → ℝ := fun x ↦ x i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage, interior_Ici]
  fun_prop

@[simp]
/-
**closure_halfSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) : closur
e { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a <= y i }
参数：p : Real>=0∞；a : Real；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用引理 `PiLp.isOpenMap_apply`：isOpenMap_apply [forall i, TopologicalSpace (β i)]
 (i : ι) : IsOpenMap (fun f : PiLp p β => f i)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `closure_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preord
er α] [ClosedIciTopology α] (a : α),   closure (Set.Ici a) = Set.Ici a
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem closure_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a ≤ y i } := by
  let f : PiLp p (fun _ : Fin n ↦ ℝ) → ℝ := fun x ↦ x i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage, closure_Ici]
  fun_prop

@[simp]
/-
**closure_open_halfSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_open_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) : c
losure { y : PiLp p (fun _ : Fin n => Real) | a < y i } = { y | a <= y i }
参数：p : Real>=0∞；a : Real；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用引理 `PiLp.isOpenMap_apply`：isOpenMap_apply [forall i, TopologicalSpace (β i)]
 (i : ι) : IsOpenMap (fun f : PiLp p β => f i)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem closure_open_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a < y i } = { y | a ≤ y i } := by
  let f : PiLp p (fun _ : Fin n ↦ ℝ) → ℝ := fun x ↦ x i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_closure_eq_closure_preimage, closure_Ioi]
  fun_prop

@[simp]
/-
**frontier_halfSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_halfSpace {n : Nat} (p : Real>=0∞) (a : Real) (i : Fin n) : front
ier { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y | a = y i }
参数：p : Real>=0∞；a : Real；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `closure_halfSpace`：closure_halfSpace {n : Nat} (p : Real>=0∞) (a : Real)
 (i : Fin n) : closure { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { y |
 a <= y…
· 使用定理 `interior_halfSpace`：interior_halfSpace {n : Nat} (p : Real>=0∞) (a : Rea
l) (i : Fin n) : interior { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { 
y | a < …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `antisymm_iff`：antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a
 b ∧ r b a ↔ a = b
-/
theorem frontier_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    frontier { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a = y i } := by
  rw [frontier, closure_halfSpace, interior_halfSpace]
  ext y
  simpa only [mem_sdiff, mem_ofPred_eq, not_lt] using antisymm_iff
/-
**range_euclideanQuadrant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_euclideanQuadrant (n : Nat) : range (Subtype.val : EuclideanQuadrant
 n -> _) = { y | forall i : Fin n, 0 <= y i }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem range_euclideanQuadrant (n : ℕ) :
    range (Subtype.val : EuclideanQuadrant n → _) = { y | ∀ i : Fin n, 0 ≤ y i } :=
  Subtype.range_val
/-
**interior_euclideanQuadrant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_euclideanQuadrant (n : Nat) (p : Real>=0∞) (a : Real) : interior 
{ y : PiLp p (fun _ : Fin n => Real) | forall i : Fin n, a <= y i } = { y | fora
ll i : Fin n, a < y i }
参数：n : Nat；p : Real>=0∞；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `interior_iInter_of_finite`：interior_iInter_of_finite [Finite ι] (f : ι -
> Set X) : interior (⋂ i, f i) = ⋂ i, interior (f i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用引理 `PiLp.isOpenMap_apply`：isOpenMap_apply [forall i, TopologicalSpace (β i)]
 (i : ι) : IsOpenMap (fun f : PiLp p β => f i)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
theorem interior_euclideanQuadrant (n : ℕ) (p : ℝ≥0∞) (a : ℝ) :
    interior { y : PiLp p (fun _ : Fin n ↦ ℝ) | ∀ i : Fin n, a ≤ y i } =
      { y | ∀ i : Fin n, a < y i } := by
  let f i : PiLp p (fun _ : Fin n ↦ ℝ) → ℝ := fun x ↦ x i
  have h : { y : PiLp p (fun _ : Fin n ↦ ℝ) | ∀ i : Fin n, a ≤ y i } = ⋂ i, (f i) ⁻¹' Ici a := by
    ext; simp; rfl
  have h' : { y : PiLp p (fun _ : Fin n ↦ ℝ) | ∀ i : Fin n, a < y i } = ⋂ i, (f i) ⁻¹' Ioi a := by
    ext; simp; rfl
  rw [h, h', interior_iInter_of_finite]
  apply iInter_congr fun i ↦ ?_
  rw [← (PiLp.isOpenMap_apply p _ i).preimage_interior_eq_interior_preimage, interior_Ici]
  fun_prop

end

/--
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanHalfSpace n)`, used as
a model for manifolds with boundary. In the scope `Manifold`, use the shortcut `𝓡∂ n`.
-/
/-
**modelWithCornersEuclideanHalfSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : ModelWithCorners
 Real (EuclideanSpace Real (Fin n)) (EuclideanHalfSpace n) where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanHalfSp
ace n)`, used as
a model for manifolds with boundary. In the scope `Manifold`, use the shortcut `
𝓡∂ n`.
-/
def modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) where
  toFun := Subtype.val
  invFun x := ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩
  source := univ
  target := { x | 0 ≤ x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk, ← WithLp.equiv_symm_apply, Equiv.symm_apply_eq, update_eq_iff]
    exact ⟨max_eq_left xprop, fun i _ => rfl⟩
  right_inv' _ hx := by
    rw [Subtype.coe_mk, ← WithLp.equiv_symm_apply, Equiv.symm_apply_eq, update_eq_iff]
    exact ⟨max_eq_left hx, fun _ _ => rfl⟩
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte]
    apply Convex.convex_isRCLikeNormedField
    rw [range_euclideanHalfSpace n]
    exact EuclideanHalfSpace.convex (n := n)
  nonempty_interior' := by
    rw [range_euclideanHalfSpace, interior_halfSpace]
    exact ⟨toLp 2 fun i ↦ 1, by simp⟩
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by
    exact ((PiLp.continuous_toLp 2 _).comp <| (PiLp.continuous_ofLp 2 _).update 0 <|
      (PiLp.continuous_apply 2 _ 0).max continuous_const).subtype_mk _

/--
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanQuadrant n)`, used as a
model for manifolds with corners -/
/-
**modelWithCornersEuclideanQuadrant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modelWithCornersEuclideanQuadrant (n : Nat) : ModelWithCorners Real (Eucli
deanSpace Real (Fin n)) (EuclideanQuadrant n) where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Definition of the model with corners `(EuclideanSpace ℝ (Fin n), EuclideanQuadra
nt n)`, used as a
model for manifolds with corners
-/
def modelWithCornersEuclideanQuadrant (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n) where
  toFun := Subtype.val
  invFun x := ⟨toLp 2 fun i ↦ max (x i) 0,
    fun i ↦ by simp only [le_sup_right]⟩
  source := univ
  target := { x | ∀ i, 0 ≤ x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [x.2 i, sup_of_le_left]
  right_inv' x hx := by ext1 i; simp only [hx i, sup_of_le_left]
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte]
    apply Convex.convex_isRCLikeNormedField
    rw [range_euclideanQuadrant]
    exact EuclideanQuadrant.convex
  nonempty_interior' := by
    rw [range_euclideanQuadrant, interior_euclideanQuadrant]
    exact ⟨toLp 2 fun i ↦ 1, by simp⟩
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp <|
    (continuous_pi fun i ↦ ((PiLp.continuous_apply 2 _ i).max continuous_const))) _

/-- The model space used to define `n`-dimensional real manifolds without boundary. -/
scoped[Manifold]
  notation3 "𝓡 " n =>
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))

/-- The model space used to define `n`-dimensional real manifolds with boundary. -/
scoped[Manifold]
  notation3 "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n))

/-
**modelWithCornersEuclideanHalfSpace_toFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n : ℕ) [inst : NeZero n], ↑(modelWithCornersEuclideanHalfSpace n) = Sub
type.val
参数：n : ℕ；modelWithCornersEuclideanHalfSpace n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
@[simp] lemma modelWithCornersEuclideanHalfSpace_toFun (n : ℕ) [NeZero n] :
    (𝓡∂ n : _ → _) = Subtype.val := rfl
/-
**modelWithCornersEuclideanHalfSpace_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：modelWithCornersEuclideanHalfSpace_symm_apply {n : Nat} [NeZero n] (x : Eu
clideanSpace Real (Fin n)) : (𝓡∂ n).symm x = ⟨toLp 2 (update x 0 (max (x 0) 0)),
 by simp⟩
参数：x : EuclideanSpace Real (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
lemma modelWithCornersEuclideanHalfSpace_symm_apply {n : ℕ} [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) :
    (𝓡∂ n).symm x = ⟨toLp 2 (update x 0 (max (x 0) 0)), by simp⟩ := rfl
/-
**modelWithCornersEuclideanHalfSpace_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：modelWithCornersEuclideanHalfSpace_zero {n : Nat} [NeZero n] : (𝓡∂ n) 0 = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
lemma modelWithCornersEuclideanHalfSpace_zero {n : ℕ} [NeZero n] : (𝓡∂ n) 0 = 0 := rfl
/-
**range_modelWithCornersEuclideanHalfSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : range (𝓡∂ 
n) = { y | 0 <= y 0 }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `range_euclideanHalfSpace`：range_euclideanHalfSpace (n : Nat) [NeZero n] 
: range (Subtype.val : EuclideanHalfSpace n -> _) = { y | 0 <= y 0 }
-/
lemma range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    range (𝓡∂ n) = { y | 0 ≤ y 0 } := range_euclideanHalfSpace n
/-
**interior_range_modelWithCornersEuclideanHalfSpace** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：interior_range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : i
nterior (range (𝓡∂ n)) = { y | 0 < y 0 }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `range_euclideanHalfSpace`：range_euclideanHalfSpace (n : Nat) [NeZero n] 
: range (Subtype.val : EuclideanHalfSpace n -> _) = { y | 0 <= y 0 }
· 使用定理 `interior_halfSpace`：interior_halfSpace {n : Nat} (p : Real>=0∞) (a : Rea
l) (i : Fin n) : interior { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { 
y | a < …
-/
lemma interior_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    interior (range (𝓡∂ n)) = { y | 0 < y 0 } := by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 ≤ y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _
/-
**frontier_range_modelWithCornersEuclideanHalfSpace** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：frontier_range_modelWithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : f
rontier (range (𝓡∂ n)) = { y | 0 = y 0 }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `range_euclideanHalfSpace`：range_euclideanHalfSpace (n : Nat) [NeZero n] 
: range (Subtype.val : EuclideanHalfSpace n -> _) = { y | 0 <= y 0 }
· 使用定理 `frontier_halfSpace`：frontier_halfSpace {n : Nat} (p : Real>=0∞) (a : Rea
l) (i : Fin n) : frontier { y : PiLp p (fun _ : Fin n => Real) | a <= y i } = { 
y | a = …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma frontier_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    frontier (range (𝓡∂ n)) = { y | 0 = y 0 } := by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 ≤ y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _

/-- The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`EuclideanHalfSpace 1`.
-/
/-
**IccLeftChart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IccLeftChart (x y : Real) [h : Fact (x < y)] : OpenPartialHomeomorph (Icc 
x y) (EuclideanHalfSpace 1) where source
参数：x y : Real；x < y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left chart for the topological space `[x, y]`, defined on `[x,y)` and sendin
g `x` to `0` in
`EuclideanHalfSpace 1`.
-/
def IccLeftChart (x y : ℝ) [h : Fact (x < y)] :
    OpenPartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨toLp 2 fun _ ↦ z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩
  map_source' := by simp
  map_target' := by
    simp only [min_lt_iff, mem_ofPred_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_ofPred_eq, mem_Icc] at hz h'z
    simp only [Fin.isValue, sub_add_cancel, hz, inf_of_le_left]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    ext i
    dsimp at hz h'z
    have A : x + z 0 ≤ y := by linarith
    rw [Subsingleton.elim i 0]
    simp only [Fin.isValue, add_comm, A, inf_of_le_left, add_sub_cancel_left]
  open_source :=
    haveI : IsOpen { z : ℝ | z < y } := isOpen_Iio
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@PiLp.continuous_apply 2 (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

variable {x y : ℝ} [hxy : Fact (x < y)]
/-
**IccLeftChart_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_apply (z : Icc x y) : IccLeftChart x y z = ⟨toLp 2 fun _ => z
.val - x, by aesop⟩
参数：z : Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma IccLeftChart_apply (z : Icc x y) :
    IccLeftChart x y z = ⟨toLp 2 fun _ ↦ z.val - x, by aesop⟩ :=
  rfl
/-
**IccLeftChart_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_symm_apply (x y : Real) [h : Fact (x < y)] (z : EuclideanHalf
Space 1) : (IccLeftChart x y).symm z = ⟨min (z.val 0 + x) y, by simp [z.prop, h.
out.le]⟩
参数：x y : Real；x < y；z : EuclideanHalfSpace 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma IccLeftChart_symm_apply (x y : ℝ) [h : Fact (x < y)] (z : EuclideanHalfSpace 1) :
    (IccLeftChart x y).symm z = ⟨min (z.val 0 + x) y, by simp [z.prop, h.out.le]⟩ :=
  rfl
/-
**IccLeftChart_symm_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 <= 
y - x) : (IccLeftChart x y).symm z = ⟨z.val 0 + x, by simpa [z.prop, hxy.out.le,
 ← le_add_neg_iff_add_le]⟩
参数：hz : z.val 0 <= y - x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 33 条，此处仅展示前 30 条）
-/
lemma IccLeftChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 ≤ y - x) :
    (IccLeftChart x y).symm z =
      ⟨z.val 0 + x, by simpa [z.prop, hxy.out.le, ← le_add_neg_iff_add_le]⟩ := by
  ext
  simp only [IccLeftChart_symm_apply, inf_eq_left]
  linarith

namespace Fact.Manifold

/-
**Fact.Manifold.** 是 Mathlib 中的一个实例，位于命名空间 `Fact.Manifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : Fact (x ≤ y) := Fact.mk hxy.out.le

end Fact.Manifold

open Fact.Manifold

/-
**IccLeftChart_extend_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_extend_bot : (IccLeftChart x y).extend (𝓡∂ 1) ⊥ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma IccLeftChart_extend_bot : (IccLeftChart x y).extend (𝓡∂ 1) ⊥ = 0 := by
  norm_num [IccLeftChart, modelWithCornersEuclideanHalfSpace_zero]
  congr
/-
**iccLeftChart_extend_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iccLeftChart_extend_zero {p : Set.Icc x y} : (IccLeftChart x y).extend (𝓡∂
 1) p 0 = p.val - x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
lemma iccLeftChart_extend_zero {p : Set.Icc x y} :
    (IccLeftChart x y).extend (𝓡∂ 1) p 0 = p.val - x := rfl
/-
**IccLeftChart_extend_interior_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_extend_interior_pos {p : Set.Icc x y} (hp : x < p.val ∧ p.val
 < y) : 0 < (IccLeftChart x y).extend (𝓡∂ 1) p 0
参数：hp : x < p.val ∧ p.val < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IccLeftChart_extend_interior_pos {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    0 < (IccLeftChart x y).extend (𝓡∂ 1) p 0 := by
  simp_rw [iccLeftChart_extend_zero]
  norm_num [hp.1]
/-
**IccLeftChart_extend_bot_mem_frontier** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccLeftChart_extend_bot_mem_frontier : (IccLeftChart x y).extend (𝓡∂ 1) ⊥ 
in frontier (range (𝓡∂ 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IccLeftChart_extend_bot`：IccLeftChart_extend_bot : (IccLeftChart x y).ex
tend (𝓡∂ 1) ⊥ = 0
· 使用引理 `frontier_range_modelWithCornersEuclideanHalfSpace`：frontier_range_modelW
ithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : frontier (range (𝓡∂ n)) = { 
y | 0 = y 0 }
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `PiLp.zero_apply`：zero_apply : (0 : PiLp p β) i = 0
-/
lemma IccLeftChart_extend_bot_mem_frontier :
    (IccLeftChart x y).extend (𝓡∂ 1) ⊥ ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccLeftChart_extend_bot, frontier_range_modelWithCornersEuclideanHalfSpace,
    mem_ofPred, PiLp.zero_apply]

/-- The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`EuclideanHalfSpace 1`.
-/
/-
**IccRightChart** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IccRightChart (x y : Real) [h : Fact (x < y)] : OpenPartialHomeomorph (Icc
 x y) (EuclideanHalfSpace 1) where source
参数：x y : Real；x < y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right chart for the topological space `[x, y]`, defined on `(x,y]` and sendi
ng `y` to `0` in
`EuclideanHalfSpace 1`.
-/
def IccRightChart (x y : ℝ) [h : Fact (x < y)] :
    OpenPartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨toLp 2 fun _ ↦ y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩
  map_source' := by simp
  map_target' := by
    simp only [lt_max_iff, mem_ofPred_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_ofPred_eq, mem_Icc] at hz h'z
    simp only [Fin.isValue, sub_eq_add_neg, neg_add_rev, neg_neg,
      add_neg_cancel_comm_assoc, hz, sup_of_le_left]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    ext i
    dsimp at hz h'z
    have A : x ≤ y - z 0 := by linarith
    rw [Subsingleton.elim i 0]
    simp only [Fin.isValue, A, sup_of_le_left, sub_sub_cancel]
  open_source :=
    haveI : IsOpen { z : ℝ | x < z } := isOpen_Ioi
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@PiLp.continuous_apply 2 (Fin 1) (fun _ ↦ ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop
/-
**IccRightChart_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccRightChart_apply (z : Icc x y) : IccRightChart x y z = ⟨toLp 2 fun _ =>
 y - z.val, by aesop⟩
参数：z : Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma IccRightChart_apply (z : Icc x y) :
    IccRightChart x y z = ⟨toLp 2 fun _ ↦ y - z.val, by aesop⟩ :=
  rfl
/-
**IccRightChart_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccRightChart_symm_apply (x y : Real) [h : Fact (x < y)] (z : EuclideanHal
fSpace 1) : (IccRightChart x y).symm z = ⟨max (y - z.val 0) x, by simp [z.prop, 
h.out.le, sub_eq_add_neg]⟩
参数：x y : Real；x < y；z : EuclideanHalfSpace 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma IccRightChart_symm_apply (x y : ℝ) [h : Fact (x < y)] (z : EuclideanHalfSpace 1) :
    (IccRightChart x y).symm z =
      ⟨max (y - z.val 0) x, by simp [z.prop, h.out.le, sub_eq_add_neg]⟩ :=
  rfl
/-
**IccRightChart_symm_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccRightChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 <=
 y - x) : (IccRightChart x y).symm z = ⟨y - z.val 0, by simp [z.prop, sub_eq_add
_neg, add_le_of_le_sub_left hz]⟩
参数：hz : z.val 0 <= y - x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 34 条，此处仅展示前 30 条）
-/
lemma IccRightChart_symm_apply_of_le {z : EuclideanHalfSpace 1} (hz : z.val 0 ≤ y - x) :
    (IccRightChart x y).symm z =
      ⟨y - z.val 0, by simp [z.prop, sub_eq_add_neg, add_le_of_le_sub_left hz]⟩ := by
  ext
  simp only [IccRightChart_symm_apply, sup_eq_left]
  linarith
/-
**IccRightChart_extend_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccRightChart_extend_top : (IccRightChart x y).extend (𝓡∂ 1) ⊤ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma IccRightChart_extend_top :
    (IccRightChart x y).extend (𝓡∂ 1) ⊤ = 0 := by
  norm_num [IccRightChart, modelWithCornersEuclideanHalfSpace_zero]
  congr
/-
**IccRightChart_extend_top_mem_frontier** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IccRightChart_extend_top_mem_frontier : (IccRightChart x y).extend (𝓡∂ 1) 
⊤ in frontier (range (𝓡∂ 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IccRightChart_extend_top`：IccRightChart_extend_top : (IccRightChart x y)
.extend (𝓡∂ 1) ⊤ = 0
· 使用引理 `frontier_range_modelWithCornersEuclideanHalfSpace`：frontier_range_modelW
ithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : frontier (range (𝓡∂ n)) = { 
y | 0 = y 0 }
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `PiLp.zero_apply`：zero_apply : (0 : PiLp p β) i = 0
-/
lemma IccRightChart_extend_top_mem_frontier :
    (IccRightChart x y).extend (𝓡∂ 1) ⊤ ∈ frontier (range (𝓡∂ 1)) := by
  rw [IccRightChart_extend_top, frontier_range_modelWithCornersEuclideanHalfSpace,
    mem_ofPred, PiLp.zero_apply]

/-- Charted space structure on `[x, y]`, using only two charts taking values in
`EuclideanHalfSpace 1`.
-/
/-
**instIccChartedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIccChartedSpace (x y : Real) [h : Fact (x < y)] : ChartedSpace (Euclid
eanHalfSpace 1) (Icc x y) where atlas
参数：x y : Real；x < y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Charted space structure on `[x, y]`, using only two charts taking values in
`EuclideanHalfSpace 1`.
-/
instance instIccChartedSpace (x y : ℝ) [h : Fact (x < y)] :
    ChartedSpace (EuclideanHalfSpace 1) (Icc x y) where
  atlas := {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : ℝ) < y <;> simp [h']

@[simp]
/-
**Icc_chartedSpaceChartAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_chartedSpaceChartAt {z : Set.Icc x y} : chartAt _ z = if z.val < y the
n IccLeftChart x y else IccRightChart x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma Icc_chartedSpaceChartAt {z : Set.Icc x y} :
    chartAt _ z = if z.val < y then IccLeftChart x y else IccRightChart x y := rfl
/-
**Icc_chartedSpaceChartAt_of_le_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_chartedSpaceChartAt_of_le_top {z : Set.Icc x y} (h : z.val < y) : char
tAt _ z = IccLeftChart x y
参数：h : z.val < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Icc_chartedSpaceChartAt_of_le_top {z : Set.Icc x y} (h : z.val < y) :
    chartAt _ z = IccLeftChart x y := by
  simp [Icc_chartedSpaceChartAt, h]
/-
**Icc_chartedSpaceChartAt_of_top_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_chartedSpaceChartAt_of_top_le {z : Set.Icc x y} (h : y <= z.val) : cha
rtAt _ z = IccRightChart x y
参数：h : y <= z.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Icc_chartedSpaceChartAt_of_top_le {z : Set.Icc x y} (h : y ≤ z.val) :
    chartAt _ z = IccRightChart x y := by
  simp [Icc_chartedSpaceChartAt, reduceIte, not_lt.mpr h]
/-
**Icc_isBoundaryPoint_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_isBoundaryPoint_bot : (𝓡∂ 1).IsBoundaryPoint (⊥ : Set.Icc x y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isBoundaryPoint_iff`：isBoundaryPoint_iff {x : M} : I.Is
BoundaryPoint x ↔ extChartAt I x x in frontier (range I)
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `Icc_chartedSpaceChartAt_of_le_top`：Icc_chartedSpaceChartAt_of_le_top {z 
: Set.Icc x y} (h : z.val < y) : chartAt _ z = IccLeftChart x y
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `IccLeftChart_extend_bot_mem_frontier`：IccLeftChart_extend_bot_mem_fronti
er : (IccLeftChart x y).extend (𝓡∂ 1) ⊥ in frontier (range (𝓡∂ 1))
-/
lemma Icc_isBoundaryPoint_bot : (𝓡∂ 1).IsBoundaryPoint (⊥ : Set.Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt,
    Icc_chartedSpaceChartAt_of_le_top (by simp [hxy.out])]
  exact IccLeftChart_extend_bot_mem_frontier
/-
**Icc_isBoundaryPoint_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_isBoundaryPoint_top : (𝓡∂ 1).IsBoundaryPoint (⊤ : Set.Icc x y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.isBoundaryPoint_iff`：isBoundaryPoint_iff {x : M} : I.Is
BoundaryPoint x ↔ extChartAt I x x in frontier (range I)
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `Icc_chartedSpaceChartAt_of_top_le`：Icc_chartedSpaceChartAt_of_top_le {z 
: Set.Icc x y} (h : y <= z.val) : chartAt _ z = IccRightChart x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IccRightChart_extend_top_mem_frontier`：IccRightChart_extend_top_mem_fron
tier : (IccRightChart x y).extend (𝓡∂ 1) ⊤ in frontier (range (𝓡∂ 1))
-/
lemma Icc_isBoundaryPoint_top : (𝓡∂ 1).IsBoundaryPoint (⊤ : Set.Icc x y) := by
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt,
    Icc_chartedSpaceChartAt_of_top_le (by simp)]
  exact IccRightChart_extend_top_mem_frontier
/-
**Icc_isInteriorPoint_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Icc_isInteriorPoint_interior {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y
) : (𝓡∂ 1).IsInteriorPoint p
参数：hp : x < p.val ∧ p.val < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.IsInteriorPoint.eq_1`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用引理 `Icc_chartedSpaceChartAt_of_le_top`：Icc_chartedSpaceChartAt_of_le_top {z 
: Set.Icc x y} (h : z.val < y) : chartAt _ z = IccLeftChart x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `interior_range_modelWithCornersEuclideanHalfSpace`：interior_range_modelW
ithCornersEuclideanHalfSpace (n : Nat) [NeZero n] : interior (range (𝓡∂ n)) = { 
y | 0 < y 0 }
· 使用引理 `IccLeftChart_extend_interior_pos`：IccLeftChart_extend_interior_pos {p : 
Set.Icc x y} (hp : x < p.val ∧ p.val < y) : 0 < (IccLeftChart x y).extend (𝓡∂ 1)
 p 0
-/
lemma Icc_isInteriorPoint_interior {p : Set.Icc x y} (hp : x < p.val ∧ p.val < y) :
    (𝓡∂ 1).IsInteriorPoint p := by
  rw [ModelWithCorners.IsInteriorPoint, extChartAt, Icc_chartedSpaceChartAt_of_le_top hp.2,
    interior_range_modelWithCornersEuclideanHalfSpace]
  exact IccLeftChart_extend_interior_pos hp
/-
**boundary_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：boundary_Icc : (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`：eq_endpoints_or_mem_Ioo_of_mem_I
cc {x : α} (hmem : x in Icc a b) : x = a ∨ x = b ∨ x in Ioo a b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用引理 `Icc_isBoundaryPoint_bot`：Icc_isBoundaryPoint_bot : (𝓡∂ 1).IsBoundaryPoin
t (⊥ : Set.Icc x y)
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用引理 `Icc_isBoundaryPoint_top`：Icc_isBoundaryPoint_top : (𝓡∂ 1).IsBoundaryPoin
t (⊤ : Set.Icc x y)
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ModelWithCorners.compl_boundary`：compl_boundary : (I.boundary M)ᶜ = I.in
terior M
· 使用引理 `Icc_isInteriorPoint_interior`：Icc_isInteriorPoint_interior {p : Set.Icc 
x y} (hp : x < p.val ∧ p.val < y) : (𝓡∂ 1).IsInteriorPoint p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma boundary_Icc : (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤} := by
  ext p
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p.2 with (hp | hp | hp)
  · have : p = ⊥ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_bot (mem_insert ⊥ {⊤})
  · have : p = ⊤ := SetCoe.ext hp
    rw [this]
    apply iff_of_true Icc_isBoundaryPoint_top (mem_insert_of_mem ⊥ rfl)
  · apply iff_of_false
    · simpa [← mem_compl_iff, ModelWithCorners.compl_boundary] using!
        Icc_isInteriorPoint_interior hp
    · rintro (rfl | rfl) <;> simp at hp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A product `M × [x,y]` for `M` boundaryless has boundary `M × {x, y}`. -/
/-
**boundary_product** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：boundary_product [I.Boundaryless] : (I.prod (𝓡∂ 1)).boundary (M × Icc x y)
 = Set.prod univ {⊥, ⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fact.Manifold.instLeReal`：∀ {x y : ℝ} [hxy : Fact (x < y)], Fact (x ≤ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.boundary_of_boundaryless_left`：boundary_of_boundaryless
_left [BoundarylessManifold I M] : (I.prod J).boundary (M × N) = Set.prod (univ 
: Set M) (J.boundary N)
· 使用定理 `ModelWithCorners.instBoundarylessManifold`：∀ {𝕜 : Type u_1} [inst : Nont
riviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 E] {H : Type u_…
· 使用引理 `boundary_Icc`：boundary_Icc : (𝓡∂ 1).boundary (Icc x y) = {⊥, ⊤}

--- 原说明 ---
A product `M × [x,y]` for `M` boundaryless has boundary `M × {x, y}`.
-/
lemma boundary_product [I.Boundaryless] :
    (I.prod (𝓡∂ 1)).boundary (M × Icc x y) = Set.prod univ {⊥, ⊤} := by
  rw [I.boundary_of_boundaryless_left, boundary_Icc]

/-- The manifold structure on `[x, y]` is smooth. -/
/-
**instIsManifoldIcc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsManifoldIcc (x y : Real) [Fact (x < y)] {n : Nat∞ω} : IsManifold (𝓡∂
 1) n (Icc x y)
参数：x y : Real；x < y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用引理 `PiLp.contDiff_toLp`：PiLp.contDiff_toLp : ContDiff 𝕜 n (@toLp p (Π i, E i
))
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.neg`：ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff
 𝕜 n fun x => -f x
· 使用引理 `PiLp.contDiff_ofLp`：PiLp.contDiff_ofLp : ContDiff 𝕜 n (@ofLp p (Π i, E i
))
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `isManifold_of_contDiffOn`：isManifold_of_contDiffOn {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Typ
e*} [Topologic…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `symm_trans_mem_contDiffGroupoid`：symm_trans_mem_contDiffGroupoid (e : Op
enPartialHomeomorph M H) : e.symm.trans e in contDiffGroupoid n I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The manifold structure on `[x, y]` is smooth.
-/
instance instIsManifoldIcc (x y : ℝ) [Fact (x < y)] {n : ℕ∞ω} :
    IsManifold (𝓡∂ 1) n (Icc x y) := by
  have M : ContDiff ℝ n (show EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      from fun z ↦ toLp 2 fun i ↦ -z i + (y - x)) :=
    PiLp.contDiff_toLp.comp <| PiLp.contDiff_ofLp.neg.add contDiff_const
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
  /- We need to check that any composition of two charts gives a `C^∞` function. Each chart can be
  either the left chart or the right chart, leaving 4 possibilities that we handle successively. -/
  rcases he with (rfl | rfl) <;> rcases he' with (rfl | rfl)
  · -- `e = left chart`, `e' = left chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · -- `e = left chart`, `e' = right chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, update_self,
      max_eq_left, hz₀, lt_sub_iff_add_lt, mfld_simps] at hz₁ hz₂
    rw [min_eq_left hz₁.le, lt_add_iff_pos_left] at hz₂
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, *,
      max_eq_left, min_eq_left hz₁.le, update_self, mfld_simps]
    abel
  · -- `e = right chart`, `e' = left chart`
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨z, hz₀⟩, rfl⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, max_lt_iff,
      update_self, max_eq_left hz₀, mfld_simps] at hz₁ hz₂
    rw [lt_sub_comm] at hz₁
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart,
      update_self, max_eq_left, hz₀, hz₁.le, mfld_simps]
    abel
  · -- `e = right chart`, `e' = right chart`
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1

/-! Register the manifold structure on `Icc 0 1`. These are merely special cases of
`instIccChartedSpace` and `instIsManifoldIcc`. -/

section

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1) := by infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ∞ω} : IsManifold (𝓡∂ 1) n (Icc (0 : ℝ) 1) := by infer_instance

end

