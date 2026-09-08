/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner dual cone of a set

We define the inner dual cone of a set `s` in an inner product space to be the proper cone
consisting of all points `y` such that `0 ≤ ⟪x, y⟫` for all `x ∈ s`.

## Main statements

We prove the following theorems:
* `ProperCone.innerDual_innerDual`: The double inner dual of a proper convex cone is itself.
* `ProperCone.hyperplane_separation'`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `C` in a complete, real inner product space `E`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).

## Implementation notes

We do not provide `ConvexCone`- nor `PointedCone`-valued versions of `ProperCone.innerDual` since
the inner dual cone of any set is always closed and contains `0`, i.e. is a proper cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < ⟪x, y⟫}` is a candidate to the name
`ConvexCone.innerDual`.
-/

@[expose] public section

open Set LinearMap Pointwise
open scoped RealInnerProductSpace

variable {R E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {s t : Set E} {x x₀ y : E}

open Function

namespace ProperCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
@[simps! toSubmodule]
/-
**ProperCone.innerDual** 是 Mathlib 中的一个定义，位于命名空间 `ProperCone`。
形式化陈述：innerDual (s : Set E) : ProperCone Real E
参数：s : Set E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.instIsContPerfPairRealInnerₗOfCompleteSpace`：∀ (E : Ty
pe u_2) [inst : NormedAddCommGroup E] [CompleteSpace E] [inst_2 : InnerProductSp
ace ℝ E],   (innerₗ E).IsContPerfPair

--- 原说明 ---
The dual cone of a set `s` is the cone consisting of all points `y` such that fo
r all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`.
-/
noncomputable def innerDual (s : Set E) : ProperCone ℝ E := .dual (innerₗ E) s
/-
**ProperCone.mem_innerDual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : CompleteSpace E] {s : Set E}   {y : E}, y ∈ ProperCone.innerDual
 s ↔ ∀ ⦃x : E⦄, x ∈ s → 0 ≤ inner ℝ x y
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_innerDual : y ∈ innerDual s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫ := .rfl
/-
**ProperCone.innerDual_empty** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : CompleteSpace E],   ProperCone.innerDual ∅ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma innerDual_empty : innerDual (∅ : Set E) = ⊤ := by ext; simp

/-- Dual cone of the convex cone `{0}` is the total space. -/
/-
**ProperCone.innerDual_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : CompleteSpace E],   ProperCone.innerDual 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Dual cone of the convex cone `{0}` is the total space.
-/
@[simp] lemma innerDual_zero : innerDual (0 : Set E) = ⊤ := by ext; simp

/-- Dual cone of the total space is the convex cone `{0}`. -/
@[simp]
/-
**ProperCone.innerDual_univ** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_univ : innerDual (univ : Set E) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Dual cone of the total space is the convex cone `{0}`.
-/
lemma innerDual_univ : innerDual (univ : Set E) = ⊥ :=
  le_antisymm (fun x hx ↦ by simpa using hx (mem_univ (-x))) (by simp)
/-
**ProperCone.innerDual_le_innerDual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : CompleteSpace E]   {s t : Set E}, t ⊆ s → ProperCone.innerDual s
 ≤ ProperCone.innerDual t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma innerDual_le_innerDual (h : t ⊆ s) : innerDual s ≤ innerDual t :=
  fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
/-
**ProperCone.innerDual_singleton** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_singleton (x : E) : innerDual ({x} : Set E) = (positive Real Rea
l).comap (innerSL Real x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
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
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The inner dual cone of a singleton is given by the preimage of the positive cone
 under the
linear map `fun y ↦ ⟪x, y⟫`.
-/
lemma innerDual_singleton (x : E) :
    innerDual ({x} : Set E) = (positive ℝ ℝ).comap (innerSL ℝ x) := by ext; simp
/-
**ProperCone.innerDual_union** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_union (s t : Set E) : innerDual (s union t) = innerDual s ⊓ inne
rDual t
参数：s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma innerDual_union (s t : Set E) : innerDual (s ∪ t) = innerDual s ⊓ innerDual t :=
  le_antisymm (le_inf (fun _ hx _ hy ↦ hx <| .inl hy) fun _ hx _ hy ↦ hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h ↦ hx.1 h) (fun h ↦ hx.2 h)
/-
**ProperCone.innerDual_insert** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_insert (x : E) (s : Set E) : innerDual (insert x s) = innerDual 
{x} ⊓ innerDual s
参数：x : E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用引理 `ProperCone.innerDual_union`：innerDual_union (s t : Set E) : innerDual (s
 union t) = innerDual s ⊓ innerDual t
-/
lemma innerDual_insert (x : E) (s : Set E) :
    innerDual (insert x s) = innerDual {x} ⊓ innerDual s := by
  rw [insert_eq, innerDual_union]
/-
**ProperCone.innerDual_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_iUnion {ι : Sort*} (f : ι -> Set E) : innerDual (⋃ i, f i) = ⨅ i
, innerDual (f i)
参数：f : ι -> Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma innerDual_iUnion {ι : Sort*} (f : ι → Set E) :
    innerDual (⋃ i, f i) = ⨅ i, innerDual (f i) := by
  ext; simp [forall_comm (α := E)]
/-
**ProperCone.innerDual_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：innerDual_sUnion (S : Set (Set E)) : innerDual (⋃₀ S) = sInf (innerDual ''
 S)
参数：S : Set (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma innerDual_sUnion (S : Set (Set E)) : innerDual (⋃₀ S) = sInf (innerDual '' S) := by
  ext; simp [forall_comm (α := E)]

/-! ### Farkas' lemma and double dual of a cone in a Hilbert space -/

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
/-
**ProperCone.hyperplane_separation'** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：hyperplane_separation' (C : ProperCone Real E) (hx₀ : x₀ ∉ C) : exists y, 
(forall x in C, 0 <= ⟪x, y⟫) ∧ ⟪x₀, y⟫ < 0
参数：C : ProperCone Real E；hx₀ : x₀ ∉ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperCone.hyperplane_separation_point`：hyperplane_separation_point (C :
 ProperCone Real E) (hx₀ : x₀ ∉ C) : exists f : StrongDual Real E, (forall x in 
C, 0 <= f x) ∧ f x₀ < 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones.
-/
theorem hyperplane_separation' (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ y, (∀ x ∈ C, 0 ≤ ⟪x, y⟫) ∧ ⟪x₀, y⟫ < 0 := by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, ?_⟩
  simpa [← real_inner_comm _ ((InnerProductSpace.toDual ℝ E).symm f), *]

@[deprecated (since := "2026-03-23")] alias
  _root_.ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem :=
  hyperplane_separation'

/-- The inner dual of inner dual of a proper cone is itself. -/
/-
**ProperCone.innerDual_innerDual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : CompleteSpace E]   (C : ProperCone ℝ E), ProperCone.innerDual ↑(
ProperCone.innerDual ↑C) = C
参数：C : ProperCone ℝ E；ProperCone.innerDual ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsContPerfPair`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : TopologicalSpace R]   [inst_2 : AddCommG
roup M] [inst_3 : _root…
· 使用定理 `InnerProductSpace.instIsContPerfPairRealInnerₗOfCompleteSpace`：∀ (E : Ty
pe u_2) [inst : NormedAddCommGroup E] [CompleteSpace E] [inst_2 : InnerProductSp
ace ℝ E],   (innerₗ E).IsContPerfPair
· 使用定理 `flip_innerₗ`：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [inst_1 
: InnerProductSpace ℝ F], (innerₗ F).flip = innerₗ F
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProperCone.dual.congr_simp`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_
3} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [i
nst_3 : Topologi…
· 使用定理 `ProperCone.dual_flip_dual`：∀ {E : Type u_1} {F : Type u_2} [inst : Topol
ogicalSpace E] [inst_1 : AddCommGroup E] [IsTopologicalAddGroup E]   [inst_3 : T
opologicalSpace…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The inner dual of inner dual of a proper cone is itself.
-/
@[simp] theorem innerDual_innerDual (C : ProperCone ℝ E) :
    innerDual (innerDual (C : Set E)) = C := by
  simpa using! C.dual_flip_dual (innerₗ E)

open scoped InnerProductSpace

/-- Relative geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
/-
**ProperCone.relative_hyperplane_separation** 是 Mathlib 中的一个定理，位于命名空间 `ProperCon
e`。
形式化陈述：relative_hyperplane_separation {C : ProperCone Real E} {f : E ->L[Real] F}
 {b : F} : b in C.map f ↔ forall y : F, f.adjoint y in innerDual C -> 0 <= ⟪b, y
⟫_Real where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mapsTo_smul_closure`：Submodule.mapsTo_smul_closure (s : Submod
ule R M) (c : R) : Set.MapsTo (c • ·) (closure s : Set M) (closure s)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Continuous.seqContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → SeqCon
tinuous f
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Relative geometric interpretation of **Farkas' lemma**. Also stronger version of
 the
**Hahn-Banach separation theorem** for proper cones.
-/
theorem relative_hyperplane_separation {C : ProperCone ℝ E} {f : E →L[ℝ] F} {b : F} :
    b ∈ C.map f ↔ ∀ y : F, f.adjoint y ∈ innerDual C → 0 ≤ ⟪b, y⟫_ℝ where
  mp := by
    -- suppose `b ∈ C.map f`
    simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
      AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
      ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_restrictScalars', ClosedSubmodule.coe_toSubmodule,
      ClosedSubmodule.mem_mk, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, Classical.skolem, forall_and,
      mem_innerDual, ContinuousLinearMap.adjoint_inner_right, forall_exists_index, and_imp]
          -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
    rintro x seq hmem hx htends y hinner
    obtain rfl : f ∘ seq = x := funext hx
    have h n : 0 ≤ ⟪f (seq n), y⟫_ℝ := by simpa [real_inner_comm] using hinner (hmem n)
    exact ge_of_tendsto' ((continuous_id.inner continuous_const).seqContinuous htends) h
  mpr h := by
    -- By contradiction, suppose `b ∉ C.map f`.
    contrapose! h
    -- as `b ∉ C.map f`, there is a hyperplane `y` separating `b` from `C.map f`
    obtain ⟨y, hxy, hyb⟩ := (C.map f).hyperplane_separation' h
    -- the rest of the proof is a straightforward algebraic manipulation
    refine ⟨y, fun x hx ↦ ?_, hyb⟩
    simpa [ContinuousLinearMap.adjoint_inner_right]
      using hxy (f x) (subset_closure <| mem_image_of_mem _ hx)
/-
**ProperCone.hyperplane_separation_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `ProperCo
ne`。
形式化陈述：hyperplane_separation_of_notMem (K : ProperCone Real E) {f : E ->L[Real] F
} {b : F} (disj : b ∉ K.map f) : exists y : F, ContinuousLinearMap.adjoint f y i
n innerDual K ∧ ⟪b, y⟫_Real < 0
参数：K : ProperCone Real E；disj : b ∉ K.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProperCone.relative_hyperplane_separation`：relative_hyperplane_separatio
n {C : ProperCone Real E} {f : E ->L[Real] F} {b : F} : b in C.map f ↔ forall y 
: F, f.adjoint y in innerDual C…
-/
theorem hyperplane_separation_of_notMem (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) :
    ∃ y : F, ContinuousLinearMap.adjoint f y ∈ innerDual K ∧ ⟪b, y⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.relative_hyperplane_separation]

end ProperCone

