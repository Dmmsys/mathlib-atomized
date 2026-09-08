/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The topological dual of a cone and Farkas' lemma

Given a continuous bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`,
we define `ProperCone.dual p C` to be the proper cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone.
See `Mathlib/Geometry/Convex/Cone/Dual.lean` for that case.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. This is developed here.

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
As a corollary, we prove that the double dual of a proper cone is itself.

## Main statements

We prove the following theorems:
* `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`: Farkas lemma.
* `ProperCone.dual_dual_flip`, `ProperCone.dual_flip_dual`: The double dual of a proper cone.

## References

* https://en.wikipedia.org/wiki/Hyperplane_separation_theorem
* https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Set LinearMap Pointwise

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [TopologicalSpace R] [ClosedIciTopology R]
  [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} {s : Set M}

/-
**PointedCone.isClosed_dual** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：isClosed_dual (hp : forall x, Continuous (p x)) : IsClosed (dual p s : Set
 N)
参数：hp : forall x, Continuous (p x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PointedCone.dual_iUnion`：dual_iUnion {ι : Sort*} (f : ι -> Set M) : dual
 p (⋃ i, f i) = ⨅ i, dual p (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsOrderedRing.toIsOrderedModule`：∀ {α : Type u_1} [inst : Semiring α] [i
nst_1 : PartialOrder α] [IsOrderedRing α], IsOrderedModule α α
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `PointedCone.dual_singleton`：dual_singleton (x : M) : dual p {x} = (posit
ive R R).comap (p x)
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
-/
lemma isClosed_dual (hp : ∀ x, Continuous (p x)) : IsClosed (dual p s : Set N) := by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.coe_iInf, dual_singleton]
  exact isClosed_biInter fun x hx ↦ isClosed_Ici.preimage <| hp _

end PointedCone

namespace ProperCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [ClosedIciTopology R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} [p.IsContPerfPair] {s t : Set M} {y : N}

variable (p s) in
/-- The dual cone of a set `s` with respect to a perfect pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
/-
**ProperCone.dual** 是 Mathlib 中的一个定义，位于命名空间 `ProperCone`。
形式化陈述：dual (s : Set M) : ProperCone R N where toSubmodule
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual cone of a set `s` with respect to a perfect pairing `p` is the cone con
sisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`.
-/
def dual (s : Set M) : ProperCone R N where
  toSubmodule := PointedCone.dual p s
  isClosed' := PointedCone.isClosed_dual fun _ ↦ p.continuous_of_isContPerfPair
/-
**ProperCone.mem_dual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : TopologicalSpace R] [i
nst_4 : ClosedIciTopology R] [inst_5 : AddCommGroup M] [inst_6 : _root_.Module R
 M]   [inst_7 : TopologicalSpace M] [inst_8 : AddCommGroup N] [inst_9 : _root_.M
odule R N] [inst_10 : TopologicalSpace N]   {p : M →ₗ[R] N →ₗ[R] R} [inst_11 : p
.IsContPerfPair] {s : Set M} {y : N},   y ∈ ProperCone.dual p s ↔ ∀ ⦃x : M⦄, x ∈
 s → 0 ≤ (p x) y
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl
/-
**ProperCone.dual_empty** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : TopologicalSpace R] [i
nst_4 : ClosedIciTopology R] [inst_5 : AddCommGroup M] [inst_6 : _root_.Module R
 M]   [inst_7 : TopologicalSpace M] [inst_8 : AddCommGroup N] [inst_9 : _root_.M
odule R N] [inst_10 : TopologicalSpace N]   {p : M →ₗ[R] N →ₗ[R] R} [inst_11 : p
.IsContPerfPair], ProperCone.dual p ∅ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
/-
**ProperCone.dual_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : TopologicalSpace R] [i
nst_4 : ClosedIciTopology R] [inst_5 : AddCommGroup M] [inst_6 : _root_.Module R
 M]   [inst_7 : TopologicalSpace M] [inst_8 : AddCommGroup N] [inst_9 : _root_.M
odule R N] [inst_10 : TopologicalSpace N]   {p : M →ₗ[R] N →ₗ[R] R} [inst_11 : p
.IsContPerfPair], ProperCone.dual p 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp
/-
**ProperCone.dual_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : TopologicalSpace R] [i
nst_4 : ClosedIciTopology R] [inst_5 : AddCommGroup M] [inst_6 : _root_.Module R
 M]   [inst_7 : TopologicalSpace M] [inst_8 : AddCommGroup N] [inst_9 : _root_.M
odule R N] [inst_10 : TopologicalSpace N]   {p : M →ₗ[R] N →ₗ[R] R} [inst_11 : p
.IsContPerfPair] [IsTopologicalRing R] [inst_13 : T1Space N],   ProperCone.dual 
p Set.univ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `LinearMap.flip.instIsContPerfPair`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : TopologicalSpace R]   [inst_2 : AddCommG
roup M] [inst_3 : _root…
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma dual_univ [IsTopologicalRing R] [T1Space N] : dual p univ = ⊥ := by
  refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff _ p.flip.toContPerfPair.injective).1 ?_)
    (by simp)
  ext x
  exact (hy <| mem_univ x).antisymm' <| by simpa using hy <| mem_univ (-x)
/-
**ProperCone.dual_le_dual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : TopologicalSpace R] [i
nst_4 : ClosedIciTopology R] [inst_5 : AddCommGroup M] [inst_6 : _root_.Module R
 M]   [inst_7 : TopologicalSpace M] [inst_8 : AddCommGroup N] [inst_9 : _root_.M
odule R N] [inst_10 : TopologicalSpace N]   {p : M →ₗ[R] N →ₗ[R] R} [inst_11 : p
.IsContPerfPair] {s t : Set M}, t ⊆ s → ProperCone.dual p s ≤ ProperCone.dual p 
t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
/-
**ProperCone.dual_singleton** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：dual_singleton [IsTopologicalRing R] [OrderClosedTopology R] (x : M) : dua
l p {x} = (positive R R).comap (p.toContPerfPair x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsOrderedRing.toIsOrderedModule`：∀ {α : Type u_1} [inst : Semiring α] [i
nst_1 : PartialOrder α] [IsOrderedRing α], IsOrderedModule α α
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
linear map `p x`.
-/
lemma dual_singleton [IsTopologicalRing R] [OrderClosedTopology R] (x : M) :
    dual p {x} = (positive R R).comap (p.toContPerfPair x) := by ext; simp
/-
**ProperCone.dual_union** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：dual_union (s t : Set M) : dual p (s union t) = dual p s ⊓ dual p t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ProperCone.ext`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [ins
t_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [i
nst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop
/-
**ProperCone.dual_insert** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual 
p s
参数：x : M；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用引理 `ProperCone.dual_union`：dual_union (s t : Set M) : dual p (s union t) = d
ual p s ⊓ dual p t
-/
lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]
/-
**ProperCone.dual_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：dual_iUnion {ι : Sort*} (f : ι -> Set M) : dual p (⋃ i, f i) = ⨅ i, dual p
 (f i)
参数：f : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_comm (α := M)]
/-
**ProperCone.dual_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S)
参数：S : Set (Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_comm (α := M)]

/-- Any set is a subset of its double dual cone. -/
/-
**ProperCone.subset_dual_dual** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：subset_dual_dual : s subseteq dual p.flip (dual p s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Any set is a subset of its double dual cone.
-/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

end ProperCone

namespace ProperCone
variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Module ℝ F]
  {K : Set E} {x₀ : E}

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
/-
**ProperCone.hyperplane_separation** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：hyperplane_separation (C : ProperCone Real E) (hKconv : Convex Real K) (hK
comp : IsCompact K) (hKC : Disjoint K C) : exists f : StrongDual Real E, (forall
 x in C, 0 <= f x) ∧ forall x in K, f x < 0
参数：C : ProperCone Real E；hKconv : Convex Real K；hKcomp : IsCompact K；hKC : Disjo
int K C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compact_clos
ed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ : IsClos
ed t) (disj : Disjoint s t…
· 使用定理 `ProperCone.convex`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [
inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E]
 [inst_…
· 使用定理 `ProperCone.isClosed`：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid 
E] [inst_…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones.
-/
theorem hyperplane_separation (C : ProperCone ℝ E) (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    (hKC : Disjoint K C) : ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0 := by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
  refine ⟨f, fun x hx ↦ ?_, fun x hx ↦ (hu x hx).trans_le <| huv.le.trans hv₀.le⟩
  by_contra! hx₀
  simpa [hx₀.ne] using hv ((v * (f x)⁻¹) • x)
    (C.smul_mem hx <| le_of_lt <| mul_pos_of_neg_of_neg hv₀ <| inv_neg''.2 hx₀)

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
/-
**ProperCone.hyperplane_separation_point** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：hyperplane_separation_point (C : ProperCone Real E) (hx₀ : x₀ ∉ C) : exist
s f : StrongDual Real E, (forall x in C, 0 <= f x) ∧ f x₀ < 0
参数：C : ProperCone Real E；hx₀ : x₀ ∉ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProperCone.hyperplane_separation`：hyperplane_separation (C : ProperCone 
Real E) (hKconv : Convex Real K) (hKcomp : IsCompact K) (hKC : Disjoint K C) : e
xists f : StrongDual R…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…

--- 原说明 ---
Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones.
-/
theorem hyperplane_separation_point (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0 := by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

/-- The **double dual of a proper cone** is itself. -/
/-
**ProperCone.dual_flip_dual** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : TopologicalSpace E] [inst_1 : AddC
ommGroup E] [IsTopologicalAddGroup E]   [inst_3 : TopologicalSpace F] [inst_4 : 
AddCommGroup F] [inst_5 : _root_.Module ℝ E] [ContinuousSMul ℝ E]   [LocallyConv
exSpace ℝ E] [inst_8 : _root_.Module ℝ F] (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [inst_9 : p.Is
ContPerfPair]   (C : ProperCone ℝ E), ProperCone.dual p.flip ↑(ProperCone.dual p
 ↑C) = C
参数：p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ；C : ProperCone ℝ E；ProperCone.dual p ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LinearMap.flip.instIsContPerfPair`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : TopologicalSpace R]   [inst_2 : AddCommG
roup M] [inst_3 : _root…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `ProperCone.hyperplane_separation_point`：hyperplane_separation_point (C :
 ProperCone Real E) (hx₀ : x₀ ∉ C) : exists f : StrongDual Real E, (forall x in 
C, 0 <= f x) ∧ f x₀ < 0
· 使用引理 `ProperCone.subset_dual_dual`：subset_dual_dual : s subseteq dual p.flip (
dual p s)

--- 原说明 ---
The **double dual of a proper cone** is itself.
-/
@[simp] theorem dual_flip_dual (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [p.IsContPerfPair] (C : ProperCone ℝ E) :
    dual p.flip (dual p (C : Set E)) = C := by
  refine le_antisymm (fun x ↦ ?_) subset_dual_dual
  simp only [mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.toContPerfPair.surjective.exists] using C.hyperplane_separation_point

/-- The **double dual of a proper cone** is itself. -/
/-
**ProperCone.dual_dual_flip** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : TopologicalSpace E] [inst_1 : AddC
ommGroup E] [IsTopologicalAddGroup E]   [inst_3 : TopologicalSpace F] [inst_4 : 
AddCommGroup F] [inst_5 : _root_.Module ℝ E] [ContinuousSMul ℝ E]   [LocallyConv
exSpace ℝ E] [inst_8 : _root_.Module ℝ F] (p : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) [inst_9 : p.Is
ContPerfPair]   (C : ProperCone ℝ E), ProperCone.dual p ↑(ProperCone.dual p.flip
 ↑C) = C
参数：p : F →ₗ[ℝ] E →ₗ[ℝ] ℝ；C : ProperCone ℝ E；ProperCone.dual p.flip ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ProperCone.dual_flip_dual`：∀ {E : Type u_1} {F : Type u_2} [inst : Topol
ogicalSpace E] [inst_1 : AddCommGroup E] [IsTopologicalAddGroup E]   [inst_3 : T
opologicalSpace…
· 使用定理 `LinearMap.flip.instIsContPerfPair`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : TopologicalSpace R]   [inst_2 : AddCommG
roup M] [inst_3 : _root…

--- 原说明 ---
The **double dual of a proper cone** is itself.
-/
@[simp] theorem dual_dual_flip (p : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) [p.IsContPerfPair] (C : ProperCone ℝ E) :
    dual p (dual p.flip (C : Set E)) = C := C.dual_flip_dual p.flip

end ProperCone

