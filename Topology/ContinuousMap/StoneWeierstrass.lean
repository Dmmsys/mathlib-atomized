/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Heather Macbeth
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.Order.Module.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topologicalClosure`.
  This follows from the Weierstrass approximation theorem on `[-‖f‖, ‖f‖]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topologicalClosure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topologicalClosure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for star subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/

@[expose] public section

assert_not_exists Unitization

noncomputable section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

open scoped Polynomial

/-- Turn a function `f : C(X, ℝ)` into a continuous map into `Set.Icc (-‖f‖) (‖f‖)`,
thereby explicitly attaching bounds.
-/
/-
**ContinuousMap.attachBound** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：attachBound (f : C(X, Real)) : C(X, Set.Icc (-‖f‖) ‖f‖) where toFun x
参数：f : C(X, Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a function `f : C(X, ℝ)` into a continuous map into `Set.Icc (-‖f‖) (‖f‖)`,
thereby explicitly attaching bounds.
-/
def attachBound (f : C(X, ℝ)) : C(X, Set.Icc (-‖f‖) ‖f‖) where
  toFun x := ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]
/-
**ContinuousMap.attachBound_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：attachBound_apply_coe (f : C(X, Real)) (x : X) : ((attachBound f) x : Real
) = f x
参数：f : C(X, Real)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem attachBound_apply_coe (f : C(X, ℝ)) (x : X) : ((attachBound f) x : ℝ) = f x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMap.polynomial_comp_attachBound** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap`。
形式化陈述：polynomial_comp_attachBound (A : Subalgebra Real C(X, Real)) (f : A) (g : 
Real[X]) : (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, Real)).atta
chBound = Polynomial.aeval f g
参数：A : Subalgebra Real C(X, Real)；f : A；g : Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_subalgebra_coe`：aeval_subalgebra_coe (g : R[X]) {A : Ty
pe*} [Semiring A] [Algebra R A] (s : Subalgebra R A) (f : s) : (aeval f g : A) =
 aeval (f : A) g
· 使用定理 `Polynomial.aeval_continuousMap_apply`：aeval_continuousMap_apply (g : R[X
]) (f : C(α, R)) (x : α) : ((Polynomial.aeval f) g) x = g.eval (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polynomial_comp_attachBound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound =
      Polynomial.aeval f g := by
  ext
  simp only [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  simp

/-- Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `Set.Icc (-‖f‖) ‖f‖)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
/-
**ContinuousMap.polynomial_comp_attachBound_mem** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMap`。
形式化陈述：polynomial_comp_attachBound_mem (A : Subalgebra Real C(X, Real)) (f : A) (
g : Real[X]) : (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, Real)).
attachBound in A
参数：A : Subalgebra Real C(X, Real)；f : A；g : Real[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.polynomial_comp_attachBound`：polynomial_comp_attachBound (
A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X]) : (g.toContinuousMapOn (Se
t.Icc (-‖f‖) ‖f‖)).comp (f : C(…
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p

--- 原说明 ---
Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a
 polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `Set.Icc (
-‖f‖) ‖f‖)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`
.
-/
theorem polynomial_comp_attachBound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem
/-
**ContinuousMap.comp_attachBound_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：comp_attachBound_mem_closure (A : Subalgebra Real C(X, Real)) (f : A) (p :
 C(Set.Icc (-‖f‖) ‖f‖, Real)) : p.comp (attachBound (f : C(X, Real))) in A.topol
ogicalClosure
参数：A : Subalgebra Real C(X, Real)；f : A；p : C(Set.Icc (-‖f‖) ‖f‖, Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuousMap_mem_polynomialFunctions_closure`：continuousMap_mem_polynom
ialFunctions_closure (a b : Real) (f : C(Set.Icc a b, Real)) : f in (polynomialF
unctions (Set.Icc a b)).topological…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Tendsto.frequently_map`：∀ {α : Type u_1} {β : Type u_2} {l₁ : Fil
ter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop} (f : α → β),   Filter.Tends
to f l₁ l₂ → (∀ (x …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousMap.continuousAt`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] (f : C(α, β)) (x : α),   Continuou
sAt (⇑f) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toContinuousMapOnAlgHom_apply`：∀ {R : Type u_1} [inst : CommS
emiring R] [inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (X :
 Set R)   (p : Polynomial R), …
· 使用定理 `ContinuousMap.polynomial_comp_attachBound_mem`：polynomial_comp_attachBou
nd_mem (A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X]) : (g.toContinuousM
apOn (Set.Icc (-‖f‖) ‖f‖)).comp (f …
-/
theorem comp_attachBound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A)
    (p : C(Set.Icc (-‖f‖) ‖f‖, ℝ)) : p.comp (attachBound (f : C(X, ℝ))) ∈ A.topologicalClosure := by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  -- To prove `p.comp (attachBound f)` is in the closure of `A`,
  -- we show there are elements of `A` arbitrarily close.
  apply mem_closure_iff_frequently.mpr
  -- To show that, we pull back the polynomials close to `p`,
  refine
    ((compRightContinuousMap ℝ (attachBound (f : C(X, ℝ)))).continuousAt
            p).tendsto.frequently_map
      _ ?_ frequently_mem_polynomials
  -- but need to show that those pullbacks are actually in `A`.
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_toRingHom,
    Polynomial.toContinuousMapOnAlgHom_apply]
  apply polynomial_comp_attachBound_mem
/-
**ContinuousMap.abs_mem_subalgebra_closure** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：abs_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f : A) : |(f 
: C(X, Real))| in A.topologicalClosure
参数：A : Subalgebra Real C(X, Real)；f : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1 : A
ddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopology 
G] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousMap.comp_attachBound_mem_closure`：comp_attachBound_mem_closure
 (A : Subalgebra Real C(X, Real)) (f : A) (p : C(Set.Icc (-‖f‖) ‖f‖, Real)) : p.
comp (attachBound (f : C(X, Real…
-/
theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) :
    |(f : C(X, ℝ))| ∈ A.topologicalClosure := by
  let f' := attachBound (f : C(X, ℝ))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, ℝ) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : ℝ)| }
  change abs.comp f' ∈ A.topologicalClosure
  apply comp_attachBound_mem_closure
/-
**ContinuousMap.inf_mem_subalgebra_closure** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：inf_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f g : A) : (f
 : C(X, Real)) ⊓ (g : C(X, Real)) in A.topologicalClosure
参数：A : Subalgebra Real C(X, Real)；f g : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inf_eq_half_smul_add_sub_abs_sub'`：inf_eq_half_smul_add_sub_abs_sub' (x 
y : M) : x ⊓ y = (2⁻¹ : 𝕜) • (x + y - |y - x|)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousMap.instIsOrderedAddMonoid`：∀ {α : Type u_1} [inst : Topologic
alSpace α] {β : Type u_2} [inst_1 : TopologicalSpace β] [inst_2 : PartialOrder β
]   [inst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.le_topologicalClosure`：Subalgebra.le_topologicalClosure (s : 
Subalgebra R A) : s <= s.topologicalClosure
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousMap.abs_mem_subalgebra_closure`：abs_mem_subalgebra_closure (A 
: Subalgebra Real C(X, Real)) (f : A) : |(f : C(X, Real))| in A.topologicalClosu
re
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _
/-
**ContinuousMap.inf_mem_closed_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：inf_mem_closed_subalgebra (A : Subalgebra Real C(X, Real)) (h : IsClosed (
A : Set C(X, Real))) (f g : A) : (f : C(X, Real)) ⊓ (g : C(X, Real)) in A
参数：A : Subalgebra Real C(X, Real)；h : IsClosed (A : Set C(X, Real))；f g : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.topologicalClosure_coe`：∀ {R : Type u_1} [inst : CommSemiring
 R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   [inst_3
 : Algebra R A] [inst_4…
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `ContinuousMap.inf_mem_subalgebra_closure`：inf_mem_subalgebra_closure (A 
: Subalgebra Real C(X, Real)) (f g : A) : (f : C(X, Real)) ⊓ (g : C(X, Real)) in
 A.topologicalClosure
-/
theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A := by
  convert! inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  rw [Subalgebra.topologicalClosure_coe, closure_eq_iff_isClosed]
  exact h
/-
**ContinuousMap.sup_mem_subalgebra_closure** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：sup_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f g : A) : (f
 : C(X, Real)) ⊔ (g : C(X, Real)) in A.topologicalClosure
参数：A : Subalgebra Real C(X, Real)；f g : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sup_eq_half_smul_add_add_abs_sub'`：sup_eq_half_smul_add_add_abs_sub' (x 
y : M) : x ⊔ y = (2⁻¹ : 𝕜) • (x + y + |y - x|)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousMap.instIsOrderedAddMonoid`：∀ {α : Type u_1} [inst : Topologic
alSpace α] {β : Type u_2} [inst_1 : TopologicalSpace β] [inst_2 : PartialOrder β
]   [inst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.le_topologicalClosure`：Subalgebra.le_topologicalClosure (s : 
Subalgebra R A) : s <= s.topologicalClosure
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousMap.abs_mem_subalgebra_closure`：abs_mem_subalgebra_closure (A 
: Subalgebra Real C(X, Real)) (f : A) : |(f : C(X, Real))| in A.topologicalClosu
re
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _
/-
**ContinuousMap.sup_mem_closed_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：sup_mem_closed_subalgebra (A : Subalgebra Real C(X, Real)) (h : IsClosed (
A : Set C(X, Real))) (f g : A) : (f : C(X, Real)) ⊔ (g : C(X, Real)) in A
参数：A : Subalgebra Real C(X, Real)；h : IsClosed (A : Set C(X, Real))；f g : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.sup_mem_subalgebra_closure`：sup_mem_subalgebra_closure (A 
: Subalgebra Real C(X, Real)) (f g : A) : (f : C(X, Real)) ⊔ (g : C(X, Real)) in
 A.topologicalClosure
-/
theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A := by
  convert! sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  simp

open scoped Topology

-- Here's the fun part of Stone-Weierstrass!
/-
**ContinuousMap.sublattice_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：sublattice_closure_eq_top (L : Set C(X, Real)) (nA : L.Nonempty) (inf_mem 
: forallᵉ (f in L) (g in L), f ⊓ g in L) (sup_mem : forallᵉ (f in L) (g in L), f
 ⊔ g in L) (sep : L.SeparatesPointsStrongly) : closure L = ⊤
参数：L : Set C(X, Real)；nA : L.Nonempty；inf_mem : forallᵉ (f in L) (g in L), f ⊓ g
 in L；sup_mem : forallᵉ (f in L) (g in L), f ⊔ g in L；sep : L.SeparatesPointsStr
ongly。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Filter.Frequently.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {x : X} {s : Set X}, (∃ᶠ (x : X) in nhds x, x ∈ s) → x ∈ closure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CompactSpace.elim_nhds_subcover`：CompactSpace.elim_nhds_subcover [Compac
tSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x) : exists t : Finset X, ⋃ 
x in t, U x = ⊤
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.nonempty_of_union_eq_top_of_nonempty`：nonempty_of_union_eq_top_of_no
nempty {ι : Type*} (t : Set ι) (s : ι -> Set α) (H : Nonempty α) (w : ⋃ i in t, 
s i = ⊤) : t.Nonempty
（共 57 条，此处仅展示前 30 条）
-/
theorem sublattice_closure_eq_top (L : Set C(X, ℝ)) (nA : L.Nonempty)
    (inf_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊓ g ∈ L)
    (sup_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊔ g ∈ L) (sep : L.SeparatesPointsStrongly) :
    closure L = ⊤ := by
  -- We start by boiling down to a statement about close approximation.
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [Metric.mem_ball]
  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases nX : Nonempty X
  swap
  · exact ⟨nA.some, (dist_lt_iff pos).mpr fun x => False.elim (nX ⟨x⟩), nA.choose_spec⟩
  /-
    The strategy now is to pick a family of continuous functions `g x y` in `A`
    with the property that `g x y x = f x` and `g x y y = f y`
    (this is immediate from `h : SeparatesPointsStrongly`)
    then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
    and finally using compactness to produce the desired function `h`
    as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
    -/
  dsimp only [Set.SeparatesPointsStrongly] at sep
  choose g hg w₁ w₂ using sep f
  -- For each `x y`, we define `U x y` to be `{z | f z - ε < g x y z}`,
  -- and observe this is a neighbourhood of `y`.
  let U : X → X → Set X := fun x y => {z | f z - ε < g x y z}
  have U_nhds_y : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · rw [Set.mem_ofPred_eq, w₂]
      exact sub_lt_self _ pos
  -- Fixing `x` for a moment, we have a family of functions `fun y ↦ g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions
  -- indexed by a finite collection of patches which cover `X`
  -- will give us an element of `A` that is globally greater than `f z - ε`
  -- and still equal to `f x` at `x`.
  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : X → Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose
  let ys_w : ∀ x, ⋃ y ∈ ys x, U x y = ⊤ := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose_spec
  have ys_nonempty : ∀ x, (ys x).Nonempty := fun x =>
    Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere
  -- and `h x x = f x`.
  let h : X → L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, ℝ)),
      Finset.sup'_mem _ sup_mem _ _ _ fun y _ => hg x y⟩
  have lt_h : ∀ x z, f z - ε < (h x : X → ℝ) z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp [h]
    simp only [coe_sup', Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : ∀ x, (h x : X → ℝ) x = f x := by intro x; simp [h, w₁]
  -- For each `x`, we define `W x` to be `{z | h x z < f z + ε}`,
  let W : X → Set X := fun x => {z | (h x : X → ℝ) z < f z + ε}
  -- This is still a neighbourhood of `x`.
  have W_nhds : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · dsimp only [W, Set.mem_ofPred_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ pos
  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhds).choose
  let xs_w : ⋃ x ∈ xs, W x = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhds).choose_spec
  have xs_nonempty : xs.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, ℝ)),
      Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine ⟨k.1, ?_, k.2⟩
  -- We just need to verify the bound, which we do pointwise.
  rw [dist_lt_iff pos]
  intro z
  -- We rewrite into this particular form,
  -- so that simp lemmas about inequalities involving `Finset.inf'` can fire.
  rw [show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a by
        intros; simp only [← Metric.mem_ball, Real.ball_eq_Ioo, Set.mem_Ioo, and_comm]]
  constructor
  · simp only [k, Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
  · simp only [k, Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    rintro x -
    apply lt_h

/-- The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
@[wikidata Q939927]
/-
**ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints** 是 Math
lib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：subalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra Re
al C(X, Real)) (w : A.SeparatesPoints) : A.topologicalClosure = ⊤
参数：A : Subalgebra Real C(X, Real)；w : A.SeparatesPoints。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Subalgebra.le_topologicalClosure`：Subalgebra.le_topologicalClosure (s : 
Subalgebra R A) : s <= s.topologicalClosure
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.sublattice_closure_eq_top`：sublattice_closure_eq_top (L : 
Set C(X, Real)) (nA : L.Nonempty) (inf_mem : forallᵉ (f in L) (g in L), f ⊓ g in
 L) (sup_mem : forallᵉ (f in …
· 使用定理 `ContinuousMap.inf_mem_closed_subalgebra`：inf_mem_closed_subalgebra (A : 
Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real))) (f g : A) : (f :
 C(X, Real)) ⊓ (g : C(X, Real…
· 使用定理 `Subalgebra.isClosed_topologicalClosure`：Subalgebra.isClosed_topologicalC
losure (s : Subalgebra R A) : IsClosed (s.topologicalClosure : Set A)
· 使用定理 `ContinuousMap.sup_mem_closed_subalgebra`：sup_mem_closed_subalgebra (A : 
Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real))) (f g : A) : (f :
 C(X, Real)) ⊔ (g : C(X, Real…
· 使用定理 `Subalgebra.SeparatesPoints.strongly`：Subalgebra.SeparatesPoints.strongly
 {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) : (s : Set C(α, 𝕜)).Separate
sPointsStrongly
· 使用定理 `Subalgebra.separatesPoints_monotone`：Subalgebra.separatesPoints_monotone
 : Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints

--- 原说明 ---
The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.le_topologicalClosure A.one_mem⟩
  convert!
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly
        (Subalgebra.separatesPoints_monotone A.le_topologicalClosure w))
  simp [L]

/-- An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
/-
**ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints** 是 Math
lib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra Re
al C(X, Real)) (w : A.SeparatesPoints) (f : C(X, Real)) : f in A.topologicalClos
ure
参数：A : Subalgebra Real C(X, Real)；w : A.SeparatesPoints；f : C(X, Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`：s
ubalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra Real C(X,
 Real)) (w : A.SeparatesPoints) : A.topologicalClosure = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `
A`.
-/
theorem continuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) : f ∈ A.topologicalClosure := by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
/-
**ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints** 是 
Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebr
a Real C(X, Real)) (w : A.SeparatesPoints) (f : C(X, Real)) (ε : Real) (pos : 0 
< ε) : exists g : A, ‖(g : C(X, Real)) - f‖ < ε
参数：A : Subalgebra Real C(X, Real)；w : A.SeparatesPoints；f : C(X, Real)；ε : Real；
pos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints`：c
ontinuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra Real C(X,
 Real)) (w : A.SeparatesPoints) (f : C(X, Real)) : f in A.t…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε

--- 原说明 ---
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some eleme
nt of `A`.
-/
theorem exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ‖(g : C(X, ℝ)) - f‖ < ε := by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
/-
**ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints** 是 Mat
hlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra R
eal C(X, Real)) (w : A.SeparatesPoints) (f : X -> Real) (c : Continuous f) (ε : 
Real) (pos : 0 < ε) : exists g : A, forall x, ‖(g : X -> Real) x - f x‖ < ε
参数：A : Subalgebra Real C(X, Real)；w : A.SeparatesPoints；f : X -> Real；c : Contin
uous f；ε : Real；pos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoint
s`：exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebra R
eal C(X, Real)) (w : A.SeparatesPoints) (f : C(X, Real)) (ε : R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_lt_iff`：norm_lt_iff {M : Real} (M0 : 0 < M) : ‖f‖ < M
 ↔ forall x, ‖f x‖ < M

--- 原说明 ---
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some eleme
nt of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ∀ x, ‖(g : X → ℝ) x - f x‖ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b

/-- A variant of the Stone-Weierstrass theorem where `X` need not be compact:
If `A` is a subalgebra of `C(X, ℝ)` which separates points, then, for any compact set `K ⊆ X`,
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A` on `K`. -/
/-
**ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesP
oints** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints {X :
 Type*} [TopologicalSpace X] {A : Subalgebra Real C(X, Real)} (hA : A.SeparatesP
oints) (f : C(X, Real)) {K : Set X} (hK : IsCompact K) {ε : Real} (pos : 0 < ε) 
: exists g in A, forall x in K, ‖(g : X -> Real) x - f x‖ < ε
参数：X, Real；hA : A.SeparatesPoints；f : C(X, Real)；hK : IsCompact K；pos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.mem_map`：mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B
} : y in map f S ↔ exists x in S, f x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMap.compStarAlgHom'_apply`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (𝕜 : Type u_4)   [inst_2 
: CommSemiring 𝕜] (A : Ty…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`：
exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra Real C(
X, Real)) (w : A.SeparatesPoints) (f : X -> Real) (c : Conti…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A variant of the Stone-Weierstrass theorem where `X` need not be compact:
If `A` is a subalgebra of `C(X, ℝ)` which separates points, then, for any compac
t set `K ⊆ X`,
every real-valued continuous function on `X` is within any `ε > 0` of some eleme
nt of `A` on `K`.
-/
theorem exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    {X : Type*} [TopologicalSpace X] {A : Subalgebra ℝ C(X, ℝ)} (hA : A.SeparatesPoints)
    (f : C(X, ℝ)) {K : Set X} (hK : IsCompact K) {ε : ℝ} (pos : 0 < ε) :
    ∃ g ∈ A, ∀ x ∈ K, ‖(g : X → ℝ) x - f x‖ < ε := by
  let restrict_on_K : C(X, ℝ) →⋆ₐ[ℝ] C(K, ℝ) :=
    ContinuousMap.compStarAlgHom' ℝ ℝ ⟨(Subtype.val), continuous_subtype_val⟩
  --consider the subalgebra AK of functions with domain K
  let AK : Subalgebra ℝ C(K, ℝ) := Subalgebra.map restrict_on_K A
  have hsep : AK.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨g, hg1, hg2⟩, hg_sep⟩ := hA (Subtype.coe_ne_coe.mpr hxy)
    simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and]
    use restrict_on_K g
    refine ⟨Subalgebra.mem_map.mpr ?_,
      by simpa only [compStarAlgHom'_apply, comp_apply, coe_mk, ne_eq, restrict_on_K, hg2]⟩
    use g, hg1
    simp
  obtain ⟨⟨gK, hgKAK⟩, hgapprox⟩ :=
    @ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _ _
    (isCompact_iff_compactSpace.mp hK) AK hsep (K.domRestrict f)
    (ContinuousOn.domRestrict (Continuous.continuousOn f.continuous)) ε pos
  obtain ⟨g, hgA, hgKAK⟩ := Subalgebra.mem_map.mp hgKAK
  use g, hgA
  intro x hxK
  have eqg : g x = gK ⟨x, hxK⟩ := by
    rw [← hgKAK]; rfl
  rw [eqg]
  exact hgapprox ⟨x, hxK⟩

end ContinuousMap

section RCLike

open RCLike

-- Redefine `X`, since for the next lemma it need not be compact
variable {𝕜 : Type*} {X : Type*} [RCLike 𝕜] [TopologicalSpace X]

open ContinuousMap

/- a post-port refactor eliminated `conjInvariantSubalgebra`, which was only used to
state and prove the Stone-Weierstrass theorem, in favor of using `StarSubalgebra`s,
which didn't exist at the time Stone-Weierstrass was written. -/


set_option backward.isDefEq.respectTransparency false in
/-- If a star subalgebra of `C(X, 𝕜)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
/-
**Subalgebra.SeparatesPoints.rclike_to_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.SeparatesPoints.rclike_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)} (
hA : A.SeparatesPoints) : ((A.restrictScalars Real).comap (ofRealAm.compLeftCont
inuous Real continuous_ofReal)).SeparatesPoints
参数：X, 𝕜；hA : A.SeparatesPoints。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `RCLike.continuous_ofReal`：continuous_ofReal : Continuous (ofReal : Real 
-> K)
· 使用定理 `ContinuousMap.instIsScalarTower`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.one_apply`：one_apply [One β] (x : α) : (1 : C(α, β)) x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StarSubalgebra.smul_mem`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSem
iring R] [inst_1 : StarRing R] [inst_2 : Semiring A]   [inst_3 : StarRing A] [in
st_4 : Algebr…
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If a star subalgebra of `C(X, 𝕜)` separates points, then the real subalgebra
of its purely real-valued elements also separates points.
-/
theorem Subalgebra.SeparatesPoints.rclike_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)}
    (hA : A.SeparatesPoints) :
      ((A.restrictScalars ℝ).comap
        (ofRealAm.compLeftContinuous ℝ continuous_ofReal)).SeparatesPoints := by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F ∈ A := by
    refine A.sub_mem hfA (@Eq.subst _ (· ∈ A) _ _ ?_ <| A.smul_mem A.one_mem <| f x₂)
    ext1
    simp only [ContinuousMap.smul_apply, one_apply, smul_eq_mul, mul_one,
      const_apply]
  -- Consider now the function `fun x ↦ |f x - f x₂| ^ 2`
  refine ⟨_, ⟨⟨(‖F ·‖ ^ 2), by fun_prop⟩, ?_, rfl⟩, ?_⟩
  · -- This is also an element of the subalgebra, and takes only real values
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert! (A.restrictScalars ℝ).mul_mem hFA (star_mem hFA : star F ∈ A)
    ext1
    simp [← RCLike.mul_conj]
  · -- And it also separates the points `x₁`, `x₂`
    simpa [F] using sub_ne_zero.mpr hf

variable [CompactSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- The Stone-Weierstrass approximation theorem, `RCLike` version, that a star subalgebra `A` of
`C(X, 𝕜)`, where `X` is a compact topological space and `RCLike 𝕜`, is dense if it separates
points. -/
/-
**ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints** 是 
Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints 
(A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topologicalClosure =
 ⊤
参数：A : StarSubalgebra 𝕜 C(X, 𝕜)；hA : A.SeparatesPoints。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarSubalgebra.eq_top_iff`：eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔
 forall x : A, x in S
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMap.instContinuousConstSMul`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_
2 : SMul R M] [inst_3 : Con…
· 使用定理 `ContinuousMap.instIsScalarTower`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `RCLike.continuous_ofReal`：continuous_ofReal : Continuous (ofReal : Real 
-> K)
· 使用定理 `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`：s
ubalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra Real C(X,
 Real)) (w : A.SeparatesPoints) : A.topologicalClosure = ⊤
· 使用定理 `Subalgebra.SeparatesPoints.rclike_to_real`：Subalgebra.SeparatesPoints.rc
like_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)} (hA : A.SeparatesPoints) : ((A.restr
ictScalars Real).comap (ofRealA…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
The Stone-Weierstrass approximation theorem, `RCLike` version, that a star subal
gebra `A` of
`C(X, 𝕜)`, where `X` is a compact topological space and `RCLike 𝕜`, is dense if 
it separates
points.
-/
theorem ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  rw [StarSubalgebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, ℝ) →L[ℝ] C(X, 𝕜) := ofRealCLM.compLeftContinuous ℝ X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure of `A`
  have key : I.range ≤ (A.toSubmodule.restrictScalars ℝ).topologicalClosure := by
    -- Let `A₀` be the subalgebra of `C(X, ℝ)` consisting of `A`'s purely real elements; it is the
    -- preimage of `A` under `I`.  In this argument we only need its submodule structure.
    let A₀ : Submodule ℝ C(X, ℝ) := (A.toSubmodule.restrictScalars ℝ).comap I.toLinearMap
    -- By `Subalgebra.SeparatesPoints.rclike_to_real`, this subalgebra also separates points, so
    -- we may apply the real Stone-Weierstrass result to it.
    have SW : A₀.topologicalClosure = ⊤ :=
      haveI := subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hA.rclike_to_real
      congr_arg Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    -- So it suffices to prove that the image under `I` of the closure of `A₀` is contained in the
    -- closure of `A`, which follows by abstract nonsense
    have h₁ := A₀.topologicalClosure_map I
    have h₂ := (A.toSubmodule.restrictScalars ℝ).map_comap_le I.toLinearMap
    exact h₁.trans (Submodule.topologicalClosure_mono h₂)
  -- In particular, for a function `f` in `C(X, 𝕜)`, the real and imaginary parts of `f` are in the
  -- closure of `A`
  intro f
  let f_re : C(X, ℝ) := (⟨RCLike.re, RCLike.reCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨RCLike.im, RCLike.imCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topologicalClosure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topologicalClosure := key ⟨f_im, rfl⟩
  -- So `f_re + I • f_im` is in the closure of `A`
  have := A.topologicalClosure.add_mem h_f_re (A.topologicalClosure.smul_mem h_f_im RCLike.I)
  rw [StarSubalgebra.mem_toSubalgebra] at this
  convert! this
  -- And this, of course, is just `f`
  ext
  apply Eq.symm
  simp [I, f_re, f_im, mul_comm RCLike.I _]

end RCLike

section PolynomialFunctions

open StarSubalgebra Polynomial
open scoped Polynomial

/-- Polynomial functions in are dense in `C(s, ℝ)` when `s` is compact.

See `polynomialFunctions_closure_eq_top` for the special case `s = Set.Icc a b` which does not use
the full Stone-Weierstrass theorem. Of course, that version could be used to prove this one as
well. -/
/-
**polynomialFunctions.topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomialFunctions.topologicalClosure (s : Set Real) [CompactSpace s] : (
polynomialFunctions s).topologicalClosure = ⊤
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`：s
ubalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra Real C(X,
 Real)) (w : A.SeparatesPoints) : A.topologicalClosure = ⊤
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `polynomialFunctions_separatesPoints`：polynomialFunctions_separatesPoints
 (X : Set R) : (polynomialFunctions X).SeparatesPoints

--- 原说明 ---
Polynomial functions in are dense in `C(s, ℝ)` when `s` is compact.

See `polynomialFunctions_closure_eq_top` for the special case `s = Set.Icc a b` 
which does not use
the full Stone-Weierstrass theorem. Of course, that version could be used to pro
ve this one as
well.
-/
theorem polynomialFunctions.topologicalClosure (s : Set ℝ)
    [CompactSpace s] : (polynomialFunctions s).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)

/-- The star subalgebra generated by polynomials functions is dense in `C(s, 𝕜)` when `s` is
compact and `𝕜` is either `ℝ` or `ℂ`. -/
/-
**polynomialFunctions.starClosure_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：polynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] 
(s : Set 𝕜) [CompactSpace s] : (polynomialFunctions s).starClosure.topologicalCl
osure = ⊤
参数：s : Set 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoint
s`：ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (A 
: StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topolo…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `Subalgebra.separatesPoints_monotone`：Subalgebra.separatesPoints_monotone
 : Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `polynomialFunctions_separatesPoints`：polynomialFunctions_separatesPoints
 (X : Set R) : (polynomialFunctions X).SeparatesPoints

--- 原说明 ---
The star subalgebra generated by polynomials functions is dense in `C(s, 𝕜)` whe
n `s` is
compact and `𝕜` is either `ℝ` or `ℂ`.
-/
theorem polynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜)
    [CompactSpace s] : (polynomialFunctions s).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))

open StarAlgebra in
/-
**ContinuousMap.elemental_id_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMap.elemental_id_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Comp
actSpace s] : elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤
参数：s : Set 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAlgebra.elemental.eq_1`：∀ (R : Type u_1) {A : Type u_2} [inst : Comm
Semiring R] [inst_1 : StarRing R] [inst_2 : TopologicalSpace A]   [inst_3 : Semi
ring A] [inst_4 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `polynomialFunctions.starClosure_topologicalClosure`：polynomialFunctions.
starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace 
s] : (polynomialFunctions s).starClosure…
· 使用定理 `polynomialFunctions.starClosure_eq_adjoin_X`：polynomialFunctions.starClo
sure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) : (polynomialFuncti
ons s).starClosure = adjoin R {to…
· 使用引理 `Polynomial.toContinuousMap_X_eq_id`：toContinuousMap_X_eq_id : X.toContin
uousMap = .id R
-/
lemma ContinuousMap.elemental_id_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace s] :
    elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤ := by
  rw [StarAlgebra.elemental, ← polynomialFunctions.starClosure_topologicalClosure,
    polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

/-- An induction principle for `C(s, 𝕜)`. -/
@[elab_as_elim]
/-
**ContinuousMap.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.induction_on {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} {p : C(s, 𝕜)
 -> Prop} (const : forall r, p (.const s r)) (id : p (.restrict s <| .id 𝕜)) (st
ar_id : p (star (.restrict s <| .id 𝕜))) (add : forall f g, p f -> p g -> p (f +
 g)) (mul : forall f g, p f -> p g -> p (f * g)) (closure : (forall f in (polyno
mialFunctions s).starClosure, p f) -> forall f, p f) (f : C(s, 𝕜)) : p f
参数：s, 𝕜；const : forall r, p (.const s r)；id : p (.restrict s <| .id 𝕜)；star_id :
 p (star (.restrict s <| .id 𝕜))；add : forall f g, p f -> p g -> p (f + g)；mul :
 forall f g, p f -> p g -> p (f * g)；closure : (forall f in (polynomialFunctions
 s).starClosure, p f) -> forall f, p f；f : C(s, 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.toContinuousMapOnAlgHom_apply`：∀ {R : Type u_1} [inst : CommS
emiring R] [inst_1 : TopologicalSpace R] [inst_2 : IsTopologicalSemiring R] (X :
 Set R)   (p : Polynomial R), …
· 使用引理 `Polynomial.toContinuousMapOn_X_eq_restrict_id`：toContinuousMapOn_X_eq_re
strict_id (s : Set R) : X.toContinuousMapOn s = restrict s (.id R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `polynomialFunctions.starClosure_eq_adjoin_X`：polynomialFunctions.starClo
sure_eq_adjoin_X [StarRing R] [ContinuousStar R] (s : Set R) : (polynomialFuncti
ons s).starClosure = adjoin R {to…

--- 原说明 ---
An induction principle for `C(s, 𝕜)`.
-/
theorem ContinuousMap.induction_on {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜}
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (closure : (∀ f ∈ (polynomialFunctions s).starClosure, p f) → ∀ f, p f) (f : C(s, 𝕜)) :
    p f := by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    push _ ∈ _ at hf
    rw [star_eq_iff_star_eq, eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id]
  | algebraMap r => exact const r
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg

open Topology in
@[elab_as_elim]
/-
**ContinuousMap.induction_on_of_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.induction_on_of_compact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [
CompactSpace s] {p : C(s, 𝕜) -> Prop} (const : forall r, p (.const s r)) (id : p
 (.restrict s <| .id 𝕜)) (star_id : p (star (.restrict s <| .id 𝕜))) (add : fora
ll f g, p f -> p g -> p (f + g)) (mul : forall f g, p f -> p g -> p (f * g)) (fr
equently : forall f, (existsᶠ g in 𝓝 f, p g) -> p f) (f : C(s, 𝕜)) : p f
参数：s, 𝕜；const : forall r, p (.const s r)；id : p (.restrict s <| .id 𝕜)；star_id :
 p (star (.restrict s <| .id 𝕜))；add : forall f g, p f -> p g -> p (f + g)；mul :
 forall f g, p f -> p g -> p (f * g)；frequently : forall f, (existsᶠ g in 𝓝 f, p
 g) -> p f；f : C(s, 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.induction_on`：ContinuousMap.induction_on {𝕜 : Type*} [RCLi
ke 𝕜] {s : Set 𝕜} {p : C(s, 𝕜) -> Prop} (const : forall r, p (.const s r)) (id :
 p (.restrict s …
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `StarSubalgebra.mem_top`：mem_top {x : A} : x in (⊤ : StarSubalgebra R A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `polynomialFunctions.starClosure_topologicalClosure`：polynomialFunctions.
starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace 
s] : (polynomialFunctions s).starClosure…
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `StarSubalgebra.topologicalClosure_coe`：topologicalClosure_coe (s : StarS
ubalgebra R A) : (s.topologicalClosure : Set A) = closure (s : Set A)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem ContinuousMap.induction_on_of_compact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s]
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)) :
    p f := by
  refine f.induction_on const id star_id add mul fun h f ↦ frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe, topologicalClosure_coe, mem_closure_iff_frequently] at this
  exact this.mp <| .of_forall h

/-- Continuous algebra homomorphisms from `C(s, ℝ)` into an `ℝ`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
/-
**ContinuousMap.algHom_ext_map_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.algHom_ext_map_X {A : Type*} [Semiring A] [Algebra Real A] [
TopologicalSpace A] [T2Space A] {s : Set Real} [CompactSpace s] {φ ψ : C(s, Real
) ->ₐ[Real] A} (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (toContinuousMapOn
AlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ
参数：s, Real；hφ : Continuous φ；hψ : Continuous ψ；h : φ (toContinuousMapOnAlgHom s 
X) = ψ (toContinuousMapOnAlgHom s X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `polynomialFunctions.topologicalClosure`：polynomialFunctions.topologicalC
losure (s : Set Real) [CompactSpace s] : (polynomialFunctions s).topologicalClos
ure = ⊤
· 使用定理 `Subalgebra.topologicalClosure_minimal`：Subalgebra.topologicalClosure_min
imal {s t : Subalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topolog
icalClosure <= t
· 使用定理 `polynomialFunctions.le_equalizer`：polynomialFunctions.le_equalizer {A : 
Type*} [Semiring A] [Algebra R A] (s : Set R) (φ ψ : C(s, R) ->ₐ[R] A) (h : φ (t
oContinuousMapOnAlgHom…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂

--- 原说明 ---
Continuous algebra homomorphisms from `C(s, ℝ)` into an `ℝ`-algebra `A` which ag
ree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal.
-/
theorem ContinuousMap.algHom_ext_map_X {A : Type*} [Semiring A]
    [Algebra ℝ A] [TopologicalSpace A] [T2Space A] {s : Set ℝ} [CompactSpace s]
    {φ ψ : C(s, ℝ) →ₐ[ℝ] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : Subalgebra ℝ C(s, ℝ)) ≤ AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

/-- Continuous star algebra homomorphisms from `C(s, 𝕜)` into a star `𝕜`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
/-
**ContinuousMap.starAlgHom_ext_map_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.starAlgHom_ext_map_X {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [Star
Ring A] [Algebra 𝕜 A] [TopologicalSpace A] [T2Space A] {s : Set 𝕜} [CompactSpace
 s] {φ ψ : C(s, 𝕜) ->⋆ₐ[𝕜] A} (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (to
ContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ
参数：s, 𝕜；hφ : Continuous φ；hψ : Continuous ψ；h : φ (toContinuousMapOnAlgHom s X) 
= ψ (toContinuousMapOnAlgHom s X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `polynomialFunctions.starClosure_topologicalClosure`：polynomialFunctions.
starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace 
s] : (polynomialFunctions s).starClosure…
· 使用定理 `StarSubalgebra.topologicalClosure_minimal`：topologicalClosure_minimal {s
 t : StarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topologica
lClosure <= t
· 使用定理 `polynomialFunctions.starClosure_le_equalizer`：polynomialFunctions.starCl
osure_le_equalizer {A : Type*} [StarRing R] [ContinuousStar R] [Semiring A] [Sta
rRing A] [Algebra R A] (s : Set R)…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `StarSubalgebra.mem_top`：mem_top {x : A} : x in (⊤ : StarSubalgebra R A)

--- 原说明 ---
Continuous star algebra homomorphisms from `C(s, 𝕜)` into a star `𝕜`-algebra `A`
 which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal.
-/
theorem ContinuousMap.starAlgHom_ext_map_X {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
    [Algebra 𝕜 A] [TopologicalSpace A] [T2Space A] {s : Set 𝕜} [CompactSpace s]
    {φ ψ : C(s, 𝕜) →⋆ₐ[𝕜] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) ≤ StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

end PolynomialFunctions

/-! ### Continuous maps sending zero to zero -/

section ContinuousMapZero

variable {𝕜 : Type*} [RCLike 𝕜]
open NonUnitalStarAlgebra Submodule

namespace ContinuousMap

/-
**ContinuousMap.adjoin_id_eq_span_one_union** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMap`。
形式化陈述：adjoin_id_eq_span_one_union (s : Set 𝕜) : ((StarAlgebra.adjoin 𝕜 {(restric
t s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) = span 𝕜 ({(1 : C(s, 𝕜))} union (adjoin 
𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}))
参数：s : Set 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `StarAlgebra.adjoin_nonUnitalStarSubalgebra`：StarAlgebra.adjoin_nonUnital
StarSubalgebra (s : Set A) : adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) 
= adjoin R s
· 使用定理 `StarSubalgebra.mem_toSubalgebra`：mem_toSubalgebra {S : StarSubalgebra R 
A} {x} : x in S.toSubalgebra ↔ x in S
· 使用定理 `Subalgebra.mem_toSubmodule`：mem_toSubmodule {x} : x in (toSubmodule S) ↔
 x in S
· 使用引理 `StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span`：adjoin_nonUnitalStar
Subalgebra_eq_span (s : NonUnitalStarSubalgebra R A) : (adjoin R (s : Set A)).to
Subalgebra.toSubmodule = span R {1} ⊔ s.…
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用引理 `NonUnitalStarAlgebra.span_eq_toSubmodule`：span_eq_toSubmodule {R} [CommS
emiring R] [Module R A] (s : NonUnitalStarSubalgebra R A) : Submodule.span R (s 
: Set A) = s.toSubmodule
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} ∪ (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, span_union, span_eq_toSubmodule]

open scoped Pointwise in
/-
**ContinuousMap.adjoin_id_eq_span_one_add** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：adjoin_id_eq_span_one_add (s : Set 𝕜) : ((StarAlgebra.adjoin 𝕜 {(restrict 
s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) = (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) +
 (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))})
参数：s : Set 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `StarAlgebra.adjoin_nonUnitalStarSubalgebra`：StarAlgebra.adjoin_nonUnital
StarSubalgebra (s : Set A) : adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) 
= adjoin R s
· 使用定理 `StarSubalgebra.mem_toSubalgebra`：mem_toSubalgebra {S : StarSubalgebra R 
A} {x} : x in S.toSubalgebra ↔ x in S
· 使用定理 `Subalgebra.mem_toSubmodule`：mem_toSubmodule {x} : x in (toSubmodule S) ↔
 x in S
· 使用引理 `StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span`：adjoin_nonUnitalStar
Subalgebra_eq_span (s : NonUnitalStarSubalgebra R A) : (adjoin R (s : Set A)).to
Subalgebra.toSubmodule = span R {1} ⊔ s.…
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma adjoin_id_eq_span_one_add (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) := by
  ext x
  rw [SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, mem_sup]
  simp [Set.mem_add]
/-
**ContinuousMap.nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom** 是 Math
lib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 
0 in s) : (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) subseteq RingHom.ker (ev
alStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s))
参数：h0 : 0 in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用引理 `NonUnitalStarAlgebra.adjoin_induction`：adjoin_induction {s : Set A} {p :
 (x : A) -> x in adjoin R s -> Prop} (mem : forall (x : A) (hx : x in s), p x (s
ubset_adjoin R s hx)) (add …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
（共 32 条，此处仅展示前 30 条）
-/
lemma nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 0 ∈ s) :
    (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ⊆
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) := by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_smul, hf, smul_zero]
  | star f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_star, hf, star_zero]
/-
**ContinuousMap.ker_evalStarAlgHom_inter_adjoin_id** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousMap`。
形式化陈述：ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 in s) : (StarAlgebr
a.adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) inter RingHom.ker (evalStarAlgHom
 𝕜 𝕜 (⟨0, h0⟩ : s)) = adjoin 𝕜 {restrict s (.id 𝕜)}
参数：s : Set 𝕜；h0 : 0 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ContinuousMap.adjoin_id_eq_span_one_add`：adjoin_id_eq_span_one_add (s : 
Set 𝕜) : ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜))
 = (span 𝕜 {(1 : C(s, 𝕜))} : …
· 使用引理 `ContinuousMap.nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom`：n
onUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 0 in s)
 : (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) subseteq R…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ContinuousMap.one_apply`：one_apply [One β] (x : α) : (1 : C(α, β)) x = 1
· 使用定理 `ContinuousMap.smul_apply`：smul_apply [SMul R M] [ContinuousConstSMul R M
] (c : R) (f : C(α, M)) (a : α) : (c • f) a = c • f a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousMap.evalStarAlgHom_apply`：∀ {X : Type u_1} (S : Type u_2) (R :
 Type u_3) [inst : TopologicalSpace X] [inst_1 : CommSemiring S]   [inst_2 : Com
mSemiring R] [inst_3 : A…
· 使用定理 `ContinuousMap.add_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolog
icalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Add β]   [inst_3 : Continuo
usAdd β] (f g…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
（共 33 条，此处仅展示前 30 条）
-/
lemma ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) :
    (StarAlgebra.adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ∩
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) = adjoin 𝕜 {restrict s (.id 𝕜)} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    simp only [SetLike.mem_coe, RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply, this, add_zero, smul_apply, one_apply, smul_eq_mul, mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf ↦ ⟨?_, nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf⟩
    exact adjoin_le_starAlgebra_adjoin _ _ hf

set_option backward.isDefEq.respectTransparency false in
-- the statement should be in terms of nonunital subalgebras, but we lack API
open RingHom Filter Topology in
/-
**ContinuousMap.AlgHom.closure_ker_inter** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.AlgHom`。
形式化陈述：∀ {F : Type u_2} {S : Type u_3} {K : Type u_4} {A : Type u_5} [inst : Comm
Ring K] [inst_1 : Ring A]   [inst_2 : Algebra K A] [inst_3 : TopologicalSpace K]
 [T1Space K] [inst_5 : TopologicalSpace A] [ContinuousSub A]   [ContinuousSMul K
 A] [inst_8 : FunLike F A K] [inst_9 : AlgHomClass F K A K] [inst_10 : SetLike S
 A] [OneMemClass S A]   [AddSubgroupClass S A] [SMulMemClass S K A] (φ : F),   C
ontinuous ⇑φ → ∀ (s : S), closure (↑s ∩ ↑(RingHom.ker φ)) = closure ↑s ∩ ↑(RingH
om.ker φ)
参数：φ : F；s : S；↑s ∩ ↑(RingHom.ker φ)；RingHom.ker φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `closure_inter_subset_inter_closure`：closure_inter_subset_inter_closure (
s t : Set X) : closure (s inter t) subseteq closure s inter closure t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 42 条，此处仅展示前 30 条）
-/
theorem AlgHom.closure_ker_inter {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s ∩ RingHom.ker φ) = closure s ∩ (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt, ClusterPt] at hxs
    have : Tendsto (fun y ↦ y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
    refine mem_closure_of_tendsto this <| eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩
/-
**ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMap`。
形式化陈述：ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 in s) [Compact
Space s] : (RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) = clos
ure (adjoin 𝕜 {(restrict s (.id 𝕜))})
参数：s : Set 𝕜；h0 : 0 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousMap.ker_evalStarAlgHom_inter_adjoin_id`：ker_evalStarAlgHom_int
er_adjoin_id (s : Set 𝕜) (h0 : 0 in s) : (StarAlgebra.adjoin 𝕜 {restrict s (.id 
𝕜)} : Set C(s, 𝕜)) inter RingHom.ker (…
· 使用定理 `ContinuousMap.AlgHom.closure_ker_inter`：∀ {F : Type u_2} {S : Type u_3} 
{K : Type u_4} {A : Type u_5} [inst : CommRing K] [inst_1 : Ring A]   [inst_2 : 
Algebra K A] [inst_3 : Topol…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `ContinuousMap.instContinuousSMul`：∀ {α : Type u_1} [inst : TopologicalSp
ace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_2 : T
opologicalSpace R] [in…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 43 条，此处仅展示前 30 条）
-/
lemma ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) [CompactSpace s] :
    (RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) =
      closure (adjoin 𝕜 {(restrict s (.id 𝕜))}) := by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0,
    AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0, h0⟩) (continuous_eval_const _) _]
  convert! (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id, ← Polynomial.toContinuousMapOnAlgHom_apply,
    ← polynomialFunctions.starClosure_eq_adjoin_X s]
  congrm (($(polynomialFunctions.starClosure_topologicalClosure s) : Set C(s, 𝕜)))

end ContinuousMap

open scoped ContinuousMapZero

/-- If `s : Set 𝕜` with `RCLike 𝕜` is compact and contains `0`, then the non-unital star subalgebra
generated by the identity function in `C(s, 𝕜)₀` is dense. This can be seen as a version of the
Weierstrass approximation theorem. -/
/-
**ContinuousMapZero.adjoin_id_dense** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMapZero.adjoin_id_dense (s : Set 𝕜) [Fact (0 in s)] [CompactSpac
e s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀)
参数：s : Set 𝕜；0 in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `ContinuousMapZero.isClosedEmbedding_toContinuousMap`：isClosedEmbedding_t
oContinuousMap [T1Space R] : IsClosedEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where
 toIsEmbedding
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Topology.IsClosedEmbedding.closure_image_eq`：∀ {X : Type u_1} {Y : Type 
u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   To
pology.IsClosedEmbedding f → ∀ (s…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `ContinuousMapZero.coe_toContinuousMapHom`：∀ {X : Type u_1} {R : Type u_2
} [inst : Zero X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSpace R]   
[inst_3 : CommSemiring R] [ins…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarSubalgebra.coe_map`：coe_map (S : NonUnitalStarSubalgebra R 
A) (f : F) : map f S = f '' S
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `NonUnitalStarAlgHom.map_adjoin_singleton`：∀ {F : Type v'} {R : Type u} {
A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 : NonUnitalSemiring A] 
  [inst_2 : StarRing A] [inst_…
· 使用引理 `ContinuousMapZero.toContinuousMap_id`：toContinuousMap_id {s : Set R} [Fa
ct (0 in s)] : (ContinuousMapZero.id s : C(s, R)) = .restrict s (.id R)
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `s : Set 𝕜` with `RCLike 𝕜` is compact and contains `0`, then the non-unital 
star subalgebra
generated by the identity function in `C(s, 𝕜)₀` is dense. This can be seen as a
 version of the
Weierstrass approximation theorem.
-/
lemma ContinuousMapZero.adjoin_id_dense (s : Set 𝕜) [Fact (0 ∈ s)]
    [CompactSpace s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀) := by
  have h0' : 0 ∈ s := Fact.out
  rw [dense_iff_closure_eq,
    ← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _),
    ← isClosedEmbedding_toContinuousMap.closure_image_eq, ← coe_toContinuousMapHom,
    ← NonUnitalStarSubalgebra.coe_map, NonUnitalStarAlgHom.map_adjoin_singleton,
    coe_toContinuousMapHom, toContinuousMap_id,
    ← ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id s h0']
  apply Set.eq_univ_of_forall fun f ↦ ?_
  simp only [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker,
    ContinuousMap.evalStarAlgHom_apply, ContinuousMap.coe_coe]
  exact map_zero f

open NonUnitalStarAlgebra in
/-
**ContinuousMapZero.elemental_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Fac
t (0 in s)] [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id s) = ⊤
参数：s : Set 𝕜；0 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `ContinuousMapZero.instCStarRing`：∀ {α : Type u_1} {R : Type u_3} [inst :
 TopologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : Zero α]   [inst_3 : Nor
medCommRing R] [inst_…
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用引理 `ContinuousMapZero.adjoin_id_dense`：ContinuousMapZero.adjoin_id_dense (s 
: Set 𝕜) [Fact (0 in s)] [CompactSpace s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)}
 : Set C(s, 𝕜)₀)
-/
lemma ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Fact (0 ∈ s)]
    [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id s) = ⊤ :=
  SetLike.ext'_iff.mpr (adjoin_id_dense s).closure_eq

/-- An induction principle for `C(s, 𝕜)₀`. -/
@[elab_as_elim]
/-
**ContinuousMapZero.induction_on** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMapZero.induction_on {s : Set 𝕜} [Fact (0 in s)] {p : C(s, 𝕜)₀ -
> Prop} (zero : p 0) (id : p (.id s)) (star_id : p (star (.id s))) (add : forall
 f g, p f -> p g -> p (f + g)) (mul : forall f g, p f -> p g -> p (f * g)) (smul
 : forall (r : 𝕜) f, p f -> p (r • f)) (closure : (forall f in adjoin 𝕜 {(.id s 
: C(s, 𝕜)₀)}, p f) -> forall f, p f) (f : C(s, 𝕜)₀) : p f
参数：0 in s；s, 𝕜；zero : p 0；id : p (.id s)；star_id : p (star (.id s))；add : forall
 f g, p f -> p g -> p (f + g)；mul : forall f g, p f -> p g -> p (f * g)；smul : f
orall (r : 𝕜) f, p f -> p (r • f)；closure : (forall f in adjoin 𝕜 {(.id s : C(s,
 𝕜)₀)}, p f) -> forall f, p f；f : C(s, 𝕜)₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalAlgebra.adjoin_induction`：adjoin_induction {s : Set A} {p : (x 
: A) -> x in adjoin R s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_ad
join R hx)) (add : fora…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An induction principle for `C(s, 𝕜)₀`.
-/
lemma ContinuousMapZero.induction_on {s : Set 𝕜} [Fact (0 ∈ s)]
    {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id s)) (star_id : p (star (.id s)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (closure : (∀ f ∈ adjoin 𝕜 {(.id s : C(s, 𝕜)₀)}, p f) → ∀ f, p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    push _ ∈ _ at hf
    rw [star_eq_iff_star_eq] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
  | smul _ _ _ hf => exact smul _ _ hf

open Topology in
@[elab_as_elim]
/-
**ContinuousMapZero.induction_on_of_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMapZero.induction_on_of_compact {s : Set 𝕜} [Fact (0 in s)] [Com
pactSpace s] {p : C(s, 𝕜)₀ -> Prop} (zero : p 0) (id : p (.id s)) (star_id : p (
star (.id s))) (add : forall f g, p f -> p g -> p (f + g)) (mul : forall f g, p 
f -> p g -> p (f * g)) (smul : forall (r : 𝕜) f, p f -> p (r • f)) (frequently :
 forall f, (existsᶠ g in 𝓝 f, p g) -> p f) (f : C(s, 𝕜)₀) : p f
参数：0 in s；s, 𝕜；zero : p 0；id : p (.id s)；star_id : p (star (.id s))；add : forall
 f g, p f -> p g -> p (f + g)；mul : forall f g, p f -> p g -> p (f * g)；smul : f
orall (r : 𝕜) f, p f -> p (r • f)；frequently : forall f, (existsᶠ g in 𝓝 f, p g)
 -> p f；f : C(s, 𝕜)₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `ContinuousMapZero.induction_on`：ContinuousMapZero.induction_on {s : Set 
𝕜} [Fact (0 in s)] {p : C(s, 𝕜)₀ -> Prop} (zero : p 0) (id : p (.id s)) (star_id
 : p (star (.id s)))…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用引理 `ContinuousMapZero.adjoin_id_dense`：ContinuousMapZero.adjoin_id_dense (s 
: Set 𝕜) [Fact (0 in s)] [CompactSpace s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)}
 : Set C(s, 𝕜)₀)
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem ContinuousMapZero.induction_on_of_compact {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id s))
    (star_id : p (star (.id s))) (add : ∀ f g, p f → p g → p (f + g))
    (mul : ∀ f g, p f → p g → p (f * g)) (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine f.induction_on zero id star_id add mul smul fun h f ↦ frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense s).closure_eq ▸ Set.mem_univ (x := f)
  exact mem_closure_iff_frequently.mp this |>.mp <| .of_forall h
/-
**ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*} [RCL
ike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuous
Mul A] [T2Space A] [DistribMulAction 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Fac
t (0 in s)] [CompactSpace s] (φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id
 s) * a = 0) (hmul_star_id : φ (star (.id s)) * a = 0) (hφ : Continuous φ) (f : 
C(s, 𝕜)₀) : φ f * a = 0
参数：0 in s；φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A；a : A；hmul_id : φ (.id s) * a = 0；hmul_star_id
 : φ (star (.id s)) * a = 0；hφ : Continuous φ；f : C(s, 𝕜)₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMapZero.induction_on_of_compact`：ContinuousMapZero.induction_o
n_of_compact {s : Set 𝕜} [Fact (0 in s)] [CompactSpace s] {p : C(s, 𝕜)₀ -> Prop}
 (zero : p 0) (id : p (.id s)) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 40 条，此处仅展示前 30 条）
-/
lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id s) * a = 0)
    (hmul_star_id : φ (star (.id s)) * a = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    φ f * a = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ h => rw [map_smul, smul_mul_assoc, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero
/-
**ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*} [RCL
ike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuous
Mul A] [T2Space A] [DistribMulAction 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Fac
t (0 in s)] [CompactSpace s] (φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ 
(.id s) = 0) (hmul_star_id : a * φ (star (.id s)) = 0) (hφ : Continuous φ) (f : 
C(s, 𝕜)₀) : a * φ f = 0
参数：0 in s；φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A；a : A；hmul_id : a * φ (.id s) = 0；hmul_star_id
 : a * φ (star (.id s)) = 0；hφ : Continuous φ；f : C(s, 𝕜)₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMapZero.induction_on_of_compact`：ContinuousMapZero.induction_o
n_of_compact {s : Set 𝕜} [Fact (0 in s)] [CompactSpace s] {p : C(s, 𝕜)₀ -> Prop}
 (zero : p 0) (id : p (.id s)) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 39 条，此处仅展示前 30 条）
-/
lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ (.id s) = 0)
    (hmul_star_id : a * φ (star (.id s)) = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    a * φ f = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ _ h => rw [map_smul, mul_smul_comm, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero

end ContinuousMapZero

