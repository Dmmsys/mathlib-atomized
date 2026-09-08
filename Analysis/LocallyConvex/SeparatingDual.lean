/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

We show in `SeparatingDual.exists_ne_zero` that given any non-zero vector in an `R`-module `V`
satisfying `SeparatingDual R V`, there exists a continuous linear functional whose value on `v` is
non-zero.

As a consequence of the existence of `SeparatingDual.exists_ne_zero`, a generalization of
Hahn-Banach beyond the normed setting, we show that if `V` and `W` are nontrivial topological vector
spaces over a topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`,
there are nontrivial continuous `R`-linear operators between `V` and `W`. This is recorded in the
instance `SeparatingDual.instNontrivialContinuousLinearMapIdOfContinuousSMul`.

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearEquiv_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/

public section
/-- When `E` is a topological module over a topological ring `R`, the class `SeparatingDual R E`
registers that continuous linear forms on `E` separate points of `E`. -/
@[mk_iff separatingDual_def]
/-
**SeparatingDual** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (V : Type u_2) →     [inst : Ring R] →       [inst_1 : 
AddCommGroup V] → [TopologicalSpace V] → [TopologicalSpace R] → [_root_.Module R
 V] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `E` is a topological module over a topological ring `R`, the class `Separat
ingDual R E`
registers that continuous linear forms on `E` separate points of `E`.
-/
class SeparatingDual (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
    [TopologicalSpace R] [Module R V] : Prop where
  /-- Any nonzero vector can be mapped by a continuous linear map to a nonzero scalar. -/
  exists_ne_zero' : ∀ (x : V), x ≠ 0 → ∃ f : StrongDual R V, f x ≠ 0
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual ℝ E :=
  ⟨fun x hx ↦ by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    simp only [map_zero] at hf
    exact ⟨f, hf.ne'⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦
    let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
    let : Module ℝ E := .restrictScalars ℝ 𝕜 E
    have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
    have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
    RCLike.geometric_hahn_banach_point_point hx |>.imp fun f hf hf' ↦ by simp [hf'] at hf⟩

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

/-
**SeparatingDual.exists_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SeparatingDual`。
形式化陈述：exists_ne_zero {x : V} (hx : x != 0) : exists f : StrongDual R V, f x != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatingDual.exists_ne_zero'`：∀ {R : Type u_1} {V : Type u_2} {inst : 
Ring R} {inst_1 : AddCommGroup V} {inst_2 : TopologicalSpace V}   {inst_3 : Topo
logicalSpace R} {ins…
-/
lemma exists_ne_zero {x : V} (hx : x ≠ 0) :
    ∃ f : StrongDual R V, f x ≠ 0 :=
  exists_ne_zero' x hx
/-
**SeparatingDual.exists_separating_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SeparatingDu
al`。
形式化陈述：exists_separating_of_ne {x y : V} (h : x != y) : exists f : StrongDual R V
, f x != f y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatingDual.exists_ne_zero`：exists_ne_zero {x : V} (hx : x != 0) : ex
ists f : StrongDual R V, f x != 0
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem exists_separating_of_ne {x y : V} (h : x ≠ y) :
    ∃ f : StrongDual R V, f x ≠ f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩
/-
**SeparatingDual.t1Space** 是 Mathlib 中的一个定理，位于命名空间 `SeparatingDual`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : TopologicalSpace V]   [inst_3 : TopologicalSpace R] [inst_4 : _root_.M
odule R V] [SeparatingDual R V] [T1Space R], T1Space V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t1Space_iff_exists_open`：t1Space_iff_exists_open : T1Space X ↔ Pairwise 
fun x y => exists U : Set X, IsOpen U ∧ x in U ∧ y ∉ U
· 使用定理 `SeparatingDual.exists_separating_of_ne`：exists_separating_of_ne {x y : V
} (h : x != y) : exists f : StrongDual R V, f x != f y
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩
/-
**SeparatingDual.t2Space** 是 Mathlib 中的一个定理，位于命名空间 `SeparatingDual`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : TopologicalSpace V]   [inst_3 : TopologicalSpace R] [inst_4 : _root_.M
odule R V] [SeparatingDual R V] [T2Space R], T2Space V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t2Space_iff`：∀ (X : Type u) [inst : TopologicalSpace X],   T2Space X ↔ P
airwise fun x y => ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
· 使用定理 `SeparatingDual.exists_separating_of_ne`：exists_separating_of_ne {x y : V
} (h : x != y) : exists f : StrongDual R V, f x != f y
· 使用定理 `separated_by_continuous`：separated_by_continuous [TopologicalSpace Y] [T
2Space Y] {f : X -> Y} (hf : Continuous f) {x y : X} (h : f x != f y) : exists u
 v : Set X, I…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf
/-
**SeparatingDual.eq_zero_of_forall_dual_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Separ
atingDual`。
形式化陈述：eq_zero_of_forall_dual_eq_zero {x : V} (h : forall f : StrongDual R V, f x
 = 0) : x = 0
参数：h : forall f : StrongDual R V, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `SeparatingDual.exists_ne_zero`：exists_ne_zero {x : V} (hx : x != 0) : ex
ists f : StrongDual R V, f x != 0
-/
theorem eq_zero_of_forall_dual_eq_zero {x : V} (h : ∀ f : StrongDual R V, f x = 0) : x = 0 := by
  by_contra hx
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact hf (h f)
/-
**SeparatingDual.eq_zero_iff_forall_dual_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sepa
ratingDual`。
形式化陈述：eq_zero_iff_forall_dual_eq_zero (x : V) : x = 0 ↔ forall g : StrongDual R 
V, g x = 0
参数：x : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SeparatingDual.eq_zero_of_forall_dual_eq_zero`：eq_zero_of_forall_dual_eq
_zero {x : V} (h : forall f : StrongDual R V, f x = 0) : x = 0
-/
theorem eq_zero_iff_forall_dual_eq_zero (x : V) : x = 0 ↔ ∀ g : StrongDual R V, g x = 0 :=
  ⟨by simp +contextual, fun h => eq_zero_of_forall_dual_eq_zero (R := R) h⟩

/-- See also `geometric_hahn_banach_point_point`. -/
/-
**SeparatingDual.eq_iff_forall_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `SeparatingDual
`。
形式化陈述：eq_iff_forall_dual_eq {x y : V} : x = y ↔ forall g : StrongDual R V, g x =
 g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `SeparatingDual.eq_zero_iff_forall_dual_eq_zero`：eq_zero_iff_forall_dual_
eq_zero (x : V) : x = 0 ↔ forall g : StrongDual R V, g x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `geometric_hahn_banach_point_point`.
-/
theorem eq_iff_forall_dual_eq {x y : V} : x = y ↔ ∀ g : StrongDual R V, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero (R := R) (x - y)]
  simp [sub_eq_zero]

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [IsTopologicalRing R] [Module R V]

-- TODO (@alreadydone): this could generalize to CommRing R if we were to add a section
/-
**SeparatingDual._root_.separatingDual_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `
SeparatingDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.separatingDual_iff_injective : SeparatingDual R V ↔
    Function.Injective (ContinuousLinearMap.coeLM (R := R) R (M := V) (N₃ := R)).flip := by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm ∀ v, ?_
  rw [not_imp_comm, LinearMap.ext_iff]
  push Not; rfl

variable [SeparatingDual R V]

open Function

/-- Given a finite-dimensional subspace `W` of a space `V` with separating dual, any
  linear functional on `W` extends to a continuous linear functional on `V`.
  This is stated more generally for an injective linear map from `W` to `V`. -/
/-
**SeparatingDual.dualMap_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparatingDua
l`。
形式化陈述：dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensiona
l R W] {f : W ->ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMa
p) ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.dualMap_surjective_iff`：dualMap_surjective_iff {f : V₁ ->ₗ[K] 
V₂} : Function.Surjective f.dualMap ↔ Function.Injective f
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `separatingDual_iff_injective`：∀ {R : Type u_1} {V : Type u_2} [inst : Fi
eld R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace R]   [inst_3 : Topol
ogicalSpace V] [in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `LinearMap.flip_surjective_iff₁`：flip_surjective_iff₁ [FiniteDimensional 
K V₁] : Surjective B.flip ↔ Injective B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g

--- 原说明 ---
Given a finite-dimensional subspace `W` of a space `V` with separating dual, any
  linear functional on `W` extends to a continuous linear functional on `V`.
  This is stated more generally for an injective linear map from `W` to `V`.
-/
theorem dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
    {f : W →ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMap) ↔ Injective f := by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

variable (V) in
open ContinuousLinearMap in
/- As a consequence of the existence of non-zero linear maps, itself a consequence of Hahn-Banach
in the normed setting, we show that if `V` and `W` are nontrivial topological vector spaces over a
topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`, there are
nontrivial continuous `R`-linear operators between `V` and `W`. -/
/-
**SeparatingDual.** 是 Mathlib 中的一个实例，位于命名空间 `SeparatingDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a consequence of the existence of non-zero linear maps, itself a consequence 
of Hahn-Banach
in the normed setting, we show that if `V` and `W` are nontrivial topological ve
ctor spaces over a
topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`
, there are
nontrivial continuous `R`-linear operators between `V` and `W`.
-/
instance (W) [AddCommGroup W] [TopologicalSpace W] [Module R W] [Nontrivial W]
    [ContinuousSMul R W] [Nontrivial V] : Nontrivial (V →L[R] W) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨ψ, hψ⟩ := exists_ne_zero (R := R) hv
  exact ⟨ψ.smulRight w, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩
/-
**SeparatingDual.exists_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `SeparatingDual`。
形式化陈述：exists_eq_one {x : V} (hx : x != 0) : exists f : StrongDual R V, f x = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatingDual.exists_ne_zero`：exists_ne_zero {x : V} (hx : x != 0) : ex
ists f : StrongDual R V, f x != 0
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
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
lemma exists_eq_one {x : V} (hx : x ≠ 0) :
    ∃ f : StrongDual R V, f x = 1 := by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩
/-
**SeparatingDual.exists_eq_one_ne_zero_of_ne_zero_pair** 是 Mathlib 中的一个定理，位于命名空间
 `SeparatingDual`。
形式化陈述：exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x != 0) (hy : y != 0
) : exists f : StrongDual R V, f x = 1 ∧ f y != 0
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatingDual.exists_eq_one`：exists_eq_one {x : V} (hx : x != 0) : exis
ts f : StrongDual R V, f x = 1
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
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
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : StrongDual R V, f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨u, ux⟩ : ∃ u : StrongDual R V, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy | uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : ∃ v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx | vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y ≠ 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

variable [IsTopologicalAddGroup V] [ContinuousSMul R V]

section algebra
variable {S : Type*} [CommSemiring S] [Module S V] [SMulCommClass R S V] [Algebra S R]
  [IsScalarTower S R V] [ContinuousConstSMul S V]

/-- The center of continuous linear maps on a topological vector space
with separating dual is trivial, in other words, it is a central algebra. -/
/-
**SeparatingDual._root_.Algebra.IsCentral.instContinuousLinearMap** 是 Mathlib 中的
一个实例，位于命名空间 `SeparatingDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of continuous linear maps on a topological vector space
with separating dual is trivial, in other words, it is a central algebra.
-/
instance _root_.Algebra.IsCentral.instContinuousLinearMap [Algebra.IsCentral S R] :
    Algebra.IsCentral S (V →L[R] V) where
  out f hf := by
    suffices ∃ α ∈ Subalgebra.center S R, f = α • .id R V from
      have ⟨_, ⟨y, _⟩, _⟩ := Algebra.IsCentral.center_eq_bot S R ▸ this
      ⟨y, by aesop⟩
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := exists_eq_one (R := R) hx
    have (y : V) := by simpa [hg] using congr($(Subalgebra.mem_center_iff.mp hf (g.smulRight y)) x)
    exact ⟨g (f x), by simp [this, ContinuousLinearMap.ext_iff]⟩

open ContinuousLinearMap ContinuousLinearEquiv in
/-
**SeparatingDual._root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff** 是
 Mathlib 中的一个定理，位于命名空间 `SeparatingDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff
    {R V W : Type*} [NormedField R] [AddCommGroup V] [AddCommGroup W] [TopologicalSpace R]
    [TopologicalSpace V] [TopologicalSpace W] [IsTopologicalRing R] [Module R V] [Module R W]
    [SeparatingDual R V] [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]
    [ContinuousSMul R V] [ContinuousSMul R W] (f g : V ≃L[R] W) :
    f.conjContinuousAlgEquiv = g.conjContinuousAlgEquiv ↔ ∃ α : Rˣ, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← ContinuousLinearMap.comp_assoc,
    eq_comp_toContinuousLinearMap_symm, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ f.toContinuousLinearMap, comp_coe, ← mul_def,
    ← Subalgebra.mem_center_iff (R := R), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one, ContinuousLinearEquiv.ext_iff]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : R), by ext; simp [h]⟩⟩
  if hy : y = 0 then exact ⟨1, funext fun x ↦ by simp [by simpa [hy] using congr($h x).symm]⟩
  else exact ⟨.mk0 y hy, funext fun x ↦ by simp [by simpa [eq_symm_apply] using congr($h x)]⟩

end algebra

/-- In a topological vector space with separating dual, the group of continuous linear equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` and `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`. -/
/-
**SeparatingDual.exists_continuousLinearEquiv_apply_eq** 是 Mathlib 中的一个定理，位于命名空间
 `SeparatingDual`。
形式化陈述：exists_continuousLinearEquiv_apply_eq {x y : V} (hx : x != 0) (hy : y != 0
) : exists A : V ≃L[R] V, A x = y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatingDual.exists_eq_one_ne_zero_of_ne_zero_pair`：exists_eq_one_ne_z
ero_of_ne_zero_pair {x y : V} (hx : x != 0) (hy : y != 0) : exists f : StrongDua
l R V, f x = 1 ∧ f y != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.Analysis.LocallyConvex.SeparatingDual.0.SeparatingDual.
exists_continuousLinearEquiv_apply_eq._abel_1_1`：∀ {R : Type u_2} {V : Type u_1}
 [inst : Field R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace R]   [ins
t_3 : TopologicalSpace V] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
In a topological vector space with separating dual, the group of continuous line
ar equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` a
nd `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`.
-/
theorem exists_continuousLinearEquiv_apply_eq
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : StrongDual R V, G x = 1 ∧ G y ≠ 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y)⁻¹ * G z) • (x - y)
    map_add' := fun a b ↦ by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z ↦ by
      simp only [RingHom.id_apply, smul_eq_mul,
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z), ← mul_assoc, inv_mul_cancel₀ Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z ↦ by
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y), ← mul_assoc, mul_inv_cancel₀ Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

end Field

end SeparatingDual

