/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* Circle` with the compact-open
topology. For example, `ℤ` and `Circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* Circle`.
-/

@[expose] public section

open scoped Pointwise
open Real

variable (A B C G H : Type*) [Monoid A] [Monoid B] [Monoid C] [CommGroup G] [Group H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

noncomputable section

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → Circle`. -/
/-
**PontryaginDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PontryaginDual
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Pontryagin dual of `A` is the group of continuous homomorphism `A → Circle`.
-/
def PontryaginDual :=
  A →ₜ* Circle
deriving TopologicalSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyCompactSpace H] : LocallyCompactSpace (PontryaginDual H) := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompactSpace_of_hasBasis Vn ?_ ?_
  · intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  · simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow

variable {A B C G}

namespace PontryaginDual

open ContinuousMonoidHom

/-
**PontryaginDual.** 是 Mathlib 中的一个实例，位于命名空间 `PontryaginDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommGroup (PontryaginDual A) := inferInstanceAs (CommGroup (A →ₜ* Circle))

deriving instance
  T2Space, IsTopologicalGroup,
  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,
  [DiscreteTopology A] → CompactSpace _
for PontryaginDual A

@[ext]
/-
**PontryaginDual.ext** 是 Mathlib 中的一个定理，位于命名空间 `PontryaginDual`。
形式化陈述：ext {ψ φ : PontryaginDual A} (h : forall a, ψ a = φ a) : ψ = φ
参数：h : forall a, ψ a = φ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {ψ φ : PontryaginDual A} (h : ∀ a, ψ a = φ a) : ψ = φ :=
  DFunLike.ext _ _ h

@[simp]
/-
**PontryaginDual.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `PontryaginDual`。
形式化陈述：one_apply (a : A) : (1 : PontryaginDual A) a = 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : PontryaginDual A) a = 1 :=
  rfl

/-- A discrete monoid has compact Pontryagin dual. -/
add_decl_doc instLocallyCompactSpacePontryaginDual

/-- A compact monoid has discrete Pontryagin dual. -/
/-
**PontryaginDual.** 是 Mathlib 中的一个实例，位于命名空间 `PontryaginDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact monoid has discrete Pontryagin dual.
-/
instance [CompactSpace A] : DiscreteTopology (PontryaginDual A) := by
  let V : Set (PontryaginDual A) := {ψ | Set.MapsTo ψ Set.univ (Circle.centeredArc (π / 2))}
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (Circle.isOpen_centeredArc (π / 2)))
  have hVeq : V = ({1} : Set (PontryaginDual A)) := by
    ext ψ
    rw [Set.mem_singleton_iff]
    refine ⟨fun hψ ↦ ?_, ?_⟩
    · ext1 a
      refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n hn ↦ ?_
      simpa using hψ (Set.mem_univ (a ^ n))
    · rintro rfl _ _
      rw [Circle.mem_centeredArc (by linarith [pi_pos])]
      simp [pi_pos]
  exact discreteTopology_of_isOpen_singleton_one (by simpa [hVeq] using hVopen)
/-
**PontryaginDual.** 是 Mathlib 中的一个实例，位于命名空间 `PontryaginDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology A] [CompactSpace A] : Finite (PontryaginDual A) :=
  finite_of_compact_of_discrete
/-
**PontryaginDual.** 是 Mathlib 中的一个实例，位于命名空间 `PontryaginDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [DiscreteTopology A] [CompactSpace A] : Fintype (PontryaginDual A) :=
  .ofFinite _

/-- `PontryaginDual` is a contravariant functor. -/
/-
**PontryaginDual.map** 是 Mathlib 中的一个定义，位于命名空间 `PontryaginDual`。
形式化陈述：map (f : A ->ₜ* B) : (PontryaginDual B) ->ₜ* (PontryaginDual A)
参数：f : A ->ₜ* B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Circle.instIsTopologicalGroup`：IsTopologicalGroup Circle

--- 原说明 ---
`PontryaginDual` is a contravariant functor.
-/
def map (f : A →ₜ* B) :
    (PontryaginDual B) →ₜ* (PontryaginDual A) :=
  f.compLeft Circle

@[simp]
/-
**PontryaginDual.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `PontryaginDual`。
形式化陈述：map_apply (f : A ->ₜ* B) (x : PontryaginDual B) (y : A) : map f x y = x (f
 y)
参数：f : A ->ₜ* B；x : PontryaginDual B；y : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (f : A →ₜ* B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[simp]
/-
**PontryaginDual.map_one** 是 Mathlib 中的一个定理，位于命名空间 `PontryaginDual`。
形式化陈述：map_one : map (1 : A ->ₜ* B) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.ext`：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `PontryaginDual.ext`：ext {ψ φ : PontryaginDual A} (h : forall a, ψ a = φ 
a) : ψ = φ
· 使用定理 `OneHomClass.map_one`：∀ {F : Type u_10} {M : outParam (Type u_11)} {N : o
utParam (Type u_12)} {inst : One M} {inst_1 : One N}   {inst_2 : FunLike F M N} 
[self : O…
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `PontryaginDual.instMonoidHomClassCircle`：∀ {A : Type u_1} [inst : Monoid
 A] [inst_1 : TopologicalSpace A], MonoidHomClass (PontryaginDual A) A Circle
-/
theorem map_one : map (1 : A →ₜ* B) = 1 :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun _y => OneHomClass.map_one x

@[simp]
/-
**PontryaginDual.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `PontryaginDual`。
形式化陈述：map_comp (g : B ->ₜ* C) (f : A ->ₜ* B) : map (comp g f) = ContinuousMonoid
Hom.comp (map f) (map g)
参数：g : B ->ₜ* C；f : A ->ₜ* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.ext`：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `PontryaginDual.ext`：ext {ψ φ : PontryaginDual A} (h : forall a, ψ a = φ 
a) : ψ = φ
-/
theorem map_comp (g : B →ₜ* C) (f : A →ₜ* B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ContinuousMonoidHom.ext fun _x => PontryaginDual.ext fun _y => rfl

@[simp]
nonrec theorem map_mul (f g : A →ₜ* G) : map (f * g) = map f * map g :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun y => map_mul x (f y) (g y)

variable (A B C G)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
/-
**PontryaginDual.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `PontryaginDual`。
形式化陈述：mapHom [LocallyCompactSpace G] : (A ->ₜ* G) ->ₜ* ((PontryaginDual G) ->ₜ* 
(PontryaginDual A)) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PontryaginDual.instIsTopologicalGroup`：∀ {A : Type u_1} [inst : Monoid A
] [inst_1 : TopologicalSpace A], IsTopologicalGroup (PontryaginDual A)
· 使用定理 `PontryaginDual.map_mul`：∀ {A : Type u_1} {G : Type u_4} [inst : Monoid A
] [inst_1 : CommGroup G] [inst_2 : TopologicalSpace A]   [inst_3 : TopologicalSp
ace G] [inst…

--- 原说明 ---
`ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`.
-/
def mapHom [LocallyCompactSpace G] :
    (A →ₜ* G) →ₜ* ((PontryaginDual G) →ₜ* (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual

